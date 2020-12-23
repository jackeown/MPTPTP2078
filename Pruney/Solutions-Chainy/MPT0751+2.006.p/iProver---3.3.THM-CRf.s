%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:54:03 EST 2020

% Result     : Theorem 2.49s
% Output     : CNFRefutation 2.49s
% Verified   : 
% Statistics : Number of formulae       :  232 (2820 expanded)
%              Number of clauses        :  159 ( 921 expanded)
%              Number of leaves         :   20 ( 571 expanded)
%              Depth                    :   24
%              Number of atoms          :  785 (10370 expanded)
%              Number of equality atoms :  353 (2769 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( ~ ( v4_ordinal1(X0)
            & ? [X1] :
                ( k1_ordinal1(X1) = X0
                & v3_ordinal1(X1) ) )
        & ~ ( ! [X1] :
                ( v3_ordinal1(X1)
               => k1_ordinal1(X1) != X0 )
            & ~ v4_ordinal1(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ( ~ ( v4_ordinal1(X0)
              & ? [X1] :
                  ( k1_ordinal1(X1) = X0
                  & v3_ordinal1(X1) ) )
          & ~ ( ! [X1] :
                  ( v3_ordinal1(X1)
                 => k1_ordinal1(X1) != X0 )
              & ~ v4_ordinal1(X0) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f14,plain,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ( ~ ( v4_ordinal1(X0)
              & ? [X1] :
                  ( k1_ordinal1(X1) = X0
                  & v3_ordinal1(X1) ) )
          & ~ ( ! [X2] :
                  ( v3_ordinal1(X2)
                 => k1_ordinal1(X2) != X0 )
              & ~ v4_ordinal1(X0) ) ) ) ),
    inference(rectify,[],[f13])).

fof(f24,plain,(
    ? [X0] :
      ( ( ( v4_ordinal1(X0)
          & ? [X1] :
              ( k1_ordinal1(X1) = X0
              & v3_ordinal1(X1) ) )
        | ( ! [X2] :
              ( k1_ordinal1(X2) != X0
              | ~ v3_ordinal1(X2) )
          & ~ v4_ordinal1(X0) ) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k1_ordinal1(X1) = X0
          & v3_ordinal1(X1) )
     => ( k1_ordinal1(sK2) = X0
        & v3_ordinal1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X0] :
        ( ( ( v4_ordinal1(X0)
            & ? [X1] :
                ( k1_ordinal1(X1) = X0
                & v3_ordinal1(X1) ) )
          | ( ! [X2] :
                ( k1_ordinal1(X2) != X0
                | ~ v3_ordinal1(X2) )
            & ~ v4_ordinal1(X0) ) )
        & v3_ordinal1(X0) )
   => ( ( ( v4_ordinal1(sK1)
          & ? [X1] :
              ( k1_ordinal1(X1) = sK1
              & v3_ordinal1(X1) ) )
        | ( ! [X2] :
              ( k1_ordinal1(X2) != sK1
              | ~ v3_ordinal1(X2) )
          & ~ v4_ordinal1(sK1) ) )
      & v3_ordinal1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ( ( v4_ordinal1(sK1)
        & k1_ordinal1(sK2) = sK1
        & v3_ordinal1(sK2) )
      | ( ! [X2] :
            ( k1_ordinal1(X2) != sK1
            | ~ v3_ordinal1(X2) )
        & ~ v4_ordinal1(sK1) ) )
    & v3_ordinal1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f24,f37,f36])).

fof(f60,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f11,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v4_ordinal1(X0)
      <=> ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X1,X0)
             => r2_hidden(k1_ordinal1(X1),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ( v4_ordinal1(X0)
      <=> ! [X1] :
            ( r2_hidden(k1_ordinal1(X1),X0)
            | ~ r2_hidden(X1,X0)
            | ~ v3_ordinal1(X1) ) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f23,plain,(
    ! [X0] :
      ( ( v4_ordinal1(X0)
      <=> ! [X1] :
            ( r2_hidden(k1_ordinal1(X1),X0)
            | ~ r2_hidden(X1,X0)
            | ~ v3_ordinal1(X1) ) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f32,plain,(
    ! [X0] :
      ( ( ( v4_ordinal1(X0)
          | ? [X1] :
              ( ~ r2_hidden(k1_ordinal1(X1),X0)
              & r2_hidden(X1,X0)
              & v3_ordinal1(X1) ) )
        & ( ! [X1] :
              ( r2_hidden(k1_ordinal1(X1),X0)
              | ~ r2_hidden(X1,X0)
              | ~ v3_ordinal1(X1) )
          | ~ v4_ordinal1(X0) ) )
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f33,plain,(
    ! [X0] :
      ( ( ( v4_ordinal1(X0)
          | ? [X1] :
              ( ~ r2_hidden(k1_ordinal1(X1),X0)
              & r2_hidden(X1,X0)
              & v3_ordinal1(X1) ) )
        & ( ! [X2] :
              ( r2_hidden(k1_ordinal1(X2),X0)
              | ~ r2_hidden(X2,X0)
              | ~ v3_ordinal1(X2) )
          | ~ v4_ordinal1(X0) ) )
      | ~ v3_ordinal1(X0) ) ),
    inference(rectify,[],[f32])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k1_ordinal1(X1),X0)
          & r2_hidden(X1,X0)
          & v3_ordinal1(X1) )
     => ( ~ r2_hidden(k1_ordinal1(sK0(X0)),X0)
        & r2_hidden(sK0(X0),X0)
        & v3_ordinal1(sK0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ( ( v4_ordinal1(X0)
          | ( ~ r2_hidden(k1_ordinal1(sK0(X0)),X0)
            & r2_hidden(sK0(X0),X0)
            & v3_ordinal1(sK0(X0)) ) )
        & ( ! [X2] :
              ( r2_hidden(k1_ordinal1(X2),X0)
              | ~ r2_hidden(X2,X0)
              | ~ v3_ordinal1(X2) )
          | ~ v4_ordinal1(X0) ) )
      | ~ v3_ordinal1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f34])).

fof(f58,plain,(
    ! [X0] :
      ( v4_ordinal1(X0)
      | r2_hidden(sK0(X0),X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f10,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r2_hidden(X0,k1_ordinal1(X1))
              | ~ r1_ordinal1(X0,X1) )
            & ( r1_ordinal1(X0,X1)
              | ~ r2_hidden(X0,k1_ordinal1(X1)) ) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f2,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f55,f42])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
    <=> ( X0 = X1
        | r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(flattening,[],[f28])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f47,f42])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ r2_hidden(X0,k1_ordinal1(X1))
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f54,f42])).

fof(f8,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k1_ordinal1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f51,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f72,plain,(
    ! [X0] :
      ( v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0)))
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f51,f42])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f9,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
          <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X0,X1)
          <=> r1_ordinal1(k1_ordinal1(X0),X1) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r2_hidden(X0,X1)
              | ~ r1_ordinal1(k1_ordinal1(X0),X1) )
            & ( r1_ordinal1(k1_ordinal1(X0),X1)
              | ~ r2_hidden(X0,X1) ) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(k1_ordinal1(X0),X1)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),X1)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f52,f42])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f25])).

fof(f41,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f57,plain,(
    ! [X0] :
      ( v4_ordinal1(X0)
      | v3_ordinal1(sK0(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f7,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | X0 = X1
      | r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f6,axiom,(
    ! [X0] : k1_ordinal1(X0) != X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : k1_ordinal1(X0) != X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f71,plain,(
    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) != X0 ),
    inference(definition_unfolding,[],[f49,f42])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_ordinal1(k1_ordinal1(X0),X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f53,f42])).

fof(f59,plain,(
    ! [X0] :
      ( v4_ordinal1(X0)
      | ~ r2_hidden(k1_ordinal1(sK0(X0)),X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f77,plain,(
    ! [X0] :
      ( v4_ordinal1(X0)
      | ~ r2_hidden(k2_xboole_0(sK0(X0),k1_tarski(sK0(X0))),X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f59,f42])).

fof(f63,plain,
    ( k1_ordinal1(sK2) = sK1
    | ~ v4_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f81,plain,
    ( k2_xboole_0(sK2,k1_tarski(sK2)) = sK1
    | ~ v4_ordinal1(sK1) ),
    inference(definition_unfolding,[],[f63,f42])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | X0 != X1 ) ),
    inference(definition_unfolding,[],[f48,f42])).

fof(f85,plain,(
    ! [X1] : r2_hidden(X1,k2_xboole_0(X1,k1_tarski(X1))) ),
    inference(equality_resolution,[],[f68])).

fof(f4,axiom,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f67,plain,(
    ! [X0] : r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f45,f42])).

fof(f61,plain,
    ( v3_ordinal1(sK2)
    | ~ v4_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f56,plain,(
    ! [X2,X0] :
      ( r2_hidden(k1_ordinal1(X2),X0)
      | ~ r2_hidden(X2,X0)
      | ~ v3_ordinal1(X2)
      | ~ v4_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f78,plain,(
    ! [X2,X0] :
      ( r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),X0)
      | ~ r2_hidden(X2,X0)
      | ~ v3_ordinal1(X2)
      | ~ v4_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f56,f42])).

fof(f66,plain,(
    ! [X2] :
      ( v4_ordinal1(sK1)
      | k1_ordinal1(X2) != sK1
      | ~ v3_ordinal1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f79,plain,(
    ! [X2] :
      ( v4_ordinal1(sK1)
      | k2_xboole_0(X2,k1_tarski(X2)) != sK1
      | ~ v3_ordinal1(X2) ) ),
    inference(definition_unfolding,[],[f66,f42])).

cnf(c_26,negated_conjecture,
    ( v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1518,plain,
    ( v3_ordinal1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_17,plain,
    ( r2_hidden(sK0(X0),X0)
    | v4_ordinal1(X0)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1526,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v4_ordinal1(X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_14,plain,
    ( r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
    | ~ r1_ordinal1(X0,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1529,plain,
    ( r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) = iProver_top
    | r1_ordinal1(X0,X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1535,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
    | r1_ordinal1(X0,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1528,plain,
    ( r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) != iProver_top
    | r1_ordinal1(X0,X1) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2508,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_ordinal1(X0,X1) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1535,c_1528])).

cnf(c_2805,plain,
    ( r1_ordinal1(X0,X1) != iProver_top
    | r1_ordinal1(X0,k2_xboole_0(X1,k1_tarski(X1))) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(k2_xboole_0(X1,k1_tarski(X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1529,c_2508])).

cnf(c_11,plain,
    ( ~ v3_ordinal1(X0)
    | v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1532,plain,
    ( v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3730,plain,
    ( r1_ordinal1(X0,X1) != iProver_top
    | r1_ordinal1(X0,k2_xboole_0(X1,k1_tarski(X1))) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2805,c_1532])).

cnf(c_4,plain,
    ( ~ r1_ordinal1(X0,X1)
    | r1_tarski(X0,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1537,plain,
    ( r1_ordinal1(X0,X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3734,plain,
    ( r1_ordinal1(X0,X1) != iProver_top
    | r1_tarski(X0,k2_xboole_0(X1,k1_tarski(X1))) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(k2_xboole_0(X1,k1_tarski(X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3730,c_1537])).

cnf(c_5482,plain,
    ( r1_ordinal1(X0,X1) != iProver_top
    | r1_tarski(X0,k2_xboole_0(X1,k1_tarski(X1))) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3734,c_1532])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1530,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),X1) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2851,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(k2_xboole_0(X0,k1_tarski(X0)),X1) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1530,c_1537])).

cnf(c_64,plain,
    ( v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_585,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(X2,X3)
    | ~ v3_ordinal1(X3)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1)
    | X1 != X3
    | k2_xboole_0(X0,k1_tarski(X0)) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_13])).

cnf(c_586,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k2_xboole_0(X0,k1_tarski(X0)),X1)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) ),
    inference(unflattening,[status(thm)],[c_585])).

cnf(c_587,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(k2_xboole_0(X0,k1_tarski(X0)),X1) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_586])).

cnf(c_3863,plain,
    ( v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top
    | r1_tarski(k2_xboole_0(X0,k1_tarski(X0)),X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2851,c_64,c_587])).

cnf(c_3864,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(k2_xboole_0(X0,k1_tarski(X0)),X1) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_3863])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1540,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3872,plain,
    ( k2_xboole_0(X0,k1_tarski(X0)) = X1
    | r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,k2_xboole_0(X0,k1_tarski(X0))) != iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3864,c_1540])).

cnf(c_5489,plain,
    ( k2_xboole_0(X0,k1_tarski(X0)) = X1
    | r2_hidden(X0,X1) != iProver_top
    | r1_ordinal1(X1,X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5482,c_3872])).

cnf(c_5581,plain,
    ( k2_xboole_0(sK0(X0),k1_tarski(sK0(X0))) = X0
    | r1_ordinal1(X0,sK0(X0)) != iProver_top
    | v4_ordinal1(X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(sK0(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1526,c_5489])).

cnf(c_18,plain,
    ( v4_ordinal1(X0)
    | ~ v3_ordinal1(X0)
    | v3_ordinal1(sK0(X0)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_43,plain,
    ( v4_ordinal1(X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(sK0(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_46,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v4_ordinal1(X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_10,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X1,X0)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1533,plain,
    ( X0 = X1
    | r2_hidden(X1,X0) = iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3900,plain,
    ( X0 = X1
    | r2_hidden(X0,X1) = iProver_top
    | r1_ordinal1(X1,X0) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1533,c_2508])).

cnf(c_9,plain,
    ( k2_xboole_0(X0,k1_tarski(X0)) != X0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_12,plain,
    ( r2_hidden(X0,X1)
    | ~ r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_513,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k2_xboole_0(X3,k1_tarski(X3)))
    | ~ v3_ordinal1(X3)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1)
    | X1 != X3
    | k2_xboole_0(X0,k1_tarski(X0)) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_12])).

cnf(c_514,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),k2_xboole_0(X1,k1_tarski(X1)))
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) ),
    inference(unflattening,[status(thm)],[c_513])).

cnf(c_518,plain,
    ( ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0)
    | ~ r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),k2_xboole_0(X1,k1_tarski(X1)))
    | r2_hidden(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_514,c_11])).

cnf(c_519,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),k2_xboole_0(X1,k1_tarski(X1)))
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(renaming,[status(thm)],[c_518])).

cnf(c_520,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),k2_xboole_0(X1,k1_tarski(X1))) != iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_519])).

cnf(c_1121,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1748,plain,
    ( X0 != X1
    | k2_xboole_0(X0,k1_tarski(X0)) != X1
    | k2_xboole_0(X0,k1_tarski(X0)) = X0 ),
    inference(instantiation,[status(thm)],[c_1121])).

cnf(c_1875,plain,
    ( ~ r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),X1)
    | r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),k2_xboole_0(X1,k1_tarski(X1))) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1876,plain,
    ( r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),X1) != iProver_top
    | r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),k2_xboole_0(X1,k1_tarski(X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1875])).

cnf(c_3906,plain,
    ( k2_xboole_0(X0,k1_tarski(X0)) = X1
    | r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),X1) = iProver_top
    | r1_ordinal1(X1,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1533,c_1528])).

cnf(c_4332,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r1_ordinal1(X1,X0) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3900,c_64,c_9,c_520,c_1748,c_1876,c_3906])).

cnf(c_4333,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r1_ordinal1(X1,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_4332])).

cnf(c_16,plain,
    ( ~ r2_hidden(k2_xboole_0(sK0(X0),k1_tarski(sK0(X0))),X0)
    | v4_ordinal1(X0)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1527,plain,
    ( r2_hidden(k2_xboole_0(sK0(X0),k1_tarski(sK0(X0))),X0) != iProver_top
    | v4_ordinal1(X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_4344,plain,
    ( r1_ordinal1(X0,k2_xboole_0(sK0(X0),k1_tarski(sK0(X0)))) = iProver_top
    | v4_ordinal1(X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(k2_xboole_0(sK0(X0),k1_tarski(sK0(X0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4333,c_1527])).

cnf(c_5286,plain,
    ( r1_tarski(X0,k2_xboole_0(sK0(X0),k1_tarski(sK0(X0)))) = iProver_top
    | v4_ordinal1(X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(k2_xboole_0(sK0(X0),k1_tarski(sK0(X0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4344,c_1537])).

cnf(c_5447,plain,
    ( k2_xboole_0(sK0(X0),k1_tarski(sK0(X0))) = X0
    | r2_hidden(sK0(X0),X0) != iProver_top
    | v4_ordinal1(X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(k2_xboole_0(sK0(X0),k1_tarski(sK0(X0)))) != iProver_top
    | v3_ordinal1(sK0(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5286,c_3872])).

cnf(c_6294,plain,
    ( v3_ordinal1(k2_xboole_0(sK0(X0),k1_tarski(sK0(X0))))
    | ~ v3_ordinal1(sK0(X0)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_6295,plain,
    ( v3_ordinal1(k2_xboole_0(sK0(X0),k1_tarski(sK0(X0)))) = iProver_top
    | v3_ordinal1(sK0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6294])).

cnf(c_6775,plain,
    ( v3_ordinal1(X0) != iProver_top
    | v4_ordinal1(X0) = iProver_top
    | k2_xboole_0(sK0(X0),k1_tarski(sK0(X0))) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5581,c_43,c_46,c_5447,c_6295])).

cnf(c_6776,plain,
    ( k2_xboole_0(sK0(X0),k1_tarski(sK0(X0))) = X0
    | v4_ordinal1(X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_6775])).

cnf(c_6786,plain,
    ( k2_xboole_0(sK0(sK1),k1_tarski(sK0(sK1))) = sK1
    | v4_ordinal1(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1518,c_6776])).

cnf(c_23,negated_conjecture,
    ( ~ v4_ordinal1(sK1)
    | k2_xboole_0(sK2,k1_tarski(sK2)) = sK1 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1521,plain,
    ( k2_xboole_0(sK2,k1_tarski(sK2)) = sK1
    | v4_ordinal1(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_7063,plain,
    ( k2_xboole_0(sK0(sK1),k1_tarski(sK0(sK1))) = sK1
    | k2_xboole_0(sK2,k1_tarski(sK2)) = sK1 ),
    inference(superposition,[status(thm)],[c_6786,c_1521])).

cnf(c_53,plain,
    ( ~ r2_hidden(sK1,k2_xboole_0(sK1,k1_tarski(sK1)))
    | r1_ordinal1(sK1,sK1)
    | ~ v3_ordinal1(sK1) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_65,plain,
    ( v3_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1)))
    | ~ v3_ordinal1(sK1) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_70,plain,
    ( k2_xboole_0(sK1,k1_tarski(sK1)) != sK1 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_6,plain,
    ( r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0))) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_78,plain,
    ( r2_hidden(sK1,k2_xboole_0(sK1,k1_tarski(sK1))) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_82,plain,
    ( ~ r1_ordinal1(sK1,sK1)
    | r1_tarski(sK1,sK1)
    | ~ v3_ordinal1(sK1) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_92,plain,
    ( ~ r1_tarski(sK1,sK1)
    | sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_590,plain,
    ( ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0)
    | r1_tarski(k2_xboole_0(X0,k1_tarski(X0)),X1)
    | ~ r2_hidden(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_586,c_11])).

cnf(c_591,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k2_xboole_0(X0,k1_tarski(X0)),X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(renaming,[status(thm)],[c_590])).

cnf(c_593,plain,
    ( ~ r2_hidden(sK1,sK1)
    | r1_tarski(k2_xboole_0(sK1,k1_tarski(sK1)),sK1)
    | ~ v3_ordinal1(sK1) ),
    inference(instantiation,[status(thm)],[c_591])).

cnf(c_1816,plain,
    ( X0 != k2_xboole_0(X0,k1_tarski(X0))
    | k2_xboole_0(X0,k1_tarski(X0)) = X0
    | k2_xboole_0(X0,k1_tarski(X0)) != k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(instantiation,[status(thm)],[c_1748])).

cnf(c_1818,plain,
    ( k2_xboole_0(sK1,k1_tarski(sK1)) != k2_xboole_0(sK1,k1_tarski(sK1))
    | k2_xboole_0(sK1,k1_tarski(sK1)) = sK1
    | sK1 != k2_xboole_0(sK1,k1_tarski(sK1)) ),
    inference(instantiation,[status(thm)],[c_1816])).

cnf(c_1120,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1817,plain,
    ( k2_xboole_0(X0,k1_tarski(X0)) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(instantiation,[status(thm)],[c_1120])).

cnf(c_1819,plain,
    ( k2_xboole_0(sK1,k1_tarski(sK1)) = k2_xboole_0(sK1,k1_tarski(sK1)) ),
    inference(instantiation,[status(thm)],[c_1817])).

cnf(c_1837,plain,
    ( ~ r1_ordinal1(X0,k2_xboole_0(X0,k1_tarski(X0)))
    | r1_tarski(X0,k2_xboole_0(X0,k1_tarski(X0)))
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1839,plain,
    ( ~ r1_ordinal1(sK1,k2_xboole_0(sK1,k1_tarski(sK1)))
    | r1_tarski(sK1,k2_xboole_0(sK1,k1_tarski(sK1)))
    | ~ v3_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1)))
    | ~ v3_ordinal1(sK1) ),
    inference(instantiation,[status(thm)],[c_1837])).

cnf(c_1884,plain,
    ( ~ r1_tarski(X0,k2_xboole_0(X1,k1_tarski(X1)))
    | ~ r1_tarski(k2_xboole_0(X1,k1_tarski(X1)),X0)
    | X0 = k2_xboole_0(X1,k1_tarski(X1)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1886,plain,
    ( ~ r1_tarski(k2_xboole_0(sK1,k1_tarski(sK1)),sK1)
    | ~ r1_tarski(sK1,k2_xboole_0(sK1,k1_tarski(sK1)))
    | sK1 = k2_xboole_0(sK1,k1_tarski(sK1)) ),
    inference(instantiation,[status(thm)],[c_1884])).

cnf(c_1899,plain,
    ( X0 != X1
    | X0 = k2_xboole_0(X2,k1_tarski(X2))
    | k2_xboole_0(X2,k1_tarski(X2)) != X1 ),
    inference(instantiation,[status(thm)],[c_1121])).

cnf(c_2304,plain,
    ( X0 = k2_xboole_0(sK2,k1_tarski(sK2))
    | X0 != sK1
    | k2_xboole_0(sK2,k1_tarski(sK2)) != sK1 ),
    inference(instantiation,[status(thm)],[c_1899])).

cnf(c_2306,plain,
    ( k2_xboole_0(sK2,k1_tarski(sK2)) != sK1
    | sK1 = k2_xboole_0(sK2,k1_tarski(sK2))
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_2304])).

cnf(c_5,plain,
    ( r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1536,plain,
    ( r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2543,plain,
    ( r1_ordinal1(X0,k2_xboole_0(X0,k1_tarski(X0))) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1536,c_2508])).

cnf(c_2572,plain,
    ( r1_ordinal1(X0,k2_xboole_0(X0,k1_tarski(X0)))
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2543])).

cnf(c_2574,plain,
    ( r1_ordinal1(sK1,k2_xboole_0(sK1,k1_tarski(sK1)))
    | ~ v3_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1)))
    | ~ v3_ordinal1(sK1) ),
    inference(instantiation,[status(thm)],[c_2572])).

cnf(c_1123,plain,
    ( ~ v3_ordinal1(X0)
    | v3_ordinal1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2619,plain,
    ( ~ v3_ordinal1(X0)
    | v3_ordinal1(k2_xboole_0(sK2,k1_tarski(sK2)))
    | k2_xboole_0(sK2,k1_tarski(sK2)) != X0 ),
    inference(instantiation,[status(thm)],[c_1123])).

cnf(c_2621,plain,
    ( v3_ordinal1(k2_xboole_0(sK2,k1_tarski(sK2)))
    | ~ v3_ordinal1(sK1)
    | k2_xboole_0(sK2,k1_tarski(sK2)) != sK1 ),
    inference(instantiation,[status(thm)],[c_2619])).

cnf(c_4003,plain,
    ( r2_hidden(sK2,k2_xboole_0(sK2,k1_tarski(sK2))) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1126,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1798,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k2_xboole_0(X3,k1_tarski(X3)))
    | X0 != X2
    | X1 != k2_xboole_0(X3,k1_tarski(X3)) ),
    inference(instantiation,[status(thm)],[c_1126])).

cnf(c_2443,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k2_xboole_0(sK2,k1_tarski(sK2)))
    | X0 != X2
    | X1 != k2_xboole_0(sK2,k1_tarski(sK2)) ),
    inference(instantiation,[status(thm)],[c_1798])).

cnf(c_4467,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k2_xboole_0(sK2,k1_tarski(sK2)),k2_xboole_0(sK2,k1_tarski(sK2)))
    | X0 != k2_xboole_0(sK2,k1_tarski(sK2))
    | X1 != k2_xboole_0(sK2,k1_tarski(sK2)) ),
    inference(instantiation,[status(thm)],[c_2443])).

cnf(c_4471,plain,
    ( ~ r2_hidden(k2_xboole_0(sK2,k1_tarski(sK2)),k2_xboole_0(sK2,k1_tarski(sK2)))
    | r2_hidden(sK1,sK1)
    | sK1 != k2_xboole_0(sK2,k1_tarski(sK2)) ),
    inference(instantiation,[status(thm)],[c_4467])).

cnf(c_1127,plain,
    ( ~ v4_ordinal1(X0)
    | v4_ordinal1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2337,plain,
    ( ~ v4_ordinal1(X0)
    | v4_ordinal1(k2_xboole_0(X1,k1_tarski(X1)))
    | k2_xboole_0(X1,k1_tarski(X1)) != X0 ),
    inference(instantiation,[status(thm)],[c_1127])).

cnf(c_5984,plain,
    ( v4_ordinal1(k2_xboole_0(sK2,k1_tarski(sK2)))
    | ~ v4_ordinal1(sK1)
    | k2_xboole_0(sK2,k1_tarski(sK2)) != sK1 ),
    inference(instantiation,[status(thm)],[c_2337])).

cnf(c_6811,plain,
    ( v4_ordinal1(sK1)
    | k2_xboole_0(sK0(sK1),k1_tarski(sK0(sK1))) = sK1 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6786])).

cnf(c_25,negated_conjecture,
    ( ~ v4_ordinal1(sK1)
    | v3_ordinal1(sK2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1519,plain,
    ( v4_ordinal1(sK1) != iProver_top
    | v3_ordinal1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_7064,plain,
    ( k2_xboole_0(sK0(sK1),k1_tarski(sK0(sK1))) = sK1
    | v3_ordinal1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_6786,c_1519])).

cnf(c_7073,plain,
    ( v3_ordinal1(sK2)
    | k2_xboole_0(sK0(sK1),k1_tarski(sK0(sK1))) = sK1 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_7064])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),X1)
    | ~ v4_ordinal1(X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1773,plain,
    ( ~ r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0)))
    | r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),k2_xboole_0(X0,k1_tarski(X0)))
    | ~ v4_ordinal1(k2_xboole_0(X0,k1_tarski(X0)))
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_7325,plain,
    ( r2_hidden(k2_xboole_0(sK2,k1_tarski(sK2)),k2_xboole_0(sK2,k1_tarski(sK2)))
    | ~ r2_hidden(sK2,k2_xboole_0(sK2,k1_tarski(sK2)))
    | ~ v4_ordinal1(k2_xboole_0(sK2,k1_tarski(sK2)))
    | ~ v3_ordinal1(k2_xboole_0(sK2,k1_tarski(sK2)))
    | ~ v3_ordinal1(sK2) ),
    inference(instantiation,[status(thm)],[c_1773])).

cnf(c_7443,plain,
    ( k2_xboole_0(sK0(sK1),k1_tarski(sK0(sK1))) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7063,c_26,c_53,c_65,c_70,c_78,c_82,c_92,c_593,c_1818,c_1819,c_1839,c_1886,c_2306,c_2574,c_2621,c_4003,c_4471,c_5984,c_6811,c_7073,c_7325])).

cnf(c_1524,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),X1) = iProver_top
    | v4_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2976,plain,
    ( v3_ordinal1(X0) != iProver_top
    | r1_ordinal1(X0,k2_xboole_0(X0,k1_tarski(X0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2543,c_64])).

cnf(c_2977,plain,
    ( r1_ordinal1(X0,k2_xboole_0(X0,k1_tarski(X0))) = iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2976])).

cnf(c_2984,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,k1_tarski(X0))) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2977,c_1537])).

cnf(c_1838,plain,
    ( r1_ordinal1(X0,k2_xboole_0(X0,k1_tarski(X0))) != iProver_top
    | r1_tarski(X0,k2_xboole_0(X0,k1_tarski(X0))) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1837])).

cnf(c_3117,plain,
    ( v3_ordinal1(X0) != iProver_top
    | r1_tarski(X0,k2_xboole_0(X0,k1_tarski(X0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2984,c_64])).

cnf(c_3118,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,k1_tarski(X0))) = iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3117])).

cnf(c_3126,plain,
    ( k2_xboole_0(X0,k1_tarski(X0)) = X0
    | r1_tarski(k2_xboole_0(X0,k1_tarski(X0)),X0) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3118,c_1540])).

cnf(c_3137,plain,
    ( r1_tarski(k2_xboole_0(X0,k1_tarski(X0)),X0) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3126,c_9])).

cnf(c_3873,plain,
    ( r2_hidden(X0,X0) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3864,c_3137])).

cnf(c_4494,plain,
    ( r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0))) != iProver_top
    | v4_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) != iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1524,c_3873])).

cnf(c_77,plain,
    ( r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_4835,plain,
    ( v3_ordinal1(X0) != iProver_top
    | v4_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4494,c_64,c_77])).

cnf(c_4836,plain,
    ( v4_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4835])).

cnf(c_7458,plain,
    ( v4_ordinal1(sK1) != iProver_top
    | v3_ordinal1(sK0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7443,c_4836])).

cnf(c_20,negated_conjecture,
    ( v4_ordinal1(sK1)
    | ~ v3_ordinal1(X0)
    | k2_xboole_0(X0,k1_tarski(X0)) != sK1 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1523,plain,
    ( k2_xboole_0(X0,k1_tarski(X0)) != sK1
    | v4_ordinal1(sK1) = iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_7477,plain,
    ( v4_ordinal1(sK1) = iProver_top
    | v3_ordinal1(sK0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7443,c_1523])).

cnf(c_7657,plain,
    ( v3_ordinal1(sK0(sK1)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_7458,c_7477])).

cnf(c_7326,plain,
    ( r2_hidden(k2_xboole_0(sK2,k1_tarski(sK2)),k2_xboole_0(sK2,k1_tarski(sK2))) = iProver_top
    | r2_hidden(sK2,k2_xboole_0(sK2,k1_tarski(sK2))) != iProver_top
    | v4_ordinal1(k2_xboole_0(sK2,k1_tarski(sK2))) != iProver_top
    | v3_ordinal1(k2_xboole_0(sK2,k1_tarski(sK2))) != iProver_top
    | v3_ordinal1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7325])).

cnf(c_5985,plain,
    ( k2_xboole_0(sK2,k1_tarski(sK2)) != sK1
    | v4_ordinal1(k2_xboole_0(sK2,k1_tarski(sK2))) = iProver_top
    | v4_ordinal1(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5984])).

cnf(c_4470,plain,
    ( X0 != k2_xboole_0(sK2,k1_tarski(sK2))
    | X1 != k2_xboole_0(sK2,k1_tarski(sK2))
    | r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k2_xboole_0(sK2,k1_tarski(sK2)),k2_xboole_0(sK2,k1_tarski(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4467])).

cnf(c_4472,plain,
    ( sK1 != k2_xboole_0(sK2,k1_tarski(sK2))
    | r2_hidden(k2_xboole_0(sK2,k1_tarski(sK2)),k2_xboole_0(sK2,k1_tarski(sK2))) != iProver_top
    | r2_hidden(sK1,sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_4470])).

cnf(c_4004,plain,
    ( r2_hidden(sK2,k2_xboole_0(sK2,k1_tarski(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4003])).

cnf(c_2624,plain,
    ( v3_ordinal1(k2_xboole_0(sK2,k1_tarski(sK2)))
    | ~ v3_ordinal1(sK2) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2625,plain,
    ( v3_ordinal1(k2_xboole_0(sK2,k1_tarski(sK2))) = iProver_top
    | v3_ordinal1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2624])).

cnf(c_2573,plain,
    ( r1_ordinal1(sK1,k2_xboole_0(sK1,k1_tarski(sK1))) = iProver_top
    | v3_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1))) != iProver_top
    | v3_ordinal1(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2543])).

cnf(c_1885,plain,
    ( X0 = k2_xboole_0(X1,k1_tarski(X1))
    | r1_tarski(X0,k2_xboole_0(X1,k1_tarski(X1))) != iProver_top
    | r1_tarski(k2_xboole_0(X1,k1_tarski(X1)),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1884])).

cnf(c_1887,plain,
    ( sK1 = k2_xboole_0(sK1,k1_tarski(sK1))
    | r1_tarski(k2_xboole_0(sK1,k1_tarski(sK1)),sK1) != iProver_top
    | r1_tarski(sK1,k2_xboole_0(sK1,k1_tarski(sK1))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1885])).

cnf(c_1840,plain,
    ( r1_ordinal1(sK1,k2_xboole_0(sK1,k1_tarski(sK1))) != iProver_top
    | r1_tarski(sK1,k2_xboole_0(sK1,k1_tarski(sK1))) = iProver_top
    | v3_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1))) != iProver_top
    | v3_ordinal1(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1838])).

cnf(c_592,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(k2_xboole_0(X0,k1_tarski(X0)),X1) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_591])).

cnf(c_594,plain,
    ( r2_hidden(sK1,sK1) != iProver_top
    | r1_tarski(k2_xboole_0(sK1,k1_tarski(sK1)),sK1) = iProver_top
    | v3_ordinal1(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_592])).

cnf(c_355,plain,
    ( ~ v3_ordinal1(X0)
    | v3_ordinal1(sK0(X0))
    | k2_xboole_0(sK2,k1_tarski(sK2)) = sK1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_23])).

cnf(c_356,plain,
    ( v3_ordinal1(sK0(sK1))
    | ~ v3_ordinal1(sK1)
    | k2_xboole_0(sK2,k1_tarski(sK2)) = sK1 ),
    inference(unflattening,[status(thm)],[c_355])).

cnf(c_358,plain,
    ( v3_ordinal1(sK0(sK1))
    | k2_xboole_0(sK2,k1_tarski(sK2)) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_356,c_26])).

cnf(c_360,plain,
    ( k2_xboole_0(sK2,k1_tarski(sK2)) = sK1
    | v3_ordinal1(sK0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_358])).

cnf(c_341,plain,
    ( ~ v3_ordinal1(X0)
    | v3_ordinal1(sK0(X0))
    | v3_ordinal1(sK2)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_25])).

cnf(c_342,plain,
    ( v3_ordinal1(sK0(sK1))
    | v3_ordinal1(sK2)
    | ~ v3_ordinal1(sK1) ),
    inference(unflattening,[status(thm)],[c_341])).

cnf(c_344,plain,
    ( v3_ordinal1(sK2)
    | v3_ordinal1(sK0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_342,c_26])).

cnf(c_345,plain,
    ( v3_ordinal1(sK0(sK1))
    | v3_ordinal1(sK2) ),
    inference(renaming,[status(thm)],[c_344])).

cnf(c_346,plain,
    ( v3_ordinal1(sK0(sK1)) = iProver_top
    | v3_ordinal1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_345])).

cnf(c_66,plain,
    ( v3_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1))) = iProver_top
    | v3_ordinal1(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_64])).

cnf(c_45,plain,
    ( v4_ordinal1(sK1) = iProver_top
    | v3_ordinal1(sK0(sK1)) = iProver_top
    | v3_ordinal1(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_43])).

cnf(c_27,plain,
    ( v3_ordinal1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7657,c_7326,c_5985,c_4472,c_4004,c_2625,c_2573,c_2306,c_1887,c_1840,c_1819,c_1818,c_594,c_360,c_346,c_92,c_82,c_78,c_70,c_66,c_53,c_45,c_27,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:31:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.49/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.49/1.01  
% 2.49/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.49/1.01  
% 2.49/1.01  ------  iProver source info
% 2.49/1.01  
% 2.49/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.49/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.49/1.01  git: non_committed_changes: false
% 2.49/1.01  git: last_make_outside_of_git: false
% 2.49/1.01  
% 2.49/1.01  ------ 
% 2.49/1.01  
% 2.49/1.01  ------ Input Options
% 2.49/1.01  
% 2.49/1.01  --out_options                           all
% 2.49/1.01  --tptp_safe_out                         true
% 2.49/1.01  --problem_path                          ""
% 2.49/1.01  --include_path                          ""
% 2.49/1.01  --clausifier                            res/vclausify_rel
% 2.49/1.01  --clausifier_options                    --mode clausify
% 2.49/1.01  --stdin                                 false
% 2.49/1.01  --stats_out                             all
% 2.49/1.01  
% 2.49/1.01  ------ General Options
% 2.49/1.01  
% 2.49/1.01  --fof                                   false
% 2.49/1.01  --time_out_real                         305.
% 2.49/1.01  --time_out_virtual                      -1.
% 2.49/1.01  --symbol_type_check                     false
% 2.49/1.01  --clausify_out                          false
% 2.49/1.01  --sig_cnt_out                           false
% 2.49/1.01  --trig_cnt_out                          false
% 2.49/1.01  --trig_cnt_out_tolerance                1.
% 2.49/1.01  --trig_cnt_out_sk_spl                   false
% 2.49/1.01  --abstr_cl_out                          false
% 2.49/1.01  
% 2.49/1.01  ------ Global Options
% 2.49/1.01  
% 2.49/1.01  --schedule                              default
% 2.49/1.01  --add_important_lit                     false
% 2.49/1.01  --prop_solver_per_cl                    1000
% 2.49/1.01  --min_unsat_core                        false
% 2.49/1.01  --soft_assumptions                      false
% 2.49/1.01  --soft_lemma_size                       3
% 2.49/1.01  --prop_impl_unit_size                   0
% 2.49/1.01  --prop_impl_unit                        []
% 2.49/1.01  --share_sel_clauses                     true
% 2.49/1.01  --reset_solvers                         false
% 2.49/1.01  --bc_imp_inh                            [conj_cone]
% 2.49/1.01  --conj_cone_tolerance                   3.
% 2.49/1.01  --extra_neg_conj                        none
% 2.49/1.01  --large_theory_mode                     true
% 2.49/1.01  --prolific_symb_bound                   200
% 2.49/1.01  --lt_threshold                          2000
% 2.49/1.01  --clause_weak_htbl                      true
% 2.49/1.01  --gc_record_bc_elim                     false
% 2.49/1.01  
% 2.49/1.01  ------ Preprocessing Options
% 2.49/1.01  
% 2.49/1.01  --preprocessing_flag                    true
% 2.49/1.01  --time_out_prep_mult                    0.1
% 2.49/1.01  --splitting_mode                        input
% 2.49/1.01  --splitting_grd                         true
% 2.49/1.01  --splitting_cvd                         false
% 2.49/1.01  --splitting_cvd_svl                     false
% 2.49/1.01  --splitting_nvd                         32
% 2.49/1.01  --sub_typing                            true
% 2.49/1.01  --prep_gs_sim                           true
% 2.49/1.01  --prep_unflatten                        true
% 2.49/1.01  --prep_res_sim                          true
% 2.49/1.01  --prep_upred                            true
% 2.49/1.01  --prep_sem_filter                       exhaustive
% 2.49/1.01  --prep_sem_filter_out                   false
% 2.49/1.01  --pred_elim                             true
% 2.49/1.01  --res_sim_input                         true
% 2.49/1.01  --eq_ax_congr_red                       true
% 2.49/1.01  --pure_diseq_elim                       true
% 2.49/1.01  --brand_transform                       false
% 2.49/1.01  --non_eq_to_eq                          false
% 2.49/1.01  --prep_def_merge                        true
% 2.49/1.01  --prep_def_merge_prop_impl              false
% 2.49/1.01  --prep_def_merge_mbd                    true
% 2.49/1.01  --prep_def_merge_tr_red                 false
% 2.49/1.01  --prep_def_merge_tr_cl                  false
% 2.49/1.01  --smt_preprocessing                     true
% 2.49/1.01  --smt_ac_axioms                         fast
% 2.49/1.01  --preprocessed_out                      false
% 2.49/1.01  --preprocessed_stats                    false
% 2.49/1.01  
% 2.49/1.01  ------ Abstraction refinement Options
% 2.49/1.01  
% 2.49/1.01  --abstr_ref                             []
% 2.49/1.01  --abstr_ref_prep                        false
% 2.49/1.01  --abstr_ref_until_sat                   false
% 2.49/1.01  --abstr_ref_sig_restrict                funpre
% 2.49/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.49/1.01  --abstr_ref_under                       []
% 2.49/1.01  
% 2.49/1.01  ------ SAT Options
% 2.49/1.01  
% 2.49/1.01  --sat_mode                              false
% 2.49/1.01  --sat_fm_restart_options                ""
% 2.49/1.01  --sat_gr_def                            false
% 2.49/1.01  --sat_epr_types                         true
% 2.49/1.01  --sat_non_cyclic_types                  false
% 2.49/1.01  --sat_finite_models                     false
% 2.49/1.01  --sat_fm_lemmas                         false
% 2.49/1.01  --sat_fm_prep                           false
% 2.49/1.01  --sat_fm_uc_incr                        true
% 2.49/1.01  --sat_out_model                         small
% 2.49/1.01  --sat_out_clauses                       false
% 2.49/1.01  
% 2.49/1.01  ------ QBF Options
% 2.49/1.01  
% 2.49/1.01  --qbf_mode                              false
% 2.49/1.01  --qbf_elim_univ                         false
% 2.49/1.01  --qbf_dom_inst                          none
% 2.49/1.01  --qbf_dom_pre_inst                      false
% 2.49/1.01  --qbf_sk_in                             false
% 2.49/1.01  --qbf_pred_elim                         true
% 2.49/1.01  --qbf_split                             512
% 2.49/1.01  
% 2.49/1.01  ------ BMC1 Options
% 2.49/1.01  
% 2.49/1.01  --bmc1_incremental                      false
% 2.49/1.01  --bmc1_axioms                           reachable_all
% 2.49/1.01  --bmc1_min_bound                        0
% 2.49/1.01  --bmc1_max_bound                        -1
% 2.49/1.01  --bmc1_max_bound_default                -1
% 2.49/1.01  --bmc1_symbol_reachability              true
% 2.49/1.01  --bmc1_property_lemmas                  false
% 2.49/1.01  --bmc1_k_induction                      false
% 2.49/1.01  --bmc1_non_equiv_states                 false
% 2.49/1.01  --bmc1_deadlock                         false
% 2.49/1.01  --bmc1_ucm                              false
% 2.49/1.01  --bmc1_add_unsat_core                   none
% 2.49/1.01  --bmc1_unsat_core_children              false
% 2.49/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.49/1.01  --bmc1_out_stat                         full
% 2.49/1.01  --bmc1_ground_init                      false
% 2.49/1.01  --bmc1_pre_inst_next_state              false
% 2.49/1.01  --bmc1_pre_inst_state                   false
% 2.49/1.01  --bmc1_pre_inst_reach_state             false
% 2.49/1.01  --bmc1_out_unsat_core                   false
% 2.49/1.01  --bmc1_aig_witness_out                  false
% 2.49/1.01  --bmc1_verbose                          false
% 2.49/1.01  --bmc1_dump_clauses_tptp                false
% 2.49/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.49/1.01  --bmc1_dump_file                        -
% 2.49/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.49/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.49/1.01  --bmc1_ucm_extend_mode                  1
% 2.49/1.01  --bmc1_ucm_init_mode                    2
% 2.49/1.01  --bmc1_ucm_cone_mode                    none
% 2.49/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.49/1.01  --bmc1_ucm_relax_model                  4
% 2.49/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.49/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.49/1.01  --bmc1_ucm_layered_model                none
% 2.49/1.01  --bmc1_ucm_max_lemma_size               10
% 2.49/1.01  
% 2.49/1.01  ------ AIG Options
% 2.49/1.01  
% 2.49/1.01  --aig_mode                              false
% 2.49/1.01  
% 2.49/1.01  ------ Instantiation Options
% 2.49/1.01  
% 2.49/1.01  --instantiation_flag                    true
% 2.49/1.01  --inst_sos_flag                         false
% 2.49/1.01  --inst_sos_phase                        true
% 2.49/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.49/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.49/1.01  --inst_lit_sel_side                     num_symb
% 2.49/1.01  --inst_solver_per_active                1400
% 2.49/1.01  --inst_solver_calls_frac                1.
% 2.49/1.01  --inst_passive_queue_type               priority_queues
% 2.49/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.49/1.01  --inst_passive_queues_freq              [25;2]
% 2.49/1.01  --inst_dismatching                      true
% 2.49/1.01  --inst_eager_unprocessed_to_passive     true
% 2.49/1.01  --inst_prop_sim_given                   true
% 2.49/1.01  --inst_prop_sim_new                     false
% 2.49/1.01  --inst_subs_new                         false
% 2.49/1.01  --inst_eq_res_simp                      false
% 2.49/1.01  --inst_subs_given                       false
% 2.49/1.01  --inst_orphan_elimination               true
% 2.49/1.01  --inst_learning_loop_flag               true
% 2.49/1.01  --inst_learning_start                   3000
% 2.49/1.01  --inst_learning_factor                  2
% 2.49/1.01  --inst_start_prop_sim_after_learn       3
% 2.49/1.01  --inst_sel_renew                        solver
% 2.49/1.01  --inst_lit_activity_flag                true
% 2.49/1.01  --inst_restr_to_given                   false
% 2.49/1.01  --inst_activity_threshold               500
% 2.49/1.01  --inst_out_proof                        true
% 2.49/1.01  
% 2.49/1.01  ------ Resolution Options
% 2.49/1.01  
% 2.49/1.01  --resolution_flag                       true
% 2.49/1.01  --res_lit_sel                           adaptive
% 2.49/1.01  --res_lit_sel_side                      none
% 2.49/1.01  --res_ordering                          kbo
% 2.49/1.01  --res_to_prop_solver                    active
% 2.49/1.01  --res_prop_simpl_new                    false
% 2.49/1.01  --res_prop_simpl_given                  true
% 2.49/1.01  --res_passive_queue_type                priority_queues
% 2.49/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.49/1.01  --res_passive_queues_freq               [15;5]
% 2.49/1.01  --res_forward_subs                      full
% 2.49/1.01  --res_backward_subs                     full
% 2.49/1.01  --res_forward_subs_resolution           true
% 2.49/1.01  --res_backward_subs_resolution          true
% 2.49/1.01  --res_orphan_elimination                true
% 2.49/1.01  --res_time_limit                        2.
% 2.49/1.01  --res_out_proof                         true
% 2.49/1.01  
% 2.49/1.01  ------ Superposition Options
% 2.49/1.01  
% 2.49/1.01  --superposition_flag                    true
% 2.49/1.01  --sup_passive_queue_type                priority_queues
% 2.49/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.49/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.49/1.01  --demod_completeness_check              fast
% 2.49/1.01  --demod_use_ground                      true
% 2.49/1.01  --sup_to_prop_solver                    passive
% 2.49/1.01  --sup_prop_simpl_new                    true
% 2.49/1.01  --sup_prop_simpl_given                  true
% 2.49/1.01  --sup_fun_splitting                     false
% 2.49/1.01  --sup_smt_interval                      50000
% 2.49/1.01  
% 2.49/1.01  ------ Superposition Simplification Setup
% 2.49/1.01  
% 2.49/1.01  --sup_indices_passive                   []
% 2.49/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.49/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.49/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.49/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.49/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.49/1.01  --sup_full_bw                           [BwDemod]
% 2.49/1.01  --sup_immed_triv                        [TrivRules]
% 2.49/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.49/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.49/1.01  --sup_immed_bw_main                     []
% 2.49/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.49/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.49/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.49/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.49/1.01  
% 2.49/1.01  ------ Combination Options
% 2.49/1.01  
% 2.49/1.01  --comb_res_mult                         3
% 2.49/1.01  --comb_sup_mult                         2
% 2.49/1.01  --comb_inst_mult                        10
% 2.49/1.01  
% 2.49/1.01  ------ Debug Options
% 2.49/1.01  
% 2.49/1.01  --dbg_backtrace                         false
% 2.49/1.01  --dbg_dump_prop_clauses                 false
% 2.49/1.01  --dbg_dump_prop_clauses_file            -
% 2.49/1.01  --dbg_out_stat                          false
% 2.49/1.01  ------ Parsing...
% 2.49/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.49/1.01  
% 2.49/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.49/1.01  
% 2.49/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.49/1.01  
% 2.49/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.49/1.01  ------ Proving...
% 2.49/1.01  ------ Problem Properties 
% 2.49/1.01  
% 2.49/1.01  
% 2.49/1.01  clauses                                 24
% 2.49/1.01  conjectures                             6
% 2.49/1.01  EPR                                     7
% 2.49/1.01  Horn                                    20
% 2.49/1.01  unary                                   4
% 2.49/1.01  binary                                  4
% 2.49/1.01  lits                                    70
% 2.49/1.01  lits eq                                 9
% 2.49/1.01  fd_pure                                 0
% 2.49/1.01  fd_pseudo                               0
% 2.49/1.01  fd_cond                                 0
% 2.49/1.01  fd_pseudo_cond                          3
% 2.49/1.01  AC symbols                              0
% 2.49/1.01  
% 2.49/1.01  ------ Schedule dynamic 5 is on 
% 2.49/1.01  
% 2.49/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.49/1.01  
% 2.49/1.01  
% 2.49/1.01  ------ 
% 2.49/1.01  Current options:
% 2.49/1.01  ------ 
% 2.49/1.01  
% 2.49/1.01  ------ Input Options
% 2.49/1.01  
% 2.49/1.01  --out_options                           all
% 2.49/1.01  --tptp_safe_out                         true
% 2.49/1.01  --problem_path                          ""
% 2.49/1.01  --include_path                          ""
% 2.49/1.01  --clausifier                            res/vclausify_rel
% 2.49/1.01  --clausifier_options                    --mode clausify
% 2.49/1.01  --stdin                                 false
% 2.49/1.01  --stats_out                             all
% 2.49/1.01  
% 2.49/1.01  ------ General Options
% 2.49/1.01  
% 2.49/1.01  --fof                                   false
% 2.49/1.01  --time_out_real                         305.
% 2.49/1.01  --time_out_virtual                      -1.
% 2.49/1.01  --symbol_type_check                     false
% 2.49/1.01  --clausify_out                          false
% 2.49/1.01  --sig_cnt_out                           false
% 2.49/1.01  --trig_cnt_out                          false
% 2.49/1.01  --trig_cnt_out_tolerance                1.
% 2.49/1.01  --trig_cnt_out_sk_spl                   false
% 2.49/1.01  --abstr_cl_out                          false
% 2.49/1.01  
% 2.49/1.01  ------ Global Options
% 2.49/1.01  
% 2.49/1.01  --schedule                              default
% 2.49/1.01  --add_important_lit                     false
% 2.49/1.01  --prop_solver_per_cl                    1000
% 2.49/1.01  --min_unsat_core                        false
% 2.49/1.01  --soft_assumptions                      false
% 2.49/1.01  --soft_lemma_size                       3
% 2.49/1.01  --prop_impl_unit_size                   0
% 2.49/1.01  --prop_impl_unit                        []
% 2.49/1.01  --share_sel_clauses                     true
% 2.49/1.01  --reset_solvers                         false
% 2.49/1.01  --bc_imp_inh                            [conj_cone]
% 2.49/1.01  --conj_cone_tolerance                   3.
% 2.49/1.01  --extra_neg_conj                        none
% 2.49/1.01  --large_theory_mode                     true
% 2.49/1.01  --prolific_symb_bound                   200
% 2.49/1.01  --lt_threshold                          2000
% 2.49/1.01  --clause_weak_htbl                      true
% 2.49/1.01  --gc_record_bc_elim                     false
% 2.49/1.01  
% 2.49/1.01  ------ Preprocessing Options
% 2.49/1.01  
% 2.49/1.01  --preprocessing_flag                    true
% 2.49/1.01  --time_out_prep_mult                    0.1
% 2.49/1.01  --splitting_mode                        input
% 2.49/1.01  --splitting_grd                         true
% 2.49/1.01  --splitting_cvd                         false
% 2.49/1.01  --splitting_cvd_svl                     false
% 2.49/1.01  --splitting_nvd                         32
% 2.49/1.01  --sub_typing                            true
% 2.49/1.01  --prep_gs_sim                           true
% 2.49/1.01  --prep_unflatten                        true
% 2.49/1.01  --prep_res_sim                          true
% 2.49/1.01  --prep_upred                            true
% 2.49/1.01  --prep_sem_filter                       exhaustive
% 2.49/1.01  --prep_sem_filter_out                   false
% 2.49/1.01  --pred_elim                             true
% 2.49/1.01  --res_sim_input                         true
% 2.49/1.01  --eq_ax_congr_red                       true
% 2.49/1.01  --pure_diseq_elim                       true
% 2.49/1.01  --brand_transform                       false
% 2.49/1.01  --non_eq_to_eq                          false
% 2.49/1.01  --prep_def_merge                        true
% 2.49/1.01  --prep_def_merge_prop_impl              false
% 2.49/1.01  --prep_def_merge_mbd                    true
% 2.49/1.01  --prep_def_merge_tr_red                 false
% 2.49/1.01  --prep_def_merge_tr_cl                  false
% 2.49/1.01  --smt_preprocessing                     true
% 2.49/1.01  --smt_ac_axioms                         fast
% 2.49/1.01  --preprocessed_out                      false
% 2.49/1.01  --preprocessed_stats                    false
% 2.49/1.01  
% 2.49/1.01  ------ Abstraction refinement Options
% 2.49/1.01  
% 2.49/1.01  --abstr_ref                             []
% 2.49/1.01  --abstr_ref_prep                        false
% 2.49/1.01  --abstr_ref_until_sat                   false
% 2.49/1.01  --abstr_ref_sig_restrict                funpre
% 2.49/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.49/1.01  --abstr_ref_under                       []
% 2.49/1.01  
% 2.49/1.01  ------ SAT Options
% 2.49/1.01  
% 2.49/1.01  --sat_mode                              false
% 2.49/1.01  --sat_fm_restart_options                ""
% 2.49/1.01  --sat_gr_def                            false
% 2.49/1.01  --sat_epr_types                         true
% 2.49/1.01  --sat_non_cyclic_types                  false
% 2.49/1.01  --sat_finite_models                     false
% 2.49/1.01  --sat_fm_lemmas                         false
% 2.49/1.01  --sat_fm_prep                           false
% 2.49/1.01  --sat_fm_uc_incr                        true
% 2.49/1.01  --sat_out_model                         small
% 2.49/1.01  --sat_out_clauses                       false
% 2.49/1.01  
% 2.49/1.01  ------ QBF Options
% 2.49/1.01  
% 2.49/1.01  --qbf_mode                              false
% 2.49/1.01  --qbf_elim_univ                         false
% 2.49/1.01  --qbf_dom_inst                          none
% 2.49/1.01  --qbf_dom_pre_inst                      false
% 2.49/1.01  --qbf_sk_in                             false
% 2.49/1.01  --qbf_pred_elim                         true
% 2.49/1.01  --qbf_split                             512
% 2.49/1.01  
% 2.49/1.01  ------ BMC1 Options
% 2.49/1.01  
% 2.49/1.01  --bmc1_incremental                      false
% 2.49/1.01  --bmc1_axioms                           reachable_all
% 2.49/1.01  --bmc1_min_bound                        0
% 2.49/1.01  --bmc1_max_bound                        -1
% 2.49/1.01  --bmc1_max_bound_default                -1
% 2.49/1.01  --bmc1_symbol_reachability              true
% 2.49/1.01  --bmc1_property_lemmas                  false
% 2.49/1.01  --bmc1_k_induction                      false
% 2.49/1.01  --bmc1_non_equiv_states                 false
% 2.49/1.01  --bmc1_deadlock                         false
% 2.49/1.01  --bmc1_ucm                              false
% 2.49/1.01  --bmc1_add_unsat_core                   none
% 2.49/1.01  --bmc1_unsat_core_children              false
% 2.49/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.49/1.01  --bmc1_out_stat                         full
% 2.49/1.01  --bmc1_ground_init                      false
% 2.49/1.01  --bmc1_pre_inst_next_state              false
% 2.49/1.01  --bmc1_pre_inst_state                   false
% 2.49/1.01  --bmc1_pre_inst_reach_state             false
% 2.49/1.01  --bmc1_out_unsat_core                   false
% 2.49/1.01  --bmc1_aig_witness_out                  false
% 2.49/1.01  --bmc1_verbose                          false
% 2.49/1.01  --bmc1_dump_clauses_tptp                false
% 2.49/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.49/1.01  --bmc1_dump_file                        -
% 2.49/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.49/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.49/1.01  --bmc1_ucm_extend_mode                  1
% 2.49/1.01  --bmc1_ucm_init_mode                    2
% 2.49/1.01  --bmc1_ucm_cone_mode                    none
% 2.49/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.49/1.01  --bmc1_ucm_relax_model                  4
% 2.49/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.49/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.49/1.01  --bmc1_ucm_layered_model                none
% 2.49/1.01  --bmc1_ucm_max_lemma_size               10
% 2.49/1.01  
% 2.49/1.01  ------ AIG Options
% 2.49/1.01  
% 2.49/1.01  --aig_mode                              false
% 2.49/1.01  
% 2.49/1.01  ------ Instantiation Options
% 2.49/1.01  
% 2.49/1.01  --instantiation_flag                    true
% 2.49/1.01  --inst_sos_flag                         false
% 2.49/1.01  --inst_sos_phase                        true
% 2.49/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.49/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.49/1.01  --inst_lit_sel_side                     none
% 2.49/1.01  --inst_solver_per_active                1400
% 2.49/1.01  --inst_solver_calls_frac                1.
% 2.49/1.01  --inst_passive_queue_type               priority_queues
% 2.49/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.49/1.01  --inst_passive_queues_freq              [25;2]
% 2.49/1.01  --inst_dismatching                      true
% 2.49/1.01  --inst_eager_unprocessed_to_passive     true
% 2.49/1.01  --inst_prop_sim_given                   true
% 2.49/1.01  --inst_prop_sim_new                     false
% 2.49/1.01  --inst_subs_new                         false
% 2.49/1.01  --inst_eq_res_simp                      false
% 2.49/1.01  --inst_subs_given                       false
% 2.49/1.01  --inst_orphan_elimination               true
% 2.49/1.01  --inst_learning_loop_flag               true
% 2.49/1.01  --inst_learning_start                   3000
% 2.49/1.01  --inst_learning_factor                  2
% 2.49/1.01  --inst_start_prop_sim_after_learn       3
% 2.49/1.01  --inst_sel_renew                        solver
% 2.49/1.01  --inst_lit_activity_flag                true
% 2.49/1.01  --inst_restr_to_given                   false
% 2.49/1.01  --inst_activity_threshold               500
% 2.49/1.01  --inst_out_proof                        true
% 2.49/1.01  
% 2.49/1.01  ------ Resolution Options
% 2.49/1.01  
% 2.49/1.01  --resolution_flag                       false
% 2.49/1.01  --res_lit_sel                           adaptive
% 2.49/1.01  --res_lit_sel_side                      none
% 2.49/1.01  --res_ordering                          kbo
% 2.49/1.01  --res_to_prop_solver                    active
% 2.49/1.01  --res_prop_simpl_new                    false
% 2.49/1.01  --res_prop_simpl_given                  true
% 2.49/1.01  --res_passive_queue_type                priority_queues
% 2.49/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.49/1.01  --res_passive_queues_freq               [15;5]
% 2.49/1.01  --res_forward_subs                      full
% 2.49/1.01  --res_backward_subs                     full
% 2.49/1.01  --res_forward_subs_resolution           true
% 2.49/1.01  --res_backward_subs_resolution          true
% 2.49/1.01  --res_orphan_elimination                true
% 2.49/1.01  --res_time_limit                        2.
% 2.49/1.01  --res_out_proof                         true
% 2.49/1.01  
% 2.49/1.01  ------ Superposition Options
% 2.49/1.01  
% 2.49/1.01  --superposition_flag                    true
% 2.49/1.01  --sup_passive_queue_type                priority_queues
% 2.49/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.49/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.49/1.01  --demod_completeness_check              fast
% 2.49/1.01  --demod_use_ground                      true
% 2.49/1.01  --sup_to_prop_solver                    passive
% 2.49/1.01  --sup_prop_simpl_new                    true
% 2.49/1.01  --sup_prop_simpl_given                  true
% 2.49/1.01  --sup_fun_splitting                     false
% 2.49/1.01  --sup_smt_interval                      50000
% 2.49/1.01  
% 2.49/1.01  ------ Superposition Simplification Setup
% 2.49/1.01  
% 2.49/1.01  --sup_indices_passive                   []
% 2.49/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.49/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.49/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.49/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.49/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.49/1.01  --sup_full_bw                           [BwDemod]
% 2.49/1.01  --sup_immed_triv                        [TrivRules]
% 2.49/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.49/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.49/1.01  --sup_immed_bw_main                     []
% 2.49/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.49/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.49/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.49/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.49/1.01  
% 2.49/1.01  ------ Combination Options
% 2.49/1.01  
% 2.49/1.01  --comb_res_mult                         3
% 2.49/1.01  --comb_sup_mult                         2
% 2.49/1.01  --comb_inst_mult                        10
% 2.49/1.01  
% 2.49/1.01  ------ Debug Options
% 2.49/1.01  
% 2.49/1.01  --dbg_backtrace                         false
% 2.49/1.01  --dbg_dump_prop_clauses                 false
% 2.49/1.01  --dbg_dump_prop_clauses_file            -
% 2.49/1.01  --dbg_out_stat                          false
% 2.49/1.01  
% 2.49/1.01  
% 2.49/1.01  
% 2.49/1.01  
% 2.49/1.01  ------ Proving...
% 2.49/1.01  
% 2.49/1.01  
% 2.49/1.01  % SZS status Theorem for theBenchmark.p
% 2.49/1.01  
% 2.49/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.49/1.01  
% 2.49/1.01  fof(f12,conjecture,(
% 2.49/1.01    ! [X0] : (v3_ordinal1(X0) => (~(v4_ordinal1(X0) & ? [X1] : (k1_ordinal1(X1) = X0 & v3_ordinal1(X1))) & ~(! [X1] : (v3_ordinal1(X1) => k1_ordinal1(X1) != X0) & ~v4_ordinal1(X0))))),
% 2.49/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.49/1.01  
% 2.49/1.01  fof(f13,negated_conjecture,(
% 2.49/1.01    ~! [X0] : (v3_ordinal1(X0) => (~(v4_ordinal1(X0) & ? [X1] : (k1_ordinal1(X1) = X0 & v3_ordinal1(X1))) & ~(! [X1] : (v3_ordinal1(X1) => k1_ordinal1(X1) != X0) & ~v4_ordinal1(X0))))),
% 2.49/1.01    inference(negated_conjecture,[],[f12])).
% 2.49/1.01  
% 2.49/1.01  fof(f14,plain,(
% 2.49/1.01    ~! [X0] : (v3_ordinal1(X0) => (~(v4_ordinal1(X0) & ? [X1] : (k1_ordinal1(X1) = X0 & v3_ordinal1(X1))) & ~(! [X2] : (v3_ordinal1(X2) => k1_ordinal1(X2) != X0) & ~v4_ordinal1(X0))))),
% 2.49/1.01    inference(rectify,[],[f13])).
% 2.49/1.01  
% 2.49/1.01  fof(f24,plain,(
% 2.49/1.01    ? [X0] : (((v4_ordinal1(X0) & ? [X1] : (k1_ordinal1(X1) = X0 & v3_ordinal1(X1))) | (! [X2] : (k1_ordinal1(X2) != X0 | ~v3_ordinal1(X2)) & ~v4_ordinal1(X0))) & v3_ordinal1(X0))),
% 2.49/1.01    inference(ennf_transformation,[],[f14])).
% 2.49/1.01  
% 2.49/1.01  fof(f37,plain,(
% 2.49/1.01    ( ! [X0] : (? [X1] : (k1_ordinal1(X1) = X0 & v3_ordinal1(X1)) => (k1_ordinal1(sK2) = X0 & v3_ordinal1(sK2))) )),
% 2.49/1.01    introduced(choice_axiom,[])).
% 2.49/1.01  
% 2.49/1.01  fof(f36,plain,(
% 2.49/1.01    ? [X0] : (((v4_ordinal1(X0) & ? [X1] : (k1_ordinal1(X1) = X0 & v3_ordinal1(X1))) | (! [X2] : (k1_ordinal1(X2) != X0 | ~v3_ordinal1(X2)) & ~v4_ordinal1(X0))) & v3_ordinal1(X0)) => (((v4_ordinal1(sK1) & ? [X1] : (k1_ordinal1(X1) = sK1 & v3_ordinal1(X1))) | (! [X2] : (k1_ordinal1(X2) != sK1 | ~v3_ordinal1(X2)) & ~v4_ordinal1(sK1))) & v3_ordinal1(sK1))),
% 2.49/1.01    introduced(choice_axiom,[])).
% 2.49/1.01  
% 2.49/1.01  fof(f38,plain,(
% 2.49/1.01    ((v4_ordinal1(sK1) & (k1_ordinal1(sK2) = sK1 & v3_ordinal1(sK2))) | (! [X2] : (k1_ordinal1(X2) != sK1 | ~v3_ordinal1(X2)) & ~v4_ordinal1(sK1))) & v3_ordinal1(sK1)),
% 2.49/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f24,f37,f36])).
% 2.49/1.01  
% 2.49/1.01  fof(f60,plain,(
% 2.49/1.01    v3_ordinal1(sK1)),
% 2.49/1.01    inference(cnf_transformation,[],[f38])).
% 2.49/1.01  
% 2.49/1.01  fof(f11,axiom,(
% 2.49/1.01    ! [X0] : (v3_ordinal1(X0) => (v4_ordinal1(X0) <=> ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) => r2_hidden(k1_ordinal1(X1),X0)))))),
% 2.49/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.49/1.01  
% 2.49/1.01  fof(f22,plain,(
% 2.49/1.01    ! [X0] : ((v4_ordinal1(X0) <=> ! [X1] : ((r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0)) | ~v3_ordinal1(X1))) | ~v3_ordinal1(X0))),
% 2.49/1.01    inference(ennf_transformation,[],[f11])).
% 2.49/1.01  
% 2.49/1.01  fof(f23,plain,(
% 2.49/1.01    ! [X0] : ((v4_ordinal1(X0) <=> ! [X1] : (r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X1))) | ~v3_ordinal1(X0))),
% 2.49/1.01    inference(flattening,[],[f22])).
% 2.49/1.01  
% 2.49/1.01  fof(f32,plain,(
% 2.49/1.01    ! [X0] : (((v4_ordinal1(X0) | ? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1))) & (! [X1] : (r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X1)) | ~v4_ordinal1(X0))) | ~v3_ordinal1(X0))),
% 2.49/1.01    inference(nnf_transformation,[],[f23])).
% 2.49/1.01  
% 2.49/1.01  fof(f33,plain,(
% 2.49/1.01    ! [X0] : (((v4_ordinal1(X0) | ? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1))) & (! [X2] : (r2_hidden(k1_ordinal1(X2),X0) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2)) | ~v4_ordinal1(X0))) | ~v3_ordinal1(X0))),
% 2.49/1.01    inference(rectify,[],[f32])).
% 2.49/1.01  
% 2.49/1.01  fof(f34,plain,(
% 2.49/1.01    ! [X0] : (? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) => (~r2_hidden(k1_ordinal1(sK0(X0)),X0) & r2_hidden(sK0(X0),X0) & v3_ordinal1(sK0(X0))))),
% 2.49/1.01    introduced(choice_axiom,[])).
% 2.49/1.01  
% 2.49/1.01  fof(f35,plain,(
% 2.49/1.01    ! [X0] : (((v4_ordinal1(X0) | (~r2_hidden(k1_ordinal1(sK0(X0)),X0) & r2_hidden(sK0(X0),X0) & v3_ordinal1(sK0(X0)))) & (! [X2] : (r2_hidden(k1_ordinal1(X2),X0) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2)) | ~v4_ordinal1(X0))) | ~v3_ordinal1(X0))),
% 2.49/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f34])).
% 2.49/1.01  
% 2.49/1.01  fof(f58,plain,(
% 2.49/1.01    ( ! [X0] : (v4_ordinal1(X0) | r2_hidden(sK0(X0),X0) | ~v3_ordinal1(X0)) )),
% 2.49/1.01    inference(cnf_transformation,[],[f35])).
% 2.49/1.01  
% 2.49/1.01  fof(f10,axiom,(
% 2.49/1.01    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 2.49/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.49/1.01  
% 2.49/1.01  fof(f21,plain,(
% 2.49/1.01    ! [X0] : (! [X1] : ((r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 2.49/1.01    inference(ennf_transformation,[],[f10])).
% 2.49/1.01  
% 2.49/1.01  fof(f31,plain,(
% 2.49/1.01    ! [X0] : (! [X1] : (((r2_hidden(X0,k1_ordinal1(X1)) | ~r1_ordinal1(X0,X1)) & (r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1)))) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 2.49/1.01    inference(nnf_transformation,[],[f21])).
% 2.49/1.01  
% 2.49/1.01  fof(f55,plain,(
% 2.49/1.01    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 2.49/1.01    inference(cnf_transformation,[],[f31])).
% 2.49/1.01  
% 2.49/1.01  fof(f2,axiom,(
% 2.49/1.01    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 2.49/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.49/1.01  
% 2.49/1.01  fof(f42,plain,(
% 2.49/1.01    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 2.49/1.01    inference(cnf_transformation,[],[f2])).
% 2.49/1.01  
% 2.49/1.01  fof(f75,plain,(
% 2.49/1.01    ( ! [X0,X1] : (r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 2.49/1.01    inference(definition_unfolding,[],[f55,f42])).
% 2.49/1.01  
% 2.49/1.01  fof(f5,axiom,(
% 2.49/1.01    ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <=> (X0 = X1 | r2_hidden(X0,X1)))),
% 2.49/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.49/1.01  
% 2.49/1.01  fof(f28,plain,(
% 2.49/1.01    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & ((X0 = X1 | r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 2.49/1.01    inference(nnf_transformation,[],[f5])).
% 2.49/1.01  
% 2.49/1.01  fof(f29,plain,(
% 2.49/1.01    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 2.49/1.01    inference(flattening,[],[f28])).
% 2.49/1.01  
% 2.49/1.01  fof(f47,plain,(
% 2.49/1.01    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | ~r2_hidden(X0,X1)) )),
% 2.49/1.01    inference(cnf_transformation,[],[f29])).
% 2.49/1.01  
% 2.49/1.01  fof(f69,plain,(
% 2.49/1.01    ( ! [X0,X1] : (r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | ~r2_hidden(X0,X1)) )),
% 2.49/1.01    inference(definition_unfolding,[],[f47,f42])).
% 2.49/1.01  
% 2.49/1.01  fof(f54,plain,(
% 2.49/1.01    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 2.49/1.01    inference(cnf_transformation,[],[f31])).
% 2.49/1.01  
% 2.49/1.01  fof(f76,plain,(
% 2.49/1.01    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | ~r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 2.49/1.01    inference(definition_unfolding,[],[f54,f42])).
% 2.49/1.01  
% 2.49/1.01  fof(f8,axiom,(
% 2.49/1.01    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k1_ordinal1(X0)))),
% 2.49/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.49/1.01  
% 2.49/1.01  fof(f19,plain,(
% 2.49/1.01    ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 2.49/1.01    inference(ennf_transformation,[],[f8])).
% 2.49/1.01  
% 2.49/1.01  fof(f51,plain,(
% 2.49/1.01    ( ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0)) )),
% 2.49/1.01    inference(cnf_transformation,[],[f19])).
% 2.49/1.01  
% 2.49/1.01  fof(f72,plain,(
% 2.49/1.01    ( ! [X0] : (v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) | ~v3_ordinal1(X0)) )),
% 2.49/1.01    inference(definition_unfolding,[],[f51,f42])).
% 2.49/1.01  
% 2.49/1.01  fof(f3,axiom,(
% 2.49/1.01    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 2.49/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.49/1.01  
% 2.49/1.01  fof(f15,plain,(
% 2.49/1.01    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 2.49/1.01    inference(ennf_transformation,[],[f3])).
% 2.49/1.01  
% 2.49/1.01  fof(f16,plain,(
% 2.49/1.01    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 2.49/1.01    inference(flattening,[],[f15])).
% 2.49/1.01  
% 2.49/1.01  fof(f27,plain,(
% 2.49/1.01    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 2.49/1.01    inference(nnf_transformation,[],[f16])).
% 2.49/1.01  
% 2.49/1.01  fof(f43,plain,(
% 2.49/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 2.49/1.01    inference(cnf_transformation,[],[f27])).
% 2.49/1.01  
% 2.49/1.01  fof(f9,axiom,(
% 2.49/1.01    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 2.49/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.49/1.01  
% 2.49/1.01  fof(f20,plain,(
% 2.49/1.01    ! [X0] : (! [X1] : ((r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 2.49/1.01    inference(ennf_transformation,[],[f9])).
% 2.49/1.01  
% 2.49/1.01  fof(f30,plain,(
% 2.49/1.01    ! [X0] : (! [X1] : (((r2_hidden(X0,X1) | ~r1_ordinal1(k1_ordinal1(X0),X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1))) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 2.49/1.01    inference(nnf_transformation,[],[f20])).
% 2.49/1.01  
% 2.49/1.01  fof(f52,plain,(
% 2.49/1.01    ( ! [X0,X1] : (r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 2.49/1.01    inference(cnf_transformation,[],[f30])).
% 2.49/1.01  
% 2.49/1.01  fof(f74,plain,(
% 2.49/1.01    ( ! [X0,X1] : (r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),X1) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 2.49/1.01    inference(definition_unfolding,[],[f52,f42])).
% 2.49/1.01  
% 2.49/1.01  fof(f1,axiom,(
% 2.49/1.01    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.49/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.49/1.01  
% 2.49/1.01  fof(f25,plain,(
% 2.49/1.01    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.49/1.01    inference(nnf_transformation,[],[f1])).
% 2.49/1.01  
% 2.49/1.01  fof(f26,plain,(
% 2.49/1.01    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.49/1.01    inference(flattening,[],[f25])).
% 2.49/1.01  
% 2.49/1.01  fof(f41,plain,(
% 2.49/1.01    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.49/1.01    inference(cnf_transformation,[],[f26])).
% 2.49/1.01  
% 2.49/1.01  fof(f57,plain,(
% 2.49/1.01    ( ! [X0] : (v4_ordinal1(X0) | v3_ordinal1(sK0(X0)) | ~v3_ordinal1(X0)) )),
% 2.49/1.01    inference(cnf_transformation,[],[f35])).
% 2.49/1.01  
% 2.49/1.01  fof(f7,axiom,(
% 2.49/1.01    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_hidden(X1,X0) & X0 != X1 & ~r2_hidden(X0,X1))))),
% 2.49/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.49/1.01  
% 2.49/1.01  fof(f17,plain,(
% 2.49/1.01    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 2.49/1.01    inference(ennf_transformation,[],[f7])).
% 2.49/1.01  
% 2.49/1.01  fof(f18,plain,(
% 2.49/1.01    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 2.49/1.01    inference(flattening,[],[f17])).
% 2.49/1.01  
% 2.49/1.01  fof(f50,plain,(
% 2.49/1.01    ( ! [X0,X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 2.49/1.01    inference(cnf_transformation,[],[f18])).
% 2.49/1.01  
% 2.49/1.01  fof(f6,axiom,(
% 2.49/1.01    ! [X0] : k1_ordinal1(X0) != X0),
% 2.49/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.49/1.01  
% 2.49/1.01  fof(f49,plain,(
% 2.49/1.01    ( ! [X0] : (k1_ordinal1(X0) != X0) )),
% 2.49/1.01    inference(cnf_transformation,[],[f6])).
% 2.49/1.01  
% 2.49/1.01  fof(f71,plain,(
% 2.49/1.01    ( ! [X0] : (k2_xboole_0(X0,k1_tarski(X0)) != X0) )),
% 2.49/1.01    inference(definition_unfolding,[],[f49,f42])).
% 2.49/1.01  
% 2.49/1.01  fof(f53,plain,(
% 2.49/1.01    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_ordinal1(k1_ordinal1(X0),X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 2.49/1.01    inference(cnf_transformation,[],[f30])).
% 2.49/1.01  
% 2.49/1.01  fof(f73,plain,(
% 2.49/1.01    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 2.49/1.01    inference(definition_unfolding,[],[f53,f42])).
% 2.49/1.01  
% 2.49/1.01  fof(f59,plain,(
% 2.49/1.01    ( ! [X0] : (v4_ordinal1(X0) | ~r2_hidden(k1_ordinal1(sK0(X0)),X0) | ~v3_ordinal1(X0)) )),
% 2.49/1.01    inference(cnf_transformation,[],[f35])).
% 2.49/1.01  
% 2.49/1.01  fof(f77,plain,(
% 2.49/1.01    ( ! [X0] : (v4_ordinal1(X0) | ~r2_hidden(k2_xboole_0(sK0(X0),k1_tarski(sK0(X0))),X0) | ~v3_ordinal1(X0)) )),
% 2.49/1.01    inference(definition_unfolding,[],[f59,f42])).
% 2.49/1.01  
% 2.49/1.01  fof(f63,plain,(
% 2.49/1.01    k1_ordinal1(sK2) = sK1 | ~v4_ordinal1(sK1)),
% 2.49/1.01    inference(cnf_transformation,[],[f38])).
% 2.49/1.01  
% 2.49/1.01  fof(f81,plain,(
% 2.49/1.01    k2_xboole_0(sK2,k1_tarski(sK2)) = sK1 | ~v4_ordinal1(sK1)),
% 2.49/1.01    inference(definition_unfolding,[],[f63,f42])).
% 2.49/1.01  
% 2.49/1.01  fof(f48,plain,(
% 2.49/1.01    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | X0 != X1) )),
% 2.49/1.01    inference(cnf_transformation,[],[f29])).
% 2.49/1.01  
% 2.49/1.01  fof(f68,plain,(
% 2.49/1.01    ( ! [X0,X1] : (r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | X0 != X1) )),
% 2.49/1.01    inference(definition_unfolding,[],[f48,f42])).
% 2.49/1.01  
% 2.49/1.01  fof(f85,plain,(
% 2.49/1.01    ( ! [X1] : (r2_hidden(X1,k2_xboole_0(X1,k1_tarski(X1)))) )),
% 2.49/1.01    inference(equality_resolution,[],[f68])).
% 2.49/1.01  
% 2.49/1.01  fof(f4,axiom,(
% 2.49/1.01    ! [X0] : r2_hidden(X0,k1_ordinal1(X0))),
% 2.49/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.49/1.01  
% 2.49/1.01  fof(f45,plain,(
% 2.49/1.01    ( ! [X0] : (r2_hidden(X0,k1_ordinal1(X0))) )),
% 2.49/1.01    inference(cnf_transformation,[],[f4])).
% 2.49/1.01  
% 2.49/1.01  fof(f67,plain,(
% 2.49/1.01    ( ! [X0] : (r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0)))) )),
% 2.49/1.01    inference(definition_unfolding,[],[f45,f42])).
% 2.49/1.01  
% 2.49/1.01  fof(f61,plain,(
% 2.49/1.01    v3_ordinal1(sK2) | ~v4_ordinal1(sK1)),
% 2.49/1.01    inference(cnf_transformation,[],[f38])).
% 2.49/1.01  
% 2.49/1.01  fof(f56,plain,(
% 2.49/1.01    ( ! [X2,X0] : (r2_hidden(k1_ordinal1(X2),X0) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2) | ~v4_ordinal1(X0) | ~v3_ordinal1(X0)) )),
% 2.49/1.01    inference(cnf_transformation,[],[f35])).
% 2.49/1.01  
% 2.49/1.01  fof(f78,plain,(
% 2.49/1.01    ( ! [X2,X0] : (r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),X0) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2) | ~v4_ordinal1(X0) | ~v3_ordinal1(X0)) )),
% 2.49/1.01    inference(definition_unfolding,[],[f56,f42])).
% 2.49/1.01  
% 2.49/1.01  fof(f66,plain,(
% 2.49/1.01    ( ! [X2] : (v4_ordinal1(sK1) | k1_ordinal1(X2) != sK1 | ~v3_ordinal1(X2)) )),
% 2.49/1.01    inference(cnf_transformation,[],[f38])).
% 2.49/1.01  
% 2.49/1.01  fof(f79,plain,(
% 2.49/1.01    ( ! [X2] : (v4_ordinal1(sK1) | k2_xboole_0(X2,k1_tarski(X2)) != sK1 | ~v3_ordinal1(X2)) )),
% 2.49/1.01    inference(definition_unfolding,[],[f66,f42])).
% 2.49/1.01  
% 2.49/1.01  cnf(c_26,negated_conjecture,
% 2.49/1.01      ( v3_ordinal1(sK1) ),
% 2.49/1.01      inference(cnf_transformation,[],[f60]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_1518,plain,
% 2.49/1.01      ( v3_ordinal1(sK1) = iProver_top ),
% 2.49/1.01      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_17,plain,
% 2.49/1.01      ( r2_hidden(sK0(X0),X0) | v4_ordinal1(X0) | ~ v3_ordinal1(X0) ),
% 2.49/1.01      inference(cnf_transformation,[],[f58]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_1526,plain,
% 2.49/1.01      ( r2_hidden(sK0(X0),X0) = iProver_top
% 2.49/1.01      | v4_ordinal1(X0) = iProver_top
% 2.49/1.01      | v3_ordinal1(X0) != iProver_top ),
% 2.49/1.01      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_14,plain,
% 2.49/1.01      ( r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
% 2.49/1.01      | ~ r1_ordinal1(X0,X1)
% 2.49/1.01      | ~ v3_ordinal1(X1)
% 2.49/1.01      | ~ v3_ordinal1(X0) ),
% 2.49/1.01      inference(cnf_transformation,[],[f75]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_1529,plain,
% 2.49/1.01      ( r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) = iProver_top
% 2.49/1.01      | r1_ordinal1(X0,X1) != iProver_top
% 2.49/1.01      | v3_ordinal1(X0) != iProver_top
% 2.49/1.01      | v3_ordinal1(X1) != iProver_top ),
% 2.49/1.01      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_7,plain,
% 2.49/1.01      ( ~ r2_hidden(X0,X1)
% 2.49/1.01      | r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) ),
% 2.49/1.01      inference(cnf_transformation,[],[f69]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_1535,plain,
% 2.49/1.01      ( r2_hidden(X0,X1) != iProver_top
% 2.49/1.01      | r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) = iProver_top ),
% 2.49/1.01      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_15,plain,
% 2.49/1.01      ( ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
% 2.49/1.01      | r1_ordinal1(X0,X1)
% 2.49/1.01      | ~ v3_ordinal1(X1)
% 2.49/1.01      | ~ v3_ordinal1(X0) ),
% 2.49/1.01      inference(cnf_transformation,[],[f76]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_1528,plain,
% 2.49/1.01      ( r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) != iProver_top
% 2.49/1.01      | r1_ordinal1(X0,X1) = iProver_top
% 2.49/1.01      | v3_ordinal1(X0) != iProver_top
% 2.49/1.01      | v3_ordinal1(X1) != iProver_top ),
% 2.49/1.01      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_2508,plain,
% 2.49/1.01      ( r2_hidden(X0,X1) != iProver_top
% 2.49/1.01      | r1_ordinal1(X0,X1) = iProver_top
% 2.49/1.01      | v3_ordinal1(X0) != iProver_top
% 2.49/1.01      | v3_ordinal1(X1) != iProver_top ),
% 2.49/1.01      inference(superposition,[status(thm)],[c_1535,c_1528]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_2805,plain,
% 2.49/1.01      ( r1_ordinal1(X0,X1) != iProver_top
% 2.49/1.01      | r1_ordinal1(X0,k2_xboole_0(X1,k1_tarski(X1))) = iProver_top
% 2.49/1.01      | v3_ordinal1(X0) != iProver_top
% 2.49/1.01      | v3_ordinal1(X1) != iProver_top
% 2.49/1.01      | v3_ordinal1(k2_xboole_0(X1,k1_tarski(X1))) != iProver_top ),
% 2.49/1.01      inference(superposition,[status(thm)],[c_1529,c_2508]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_11,plain,
% 2.49/1.01      ( ~ v3_ordinal1(X0) | v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) ),
% 2.49/1.01      inference(cnf_transformation,[],[f72]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_1532,plain,
% 2.49/1.01      ( v3_ordinal1(X0) != iProver_top
% 2.49/1.01      | v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) = iProver_top ),
% 2.49/1.01      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_3730,plain,
% 2.49/1.01      ( r1_ordinal1(X0,X1) != iProver_top
% 2.49/1.01      | r1_ordinal1(X0,k2_xboole_0(X1,k1_tarski(X1))) = iProver_top
% 2.49/1.01      | v3_ordinal1(X0) != iProver_top
% 2.49/1.01      | v3_ordinal1(X1) != iProver_top ),
% 2.49/1.01      inference(forward_subsumption_resolution,
% 2.49/1.01                [status(thm)],
% 2.49/1.01                [c_2805,c_1532]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_4,plain,
% 2.49/1.01      ( ~ r1_ordinal1(X0,X1)
% 2.49/1.01      | r1_tarski(X0,X1)
% 2.49/1.01      | ~ v3_ordinal1(X1)
% 2.49/1.01      | ~ v3_ordinal1(X0) ),
% 2.49/1.01      inference(cnf_transformation,[],[f43]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_1537,plain,
% 2.49/1.01      ( r1_ordinal1(X0,X1) != iProver_top
% 2.49/1.01      | r1_tarski(X0,X1) = iProver_top
% 2.49/1.01      | v3_ordinal1(X0) != iProver_top
% 2.49/1.01      | v3_ordinal1(X1) != iProver_top ),
% 2.49/1.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_3734,plain,
% 2.49/1.01      ( r1_ordinal1(X0,X1) != iProver_top
% 2.49/1.01      | r1_tarski(X0,k2_xboole_0(X1,k1_tarski(X1))) = iProver_top
% 2.49/1.01      | v3_ordinal1(X0) != iProver_top
% 2.49/1.01      | v3_ordinal1(X1) != iProver_top
% 2.49/1.01      | v3_ordinal1(k2_xboole_0(X1,k1_tarski(X1))) != iProver_top ),
% 2.49/1.01      inference(superposition,[status(thm)],[c_3730,c_1537]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_5482,plain,
% 2.49/1.01      ( r1_ordinal1(X0,X1) != iProver_top
% 2.49/1.01      | r1_tarski(X0,k2_xboole_0(X1,k1_tarski(X1))) = iProver_top
% 2.49/1.01      | v3_ordinal1(X0) != iProver_top
% 2.49/1.01      | v3_ordinal1(X1) != iProver_top ),
% 2.49/1.01      inference(forward_subsumption_resolution,
% 2.49/1.01                [status(thm)],
% 2.49/1.01                [c_3734,c_1532]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_13,plain,
% 2.49/1.01      ( ~ r2_hidden(X0,X1)
% 2.49/1.01      | r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),X1)
% 2.49/1.01      | ~ v3_ordinal1(X1)
% 2.49/1.01      | ~ v3_ordinal1(X0) ),
% 2.49/1.01      inference(cnf_transformation,[],[f74]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_1530,plain,
% 2.49/1.01      ( r2_hidden(X0,X1) != iProver_top
% 2.49/1.01      | r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),X1) = iProver_top
% 2.49/1.01      | v3_ordinal1(X0) != iProver_top
% 2.49/1.01      | v3_ordinal1(X1) != iProver_top ),
% 2.49/1.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_2851,plain,
% 2.49/1.01      ( r2_hidden(X0,X1) != iProver_top
% 2.49/1.01      | r1_tarski(k2_xboole_0(X0,k1_tarski(X0)),X1) = iProver_top
% 2.49/1.01      | v3_ordinal1(X0) != iProver_top
% 2.49/1.01      | v3_ordinal1(X1) != iProver_top
% 2.49/1.01      | v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) != iProver_top ),
% 2.49/1.01      inference(superposition,[status(thm)],[c_1530,c_1537]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_64,plain,
% 2.49/1.01      ( v3_ordinal1(X0) != iProver_top
% 2.49/1.01      | v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) = iProver_top ),
% 2.49/1.01      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_585,plain,
% 2.49/1.01      ( ~ r2_hidden(X0,X1)
% 2.49/1.01      | r1_tarski(X2,X3)
% 2.49/1.01      | ~ v3_ordinal1(X3)
% 2.49/1.01      | ~ v3_ordinal1(X2)
% 2.49/1.01      | ~ v3_ordinal1(X0)
% 2.49/1.01      | ~ v3_ordinal1(X1)
% 2.49/1.01      | X1 != X3
% 2.49/1.01      | k2_xboole_0(X0,k1_tarski(X0)) != X2 ),
% 2.49/1.01      inference(resolution_lifted,[status(thm)],[c_4,c_13]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_586,plain,
% 2.49/1.01      ( ~ r2_hidden(X0,X1)
% 2.49/1.01      | r1_tarski(k2_xboole_0(X0,k1_tarski(X0)),X1)
% 2.49/1.01      | ~ v3_ordinal1(X0)
% 2.49/1.01      | ~ v3_ordinal1(X1)
% 2.49/1.01      | ~ v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) ),
% 2.49/1.01      inference(unflattening,[status(thm)],[c_585]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_587,plain,
% 2.49/1.01      ( r2_hidden(X0,X1) != iProver_top
% 2.49/1.01      | r1_tarski(k2_xboole_0(X0,k1_tarski(X0)),X1) = iProver_top
% 2.49/1.01      | v3_ordinal1(X0) != iProver_top
% 2.49/1.01      | v3_ordinal1(X1) != iProver_top
% 2.49/1.01      | v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) != iProver_top ),
% 2.49/1.01      inference(predicate_to_equality,[status(thm)],[c_586]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_3863,plain,
% 2.49/1.01      ( v3_ordinal1(X1) != iProver_top
% 2.49/1.01      | v3_ordinal1(X0) != iProver_top
% 2.49/1.01      | r1_tarski(k2_xboole_0(X0,k1_tarski(X0)),X1) = iProver_top
% 2.49/1.01      | r2_hidden(X0,X1) != iProver_top ),
% 2.49/1.01      inference(global_propositional_subsumption,
% 2.49/1.01                [status(thm)],
% 2.49/1.01                [c_2851,c_64,c_587]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_3864,plain,
% 2.49/1.01      ( r2_hidden(X0,X1) != iProver_top
% 2.49/1.01      | r1_tarski(k2_xboole_0(X0,k1_tarski(X0)),X1) = iProver_top
% 2.49/1.01      | v3_ordinal1(X0) != iProver_top
% 2.49/1.01      | v3_ordinal1(X1) != iProver_top ),
% 2.49/1.01      inference(renaming,[status(thm)],[c_3863]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_0,plain,
% 2.49/1.01      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 2.49/1.01      inference(cnf_transformation,[],[f41]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_1540,plain,
% 2.49/1.01      ( X0 = X1
% 2.49/1.01      | r1_tarski(X0,X1) != iProver_top
% 2.49/1.01      | r1_tarski(X1,X0) != iProver_top ),
% 2.49/1.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_3872,plain,
% 2.49/1.01      ( k2_xboole_0(X0,k1_tarski(X0)) = X1
% 2.49/1.01      | r2_hidden(X0,X1) != iProver_top
% 2.49/1.01      | r1_tarski(X1,k2_xboole_0(X0,k1_tarski(X0))) != iProver_top
% 2.49/1.01      | v3_ordinal1(X0) != iProver_top
% 2.49/1.01      | v3_ordinal1(X1) != iProver_top ),
% 2.49/1.01      inference(superposition,[status(thm)],[c_3864,c_1540]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_5489,plain,
% 2.49/1.01      ( k2_xboole_0(X0,k1_tarski(X0)) = X1
% 2.49/1.01      | r2_hidden(X0,X1) != iProver_top
% 2.49/1.01      | r1_ordinal1(X1,X0) != iProver_top
% 2.49/1.01      | v3_ordinal1(X1) != iProver_top
% 2.49/1.01      | v3_ordinal1(X0) != iProver_top ),
% 2.49/1.01      inference(superposition,[status(thm)],[c_5482,c_3872]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_5581,plain,
% 2.49/1.01      ( k2_xboole_0(sK0(X0),k1_tarski(sK0(X0))) = X0
% 2.49/1.01      | r1_ordinal1(X0,sK0(X0)) != iProver_top
% 2.49/1.01      | v4_ordinal1(X0) = iProver_top
% 2.49/1.01      | v3_ordinal1(X0) != iProver_top
% 2.49/1.01      | v3_ordinal1(sK0(X0)) != iProver_top ),
% 2.49/1.01      inference(superposition,[status(thm)],[c_1526,c_5489]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_18,plain,
% 2.49/1.01      ( v4_ordinal1(X0) | ~ v3_ordinal1(X0) | v3_ordinal1(sK0(X0)) ),
% 2.49/1.01      inference(cnf_transformation,[],[f57]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_43,plain,
% 2.49/1.01      ( v4_ordinal1(X0) = iProver_top
% 2.49/1.01      | v3_ordinal1(X0) != iProver_top
% 2.49/1.01      | v3_ordinal1(sK0(X0)) = iProver_top ),
% 2.49/1.01      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_46,plain,
% 2.49/1.01      ( r2_hidden(sK0(X0),X0) = iProver_top
% 2.49/1.01      | v4_ordinal1(X0) = iProver_top
% 2.49/1.01      | v3_ordinal1(X0) != iProver_top ),
% 2.49/1.01      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_10,plain,
% 2.49/1.01      ( r2_hidden(X0,X1)
% 2.49/1.01      | r2_hidden(X1,X0)
% 2.49/1.01      | ~ v3_ordinal1(X1)
% 2.49/1.01      | ~ v3_ordinal1(X0)
% 2.49/1.01      | X1 = X0 ),
% 2.49/1.01      inference(cnf_transformation,[],[f50]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_1533,plain,
% 2.49/1.01      ( X0 = X1
% 2.49/1.01      | r2_hidden(X1,X0) = iProver_top
% 2.49/1.01      | r2_hidden(X0,X1) = iProver_top
% 2.49/1.01      | v3_ordinal1(X1) != iProver_top
% 2.49/1.01      | v3_ordinal1(X0) != iProver_top ),
% 2.49/1.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_3900,plain,
% 2.49/1.01      ( X0 = X1
% 2.49/1.01      | r2_hidden(X0,X1) = iProver_top
% 2.49/1.01      | r1_ordinal1(X1,X0) = iProver_top
% 2.49/1.01      | v3_ordinal1(X1) != iProver_top
% 2.49/1.01      | v3_ordinal1(X0) != iProver_top ),
% 2.49/1.01      inference(superposition,[status(thm)],[c_1533,c_2508]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_9,plain,
% 2.49/1.01      ( k2_xboole_0(X0,k1_tarski(X0)) != X0 ),
% 2.49/1.01      inference(cnf_transformation,[],[f71]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_12,plain,
% 2.49/1.01      ( r2_hidden(X0,X1)
% 2.49/1.01      | ~ r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),X1)
% 2.49/1.01      | ~ v3_ordinal1(X1)
% 2.49/1.01      | ~ v3_ordinal1(X0) ),
% 2.49/1.01      inference(cnf_transformation,[],[f73]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_513,plain,
% 2.49/1.01      ( r2_hidden(X0,X1)
% 2.49/1.01      | ~ r2_hidden(X2,k2_xboole_0(X3,k1_tarski(X3)))
% 2.49/1.01      | ~ v3_ordinal1(X3)
% 2.49/1.01      | ~ v3_ordinal1(X2)
% 2.49/1.01      | ~ v3_ordinal1(X0)
% 2.49/1.01      | ~ v3_ordinal1(X1)
% 2.49/1.01      | X1 != X3
% 2.49/1.01      | k2_xboole_0(X0,k1_tarski(X0)) != X2 ),
% 2.49/1.01      inference(resolution_lifted,[status(thm)],[c_15,c_12]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_514,plain,
% 2.49/1.01      ( r2_hidden(X0,X1)
% 2.49/1.01      | ~ r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),k2_xboole_0(X1,k1_tarski(X1)))
% 2.49/1.01      | ~ v3_ordinal1(X0)
% 2.49/1.01      | ~ v3_ordinal1(X1)
% 2.49/1.01      | ~ v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) ),
% 2.49/1.01      inference(unflattening,[status(thm)],[c_513]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_518,plain,
% 2.49/1.01      ( ~ v3_ordinal1(X1)
% 2.49/1.01      | ~ v3_ordinal1(X0)
% 2.49/1.01      | ~ r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),k2_xboole_0(X1,k1_tarski(X1)))
% 2.49/1.01      | r2_hidden(X0,X1) ),
% 2.49/1.01      inference(global_propositional_subsumption,
% 2.49/1.01                [status(thm)],
% 2.49/1.01                [c_514,c_11]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_519,plain,
% 2.49/1.01      ( r2_hidden(X0,X1)
% 2.49/1.01      | ~ r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),k2_xboole_0(X1,k1_tarski(X1)))
% 2.49/1.01      | ~ v3_ordinal1(X1)
% 2.49/1.01      | ~ v3_ordinal1(X0) ),
% 2.49/1.01      inference(renaming,[status(thm)],[c_518]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_520,plain,
% 2.49/1.01      ( r2_hidden(X0,X1) = iProver_top
% 2.49/1.01      | r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),k2_xboole_0(X1,k1_tarski(X1))) != iProver_top
% 2.49/1.01      | v3_ordinal1(X0) != iProver_top
% 2.49/1.01      | v3_ordinal1(X1) != iProver_top ),
% 2.49/1.01      inference(predicate_to_equality,[status(thm)],[c_519]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_1121,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_1748,plain,
% 2.49/1.01      ( X0 != X1
% 2.49/1.01      | k2_xboole_0(X0,k1_tarski(X0)) != X1
% 2.49/1.01      | k2_xboole_0(X0,k1_tarski(X0)) = X0 ),
% 2.49/1.01      inference(instantiation,[status(thm)],[c_1121]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_1875,plain,
% 2.49/1.01      ( ~ r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),X1)
% 2.49/1.01      | r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),k2_xboole_0(X1,k1_tarski(X1))) ),
% 2.49/1.01      inference(instantiation,[status(thm)],[c_7]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_1876,plain,
% 2.49/1.01      ( r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),X1) != iProver_top
% 2.49/1.01      | r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),k2_xboole_0(X1,k1_tarski(X1))) = iProver_top ),
% 2.49/1.01      inference(predicate_to_equality,[status(thm)],[c_1875]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_3906,plain,
% 2.49/1.01      ( k2_xboole_0(X0,k1_tarski(X0)) = X1
% 2.49/1.01      | r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),X1) = iProver_top
% 2.49/1.01      | r1_ordinal1(X1,X0) = iProver_top
% 2.49/1.01      | v3_ordinal1(X0) != iProver_top
% 2.49/1.01      | v3_ordinal1(X1) != iProver_top
% 2.49/1.01      | v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) != iProver_top ),
% 2.49/1.01      inference(superposition,[status(thm)],[c_1533,c_1528]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_4332,plain,
% 2.49/1.01      ( r2_hidden(X0,X1) = iProver_top
% 2.49/1.01      | r1_ordinal1(X1,X0) = iProver_top
% 2.49/1.01      | v3_ordinal1(X1) != iProver_top
% 2.49/1.01      | v3_ordinal1(X0) != iProver_top ),
% 2.49/1.01      inference(global_propositional_subsumption,
% 2.49/1.01                [status(thm)],
% 2.49/1.01                [c_3900,c_64,c_9,c_520,c_1748,c_1876,c_3906]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_4333,plain,
% 2.49/1.01      ( r2_hidden(X0,X1) = iProver_top
% 2.49/1.01      | r1_ordinal1(X1,X0) = iProver_top
% 2.49/1.01      | v3_ordinal1(X0) != iProver_top
% 2.49/1.01      | v3_ordinal1(X1) != iProver_top ),
% 2.49/1.01      inference(renaming,[status(thm)],[c_4332]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_16,plain,
% 2.49/1.01      ( ~ r2_hidden(k2_xboole_0(sK0(X0),k1_tarski(sK0(X0))),X0)
% 2.49/1.01      | v4_ordinal1(X0)
% 2.49/1.01      | ~ v3_ordinal1(X0) ),
% 2.49/1.01      inference(cnf_transformation,[],[f77]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_1527,plain,
% 2.49/1.01      ( r2_hidden(k2_xboole_0(sK0(X0),k1_tarski(sK0(X0))),X0) != iProver_top
% 2.49/1.01      | v4_ordinal1(X0) = iProver_top
% 2.49/1.01      | v3_ordinal1(X0) != iProver_top ),
% 2.49/1.01      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_4344,plain,
% 2.49/1.01      ( r1_ordinal1(X0,k2_xboole_0(sK0(X0),k1_tarski(sK0(X0)))) = iProver_top
% 2.49/1.01      | v4_ordinal1(X0) = iProver_top
% 2.49/1.01      | v3_ordinal1(X0) != iProver_top
% 2.49/1.01      | v3_ordinal1(k2_xboole_0(sK0(X0),k1_tarski(sK0(X0)))) != iProver_top ),
% 2.49/1.01      inference(superposition,[status(thm)],[c_4333,c_1527]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_5286,plain,
% 2.49/1.01      ( r1_tarski(X0,k2_xboole_0(sK0(X0),k1_tarski(sK0(X0)))) = iProver_top
% 2.49/1.01      | v4_ordinal1(X0) = iProver_top
% 2.49/1.01      | v3_ordinal1(X0) != iProver_top
% 2.49/1.01      | v3_ordinal1(k2_xboole_0(sK0(X0),k1_tarski(sK0(X0)))) != iProver_top ),
% 2.49/1.01      inference(superposition,[status(thm)],[c_4344,c_1537]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_5447,plain,
% 2.49/1.01      ( k2_xboole_0(sK0(X0),k1_tarski(sK0(X0))) = X0
% 2.49/1.01      | r2_hidden(sK0(X0),X0) != iProver_top
% 2.49/1.01      | v4_ordinal1(X0) = iProver_top
% 2.49/1.01      | v3_ordinal1(X0) != iProver_top
% 2.49/1.01      | v3_ordinal1(k2_xboole_0(sK0(X0),k1_tarski(sK0(X0)))) != iProver_top
% 2.49/1.01      | v3_ordinal1(sK0(X0)) != iProver_top ),
% 2.49/1.01      inference(superposition,[status(thm)],[c_5286,c_3872]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_6294,plain,
% 2.49/1.01      ( v3_ordinal1(k2_xboole_0(sK0(X0),k1_tarski(sK0(X0))))
% 2.49/1.01      | ~ v3_ordinal1(sK0(X0)) ),
% 2.49/1.01      inference(instantiation,[status(thm)],[c_11]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_6295,plain,
% 2.49/1.01      ( v3_ordinal1(k2_xboole_0(sK0(X0),k1_tarski(sK0(X0)))) = iProver_top
% 2.49/1.01      | v3_ordinal1(sK0(X0)) != iProver_top ),
% 2.49/1.01      inference(predicate_to_equality,[status(thm)],[c_6294]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_6775,plain,
% 2.49/1.01      ( v3_ordinal1(X0) != iProver_top
% 2.49/1.01      | v4_ordinal1(X0) = iProver_top
% 2.49/1.01      | k2_xboole_0(sK0(X0),k1_tarski(sK0(X0))) = X0 ),
% 2.49/1.01      inference(global_propositional_subsumption,
% 2.49/1.01                [status(thm)],
% 2.49/1.01                [c_5581,c_43,c_46,c_5447,c_6295]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_6776,plain,
% 2.49/1.01      ( k2_xboole_0(sK0(X0),k1_tarski(sK0(X0))) = X0
% 2.49/1.01      | v4_ordinal1(X0) = iProver_top
% 2.49/1.01      | v3_ordinal1(X0) != iProver_top ),
% 2.49/1.01      inference(renaming,[status(thm)],[c_6775]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_6786,plain,
% 2.49/1.01      ( k2_xboole_0(sK0(sK1),k1_tarski(sK0(sK1))) = sK1
% 2.49/1.01      | v4_ordinal1(sK1) = iProver_top ),
% 2.49/1.01      inference(superposition,[status(thm)],[c_1518,c_6776]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_23,negated_conjecture,
% 2.49/1.01      ( ~ v4_ordinal1(sK1) | k2_xboole_0(sK2,k1_tarski(sK2)) = sK1 ),
% 2.49/1.01      inference(cnf_transformation,[],[f81]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_1521,plain,
% 2.49/1.01      ( k2_xboole_0(sK2,k1_tarski(sK2)) = sK1
% 2.49/1.01      | v4_ordinal1(sK1) != iProver_top ),
% 2.49/1.01      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_7063,plain,
% 2.49/1.01      ( k2_xboole_0(sK0(sK1),k1_tarski(sK0(sK1))) = sK1
% 2.49/1.01      | k2_xboole_0(sK2,k1_tarski(sK2)) = sK1 ),
% 2.49/1.01      inference(superposition,[status(thm)],[c_6786,c_1521]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_53,plain,
% 2.49/1.01      ( ~ r2_hidden(sK1,k2_xboole_0(sK1,k1_tarski(sK1)))
% 2.49/1.01      | r1_ordinal1(sK1,sK1)
% 2.49/1.01      | ~ v3_ordinal1(sK1) ),
% 2.49/1.01      inference(instantiation,[status(thm)],[c_15]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_65,plain,
% 2.49/1.01      ( v3_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1)))
% 2.49/1.01      | ~ v3_ordinal1(sK1) ),
% 2.49/1.01      inference(instantiation,[status(thm)],[c_11]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_70,plain,
% 2.49/1.01      ( k2_xboole_0(sK1,k1_tarski(sK1)) != sK1 ),
% 2.49/1.01      inference(instantiation,[status(thm)],[c_9]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_6,plain,
% 2.49/1.01      ( r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0))) ),
% 2.49/1.01      inference(cnf_transformation,[],[f85]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_78,plain,
% 2.49/1.01      ( r2_hidden(sK1,k2_xboole_0(sK1,k1_tarski(sK1))) ),
% 2.49/1.01      inference(instantiation,[status(thm)],[c_6]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_82,plain,
% 2.49/1.01      ( ~ r1_ordinal1(sK1,sK1)
% 2.49/1.01      | r1_tarski(sK1,sK1)
% 2.49/1.01      | ~ v3_ordinal1(sK1) ),
% 2.49/1.01      inference(instantiation,[status(thm)],[c_4]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_92,plain,
% 2.49/1.01      ( ~ r1_tarski(sK1,sK1) | sK1 = sK1 ),
% 2.49/1.01      inference(instantiation,[status(thm)],[c_0]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_590,plain,
% 2.49/1.01      ( ~ v3_ordinal1(X1)
% 2.49/1.01      | ~ v3_ordinal1(X0)
% 2.49/1.01      | r1_tarski(k2_xboole_0(X0,k1_tarski(X0)),X1)
% 2.49/1.01      | ~ r2_hidden(X0,X1) ),
% 2.49/1.01      inference(global_propositional_subsumption,
% 2.49/1.01                [status(thm)],
% 2.49/1.01                [c_586,c_11]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_591,plain,
% 2.49/1.01      ( ~ r2_hidden(X0,X1)
% 2.49/1.01      | r1_tarski(k2_xboole_0(X0,k1_tarski(X0)),X1)
% 2.49/1.01      | ~ v3_ordinal1(X1)
% 2.49/1.01      | ~ v3_ordinal1(X0) ),
% 2.49/1.01      inference(renaming,[status(thm)],[c_590]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_593,plain,
% 2.49/1.01      ( ~ r2_hidden(sK1,sK1)
% 2.49/1.01      | r1_tarski(k2_xboole_0(sK1,k1_tarski(sK1)),sK1)
% 2.49/1.01      | ~ v3_ordinal1(sK1) ),
% 2.49/1.01      inference(instantiation,[status(thm)],[c_591]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_1816,plain,
% 2.49/1.01      ( X0 != k2_xboole_0(X0,k1_tarski(X0))
% 2.49/1.01      | k2_xboole_0(X0,k1_tarski(X0)) = X0
% 2.49/1.01      | k2_xboole_0(X0,k1_tarski(X0)) != k2_xboole_0(X0,k1_tarski(X0)) ),
% 2.49/1.01      inference(instantiation,[status(thm)],[c_1748]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_1818,plain,
% 2.49/1.01      ( k2_xboole_0(sK1,k1_tarski(sK1)) != k2_xboole_0(sK1,k1_tarski(sK1))
% 2.49/1.01      | k2_xboole_0(sK1,k1_tarski(sK1)) = sK1
% 2.49/1.01      | sK1 != k2_xboole_0(sK1,k1_tarski(sK1)) ),
% 2.49/1.01      inference(instantiation,[status(thm)],[c_1816]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_1120,plain,( X0 = X0 ),theory(equality) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_1817,plain,
% 2.49/1.01      ( k2_xboole_0(X0,k1_tarski(X0)) = k2_xboole_0(X0,k1_tarski(X0)) ),
% 2.49/1.01      inference(instantiation,[status(thm)],[c_1120]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_1819,plain,
% 2.49/1.01      ( k2_xboole_0(sK1,k1_tarski(sK1)) = k2_xboole_0(sK1,k1_tarski(sK1)) ),
% 2.49/1.01      inference(instantiation,[status(thm)],[c_1817]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_1837,plain,
% 2.49/1.01      ( ~ r1_ordinal1(X0,k2_xboole_0(X0,k1_tarski(X0)))
% 2.49/1.01      | r1_tarski(X0,k2_xboole_0(X0,k1_tarski(X0)))
% 2.49/1.01      | ~ v3_ordinal1(X0)
% 2.49/1.01      | ~ v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) ),
% 2.49/1.01      inference(instantiation,[status(thm)],[c_4]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_1839,plain,
% 2.49/1.01      ( ~ r1_ordinal1(sK1,k2_xboole_0(sK1,k1_tarski(sK1)))
% 2.49/1.01      | r1_tarski(sK1,k2_xboole_0(sK1,k1_tarski(sK1)))
% 2.49/1.01      | ~ v3_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1)))
% 2.49/1.01      | ~ v3_ordinal1(sK1) ),
% 2.49/1.01      inference(instantiation,[status(thm)],[c_1837]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_1884,plain,
% 2.49/1.01      ( ~ r1_tarski(X0,k2_xboole_0(X1,k1_tarski(X1)))
% 2.49/1.01      | ~ r1_tarski(k2_xboole_0(X1,k1_tarski(X1)),X0)
% 2.49/1.01      | X0 = k2_xboole_0(X1,k1_tarski(X1)) ),
% 2.49/1.01      inference(instantiation,[status(thm)],[c_0]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_1886,plain,
% 2.49/1.01      ( ~ r1_tarski(k2_xboole_0(sK1,k1_tarski(sK1)),sK1)
% 2.49/1.01      | ~ r1_tarski(sK1,k2_xboole_0(sK1,k1_tarski(sK1)))
% 2.49/1.01      | sK1 = k2_xboole_0(sK1,k1_tarski(sK1)) ),
% 2.49/1.01      inference(instantiation,[status(thm)],[c_1884]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_1899,plain,
% 2.49/1.01      ( X0 != X1
% 2.49/1.01      | X0 = k2_xboole_0(X2,k1_tarski(X2))
% 2.49/1.01      | k2_xboole_0(X2,k1_tarski(X2)) != X1 ),
% 2.49/1.01      inference(instantiation,[status(thm)],[c_1121]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_2304,plain,
% 2.49/1.01      ( X0 = k2_xboole_0(sK2,k1_tarski(sK2))
% 2.49/1.01      | X0 != sK1
% 2.49/1.01      | k2_xboole_0(sK2,k1_tarski(sK2)) != sK1 ),
% 2.49/1.01      inference(instantiation,[status(thm)],[c_1899]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_2306,plain,
% 2.49/1.01      ( k2_xboole_0(sK2,k1_tarski(sK2)) != sK1
% 2.49/1.01      | sK1 = k2_xboole_0(sK2,k1_tarski(sK2))
% 2.49/1.01      | sK1 != sK1 ),
% 2.49/1.01      inference(instantiation,[status(thm)],[c_2304]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_5,plain,
% 2.49/1.01      ( r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0))) ),
% 2.49/1.01      inference(cnf_transformation,[],[f67]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_1536,plain,
% 2.49/1.01      ( r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0))) = iProver_top ),
% 2.49/1.01      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_2543,plain,
% 2.49/1.01      ( r1_ordinal1(X0,k2_xboole_0(X0,k1_tarski(X0))) = iProver_top
% 2.49/1.01      | v3_ordinal1(X0) != iProver_top
% 2.49/1.01      | v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) != iProver_top ),
% 2.49/1.01      inference(superposition,[status(thm)],[c_1536,c_2508]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_2572,plain,
% 2.49/1.01      ( r1_ordinal1(X0,k2_xboole_0(X0,k1_tarski(X0)))
% 2.49/1.01      | ~ v3_ordinal1(X0)
% 2.49/1.01      | ~ v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) ),
% 2.49/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_2543]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_2574,plain,
% 2.49/1.01      ( r1_ordinal1(sK1,k2_xboole_0(sK1,k1_tarski(sK1)))
% 2.49/1.01      | ~ v3_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1)))
% 2.49/1.01      | ~ v3_ordinal1(sK1) ),
% 2.49/1.01      inference(instantiation,[status(thm)],[c_2572]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_1123,plain,
% 2.49/1.01      ( ~ v3_ordinal1(X0) | v3_ordinal1(X1) | X1 != X0 ),
% 2.49/1.01      theory(equality) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_2619,plain,
% 2.49/1.01      ( ~ v3_ordinal1(X0)
% 2.49/1.01      | v3_ordinal1(k2_xboole_0(sK2,k1_tarski(sK2)))
% 2.49/1.01      | k2_xboole_0(sK2,k1_tarski(sK2)) != X0 ),
% 2.49/1.01      inference(instantiation,[status(thm)],[c_1123]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_2621,plain,
% 2.49/1.01      ( v3_ordinal1(k2_xboole_0(sK2,k1_tarski(sK2)))
% 2.49/1.01      | ~ v3_ordinal1(sK1)
% 2.49/1.01      | k2_xboole_0(sK2,k1_tarski(sK2)) != sK1 ),
% 2.49/1.01      inference(instantiation,[status(thm)],[c_2619]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_4003,plain,
% 2.49/1.01      ( r2_hidden(sK2,k2_xboole_0(sK2,k1_tarski(sK2))) ),
% 2.49/1.01      inference(instantiation,[status(thm)],[c_5]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_1126,plain,
% 2.49/1.01      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.49/1.01      theory(equality) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_1798,plain,
% 2.49/1.01      ( r2_hidden(X0,X1)
% 2.49/1.01      | ~ r2_hidden(X2,k2_xboole_0(X3,k1_tarski(X3)))
% 2.49/1.01      | X0 != X2
% 2.49/1.01      | X1 != k2_xboole_0(X3,k1_tarski(X3)) ),
% 2.49/1.01      inference(instantiation,[status(thm)],[c_1126]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_2443,plain,
% 2.49/1.01      ( r2_hidden(X0,X1)
% 2.49/1.01      | ~ r2_hidden(X2,k2_xboole_0(sK2,k1_tarski(sK2)))
% 2.49/1.01      | X0 != X2
% 2.49/1.01      | X1 != k2_xboole_0(sK2,k1_tarski(sK2)) ),
% 2.49/1.01      inference(instantiation,[status(thm)],[c_1798]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_4467,plain,
% 2.49/1.01      ( r2_hidden(X0,X1)
% 2.49/1.01      | ~ r2_hidden(k2_xboole_0(sK2,k1_tarski(sK2)),k2_xboole_0(sK2,k1_tarski(sK2)))
% 2.49/1.01      | X0 != k2_xboole_0(sK2,k1_tarski(sK2))
% 2.49/1.01      | X1 != k2_xboole_0(sK2,k1_tarski(sK2)) ),
% 2.49/1.01      inference(instantiation,[status(thm)],[c_2443]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_4471,plain,
% 2.49/1.01      ( ~ r2_hidden(k2_xboole_0(sK2,k1_tarski(sK2)),k2_xboole_0(sK2,k1_tarski(sK2)))
% 2.49/1.01      | r2_hidden(sK1,sK1)
% 2.49/1.01      | sK1 != k2_xboole_0(sK2,k1_tarski(sK2)) ),
% 2.49/1.01      inference(instantiation,[status(thm)],[c_4467]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_1127,plain,
% 2.49/1.01      ( ~ v4_ordinal1(X0) | v4_ordinal1(X1) | X1 != X0 ),
% 2.49/1.01      theory(equality) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_2337,plain,
% 2.49/1.01      ( ~ v4_ordinal1(X0)
% 2.49/1.01      | v4_ordinal1(k2_xboole_0(X1,k1_tarski(X1)))
% 2.49/1.01      | k2_xboole_0(X1,k1_tarski(X1)) != X0 ),
% 2.49/1.01      inference(instantiation,[status(thm)],[c_1127]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_5984,plain,
% 2.49/1.01      ( v4_ordinal1(k2_xboole_0(sK2,k1_tarski(sK2)))
% 2.49/1.01      | ~ v4_ordinal1(sK1)
% 2.49/1.01      | k2_xboole_0(sK2,k1_tarski(sK2)) != sK1 ),
% 2.49/1.01      inference(instantiation,[status(thm)],[c_2337]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_6811,plain,
% 2.49/1.01      ( v4_ordinal1(sK1)
% 2.49/1.01      | k2_xboole_0(sK0(sK1),k1_tarski(sK0(sK1))) = sK1 ),
% 2.49/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_6786]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_25,negated_conjecture,
% 2.49/1.01      ( ~ v4_ordinal1(sK1) | v3_ordinal1(sK2) ),
% 2.49/1.01      inference(cnf_transformation,[],[f61]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_1519,plain,
% 2.49/1.01      ( v4_ordinal1(sK1) != iProver_top
% 2.49/1.01      | v3_ordinal1(sK2) = iProver_top ),
% 2.49/1.01      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_7064,plain,
% 2.49/1.01      ( k2_xboole_0(sK0(sK1),k1_tarski(sK0(sK1))) = sK1
% 2.49/1.01      | v3_ordinal1(sK2) = iProver_top ),
% 2.49/1.01      inference(superposition,[status(thm)],[c_6786,c_1519]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_7073,plain,
% 2.49/1.01      ( v3_ordinal1(sK2)
% 2.49/1.01      | k2_xboole_0(sK0(sK1),k1_tarski(sK0(sK1))) = sK1 ),
% 2.49/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_7064]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_19,plain,
% 2.49/1.01      ( ~ r2_hidden(X0,X1)
% 2.49/1.01      | r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),X1)
% 2.49/1.01      | ~ v4_ordinal1(X1)
% 2.49/1.01      | ~ v3_ordinal1(X1)
% 2.49/1.01      | ~ v3_ordinal1(X0) ),
% 2.49/1.01      inference(cnf_transformation,[],[f78]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_1773,plain,
% 2.49/1.01      ( ~ r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0)))
% 2.49/1.01      | r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),k2_xboole_0(X0,k1_tarski(X0)))
% 2.49/1.01      | ~ v4_ordinal1(k2_xboole_0(X0,k1_tarski(X0)))
% 2.49/1.01      | ~ v3_ordinal1(X0)
% 2.49/1.01      | ~ v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) ),
% 2.49/1.01      inference(instantiation,[status(thm)],[c_19]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_7325,plain,
% 2.49/1.01      ( r2_hidden(k2_xboole_0(sK2,k1_tarski(sK2)),k2_xboole_0(sK2,k1_tarski(sK2)))
% 2.49/1.01      | ~ r2_hidden(sK2,k2_xboole_0(sK2,k1_tarski(sK2)))
% 2.49/1.01      | ~ v4_ordinal1(k2_xboole_0(sK2,k1_tarski(sK2)))
% 2.49/1.01      | ~ v3_ordinal1(k2_xboole_0(sK2,k1_tarski(sK2)))
% 2.49/1.01      | ~ v3_ordinal1(sK2) ),
% 2.49/1.01      inference(instantiation,[status(thm)],[c_1773]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_7443,plain,
% 2.49/1.01      ( k2_xboole_0(sK0(sK1),k1_tarski(sK0(sK1))) = sK1 ),
% 2.49/1.01      inference(global_propositional_subsumption,
% 2.49/1.01                [status(thm)],
% 2.49/1.01                [c_7063,c_26,c_53,c_65,c_70,c_78,c_82,c_92,c_593,c_1818,
% 2.49/1.01                 c_1819,c_1839,c_1886,c_2306,c_2574,c_2621,c_4003,c_4471,
% 2.49/1.01                 c_5984,c_6811,c_7073,c_7325]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_1524,plain,
% 2.49/1.01      ( r2_hidden(X0,X1) != iProver_top
% 2.49/1.01      | r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),X1) = iProver_top
% 2.49/1.01      | v4_ordinal1(X1) != iProver_top
% 2.49/1.01      | v3_ordinal1(X0) != iProver_top
% 2.49/1.01      | v3_ordinal1(X1) != iProver_top ),
% 2.49/1.01      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_2976,plain,
% 2.49/1.01      ( v3_ordinal1(X0) != iProver_top
% 2.49/1.01      | r1_ordinal1(X0,k2_xboole_0(X0,k1_tarski(X0))) = iProver_top ),
% 2.49/1.01      inference(global_propositional_subsumption,
% 2.49/1.01                [status(thm)],
% 2.49/1.01                [c_2543,c_64]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_2977,plain,
% 2.49/1.01      ( r1_ordinal1(X0,k2_xboole_0(X0,k1_tarski(X0))) = iProver_top
% 2.49/1.01      | v3_ordinal1(X0) != iProver_top ),
% 2.49/1.01      inference(renaming,[status(thm)],[c_2976]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_2984,plain,
% 2.49/1.01      ( r1_tarski(X0,k2_xboole_0(X0,k1_tarski(X0))) = iProver_top
% 2.49/1.01      | v3_ordinal1(X0) != iProver_top
% 2.49/1.01      | v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) != iProver_top ),
% 2.49/1.01      inference(superposition,[status(thm)],[c_2977,c_1537]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_1838,plain,
% 2.49/1.01      ( r1_ordinal1(X0,k2_xboole_0(X0,k1_tarski(X0))) != iProver_top
% 2.49/1.01      | r1_tarski(X0,k2_xboole_0(X0,k1_tarski(X0))) = iProver_top
% 2.49/1.01      | v3_ordinal1(X0) != iProver_top
% 2.49/1.01      | v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) != iProver_top ),
% 2.49/1.01      inference(predicate_to_equality,[status(thm)],[c_1837]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_3117,plain,
% 2.49/1.01      ( v3_ordinal1(X0) != iProver_top
% 2.49/1.01      | r1_tarski(X0,k2_xboole_0(X0,k1_tarski(X0))) = iProver_top ),
% 2.49/1.01      inference(global_propositional_subsumption,
% 2.49/1.01                [status(thm)],
% 2.49/1.01                [c_2984,c_64]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_3118,plain,
% 2.49/1.01      ( r1_tarski(X0,k2_xboole_0(X0,k1_tarski(X0))) = iProver_top
% 2.49/1.01      | v3_ordinal1(X0) != iProver_top ),
% 2.49/1.01      inference(renaming,[status(thm)],[c_3117]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_3126,plain,
% 2.49/1.01      ( k2_xboole_0(X0,k1_tarski(X0)) = X0
% 2.49/1.01      | r1_tarski(k2_xboole_0(X0,k1_tarski(X0)),X0) != iProver_top
% 2.49/1.01      | v3_ordinal1(X0) != iProver_top ),
% 2.49/1.01      inference(superposition,[status(thm)],[c_3118,c_1540]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_3137,plain,
% 2.49/1.01      ( r1_tarski(k2_xboole_0(X0,k1_tarski(X0)),X0) != iProver_top
% 2.49/1.01      | v3_ordinal1(X0) != iProver_top ),
% 2.49/1.01      inference(global_propositional_subsumption,
% 2.49/1.01                [status(thm)],
% 2.49/1.01                [c_3126,c_9]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_3873,plain,
% 2.49/1.01      ( r2_hidden(X0,X0) != iProver_top
% 2.49/1.01      | v3_ordinal1(X0) != iProver_top ),
% 2.49/1.01      inference(superposition,[status(thm)],[c_3864,c_3137]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_4494,plain,
% 2.49/1.01      ( r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0))) != iProver_top
% 2.49/1.01      | v4_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) != iProver_top
% 2.49/1.01      | v3_ordinal1(X0) != iProver_top
% 2.49/1.01      | v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) != iProver_top ),
% 2.49/1.01      inference(superposition,[status(thm)],[c_1524,c_3873]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_77,plain,
% 2.49/1.01      ( r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0))) = iProver_top ),
% 2.49/1.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_4835,plain,
% 2.49/1.01      ( v3_ordinal1(X0) != iProver_top
% 2.49/1.01      | v4_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) != iProver_top ),
% 2.49/1.01      inference(global_propositional_subsumption,
% 2.49/1.01                [status(thm)],
% 2.49/1.01                [c_4494,c_64,c_77]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_4836,plain,
% 2.49/1.01      ( v4_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) != iProver_top
% 2.49/1.01      | v3_ordinal1(X0) != iProver_top ),
% 2.49/1.01      inference(renaming,[status(thm)],[c_4835]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_7458,plain,
% 2.49/1.01      ( v4_ordinal1(sK1) != iProver_top
% 2.49/1.01      | v3_ordinal1(sK0(sK1)) != iProver_top ),
% 2.49/1.01      inference(superposition,[status(thm)],[c_7443,c_4836]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_20,negated_conjecture,
% 2.49/1.01      ( v4_ordinal1(sK1)
% 2.49/1.01      | ~ v3_ordinal1(X0)
% 2.49/1.01      | k2_xboole_0(X0,k1_tarski(X0)) != sK1 ),
% 2.49/1.01      inference(cnf_transformation,[],[f79]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_1523,plain,
% 2.49/1.01      ( k2_xboole_0(X0,k1_tarski(X0)) != sK1
% 2.49/1.01      | v4_ordinal1(sK1) = iProver_top
% 2.49/1.01      | v3_ordinal1(X0) != iProver_top ),
% 2.49/1.01      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_7477,plain,
% 2.49/1.01      ( v4_ordinal1(sK1) = iProver_top
% 2.49/1.01      | v3_ordinal1(sK0(sK1)) != iProver_top ),
% 2.49/1.01      inference(superposition,[status(thm)],[c_7443,c_1523]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_7657,plain,
% 2.49/1.01      ( v3_ordinal1(sK0(sK1)) != iProver_top ),
% 2.49/1.01      inference(forward_subsumption_resolution,
% 2.49/1.01                [status(thm)],
% 2.49/1.01                [c_7458,c_7477]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_7326,plain,
% 2.49/1.01      ( r2_hidden(k2_xboole_0(sK2,k1_tarski(sK2)),k2_xboole_0(sK2,k1_tarski(sK2))) = iProver_top
% 2.49/1.01      | r2_hidden(sK2,k2_xboole_0(sK2,k1_tarski(sK2))) != iProver_top
% 2.49/1.01      | v4_ordinal1(k2_xboole_0(sK2,k1_tarski(sK2))) != iProver_top
% 2.49/1.01      | v3_ordinal1(k2_xboole_0(sK2,k1_tarski(sK2))) != iProver_top
% 2.49/1.01      | v3_ordinal1(sK2) != iProver_top ),
% 2.49/1.01      inference(predicate_to_equality,[status(thm)],[c_7325]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_5985,plain,
% 2.49/1.01      ( k2_xboole_0(sK2,k1_tarski(sK2)) != sK1
% 2.49/1.01      | v4_ordinal1(k2_xboole_0(sK2,k1_tarski(sK2))) = iProver_top
% 2.49/1.01      | v4_ordinal1(sK1) != iProver_top ),
% 2.49/1.01      inference(predicate_to_equality,[status(thm)],[c_5984]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_4470,plain,
% 2.49/1.01      ( X0 != k2_xboole_0(sK2,k1_tarski(sK2))
% 2.49/1.01      | X1 != k2_xboole_0(sK2,k1_tarski(sK2))
% 2.49/1.01      | r2_hidden(X0,X1) = iProver_top
% 2.49/1.01      | r2_hidden(k2_xboole_0(sK2,k1_tarski(sK2)),k2_xboole_0(sK2,k1_tarski(sK2))) != iProver_top ),
% 2.49/1.01      inference(predicate_to_equality,[status(thm)],[c_4467]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_4472,plain,
% 2.49/1.01      ( sK1 != k2_xboole_0(sK2,k1_tarski(sK2))
% 2.49/1.01      | r2_hidden(k2_xboole_0(sK2,k1_tarski(sK2)),k2_xboole_0(sK2,k1_tarski(sK2))) != iProver_top
% 2.49/1.01      | r2_hidden(sK1,sK1) = iProver_top ),
% 2.49/1.01      inference(instantiation,[status(thm)],[c_4470]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_4004,plain,
% 2.49/1.01      ( r2_hidden(sK2,k2_xboole_0(sK2,k1_tarski(sK2))) = iProver_top ),
% 2.49/1.01      inference(predicate_to_equality,[status(thm)],[c_4003]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_2624,plain,
% 2.49/1.01      ( v3_ordinal1(k2_xboole_0(sK2,k1_tarski(sK2)))
% 2.49/1.01      | ~ v3_ordinal1(sK2) ),
% 2.49/1.01      inference(instantiation,[status(thm)],[c_11]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_2625,plain,
% 2.49/1.01      ( v3_ordinal1(k2_xboole_0(sK2,k1_tarski(sK2))) = iProver_top
% 2.49/1.01      | v3_ordinal1(sK2) != iProver_top ),
% 2.49/1.01      inference(predicate_to_equality,[status(thm)],[c_2624]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_2573,plain,
% 2.49/1.01      ( r1_ordinal1(sK1,k2_xboole_0(sK1,k1_tarski(sK1))) = iProver_top
% 2.49/1.01      | v3_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1))) != iProver_top
% 2.49/1.01      | v3_ordinal1(sK1) != iProver_top ),
% 2.49/1.01      inference(instantiation,[status(thm)],[c_2543]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_1885,plain,
% 2.49/1.01      ( X0 = k2_xboole_0(X1,k1_tarski(X1))
% 2.49/1.01      | r1_tarski(X0,k2_xboole_0(X1,k1_tarski(X1))) != iProver_top
% 2.49/1.01      | r1_tarski(k2_xboole_0(X1,k1_tarski(X1)),X0) != iProver_top ),
% 2.49/1.01      inference(predicate_to_equality,[status(thm)],[c_1884]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_1887,plain,
% 2.49/1.01      ( sK1 = k2_xboole_0(sK1,k1_tarski(sK1))
% 2.49/1.01      | r1_tarski(k2_xboole_0(sK1,k1_tarski(sK1)),sK1) != iProver_top
% 2.49/1.01      | r1_tarski(sK1,k2_xboole_0(sK1,k1_tarski(sK1))) != iProver_top ),
% 2.49/1.01      inference(instantiation,[status(thm)],[c_1885]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_1840,plain,
% 2.49/1.01      ( r1_ordinal1(sK1,k2_xboole_0(sK1,k1_tarski(sK1))) != iProver_top
% 2.49/1.01      | r1_tarski(sK1,k2_xboole_0(sK1,k1_tarski(sK1))) = iProver_top
% 2.49/1.01      | v3_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1))) != iProver_top
% 2.49/1.01      | v3_ordinal1(sK1) != iProver_top ),
% 2.49/1.01      inference(instantiation,[status(thm)],[c_1838]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_592,plain,
% 2.49/1.01      ( r2_hidden(X0,X1) != iProver_top
% 2.49/1.01      | r1_tarski(k2_xboole_0(X0,k1_tarski(X0)),X1) = iProver_top
% 2.49/1.01      | v3_ordinal1(X0) != iProver_top
% 2.49/1.01      | v3_ordinal1(X1) != iProver_top ),
% 2.49/1.01      inference(predicate_to_equality,[status(thm)],[c_591]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_594,plain,
% 2.49/1.01      ( r2_hidden(sK1,sK1) != iProver_top
% 2.49/1.01      | r1_tarski(k2_xboole_0(sK1,k1_tarski(sK1)),sK1) = iProver_top
% 2.49/1.01      | v3_ordinal1(sK1) != iProver_top ),
% 2.49/1.01      inference(instantiation,[status(thm)],[c_592]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_355,plain,
% 2.49/1.01      ( ~ v3_ordinal1(X0)
% 2.49/1.01      | v3_ordinal1(sK0(X0))
% 2.49/1.01      | k2_xboole_0(sK2,k1_tarski(sK2)) = sK1
% 2.49/1.01      | sK1 != X0 ),
% 2.49/1.01      inference(resolution_lifted,[status(thm)],[c_18,c_23]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_356,plain,
% 2.49/1.01      ( v3_ordinal1(sK0(sK1))
% 2.49/1.01      | ~ v3_ordinal1(sK1)
% 2.49/1.01      | k2_xboole_0(sK2,k1_tarski(sK2)) = sK1 ),
% 2.49/1.01      inference(unflattening,[status(thm)],[c_355]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_358,plain,
% 2.49/1.01      ( v3_ordinal1(sK0(sK1)) | k2_xboole_0(sK2,k1_tarski(sK2)) = sK1 ),
% 2.49/1.01      inference(global_propositional_subsumption,
% 2.49/1.01                [status(thm)],
% 2.49/1.01                [c_356,c_26]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_360,plain,
% 2.49/1.01      ( k2_xboole_0(sK2,k1_tarski(sK2)) = sK1
% 2.49/1.01      | v3_ordinal1(sK0(sK1)) = iProver_top ),
% 2.49/1.01      inference(predicate_to_equality,[status(thm)],[c_358]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_341,plain,
% 2.49/1.01      ( ~ v3_ordinal1(X0)
% 2.49/1.01      | v3_ordinal1(sK0(X0))
% 2.49/1.01      | v3_ordinal1(sK2)
% 2.49/1.01      | sK1 != X0 ),
% 2.49/1.01      inference(resolution_lifted,[status(thm)],[c_18,c_25]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_342,plain,
% 2.49/1.01      ( v3_ordinal1(sK0(sK1)) | v3_ordinal1(sK2) | ~ v3_ordinal1(sK1) ),
% 2.49/1.01      inference(unflattening,[status(thm)],[c_341]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_344,plain,
% 2.49/1.01      ( v3_ordinal1(sK2) | v3_ordinal1(sK0(sK1)) ),
% 2.49/1.01      inference(global_propositional_subsumption,
% 2.49/1.01                [status(thm)],
% 2.49/1.01                [c_342,c_26]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_345,plain,
% 2.49/1.01      ( v3_ordinal1(sK0(sK1)) | v3_ordinal1(sK2) ),
% 2.49/1.01      inference(renaming,[status(thm)],[c_344]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_346,plain,
% 2.49/1.01      ( v3_ordinal1(sK0(sK1)) = iProver_top
% 2.49/1.01      | v3_ordinal1(sK2) = iProver_top ),
% 2.49/1.01      inference(predicate_to_equality,[status(thm)],[c_345]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_66,plain,
% 2.49/1.01      ( v3_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1))) = iProver_top
% 2.49/1.01      | v3_ordinal1(sK1) != iProver_top ),
% 2.49/1.01      inference(instantiation,[status(thm)],[c_64]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_45,plain,
% 2.49/1.01      ( v4_ordinal1(sK1) = iProver_top
% 2.49/1.01      | v3_ordinal1(sK0(sK1)) = iProver_top
% 2.49/1.01      | v3_ordinal1(sK1) != iProver_top ),
% 2.49/1.01      inference(instantiation,[status(thm)],[c_43]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(c_27,plain,
% 2.49/1.01      ( v3_ordinal1(sK1) = iProver_top ),
% 2.49/1.01      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.49/1.01  
% 2.49/1.01  cnf(contradiction,plain,
% 2.49/1.01      ( $false ),
% 2.49/1.01      inference(minisat,
% 2.49/1.01                [status(thm)],
% 2.49/1.01                [c_7657,c_7326,c_5985,c_4472,c_4004,c_2625,c_2573,c_2306,
% 2.49/1.01                 c_1887,c_1840,c_1819,c_1818,c_594,c_360,c_346,c_92,c_82,
% 2.49/1.01                 c_78,c_70,c_66,c_53,c_45,c_27,c_26]) ).
% 2.49/1.01  
% 2.49/1.01  
% 2.49/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.49/1.01  
% 2.49/1.01  ------                               Statistics
% 2.49/1.01  
% 2.49/1.01  ------ General
% 2.49/1.01  
% 2.49/1.01  abstr_ref_over_cycles:                  0
% 2.49/1.01  abstr_ref_under_cycles:                 0
% 2.49/1.01  gc_basic_clause_elim:                   0
% 2.49/1.01  forced_gc_time:                         0
% 2.49/1.01  parsing_time:                           0.014
% 2.49/1.01  unif_index_cands_time:                  0.
% 2.49/1.01  unif_index_add_time:                    0.
% 2.49/1.01  orderings_time:                         0.
% 2.49/1.01  out_proof_time:                         0.013
% 2.49/1.01  total_time:                             0.225
% 2.49/1.01  num_of_symbols:                         41
% 2.49/1.01  num_of_terms:                           5096
% 2.49/1.01  
% 2.49/1.01  ------ Preprocessing
% 2.49/1.01  
% 2.49/1.01  num_of_splits:                          0
% 2.49/1.01  num_of_split_atoms:                     0
% 2.49/1.01  num_of_reused_defs:                     0
% 2.49/1.01  num_eq_ax_congr_red:                    12
% 2.49/1.01  num_of_sem_filtered_clauses:            1
% 2.49/1.01  num_of_subtypes:                        0
% 2.49/1.01  monotx_restored_types:                  0
% 2.49/1.01  sat_num_of_epr_types:                   0
% 2.49/1.01  sat_num_of_non_cyclic_types:            0
% 2.49/1.01  sat_guarded_non_collapsed_types:        0
% 2.49/1.01  num_pure_diseq_elim:                    0
% 2.49/1.01  simp_replaced_by:                       0
% 2.49/1.01  res_preprocessed:                       113
% 2.49/1.01  prep_upred:                             0
% 2.49/1.01  prep_unflattend:                        36
% 2.49/1.01  smt_new_axioms:                         0
% 2.49/1.01  pred_elim_cands:                        5
% 2.49/1.01  pred_elim:                              0
% 2.49/1.01  pred_elim_cl:                           0
% 2.49/1.01  pred_elim_cycles:                       4
% 2.49/1.01  merged_defs:                            0
% 2.49/1.01  merged_defs_ncl:                        0
% 2.49/1.01  bin_hyper_res:                          0
% 2.49/1.01  prep_cycles:                            4
% 2.49/1.01  pred_elim_time:                         0.011
% 2.49/1.01  splitting_time:                         0.
% 2.49/1.01  sem_filter_time:                        0.
% 2.49/1.01  monotx_time:                            0.001
% 2.49/1.01  subtype_inf_time:                       0.
% 2.49/1.01  
% 2.49/1.01  ------ Problem properties
% 2.49/1.01  
% 2.49/1.01  clauses:                                24
% 2.49/1.01  conjectures:                            6
% 2.49/1.01  epr:                                    7
% 2.49/1.01  horn:                                   20
% 2.49/1.01  ground:                                 3
% 2.49/1.01  unary:                                  4
% 2.49/1.01  binary:                                 4
% 2.49/1.01  lits:                                   70
% 2.49/1.01  lits_eq:                                9
% 2.49/1.01  fd_pure:                                0
% 2.49/1.01  fd_pseudo:                              0
% 2.49/1.01  fd_cond:                                0
% 2.49/1.01  fd_pseudo_cond:                         3
% 2.49/1.01  ac_symbols:                             0
% 2.49/1.01  
% 2.49/1.01  ------ Propositional Solver
% 2.49/1.01  
% 2.49/1.01  prop_solver_calls:                      28
% 2.49/1.01  prop_fast_solver_calls:                 1145
% 2.49/1.01  smt_solver_calls:                       0
% 2.49/1.01  smt_fast_solver_calls:                  0
% 2.49/1.01  prop_num_of_clauses:                    2202
% 2.49/1.01  prop_preprocess_simplified:             7740
% 2.49/1.01  prop_fo_subsumed:                       40
% 2.49/1.01  prop_solver_time:                       0.
% 2.49/1.01  smt_solver_time:                        0.
% 2.49/1.01  smt_fast_solver_time:                   0.
% 2.49/1.01  prop_fast_solver_time:                  0.
% 2.49/1.01  prop_unsat_core_time:                   0.
% 2.49/1.01  
% 2.49/1.01  ------ QBF
% 2.49/1.01  
% 2.49/1.01  qbf_q_res:                              0
% 2.49/1.01  qbf_num_tautologies:                    0
% 2.49/1.01  qbf_prep_cycles:                        0
% 2.49/1.01  
% 2.49/1.01  ------ BMC1
% 2.49/1.01  
% 2.49/1.01  bmc1_current_bound:                     -1
% 2.49/1.01  bmc1_last_solved_bound:                 -1
% 2.49/1.01  bmc1_unsat_core_size:                   -1
% 2.49/1.01  bmc1_unsat_core_parents_size:           -1
% 2.49/1.01  bmc1_merge_next_fun:                    0
% 2.49/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.49/1.01  
% 2.49/1.01  ------ Instantiation
% 2.49/1.01  
% 2.49/1.01  inst_num_of_clauses:                    613
% 2.49/1.01  inst_num_in_passive:                    338
% 2.49/1.01  inst_num_in_active:                     264
% 2.49/1.01  inst_num_in_unprocessed:                11
% 2.49/1.01  inst_num_of_loops:                      320
% 2.49/1.01  inst_num_of_learning_restarts:          0
% 2.49/1.01  inst_num_moves_active_passive:          54
% 2.49/1.01  inst_lit_activity:                      0
% 2.49/1.01  inst_lit_activity_moves:                0
% 2.49/1.01  inst_num_tautologies:                   0
% 2.49/1.01  inst_num_prop_implied:                  0
% 2.49/1.01  inst_num_existing_simplified:           0
% 2.49/1.01  inst_num_eq_res_simplified:             0
% 2.49/1.01  inst_num_child_elim:                    0
% 2.49/1.01  inst_num_of_dismatching_blockings:      451
% 2.49/1.01  inst_num_of_non_proper_insts:           725
% 2.49/1.01  inst_num_of_duplicates:                 0
% 2.49/1.01  inst_inst_num_from_inst_to_res:         0
% 2.49/1.01  inst_dismatching_checking_time:         0.
% 2.49/1.01  
% 2.49/1.01  ------ Resolution
% 2.49/1.01  
% 2.49/1.01  res_num_of_clauses:                     0
% 2.49/1.01  res_num_in_passive:                     0
% 2.49/1.01  res_num_in_active:                      0
% 2.49/1.01  res_num_of_loops:                       117
% 2.49/1.01  res_forward_subset_subsumed:            106
% 2.49/1.01  res_backward_subset_subsumed:           2
% 2.49/1.01  res_forward_subsumed:                   0
% 2.49/1.01  res_backward_subsumed:                  0
% 2.49/1.01  res_forward_subsumption_resolution:     0
% 2.49/1.01  res_backward_subsumption_resolution:    0
% 2.49/1.01  res_clause_to_clause_subsumption:       1126
% 2.49/1.01  res_orphan_elimination:                 0
% 2.49/1.01  res_tautology_del:                      68
% 2.49/1.01  res_num_eq_res_simplified:              0
% 2.49/1.01  res_num_sel_changes:                    0
% 2.49/1.01  res_moves_from_active_to_pass:          0
% 2.49/1.01  
% 2.49/1.01  ------ Superposition
% 2.49/1.01  
% 2.49/1.01  sup_time_total:                         0.
% 2.49/1.01  sup_time_generating:                    0.
% 2.49/1.01  sup_time_sim_full:                      0.
% 2.49/1.01  sup_time_sim_immed:                     0.
% 2.49/1.01  
% 2.49/1.01  sup_num_of_clauses:                     129
% 2.49/1.01  sup_num_in_active:                      61
% 2.49/1.01  sup_num_in_passive:                     68
% 2.49/1.01  sup_num_of_loops:                       62
% 2.49/1.01  sup_fw_superposition:                   96
% 2.49/1.01  sup_bw_superposition:                   120
% 2.49/1.01  sup_immediate_simplified:               67
% 2.49/1.01  sup_given_eliminated:                   0
% 2.49/1.01  comparisons_done:                       0
% 2.49/1.01  comparisons_avoided:                    0
% 2.49/1.01  
% 2.49/1.01  ------ Simplifications
% 2.49/1.01  
% 2.49/1.01  
% 2.49/1.01  sim_fw_subset_subsumed:                 24
% 2.49/1.01  sim_bw_subset_subsumed:                 4
% 2.49/1.01  sim_fw_subsumed:                        16
% 2.49/1.01  sim_bw_subsumed:                        15
% 2.49/1.01  sim_fw_subsumption_res:                 3
% 2.49/1.01  sim_bw_subsumption_res:                 0
% 2.49/1.01  sim_tautology_del:                      9
% 2.49/1.01  sim_eq_tautology_del:                   14
% 2.49/1.01  sim_eq_res_simp:                        0
% 2.49/1.01  sim_fw_demodulated:                     1
% 2.49/1.01  sim_bw_demodulated:                     0
% 2.49/1.01  sim_light_normalised:                   12
% 2.49/1.01  sim_joinable_taut:                      0
% 2.49/1.01  sim_joinable_simp:                      0
% 2.49/1.01  sim_ac_normalised:                      0
% 2.49/1.01  sim_smt_subsumption:                    0
% 2.49/1.01  
%------------------------------------------------------------------------------
