%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:54:03 EST 2020

% Result     : Theorem 6.69s
% Output     : CNFRefutation 6.69s
% Verified   : 
% Statistics : Number of formulae       :  183 ( 726 expanded)
%              Number of clauses        :   97 ( 204 expanded)
%              Number of leaves         :   22 ( 169 expanded)
%              Depth                    :   19
%              Number of atoms          :  671 (3010 expanded)
%              Number of equality atoms :  112 ( 556 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r2_hidden(X0,k1_ordinal1(X1))
              | ~ r1_ordinal1(X0,X1) )
            & ( r1_ordinal1(X0,X1)
              | ~ r2_hidden(X0,k1_ordinal1(X1)) ) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f80,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f4,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f102,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f80,f65])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
    <=> ( X0 = X1
        | r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(flattening,[],[f45])).

fof(f72,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f98,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) ) ),
    inference(definition_unfolding,[],[f72,f65])).

fof(f16,conjecture,(
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

fof(f17,negated_conjecture,(
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
    inference(negated_conjecture,[],[f16])).

fof(f18,plain,(
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
    inference(rectify,[],[f17])).

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f56,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k1_ordinal1(X1) = X0
          & v3_ordinal1(X1) )
     => ( k1_ordinal1(sK5) = X0
        & v3_ordinal1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,
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
   => ( ( ( v4_ordinal1(sK4)
          & ? [X1] :
              ( k1_ordinal1(X1) = sK4
              & v3_ordinal1(X1) ) )
        | ( ! [X2] :
              ( k1_ordinal1(X2) != sK4
              | ~ v3_ordinal1(X2) )
          & ~ v4_ordinal1(sK4) ) )
      & v3_ordinal1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,
    ( ( ( v4_ordinal1(sK4)
        & k1_ordinal1(sK5) = sK4
        & v3_ordinal1(sK5) )
      | ( ! [X2] :
            ( k1_ordinal1(X2) != sK4
            | ~ v3_ordinal1(X2) )
        & ~ v4_ordinal1(sK4) ) )
    & v3_ordinal1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f33,f56,f55])).

fof(f94,plain,(
    ! [X2] :
      ( v4_ordinal1(sK4)
      | k1_ordinal1(X2) != sK4
      | ~ v3_ordinal1(X2) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f106,plain,(
    ! [X2] :
      ( v4_ordinal1(sK4)
      | k2_xboole_0(X2,k1_tarski(X2)) != sK4
      | ~ v3_ordinal1(X2) ) ),
    inference(definition_unfolding,[],[f94,f65])).

fof(f88,plain,(
    v3_ordinal1(sK4) ),
    inference(cnf_transformation,[],[f57])).

fof(f89,plain,
    ( v3_ordinal1(sK5)
    | ~ v4_ordinal1(sK4) ),
    inference(cnf_transformation,[],[f57])).

fof(f91,plain,
    ( k1_ordinal1(sK5) = sK4
    | ~ v4_ordinal1(sK4) ),
    inference(cnf_transformation,[],[f57])).

fof(f108,plain,
    ( k2_xboole_0(sK5,k1_tarski(sK5)) = sK4
    | ~ v4_ordinal1(sK4) ),
    inference(definition_unfolding,[],[f91,f65])).

fof(f15,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ r2_hidden(X0,k1_ordinal1(X1))
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f103,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f79,f65])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f96,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | X0 != X1 ) ),
    inference(definition_unfolding,[],[f74,f65])).

fof(f112,plain,(
    ! [X1] : r2_hidden(X1,k2_xboole_0(X1,k1_tarski(X1))) ),
    inference(equality_resolution,[],[f96])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v3_ordinal1(X1)
     => ( r2_hidden(X0,X1)
       => v3_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f75,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f11,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
          <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X0,X1)
          <=> r1_ordinal1(k1_ordinal1(X0),X1) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r2_hidden(X0,X1)
              | ~ r1_ordinal1(k1_ordinal1(X0),X1) )
            & ( r1_ordinal1(k1_ordinal1(X0),X1)
              | ~ r2_hidden(X0,X1) ) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_ordinal1(k1_ordinal1(X0),X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f100,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f78,f65])).

fof(f14,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v4_ordinal1(X0)
      <=> ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X1,X0)
             => r2_hidden(k1_ordinal1(X1),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ( v4_ordinal1(X0)
      <=> ! [X1] :
            ( r2_hidden(k1_ordinal1(X1),X0)
            | ~ r2_hidden(X1,X0)
            | ~ v3_ordinal1(X1) ) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f31,plain,(
    ! [X0] :
      ( ( v4_ordinal1(X0)
      <=> ! [X1] :
            ( r2_hidden(k1_ordinal1(X1),X0)
            | ~ r2_hidden(X1,X0)
            | ~ v3_ordinal1(X1) ) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f51,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f52,plain,(
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
    inference(rectify,[],[f51])).

fof(f53,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k1_ordinal1(X1),X0)
          & r2_hidden(X1,X0)
          & v3_ordinal1(X1) )
     => ( ~ r2_hidden(k1_ordinal1(sK3(X0)),X0)
        & r2_hidden(sK3(X0),X0)
        & v3_ordinal1(sK3(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0] :
      ( ( ( v4_ordinal1(X0)
          | ( ~ r2_hidden(k1_ordinal1(sK3(X0)),X0)
            & r2_hidden(sK3(X0),X0)
            & v3_ordinal1(sK3(X0)) ) )
        & ( ! [X2] :
              ( r2_hidden(k1_ordinal1(X2),X0)
              | ~ r2_hidden(X2,X0)
              | ~ v3_ordinal1(X2) )
          | ~ v4_ordinal1(X0) ) )
      | ~ v3_ordinal1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f52,f53])).

fof(f83,plain,(
    ! [X2,X0] :
      ( r2_hidden(k1_ordinal1(X2),X0)
      | ~ r2_hidden(X2,X0)
      | ~ v3_ordinal1(X2)
      | ~ v4_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f105,plain,(
    ! [X2,X0] :
      ( r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),X0)
      | ~ r2_hidden(X2,X0)
      | ~ v3_ordinal1(X2)
      | ~ v4_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f83,f65])).

fof(f92,plain,(
    ! [X2] :
      ( k1_ordinal1(sK5) = sK4
      | k1_ordinal1(X2) != sK4
      | ~ v3_ordinal1(X2) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f107,plain,(
    ! [X2] :
      ( k2_xboole_0(sK5,k1_tarski(sK5)) = sK4
      | k2_xboole_0(X2,k1_tarski(X2)) != sK4
      | ~ v3_ordinal1(X2) ) ),
    inference(definition_unfolding,[],[f92,f65,f65])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X1,X0)
        | r1_ordinal1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f86,plain,(
    ! [X0] :
      ( v4_ordinal1(X0)
      | ~ r2_hidden(k1_ordinal1(sK3(X0)),X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f104,plain,(
    ! [X0] :
      ( v4_ordinal1(X0)
      | ~ r2_hidden(k2_xboole_0(sK3(X0),k1_tarski(sK3(X0))),X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f86,f65])).

fof(f85,plain,(
    ! [X0] :
      ( v4_ordinal1(X0)
      | r2_hidden(sK3(X0),X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f34])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f35,f36])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f6,axiom,(
    ! [X0] :
    ? [X1] :
    ! [X2] :
      ( r2_hidden(X2,X1)
    <=> ( v3_ordinal1(X2)
        & r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
    ? [X1] :
    ! [X2] :
      ( ( r2_hidden(X2,X1)
        | ~ v3_ordinal1(X2)
        | ~ r2_hidden(X2,X0) )
      & ( ( v3_ordinal1(X2)
          & r2_hidden(X2,X0) )
        | ~ r2_hidden(X2,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f42,plain,(
    ! [X0] :
    ? [X1] :
    ! [X2] :
      ( ( r2_hidden(X2,X1)
        | ~ v3_ordinal1(X2)
        | ~ r2_hidden(X2,X0) )
      & ( ( v3_ordinal1(X2)
          & r2_hidden(X2,X0) )
        | ~ r2_hidden(X2,X1) ) ) ),
    inference(flattening,[],[f41])).

fof(f43,plain,(
    ! [X0] :
      ( ? [X1] :
        ! [X2] :
          ( ( r2_hidden(X2,X1)
            | ~ v3_ordinal1(X2)
            | ~ r2_hidden(X2,X0) )
          & ( ( v3_ordinal1(X2)
              & r2_hidden(X2,X0) )
            | ~ r2_hidden(X2,X1) ) )
     => ! [X2] :
          ( ( r2_hidden(X2,sK1(X0))
            | ~ v3_ordinal1(X2)
            | ~ r2_hidden(X2,X0) )
          & ( ( v3_ordinal1(X2)
              & r2_hidden(X2,X0) )
            | ~ r2_hidden(X2,sK1(X0)) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X2] :
      ( ( r2_hidden(X2,sK1(X0))
        | ~ v3_ordinal1(X2)
        | ~ r2_hidden(X2,X0) )
      & ( ( v3_ordinal1(X2)
          & r2_hidden(X2,X0) )
        | ~ r2_hidden(X2,sK1(X0)) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f42,f43])).

fof(f70,plain,(
    ! [X2,X0] :
      ( r2_hidden(X2,sK1(X0))
      | ~ v3_ordinal1(X2)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f58,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f69,plain,(
    ! [X2,X0] :
      ( v3_ordinal1(X2)
      | ~ r2_hidden(X2,sK1(X0)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f10,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k1_ordinal1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f76,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f99,plain,(
    ! [X0] :
      ( v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0)))
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f76,f65])).

fof(f84,plain,(
    ! [X0] :
      ( v4_ordinal1(X0)
      | v3_ordinal1(sK3(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_20,plain,
    ( ~ r1_ordinal1(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_15,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
    | X1 = X0 ),
    inference(cnf_transformation,[],[f98])).

cnf(c_5314,plain,
    ( ~ r1_ordinal1(X0,X1)
    | r2_hidden(X0,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0)
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_20,c_15])).

cnf(c_977,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_976,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_5272,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_977,c_976])).

cnf(c_12011,plain,
    ( ~ r1_ordinal1(X0,X1)
    | r2_hidden(X0,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0)
    | X0 = X1 ),
    inference(resolution,[status(thm)],[c_5314,c_5272])).

cnf(c_29,negated_conjecture,
    ( v4_ordinal1(sK4)
    | ~ v3_ordinal1(X0)
    | k2_xboole_0(X0,k1_tarski(X0)) != sK4 ),
    inference(cnf_transformation,[],[f106])).

cnf(c_22075,plain,
    ( ~ r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),sK4)
    | r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),sK4)
    | v4_ordinal1(sK4)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0)))
    | ~ v3_ordinal1(sK4) ),
    inference(resolution,[status(thm)],[c_12011,c_29])).

cnf(c_35,negated_conjecture,
    ( v3_ordinal1(sK4) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_34,negated_conjecture,
    ( ~ v4_ordinal1(sK4)
    | v3_ordinal1(sK5) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_32,negated_conjecture,
    ( ~ v4_ordinal1(sK4)
    | k2_xboole_0(sK5,k1_tarski(sK5)) = sK4 ),
    inference(cnf_transformation,[],[f108])).

cnf(c_28,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_50,plain,
    ( ~ r2_hidden(sK4,sK4)
    | ~ r1_tarski(sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_21,plain,
    ( r1_ordinal1(X0,X1)
    | ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_71,plain,
    ( r1_ordinal1(sK4,sK4)
    | ~ r2_hidden(sK4,k2_xboole_0(sK4,k1_tarski(sK4)))
    | ~ v3_ordinal1(sK4) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_87,plain,
    ( ~ r2_hidden(sK4,k2_xboole_0(sK4,k1_tarski(sK4)))
    | r2_hidden(sK4,sK4)
    | sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_13,plain,
    ( r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0))) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_93,plain,
    ( r2_hidden(sK4,k2_xboole_0(sK4,k1_tarski(sK4))) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_8,plain,
    ( ~ r1_ordinal1(X0,X1)
    | r1_tarski(X0,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_104,plain,
    ( ~ r1_ordinal1(sK4,sK4)
    | r1_tarski(sK4,sK4)
    | ~ v3_ordinal1(sK4) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v3_ordinal1(X1)
    | v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_2433,plain,
    ( v3_ordinal1(X0)
    | ~ v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) ),
    inference(resolution,[status(thm)],[c_16,c_13])).

cnf(c_979,plain,
    ( ~ r1_ordinal1(X0,X1)
    | r1_ordinal1(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_1954,plain,
    ( ~ r1_ordinal1(X0,X1)
    | r1_ordinal1(k2_xboole_0(X2,k1_tarski(X2)),X1)
    | k2_xboole_0(X2,k1_tarski(X2)) != X0 ),
    inference(instantiation,[status(thm)],[c_979])).

cnf(c_2450,plain,
    ( r1_ordinal1(k2_xboole_0(sK5,k1_tarski(sK5)),X0)
    | ~ r1_ordinal1(sK4,X0)
    | k2_xboole_0(sK5,k1_tarski(sK5)) != sK4 ),
    inference(instantiation,[status(thm)],[c_1954])).

cnf(c_2452,plain,
    ( r1_ordinal1(k2_xboole_0(sK5,k1_tarski(sK5)),sK4)
    | ~ r1_ordinal1(sK4,sK4)
    | k2_xboole_0(sK5,k1_tarski(sK5)) != sK4 ),
    inference(instantiation,[status(thm)],[c_2450])).

cnf(c_2802,plain,
    ( X0 != X1
    | X0 = k2_xboole_0(X2,k1_tarski(X2))
    | k2_xboole_0(X2,k1_tarski(X2)) != X1 ),
    inference(instantiation,[status(thm)],[c_977])).

cnf(c_4868,plain,
    ( X0 = k2_xboole_0(sK5,k1_tarski(sK5))
    | X0 != sK4
    | k2_xboole_0(sK5,k1_tarski(sK5)) != sK4 ),
    inference(instantiation,[status(thm)],[c_2802])).

cnf(c_4870,plain,
    ( k2_xboole_0(sK5,k1_tarski(sK5)) != sK4
    | sK4 = k2_xboole_0(sK5,k1_tarski(sK5))
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_4868])).

cnf(c_18,plain,
    ( ~ r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),X1)
    | r2_hidden(X0,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_4873,plain,
    ( ~ r1_ordinal1(k2_xboole_0(sK5,k1_tarski(sK5)),X0)
    | r2_hidden(sK5,X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(sK5) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_4875,plain,
    ( ~ r1_ordinal1(k2_xboole_0(sK5,k1_tarski(sK5)),sK4)
    | r2_hidden(sK5,sK4)
    | ~ v3_ordinal1(sK5)
    | ~ v3_ordinal1(sK4) ),
    inference(instantiation,[status(thm)],[c_4873])).

cnf(c_27,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),X1)
    | ~ v4_ordinal1(X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_202,plain,
    ( ~ v3_ordinal1(X1)
    | ~ v4_ordinal1(X1)
    | r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),X1)
    | ~ r2_hidden(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_27,c_16])).

cnf(c_203,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),X1)
    | ~ v4_ordinal1(X1)
    | ~ v3_ordinal1(X1) ),
    inference(renaming,[status(thm)],[c_202])).

cnf(c_9025,plain,
    ( r2_hidden(k2_xboole_0(sK5,k1_tarski(sK5)),X0)
    | ~ r2_hidden(sK5,X0)
    | ~ v4_ordinal1(X0)
    | ~ v3_ordinal1(X0) ),
    inference(instantiation,[status(thm)],[c_203])).

cnf(c_9042,plain,
    ( r2_hidden(k2_xboole_0(sK5,k1_tarski(sK5)),sK4)
    | ~ r2_hidden(sK5,sK4)
    | ~ v4_ordinal1(sK4)
    | ~ v3_ordinal1(sK4) ),
    inference(instantiation,[status(thm)],[c_9025])).

cnf(c_978,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_18212,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k2_xboole_0(sK5,k1_tarski(sK5)),X2)
    | X1 != X2
    | X0 != k2_xboole_0(sK5,k1_tarski(sK5)) ),
    inference(instantiation,[status(thm)],[c_978])).

cnf(c_18234,plain,
    ( ~ r2_hidden(k2_xboole_0(sK5,k1_tarski(sK5)),sK4)
    | r2_hidden(sK4,sK4)
    | sK4 != k2_xboole_0(sK5,k1_tarski(sK5))
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_18212])).

cnf(c_22284,plain,
    ( ~ v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0)))
    | r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),sK4)
    | ~ r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_22075,c_35,c_34,c_32,c_50,c_71,c_87,c_93,c_104,c_2433,c_2452,c_4870,c_4875,c_9042,c_18234])).

cnf(c_22285,plain,
    ( ~ r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),sK4)
    | r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),sK4)
    | ~ v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) ),
    inference(renaming,[status(thm)],[c_22284])).

cnf(c_31,negated_conjecture,
    ( ~ v3_ordinal1(X0)
    | k2_xboole_0(X0,k1_tarski(X0)) != sK4
    | k2_xboole_0(sK5,k1_tarski(sK5)) = sK4 ),
    inference(cnf_transformation,[],[f107])).

cnf(c_12006,plain,
    ( ~ r1_ordinal1(sK4,k2_xboole_0(X0,k1_tarski(X0)))
    | r2_hidden(sK4,k2_xboole_0(X0,k1_tarski(X0)))
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0)))
    | ~ v3_ordinal1(sK4)
    | k2_xboole_0(sK5,k1_tarski(sK5)) = sK4 ),
    inference(resolution,[status(thm)],[c_5314,c_31])).

cnf(c_12748,plain,
    ( ~ v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0)))
    | ~ r1_ordinal1(sK4,k2_xboole_0(X0,k1_tarski(X0)))
    | r2_hidden(sK4,k2_xboole_0(X0,k1_tarski(X0)))
    | k2_xboole_0(sK5,k1_tarski(sK5)) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_12006,c_35,c_2433])).

cnf(c_12749,plain,
    ( ~ r1_ordinal1(sK4,k2_xboole_0(X0,k1_tarski(X0)))
    | r2_hidden(sK4,k2_xboole_0(X0,k1_tarski(X0)))
    | ~ v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0)))
    | k2_xboole_0(sK5,k1_tarski(sK5)) = sK4 ),
    inference(renaming,[status(thm)],[c_12748])).

cnf(c_6,plain,
    ( r1_ordinal1(X0,X1)
    | r1_ordinal1(X1,X0)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_12772,plain,
    ( r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),sK4)
    | r2_hidden(sK4,k2_xboole_0(X0,k1_tarski(X0)))
    | ~ v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0)))
    | ~ v3_ordinal1(sK4)
    | k2_xboole_0(sK5,k1_tarski(sK5)) = sK4 ),
    inference(resolution,[status(thm)],[c_12749,c_6])).

cnf(c_14640,plain,
    ( ~ v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0)))
    | r2_hidden(sK4,k2_xboole_0(X0,k1_tarski(X0)))
    | r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),sK4)
    | k2_xboole_0(sK5,k1_tarski(sK5)) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_12772,c_35])).

cnf(c_14641,plain,
    ( r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),sK4)
    | r2_hidden(sK4,k2_xboole_0(X0,k1_tarski(X0)))
    | ~ v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0)))
    | k2_xboole_0(sK5,k1_tarski(sK5)) = sK4 ),
    inference(renaming,[status(thm)],[c_14640])).

cnf(c_14670,plain,
    ( r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),sK4)
    | r2_hidden(sK4,k2_xboole_0(X0,k1_tarski(X0)))
    | ~ v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0)))
    | sK4 = k2_xboole_0(sK5,k1_tarski(sK5)) ),
    inference(resolution,[status(thm)],[c_14641,c_5272])).

cnf(c_12004,plain,
    ( ~ r1_ordinal1(sK4,k2_xboole_0(X0,k1_tarski(X0)))
    | r2_hidden(sK4,k2_xboole_0(X0,k1_tarski(X0)))
    | v4_ordinal1(sK4)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0)))
    | ~ v3_ordinal1(sK4) ),
    inference(resolution,[status(thm)],[c_5314,c_29])).

cnf(c_12235,plain,
    ( ~ v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0)))
    | ~ r1_ordinal1(sK4,k2_xboole_0(X0,k1_tarski(X0)))
    | r2_hidden(sK4,k2_xboole_0(X0,k1_tarski(X0)))
    | v4_ordinal1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12004,c_35,c_2433])).

cnf(c_12236,plain,
    ( ~ r1_ordinal1(sK4,k2_xboole_0(X0,k1_tarski(X0)))
    | r2_hidden(sK4,k2_xboole_0(X0,k1_tarski(X0)))
    | v4_ordinal1(sK4)
    | ~ v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) ),
    inference(renaming,[status(thm)],[c_12235])).

cnf(c_12429,plain,
    ( r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),sK4)
    | r2_hidden(sK4,k2_xboole_0(X0,k1_tarski(X0)))
    | v4_ordinal1(sK4)
    | ~ v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0)))
    | ~ v3_ordinal1(sK4) ),
    inference(resolution,[status(thm)],[c_12236,c_6])).

cnf(c_19460,plain,
    ( ~ v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0)))
    | r2_hidden(sK4,k2_xboole_0(X0,k1_tarski(X0)))
    | r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14670,c_35,c_34,c_32,c_50,c_71,c_87,c_93,c_104,c_2452,c_4870,c_4875,c_9042,c_12429,c_18234])).

cnf(c_19461,plain,
    ( r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),sK4)
    | r2_hidden(sK4,k2_xboole_0(X0,k1_tarski(X0)))
    | ~ v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) ),
    inference(renaming,[status(thm)],[c_19460])).

cnf(c_22525,plain,
    ( r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),sK4)
    | r2_hidden(sK4,k2_xboole_0(X0,k1_tarski(X0)))
    | ~ v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) ),
    inference(resolution,[status(thm)],[c_22285,c_19461])).

cnf(c_24,plain,
    ( ~ r2_hidden(k2_xboole_0(sK3(X0),k1_tarski(sK3(X0))),X0)
    | v4_ordinal1(X0)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_22538,plain,
    ( r2_hidden(sK4,k2_xboole_0(sK3(sK4),k1_tarski(sK3(sK4))))
    | v4_ordinal1(sK4)
    | ~ v3_ordinal1(k2_xboole_0(sK3(sK4),k1_tarski(sK3(sK4))))
    | ~ v3_ordinal1(sK4) ),
    inference(resolution,[status(thm)],[c_22525,c_24])).

cnf(c_25,plain,
    ( r2_hidden(sK3(X0),X0)
    | v4_ordinal1(X0)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1571,plain,
    ( r2_hidden(sK3(X0),X0) = iProver_top
    | v4_ordinal1(X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_1562,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),X1) = iProver_top
    | v4_ordinal1(X1) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_203])).

cnf(c_1579,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3864,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v4_ordinal1(X1) != iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1562,c_1579])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,sK1(X1))
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_3683,plain,
    ( ~ r2_hidden(sK0(X0,sK1(X1)),X1)
    | r1_tarski(X0,sK1(X1))
    | ~ v3_ordinal1(sK0(X0,sK1(X1))) ),
    inference(resolution,[status(thm)],[c_0,c_9])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_9596,plain,
    ( r1_tarski(X0,sK1(X0))
    | ~ v3_ordinal1(sK0(X0,sK1(X0))) ),
    inference(resolution,[status(thm)],[c_3683,c_1])).

cnf(c_2431,plain,
    ( r1_tarski(X0,X1)
    | ~ v3_ordinal1(X0)
    | v3_ordinal1(sK0(X0,X1)) ),
    inference(resolution,[status(thm)],[c_16,c_1])).

cnf(c_9768,plain,
    ( r1_tarski(X0,sK1(X0))
    | ~ v3_ordinal1(X0) ),
    inference(resolution,[status(thm)],[c_9596,c_2431])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_9782,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,sK1(X1))
    | ~ v3_ordinal1(X1) ),
    inference(resolution,[status(thm)],[c_9768,c_2])).

cnf(c_9783,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,sK1(X1)) = iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9782])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,sK1(X1))
    | v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1584,plain,
    ( r2_hidden(X0,sK1(X1)) != iProver_top
    | v3_ordinal1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3318,plain,
    ( r2_hidden(X0,sK1(X1)) != iProver_top
    | v4_ordinal1(sK1(X1)) != iProver_top
    | v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) = iProver_top
    | v3_ordinal1(sK1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1562,c_1584])).

cnf(c_17,plain,
    ( ~ v3_ordinal1(X0)
    | v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_82,plain,
    ( v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_99,plain,
    ( r2_hidden(X0,sK1(X1)) != iProver_top
    | v3_ordinal1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_13155,plain,
    ( v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) = iProver_top
    | r2_hidden(X0,sK1(X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3318,c_82,c_99])).

cnf(c_13156,plain,
    ( r2_hidden(X0,sK1(X1)) != iProver_top
    | v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) = iProver_top ),
    inference(renaming,[status(thm)],[c_13155])).

cnf(c_15323,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3864,c_9783,c_13156])).

cnf(c_15335,plain,
    ( v4_ordinal1(X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(k2_xboole_0(sK3(X0),k1_tarski(sK3(X0)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1571,c_15323])).

cnf(c_15404,plain,
    ( v4_ordinal1(X0)
    | ~ v3_ordinal1(X0)
    | v3_ordinal1(k2_xboole_0(sK3(X0),k1_tarski(sK3(X0)))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_15335])).

cnf(c_15406,plain,
    ( v4_ordinal1(sK4)
    | v3_ordinal1(k2_xboole_0(sK3(sK4),k1_tarski(sK3(sK4))))
    | ~ v3_ordinal1(sK4) ),
    inference(instantiation,[status(thm)],[c_15404])).

cnf(c_9795,plain,
    ( r1_ordinal1(X0,sK3(X0))
    | ~ r2_hidden(X0,k2_xboole_0(sK3(X0),k1_tarski(sK3(X0))))
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(sK3(X0)) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_9802,plain,
    ( r1_ordinal1(sK4,sK3(sK4))
    | ~ r2_hidden(sK4,k2_xboole_0(sK3(sK4),k1_tarski(sK3(sK4))))
    | ~ v3_ordinal1(sK3(sK4))
    | ~ v3_ordinal1(sK4) ),
    inference(instantiation,[status(thm)],[c_9795])).

cnf(c_5232,plain,
    ( ~ r1_ordinal1(X0,sK3(X0))
    | r1_tarski(X0,sK3(X0))
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(sK3(X0)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_5234,plain,
    ( ~ r1_ordinal1(sK4,sK3(sK4))
    | r1_tarski(sK4,sK3(sK4))
    | ~ v3_ordinal1(sK3(sK4))
    | ~ v3_ordinal1(sK4) ),
    inference(instantiation,[status(thm)],[c_5232])).

cnf(c_3404,plain,
    ( ~ r1_tarski(X0,sK3(X0))
    | v4_ordinal1(X0)
    | ~ v3_ordinal1(X0) ),
    inference(resolution,[status(thm)],[c_28,c_25])).

cnf(c_3406,plain,
    ( ~ r1_tarski(sK4,sK3(sK4))
    | v4_ordinal1(sK4)
    | ~ v3_ordinal1(sK4) ),
    inference(instantiation,[status(thm)],[c_3404])).

cnf(c_26,plain,
    ( v4_ordinal1(X0)
    | ~ v3_ordinal1(X0)
    | v3_ordinal1(sK3(X0)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_56,plain,
    ( v4_ordinal1(sK4)
    | v3_ordinal1(sK3(sK4))
    | ~ v3_ordinal1(sK4) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_22538,c_18234,c_15406,c_9802,c_9042,c_5234,c_4875,c_4870,c_3406,c_2452,c_104,c_93,c_87,c_71,c_56,c_50,c_32,c_34,c_35])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.20/0.34  % CPULimit   : 60
% 0.20/0.34  % WCLimit    : 600
% 0.20/0.34  % DateTime   : Tue Dec  1 15:47:12 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.35  % Running in FOF mode
% 6.69/1.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.69/1.50  
% 6.69/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 6.69/1.50  
% 6.69/1.50  ------  iProver source info
% 6.69/1.50  
% 6.69/1.50  git: date: 2020-06-30 10:37:57 +0100
% 6.69/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 6.69/1.50  git: non_committed_changes: false
% 6.69/1.50  git: last_make_outside_of_git: false
% 6.69/1.50  
% 6.69/1.50  ------ 
% 6.69/1.50  ------ Parsing...
% 6.69/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 6.69/1.50  
% 6.69/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 6.69/1.50  
% 6.69/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 6.69/1.50  
% 6.69/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 6.69/1.50  ------ Proving...
% 6.69/1.50  ------ Problem Properties 
% 6.69/1.50  
% 6.69/1.50  
% 6.69/1.50  clauses                                 33
% 6.69/1.50  conjectures                             6
% 6.69/1.50  EPR                                     10
% 6.69/1.50  Horn                                    28
% 6.69/1.50  unary                                   5
% 6.69/1.50  binary                                  9
% 6.69/1.50  lits                                    87
% 6.69/1.50  lits eq                                 7
% 6.69/1.50  fd_pure                                 0
% 6.69/1.50  fd_pseudo                               0
% 6.69/1.50  fd_cond                                 0
% 6.69/1.50  fd_pseudo_cond                          2
% 6.69/1.50  AC symbols                              0
% 6.69/1.50  
% 6.69/1.50  ------ Input Options Time Limit: Unbounded
% 6.69/1.50  
% 6.69/1.50  
% 6.69/1.50  ------ 
% 6.69/1.50  Current options:
% 6.69/1.50  ------ 
% 6.69/1.50  
% 6.69/1.50  
% 6.69/1.50  
% 6.69/1.50  
% 6.69/1.50  ------ Proving...
% 6.69/1.50  
% 6.69/1.50  
% 6.69/1.50  % SZS status Theorem for theBenchmark.p
% 6.69/1.50  
% 6.69/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 6.69/1.50  
% 6.69/1.50  fof(f12,axiom,(
% 6.69/1.50    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 6.69/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.69/1.50  
% 6.69/1.50  fof(f28,plain,(
% 6.69/1.50    ! [X0] : (! [X1] : ((r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 6.69/1.50    inference(ennf_transformation,[],[f12])).
% 6.69/1.50  
% 6.69/1.50  fof(f48,plain,(
% 6.69/1.50    ! [X0] : (! [X1] : (((r2_hidden(X0,k1_ordinal1(X1)) | ~r1_ordinal1(X0,X1)) & (r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1)))) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 6.69/1.50    inference(nnf_transformation,[],[f28])).
% 6.69/1.50  
% 6.69/1.50  fof(f80,plain,(
% 6.69/1.50    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 6.69/1.50    inference(cnf_transformation,[],[f48])).
% 6.69/1.50  
% 6.69/1.50  fof(f4,axiom,(
% 6.69/1.50    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 6.69/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.69/1.50  
% 6.69/1.50  fof(f65,plain,(
% 6.69/1.50    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 6.69/1.50    inference(cnf_transformation,[],[f4])).
% 6.69/1.50  
% 6.69/1.50  fof(f102,plain,(
% 6.69/1.50    ( ! [X0,X1] : (r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 6.69/1.50    inference(definition_unfolding,[],[f80,f65])).
% 6.69/1.50  
% 6.69/1.50  fof(f8,axiom,(
% 6.69/1.50    ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <=> (X0 = X1 | r2_hidden(X0,X1)))),
% 6.69/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.69/1.50  
% 6.69/1.50  fof(f45,plain,(
% 6.69/1.50    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & ((X0 = X1 | r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 6.69/1.50    inference(nnf_transformation,[],[f8])).
% 6.69/1.51  
% 6.69/1.51  fof(f46,plain,(
% 6.69/1.51    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 6.69/1.51    inference(flattening,[],[f45])).
% 6.69/1.51  
% 6.69/1.51  fof(f72,plain,(
% 6.69/1.51    ( ! [X0,X1] : (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) )),
% 6.69/1.51    inference(cnf_transformation,[],[f46])).
% 6.69/1.51  
% 6.69/1.51  fof(f98,plain,(
% 6.69/1.51    ( ! [X0,X1] : (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))) )),
% 6.69/1.51    inference(definition_unfolding,[],[f72,f65])).
% 6.69/1.51  
% 6.69/1.51  fof(f16,conjecture,(
% 6.69/1.51    ! [X0] : (v3_ordinal1(X0) => (~(v4_ordinal1(X0) & ? [X1] : (k1_ordinal1(X1) = X0 & v3_ordinal1(X1))) & ~(! [X1] : (v3_ordinal1(X1) => k1_ordinal1(X1) != X0) & ~v4_ordinal1(X0))))),
% 6.69/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.69/1.51  
% 6.69/1.51  fof(f17,negated_conjecture,(
% 6.69/1.51    ~! [X0] : (v3_ordinal1(X0) => (~(v4_ordinal1(X0) & ? [X1] : (k1_ordinal1(X1) = X0 & v3_ordinal1(X1))) & ~(! [X1] : (v3_ordinal1(X1) => k1_ordinal1(X1) != X0) & ~v4_ordinal1(X0))))),
% 6.69/1.51    inference(negated_conjecture,[],[f16])).
% 6.69/1.51  
% 6.69/1.51  fof(f18,plain,(
% 6.69/1.51    ~! [X0] : (v3_ordinal1(X0) => (~(v4_ordinal1(X0) & ? [X1] : (k1_ordinal1(X1) = X0 & v3_ordinal1(X1))) & ~(! [X2] : (v3_ordinal1(X2) => k1_ordinal1(X2) != X0) & ~v4_ordinal1(X0))))),
% 6.69/1.51    inference(rectify,[],[f17])).
% 6.69/1.51  
% 6.69/1.51  fof(f33,plain,(
% 6.69/1.51    ? [X0] : (((v4_ordinal1(X0) & ? [X1] : (k1_ordinal1(X1) = X0 & v3_ordinal1(X1))) | (! [X2] : (k1_ordinal1(X2) != X0 | ~v3_ordinal1(X2)) & ~v4_ordinal1(X0))) & v3_ordinal1(X0))),
% 6.69/1.51    inference(ennf_transformation,[],[f18])).
% 6.69/1.51  
% 6.69/1.51  fof(f56,plain,(
% 6.69/1.51    ( ! [X0] : (? [X1] : (k1_ordinal1(X1) = X0 & v3_ordinal1(X1)) => (k1_ordinal1(sK5) = X0 & v3_ordinal1(sK5))) )),
% 6.69/1.51    introduced(choice_axiom,[])).
% 6.69/1.51  
% 6.69/1.51  fof(f55,plain,(
% 6.69/1.51    ? [X0] : (((v4_ordinal1(X0) & ? [X1] : (k1_ordinal1(X1) = X0 & v3_ordinal1(X1))) | (! [X2] : (k1_ordinal1(X2) != X0 | ~v3_ordinal1(X2)) & ~v4_ordinal1(X0))) & v3_ordinal1(X0)) => (((v4_ordinal1(sK4) & ? [X1] : (k1_ordinal1(X1) = sK4 & v3_ordinal1(X1))) | (! [X2] : (k1_ordinal1(X2) != sK4 | ~v3_ordinal1(X2)) & ~v4_ordinal1(sK4))) & v3_ordinal1(sK4))),
% 6.69/1.51    introduced(choice_axiom,[])).
% 6.69/1.51  
% 6.69/1.51  fof(f57,plain,(
% 6.69/1.51    ((v4_ordinal1(sK4) & (k1_ordinal1(sK5) = sK4 & v3_ordinal1(sK5))) | (! [X2] : (k1_ordinal1(X2) != sK4 | ~v3_ordinal1(X2)) & ~v4_ordinal1(sK4))) & v3_ordinal1(sK4)),
% 6.69/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f33,f56,f55])).
% 6.69/1.51  
% 6.69/1.51  fof(f94,plain,(
% 6.69/1.51    ( ! [X2] : (v4_ordinal1(sK4) | k1_ordinal1(X2) != sK4 | ~v3_ordinal1(X2)) )),
% 6.69/1.51    inference(cnf_transformation,[],[f57])).
% 6.69/1.51  
% 6.69/1.51  fof(f106,plain,(
% 6.69/1.51    ( ! [X2] : (v4_ordinal1(sK4) | k2_xboole_0(X2,k1_tarski(X2)) != sK4 | ~v3_ordinal1(X2)) )),
% 6.69/1.51    inference(definition_unfolding,[],[f94,f65])).
% 6.69/1.51  
% 6.69/1.51  fof(f88,plain,(
% 6.69/1.51    v3_ordinal1(sK4)),
% 6.69/1.51    inference(cnf_transformation,[],[f57])).
% 6.69/1.51  
% 6.69/1.51  fof(f89,plain,(
% 6.69/1.51    v3_ordinal1(sK5) | ~v4_ordinal1(sK4)),
% 6.69/1.51    inference(cnf_transformation,[],[f57])).
% 6.69/1.51  
% 6.69/1.51  fof(f91,plain,(
% 6.69/1.51    k1_ordinal1(sK5) = sK4 | ~v4_ordinal1(sK4)),
% 6.69/1.51    inference(cnf_transformation,[],[f57])).
% 6.69/1.51  
% 6.69/1.51  fof(f108,plain,(
% 6.69/1.51    k2_xboole_0(sK5,k1_tarski(sK5)) = sK4 | ~v4_ordinal1(sK4)),
% 6.69/1.51    inference(definition_unfolding,[],[f91,f65])).
% 6.69/1.51  
% 6.69/1.51  fof(f15,axiom,(
% 6.69/1.51    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 6.69/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.69/1.51  
% 6.69/1.51  fof(f32,plain,(
% 6.69/1.51    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 6.69/1.51    inference(ennf_transformation,[],[f15])).
% 6.69/1.51  
% 6.69/1.51  fof(f87,plain,(
% 6.69/1.51    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 6.69/1.51    inference(cnf_transformation,[],[f32])).
% 6.69/1.51  
% 6.69/1.51  fof(f79,plain,(
% 6.69/1.51    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 6.69/1.51    inference(cnf_transformation,[],[f48])).
% 6.69/1.51  
% 6.69/1.51  fof(f103,plain,(
% 6.69/1.51    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | ~r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 6.69/1.51    inference(definition_unfolding,[],[f79,f65])).
% 6.69/1.51  
% 6.69/1.51  fof(f74,plain,(
% 6.69/1.51    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | X0 != X1) )),
% 6.69/1.51    inference(cnf_transformation,[],[f46])).
% 6.69/1.51  
% 6.69/1.51  fof(f96,plain,(
% 6.69/1.51    ( ! [X0,X1] : (r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | X0 != X1) )),
% 6.69/1.51    inference(definition_unfolding,[],[f74,f65])).
% 6.69/1.51  
% 6.69/1.51  fof(f112,plain,(
% 6.69/1.51    ( ! [X1] : (r2_hidden(X1,k2_xboole_0(X1,k1_tarski(X1)))) )),
% 6.69/1.51    inference(equality_resolution,[],[f96])).
% 6.69/1.51  
% 6.69/1.51  fof(f5,axiom,(
% 6.69/1.51    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 6.69/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.69/1.51  
% 6.69/1.51  fof(f22,plain,(
% 6.69/1.51    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 6.69/1.51    inference(ennf_transformation,[],[f5])).
% 6.69/1.51  
% 6.69/1.51  fof(f23,plain,(
% 6.69/1.51    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 6.69/1.51    inference(flattening,[],[f22])).
% 6.69/1.51  
% 6.69/1.51  fof(f40,plain,(
% 6.69/1.51    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 6.69/1.51    inference(nnf_transformation,[],[f23])).
% 6.69/1.51  
% 6.69/1.51  fof(f66,plain,(
% 6.69/1.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 6.69/1.51    inference(cnf_transformation,[],[f40])).
% 6.69/1.51  
% 6.69/1.51  fof(f9,axiom,(
% 6.69/1.51    ! [X0,X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) => v3_ordinal1(X0)))),
% 6.69/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.69/1.51  
% 6.69/1.51  fof(f24,plain,(
% 6.69/1.51    ! [X0,X1] : ((v3_ordinal1(X0) | ~r2_hidden(X0,X1)) | ~v3_ordinal1(X1))),
% 6.69/1.51    inference(ennf_transformation,[],[f9])).
% 6.69/1.51  
% 6.69/1.51  fof(f25,plain,(
% 6.69/1.51    ! [X0,X1] : (v3_ordinal1(X0) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1))),
% 6.69/1.51    inference(flattening,[],[f24])).
% 6.69/1.51  
% 6.69/1.51  fof(f75,plain,(
% 6.69/1.51    ( ! [X0,X1] : (v3_ordinal1(X0) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1)) )),
% 6.69/1.51    inference(cnf_transformation,[],[f25])).
% 6.69/1.51  
% 6.69/1.51  fof(f11,axiom,(
% 6.69/1.51    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 6.69/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.69/1.51  
% 6.69/1.51  fof(f27,plain,(
% 6.69/1.51    ! [X0] : (! [X1] : ((r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 6.69/1.51    inference(ennf_transformation,[],[f11])).
% 6.69/1.51  
% 6.69/1.51  fof(f47,plain,(
% 6.69/1.51    ! [X0] : (! [X1] : (((r2_hidden(X0,X1) | ~r1_ordinal1(k1_ordinal1(X0),X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1))) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 6.69/1.51    inference(nnf_transformation,[],[f27])).
% 6.69/1.51  
% 6.69/1.51  fof(f78,plain,(
% 6.69/1.51    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_ordinal1(k1_ordinal1(X0),X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 6.69/1.51    inference(cnf_transformation,[],[f47])).
% 6.69/1.51  
% 6.69/1.51  fof(f100,plain,(
% 6.69/1.51    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 6.69/1.51    inference(definition_unfolding,[],[f78,f65])).
% 6.69/1.51  
% 6.69/1.51  fof(f14,axiom,(
% 6.69/1.51    ! [X0] : (v3_ordinal1(X0) => (v4_ordinal1(X0) <=> ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) => r2_hidden(k1_ordinal1(X1),X0)))))),
% 6.69/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.69/1.51  
% 6.69/1.51  fof(f30,plain,(
% 6.69/1.51    ! [X0] : ((v4_ordinal1(X0) <=> ! [X1] : ((r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0)) | ~v3_ordinal1(X1))) | ~v3_ordinal1(X0))),
% 6.69/1.51    inference(ennf_transformation,[],[f14])).
% 6.69/1.51  
% 6.69/1.51  fof(f31,plain,(
% 6.69/1.51    ! [X0] : ((v4_ordinal1(X0) <=> ! [X1] : (r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X1))) | ~v3_ordinal1(X0))),
% 6.69/1.51    inference(flattening,[],[f30])).
% 6.69/1.51  
% 6.69/1.51  fof(f51,plain,(
% 6.69/1.51    ! [X0] : (((v4_ordinal1(X0) | ? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1))) & (! [X1] : (r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X1)) | ~v4_ordinal1(X0))) | ~v3_ordinal1(X0))),
% 6.69/1.51    inference(nnf_transformation,[],[f31])).
% 6.69/1.51  
% 6.69/1.51  fof(f52,plain,(
% 6.69/1.51    ! [X0] : (((v4_ordinal1(X0) | ? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1))) & (! [X2] : (r2_hidden(k1_ordinal1(X2),X0) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2)) | ~v4_ordinal1(X0))) | ~v3_ordinal1(X0))),
% 6.69/1.51    inference(rectify,[],[f51])).
% 6.69/1.51  
% 6.69/1.51  fof(f53,plain,(
% 6.69/1.51    ! [X0] : (? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) => (~r2_hidden(k1_ordinal1(sK3(X0)),X0) & r2_hidden(sK3(X0),X0) & v3_ordinal1(sK3(X0))))),
% 6.69/1.51    introduced(choice_axiom,[])).
% 6.69/1.51  
% 6.69/1.51  fof(f54,plain,(
% 6.69/1.51    ! [X0] : (((v4_ordinal1(X0) | (~r2_hidden(k1_ordinal1(sK3(X0)),X0) & r2_hidden(sK3(X0),X0) & v3_ordinal1(sK3(X0)))) & (! [X2] : (r2_hidden(k1_ordinal1(X2),X0) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2)) | ~v4_ordinal1(X0))) | ~v3_ordinal1(X0))),
% 6.69/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f52,f53])).
% 6.69/1.51  
% 6.69/1.51  fof(f83,plain,(
% 6.69/1.51    ( ! [X2,X0] : (r2_hidden(k1_ordinal1(X2),X0) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2) | ~v4_ordinal1(X0) | ~v3_ordinal1(X0)) )),
% 6.69/1.51    inference(cnf_transformation,[],[f54])).
% 6.69/1.51  
% 6.69/1.51  fof(f105,plain,(
% 6.69/1.51    ( ! [X2,X0] : (r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),X0) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2) | ~v4_ordinal1(X0) | ~v3_ordinal1(X0)) )),
% 6.69/1.51    inference(definition_unfolding,[],[f83,f65])).
% 6.69/1.51  
% 6.69/1.51  fof(f92,plain,(
% 6.69/1.51    ( ! [X2] : (k1_ordinal1(sK5) = sK4 | k1_ordinal1(X2) != sK4 | ~v3_ordinal1(X2)) )),
% 6.69/1.51    inference(cnf_transformation,[],[f57])).
% 6.69/1.51  
% 6.69/1.51  fof(f107,plain,(
% 6.69/1.51    ( ! [X2] : (k2_xboole_0(sK5,k1_tarski(sK5)) = sK4 | k2_xboole_0(X2,k1_tarski(X2)) != sK4 | ~v3_ordinal1(X2)) )),
% 6.69/1.51    inference(definition_unfolding,[],[f92,f65,f65])).
% 6.69/1.51  
% 6.69/1.51  fof(f3,axiom,(
% 6.69/1.51    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)))),
% 6.69/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.69/1.51  
% 6.69/1.51  fof(f20,plain,(
% 6.69/1.51    ! [X0,X1] : ((r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 6.69/1.51    inference(ennf_transformation,[],[f3])).
% 6.69/1.51  
% 6.69/1.51  fof(f21,plain,(
% 6.69/1.51    ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 6.69/1.51    inference(flattening,[],[f20])).
% 6.69/1.51  
% 6.69/1.51  fof(f64,plain,(
% 6.69/1.51    ( ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 6.69/1.51    inference(cnf_transformation,[],[f21])).
% 6.69/1.51  
% 6.69/1.51  fof(f86,plain,(
% 6.69/1.51    ( ! [X0] : (v4_ordinal1(X0) | ~r2_hidden(k1_ordinal1(sK3(X0)),X0) | ~v3_ordinal1(X0)) )),
% 6.69/1.51    inference(cnf_transformation,[],[f54])).
% 6.69/1.51  
% 6.69/1.51  fof(f104,plain,(
% 6.69/1.51    ( ! [X0] : (v4_ordinal1(X0) | ~r2_hidden(k2_xboole_0(sK3(X0),k1_tarski(sK3(X0))),X0) | ~v3_ordinal1(X0)) )),
% 6.69/1.51    inference(definition_unfolding,[],[f86,f65])).
% 6.69/1.51  
% 6.69/1.51  fof(f85,plain,(
% 6.69/1.51    ( ! [X0] : (v4_ordinal1(X0) | r2_hidden(sK3(X0),X0) | ~v3_ordinal1(X0)) )),
% 6.69/1.51    inference(cnf_transformation,[],[f54])).
% 6.69/1.51  
% 6.69/1.51  fof(f1,axiom,(
% 6.69/1.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 6.69/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.69/1.51  
% 6.69/1.51  fof(f19,plain,(
% 6.69/1.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 6.69/1.51    inference(ennf_transformation,[],[f1])).
% 6.69/1.51  
% 6.69/1.51  fof(f34,plain,(
% 6.69/1.51    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 6.69/1.51    inference(nnf_transformation,[],[f19])).
% 6.69/1.51  
% 6.69/1.51  fof(f35,plain,(
% 6.69/1.51    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 6.69/1.51    inference(rectify,[],[f34])).
% 6.69/1.51  
% 6.69/1.51  fof(f36,plain,(
% 6.69/1.51    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 6.69/1.51    introduced(choice_axiom,[])).
% 6.69/1.51  
% 6.69/1.51  fof(f37,plain,(
% 6.69/1.51    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 6.69/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f35,f36])).
% 6.69/1.51  
% 6.69/1.51  fof(f60,plain,(
% 6.69/1.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 6.69/1.51    inference(cnf_transformation,[],[f37])).
% 6.69/1.51  
% 6.69/1.51  fof(f6,axiom,(
% 6.69/1.51    ! [X0] : ? [X1] : ! [X2] : (r2_hidden(X2,X1) <=> (v3_ordinal1(X2) & r2_hidden(X2,X0)))),
% 6.69/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.69/1.51  
% 6.69/1.51  fof(f41,plain,(
% 6.69/1.51    ! [X0] : ? [X1] : ! [X2] : ((r2_hidden(X2,X1) | (~v3_ordinal1(X2) | ~r2_hidden(X2,X0))) & ((v3_ordinal1(X2) & r2_hidden(X2,X0)) | ~r2_hidden(X2,X1)))),
% 6.69/1.51    inference(nnf_transformation,[],[f6])).
% 6.69/1.51  
% 6.69/1.51  fof(f42,plain,(
% 6.69/1.51    ! [X0] : ? [X1] : ! [X2] : ((r2_hidden(X2,X1) | ~v3_ordinal1(X2) | ~r2_hidden(X2,X0)) & ((v3_ordinal1(X2) & r2_hidden(X2,X0)) | ~r2_hidden(X2,X1)))),
% 6.69/1.51    inference(flattening,[],[f41])).
% 6.69/1.51  
% 6.69/1.51  fof(f43,plain,(
% 6.69/1.51    ! [X0] : (? [X1] : ! [X2] : ((r2_hidden(X2,X1) | ~v3_ordinal1(X2) | ~r2_hidden(X2,X0)) & ((v3_ordinal1(X2) & r2_hidden(X2,X0)) | ~r2_hidden(X2,X1))) => ! [X2] : ((r2_hidden(X2,sK1(X0)) | ~v3_ordinal1(X2) | ~r2_hidden(X2,X0)) & ((v3_ordinal1(X2) & r2_hidden(X2,X0)) | ~r2_hidden(X2,sK1(X0)))))),
% 6.69/1.51    introduced(choice_axiom,[])).
% 6.69/1.51  
% 6.69/1.51  fof(f44,plain,(
% 6.69/1.51    ! [X0] : ! [X2] : ((r2_hidden(X2,sK1(X0)) | ~v3_ordinal1(X2) | ~r2_hidden(X2,X0)) & ((v3_ordinal1(X2) & r2_hidden(X2,X0)) | ~r2_hidden(X2,sK1(X0))))),
% 6.69/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f42,f43])).
% 6.69/1.51  
% 6.69/1.51  fof(f70,plain,(
% 6.69/1.51    ( ! [X2,X0] : (r2_hidden(X2,sK1(X0)) | ~v3_ordinal1(X2) | ~r2_hidden(X2,X0)) )),
% 6.69/1.51    inference(cnf_transformation,[],[f44])).
% 6.69/1.51  
% 6.69/1.51  fof(f59,plain,(
% 6.69/1.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 6.69/1.51    inference(cnf_transformation,[],[f37])).
% 6.69/1.51  
% 6.69/1.51  fof(f58,plain,(
% 6.69/1.51    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 6.69/1.51    inference(cnf_transformation,[],[f37])).
% 6.69/1.51  
% 6.69/1.51  fof(f69,plain,(
% 6.69/1.51    ( ! [X2,X0] : (v3_ordinal1(X2) | ~r2_hidden(X2,sK1(X0))) )),
% 6.69/1.51    inference(cnf_transformation,[],[f44])).
% 6.69/1.51  
% 6.69/1.51  fof(f10,axiom,(
% 6.69/1.51    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k1_ordinal1(X0)))),
% 6.69/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.69/1.51  
% 6.69/1.51  fof(f26,plain,(
% 6.69/1.51    ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 6.69/1.51    inference(ennf_transformation,[],[f10])).
% 6.69/1.51  
% 6.69/1.51  fof(f76,plain,(
% 6.69/1.51    ( ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0)) )),
% 6.69/1.51    inference(cnf_transformation,[],[f26])).
% 6.69/1.51  
% 6.69/1.51  fof(f99,plain,(
% 6.69/1.51    ( ! [X0] : (v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) | ~v3_ordinal1(X0)) )),
% 6.69/1.51    inference(definition_unfolding,[],[f76,f65])).
% 6.69/1.51  
% 6.69/1.51  fof(f84,plain,(
% 6.69/1.51    ( ! [X0] : (v4_ordinal1(X0) | v3_ordinal1(sK3(X0)) | ~v3_ordinal1(X0)) )),
% 6.69/1.51    inference(cnf_transformation,[],[f54])).
% 6.69/1.51  
% 6.69/1.51  cnf(c_20,plain,
% 6.69/1.51      ( ~ r1_ordinal1(X0,X1)
% 6.69/1.51      | r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
% 6.69/1.51      | ~ v3_ordinal1(X1)
% 6.69/1.51      | ~ v3_ordinal1(X0) ),
% 6.69/1.51      inference(cnf_transformation,[],[f102]) ).
% 6.69/1.51  
% 6.69/1.51  cnf(c_15,plain,
% 6.69/1.51      ( r2_hidden(X0,X1)
% 6.69/1.51      | ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
% 6.69/1.51      | X1 = X0 ),
% 6.69/1.51      inference(cnf_transformation,[],[f98]) ).
% 6.69/1.51  
% 6.69/1.51  cnf(c_5314,plain,
% 6.69/1.51      ( ~ r1_ordinal1(X0,X1)
% 6.69/1.51      | r2_hidden(X0,X1)
% 6.69/1.51      | ~ v3_ordinal1(X1)
% 6.69/1.51      | ~ v3_ordinal1(X0)
% 6.69/1.51      | X1 = X0 ),
% 6.69/1.51      inference(resolution,[status(thm)],[c_20,c_15]) ).
% 6.69/1.51  
% 6.69/1.51  cnf(c_977,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 6.69/1.51  
% 6.69/1.51  cnf(c_976,plain,( X0 = X0 ),theory(equality) ).
% 6.69/1.51  
% 6.69/1.51  cnf(c_5272,plain,
% 6.69/1.51      ( X0 != X1 | X1 = X0 ),
% 6.69/1.51      inference(resolution,[status(thm)],[c_977,c_976]) ).
% 6.69/1.51  
% 6.69/1.51  cnf(c_12011,plain,
% 6.69/1.51      ( ~ r1_ordinal1(X0,X1)
% 6.69/1.51      | r2_hidden(X0,X1)
% 6.69/1.51      | ~ v3_ordinal1(X1)
% 6.69/1.51      | ~ v3_ordinal1(X0)
% 6.69/1.51      | X0 = X1 ),
% 6.69/1.51      inference(resolution,[status(thm)],[c_5314,c_5272]) ).
% 6.69/1.51  
% 6.69/1.51  cnf(c_29,negated_conjecture,
% 6.69/1.51      ( v4_ordinal1(sK4)
% 6.69/1.51      | ~ v3_ordinal1(X0)
% 6.69/1.51      | k2_xboole_0(X0,k1_tarski(X0)) != sK4 ),
% 6.69/1.51      inference(cnf_transformation,[],[f106]) ).
% 6.69/1.51  
% 6.69/1.51  cnf(c_22075,plain,
% 6.69/1.51      ( ~ r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),sK4)
% 6.69/1.51      | r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),sK4)
% 6.69/1.51      | v4_ordinal1(sK4)
% 6.69/1.51      | ~ v3_ordinal1(X0)
% 6.69/1.51      | ~ v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0)))
% 6.69/1.51      | ~ v3_ordinal1(sK4) ),
% 6.69/1.51      inference(resolution,[status(thm)],[c_12011,c_29]) ).
% 6.69/1.51  
% 6.69/1.51  cnf(c_35,negated_conjecture,
% 6.69/1.51      ( v3_ordinal1(sK4) ),
% 6.69/1.51      inference(cnf_transformation,[],[f88]) ).
% 6.69/1.51  
% 6.69/1.51  cnf(c_34,negated_conjecture,
% 6.69/1.51      ( ~ v4_ordinal1(sK4) | v3_ordinal1(sK5) ),
% 6.69/1.51      inference(cnf_transformation,[],[f89]) ).
% 6.69/1.51  
% 6.69/1.51  cnf(c_32,negated_conjecture,
% 6.69/1.51      ( ~ v4_ordinal1(sK4) | k2_xboole_0(sK5,k1_tarski(sK5)) = sK4 ),
% 6.69/1.51      inference(cnf_transformation,[],[f108]) ).
% 6.69/1.51  
% 6.69/1.51  cnf(c_28,plain,
% 6.69/1.51      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 6.69/1.51      inference(cnf_transformation,[],[f87]) ).
% 6.69/1.51  
% 6.69/1.51  cnf(c_50,plain,
% 6.69/1.51      ( ~ r2_hidden(sK4,sK4) | ~ r1_tarski(sK4,sK4) ),
% 6.69/1.51      inference(instantiation,[status(thm)],[c_28]) ).
% 6.69/1.51  
% 6.69/1.51  cnf(c_21,plain,
% 6.69/1.51      ( r1_ordinal1(X0,X1)
% 6.69/1.51      | ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
% 6.69/1.51      | ~ v3_ordinal1(X1)
% 6.69/1.51      | ~ v3_ordinal1(X0) ),
% 6.69/1.51      inference(cnf_transformation,[],[f103]) ).
% 6.69/1.51  
% 6.69/1.51  cnf(c_71,plain,
% 6.69/1.51      ( r1_ordinal1(sK4,sK4)
% 6.69/1.51      | ~ r2_hidden(sK4,k2_xboole_0(sK4,k1_tarski(sK4)))
% 6.69/1.51      | ~ v3_ordinal1(sK4) ),
% 6.69/1.51      inference(instantiation,[status(thm)],[c_21]) ).
% 6.69/1.51  
% 6.69/1.51  cnf(c_87,plain,
% 6.69/1.51      ( ~ r2_hidden(sK4,k2_xboole_0(sK4,k1_tarski(sK4)))
% 6.69/1.51      | r2_hidden(sK4,sK4)
% 6.69/1.51      | sK4 = sK4 ),
% 6.69/1.51      inference(instantiation,[status(thm)],[c_15]) ).
% 6.69/1.51  
% 6.69/1.51  cnf(c_13,plain,
% 6.69/1.51      ( r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0))) ),
% 6.69/1.51      inference(cnf_transformation,[],[f112]) ).
% 6.69/1.51  
% 6.69/1.51  cnf(c_93,plain,
% 6.69/1.51      ( r2_hidden(sK4,k2_xboole_0(sK4,k1_tarski(sK4))) ),
% 6.69/1.51      inference(instantiation,[status(thm)],[c_13]) ).
% 6.69/1.51  
% 6.69/1.51  cnf(c_8,plain,
% 6.69/1.51      ( ~ r1_ordinal1(X0,X1)
% 6.69/1.51      | r1_tarski(X0,X1)
% 6.69/1.51      | ~ v3_ordinal1(X1)
% 6.69/1.51      | ~ v3_ordinal1(X0) ),
% 6.69/1.51      inference(cnf_transformation,[],[f66]) ).
% 6.69/1.51  
% 6.69/1.51  cnf(c_104,plain,
% 6.69/1.51      ( ~ r1_ordinal1(sK4,sK4)
% 6.69/1.51      | r1_tarski(sK4,sK4)
% 6.69/1.51      | ~ v3_ordinal1(sK4) ),
% 6.69/1.51      inference(instantiation,[status(thm)],[c_8]) ).
% 6.69/1.51  
% 6.69/1.51  cnf(c_16,plain,
% 6.69/1.51      ( ~ r2_hidden(X0,X1) | ~ v3_ordinal1(X1) | v3_ordinal1(X0) ),
% 6.69/1.51      inference(cnf_transformation,[],[f75]) ).
% 6.69/1.51  
% 6.69/1.51  cnf(c_2433,plain,
% 6.69/1.51      ( v3_ordinal1(X0) | ~ v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) ),
% 6.69/1.51      inference(resolution,[status(thm)],[c_16,c_13]) ).
% 6.69/1.51  
% 6.69/1.51  cnf(c_979,plain,
% 6.69/1.51      ( ~ r1_ordinal1(X0,X1) | r1_ordinal1(X2,X1) | X2 != X0 ),
% 6.69/1.51      theory(equality) ).
% 6.69/1.51  
% 6.69/1.51  cnf(c_1954,plain,
% 6.69/1.51      ( ~ r1_ordinal1(X0,X1)
% 6.69/1.51      | r1_ordinal1(k2_xboole_0(X2,k1_tarski(X2)),X1)
% 6.69/1.51      | k2_xboole_0(X2,k1_tarski(X2)) != X0 ),
% 6.69/1.51      inference(instantiation,[status(thm)],[c_979]) ).
% 6.69/1.51  
% 6.69/1.51  cnf(c_2450,plain,
% 6.69/1.51      ( r1_ordinal1(k2_xboole_0(sK5,k1_tarski(sK5)),X0)
% 6.69/1.51      | ~ r1_ordinal1(sK4,X0)
% 6.69/1.51      | k2_xboole_0(sK5,k1_tarski(sK5)) != sK4 ),
% 6.69/1.51      inference(instantiation,[status(thm)],[c_1954]) ).
% 6.69/1.51  
% 6.69/1.51  cnf(c_2452,plain,
% 6.69/1.51      ( r1_ordinal1(k2_xboole_0(sK5,k1_tarski(sK5)),sK4)
% 6.69/1.51      | ~ r1_ordinal1(sK4,sK4)
% 6.69/1.51      | k2_xboole_0(sK5,k1_tarski(sK5)) != sK4 ),
% 6.69/1.51      inference(instantiation,[status(thm)],[c_2450]) ).
% 6.69/1.51  
% 6.69/1.51  cnf(c_2802,plain,
% 6.69/1.51      ( X0 != X1
% 6.69/1.51      | X0 = k2_xboole_0(X2,k1_tarski(X2))
% 6.69/1.51      | k2_xboole_0(X2,k1_tarski(X2)) != X1 ),
% 6.69/1.51      inference(instantiation,[status(thm)],[c_977]) ).
% 6.69/1.51  
% 6.69/1.51  cnf(c_4868,plain,
% 6.69/1.51      ( X0 = k2_xboole_0(sK5,k1_tarski(sK5))
% 6.69/1.51      | X0 != sK4
% 6.69/1.51      | k2_xboole_0(sK5,k1_tarski(sK5)) != sK4 ),
% 6.69/1.51      inference(instantiation,[status(thm)],[c_2802]) ).
% 6.69/1.51  
% 6.69/1.51  cnf(c_4870,plain,
% 6.69/1.51      ( k2_xboole_0(sK5,k1_tarski(sK5)) != sK4
% 6.69/1.51      | sK4 = k2_xboole_0(sK5,k1_tarski(sK5))
% 6.69/1.51      | sK4 != sK4 ),
% 6.69/1.51      inference(instantiation,[status(thm)],[c_4868]) ).
% 6.69/1.51  
% 6.69/1.51  cnf(c_18,plain,
% 6.69/1.51      ( ~ r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),X1)
% 6.69/1.51      | r2_hidden(X0,X1)
% 6.69/1.51      | ~ v3_ordinal1(X1)
% 6.69/1.51      | ~ v3_ordinal1(X0) ),
% 6.69/1.51      inference(cnf_transformation,[],[f100]) ).
% 6.69/1.51  
% 6.69/1.51  cnf(c_4873,plain,
% 6.69/1.51      ( ~ r1_ordinal1(k2_xboole_0(sK5,k1_tarski(sK5)),X0)
% 6.69/1.51      | r2_hidden(sK5,X0)
% 6.69/1.51      | ~ v3_ordinal1(X0)
% 6.69/1.51      | ~ v3_ordinal1(sK5) ),
% 6.69/1.51      inference(instantiation,[status(thm)],[c_18]) ).
% 6.69/1.51  
% 6.69/1.51  cnf(c_4875,plain,
% 6.69/1.51      ( ~ r1_ordinal1(k2_xboole_0(sK5,k1_tarski(sK5)),sK4)
% 6.69/1.51      | r2_hidden(sK5,sK4)
% 6.69/1.51      | ~ v3_ordinal1(sK5)
% 6.69/1.51      | ~ v3_ordinal1(sK4) ),
% 6.69/1.51      inference(instantiation,[status(thm)],[c_4873]) ).
% 6.69/1.51  
% 6.69/1.51  cnf(c_27,plain,
% 6.69/1.51      ( ~ r2_hidden(X0,X1)
% 6.69/1.51      | r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),X1)
% 6.69/1.51      | ~ v4_ordinal1(X1)
% 6.69/1.51      | ~ v3_ordinal1(X1)
% 6.69/1.51      | ~ v3_ordinal1(X0) ),
% 6.69/1.51      inference(cnf_transformation,[],[f105]) ).
% 6.69/1.51  
% 6.69/1.51  cnf(c_202,plain,
% 6.69/1.51      ( ~ v3_ordinal1(X1)
% 6.69/1.51      | ~ v4_ordinal1(X1)
% 6.69/1.51      | r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),X1)
% 6.69/1.51      | ~ r2_hidden(X0,X1) ),
% 6.69/1.51      inference(global_propositional_subsumption,
% 6.69/1.51                [status(thm)],
% 6.69/1.51                [c_27,c_16]) ).
% 6.69/1.51  
% 6.69/1.51  cnf(c_203,plain,
% 6.69/1.51      ( ~ r2_hidden(X0,X1)
% 6.69/1.51      | r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),X1)
% 6.69/1.51      | ~ v4_ordinal1(X1)
% 6.69/1.51      | ~ v3_ordinal1(X1) ),
% 6.69/1.51      inference(renaming,[status(thm)],[c_202]) ).
% 6.69/1.51  
% 6.69/1.51  cnf(c_9025,plain,
% 6.69/1.51      ( r2_hidden(k2_xboole_0(sK5,k1_tarski(sK5)),X0)
% 6.69/1.51      | ~ r2_hidden(sK5,X0)
% 6.69/1.51      | ~ v4_ordinal1(X0)
% 6.69/1.51      | ~ v3_ordinal1(X0) ),
% 6.69/1.51      inference(instantiation,[status(thm)],[c_203]) ).
% 6.69/1.51  
% 6.69/1.51  cnf(c_9042,plain,
% 6.69/1.51      ( r2_hidden(k2_xboole_0(sK5,k1_tarski(sK5)),sK4)
% 6.69/1.51      | ~ r2_hidden(sK5,sK4)
% 6.69/1.51      | ~ v4_ordinal1(sK4)
% 6.69/1.51      | ~ v3_ordinal1(sK4) ),
% 6.69/1.51      inference(instantiation,[status(thm)],[c_9025]) ).
% 6.69/1.51  
% 6.69/1.51  cnf(c_978,plain,
% 6.69/1.51      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 6.69/1.51      theory(equality) ).
% 6.69/1.51  
% 6.69/1.51  cnf(c_18212,plain,
% 6.69/1.51      ( r2_hidden(X0,X1)
% 6.69/1.51      | ~ r2_hidden(k2_xboole_0(sK5,k1_tarski(sK5)),X2)
% 6.69/1.51      | X1 != X2
% 6.69/1.51      | X0 != k2_xboole_0(sK5,k1_tarski(sK5)) ),
% 6.69/1.51      inference(instantiation,[status(thm)],[c_978]) ).
% 6.69/1.51  
% 6.69/1.51  cnf(c_18234,plain,
% 6.69/1.51      ( ~ r2_hidden(k2_xboole_0(sK5,k1_tarski(sK5)),sK4)
% 6.69/1.51      | r2_hidden(sK4,sK4)
% 6.69/1.51      | sK4 != k2_xboole_0(sK5,k1_tarski(sK5))
% 6.69/1.51      | sK4 != sK4 ),
% 6.69/1.51      inference(instantiation,[status(thm)],[c_18212]) ).
% 6.69/1.51  
% 6.69/1.51  cnf(c_22284,plain,
% 6.69/1.51      ( ~ v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0)))
% 6.69/1.51      | r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),sK4)
% 6.69/1.51      | ~ r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),sK4) ),
% 6.69/1.51      inference(global_propositional_subsumption,
% 6.69/1.51                [status(thm)],
% 6.69/1.51                [c_22075,c_35,c_34,c_32,c_50,c_71,c_87,c_93,c_104,c_2433,
% 6.69/1.51                 c_2452,c_4870,c_4875,c_9042,c_18234]) ).
% 6.69/1.51  
% 6.69/1.51  cnf(c_22285,plain,
% 6.69/1.51      ( ~ r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),sK4)
% 6.69/1.51      | r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),sK4)
% 6.69/1.51      | ~ v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) ),
% 6.69/1.51      inference(renaming,[status(thm)],[c_22284]) ).
% 6.69/1.51  
% 6.69/1.51  cnf(c_31,negated_conjecture,
% 6.69/1.51      ( ~ v3_ordinal1(X0)
% 6.69/1.51      | k2_xboole_0(X0,k1_tarski(X0)) != sK4
% 6.69/1.51      | k2_xboole_0(sK5,k1_tarski(sK5)) = sK4 ),
% 6.69/1.51      inference(cnf_transformation,[],[f107]) ).
% 6.69/1.51  
% 6.69/1.51  cnf(c_12006,plain,
% 6.69/1.51      ( ~ r1_ordinal1(sK4,k2_xboole_0(X0,k1_tarski(X0)))
% 6.69/1.51      | r2_hidden(sK4,k2_xboole_0(X0,k1_tarski(X0)))
% 6.69/1.51      | ~ v3_ordinal1(X0)
% 6.69/1.51      | ~ v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0)))
% 6.69/1.51      | ~ v3_ordinal1(sK4)
% 6.69/1.51      | k2_xboole_0(sK5,k1_tarski(sK5)) = sK4 ),
% 6.69/1.51      inference(resolution,[status(thm)],[c_5314,c_31]) ).
% 6.69/1.51  
% 6.69/1.51  cnf(c_12748,plain,
% 6.69/1.51      ( ~ v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0)))
% 6.69/1.51      | ~ r1_ordinal1(sK4,k2_xboole_0(X0,k1_tarski(X0)))
% 6.69/1.51      | r2_hidden(sK4,k2_xboole_0(X0,k1_tarski(X0)))
% 6.69/1.51      | k2_xboole_0(sK5,k1_tarski(sK5)) = sK4 ),
% 6.69/1.51      inference(global_propositional_subsumption,
% 6.69/1.51                [status(thm)],
% 6.69/1.51                [c_12006,c_35,c_2433]) ).
% 6.69/1.51  
% 6.69/1.51  cnf(c_12749,plain,
% 6.69/1.51      ( ~ r1_ordinal1(sK4,k2_xboole_0(X0,k1_tarski(X0)))
% 6.69/1.51      | r2_hidden(sK4,k2_xboole_0(X0,k1_tarski(X0)))
% 6.69/1.51      | ~ v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0)))
% 6.69/1.51      | k2_xboole_0(sK5,k1_tarski(sK5)) = sK4 ),
% 6.69/1.51      inference(renaming,[status(thm)],[c_12748]) ).
% 6.69/1.51  
% 6.69/1.51  cnf(c_6,plain,
% 6.69/1.51      ( r1_ordinal1(X0,X1)
% 6.69/1.51      | r1_ordinal1(X1,X0)
% 6.69/1.51      | ~ v3_ordinal1(X1)
% 6.69/1.51      | ~ v3_ordinal1(X0) ),
% 6.69/1.51      inference(cnf_transformation,[],[f64]) ).
% 6.69/1.51  
% 6.69/1.51  cnf(c_12772,plain,
% 6.69/1.51      ( r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),sK4)
% 6.69/1.51      | r2_hidden(sK4,k2_xboole_0(X0,k1_tarski(X0)))
% 6.69/1.51      | ~ v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0)))
% 6.69/1.51      | ~ v3_ordinal1(sK4)
% 6.69/1.51      | k2_xboole_0(sK5,k1_tarski(sK5)) = sK4 ),
% 6.69/1.51      inference(resolution,[status(thm)],[c_12749,c_6]) ).
% 6.69/1.51  
% 6.69/1.51  cnf(c_14640,plain,
% 6.69/1.51      ( ~ v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0)))
% 6.69/1.51      | r2_hidden(sK4,k2_xboole_0(X0,k1_tarski(X0)))
% 6.69/1.51      | r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),sK4)
% 6.69/1.51      | k2_xboole_0(sK5,k1_tarski(sK5)) = sK4 ),
% 6.69/1.51      inference(global_propositional_subsumption,
% 6.69/1.51                [status(thm)],
% 6.69/1.51                [c_12772,c_35]) ).
% 6.69/1.51  
% 6.69/1.51  cnf(c_14641,plain,
% 6.69/1.51      ( r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),sK4)
% 6.69/1.51      | r2_hidden(sK4,k2_xboole_0(X0,k1_tarski(X0)))
% 6.69/1.51      | ~ v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0)))
% 6.69/1.51      | k2_xboole_0(sK5,k1_tarski(sK5)) = sK4 ),
% 6.69/1.51      inference(renaming,[status(thm)],[c_14640]) ).
% 6.69/1.51  
% 6.69/1.51  cnf(c_14670,plain,
% 6.69/1.51      ( r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),sK4)
% 6.69/1.51      | r2_hidden(sK4,k2_xboole_0(X0,k1_tarski(X0)))
% 6.69/1.51      | ~ v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0)))
% 6.69/1.51      | sK4 = k2_xboole_0(sK5,k1_tarski(sK5)) ),
% 6.69/1.51      inference(resolution,[status(thm)],[c_14641,c_5272]) ).
% 6.69/1.51  
% 6.69/1.51  cnf(c_12004,plain,
% 6.69/1.51      ( ~ r1_ordinal1(sK4,k2_xboole_0(X0,k1_tarski(X0)))
% 6.69/1.51      | r2_hidden(sK4,k2_xboole_0(X0,k1_tarski(X0)))
% 6.69/1.51      | v4_ordinal1(sK4)
% 6.69/1.51      | ~ v3_ordinal1(X0)
% 6.69/1.51      | ~ v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0)))
% 6.69/1.51      | ~ v3_ordinal1(sK4) ),
% 6.69/1.51      inference(resolution,[status(thm)],[c_5314,c_29]) ).
% 6.69/1.51  
% 6.69/1.51  cnf(c_12235,plain,
% 6.69/1.51      ( ~ v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0)))
% 6.69/1.51      | ~ r1_ordinal1(sK4,k2_xboole_0(X0,k1_tarski(X0)))
% 6.69/1.51      | r2_hidden(sK4,k2_xboole_0(X0,k1_tarski(X0)))
% 6.69/1.51      | v4_ordinal1(sK4) ),
% 6.69/1.51      inference(global_propositional_subsumption,
% 6.69/1.51                [status(thm)],
% 6.69/1.51                [c_12004,c_35,c_2433]) ).
% 6.69/1.51  
% 6.69/1.51  cnf(c_12236,plain,
% 6.69/1.51      ( ~ r1_ordinal1(sK4,k2_xboole_0(X0,k1_tarski(X0)))
% 6.69/1.51      | r2_hidden(sK4,k2_xboole_0(X0,k1_tarski(X0)))
% 6.69/1.51      | v4_ordinal1(sK4)
% 6.69/1.51      | ~ v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) ),
% 6.69/1.51      inference(renaming,[status(thm)],[c_12235]) ).
% 6.69/1.51  
% 6.69/1.51  cnf(c_12429,plain,
% 6.69/1.51      ( r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),sK4)
% 6.69/1.51      | r2_hidden(sK4,k2_xboole_0(X0,k1_tarski(X0)))
% 6.69/1.51      | v4_ordinal1(sK4)
% 6.69/1.51      | ~ v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0)))
% 6.69/1.51      | ~ v3_ordinal1(sK4) ),
% 6.69/1.51      inference(resolution,[status(thm)],[c_12236,c_6]) ).
% 6.69/1.51  
% 6.69/1.51  cnf(c_19460,plain,
% 6.69/1.51      ( ~ v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0)))
% 6.69/1.51      | r2_hidden(sK4,k2_xboole_0(X0,k1_tarski(X0)))
% 6.69/1.51      | r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),sK4) ),
% 6.69/1.51      inference(global_propositional_subsumption,
% 6.69/1.51                [status(thm)],
% 6.69/1.51                [c_14670,c_35,c_34,c_32,c_50,c_71,c_87,c_93,c_104,c_2452,
% 6.69/1.51                 c_4870,c_4875,c_9042,c_12429,c_18234]) ).
% 6.69/1.51  
% 6.69/1.51  cnf(c_19461,plain,
% 6.69/1.51      ( r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),sK4)
% 6.69/1.51      | r2_hidden(sK4,k2_xboole_0(X0,k1_tarski(X0)))
% 6.69/1.51      | ~ v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) ),
% 6.69/1.51      inference(renaming,[status(thm)],[c_19460]) ).
% 6.69/1.51  
% 6.69/1.51  cnf(c_22525,plain,
% 6.69/1.51      ( r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),sK4)
% 6.69/1.51      | r2_hidden(sK4,k2_xboole_0(X0,k1_tarski(X0)))
% 6.69/1.51      | ~ v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) ),
% 6.69/1.51      inference(resolution,[status(thm)],[c_22285,c_19461]) ).
% 6.69/1.51  
% 6.69/1.51  cnf(c_24,plain,
% 6.69/1.51      ( ~ r2_hidden(k2_xboole_0(sK3(X0),k1_tarski(sK3(X0))),X0)
% 6.69/1.51      | v4_ordinal1(X0)
% 6.69/1.51      | ~ v3_ordinal1(X0) ),
% 6.69/1.51      inference(cnf_transformation,[],[f104]) ).
% 6.69/1.51  
% 6.69/1.51  cnf(c_22538,plain,
% 6.69/1.51      ( r2_hidden(sK4,k2_xboole_0(sK3(sK4),k1_tarski(sK3(sK4))))
% 6.69/1.51      | v4_ordinal1(sK4)
% 6.69/1.51      | ~ v3_ordinal1(k2_xboole_0(sK3(sK4),k1_tarski(sK3(sK4))))
% 6.69/1.51      | ~ v3_ordinal1(sK4) ),
% 6.69/1.51      inference(resolution,[status(thm)],[c_22525,c_24]) ).
% 6.69/1.51  
% 6.69/1.51  cnf(c_25,plain,
% 6.69/1.51      ( r2_hidden(sK3(X0),X0) | v4_ordinal1(X0) | ~ v3_ordinal1(X0) ),
% 6.69/1.51      inference(cnf_transformation,[],[f85]) ).
% 6.69/1.51  
% 6.69/1.51  cnf(c_1571,plain,
% 6.69/1.51      ( r2_hidden(sK3(X0),X0) = iProver_top
% 6.69/1.51      | v4_ordinal1(X0) = iProver_top
% 6.69/1.51      | v3_ordinal1(X0) != iProver_top ),
% 6.69/1.51      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 6.69/1.51  
% 6.69/1.51  cnf(c_1562,plain,
% 6.69/1.51      ( r2_hidden(X0,X1) != iProver_top
% 6.69/1.51      | r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),X1) = iProver_top
% 6.69/1.51      | v4_ordinal1(X1) != iProver_top
% 6.69/1.51      | v3_ordinal1(X1) != iProver_top ),
% 6.69/1.51      inference(predicate_to_equality,[status(thm)],[c_203]) ).
% 6.69/1.51  
% 6.69/1.51  cnf(c_1579,plain,
% 6.69/1.51      ( r2_hidden(X0,X1) != iProver_top
% 6.69/1.51      | v3_ordinal1(X1) != iProver_top
% 6.69/1.51      | v3_ordinal1(X0) = iProver_top ),
% 6.69/1.51      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 6.69/1.51  
% 6.69/1.51  cnf(c_3864,plain,
% 6.69/1.51      ( r2_hidden(X0,X1) != iProver_top
% 6.69/1.51      | v4_ordinal1(X1) != iProver_top
% 6.69/1.51      | v3_ordinal1(X1) != iProver_top
% 6.69/1.51      | v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) = iProver_top ),
% 6.69/1.51      inference(superposition,[status(thm)],[c_1562,c_1579]) ).
% 6.69/1.51  
% 6.69/1.51  cnf(c_0,plain,
% 6.69/1.51      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 6.69/1.51      inference(cnf_transformation,[],[f60]) ).
% 6.69/1.51  
% 6.69/1.51  cnf(c_9,plain,
% 6.69/1.51      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,sK1(X1)) | ~ v3_ordinal1(X0) ),
% 6.69/1.51      inference(cnf_transformation,[],[f70]) ).
% 6.69/1.51  
% 6.69/1.51  cnf(c_3683,plain,
% 6.69/1.51      ( ~ r2_hidden(sK0(X0,sK1(X1)),X1)
% 6.69/1.51      | r1_tarski(X0,sK1(X1))
% 6.69/1.51      | ~ v3_ordinal1(sK0(X0,sK1(X1))) ),
% 6.69/1.51      inference(resolution,[status(thm)],[c_0,c_9]) ).
% 6.69/1.51  
% 6.69/1.51  cnf(c_1,plain,
% 6.69/1.51      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 6.69/1.51      inference(cnf_transformation,[],[f59]) ).
% 6.69/1.51  
% 6.69/1.51  cnf(c_9596,plain,
% 6.69/1.51      ( r1_tarski(X0,sK1(X0)) | ~ v3_ordinal1(sK0(X0,sK1(X0))) ),
% 6.69/1.51      inference(resolution,[status(thm)],[c_3683,c_1]) ).
% 6.69/1.51  
% 6.69/1.51  cnf(c_2431,plain,
% 6.69/1.51      ( r1_tarski(X0,X1) | ~ v3_ordinal1(X0) | v3_ordinal1(sK0(X0,X1)) ),
% 6.69/1.51      inference(resolution,[status(thm)],[c_16,c_1]) ).
% 6.69/1.51  
% 6.69/1.51  cnf(c_9768,plain,
% 6.69/1.51      ( r1_tarski(X0,sK1(X0)) | ~ v3_ordinal1(X0) ),
% 6.69/1.51      inference(resolution,[status(thm)],[c_9596,c_2431]) ).
% 6.69/1.51  
% 6.69/1.51  cnf(c_2,plain,
% 6.69/1.51      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 6.69/1.51      inference(cnf_transformation,[],[f58]) ).
% 6.69/1.51  
% 6.69/1.51  cnf(c_9782,plain,
% 6.69/1.51      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,sK1(X1)) | ~ v3_ordinal1(X1) ),
% 6.69/1.51      inference(resolution,[status(thm)],[c_9768,c_2]) ).
% 6.69/1.51  
% 6.69/1.51  cnf(c_9783,plain,
% 6.69/1.51      ( r2_hidden(X0,X1) != iProver_top
% 6.69/1.51      | r2_hidden(X0,sK1(X1)) = iProver_top
% 6.69/1.51      | v3_ordinal1(X1) != iProver_top ),
% 6.69/1.51      inference(predicate_to_equality,[status(thm)],[c_9782]) ).
% 6.69/1.51  
% 6.69/1.51  cnf(c_10,plain,
% 6.69/1.51      ( ~ r2_hidden(X0,sK1(X1)) | v3_ordinal1(X0) ),
% 6.69/1.51      inference(cnf_transformation,[],[f69]) ).
% 6.69/1.51  
% 6.69/1.51  cnf(c_1584,plain,
% 6.69/1.51      ( r2_hidden(X0,sK1(X1)) != iProver_top
% 6.69/1.51      | v3_ordinal1(X0) = iProver_top ),
% 6.69/1.51      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 6.69/1.51  
% 6.69/1.51  cnf(c_3318,plain,
% 6.69/1.51      ( r2_hidden(X0,sK1(X1)) != iProver_top
% 6.69/1.51      | v4_ordinal1(sK1(X1)) != iProver_top
% 6.69/1.51      | v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) = iProver_top
% 6.69/1.51      | v3_ordinal1(sK1(X1)) != iProver_top ),
% 6.69/1.51      inference(superposition,[status(thm)],[c_1562,c_1584]) ).
% 6.69/1.51  
% 6.69/1.51  cnf(c_17,plain,
% 6.69/1.51      ( ~ v3_ordinal1(X0) | v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) ),
% 6.69/1.51      inference(cnf_transformation,[],[f99]) ).
% 6.69/1.51  
% 6.69/1.51  cnf(c_82,plain,
% 6.69/1.51      ( v3_ordinal1(X0) != iProver_top
% 6.69/1.51      | v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) = iProver_top ),
% 6.69/1.51      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 6.69/1.51  
% 6.69/1.51  cnf(c_99,plain,
% 6.69/1.51      ( r2_hidden(X0,sK1(X1)) != iProver_top
% 6.69/1.51      | v3_ordinal1(X0) = iProver_top ),
% 6.69/1.51      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 6.69/1.51  
% 6.69/1.51  cnf(c_13155,plain,
% 6.69/1.51      ( v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) = iProver_top
% 6.69/1.51      | r2_hidden(X0,sK1(X1)) != iProver_top ),
% 6.69/1.51      inference(global_propositional_subsumption,
% 6.69/1.51                [status(thm)],
% 6.69/1.51                [c_3318,c_82,c_99]) ).
% 6.69/1.51  
% 6.69/1.51  cnf(c_13156,plain,
% 6.69/1.51      ( r2_hidden(X0,sK1(X1)) != iProver_top
% 6.69/1.51      | v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) = iProver_top ),
% 6.69/1.51      inference(renaming,[status(thm)],[c_13155]) ).
% 6.69/1.51  
% 6.69/1.51  cnf(c_15323,plain,
% 6.69/1.51      ( r2_hidden(X0,X1) != iProver_top
% 6.69/1.51      | v3_ordinal1(X1) != iProver_top
% 6.69/1.51      | v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) = iProver_top ),
% 6.69/1.51      inference(global_propositional_subsumption,
% 6.69/1.51                [status(thm)],
% 6.69/1.51                [c_3864,c_9783,c_13156]) ).
% 6.69/1.51  
% 6.69/1.51  cnf(c_15335,plain,
% 6.69/1.51      ( v4_ordinal1(X0) = iProver_top
% 6.69/1.51      | v3_ordinal1(X0) != iProver_top
% 6.69/1.51      | v3_ordinal1(k2_xboole_0(sK3(X0),k1_tarski(sK3(X0)))) = iProver_top ),
% 6.69/1.51      inference(superposition,[status(thm)],[c_1571,c_15323]) ).
% 6.69/1.51  
% 6.69/1.51  cnf(c_15404,plain,
% 6.69/1.51      ( v4_ordinal1(X0)
% 6.69/1.51      | ~ v3_ordinal1(X0)
% 6.69/1.51      | v3_ordinal1(k2_xboole_0(sK3(X0),k1_tarski(sK3(X0)))) ),
% 6.69/1.51      inference(predicate_to_equality_rev,[status(thm)],[c_15335]) ).
% 6.69/1.51  
% 6.69/1.51  cnf(c_15406,plain,
% 6.69/1.51      ( v4_ordinal1(sK4)
% 6.69/1.51      | v3_ordinal1(k2_xboole_0(sK3(sK4),k1_tarski(sK3(sK4))))
% 6.69/1.51      | ~ v3_ordinal1(sK4) ),
% 6.69/1.51      inference(instantiation,[status(thm)],[c_15404]) ).
% 6.69/1.51  
% 6.69/1.51  cnf(c_9795,plain,
% 6.69/1.51      ( r1_ordinal1(X0,sK3(X0))
% 6.69/1.51      | ~ r2_hidden(X0,k2_xboole_0(sK3(X0),k1_tarski(sK3(X0))))
% 6.69/1.51      | ~ v3_ordinal1(X0)
% 6.69/1.51      | ~ v3_ordinal1(sK3(X0)) ),
% 6.69/1.51      inference(instantiation,[status(thm)],[c_21]) ).
% 6.69/1.51  
% 6.69/1.51  cnf(c_9802,plain,
% 6.69/1.51      ( r1_ordinal1(sK4,sK3(sK4))
% 6.69/1.51      | ~ r2_hidden(sK4,k2_xboole_0(sK3(sK4),k1_tarski(sK3(sK4))))
% 6.69/1.51      | ~ v3_ordinal1(sK3(sK4))
% 6.69/1.51      | ~ v3_ordinal1(sK4) ),
% 6.69/1.51      inference(instantiation,[status(thm)],[c_9795]) ).
% 6.69/1.51  
% 6.69/1.51  cnf(c_5232,plain,
% 6.69/1.51      ( ~ r1_ordinal1(X0,sK3(X0))
% 6.69/1.51      | r1_tarski(X0,sK3(X0))
% 6.69/1.51      | ~ v3_ordinal1(X0)
% 6.69/1.51      | ~ v3_ordinal1(sK3(X0)) ),
% 6.69/1.51      inference(instantiation,[status(thm)],[c_8]) ).
% 6.69/1.51  
% 6.69/1.51  cnf(c_5234,plain,
% 6.69/1.51      ( ~ r1_ordinal1(sK4,sK3(sK4))
% 6.69/1.51      | r1_tarski(sK4,sK3(sK4))
% 6.69/1.51      | ~ v3_ordinal1(sK3(sK4))
% 6.69/1.51      | ~ v3_ordinal1(sK4) ),
% 6.69/1.51      inference(instantiation,[status(thm)],[c_5232]) ).
% 6.69/1.51  
% 6.69/1.51  cnf(c_3404,plain,
% 6.69/1.51      ( ~ r1_tarski(X0,sK3(X0)) | v4_ordinal1(X0) | ~ v3_ordinal1(X0) ),
% 6.69/1.51      inference(resolution,[status(thm)],[c_28,c_25]) ).
% 6.69/1.51  
% 6.69/1.51  cnf(c_3406,plain,
% 6.69/1.51      ( ~ r1_tarski(sK4,sK3(sK4))
% 6.69/1.51      | v4_ordinal1(sK4)
% 6.69/1.51      | ~ v3_ordinal1(sK4) ),
% 6.69/1.51      inference(instantiation,[status(thm)],[c_3404]) ).
% 6.69/1.51  
% 6.69/1.51  cnf(c_26,plain,
% 6.69/1.51      ( v4_ordinal1(X0) | ~ v3_ordinal1(X0) | v3_ordinal1(sK3(X0)) ),
% 6.69/1.51      inference(cnf_transformation,[],[f84]) ).
% 6.69/1.51  
% 6.69/1.51  cnf(c_56,plain,
% 6.69/1.51      ( v4_ordinal1(sK4) | v3_ordinal1(sK3(sK4)) | ~ v3_ordinal1(sK4) ),
% 6.69/1.51      inference(instantiation,[status(thm)],[c_26]) ).
% 6.69/1.51  
% 6.69/1.51  cnf(contradiction,plain,
% 6.69/1.51      ( $false ),
% 6.69/1.51      inference(minisat,
% 6.69/1.51                [status(thm)],
% 6.69/1.51                [c_22538,c_18234,c_15406,c_9802,c_9042,c_5234,c_4875,
% 6.69/1.51                 c_4870,c_3406,c_2452,c_104,c_93,c_87,c_71,c_56,c_50,
% 6.69/1.51                 c_32,c_34,c_35]) ).
% 6.69/1.51  
% 6.69/1.51  
% 6.69/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 6.69/1.51  
% 6.69/1.51  ------                               Statistics
% 6.69/1.51  
% 6.69/1.51  ------ Selected
% 6.69/1.51  
% 6.69/1.51  total_time:                             0.589
% 6.69/1.51  
%------------------------------------------------------------------------------
