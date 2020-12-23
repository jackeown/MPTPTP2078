%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:54:03 EST 2020

% Result     : Theorem 3.13s
% Output     : CNFRefutation 3.13s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 441 expanded)
%              Number of clauses        :   68 ( 130 expanded)
%              Number of leaves         :   17 (  99 expanded)
%              Depth                    :   14
%              Number of atoms          :  492 (1716 expanded)
%              Number of equality atoms :   92 ( 351 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r2_hidden(X0,k1_ordinal1(X1))
              | ~ r1_ordinal1(X0,X1) )
            & ( r1_ordinal1(X0,X1)
              | ~ r2_hidden(X0,k1_ordinal1(X1)) ) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f3,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f53,f42])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
    <=> ( X0 = X1
        | r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(flattening,[],[f27])).

fof(f45,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f67,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) ) ),
    inference(definition_unfolding,[],[f45,f42])).

fof(f11,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
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
    inference(negated_conjecture,[],[f11])).

fof(f13,plain,(
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
    inference(rectify,[],[f12])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k1_ordinal1(X1) = X0
          & v3_ordinal1(X1) )
     => ( k1_ordinal1(sK2) = X0
        & v3_ordinal1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
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

fof(f37,plain,
    ( ( ( v4_ordinal1(sK1)
        & k1_ordinal1(sK2) = sK1
        & v3_ordinal1(sK2) )
      | ( ! [X2] :
            ( k1_ordinal1(X2) != sK1
            | ~ v3_ordinal1(X2) )
        & ~ v4_ordinal1(sK1) ) )
    & v3_ordinal1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f23,f36,f35])).

fof(f64,plain,(
    ! [X2] :
      ( v4_ordinal1(sK1)
      | k1_ordinal1(X2) != sK1
      | ~ v3_ordinal1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f76,plain,(
    ! [X2] :
      ( v4_ordinal1(sK1)
      | k2_xboole_0(X2,k1_tarski(X2)) != sK1
      | ~ v3_ordinal1(X2) ) ),
    inference(definition_unfolding,[],[f64,f42])).

fof(f58,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f59,plain,
    ( v3_ordinal1(sK2)
    | ~ v4_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f61,plain,
    ( k1_ordinal1(sK2) = sK1
    | ~ v4_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f78,plain,
    ( k2_xboole_0(sK2,k1_tarski(sK2)) = sK1
    | ~ v4_ordinal1(sK1) ),
    inference(definition_unfolding,[],[f61,f42])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ r2_hidden(X0,k1_ordinal1(X1))
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f52,f42])).

fof(f8,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
          <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X0,X1)
          <=> r1_ordinal1(k1_ordinal1(X0),X1) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r2_hidden(X0,X1)
              | ~ r1_ordinal1(k1_ordinal1(X0),X1) )
            & ( r1_ordinal1(k1_ordinal1(X0),X1)
              | ~ r2_hidden(X0,X1) ) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(k1_ordinal1(X0),X1)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),X1)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f50,f42])).

fof(f7,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k1_ordinal1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f49,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f69,plain,(
    ! [X0] :
      ( v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0)))
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f49,f42])).

fof(f6,axiom,(
    ! [X0] : k1_ordinal1(X0) != X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : k1_ordinal1(X0) != X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f68,plain,(
    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) != X0 ),
    inference(definition_unfolding,[],[f48,f42])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | X0 != X1 ) ),
    inference(definition_unfolding,[],[f47,f42])).

fof(f82,plain,(
    ! [X1] : r2_hidden(X1,k2_xboole_0(X1,k1_tarski(X1))) ),
    inference(equality_resolution,[],[f65])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f24])).

fof(f40,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f46,f42])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_ordinal1(k1_ordinal1(X0),X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f51,f42])).

fof(f10,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v4_ordinal1(X0)
      <=> ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X1,X0)
             => r2_hidden(k1_ordinal1(X1),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ( v4_ordinal1(X0)
      <=> ! [X1] :
            ( r2_hidden(k1_ordinal1(X1),X0)
            | ~ r2_hidden(X1,X0)
            | ~ v3_ordinal1(X1) ) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f22,plain,(
    ! [X0] :
      ( ( v4_ordinal1(X0)
      <=> ! [X1] :
            ( r2_hidden(k1_ordinal1(X1),X0)
            | ~ r2_hidden(X1,X0)
            | ~ v3_ordinal1(X1) ) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f32,plain,(
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
    inference(rectify,[],[f31])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k1_ordinal1(X1),X0)
          & r2_hidden(X1,X0)
          & v3_ordinal1(X1) )
     => ( ~ r2_hidden(k1_ordinal1(sK0(X0)),X0)
        & r2_hidden(sK0(X0),X0)
        & v3_ordinal1(sK0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f32,f33])).

fof(f54,plain,(
    ! [X2,X0] :
      ( r2_hidden(k1_ordinal1(X2),X0)
      | ~ r2_hidden(X2,X0)
      | ~ v3_ordinal1(X2)
      | ~ v4_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f75,plain,(
    ! [X2,X0] :
      ( r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),X0)
      | ~ r2_hidden(X2,X0)
      | ~ v3_ordinal1(X2)
      | ~ v4_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f54,f42])).

fof(f57,plain,(
    ! [X0] :
      ( v4_ordinal1(X0)
      | ~ r2_hidden(k1_ordinal1(sK0(X0)),X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f74,plain,(
    ! [X0] :
      ( v4_ordinal1(X0)
      | ~ r2_hidden(k2_xboole_0(sK0(X0),k1_tarski(sK0(X0))),X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f57,f42])).

fof(f56,plain,(
    ! [X0] :
      ( v4_ordinal1(X0)
      | r2_hidden(sK0(X0),X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f55,plain,(
    ! [X0] :
      ( v4_ordinal1(X0)
      | v3_ordinal1(sK0(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_13,plain,
    ( r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
    | ~ r1_ordinal1(X0,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_8,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
    | X1 = X0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_2825,plain,
    ( r2_hidden(X0,X1)
    | ~ r1_ordinal1(X0,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0)
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_13,c_8])).

cnf(c_826,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_825,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2603,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_826,c_825])).

cnf(c_5464,plain,
    ( r2_hidden(X0,X1)
    | ~ r1_ordinal1(X0,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0)
    | X0 = X1 ),
    inference(resolution,[status(thm)],[c_2825,c_2603])).

cnf(c_19,negated_conjecture,
    ( v4_ordinal1(sK1)
    | ~ v3_ordinal1(X0)
    | k2_xboole_0(X0,k1_tarski(X0)) != sK1 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_13165,plain,
    ( r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),sK1)
    | ~ r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),sK1)
    | v4_ordinal1(sK1)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0)))
    | ~ v3_ordinal1(sK1) ),
    inference(resolution,[status(thm)],[c_5464,c_19])).

cnf(c_25,negated_conjecture,
    ( v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_24,negated_conjecture,
    ( ~ v4_ordinal1(sK1)
    | v3_ordinal1(sK2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_22,negated_conjecture,
    ( ~ v4_ordinal1(sK1)
    | k2_xboole_0(sK2,k1_tarski(sK2)) = sK1 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
    | r1_ordinal1(X0,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_52,plain,
    ( ~ r2_hidden(sK1,k2_xboole_0(sK1,k1_tarski(sK1)))
    | r1_ordinal1(sK1,sK1)
    | ~ v3_ordinal1(sK1) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_58,plain,
    ( ~ r2_hidden(sK1,sK1)
    | r1_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1)),sK1)
    | ~ v3_ordinal1(sK1) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_10,plain,
    ( ~ v3_ordinal1(X0)
    | v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_64,plain,
    ( v3_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1)))
    | ~ v3_ordinal1(sK1) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_9,plain,
    ( k2_xboole_0(X0,k1_tarski(X0)) != X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_66,plain,
    ( k2_xboole_0(sK1,k1_tarski(sK1)) != sK1 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_6,plain,
    ( r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_74,plain,
    ( r2_hidden(sK1,k2_xboole_0(sK1,k1_tarski(sK1))) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_5,plain,
    ( ~ r1_ordinal1(X0,X1)
    | r1_tarski(X0,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_77,plain,
    ( ~ r1_ordinal1(sK1,sK1)
    | r1_tarski(sK1,sK1)
    | ~ v3_ordinal1(sK1) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_90,plain,
    ( ~ r1_tarski(sK1,sK1)
    | sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1506,plain,
    ( ~ r1_tarski(X0,k2_xboole_0(X0,k1_tarski(X0)))
    | ~ r1_tarski(k2_xboole_0(X0,k1_tarski(X0)),X0)
    | k2_xboole_0(X0,k1_tarski(X0)) = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1508,plain,
    ( ~ r1_tarski(k2_xboole_0(sK1,k1_tarski(sK1)),sK1)
    | ~ r1_tarski(sK1,k2_xboole_0(sK1,k1_tarski(sK1)))
    | k2_xboole_0(sK1,k1_tarski(sK1)) = sK1 ),
    inference(instantiation,[status(thm)],[c_1506])).

cnf(c_1649,plain,
    ( ~ r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),X0)
    | r1_tarski(k2_xboole_0(X0,k1_tarski(X0)),X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1651,plain,
    ( ~ r1_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1)),sK1)
    | r1_tarski(k2_xboole_0(sK1,k1_tarski(sK1)),sK1)
    | ~ v3_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1)))
    | ~ v3_ordinal1(sK1) ),
    inference(instantiation,[status(thm)],[c_1649])).

cnf(c_1825,plain,
    ( ~ r1_ordinal1(X0,k2_xboole_0(X1,k1_tarski(X1)))
    | r1_tarski(X0,k2_xboole_0(X1,k1_tarski(X1)))
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(k2_xboole_0(X1,k1_tarski(X1))) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1827,plain,
    ( ~ r1_ordinal1(sK1,k2_xboole_0(sK1,k1_tarski(sK1)))
    | r1_tarski(sK1,k2_xboole_0(sK1,k1_tarski(sK1)))
    | ~ v3_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1)))
    | ~ v3_ordinal1(sK1) ),
    inference(instantiation,[status(thm)],[c_1825])).

cnf(c_1267,plain,
    ( r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1266,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1260,plain,
    ( r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) != iProver_top
    | r1_ordinal1(X0,X1) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2299,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_ordinal1(X0,X1) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1266,c_1260])).

cnf(c_2334,plain,
    ( r1_ordinal1(X0,k2_xboole_0(X0,k1_tarski(X0))) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1267,c_2299])).

cnf(c_2363,plain,
    ( r1_ordinal1(X0,k2_xboole_0(X0,k1_tarski(X0)))
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2334])).

cnf(c_2365,plain,
    ( r1_ordinal1(sK1,k2_xboole_0(sK1,k1_tarski(sK1)))
    | ~ v3_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1)))
    | ~ v3_ordinal1(sK1) ),
    inference(instantiation,[status(thm)],[c_2363])).

cnf(c_827,plain,
    ( ~ r1_ordinal1(X0,X1)
    | r1_ordinal1(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_1546,plain,
    ( ~ r1_ordinal1(X0,X1)
    | r1_ordinal1(k2_xboole_0(X2,k1_tarski(X2)),X1)
    | k2_xboole_0(X2,k1_tarski(X2)) != X0 ),
    inference(instantiation,[status(thm)],[c_827])).

cnf(c_2616,plain,
    ( r1_ordinal1(k2_xboole_0(sK2,k1_tarski(sK2)),X0)
    | ~ r1_ordinal1(sK1,X0)
    | k2_xboole_0(sK2,k1_tarski(sK2)) != sK1 ),
    inference(instantiation,[status(thm)],[c_1546])).

cnf(c_2618,plain,
    ( r1_ordinal1(k2_xboole_0(sK2,k1_tarski(sK2)),sK1)
    | ~ r1_ordinal1(sK1,sK1)
    | k2_xboole_0(sK2,k1_tarski(sK2)) != sK1 ),
    inference(instantiation,[status(thm)],[c_2616])).

cnf(c_1871,plain,
    ( X0 != X1
    | X0 = k2_xboole_0(X2,X3)
    | k2_xboole_0(X2,X3) != X1 ),
    inference(instantiation,[status(thm)],[c_826])).

cnf(c_2699,plain,
    ( X0 = k2_xboole_0(sK2,k1_tarski(sK2))
    | X0 != sK1
    | k2_xboole_0(sK2,k1_tarski(sK2)) != sK1 ),
    inference(instantiation,[status(thm)],[c_1871])).

cnf(c_2700,plain,
    ( k2_xboole_0(sK2,k1_tarski(sK2)) != sK1
    | sK1 = k2_xboole_0(sK2,k1_tarski(sK2))
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_2699])).

cnf(c_11,plain,
    ( r2_hidden(X0,X1)
    | ~ r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_3771,plain,
    ( r2_hidden(sK2,X0)
    | ~ r1_ordinal1(k2_xboole_0(sK2,k1_tarski(sK2)),X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(sK2) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_3773,plain,
    ( r2_hidden(sK2,sK1)
    | ~ r1_ordinal1(k2_xboole_0(sK2,k1_tarski(sK2)),sK1)
    | ~ v3_ordinal1(sK2)
    | ~ v3_ordinal1(sK1) ),
    inference(instantiation,[status(thm)],[c_3771])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),X1)
    | ~ v4_ordinal1(X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_4296,plain,
    ( r2_hidden(k2_xboole_0(sK2,k1_tarski(sK2)),X0)
    | ~ r2_hidden(sK2,X0)
    | ~ v4_ordinal1(X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(sK2) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_4298,plain,
    ( r2_hidden(k2_xboole_0(sK2,k1_tarski(sK2)),sK1)
    | ~ r2_hidden(sK2,sK1)
    | ~ v4_ordinal1(sK1)
    | ~ v3_ordinal1(sK2)
    | ~ v3_ordinal1(sK1) ),
    inference(instantiation,[status(thm)],[c_4296])).

cnf(c_831,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2608,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),X3)
    | X1 != X3
    | X0 != k2_xboole_0(X2,k1_tarski(X2)) ),
    inference(instantiation,[status(thm)],[c_831])).

cnf(c_10906,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k2_xboole_0(sK2,k1_tarski(sK2)),X2)
    | X1 != X2
    | X0 != k2_xboole_0(sK2,k1_tarski(sK2)) ),
    inference(instantiation,[status(thm)],[c_2608])).

cnf(c_10908,plain,
    ( ~ r2_hidden(k2_xboole_0(sK2,k1_tarski(sK2)),sK1)
    | r2_hidden(sK1,sK1)
    | sK1 != k2_xboole_0(sK2,k1_tarski(sK2))
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_10906])).

cnf(c_13640,plain,
    ( ~ r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),sK1)
    | r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),sK1)
    | ~ v3_ordinal1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13165,c_25,c_24,c_22,c_52,c_58,c_10,c_64,c_66,c_74,c_77,c_90,c_1508,c_1651,c_1827,c_2365,c_2618,c_2700,c_3773,c_4298,c_10908])).

cnf(c_13641,plain,
    ( r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),sK1)
    | ~ r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),sK1)
    | ~ v3_ordinal1(X0) ),
    inference(renaming,[status(thm)],[c_13640])).

cnf(c_15,plain,
    ( ~ r2_hidden(k2_xboole_0(sK0(X0),k1_tarski(sK0(X0))),X0)
    | v4_ordinal1(X0)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_13998,plain,
    ( ~ r1_ordinal1(k2_xboole_0(sK0(sK1),k1_tarski(sK0(sK1))),sK1)
    | v4_ordinal1(sK1)
    | ~ v3_ordinal1(sK0(sK1))
    | ~ v3_ordinal1(sK1) ),
    inference(resolution,[status(thm)],[c_13641,c_15])).

cnf(c_8838,plain,
    ( ~ r2_hidden(sK0(X0),X0)
    | r1_ordinal1(k2_xboole_0(sK0(X0),k1_tarski(sK0(X0))),X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(sK0(X0)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_8845,plain,
    ( ~ r2_hidden(sK0(sK1),sK1)
    | r1_ordinal1(k2_xboole_0(sK0(sK1),k1_tarski(sK0(sK1))),sK1)
    | ~ v3_ordinal1(sK0(sK1))
    | ~ v3_ordinal1(sK1) ),
    inference(instantiation,[status(thm)],[c_8838])).

cnf(c_16,plain,
    ( r2_hidden(sK0(X0),X0)
    | v4_ordinal1(X0)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_46,plain,
    ( r2_hidden(sK0(sK1),sK1)
    | v4_ordinal1(sK1)
    | ~ v3_ordinal1(sK1) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_17,plain,
    ( v4_ordinal1(X0)
    | ~ v3_ordinal1(X0)
    | v3_ordinal1(sK0(X0)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_43,plain,
    ( v4_ordinal1(sK1)
    | v3_ordinal1(sK0(sK1))
    | ~ v3_ordinal1(sK1) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13998,c_10908,c_8845,c_4298,c_3773,c_2700,c_2618,c_2365,c_1827,c_1651,c_1508,c_90,c_77,c_74,c_66,c_64,c_58,c_52,c_46,c_43,c_22,c_24,c_25])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:58:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.13/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.13/0.98  
% 3.13/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.13/0.98  
% 3.13/0.98  ------  iProver source info
% 3.13/0.98  
% 3.13/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.13/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.13/0.98  git: non_committed_changes: false
% 3.13/0.98  git: last_make_outside_of_git: false
% 3.13/0.98  
% 3.13/0.98  ------ 
% 3.13/0.98  ------ Parsing...
% 3.13/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.13/0.98  
% 3.13/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.13/0.98  
% 3.13/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.13/0.98  
% 3.13/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.13/0.98  ------ Proving...
% 3.13/0.98  ------ Problem Properties 
% 3.13/0.98  
% 3.13/0.98  
% 3.13/0.98  clauses                                 24
% 3.13/0.98  conjectures                             6
% 3.13/0.98  EPR                                     7
% 3.13/0.98  Horn                                    20
% 3.13/0.98  unary                                   4
% 3.13/0.98  binary                                  4
% 3.13/0.98  lits                                    69
% 3.13/0.98  lits eq                                 8
% 3.13/0.98  fd_pure                                 0
% 3.13/0.98  fd_pseudo                               0
% 3.13/0.98  fd_cond                                 0
% 3.13/0.98  fd_pseudo_cond                          2
% 3.13/0.98  AC symbols                              0
% 3.13/0.98  
% 3.13/0.98  ------ Input Options Time Limit: Unbounded
% 3.13/0.98  
% 3.13/0.98  
% 3.13/0.98  ------ 
% 3.13/0.98  Current options:
% 3.13/0.98  ------ 
% 3.13/0.98  
% 3.13/0.98  
% 3.13/0.98  
% 3.13/0.98  
% 3.13/0.98  ------ Proving...
% 3.13/0.98  
% 3.13/0.98  
% 3.13/0.98  % SZS status Theorem for theBenchmark.p
% 3.13/0.98  
% 3.13/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.13/0.98  
% 3.13/0.98  fof(f9,axiom,(
% 3.13/0.98    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 3.13/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.13/0.98  
% 3.13/0.98  fof(f20,plain,(
% 3.13/0.98    ! [X0] : (! [X1] : ((r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 3.13/0.98    inference(ennf_transformation,[],[f9])).
% 3.13/0.98  
% 3.13/0.98  fof(f30,plain,(
% 3.13/0.98    ! [X0] : (! [X1] : (((r2_hidden(X0,k1_ordinal1(X1)) | ~r1_ordinal1(X0,X1)) & (r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1)))) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 3.13/0.98    inference(nnf_transformation,[],[f20])).
% 3.13/0.98  
% 3.13/0.98  fof(f53,plain,(
% 3.13/0.98    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.13/0.98    inference(cnf_transformation,[],[f30])).
% 3.13/0.98  
% 3.13/0.98  fof(f3,axiom,(
% 3.13/0.98    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 3.13/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.13/0.98  
% 3.13/0.98  fof(f42,plain,(
% 3.13/0.98    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 3.13/0.98    inference(cnf_transformation,[],[f3])).
% 3.13/0.98  
% 3.13/0.98  fof(f72,plain,(
% 3.13/0.98    ( ! [X0,X1] : (r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.13/0.98    inference(definition_unfolding,[],[f53,f42])).
% 3.13/0.98  
% 3.13/0.98  fof(f5,axiom,(
% 3.13/0.98    ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <=> (X0 = X1 | r2_hidden(X0,X1)))),
% 3.13/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.13/0.98  
% 3.13/0.98  fof(f27,plain,(
% 3.13/0.98    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & ((X0 = X1 | r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 3.13/0.98    inference(nnf_transformation,[],[f5])).
% 3.13/0.98  
% 3.13/0.98  fof(f28,plain,(
% 3.13/0.98    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 3.13/0.98    inference(flattening,[],[f27])).
% 3.13/0.98  
% 3.13/0.98  fof(f45,plain,(
% 3.13/0.98    ( ! [X0,X1] : (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) )),
% 3.13/0.98    inference(cnf_transformation,[],[f28])).
% 3.13/0.98  
% 3.13/0.98  fof(f67,plain,(
% 3.13/0.98    ( ! [X0,X1] : (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))) )),
% 3.13/0.98    inference(definition_unfolding,[],[f45,f42])).
% 3.13/0.98  
% 3.13/0.98  fof(f11,conjecture,(
% 3.13/0.98    ! [X0] : (v3_ordinal1(X0) => (~(v4_ordinal1(X0) & ? [X1] : (k1_ordinal1(X1) = X0 & v3_ordinal1(X1))) & ~(! [X1] : (v3_ordinal1(X1) => k1_ordinal1(X1) != X0) & ~v4_ordinal1(X0))))),
% 3.13/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.13/0.98  
% 3.13/0.98  fof(f12,negated_conjecture,(
% 3.13/0.98    ~! [X0] : (v3_ordinal1(X0) => (~(v4_ordinal1(X0) & ? [X1] : (k1_ordinal1(X1) = X0 & v3_ordinal1(X1))) & ~(! [X1] : (v3_ordinal1(X1) => k1_ordinal1(X1) != X0) & ~v4_ordinal1(X0))))),
% 3.13/0.98    inference(negated_conjecture,[],[f11])).
% 3.13/0.98  
% 3.13/0.98  fof(f13,plain,(
% 3.13/0.98    ~! [X0] : (v3_ordinal1(X0) => (~(v4_ordinal1(X0) & ? [X1] : (k1_ordinal1(X1) = X0 & v3_ordinal1(X1))) & ~(! [X2] : (v3_ordinal1(X2) => k1_ordinal1(X2) != X0) & ~v4_ordinal1(X0))))),
% 3.13/0.98    inference(rectify,[],[f12])).
% 3.13/0.98  
% 3.13/0.98  fof(f23,plain,(
% 3.13/0.98    ? [X0] : (((v4_ordinal1(X0) & ? [X1] : (k1_ordinal1(X1) = X0 & v3_ordinal1(X1))) | (! [X2] : (k1_ordinal1(X2) != X0 | ~v3_ordinal1(X2)) & ~v4_ordinal1(X0))) & v3_ordinal1(X0))),
% 3.13/0.98    inference(ennf_transformation,[],[f13])).
% 3.13/0.98  
% 3.13/0.98  fof(f36,plain,(
% 3.13/0.98    ( ! [X0] : (? [X1] : (k1_ordinal1(X1) = X0 & v3_ordinal1(X1)) => (k1_ordinal1(sK2) = X0 & v3_ordinal1(sK2))) )),
% 3.13/0.98    introduced(choice_axiom,[])).
% 3.13/0.98  
% 3.13/0.98  fof(f35,plain,(
% 3.13/0.98    ? [X0] : (((v4_ordinal1(X0) & ? [X1] : (k1_ordinal1(X1) = X0 & v3_ordinal1(X1))) | (! [X2] : (k1_ordinal1(X2) != X0 | ~v3_ordinal1(X2)) & ~v4_ordinal1(X0))) & v3_ordinal1(X0)) => (((v4_ordinal1(sK1) & ? [X1] : (k1_ordinal1(X1) = sK1 & v3_ordinal1(X1))) | (! [X2] : (k1_ordinal1(X2) != sK1 | ~v3_ordinal1(X2)) & ~v4_ordinal1(sK1))) & v3_ordinal1(sK1))),
% 3.13/0.98    introduced(choice_axiom,[])).
% 3.13/0.98  
% 3.13/0.98  fof(f37,plain,(
% 3.13/0.98    ((v4_ordinal1(sK1) & (k1_ordinal1(sK2) = sK1 & v3_ordinal1(sK2))) | (! [X2] : (k1_ordinal1(X2) != sK1 | ~v3_ordinal1(X2)) & ~v4_ordinal1(sK1))) & v3_ordinal1(sK1)),
% 3.13/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f23,f36,f35])).
% 3.13/0.98  
% 3.13/0.98  fof(f64,plain,(
% 3.13/0.98    ( ! [X2] : (v4_ordinal1(sK1) | k1_ordinal1(X2) != sK1 | ~v3_ordinal1(X2)) )),
% 3.13/0.98    inference(cnf_transformation,[],[f37])).
% 3.13/0.98  
% 3.13/0.98  fof(f76,plain,(
% 3.13/0.98    ( ! [X2] : (v4_ordinal1(sK1) | k2_xboole_0(X2,k1_tarski(X2)) != sK1 | ~v3_ordinal1(X2)) )),
% 3.13/0.98    inference(definition_unfolding,[],[f64,f42])).
% 3.13/0.98  
% 3.13/0.98  fof(f58,plain,(
% 3.13/0.98    v3_ordinal1(sK1)),
% 3.13/0.98    inference(cnf_transformation,[],[f37])).
% 3.13/0.98  
% 3.13/0.98  fof(f59,plain,(
% 3.13/0.98    v3_ordinal1(sK2) | ~v4_ordinal1(sK1)),
% 3.13/0.98    inference(cnf_transformation,[],[f37])).
% 3.13/0.98  
% 3.13/0.98  fof(f61,plain,(
% 3.13/0.98    k1_ordinal1(sK2) = sK1 | ~v4_ordinal1(sK1)),
% 3.13/0.98    inference(cnf_transformation,[],[f37])).
% 3.13/0.98  
% 3.13/0.98  fof(f78,plain,(
% 3.13/0.98    k2_xboole_0(sK2,k1_tarski(sK2)) = sK1 | ~v4_ordinal1(sK1)),
% 3.13/0.98    inference(definition_unfolding,[],[f61,f42])).
% 3.13/0.98  
% 3.13/0.98  fof(f52,plain,(
% 3.13/0.98    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.13/0.98    inference(cnf_transformation,[],[f30])).
% 3.13/0.98  
% 3.13/0.98  fof(f73,plain,(
% 3.13/0.98    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | ~r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.13/0.98    inference(definition_unfolding,[],[f52,f42])).
% 3.13/0.98  
% 3.13/0.98  fof(f8,axiom,(
% 3.13/0.98    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 3.13/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.13/0.98  
% 3.13/0.98  fof(f19,plain,(
% 3.13/0.98    ! [X0] : (! [X1] : ((r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 3.13/0.98    inference(ennf_transformation,[],[f8])).
% 3.13/0.98  
% 3.13/0.98  fof(f29,plain,(
% 3.13/0.98    ! [X0] : (! [X1] : (((r2_hidden(X0,X1) | ~r1_ordinal1(k1_ordinal1(X0),X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1))) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 3.13/0.98    inference(nnf_transformation,[],[f19])).
% 3.13/0.98  
% 3.13/0.98  fof(f50,plain,(
% 3.13/0.98    ( ! [X0,X1] : (r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.13/0.98    inference(cnf_transformation,[],[f29])).
% 3.13/0.98  
% 3.13/0.98  fof(f71,plain,(
% 3.13/0.98    ( ! [X0,X1] : (r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),X1) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.13/0.98    inference(definition_unfolding,[],[f50,f42])).
% 3.13/0.98  
% 3.13/0.98  fof(f7,axiom,(
% 3.13/0.98    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k1_ordinal1(X0)))),
% 3.13/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.13/0.98  
% 3.13/0.98  fof(f18,plain,(
% 3.13/0.98    ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 3.13/0.98    inference(ennf_transformation,[],[f7])).
% 3.13/0.98  
% 3.13/0.98  fof(f49,plain,(
% 3.13/0.98    ( ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0)) )),
% 3.13/0.98    inference(cnf_transformation,[],[f18])).
% 3.13/0.98  
% 3.13/0.98  fof(f69,plain,(
% 3.13/0.98    ( ! [X0] : (v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) | ~v3_ordinal1(X0)) )),
% 3.13/0.98    inference(definition_unfolding,[],[f49,f42])).
% 3.13/0.98  
% 3.13/0.98  fof(f6,axiom,(
% 3.13/0.98    ! [X0] : k1_ordinal1(X0) != X0),
% 3.13/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.13/0.98  
% 3.13/0.98  fof(f48,plain,(
% 3.13/0.98    ( ! [X0] : (k1_ordinal1(X0) != X0) )),
% 3.13/0.98    inference(cnf_transformation,[],[f6])).
% 3.13/0.98  
% 3.13/0.98  fof(f68,plain,(
% 3.13/0.98    ( ! [X0] : (k2_xboole_0(X0,k1_tarski(X0)) != X0) )),
% 3.13/0.98    inference(definition_unfolding,[],[f48,f42])).
% 3.13/0.98  
% 3.13/0.98  fof(f47,plain,(
% 3.13/0.98    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | X0 != X1) )),
% 3.13/0.98    inference(cnf_transformation,[],[f28])).
% 3.13/0.98  
% 3.13/0.98  fof(f65,plain,(
% 3.13/0.98    ( ! [X0,X1] : (r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | X0 != X1) )),
% 3.13/0.98    inference(definition_unfolding,[],[f47,f42])).
% 3.13/0.98  
% 3.13/0.98  fof(f82,plain,(
% 3.13/0.98    ( ! [X1] : (r2_hidden(X1,k2_xboole_0(X1,k1_tarski(X1)))) )),
% 3.13/0.98    inference(equality_resolution,[],[f65])).
% 3.13/0.98  
% 3.13/0.98  fof(f4,axiom,(
% 3.13/0.98    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 3.13/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.13/0.98  
% 3.13/0.98  fof(f16,plain,(
% 3.13/0.98    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 3.13/0.98    inference(ennf_transformation,[],[f4])).
% 3.13/0.98  
% 3.13/0.98  fof(f17,plain,(
% 3.13/0.98    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 3.13/0.98    inference(flattening,[],[f16])).
% 3.13/0.98  
% 3.13/0.98  fof(f26,plain,(
% 3.13/0.98    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 3.13/0.98    inference(nnf_transformation,[],[f17])).
% 3.13/0.98  
% 3.13/0.98  fof(f43,plain,(
% 3.13/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.13/0.98    inference(cnf_transformation,[],[f26])).
% 3.13/0.98  
% 3.13/0.98  fof(f1,axiom,(
% 3.13/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.13/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.13/0.98  
% 3.13/0.98  fof(f24,plain,(
% 3.13/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.13/0.98    inference(nnf_transformation,[],[f1])).
% 3.13/0.98  
% 3.13/0.98  fof(f25,plain,(
% 3.13/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.13/0.98    inference(flattening,[],[f24])).
% 3.13/0.98  
% 3.13/0.98  fof(f40,plain,(
% 3.13/0.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.13/0.98    inference(cnf_transformation,[],[f25])).
% 3.13/0.98  
% 3.13/0.98  fof(f46,plain,(
% 3.13/0.98    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | ~r2_hidden(X0,X1)) )),
% 3.13/0.98    inference(cnf_transformation,[],[f28])).
% 3.13/0.98  
% 3.13/0.98  fof(f66,plain,(
% 3.13/0.98    ( ! [X0,X1] : (r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | ~r2_hidden(X0,X1)) )),
% 3.13/0.98    inference(definition_unfolding,[],[f46,f42])).
% 3.13/0.98  
% 3.13/0.98  fof(f51,plain,(
% 3.13/0.98    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_ordinal1(k1_ordinal1(X0),X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.13/0.98    inference(cnf_transformation,[],[f29])).
% 3.13/0.98  
% 3.13/0.98  fof(f70,plain,(
% 3.13/0.98    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.13/0.98    inference(definition_unfolding,[],[f51,f42])).
% 3.13/0.98  
% 3.13/0.98  fof(f10,axiom,(
% 3.13/0.98    ! [X0] : (v3_ordinal1(X0) => (v4_ordinal1(X0) <=> ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) => r2_hidden(k1_ordinal1(X1),X0)))))),
% 3.13/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.13/0.98  
% 3.13/0.98  fof(f21,plain,(
% 3.13/0.98    ! [X0] : ((v4_ordinal1(X0) <=> ! [X1] : ((r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0)) | ~v3_ordinal1(X1))) | ~v3_ordinal1(X0))),
% 3.13/0.98    inference(ennf_transformation,[],[f10])).
% 3.13/0.98  
% 3.13/0.98  fof(f22,plain,(
% 3.13/0.98    ! [X0] : ((v4_ordinal1(X0) <=> ! [X1] : (r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X1))) | ~v3_ordinal1(X0))),
% 3.13/0.98    inference(flattening,[],[f21])).
% 3.13/0.98  
% 3.13/0.98  fof(f31,plain,(
% 3.13/0.98    ! [X0] : (((v4_ordinal1(X0) | ? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1))) & (! [X1] : (r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X1)) | ~v4_ordinal1(X0))) | ~v3_ordinal1(X0))),
% 3.13/0.98    inference(nnf_transformation,[],[f22])).
% 3.13/0.98  
% 3.13/0.98  fof(f32,plain,(
% 3.13/0.98    ! [X0] : (((v4_ordinal1(X0) | ? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1))) & (! [X2] : (r2_hidden(k1_ordinal1(X2),X0) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2)) | ~v4_ordinal1(X0))) | ~v3_ordinal1(X0))),
% 3.13/0.98    inference(rectify,[],[f31])).
% 3.13/0.98  
% 3.13/0.98  fof(f33,plain,(
% 3.13/0.98    ! [X0] : (? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) => (~r2_hidden(k1_ordinal1(sK0(X0)),X0) & r2_hidden(sK0(X0),X0) & v3_ordinal1(sK0(X0))))),
% 3.13/0.98    introduced(choice_axiom,[])).
% 3.13/0.98  
% 3.13/0.98  fof(f34,plain,(
% 3.13/0.98    ! [X0] : (((v4_ordinal1(X0) | (~r2_hidden(k1_ordinal1(sK0(X0)),X0) & r2_hidden(sK0(X0),X0) & v3_ordinal1(sK0(X0)))) & (! [X2] : (r2_hidden(k1_ordinal1(X2),X0) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2)) | ~v4_ordinal1(X0))) | ~v3_ordinal1(X0))),
% 3.13/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f32,f33])).
% 3.13/0.98  
% 3.13/0.98  fof(f54,plain,(
% 3.13/0.98    ( ! [X2,X0] : (r2_hidden(k1_ordinal1(X2),X0) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2) | ~v4_ordinal1(X0) | ~v3_ordinal1(X0)) )),
% 3.13/0.98    inference(cnf_transformation,[],[f34])).
% 3.13/0.98  
% 3.13/0.98  fof(f75,plain,(
% 3.13/0.98    ( ! [X2,X0] : (r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),X0) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2) | ~v4_ordinal1(X0) | ~v3_ordinal1(X0)) )),
% 3.13/0.98    inference(definition_unfolding,[],[f54,f42])).
% 3.13/0.98  
% 3.13/0.98  fof(f57,plain,(
% 3.13/0.98    ( ! [X0] : (v4_ordinal1(X0) | ~r2_hidden(k1_ordinal1(sK0(X0)),X0) | ~v3_ordinal1(X0)) )),
% 3.13/0.98    inference(cnf_transformation,[],[f34])).
% 3.13/0.98  
% 3.13/0.98  fof(f74,plain,(
% 3.13/0.98    ( ! [X0] : (v4_ordinal1(X0) | ~r2_hidden(k2_xboole_0(sK0(X0),k1_tarski(sK0(X0))),X0) | ~v3_ordinal1(X0)) )),
% 3.13/0.98    inference(definition_unfolding,[],[f57,f42])).
% 3.13/0.98  
% 3.13/0.98  fof(f56,plain,(
% 3.13/0.98    ( ! [X0] : (v4_ordinal1(X0) | r2_hidden(sK0(X0),X0) | ~v3_ordinal1(X0)) )),
% 3.13/0.98    inference(cnf_transformation,[],[f34])).
% 3.13/0.98  
% 3.13/0.98  fof(f55,plain,(
% 3.13/0.98    ( ! [X0] : (v4_ordinal1(X0) | v3_ordinal1(sK0(X0)) | ~v3_ordinal1(X0)) )),
% 3.13/0.98    inference(cnf_transformation,[],[f34])).
% 3.13/0.98  
% 3.13/0.98  cnf(c_13,plain,
% 3.13/0.98      ( r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
% 3.13/0.98      | ~ r1_ordinal1(X0,X1)
% 3.13/0.98      | ~ v3_ordinal1(X1)
% 3.13/0.98      | ~ v3_ordinal1(X0) ),
% 3.13/0.98      inference(cnf_transformation,[],[f72]) ).
% 3.13/0.98  
% 3.13/0.98  cnf(c_8,plain,
% 3.13/0.98      ( r2_hidden(X0,X1)
% 3.13/0.98      | ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
% 3.13/0.98      | X1 = X0 ),
% 3.13/0.98      inference(cnf_transformation,[],[f67]) ).
% 3.13/0.98  
% 3.13/0.98  cnf(c_2825,plain,
% 3.13/0.98      ( r2_hidden(X0,X1)
% 3.13/0.98      | ~ r1_ordinal1(X0,X1)
% 3.13/0.98      | ~ v3_ordinal1(X1)
% 3.13/0.98      | ~ v3_ordinal1(X0)
% 3.13/0.98      | X1 = X0 ),
% 3.13/0.98      inference(resolution,[status(thm)],[c_13,c_8]) ).
% 3.13/0.98  
% 3.13/0.98  cnf(c_826,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.13/0.98  
% 3.13/0.98  cnf(c_825,plain,( X0 = X0 ),theory(equality) ).
% 3.13/0.98  
% 3.13/0.98  cnf(c_2603,plain,
% 3.13/0.98      ( X0 != X1 | X1 = X0 ),
% 3.13/0.98      inference(resolution,[status(thm)],[c_826,c_825]) ).
% 3.13/0.98  
% 3.13/0.98  cnf(c_5464,plain,
% 3.13/0.98      ( r2_hidden(X0,X1)
% 3.13/0.98      | ~ r1_ordinal1(X0,X1)
% 3.13/0.98      | ~ v3_ordinal1(X1)
% 3.13/0.98      | ~ v3_ordinal1(X0)
% 3.13/0.98      | X0 = X1 ),
% 3.13/0.98      inference(resolution,[status(thm)],[c_2825,c_2603]) ).
% 3.13/0.98  
% 3.13/0.98  cnf(c_19,negated_conjecture,
% 3.13/0.98      ( v4_ordinal1(sK1)
% 3.13/0.98      | ~ v3_ordinal1(X0)
% 3.13/0.98      | k2_xboole_0(X0,k1_tarski(X0)) != sK1 ),
% 3.13/0.98      inference(cnf_transformation,[],[f76]) ).
% 3.13/0.98  
% 3.13/0.98  cnf(c_13165,plain,
% 3.13/0.98      ( r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),sK1)
% 3.13/0.98      | ~ r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),sK1)
% 3.13/0.98      | v4_ordinal1(sK1)
% 3.13/0.98      | ~ v3_ordinal1(X0)
% 3.13/0.98      | ~ v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0)))
% 3.13/0.98      | ~ v3_ordinal1(sK1) ),
% 3.13/0.98      inference(resolution,[status(thm)],[c_5464,c_19]) ).
% 3.13/0.98  
% 3.13/0.98  cnf(c_25,negated_conjecture,
% 3.13/0.98      ( v3_ordinal1(sK1) ),
% 3.13/0.98      inference(cnf_transformation,[],[f58]) ).
% 3.13/0.98  
% 3.13/0.98  cnf(c_24,negated_conjecture,
% 3.13/0.98      ( ~ v4_ordinal1(sK1) | v3_ordinal1(sK2) ),
% 3.13/0.98      inference(cnf_transformation,[],[f59]) ).
% 3.13/0.98  
% 3.13/0.98  cnf(c_22,negated_conjecture,
% 3.13/0.98      ( ~ v4_ordinal1(sK1) | k2_xboole_0(sK2,k1_tarski(sK2)) = sK1 ),
% 3.13/0.98      inference(cnf_transformation,[],[f78]) ).
% 3.13/0.98  
% 3.13/0.98  cnf(c_14,plain,
% 3.13/0.98      ( ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
% 3.13/0.98      | r1_ordinal1(X0,X1)
% 3.13/0.98      | ~ v3_ordinal1(X1)
% 3.13/0.98      | ~ v3_ordinal1(X0) ),
% 3.13/0.98      inference(cnf_transformation,[],[f73]) ).
% 3.13/0.98  
% 3.13/0.98  cnf(c_52,plain,
% 3.13/0.98      ( ~ r2_hidden(sK1,k2_xboole_0(sK1,k1_tarski(sK1)))
% 3.13/0.98      | r1_ordinal1(sK1,sK1)
% 3.13/0.98      | ~ v3_ordinal1(sK1) ),
% 3.13/0.98      inference(instantiation,[status(thm)],[c_14]) ).
% 3.13/0.98  
% 3.13/0.98  cnf(c_12,plain,
% 3.13/0.98      ( ~ r2_hidden(X0,X1)
% 3.13/0.98      | r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),X1)
% 3.13/0.98      | ~ v3_ordinal1(X1)
% 3.13/0.98      | ~ v3_ordinal1(X0) ),
% 3.13/0.98      inference(cnf_transformation,[],[f71]) ).
% 3.13/0.98  
% 3.13/0.98  cnf(c_58,plain,
% 3.13/0.98      ( ~ r2_hidden(sK1,sK1)
% 3.13/0.98      | r1_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1)),sK1)
% 3.13/0.98      | ~ v3_ordinal1(sK1) ),
% 3.13/0.98      inference(instantiation,[status(thm)],[c_12]) ).
% 3.13/0.98  
% 3.13/0.98  cnf(c_10,plain,
% 3.13/0.98      ( ~ v3_ordinal1(X0) | v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) ),
% 3.13/0.98      inference(cnf_transformation,[],[f69]) ).
% 3.13/0.98  
% 3.13/0.98  cnf(c_64,plain,
% 3.13/0.98      ( v3_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1)))
% 3.13/0.98      | ~ v3_ordinal1(sK1) ),
% 3.13/0.98      inference(instantiation,[status(thm)],[c_10]) ).
% 3.13/0.98  
% 3.13/0.98  cnf(c_9,plain,
% 3.13/0.98      ( k2_xboole_0(X0,k1_tarski(X0)) != X0 ),
% 3.13/0.98      inference(cnf_transformation,[],[f68]) ).
% 3.13/0.98  
% 3.13/0.98  cnf(c_66,plain,
% 3.13/0.98      ( k2_xboole_0(sK1,k1_tarski(sK1)) != sK1 ),
% 3.13/0.98      inference(instantiation,[status(thm)],[c_9]) ).
% 3.13/0.98  
% 3.13/0.98  cnf(c_6,plain,
% 3.13/0.98      ( r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0))) ),
% 3.13/0.98      inference(cnf_transformation,[],[f82]) ).
% 3.13/0.98  
% 3.13/0.98  cnf(c_74,plain,
% 3.13/0.98      ( r2_hidden(sK1,k2_xboole_0(sK1,k1_tarski(sK1))) ),
% 3.13/0.98      inference(instantiation,[status(thm)],[c_6]) ).
% 3.13/0.98  
% 3.13/0.98  cnf(c_5,plain,
% 3.13/0.98      ( ~ r1_ordinal1(X0,X1)
% 3.13/0.98      | r1_tarski(X0,X1)
% 3.13/0.98      | ~ v3_ordinal1(X1)
% 3.13/0.98      | ~ v3_ordinal1(X0) ),
% 3.13/0.98      inference(cnf_transformation,[],[f43]) ).
% 3.13/0.98  
% 3.13/0.98  cnf(c_77,plain,
% 3.13/0.98      ( ~ r1_ordinal1(sK1,sK1)
% 3.13/0.98      | r1_tarski(sK1,sK1)
% 3.13/0.98      | ~ v3_ordinal1(sK1) ),
% 3.13/0.98      inference(instantiation,[status(thm)],[c_5]) ).
% 3.13/0.98  
% 3.13/0.98  cnf(c_0,plain,
% 3.13/0.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.13/0.98      inference(cnf_transformation,[],[f40]) ).
% 3.13/0.98  
% 3.13/0.98  cnf(c_90,plain,
% 3.13/0.98      ( ~ r1_tarski(sK1,sK1) | sK1 = sK1 ),
% 3.13/0.98      inference(instantiation,[status(thm)],[c_0]) ).
% 3.13/0.98  
% 3.13/0.98  cnf(c_1506,plain,
% 3.13/0.98      ( ~ r1_tarski(X0,k2_xboole_0(X0,k1_tarski(X0)))
% 3.13/0.98      | ~ r1_tarski(k2_xboole_0(X0,k1_tarski(X0)),X0)
% 3.13/0.98      | k2_xboole_0(X0,k1_tarski(X0)) = X0 ),
% 3.13/0.98      inference(instantiation,[status(thm)],[c_0]) ).
% 3.13/0.98  
% 3.13/0.98  cnf(c_1508,plain,
% 3.13/0.98      ( ~ r1_tarski(k2_xboole_0(sK1,k1_tarski(sK1)),sK1)
% 3.13/0.98      | ~ r1_tarski(sK1,k2_xboole_0(sK1,k1_tarski(sK1)))
% 3.13/0.98      | k2_xboole_0(sK1,k1_tarski(sK1)) = sK1 ),
% 3.13/0.98      inference(instantiation,[status(thm)],[c_1506]) ).
% 3.13/0.98  
% 3.13/0.98  cnf(c_1649,plain,
% 3.13/0.98      ( ~ r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),X0)
% 3.13/0.98      | r1_tarski(k2_xboole_0(X0,k1_tarski(X0)),X0)
% 3.13/0.98      | ~ v3_ordinal1(X0)
% 3.13/0.98      | ~ v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) ),
% 3.13/0.98      inference(instantiation,[status(thm)],[c_5]) ).
% 3.13/0.98  
% 3.13/0.98  cnf(c_1651,plain,
% 3.13/0.98      ( ~ r1_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1)),sK1)
% 3.13/0.98      | r1_tarski(k2_xboole_0(sK1,k1_tarski(sK1)),sK1)
% 3.13/0.98      | ~ v3_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1)))
% 3.13/0.98      | ~ v3_ordinal1(sK1) ),
% 3.13/0.98      inference(instantiation,[status(thm)],[c_1649]) ).
% 3.13/0.98  
% 3.13/0.98  cnf(c_1825,plain,
% 3.13/0.98      ( ~ r1_ordinal1(X0,k2_xboole_0(X1,k1_tarski(X1)))
% 3.13/0.98      | r1_tarski(X0,k2_xboole_0(X1,k1_tarski(X1)))
% 3.13/0.98      | ~ v3_ordinal1(X0)
% 3.13/0.98      | ~ v3_ordinal1(k2_xboole_0(X1,k1_tarski(X1))) ),
% 3.13/0.98      inference(instantiation,[status(thm)],[c_5]) ).
% 3.13/0.98  
% 3.13/0.98  cnf(c_1827,plain,
% 3.13/0.98      ( ~ r1_ordinal1(sK1,k2_xboole_0(sK1,k1_tarski(sK1)))
% 3.13/0.98      | r1_tarski(sK1,k2_xboole_0(sK1,k1_tarski(sK1)))
% 3.13/0.98      | ~ v3_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1)))
% 3.13/0.98      | ~ v3_ordinal1(sK1) ),
% 3.13/0.98      inference(instantiation,[status(thm)],[c_1825]) ).
% 3.13/0.98  
% 3.13/0.98  cnf(c_1267,plain,
% 3.13/0.98      ( r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0))) = iProver_top ),
% 3.13/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.13/0.98  
% 3.13/0.98  cnf(c_7,plain,
% 3.13/0.98      ( ~ r2_hidden(X0,X1)
% 3.13/0.98      | r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) ),
% 3.13/0.98      inference(cnf_transformation,[],[f66]) ).
% 3.13/0.98  
% 3.13/0.98  cnf(c_1266,plain,
% 3.13/0.98      ( r2_hidden(X0,X1) != iProver_top
% 3.13/0.98      | r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) = iProver_top ),
% 3.13/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.13/0.98  
% 3.13/0.98  cnf(c_1260,plain,
% 3.13/0.98      ( r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) != iProver_top
% 3.13/0.98      | r1_ordinal1(X0,X1) = iProver_top
% 3.13/0.98      | v3_ordinal1(X0) != iProver_top
% 3.13/0.98      | v3_ordinal1(X1) != iProver_top ),
% 3.13/0.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.13/0.98  
% 3.13/0.98  cnf(c_2299,plain,
% 3.13/0.98      ( r2_hidden(X0,X1) != iProver_top
% 3.13/0.98      | r1_ordinal1(X0,X1) = iProver_top
% 3.13/0.98      | v3_ordinal1(X0) != iProver_top
% 3.13/0.98      | v3_ordinal1(X1) != iProver_top ),
% 3.13/0.98      inference(superposition,[status(thm)],[c_1266,c_1260]) ).
% 3.13/0.98  
% 3.13/0.98  cnf(c_2334,plain,
% 3.13/0.98      ( r1_ordinal1(X0,k2_xboole_0(X0,k1_tarski(X0))) = iProver_top
% 3.13/0.98      | v3_ordinal1(X0) != iProver_top
% 3.13/0.98      | v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) != iProver_top ),
% 3.13/0.98      inference(superposition,[status(thm)],[c_1267,c_2299]) ).
% 3.13/0.98  
% 3.13/0.98  cnf(c_2363,plain,
% 3.13/0.98      ( r1_ordinal1(X0,k2_xboole_0(X0,k1_tarski(X0)))
% 3.13/0.98      | ~ v3_ordinal1(X0)
% 3.13/0.98      | ~ v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) ),
% 3.13/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_2334]) ).
% 3.13/0.98  
% 3.13/0.98  cnf(c_2365,plain,
% 3.13/0.98      ( r1_ordinal1(sK1,k2_xboole_0(sK1,k1_tarski(sK1)))
% 3.13/0.98      | ~ v3_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1)))
% 3.13/0.98      | ~ v3_ordinal1(sK1) ),
% 3.13/0.98      inference(instantiation,[status(thm)],[c_2363]) ).
% 3.13/0.98  
% 3.13/0.98  cnf(c_827,plain,
% 3.13/0.98      ( ~ r1_ordinal1(X0,X1) | r1_ordinal1(X2,X1) | X2 != X0 ),
% 3.13/0.98      theory(equality) ).
% 3.13/0.98  
% 3.13/0.98  cnf(c_1546,plain,
% 3.13/0.98      ( ~ r1_ordinal1(X0,X1)
% 3.13/0.98      | r1_ordinal1(k2_xboole_0(X2,k1_tarski(X2)),X1)
% 3.13/0.98      | k2_xboole_0(X2,k1_tarski(X2)) != X0 ),
% 3.13/0.98      inference(instantiation,[status(thm)],[c_827]) ).
% 3.13/0.98  
% 3.13/0.98  cnf(c_2616,plain,
% 3.13/0.98      ( r1_ordinal1(k2_xboole_0(sK2,k1_tarski(sK2)),X0)
% 3.13/0.98      | ~ r1_ordinal1(sK1,X0)
% 3.13/0.98      | k2_xboole_0(sK2,k1_tarski(sK2)) != sK1 ),
% 3.13/0.98      inference(instantiation,[status(thm)],[c_1546]) ).
% 3.13/0.98  
% 3.13/0.98  cnf(c_2618,plain,
% 3.13/0.98      ( r1_ordinal1(k2_xboole_0(sK2,k1_tarski(sK2)),sK1)
% 3.13/0.98      | ~ r1_ordinal1(sK1,sK1)
% 3.13/0.98      | k2_xboole_0(sK2,k1_tarski(sK2)) != sK1 ),
% 3.13/0.98      inference(instantiation,[status(thm)],[c_2616]) ).
% 3.13/0.98  
% 3.13/0.98  cnf(c_1871,plain,
% 3.13/0.98      ( X0 != X1 | X0 = k2_xboole_0(X2,X3) | k2_xboole_0(X2,X3) != X1 ),
% 3.13/0.98      inference(instantiation,[status(thm)],[c_826]) ).
% 3.13/0.98  
% 3.13/0.98  cnf(c_2699,plain,
% 3.13/0.98      ( X0 = k2_xboole_0(sK2,k1_tarski(sK2))
% 3.13/0.98      | X0 != sK1
% 3.13/0.98      | k2_xboole_0(sK2,k1_tarski(sK2)) != sK1 ),
% 3.13/0.98      inference(instantiation,[status(thm)],[c_1871]) ).
% 3.13/0.98  
% 3.13/0.98  cnf(c_2700,plain,
% 3.13/0.98      ( k2_xboole_0(sK2,k1_tarski(sK2)) != sK1
% 3.13/0.98      | sK1 = k2_xboole_0(sK2,k1_tarski(sK2))
% 3.13/0.98      | sK1 != sK1 ),
% 3.13/0.98      inference(instantiation,[status(thm)],[c_2699]) ).
% 3.13/0.98  
% 3.13/0.98  cnf(c_11,plain,
% 3.13/0.98      ( r2_hidden(X0,X1)
% 3.13/0.98      | ~ r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),X1)
% 3.13/0.98      | ~ v3_ordinal1(X1)
% 3.13/0.98      | ~ v3_ordinal1(X0) ),
% 3.13/0.98      inference(cnf_transformation,[],[f70]) ).
% 3.13/0.98  
% 3.13/0.98  cnf(c_3771,plain,
% 3.13/0.98      ( r2_hidden(sK2,X0)
% 3.13/0.98      | ~ r1_ordinal1(k2_xboole_0(sK2,k1_tarski(sK2)),X0)
% 3.13/0.98      | ~ v3_ordinal1(X0)
% 3.13/0.98      | ~ v3_ordinal1(sK2) ),
% 3.13/0.98      inference(instantiation,[status(thm)],[c_11]) ).
% 3.13/0.98  
% 3.13/0.98  cnf(c_3773,plain,
% 3.13/0.98      ( r2_hidden(sK2,sK1)
% 3.13/0.98      | ~ r1_ordinal1(k2_xboole_0(sK2,k1_tarski(sK2)),sK1)
% 3.13/0.98      | ~ v3_ordinal1(sK2)
% 3.13/0.98      | ~ v3_ordinal1(sK1) ),
% 3.13/0.98      inference(instantiation,[status(thm)],[c_3771]) ).
% 3.13/0.98  
% 3.13/0.98  cnf(c_18,plain,
% 3.13/0.98      ( ~ r2_hidden(X0,X1)
% 3.13/0.98      | r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),X1)
% 3.13/0.98      | ~ v4_ordinal1(X1)
% 3.13/0.98      | ~ v3_ordinal1(X1)
% 3.13/0.98      | ~ v3_ordinal1(X0) ),
% 3.13/0.98      inference(cnf_transformation,[],[f75]) ).
% 3.13/0.98  
% 3.13/0.98  cnf(c_4296,plain,
% 3.13/0.98      ( r2_hidden(k2_xboole_0(sK2,k1_tarski(sK2)),X0)
% 3.13/0.98      | ~ r2_hidden(sK2,X0)
% 3.13/0.98      | ~ v4_ordinal1(X0)
% 3.13/0.98      | ~ v3_ordinal1(X0)
% 3.13/0.98      | ~ v3_ordinal1(sK2) ),
% 3.13/0.98      inference(instantiation,[status(thm)],[c_18]) ).
% 3.13/0.98  
% 3.13/0.98  cnf(c_4298,plain,
% 3.13/0.98      ( r2_hidden(k2_xboole_0(sK2,k1_tarski(sK2)),sK1)
% 3.13/0.98      | ~ r2_hidden(sK2,sK1)
% 3.13/0.98      | ~ v4_ordinal1(sK1)
% 3.13/0.98      | ~ v3_ordinal1(sK2)
% 3.13/0.98      | ~ v3_ordinal1(sK1) ),
% 3.13/0.98      inference(instantiation,[status(thm)],[c_4296]) ).
% 3.13/0.98  
% 3.13/0.98  cnf(c_831,plain,
% 3.13/0.98      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.13/0.98      theory(equality) ).
% 3.13/0.98  
% 3.13/0.98  cnf(c_2608,plain,
% 3.13/0.98      ( r2_hidden(X0,X1)
% 3.13/0.98      | ~ r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),X3)
% 3.13/0.98      | X1 != X3
% 3.13/0.98      | X0 != k2_xboole_0(X2,k1_tarski(X2)) ),
% 3.13/0.98      inference(instantiation,[status(thm)],[c_831]) ).
% 3.13/0.98  
% 3.13/0.98  cnf(c_10906,plain,
% 3.13/0.98      ( r2_hidden(X0,X1)
% 3.13/0.98      | ~ r2_hidden(k2_xboole_0(sK2,k1_tarski(sK2)),X2)
% 3.13/0.98      | X1 != X2
% 3.13/0.98      | X0 != k2_xboole_0(sK2,k1_tarski(sK2)) ),
% 3.13/0.98      inference(instantiation,[status(thm)],[c_2608]) ).
% 3.13/0.98  
% 3.13/0.98  cnf(c_10908,plain,
% 3.13/0.98      ( ~ r2_hidden(k2_xboole_0(sK2,k1_tarski(sK2)),sK1)
% 3.13/0.98      | r2_hidden(sK1,sK1)
% 3.13/0.98      | sK1 != k2_xboole_0(sK2,k1_tarski(sK2))
% 3.13/0.98      | sK1 != sK1 ),
% 3.13/0.98      inference(instantiation,[status(thm)],[c_10906]) ).
% 3.13/0.98  
% 3.13/0.98  cnf(c_13640,plain,
% 3.13/0.98      ( ~ r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),sK1)
% 3.13/0.98      | r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),sK1)
% 3.13/0.98      | ~ v3_ordinal1(X0) ),
% 3.13/0.98      inference(global_propositional_subsumption,
% 3.13/0.98                [status(thm)],
% 3.13/0.98                [c_13165,c_25,c_24,c_22,c_52,c_58,c_10,c_64,c_66,c_74,
% 3.13/0.98                 c_77,c_90,c_1508,c_1651,c_1827,c_2365,c_2618,c_2700,
% 3.13/0.98                 c_3773,c_4298,c_10908]) ).
% 3.13/0.98  
% 3.13/0.98  cnf(c_13641,plain,
% 3.13/0.98      ( r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),sK1)
% 3.13/0.98      | ~ r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),sK1)
% 3.13/0.98      | ~ v3_ordinal1(X0) ),
% 3.13/0.98      inference(renaming,[status(thm)],[c_13640]) ).
% 3.13/0.98  
% 3.13/0.98  cnf(c_15,plain,
% 3.13/0.98      ( ~ r2_hidden(k2_xboole_0(sK0(X0),k1_tarski(sK0(X0))),X0)
% 3.13/0.98      | v4_ordinal1(X0)
% 3.13/0.98      | ~ v3_ordinal1(X0) ),
% 3.13/0.98      inference(cnf_transformation,[],[f74]) ).
% 3.13/0.98  
% 3.13/0.98  cnf(c_13998,plain,
% 3.13/0.98      ( ~ r1_ordinal1(k2_xboole_0(sK0(sK1),k1_tarski(sK0(sK1))),sK1)
% 3.13/0.98      | v4_ordinal1(sK1)
% 3.13/0.98      | ~ v3_ordinal1(sK0(sK1))
% 3.13/0.98      | ~ v3_ordinal1(sK1) ),
% 3.13/0.98      inference(resolution,[status(thm)],[c_13641,c_15]) ).
% 3.13/0.98  
% 3.13/0.98  cnf(c_8838,plain,
% 3.13/0.98      ( ~ r2_hidden(sK0(X0),X0)
% 3.13/0.98      | r1_ordinal1(k2_xboole_0(sK0(X0),k1_tarski(sK0(X0))),X0)
% 3.13/0.98      | ~ v3_ordinal1(X0)
% 3.13/0.98      | ~ v3_ordinal1(sK0(X0)) ),
% 3.13/0.98      inference(instantiation,[status(thm)],[c_12]) ).
% 3.13/0.98  
% 3.13/0.98  cnf(c_8845,plain,
% 3.13/0.98      ( ~ r2_hidden(sK0(sK1),sK1)
% 3.13/0.98      | r1_ordinal1(k2_xboole_0(sK0(sK1),k1_tarski(sK0(sK1))),sK1)
% 3.13/0.98      | ~ v3_ordinal1(sK0(sK1))
% 3.13/0.98      | ~ v3_ordinal1(sK1) ),
% 3.13/0.98      inference(instantiation,[status(thm)],[c_8838]) ).
% 3.13/0.98  
% 3.13/0.98  cnf(c_16,plain,
% 3.13/0.98      ( r2_hidden(sK0(X0),X0) | v4_ordinal1(X0) | ~ v3_ordinal1(X0) ),
% 3.13/0.98      inference(cnf_transformation,[],[f56]) ).
% 3.13/0.98  
% 3.13/0.98  cnf(c_46,plain,
% 3.13/0.98      ( r2_hidden(sK0(sK1),sK1) | v4_ordinal1(sK1) | ~ v3_ordinal1(sK1) ),
% 3.13/0.98      inference(instantiation,[status(thm)],[c_16]) ).
% 3.13/0.98  
% 3.13/0.98  cnf(c_17,plain,
% 3.13/0.98      ( v4_ordinal1(X0) | ~ v3_ordinal1(X0) | v3_ordinal1(sK0(X0)) ),
% 3.13/0.98      inference(cnf_transformation,[],[f55]) ).
% 3.13/0.98  
% 3.13/0.98  cnf(c_43,plain,
% 3.13/0.98      ( v4_ordinal1(sK1) | v3_ordinal1(sK0(sK1)) | ~ v3_ordinal1(sK1) ),
% 3.13/0.98      inference(instantiation,[status(thm)],[c_17]) ).
% 3.13/0.98  
% 3.13/0.98  cnf(contradiction,plain,
% 3.13/0.98      ( $false ),
% 3.13/0.98      inference(minisat,
% 3.13/0.98                [status(thm)],
% 3.13/0.98                [c_13998,c_10908,c_8845,c_4298,c_3773,c_2700,c_2618,
% 3.13/0.98                 c_2365,c_1827,c_1651,c_1508,c_90,c_77,c_74,c_66,c_64,
% 3.13/0.98                 c_58,c_52,c_46,c_43,c_22,c_24,c_25]) ).
% 3.13/0.98  
% 3.13/0.98  
% 3.13/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.13/0.98  
% 3.13/0.98  ------                               Statistics
% 3.13/0.98  
% 3.13/0.98  ------ Selected
% 3.13/0.98  
% 3.13/0.98  total_time:                             0.416
% 3.13/0.98  
%------------------------------------------------------------------------------
