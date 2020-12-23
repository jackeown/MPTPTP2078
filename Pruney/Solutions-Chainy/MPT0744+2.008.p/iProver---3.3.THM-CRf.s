%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:53:47 EST 2020

% Result     : Theorem 3.46s
% Output     : CNFRefutation 3.46s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 964 expanded)
%              Number of clauses        :   74 ( 226 expanded)
%              Number of leaves         :   14 ( 229 expanded)
%              Depth                    :   19
%              Number of atoms          :  436 (3983 expanded)
%              Number of equality atoms :  104 ( 418 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f14,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X0,k1_ordinal1(X1))
            <=> r1_ordinal1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(X0,k1_ordinal1(X1))
          <~> r1_ordinal1(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(X0,X1)
            | ~ r2_hidden(X0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(X0,X1)
            | r2_hidden(X0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(X0,X1)
            | ~ r2_hidden(X0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(X0,X1)
            | r2_hidden(X0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f36])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(X0,X1)
            | ~ r2_hidden(X0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(X0,X1)
            | r2_hidden(X0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
     => ( ( ~ r1_ordinal1(X0,sK2)
          | ~ r2_hidden(X0,k1_ordinal1(sK2)) )
        & ( r1_ordinal1(X0,sK2)
          | r2_hidden(X0,k1_ordinal1(sK2)) )
        & v3_ordinal1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_ordinal1(X0,X1)
              | ~ r2_hidden(X0,k1_ordinal1(X1)) )
            & ( r1_ordinal1(X0,X1)
              | r2_hidden(X0,k1_ordinal1(X1)) )
            & v3_ordinal1(X1) )
        & v3_ordinal1(X0) )
   => ( ? [X1] :
          ( ( ~ r1_ordinal1(sK1,X1)
            | ~ r2_hidden(sK1,k1_ordinal1(X1)) )
          & ( r1_ordinal1(sK1,X1)
            | r2_hidden(sK1,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ( ~ r1_ordinal1(sK1,sK2)
      | ~ r2_hidden(sK1,k1_ordinal1(sK2)) )
    & ( r1_ordinal1(sK1,sK2)
      | r2_hidden(sK1,k1_ordinal1(sK2)) )
    & v3_ordinal1(sK2)
    & v3_ordinal1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f37,f39,f38])).

fof(f69,plain,
    ( ~ r1_ordinal1(sK1,sK2)
    | ~ r2_hidden(sK1,k1_ordinal1(sK2)) ),
    inference(cnf_transformation,[],[f40])).

fof(f9,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f70,plain,(
    ! [X0] : k2_xboole_0(X0,k2_tarski(X0,X0)) = k1_ordinal1(X0) ),
    inference(definition_unfolding,[],[f58,f53])).

fof(f75,plain,
    ( ~ r1_ordinal1(sK1,sK2)
    | ~ r2_hidden(sK1,k2_xboole_0(sK2,k2_tarski(sK2,sK2))) ),
    inference(definition_unfolding,[],[f69,f70])).

fof(f66,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f67,plain,(
    v3_ordinal1(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f68,plain,
    ( r1_ordinal1(sK1,sK2)
    | r2_hidden(sK1,k1_ordinal1(sK2)) ),
    inference(cnf_transformation,[],[f40])).

fof(f76,plain,
    ( r1_ordinal1(sK1,sK2)
    | r2_hidden(sK1,k2_xboole_0(sK2,k2_tarski(sK2,sK2))) ),
    inference(definition_unfolding,[],[f68,f70])).

fof(f13,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
    <=> ( X0 = X1
        | r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(flattening,[],[f34])).

fof(f61,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f74,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k2_xboole_0(X1,k2_tarski(X1,X1))) ) ),
    inference(definition_unfolding,[],[f61,f70])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_xboole_0(X1,k2_tarski(X1,X1)))
      | X0 != X1 ) ),
    inference(definition_unfolding,[],[f63,f70])).

fof(f82,plain,(
    ! [X1] : r2_hidden(X1,k2_xboole_0(X1,k2_tarski(X1,X1))) ),
    inference(equality_resolution,[],[f72])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f29])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f81,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f49])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f51,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f24])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f25])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            & ~ r2_hidden(sK0(X0,X1,X2),X0) )
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( r2_hidden(sK0(X0,X1,X2),X1)
          | r2_hidden(sK0(X0,X1,X2),X0)
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
              & ~ r2_hidden(sK0(X0,X1,X2),X0) )
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( r2_hidden(sK0(X0,X1,X2),X1)
            | r2_hidden(sK0(X0,X1,X2),X0)
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).

fof(f44,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f78,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f44])).

fof(f45,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f77,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f45])).

fof(f43,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f79,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f43])).

cnf(c_21,plain,
    ( r1_ordinal1(X0,X1)
    | r2_hidden(X1,X0)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_23,negated_conjecture,
    ( ~ r1_ordinal1(sK1,sK2)
    | ~ r2_hidden(sK1,k2_xboole_0(sK2,k2_tarski(sK2,sK2))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_203,plain,
    ( ~ r1_ordinal1(sK1,sK2)
    | ~ r2_hidden(sK1,k2_xboole_0(sK2,k2_tarski(sK2,sK2))) ),
    inference(prop_impl,[status(thm)],[c_23])).

cnf(c_352,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK1,k2_xboole_0(sK2,k2_tarski(sK2,sK2)))
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0)
    | sK2 != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_203])).

cnf(c_353,plain,
    ( r2_hidden(sK2,sK1)
    | ~ r2_hidden(sK1,k2_xboole_0(sK2,k2_tarski(sK2,sK2)))
    | ~ v3_ordinal1(sK2)
    | ~ v3_ordinal1(sK1) ),
    inference(unflattening,[status(thm)],[c_352])).

cnf(c_26,negated_conjecture,
    ( v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_25,negated_conjecture,
    ( v3_ordinal1(sK2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_355,plain,
    ( r2_hidden(sK2,sK1)
    | ~ r2_hidden(sK1,k2_xboole_0(sK2,k2_tarski(sK2,sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_353,c_26,c_25])).

cnf(c_17,plain,
    ( ~ r1_ordinal1(X0,X1)
    | r1_tarski(X0,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_24,negated_conjecture,
    ( r1_ordinal1(sK1,sK2)
    | r2_hidden(sK1,k2_xboole_0(sK2,k2_tarski(sK2,sK2))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_205,plain,
    ( r1_ordinal1(sK1,sK2)
    | r2_hidden(sK1,k2_xboole_0(sK2,k2_tarski(sK2,sK2))) ),
    inference(prop_impl,[status(thm)],[c_24])).

cnf(c_380,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1,k2_xboole_0(sK2,k2_tarski(sK2,sK2)))
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1)
    | sK2 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_205])).

cnf(c_381,plain,
    ( r1_tarski(sK1,sK2)
    | r2_hidden(sK1,k2_xboole_0(sK2,k2_tarski(sK2,sK2)))
    | ~ v3_ordinal1(sK2)
    | ~ v3_ordinal1(sK1) ),
    inference(unflattening,[status(thm)],[c_380])).

cnf(c_383,plain,
    ( r1_tarski(sK1,sK2)
    | r2_hidden(sK1,k2_xboole_0(sK2,k2_tarski(sK2,sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_381,c_26,c_25])).

cnf(c_493,plain,
    ( r1_tarski(sK1,sK2)
    | r2_hidden(sK1,k2_xboole_0(sK2,k2_tarski(sK2,sK2))) ),
    inference(prop_impl,[status(thm)],[c_26,c_25,c_381])).

cnf(c_536,plain,
    ( r1_tarski(sK1,sK2)
    | r2_hidden(sK2,sK1) ),
    inference(bin_hyper_res,[status(thm)],[c_355,c_493])).

cnf(c_1126,plain,
    ( r1_tarski(sK1,sK2) = iProver_top
    | r2_hidden(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_536])).

cnf(c_22,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_32,plain,
    ( ~ r1_tarski(sK2,sK2)
    | ~ r2_hidden(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_20,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k2_xboole_0(X1,k2_tarski(X1,X1)))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_38,plain,
    ( ~ r2_hidden(sK2,k2_xboole_0(sK2,k2_tarski(sK2,sK2)))
    | r2_hidden(sK2,sK2)
    | sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_18,plain,
    ( r2_hidden(X0,k2_xboole_0(X0,k2_tarski(X0,X0))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_44,plain,
    ( r2_hidden(sK2,k2_xboole_0(sK2,k2_tarski(sK2,sK2))) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_10,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_66,plain,
    ( r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_65,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_67,plain,
    ( r1_tarski(sK2,sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_65])).

cnf(c_385,plain,
    ( r1_tarski(sK1,sK2) = iProver_top
    | r2_hidden(sK1,k2_xboole_0(sK2,k2_tarski(sK2,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_383])).

cnf(c_547,plain,
    ( r1_tarski(sK1,sK2) = iProver_top
    | r2_hidden(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_536])).

cnf(c_624,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1184,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK1,sK2)
    | sK2 != X1
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_624])).

cnf(c_1185,plain,
    ( sK2 != X0
    | sK1 != X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1184])).

cnf(c_1187,plain,
    ( sK2 != sK2
    | sK1 != sK2
    | r1_tarski(sK2,sK2) != iProver_top
    | r1_tarski(sK1,sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1185])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1191,plain,
    ( ~ r2_hidden(sK2,sK1)
    | ~ r2_hidden(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1192,plain,
    ( r2_hidden(sK2,sK1) != iProver_top
    | r2_hidden(sK1,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1191])).

cnf(c_1230,plain,
    ( r2_hidden(sK1,X0)
    | ~ r2_hidden(sK1,k2_xboole_0(X0,k2_tarski(X0,X0)))
    | sK1 = X0 ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_1231,plain,
    ( sK1 = X0
    | r2_hidden(sK1,X0) = iProver_top
    | r2_hidden(sK1,k2_xboole_0(X0,k2_tarski(X0,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1230])).

cnf(c_1233,plain,
    ( sK1 = sK2
    | r2_hidden(sK1,k2_xboole_0(sK2,k2_tarski(sK2,sK2))) != iProver_top
    | r2_hidden(sK1,sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1231])).

cnf(c_1547,plain,
    ( r1_tarski(sK1,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1126,c_32,c_38,c_44,c_66,c_67,c_385,c_547,c_1187,c_1192,c_1233])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1142,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3230,plain,
    ( sK2 = sK1
    | r1_tarski(sK2,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1547,c_1142])).

cnf(c_27,plain,
    ( v3_ordinal1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_28,plain,
    ( v3_ordinal1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_16,plain,
    ( r1_ordinal1(X0,X1)
    | ~ r1_tarski(X0,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_366,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(sK1,k2_xboole_0(sK2,k2_tarski(sK2,sK2)))
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1)
    | sK2 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_203])).

cnf(c_367,plain,
    ( ~ r1_tarski(sK1,sK2)
    | ~ r2_hidden(sK1,k2_xboole_0(sK2,k2_tarski(sK2,sK2)))
    | ~ v3_ordinal1(sK2)
    | ~ v3_ordinal1(sK1) ),
    inference(unflattening,[status(thm)],[c_366])).

cnf(c_369,plain,
    ( ~ r1_tarski(sK1,sK2)
    | ~ r2_hidden(sK1,k2_xboole_0(sK2,k2_tarski(sK2,sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_367,c_26,c_25])).

cnf(c_371,plain,
    ( r1_tarski(sK1,sK2) != iProver_top
    | r2_hidden(sK1,k2_xboole_0(sK2,k2_tarski(sK2,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_369])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1257,plain,
    ( r2_hidden(sK1,k2_xboole_0(sK2,k2_tarski(sK2,sK2)))
    | ~ r2_hidden(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1258,plain,
    ( r2_hidden(sK1,k2_xboole_0(sK2,k2_tarski(sK2,sK2))) = iProver_top
    | r2_hidden(sK1,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1257])).

cnf(c_335,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(X1,X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1) ),
    inference(resolution,[status(thm)],[c_21,c_17])).

cnf(c_1263,plain,
    ( r1_tarski(X0,sK1)
    | r2_hidden(sK1,X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(sK1) ),
    inference(instantiation,[status(thm)],[c_335])).

cnf(c_1264,plain,
    ( r1_tarski(X0,sK1) = iProver_top
    | r2_hidden(sK1,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1263])).

cnf(c_1266,plain,
    ( r1_tarski(sK2,sK1) = iProver_top
    | r2_hidden(sK1,sK2) = iProver_top
    | v3_ordinal1(sK2) != iProver_top
    | v3_ordinal1(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1264])).

cnf(c_6418,plain,
    ( sK2 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3230,c_27,c_28,c_32,c_38,c_44,c_66,c_67,c_371,c_385,c_547,c_1187,c_1192,c_1233,c_1258,c_1266])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1145,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k2_xboole_0(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_491,plain,
    ( ~ r1_tarski(sK1,sK2)
    | ~ r2_hidden(sK1,k2_xboole_0(sK2,k2_tarski(sK2,sK2))) ),
    inference(prop_impl,[status(thm)],[c_26,c_25,c_367])).

cnf(c_1128,plain,
    ( r1_tarski(sK1,sK2) != iProver_top
    | r2_hidden(sK1,k2_xboole_0(sK2,k2_tarski(sK2,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_491])).

cnf(c_2850,plain,
    ( r2_hidden(sK1,k2_xboole_0(sK2,k2_tarski(sK2,sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1128,c_32,c_38,c_44,c_66,c_67,c_371,c_385,c_547,c_1187,c_1192,c_1233])).

cnf(c_2854,plain,
    ( r2_hidden(sK1,k2_tarski(sK2,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1145,c_2850])).

cnf(c_6420,plain,
    ( r2_hidden(sK1,k2_tarski(sK1,sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6418,c_2854])).

cnf(c_1642,plain,
    ( ~ r2_hidden(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1643,plain,
    ( r2_hidden(sK1,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1642])).

cnf(c_7,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1459,plain,
    ( r2_hidden(X0,X0)
    | r2_hidden(X0,k2_tarski(X0,X0))
    | ~ r2_hidden(X0,k2_xboole_0(X0,k2_tarski(X0,X0))) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1621,plain,
    ( r2_hidden(sK1,k2_tarski(sK1,sK1))
    | ~ r2_hidden(sK1,k2_xboole_0(sK1,k2_tarski(sK1,sK1)))
    | r2_hidden(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_1459])).

cnf(c_1623,plain,
    ( r2_hidden(sK1,k2_tarski(sK1,sK1)) = iProver_top
    | r2_hidden(sK1,k2_xboole_0(sK1,k2_tarski(sK1,sK1))) != iProver_top
    | r2_hidden(sK1,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1621])).

cnf(c_1366,plain,
    ( r2_hidden(sK1,k2_xboole_0(sK1,k2_tarski(sK1,sK1))) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_1367,plain,
    ( r2_hidden(sK1,k2_xboole_0(sK1,k2_tarski(sK1,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1366])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6420,c_1643,c_1623,c_1367])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:35:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 3.46/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.46/1.00  
% 3.46/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.46/1.00  
% 3.46/1.00  ------  iProver source info
% 3.46/1.00  
% 3.46/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.46/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.46/1.00  git: non_committed_changes: false
% 3.46/1.00  git: last_make_outside_of_git: false
% 3.46/1.00  
% 3.46/1.00  ------ 
% 3.46/1.00  
% 3.46/1.00  ------ Input Options
% 3.46/1.00  
% 3.46/1.00  --out_options                           all
% 3.46/1.00  --tptp_safe_out                         true
% 3.46/1.00  --problem_path                          ""
% 3.46/1.00  --include_path                          ""
% 3.46/1.00  --clausifier                            res/vclausify_rel
% 3.46/1.00  --clausifier_options                    ""
% 3.46/1.00  --stdin                                 false
% 3.46/1.00  --stats_out                             all
% 3.46/1.00  
% 3.46/1.00  ------ General Options
% 3.46/1.00  
% 3.46/1.00  --fof                                   false
% 3.46/1.00  --time_out_real                         305.
% 3.46/1.00  --time_out_virtual                      -1.
% 3.46/1.00  --symbol_type_check                     false
% 3.46/1.00  --clausify_out                          false
% 3.46/1.00  --sig_cnt_out                           false
% 3.46/1.00  --trig_cnt_out                          false
% 3.46/1.00  --trig_cnt_out_tolerance                1.
% 3.46/1.00  --trig_cnt_out_sk_spl                   false
% 3.46/1.00  --abstr_cl_out                          false
% 3.46/1.00  
% 3.46/1.00  ------ Global Options
% 3.46/1.00  
% 3.46/1.00  --schedule                              default
% 3.46/1.00  --add_important_lit                     false
% 3.46/1.00  --prop_solver_per_cl                    1000
% 3.46/1.00  --min_unsat_core                        false
% 3.46/1.00  --soft_assumptions                      false
% 3.46/1.00  --soft_lemma_size                       3
% 3.46/1.00  --prop_impl_unit_size                   0
% 3.46/1.00  --prop_impl_unit                        []
% 3.46/1.00  --share_sel_clauses                     true
% 3.46/1.00  --reset_solvers                         false
% 3.46/1.00  --bc_imp_inh                            [conj_cone]
% 3.46/1.00  --conj_cone_tolerance                   3.
% 3.46/1.00  --extra_neg_conj                        none
% 3.46/1.00  --large_theory_mode                     true
% 3.46/1.00  --prolific_symb_bound                   200
% 3.46/1.00  --lt_threshold                          2000
% 3.46/1.00  --clause_weak_htbl                      true
% 3.46/1.00  --gc_record_bc_elim                     false
% 3.46/1.00  
% 3.46/1.00  ------ Preprocessing Options
% 3.46/1.00  
% 3.46/1.00  --preprocessing_flag                    true
% 3.46/1.00  --time_out_prep_mult                    0.1
% 3.46/1.00  --splitting_mode                        input
% 3.46/1.00  --splitting_grd                         true
% 3.46/1.00  --splitting_cvd                         false
% 3.46/1.00  --splitting_cvd_svl                     false
% 3.46/1.00  --splitting_nvd                         32
% 3.46/1.00  --sub_typing                            true
% 3.46/1.00  --prep_gs_sim                           true
% 3.46/1.00  --prep_unflatten                        true
% 3.46/1.00  --prep_res_sim                          true
% 3.46/1.00  --prep_upred                            true
% 3.46/1.00  --prep_sem_filter                       exhaustive
% 3.46/1.00  --prep_sem_filter_out                   false
% 3.46/1.00  --pred_elim                             true
% 3.46/1.00  --res_sim_input                         true
% 3.46/1.00  --eq_ax_congr_red                       true
% 3.46/1.00  --pure_diseq_elim                       true
% 3.46/1.00  --brand_transform                       false
% 3.46/1.00  --non_eq_to_eq                          false
% 3.46/1.00  --prep_def_merge                        true
% 3.46/1.00  --prep_def_merge_prop_impl              false
% 3.46/1.00  --prep_def_merge_mbd                    true
% 3.46/1.00  --prep_def_merge_tr_red                 false
% 3.46/1.00  --prep_def_merge_tr_cl                  false
% 3.46/1.00  --smt_preprocessing                     true
% 3.46/1.00  --smt_ac_axioms                         fast
% 3.46/1.00  --preprocessed_out                      false
% 3.46/1.00  --preprocessed_stats                    false
% 3.46/1.00  
% 3.46/1.00  ------ Abstraction refinement Options
% 3.46/1.00  
% 3.46/1.00  --abstr_ref                             []
% 3.46/1.00  --abstr_ref_prep                        false
% 3.46/1.00  --abstr_ref_until_sat                   false
% 3.46/1.00  --abstr_ref_sig_restrict                funpre
% 3.46/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.46/1.00  --abstr_ref_under                       []
% 3.46/1.00  
% 3.46/1.00  ------ SAT Options
% 3.46/1.00  
% 3.46/1.00  --sat_mode                              false
% 3.46/1.00  --sat_fm_restart_options                ""
% 3.46/1.00  --sat_gr_def                            false
% 3.46/1.00  --sat_epr_types                         true
% 3.46/1.00  --sat_non_cyclic_types                  false
% 3.46/1.00  --sat_finite_models                     false
% 3.46/1.00  --sat_fm_lemmas                         false
% 3.46/1.00  --sat_fm_prep                           false
% 3.46/1.00  --sat_fm_uc_incr                        true
% 3.46/1.00  --sat_out_model                         small
% 3.46/1.00  --sat_out_clauses                       false
% 3.46/1.00  
% 3.46/1.00  ------ QBF Options
% 3.46/1.00  
% 3.46/1.00  --qbf_mode                              false
% 3.46/1.00  --qbf_elim_univ                         false
% 3.46/1.00  --qbf_dom_inst                          none
% 3.46/1.00  --qbf_dom_pre_inst                      false
% 3.46/1.00  --qbf_sk_in                             false
% 3.46/1.00  --qbf_pred_elim                         true
% 3.46/1.00  --qbf_split                             512
% 3.46/1.00  
% 3.46/1.00  ------ BMC1 Options
% 3.46/1.00  
% 3.46/1.00  --bmc1_incremental                      false
% 3.46/1.00  --bmc1_axioms                           reachable_all
% 3.46/1.00  --bmc1_min_bound                        0
% 3.46/1.00  --bmc1_max_bound                        -1
% 3.46/1.00  --bmc1_max_bound_default                -1
% 3.46/1.00  --bmc1_symbol_reachability              true
% 3.46/1.00  --bmc1_property_lemmas                  false
% 3.46/1.00  --bmc1_k_induction                      false
% 3.46/1.00  --bmc1_non_equiv_states                 false
% 3.46/1.00  --bmc1_deadlock                         false
% 3.46/1.00  --bmc1_ucm                              false
% 3.46/1.00  --bmc1_add_unsat_core                   none
% 3.46/1.00  --bmc1_unsat_core_children              false
% 3.46/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.46/1.00  --bmc1_out_stat                         full
% 3.46/1.00  --bmc1_ground_init                      false
% 3.46/1.00  --bmc1_pre_inst_next_state              false
% 3.46/1.00  --bmc1_pre_inst_state                   false
% 3.46/1.00  --bmc1_pre_inst_reach_state             false
% 3.46/1.00  --bmc1_out_unsat_core                   false
% 3.46/1.00  --bmc1_aig_witness_out                  false
% 3.46/1.00  --bmc1_verbose                          false
% 3.46/1.00  --bmc1_dump_clauses_tptp                false
% 3.46/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.46/1.00  --bmc1_dump_file                        -
% 3.46/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.46/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.46/1.00  --bmc1_ucm_extend_mode                  1
% 3.46/1.00  --bmc1_ucm_init_mode                    2
% 3.46/1.00  --bmc1_ucm_cone_mode                    none
% 3.46/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.46/1.00  --bmc1_ucm_relax_model                  4
% 3.46/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.46/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.46/1.00  --bmc1_ucm_layered_model                none
% 3.46/1.00  --bmc1_ucm_max_lemma_size               10
% 3.46/1.00  
% 3.46/1.00  ------ AIG Options
% 3.46/1.00  
% 3.46/1.00  --aig_mode                              false
% 3.46/1.00  
% 3.46/1.00  ------ Instantiation Options
% 3.46/1.00  
% 3.46/1.00  --instantiation_flag                    true
% 3.46/1.00  --inst_sos_flag                         true
% 3.46/1.00  --inst_sos_phase                        true
% 3.46/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.46/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.46/1.00  --inst_lit_sel_side                     num_symb
% 3.46/1.00  --inst_solver_per_active                1400
% 3.46/1.00  --inst_solver_calls_frac                1.
% 3.46/1.00  --inst_passive_queue_type               priority_queues
% 3.46/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.46/1.00  --inst_passive_queues_freq              [25;2]
% 3.46/1.00  --inst_dismatching                      true
% 3.46/1.00  --inst_eager_unprocessed_to_passive     true
% 3.46/1.00  --inst_prop_sim_given                   true
% 3.46/1.00  --inst_prop_sim_new                     false
% 3.46/1.00  --inst_subs_new                         false
% 3.46/1.00  --inst_eq_res_simp                      false
% 3.46/1.00  --inst_subs_given                       false
% 3.46/1.00  --inst_orphan_elimination               true
% 3.46/1.00  --inst_learning_loop_flag               true
% 3.46/1.00  --inst_learning_start                   3000
% 3.46/1.00  --inst_learning_factor                  2
% 3.46/1.00  --inst_start_prop_sim_after_learn       3
% 3.46/1.00  --inst_sel_renew                        solver
% 3.46/1.00  --inst_lit_activity_flag                true
% 3.46/1.00  --inst_restr_to_given                   false
% 3.46/1.00  --inst_activity_threshold               500
% 3.46/1.00  --inst_out_proof                        true
% 3.46/1.00  
% 3.46/1.00  ------ Resolution Options
% 3.46/1.00  
% 3.46/1.00  --resolution_flag                       true
% 3.46/1.00  --res_lit_sel                           adaptive
% 3.46/1.00  --res_lit_sel_side                      none
% 3.46/1.00  --res_ordering                          kbo
% 3.46/1.00  --res_to_prop_solver                    active
% 3.46/1.00  --res_prop_simpl_new                    false
% 3.46/1.00  --res_prop_simpl_given                  true
% 3.46/1.00  --res_passive_queue_type                priority_queues
% 3.46/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.46/1.00  --res_passive_queues_freq               [15;5]
% 3.46/1.00  --res_forward_subs                      full
% 3.46/1.00  --res_backward_subs                     full
% 3.46/1.00  --res_forward_subs_resolution           true
% 3.46/1.00  --res_backward_subs_resolution          true
% 3.46/1.00  --res_orphan_elimination                true
% 3.46/1.00  --res_time_limit                        2.
% 3.46/1.00  --res_out_proof                         true
% 3.46/1.00  
% 3.46/1.00  ------ Superposition Options
% 3.46/1.00  
% 3.46/1.00  --superposition_flag                    true
% 3.46/1.00  --sup_passive_queue_type                priority_queues
% 3.46/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.46/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.46/1.00  --demod_completeness_check              fast
% 3.46/1.00  --demod_use_ground                      true
% 3.46/1.00  --sup_to_prop_solver                    passive
% 3.46/1.00  --sup_prop_simpl_new                    true
% 3.46/1.00  --sup_prop_simpl_given                  true
% 3.46/1.00  --sup_fun_splitting                     true
% 3.46/1.00  --sup_smt_interval                      50000
% 3.46/1.00  
% 3.46/1.00  ------ Superposition Simplification Setup
% 3.46/1.00  
% 3.46/1.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.46/1.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.46/1.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.46/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.46/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.46/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.46/1.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.46/1.00  --sup_immed_triv                        [TrivRules]
% 3.46/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.46/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.46/1.00  --sup_immed_bw_main                     []
% 3.46/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.46/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.46/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.46/1.00  --sup_input_bw                          []
% 3.46/1.00  
% 3.46/1.00  ------ Combination Options
% 3.46/1.00  
% 3.46/1.00  --comb_res_mult                         3
% 3.46/1.00  --comb_sup_mult                         2
% 3.46/1.00  --comb_inst_mult                        10
% 3.46/1.00  
% 3.46/1.00  ------ Debug Options
% 3.46/1.00  
% 3.46/1.00  --dbg_backtrace                         false
% 3.46/1.00  --dbg_dump_prop_clauses                 false
% 3.46/1.00  --dbg_dump_prop_clauses_file            -
% 3.46/1.00  --dbg_out_stat                          false
% 3.46/1.00  ------ Parsing...
% 3.46/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.46/1.00  
% 3.46/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.46/1.00  
% 3.46/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.46/1.00  
% 3.46/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.46/1.00  ------ Proving...
% 3.46/1.00  ------ Problem Properties 
% 3.46/1.00  
% 3.46/1.00  
% 3.46/1.00  clauses                                 25
% 3.46/1.00  conjectures                             2
% 3.46/1.00  EPR                                     8
% 3.46/1.00  Horn                                    19
% 3.46/1.00  unary                                   6
% 3.46/1.00  binary                                  11
% 3.46/1.00  lits                                    54
% 3.46/1.00  lits eq                                 7
% 3.46/1.00  fd_pure                                 0
% 3.46/1.00  fd_pseudo                               0
% 3.46/1.00  fd_cond                                 0
% 3.46/1.00  fd_pseudo_cond                          5
% 3.46/1.00  AC symbols                              0
% 3.46/1.00  
% 3.46/1.00  ------ Schedule dynamic 5 is on 
% 3.46/1.00  
% 3.46/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.46/1.00  
% 3.46/1.00  
% 3.46/1.00  ------ 
% 3.46/1.00  Current options:
% 3.46/1.00  ------ 
% 3.46/1.00  
% 3.46/1.00  ------ Input Options
% 3.46/1.00  
% 3.46/1.00  --out_options                           all
% 3.46/1.00  --tptp_safe_out                         true
% 3.46/1.00  --problem_path                          ""
% 3.46/1.00  --include_path                          ""
% 3.46/1.00  --clausifier                            res/vclausify_rel
% 3.46/1.00  --clausifier_options                    ""
% 3.46/1.00  --stdin                                 false
% 3.46/1.00  --stats_out                             all
% 3.46/1.00  
% 3.46/1.00  ------ General Options
% 3.46/1.00  
% 3.46/1.00  --fof                                   false
% 3.46/1.00  --time_out_real                         305.
% 3.46/1.00  --time_out_virtual                      -1.
% 3.46/1.00  --symbol_type_check                     false
% 3.46/1.00  --clausify_out                          false
% 3.46/1.00  --sig_cnt_out                           false
% 3.46/1.00  --trig_cnt_out                          false
% 3.46/1.00  --trig_cnt_out_tolerance                1.
% 3.46/1.00  --trig_cnt_out_sk_spl                   false
% 3.46/1.00  --abstr_cl_out                          false
% 3.46/1.00  
% 3.46/1.00  ------ Global Options
% 3.46/1.00  
% 3.46/1.00  --schedule                              default
% 3.46/1.00  --add_important_lit                     false
% 3.46/1.00  --prop_solver_per_cl                    1000
% 3.46/1.00  --min_unsat_core                        false
% 3.46/1.00  --soft_assumptions                      false
% 3.46/1.00  --soft_lemma_size                       3
% 3.46/1.00  --prop_impl_unit_size                   0
% 3.46/1.00  --prop_impl_unit                        []
% 3.46/1.00  --share_sel_clauses                     true
% 3.46/1.00  --reset_solvers                         false
% 3.46/1.00  --bc_imp_inh                            [conj_cone]
% 3.46/1.00  --conj_cone_tolerance                   3.
% 3.46/1.00  --extra_neg_conj                        none
% 3.46/1.00  --large_theory_mode                     true
% 3.46/1.00  --prolific_symb_bound                   200
% 3.46/1.00  --lt_threshold                          2000
% 3.46/1.00  --clause_weak_htbl                      true
% 3.46/1.00  --gc_record_bc_elim                     false
% 3.46/1.00  
% 3.46/1.00  ------ Preprocessing Options
% 3.46/1.00  
% 3.46/1.00  --preprocessing_flag                    true
% 3.46/1.00  --time_out_prep_mult                    0.1
% 3.46/1.00  --splitting_mode                        input
% 3.46/1.00  --splitting_grd                         true
% 3.46/1.00  --splitting_cvd                         false
% 3.46/1.00  --splitting_cvd_svl                     false
% 3.46/1.00  --splitting_nvd                         32
% 3.46/1.00  --sub_typing                            true
% 3.46/1.00  --prep_gs_sim                           true
% 3.46/1.00  --prep_unflatten                        true
% 3.46/1.00  --prep_res_sim                          true
% 3.46/1.00  --prep_upred                            true
% 3.46/1.00  --prep_sem_filter                       exhaustive
% 3.46/1.00  --prep_sem_filter_out                   false
% 3.46/1.00  --pred_elim                             true
% 3.46/1.00  --res_sim_input                         true
% 3.46/1.00  --eq_ax_congr_red                       true
% 3.46/1.00  --pure_diseq_elim                       true
% 3.46/1.00  --brand_transform                       false
% 3.46/1.00  --non_eq_to_eq                          false
% 3.46/1.00  --prep_def_merge                        true
% 3.46/1.00  --prep_def_merge_prop_impl              false
% 3.46/1.00  --prep_def_merge_mbd                    true
% 3.46/1.00  --prep_def_merge_tr_red                 false
% 3.46/1.00  --prep_def_merge_tr_cl                  false
% 3.46/1.00  --smt_preprocessing                     true
% 3.46/1.00  --smt_ac_axioms                         fast
% 3.46/1.00  --preprocessed_out                      false
% 3.46/1.00  --preprocessed_stats                    false
% 3.46/1.00  
% 3.46/1.00  ------ Abstraction refinement Options
% 3.46/1.00  
% 3.46/1.00  --abstr_ref                             []
% 3.46/1.00  --abstr_ref_prep                        false
% 3.46/1.00  --abstr_ref_until_sat                   false
% 3.46/1.00  --abstr_ref_sig_restrict                funpre
% 3.46/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.46/1.00  --abstr_ref_under                       []
% 3.46/1.00  
% 3.46/1.00  ------ SAT Options
% 3.46/1.00  
% 3.46/1.00  --sat_mode                              false
% 3.46/1.00  --sat_fm_restart_options                ""
% 3.46/1.00  --sat_gr_def                            false
% 3.46/1.00  --sat_epr_types                         true
% 3.46/1.00  --sat_non_cyclic_types                  false
% 3.46/1.00  --sat_finite_models                     false
% 3.46/1.00  --sat_fm_lemmas                         false
% 3.46/1.00  --sat_fm_prep                           false
% 3.46/1.00  --sat_fm_uc_incr                        true
% 3.46/1.00  --sat_out_model                         small
% 3.46/1.00  --sat_out_clauses                       false
% 3.46/1.00  
% 3.46/1.00  ------ QBF Options
% 3.46/1.00  
% 3.46/1.00  --qbf_mode                              false
% 3.46/1.00  --qbf_elim_univ                         false
% 3.46/1.00  --qbf_dom_inst                          none
% 3.46/1.00  --qbf_dom_pre_inst                      false
% 3.46/1.00  --qbf_sk_in                             false
% 3.46/1.00  --qbf_pred_elim                         true
% 3.46/1.00  --qbf_split                             512
% 3.46/1.00  
% 3.46/1.00  ------ BMC1 Options
% 3.46/1.00  
% 3.46/1.00  --bmc1_incremental                      false
% 3.46/1.00  --bmc1_axioms                           reachable_all
% 3.46/1.00  --bmc1_min_bound                        0
% 3.46/1.00  --bmc1_max_bound                        -1
% 3.46/1.00  --bmc1_max_bound_default                -1
% 3.46/1.00  --bmc1_symbol_reachability              true
% 3.46/1.00  --bmc1_property_lemmas                  false
% 3.46/1.00  --bmc1_k_induction                      false
% 3.46/1.00  --bmc1_non_equiv_states                 false
% 3.46/1.00  --bmc1_deadlock                         false
% 3.46/1.00  --bmc1_ucm                              false
% 3.46/1.00  --bmc1_add_unsat_core                   none
% 3.46/1.00  --bmc1_unsat_core_children              false
% 3.46/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.46/1.00  --bmc1_out_stat                         full
% 3.46/1.00  --bmc1_ground_init                      false
% 3.46/1.00  --bmc1_pre_inst_next_state              false
% 3.46/1.00  --bmc1_pre_inst_state                   false
% 3.46/1.00  --bmc1_pre_inst_reach_state             false
% 3.46/1.00  --bmc1_out_unsat_core                   false
% 3.46/1.00  --bmc1_aig_witness_out                  false
% 3.46/1.00  --bmc1_verbose                          false
% 3.46/1.00  --bmc1_dump_clauses_tptp                false
% 3.46/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.46/1.00  --bmc1_dump_file                        -
% 3.46/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.46/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.46/1.00  --bmc1_ucm_extend_mode                  1
% 3.46/1.00  --bmc1_ucm_init_mode                    2
% 3.46/1.00  --bmc1_ucm_cone_mode                    none
% 3.46/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.46/1.00  --bmc1_ucm_relax_model                  4
% 3.46/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.46/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.46/1.00  --bmc1_ucm_layered_model                none
% 3.46/1.00  --bmc1_ucm_max_lemma_size               10
% 3.46/1.00  
% 3.46/1.00  ------ AIG Options
% 3.46/1.00  
% 3.46/1.00  --aig_mode                              false
% 3.46/1.00  
% 3.46/1.00  ------ Instantiation Options
% 3.46/1.00  
% 3.46/1.00  --instantiation_flag                    true
% 3.46/1.00  --inst_sos_flag                         true
% 3.46/1.00  --inst_sos_phase                        true
% 3.46/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.46/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.46/1.00  --inst_lit_sel_side                     none
% 3.46/1.00  --inst_solver_per_active                1400
% 3.46/1.00  --inst_solver_calls_frac                1.
% 3.46/1.00  --inst_passive_queue_type               priority_queues
% 3.46/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.46/1.00  --inst_passive_queues_freq              [25;2]
% 3.46/1.00  --inst_dismatching                      true
% 3.46/1.00  --inst_eager_unprocessed_to_passive     true
% 3.46/1.00  --inst_prop_sim_given                   true
% 3.46/1.00  --inst_prop_sim_new                     false
% 3.46/1.00  --inst_subs_new                         false
% 3.46/1.00  --inst_eq_res_simp                      false
% 3.46/1.00  --inst_subs_given                       false
% 3.46/1.00  --inst_orphan_elimination               true
% 3.46/1.00  --inst_learning_loop_flag               true
% 3.46/1.00  --inst_learning_start                   3000
% 3.46/1.00  --inst_learning_factor                  2
% 3.46/1.00  --inst_start_prop_sim_after_learn       3
% 3.46/1.00  --inst_sel_renew                        solver
% 3.46/1.00  --inst_lit_activity_flag                true
% 3.46/1.00  --inst_restr_to_given                   false
% 3.46/1.00  --inst_activity_threshold               500
% 3.46/1.00  --inst_out_proof                        true
% 3.46/1.00  
% 3.46/1.00  ------ Resolution Options
% 3.46/1.00  
% 3.46/1.00  --resolution_flag                       false
% 3.46/1.00  --res_lit_sel                           adaptive
% 3.46/1.00  --res_lit_sel_side                      none
% 3.46/1.00  --res_ordering                          kbo
% 3.46/1.00  --res_to_prop_solver                    active
% 3.46/1.00  --res_prop_simpl_new                    false
% 3.46/1.00  --res_prop_simpl_given                  true
% 3.46/1.00  --res_passive_queue_type                priority_queues
% 3.46/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.46/1.00  --res_passive_queues_freq               [15;5]
% 3.46/1.00  --res_forward_subs                      full
% 3.46/1.00  --res_backward_subs                     full
% 3.46/1.00  --res_forward_subs_resolution           true
% 3.46/1.00  --res_backward_subs_resolution          true
% 3.46/1.00  --res_orphan_elimination                true
% 3.46/1.00  --res_time_limit                        2.
% 3.46/1.00  --res_out_proof                         true
% 3.46/1.00  
% 3.46/1.00  ------ Superposition Options
% 3.46/1.00  
% 3.46/1.00  --superposition_flag                    true
% 3.46/1.00  --sup_passive_queue_type                priority_queues
% 3.46/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.46/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.46/1.00  --demod_completeness_check              fast
% 3.46/1.00  --demod_use_ground                      true
% 3.46/1.00  --sup_to_prop_solver                    passive
% 3.46/1.00  --sup_prop_simpl_new                    true
% 3.46/1.00  --sup_prop_simpl_given                  true
% 3.46/1.00  --sup_fun_splitting                     true
% 3.46/1.00  --sup_smt_interval                      50000
% 3.46/1.00  
% 3.46/1.00  ------ Superposition Simplification Setup
% 3.46/1.00  
% 3.46/1.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.46/1.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.46/1.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.46/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.46/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.46/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.46/1.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.46/1.00  --sup_immed_triv                        [TrivRules]
% 3.46/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.46/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.46/1.00  --sup_immed_bw_main                     []
% 3.46/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.46/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.46/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.46/1.00  --sup_input_bw                          []
% 3.46/1.00  
% 3.46/1.00  ------ Combination Options
% 3.46/1.00  
% 3.46/1.00  --comb_res_mult                         3
% 3.46/1.00  --comb_sup_mult                         2
% 3.46/1.00  --comb_inst_mult                        10
% 3.46/1.00  
% 3.46/1.00  ------ Debug Options
% 3.46/1.00  
% 3.46/1.00  --dbg_backtrace                         false
% 3.46/1.00  --dbg_dump_prop_clauses                 false
% 3.46/1.00  --dbg_dump_prop_clauses_file            -
% 3.46/1.00  --dbg_out_stat                          false
% 3.46/1.00  
% 3.46/1.00  
% 3.46/1.00  
% 3.46/1.00  
% 3.46/1.00  ------ Proving...
% 3.46/1.00  
% 3.46/1.00  
% 3.46/1.00  % SZS status Theorem for theBenchmark.p
% 3.46/1.00  
% 3.46/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.46/1.00  
% 3.46/1.00  fof(f12,axiom,(
% 3.46/1.00    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 3.46/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.46/1.00  
% 3.46/1.00  fof(f20,plain,(
% 3.46/1.00    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 3.46/1.00    inference(ennf_transformation,[],[f12])).
% 3.46/1.00  
% 3.46/1.00  fof(f21,plain,(
% 3.46/1.00    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 3.46/1.00    inference(flattening,[],[f20])).
% 3.46/1.00  
% 3.46/1.00  fof(f64,plain,(
% 3.46/1.00    ( ! [X0,X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.46/1.00    inference(cnf_transformation,[],[f21])).
% 3.46/1.00  
% 3.46/1.00  fof(f14,conjecture,(
% 3.46/1.00    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 3.46/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.46/1.00  
% 3.46/1.00  fof(f15,negated_conjecture,(
% 3.46/1.00    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 3.46/1.00    inference(negated_conjecture,[],[f14])).
% 3.46/1.00  
% 3.46/1.00  fof(f23,plain,(
% 3.46/1.00    ? [X0] : (? [X1] : ((r2_hidden(X0,k1_ordinal1(X1)) <~> r1_ordinal1(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 3.46/1.00    inference(ennf_transformation,[],[f15])).
% 3.46/1.00  
% 3.46/1.00  fof(f36,plain,(
% 3.46/1.00    ? [X0] : (? [X1] : (((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1)))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 3.46/1.00    inference(nnf_transformation,[],[f23])).
% 3.46/1.00  
% 3.46/1.00  fof(f37,plain,(
% 3.46/1.00    ? [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 3.46/1.00    inference(flattening,[],[f36])).
% 3.46/1.00  
% 3.46/1.00  fof(f39,plain,(
% 3.46/1.00    ( ! [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) => ((~r1_ordinal1(X0,sK2) | ~r2_hidden(X0,k1_ordinal1(sK2))) & (r1_ordinal1(X0,sK2) | r2_hidden(X0,k1_ordinal1(sK2))) & v3_ordinal1(sK2))) )),
% 3.46/1.00    introduced(choice_axiom,[])).
% 3.46/1.00  
% 3.46/1.00  fof(f38,plain,(
% 3.46/1.00    ? [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : ((~r1_ordinal1(sK1,X1) | ~r2_hidden(sK1,k1_ordinal1(X1))) & (r1_ordinal1(sK1,X1) | r2_hidden(sK1,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(sK1))),
% 3.46/1.00    introduced(choice_axiom,[])).
% 3.46/1.00  
% 3.46/1.00  fof(f40,plain,(
% 3.46/1.00    ((~r1_ordinal1(sK1,sK2) | ~r2_hidden(sK1,k1_ordinal1(sK2))) & (r1_ordinal1(sK1,sK2) | r2_hidden(sK1,k1_ordinal1(sK2))) & v3_ordinal1(sK2)) & v3_ordinal1(sK1)),
% 3.46/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f37,f39,f38])).
% 3.46/1.00  
% 3.46/1.00  fof(f69,plain,(
% 3.46/1.00    ~r1_ordinal1(sK1,sK2) | ~r2_hidden(sK1,k1_ordinal1(sK2))),
% 3.46/1.00    inference(cnf_transformation,[],[f40])).
% 3.46/1.00  
% 3.46/1.00  fof(f9,axiom,(
% 3.46/1.00    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0)),
% 3.46/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.46/1.00  
% 3.46/1.00  fof(f58,plain,(
% 3.46/1.00    ( ! [X0] : (k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0)) )),
% 3.46/1.00    inference(cnf_transformation,[],[f9])).
% 3.46/1.00  
% 3.46/1.00  fof(f6,axiom,(
% 3.46/1.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.46/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.46/1.00  
% 3.46/1.00  fof(f53,plain,(
% 3.46/1.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.46/1.00    inference(cnf_transformation,[],[f6])).
% 3.46/1.00  
% 3.46/1.00  fof(f70,plain,(
% 3.46/1.00    ( ! [X0] : (k2_xboole_0(X0,k2_tarski(X0,X0)) = k1_ordinal1(X0)) )),
% 3.46/1.00    inference(definition_unfolding,[],[f58,f53])).
% 3.46/1.00  
% 3.46/1.00  fof(f75,plain,(
% 3.46/1.00    ~r1_ordinal1(sK1,sK2) | ~r2_hidden(sK1,k2_xboole_0(sK2,k2_tarski(sK2,sK2)))),
% 3.46/1.00    inference(definition_unfolding,[],[f69,f70])).
% 3.46/1.00  
% 3.46/1.00  fof(f66,plain,(
% 3.46/1.00    v3_ordinal1(sK1)),
% 3.46/1.00    inference(cnf_transformation,[],[f40])).
% 3.46/1.00  
% 3.46/1.00  fof(f67,plain,(
% 3.46/1.00    v3_ordinal1(sK2)),
% 3.46/1.00    inference(cnf_transformation,[],[f40])).
% 3.46/1.00  
% 3.46/1.00  fof(f10,axiom,(
% 3.46/1.00    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 3.46/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.46/1.00  
% 3.46/1.00  fof(f18,plain,(
% 3.46/1.00    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 3.46/1.00    inference(ennf_transformation,[],[f10])).
% 3.46/1.00  
% 3.46/1.00  fof(f19,plain,(
% 3.46/1.00    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 3.46/1.00    inference(flattening,[],[f18])).
% 3.46/1.00  
% 3.46/1.00  fof(f33,plain,(
% 3.46/1.00    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 3.46/1.00    inference(nnf_transformation,[],[f19])).
% 3.46/1.00  
% 3.46/1.00  fof(f59,plain,(
% 3.46/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.46/1.00    inference(cnf_transformation,[],[f33])).
% 3.46/1.00  
% 3.46/1.00  fof(f68,plain,(
% 3.46/1.00    r1_ordinal1(sK1,sK2) | r2_hidden(sK1,k1_ordinal1(sK2))),
% 3.46/1.00    inference(cnf_transformation,[],[f40])).
% 3.46/1.00  
% 3.46/1.00  fof(f76,plain,(
% 3.46/1.00    r1_ordinal1(sK1,sK2) | r2_hidden(sK1,k2_xboole_0(sK2,k2_tarski(sK2,sK2)))),
% 3.46/1.00    inference(definition_unfolding,[],[f68,f70])).
% 3.46/1.00  
% 3.46/1.00  fof(f13,axiom,(
% 3.46/1.00    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.46/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.46/1.00  
% 3.46/1.00  fof(f22,plain,(
% 3.46/1.00    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.46/1.00    inference(ennf_transformation,[],[f13])).
% 3.46/1.00  
% 3.46/1.00  fof(f65,plain,(
% 3.46/1.00    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.46/1.00    inference(cnf_transformation,[],[f22])).
% 3.46/1.00  
% 3.46/1.00  fof(f11,axiom,(
% 3.46/1.00    ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <=> (X0 = X1 | r2_hidden(X0,X1)))),
% 3.46/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.46/1.00  
% 3.46/1.00  fof(f34,plain,(
% 3.46/1.00    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & ((X0 = X1 | r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 3.46/1.00    inference(nnf_transformation,[],[f11])).
% 3.46/1.00  
% 3.46/1.00  fof(f35,plain,(
% 3.46/1.00    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 3.46/1.00    inference(flattening,[],[f34])).
% 3.46/1.00  
% 3.46/1.00  fof(f61,plain,(
% 3.46/1.00    ( ! [X0,X1] : (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) )),
% 3.46/1.00    inference(cnf_transformation,[],[f35])).
% 3.46/1.00  
% 3.46/1.00  fof(f74,plain,(
% 3.46/1.00    ( ! [X0,X1] : (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k2_xboole_0(X1,k2_tarski(X1,X1)))) )),
% 3.46/1.00    inference(definition_unfolding,[],[f61,f70])).
% 3.46/1.00  
% 3.46/1.00  fof(f63,plain,(
% 3.46/1.00    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | X0 != X1) )),
% 3.46/1.00    inference(cnf_transformation,[],[f35])).
% 3.46/1.00  
% 3.46/1.00  fof(f72,plain,(
% 3.46/1.00    ( ! [X0,X1] : (r2_hidden(X0,k2_xboole_0(X1,k2_tarski(X1,X1))) | X0 != X1) )),
% 3.46/1.00    inference(definition_unfolding,[],[f63,f70])).
% 3.46/1.00  
% 3.46/1.00  fof(f82,plain,(
% 3.46/1.00    ( ! [X1] : (r2_hidden(X1,k2_xboole_0(X1,k2_tarski(X1,X1)))) )),
% 3.46/1.00    inference(equality_resolution,[],[f72])).
% 3.46/1.00  
% 3.46/1.00  fof(f4,axiom,(
% 3.46/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.46/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.46/1.00  
% 3.46/1.00  fof(f29,plain,(
% 3.46/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.46/1.00    inference(nnf_transformation,[],[f4])).
% 3.46/1.00  
% 3.46/1.00  fof(f30,plain,(
% 3.46/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.46/1.00    inference(flattening,[],[f29])).
% 3.46/1.00  
% 3.46/1.00  fof(f49,plain,(
% 3.46/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.46/1.00    inference(cnf_transformation,[],[f30])).
% 3.46/1.00  
% 3.46/1.00  fof(f81,plain,(
% 3.46/1.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.46/1.00    inference(equality_resolution,[],[f49])).
% 3.46/1.00  
% 3.46/1.00  fof(f1,axiom,(
% 3.46/1.00    ! [X0,X1] : (r2_hidden(X0,X1) => ~r2_hidden(X1,X0))),
% 3.46/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.46/1.00  
% 3.46/1.00  fof(f16,plain,(
% 3.46/1.00    ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1))),
% 3.46/1.00    inference(ennf_transformation,[],[f1])).
% 3.46/1.00  
% 3.46/1.00  fof(f41,plain,(
% 3.46/1.00    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.46/1.00    inference(cnf_transformation,[],[f16])).
% 3.46/1.00  
% 3.46/1.00  fof(f51,plain,(
% 3.46/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.46/1.00    inference(cnf_transformation,[],[f30])).
% 3.46/1.00  
% 3.46/1.00  fof(f60,plain,(
% 3.46/1.00    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.46/1.00    inference(cnf_transformation,[],[f33])).
% 3.46/1.00  
% 3.46/1.00  fof(f3,axiom,(
% 3.46/1.00    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 3.46/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.46/1.00  
% 3.46/1.00  fof(f24,plain,(
% 3.46/1.00    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.46/1.00    inference(nnf_transformation,[],[f3])).
% 3.46/1.00  
% 3.46/1.00  fof(f25,plain,(
% 3.46/1.00    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.46/1.00    inference(flattening,[],[f24])).
% 3.46/1.00  
% 3.46/1.00  fof(f26,plain,(
% 3.46/1.00    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.46/1.00    inference(rectify,[],[f25])).
% 3.46/1.00  
% 3.46/1.00  fof(f27,plain,(
% 3.46/1.00    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 3.46/1.00    introduced(choice_axiom,[])).
% 3.46/1.00  
% 3.46/1.00  fof(f28,plain,(
% 3.46/1.00    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.46/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).
% 3.46/1.00  
% 3.46/1.00  fof(f44,plain,(
% 3.46/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 3.46/1.00    inference(cnf_transformation,[],[f28])).
% 3.46/1.00  
% 3.46/1.00  fof(f78,plain,(
% 3.46/1.00    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X0)) )),
% 3.46/1.00    inference(equality_resolution,[],[f44])).
% 3.46/1.00  
% 3.46/1.00  fof(f45,plain,(
% 3.46/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 3.46/1.00    inference(cnf_transformation,[],[f28])).
% 3.46/1.00  
% 3.46/1.00  fof(f77,plain,(
% 3.46/1.00    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 3.46/1.00    inference(equality_resolution,[],[f45])).
% 3.46/1.00  
% 3.46/1.00  fof(f43,plain,(
% 3.46/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 3.46/1.00    inference(cnf_transformation,[],[f28])).
% 3.46/1.00  
% 3.46/1.00  fof(f79,plain,(
% 3.46/1.00    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,k2_xboole_0(X0,X1))) )),
% 3.46/1.00    inference(equality_resolution,[],[f43])).
% 3.46/1.00  
% 3.46/1.00  cnf(c_21,plain,
% 3.46/1.00      ( r1_ordinal1(X0,X1)
% 3.46/1.00      | r2_hidden(X1,X0)
% 3.46/1.00      | ~ v3_ordinal1(X1)
% 3.46/1.00      | ~ v3_ordinal1(X0) ),
% 3.46/1.00      inference(cnf_transformation,[],[f64]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_23,negated_conjecture,
% 3.46/1.00      ( ~ r1_ordinal1(sK1,sK2)
% 3.46/1.00      | ~ r2_hidden(sK1,k2_xboole_0(sK2,k2_tarski(sK2,sK2))) ),
% 3.46/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_203,plain,
% 3.46/1.00      ( ~ r1_ordinal1(sK1,sK2)
% 3.46/1.00      | ~ r2_hidden(sK1,k2_xboole_0(sK2,k2_tarski(sK2,sK2))) ),
% 3.46/1.00      inference(prop_impl,[status(thm)],[c_23]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_352,plain,
% 3.46/1.00      ( r2_hidden(X0,X1)
% 3.46/1.00      | ~ r2_hidden(sK1,k2_xboole_0(sK2,k2_tarski(sK2,sK2)))
% 3.46/1.00      | ~ v3_ordinal1(X1)
% 3.46/1.00      | ~ v3_ordinal1(X0)
% 3.46/1.00      | sK2 != X0
% 3.46/1.00      | sK1 != X1 ),
% 3.46/1.00      inference(resolution_lifted,[status(thm)],[c_21,c_203]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_353,plain,
% 3.46/1.00      ( r2_hidden(sK2,sK1)
% 3.46/1.00      | ~ r2_hidden(sK1,k2_xboole_0(sK2,k2_tarski(sK2,sK2)))
% 3.46/1.00      | ~ v3_ordinal1(sK2)
% 3.46/1.00      | ~ v3_ordinal1(sK1) ),
% 3.46/1.00      inference(unflattening,[status(thm)],[c_352]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_26,negated_conjecture,
% 3.46/1.00      ( v3_ordinal1(sK1) ),
% 3.46/1.00      inference(cnf_transformation,[],[f66]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_25,negated_conjecture,
% 3.46/1.00      ( v3_ordinal1(sK2) ),
% 3.46/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_355,plain,
% 3.46/1.00      ( r2_hidden(sK2,sK1)
% 3.46/1.00      | ~ r2_hidden(sK1,k2_xboole_0(sK2,k2_tarski(sK2,sK2))) ),
% 3.46/1.00      inference(global_propositional_subsumption,
% 3.46/1.00                [status(thm)],
% 3.46/1.00                [c_353,c_26,c_25]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_17,plain,
% 3.46/1.00      ( ~ r1_ordinal1(X0,X1)
% 3.46/1.00      | r1_tarski(X0,X1)
% 3.46/1.00      | ~ v3_ordinal1(X1)
% 3.46/1.00      | ~ v3_ordinal1(X0) ),
% 3.46/1.00      inference(cnf_transformation,[],[f59]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_24,negated_conjecture,
% 3.46/1.00      ( r1_ordinal1(sK1,sK2)
% 3.46/1.00      | r2_hidden(sK1,k2_xboole_0(sK2,k2_tarski(sK2,sK2))) ),
% 3.46/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_205,plain,
% 3.46/1.00      ( r1_ordinal1(sK1,sK2)
% 3.46/1.00      | r2_hidden(sK1,k2_xboole_0(sK2,k2_tarski(sK2,sK2))) ),
% 3.46/1.00      inference(prop_impl,[status(thm)],[c_24]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_380,plain,
% 3.46/1.00      ( r1_tarski(X0,X1)
% 3.46/1.00      | r2_hidden(sK1,k2_xboole_0(sK2,k2_tarski(sK2,sK2)))
% 3.46/1.00      | ~ v3_ordinal1(X0)
% 3.46/1.00      | ~ v3_ordinal1(X1)
% 3.46/1.00      | sK2 != X1
% 3.46/1.00      | sK1 != X0 ),
% 3.46/1.00      inference(resolution_lifted,[status(thm)],[c_17,c_205]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_381,plain,
% 3.46/1.00      ( r1_tarski(sK1,sK2)
% 3.46/1.00      | r2_hidden(sK1,k2_xboole_0(sK2,k2_tarski(sK2,sK2)))
% 3.46/1.00      | ~ v3_ordinal1(sK2)
% 3.46/1.00      | ~ v3_ordinal1(sK1) ),
% 3.46/1.00      inference(unflattening,[status(thm)],[c_380]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_383,plain,
% 3.46/1.00      ( r1_tarski(sK1,sK2)
% 3.46/1.00      | r2_hidden(sK1,k2_xboole_0(sK2,k2_tarski(sK2,sK2))) ),
% 3.46/1.00      inference(global_propositional_subsumption,
% 3.46/1.00                [status(thm)],
% 3.46/1.00                [c_381,c_26,c_25]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_493,plain,
% 3.46/1.00      ( r1_tarski(sK1,sK2)
% 3.46/1.00      | r2_hidden(sK1,k2_xboole_0(sK2,k2_tarski(sK2,sK2))) ),
% 3.46/1.00      inference(prop_impl,[status(thm)],[c_26,c_25,c_381]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_536,plain,
% 3.46/1.00      ( r1_tarski(sK1,sK2) | r2_hidden(sK2,sK1) ),
% 3.46/1.00      inference(bin_hyper_res,[status(thm)],[c_355,c_493]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_1126,plain,
% 3.46/1.00      ( r1_tarski(sK1,sK2) = iProver_top
% 3.46/1.00      | r2_hidden(sK2,sK1) = iProver_top ),
% 3.46/1.00      inference(predicate_to_equality,[status(thm)],[c_536]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_22,plain,
% 3.46/1.00      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X1,X0) ),
% 3.46/1.00      inference(cnf_transformation,[],[f65]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_32,plain,
% 3.46/1.00      ( ~ r1_tarski(sK2,sK2) | ~ r2_hidden(sK2,sK2) ),
% 3.46/1.00      inference(instantiation,[status(thm)],[c_22]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_20,plain,
% 3.46/1.00      ( r2_hidden(X0,X1)
% 3.46/1.00      | ~ r2_hidden(X0,k2_xboole_0(X1,k2_tarski(X1,X1)))
% 3.46/1.00      | X0 = X1 ),
% 3.46/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_38,plain,
% 3.46/1.00      ( ~ r2_hidden(sK2,k2_xboole_0(sK2,k2_tarski(sK2,sK2)))
% 3.46/1.00      | r2_hidden(sK2,sK2)
% 3.46/1.00      | sK2 = sK2 ),
% 3.46/1.00      inference(instantiation,[status(thm)],[c_20]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_18,plain,
% 3.46/1.00      ( r2_hidden(X0,k2_xboole_0(X0,k2_tarski(X0,X0))) ),
% 3.46/1.00      inference(cnf_transformation,[],[f82]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_44,plain,
% 3.46/1.00      ( r2_hidden(sK2,k2_xboole_0(sK2,k2_tarski(sK2,sK2))) ),
% 3.46/1.00      inference(instantiation,[status(thm)],[c_18]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_10,plain,
% 3.46/1.00      ( r1_tarski(X0,X0) ),
% 3.46/1.00      inference(cnf_transformation,[],[f81]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_66,plain,
% 3.46/1.00      ( r1_tarski(sK2,sK2) ),
% 3.46/1.00      inference(instantiation,[status(thm)],[c_10]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_65,plain,
% 3.46/1.00      ( r1_tarski(X0,X0) = iProver_top ),
% 3.46/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_67,plain,
% 3.46/1.00      ( r1_tarski(sK2,sK2) = iProver_top ),
% 3.46/1.00      inference(instantiation,[status(thm)],[c_65]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_385,plain,
% 3.46/1.00      ( r1_tarski(sK1,sK2) = iProver_top
% 3.46/1.00      | r2_hidden(sK1,k2_xboole_0(sK2,k2_tarski(sK2,sK2))) = iProver_top ),
% 3.46/1.00      inference(predicate_to_equality,[status(thm)],[c_383]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_547,plain,
% 3.46/1.00      ( r1_tarski(sK1,sK2) = iProver_top
% 3.46/1.00      | r2_hidden(sK2,sK1) = iProver_top ),
% 3.46/1.00      inference(predicate_to_equality,[status(thm)],[c_536]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_624,plain,
% 3.46/1.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.46/1.00      theory(equality) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_1184,plain,
% 3.46/1.00      ( ~ r1_tarski(X0,X1) | r1_tarski(sK1,sK2) | sK2 != X1 | sK1 != X0 ),
% 3.46/1.00      inference(instantiation,[status(thm)],[c_624]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_1185,plain,
% 3.46/1.00      ( sK2 != X0
% 3.46/1.00      | sK1 != X1
% 3.46/1.00      | r1_tarski(X1,X0) != iProver_top
% 3.46/1.00      | r1_tarski(sK1,sK2) = iProver_top ),
% 3.46/1.00      inference(predicate_to_equality,[status(thm)],[c_1184]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_1187,plain,
% 3.46/1.00      ( sK2 != sK2
% 3.46/1.00      | sK1 != sK2
% 3.46/1.00      | r1_tarski(sK2,sK2) != iProver_top
% 3.46/1.00      | r1_tarski(sK1,sK2) = iProver_top ),
% 3.46/1.00      inference(instantiation,[status(thm)],[c_1185]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_0,plain,
% 3.46/1.00      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X1,X0) ),
% 3.46/1.00      inference(cnf_transformation,[],[f41]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_1191,plain,
% 3.46/1.00      ( ~ r2_hidden(sK2,sK1) | ~ r2_hidden(sK1,sK2) ),
% 3.46/1.00      inference(instantiation,[status(thm)],[c_0]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_1192,plain,
% 3.46/1.00      ( r2_hidden(sK2,sK1) != iProver_top
% 3.46/1.00      | r2_hidden(sK1,sK2) != iProver_top ),
% 3.46/1.00      inference(predicate_to_equality,[status(thm)],[c_1191]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_1230,plain,
% 3.46/1.00      ( r2_hidden(sK1,X0)
% 3.46/1.00      | ~ r2_hidden(sK1,k2_xboole_0(X0,k2_tarski(X0,X0)))
% 3.46/1.00      | sK1 = X0 ),
% 3.46/1.00      inference(instantiation,[status(thm)],[c_20]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_1231,plain,
% 3.46/1.00      ( sK1 = X0
% 3.46/1.00      | r2_hidden(sK1,X0) = iProver_top
% 3.46/1.00      | r2_hidden(sK1,k2_xboole_0(X0,k2_tarski(X0,X0))) != iProver_top ),
% 3.46/1.00      inference(predicate_to_equality,[status(thm)],[c_1230]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_1233,plain,
% 3.46/1.00      ( sK1 = sK2
% 3.46/1.00      | r2_hidden(sK1,k2_xboole_0(sK2,k2_tarski(sK2,sK2))) != iProver_top
% 3.46/1.00      | r2_hidden(sK1,sK2) = iProver_top ),
% 3.46/1.00      inference(instantiation,[status(thm)],[c_1231]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_1547,plain,
% 3.46/1.00      ( r1_tarski(sK1,sK2) = iProver_top ),
% 3.46/1.00      inference(global_propositional_subsumption,
% 3.46/1.00                [status(thm)],
% 3.46/1.00                [c_1126,c_32,c_38,c_44,c_66,c_67,c_385,c_547,c_1187,
% 3.46/1.00                 c_1192,c_1233]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_8,plain,
% 3.46/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 3.46/1.00      inference(cnf_transformation,[],[f51]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_1142,plain,
% 3.46/1.00      ( X0 = X1
% 3.46/1.00      | r1_tarski(X1,X0) != iProver_top
% 3.46/1.00      | r1_tarski(X0,X1) != iProver_top ),
% 3.46/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_3230,plain,
% 3.46/1.00      ( sK2 = sK1 | r1_tarski(sK2,sK1) != iProver_top ),
% 3.46/1.00      inference(superposition,[status(thm)],[c_1547,c_1142]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_27,plain,
% 3.46/1.00      ( v3_ordinal1(sK1) = iProver_top ),
% 3.46/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_28,plain,
% 3.46/1.00      ( v3_ordinal1(sK2) = iProver_top ),
% 3.46/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_16,plain,
% 3.46/1.00      ( r1_ordinal1(X0,X1)
% 3.46/1.00      | ~ r1_tarski(X0,X1)
% 3.46/1.00      | ~ v3_ordinal1(X1)
% 3.46/1.00      | ~ v3_ordinal1(X0) ),
% 3.46/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_366,plain,
% 3.46/1.00      ( ~ r1_tarski(X0,X1)
% 3.46/1.00      | ~ r2_hidden(sK1,k2_xboole_0(sK2,k2_tarski(sK2,sK2)))
% 3.46/1.00      | ~ v3_ordinal1(X0)
% 3.46/1.00      | ~ v3_ordinal1(X1)
% 3.46/1.00      | sK2 != X1
% 3.46/1.00      | sK1 != X0 ),
% 3.46/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_203]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_367,plain,
% 3.46/1.00      ( ~ r1_tarski(sK1,sK2)
% 3.46/1.00      | ~ r2_hidden(sK1,k2_xboole_0(sK2,k2_tarski(sK2,sK2)))
% 3.46/1.00      | ~ v3_ordinal1(sK2)
% 3.46/1.00      | ~ v3_ordinal1(sK1) ),
% 3.46/1.00      inference(unflattening,[status(thm)],[c_366]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_369,plain,
% 3.46/1.00      ( ~ r1_tarski(sK1,sK2)
% 3.46/1.00      | ~ r2_hidden(sK1,k2_xboole_0(sK2,k2_tarski(sK2,sK2))) ),
% 3.46/1.00      inference(global_propositional_subsumption,
% 3.46/1.00                [status(thm)],
% 3.46/1.00                [c_367,c_26,c_25]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_371,plain,
% 3.46/1.00      ( r1_tarski(sK1,sK2) != iProver_top
% 3.46/1.00      | r2_hidden(sK1,k2_xboole_0(sK2,k2_tarski(sK2,sK2))) != iProver_top ),
% 3.46/1.00      inference(predicate_to_equality,[status(thm)],[c_369]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_6,plain,
% 3.46/1.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,k2_xboole_0(X1,X2)) ),
% 3.46/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_1257,plain,
% 3.46/1.00      ( r2_hidden(sK1,k2_xboole_0(sK2,k2_tarski(sK2,sK2)))
% 3.46/1.00      | ~ r2_hidden(sK1,sK2) ),
% 3.46/1.00      inference(instantiation,[status(thm)],[c_6]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_1258,plain,
% 3.46/1.00      ( r2_hidden(sK1,k2_xboole_0(sK2,k2_tarski(sK2,sK2))) = iProver_top
% 3.46/1.00      | r2_hidden(sK1,sK2) != iProver_top ),
% 3.46/1.00      inference(predicate_to_equality,[status(thm)],[c_1257]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_335,plain,
% 3.46/1.00      ( r1_tarski(X0,X1)
% 3.46/1.00      | r2_hidden(X1,X0)
% 3.46/1.00      | ~ v3_ordinal1(X0)
% 3.46/1.00      | ~ v3_ordinal1(X1) ),
% 3.46/1.00      inference(resolution,[status(thm)],[c_21,c_17]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_1263,plain,
% 3.46/1.00      ( r1_tarski(X0,sK1)
% 3.46/1.00      | r2_hidden(sK1,X0)
% 3.46/1.00      | ~ v3_ordinal1(X0)
% 3.46/1.00      | ~ v3_ordinal1(sK1) ),
% 3.46/1.00      inference(instantiation,[status(thm)],[c_335]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_1264,plain,
% 3.46/1.00      ( r1_tarski(X0,sK1) = iProver_top
% 3.46/1.00      | r2_hidden(sK1,X0) = iProver_top
% 3.46/1.00      | v3_ordinal1(X0) != iProver_top
% 3.46/1.00      | v3_ordinal1(sK1) != iProver_top ),
% 3.46/1.00      inference(predicate_to_equality,[status(thm)],[c_1263]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_1266,plain,
% 3.46/1.00      ( r1_tarski(sK2,sK1) = iProver_top
% 3.46/1.00      | r2_hidden(sK1,sK2) = iProver_top
% 3.46/1.00      | v3_ordinal1(sK2) != iProver_top
% 3.46/1.00      | v3_ordinal1(sK1) != iProver_top ),
% 3.46/1.00      inference(instantiation,[status(thm)],[c_1264]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_6418,plain,
% 3.46/1.00      ( sK2 = sK1 ),
% 3.46/1.00      inference(global_propositional_subsumption,
% 3.46/1.00                [status(thm)],
% 3.46/1.00                [c_3230,c_27,c_28,c_32,c_38,c_44,c_66,c_67,c_371,c_385,
% 3.46/1.00                 c_547,c_1187,c_1192,c_1233,c_1258,c_1266]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_5,plain,
% 3.46/1.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,k2_xboole_0(X2,X1)) ),
% 3.46/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_1145,plain,
% 3.46/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.46/1.00      | r2_hidden(X0,k2_xboole_0(X2,X1)) = iProver_top ),
% 3.46/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_491,plain,
% 3.46/1.00      ( ~ r1_tarski(sK1,sK2)
% 3.46/1.00      | ~ r2_hidden(sK1,k2_xboole_0(sK2,k2_tarski(sK2,sK2))) ),
% 3.46/1.00      inference(prop_impl,[status(thm)],[c_26,c_25,c_367]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_1128,plain,
% 3.46/1.00      ( r1_tarski(sK1,sK2) != iProver_top
% 3.46/1.00      | r2_hidden(sK1,k2_xboole_0(sK2,k2_tarski(sK2,sK2))) != iProver_top ),
% 3.46/1.00      inference(predicate_to_equality,[status(thm)],[c_491]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_2850,plain,
% 3.46/1.00      ( r2_hidden(sK1,k2_xboole_0(sK2,k2_tarski(sK2,sK2))) != iProver_top ),
% 3.46/1.00      inference(global_propositional_subsumption,
% 3.46/1.00                [status(thm)],
% 3.46/1.00                [c_1128,c_32,c_38,c_44,c_66,c_67,c_371,c_385,c_547,
% 3.46/1.00                 c_1187,c_1192,c_1233]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_2854,plain,
% 3.46/1.00      ( r2_hidden(sK1,k2_tarski(sK2,sK2)) != iProver_top ),
% 3.46/1.00      inference(superposition,[status(thm)],[c_1145,c_2850]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_6420,plain,
% 3.46/1.00      ( r2_hidden(sK1,k2_tarski(sK1,sK1)) != iProver_top ),
% 3.46/1.00      inference(demodulation,[status(thm)],[c_6418,c_2854]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_1642,plain,
% 3.46/1.00      ( ~ r2_hidden(sK1,sK1) ),
% 3.46/1.00      inference(instantiation,[status(thm)],[c_0]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_1643,plain,
% 3.46/1.00      ( r2_hidden(sK1,sK1) != iProver_top ),
% 3.46/1.00      inference(predicate_to_equality,[status(thm)],[c_1642]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_7,plain,
% 3.46/1.00      ( r2_hidden(X0,X1)
% 3.46/1.00      | r2_hidden(X0,X2)
% 3.46/1.00      | ~ r2_hidden(X0,k2_xboole_0(X2,X1)) ),
% 3.46/1.00      inference(cnf_transformation,[],[f79]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_1459,plain,
% 3.46/1.00      ( r2_hidden(X0,X0)
% 3.46/1.00      | r2_hidden(X0,k2_tarski(X0,X0))
% 3.46/1.00      | ~ r2_hidden(X0,k2_xboole_0(X0,k2_tarski(X0,X0))) ),
% 3.46/1.00      inference(instantiation,[status(thm)],[c_7]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_1621,plain,
% 3.46/1.00      ( r2_hidden(sK1,k2_tarski(sK1,sK1))
% 3.46/1.00      | ~ r2_hidden(sK1,k2_xboole_0(sK1,k2_tarski(sK1,sK1)))
% 3.46/1.00      | r2_hidden(sK1,sK1) ),
% 3.46/1.00      inference(instantiation,[status(thm)],[c_1459]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_1623,plain,
% 3.46/1.00      ( r2_hidden(sK1,k2_tarski(sK1,sK1)) = iProver_top
% 3.46/1.00      | r2_hidden(sK1,k2_xboole_0(sK1,k2_tarski(sK1,sK1))) != iProver_top
% 3.46/1.00      | r2_hidden(sK1,sK1) = iProver_top ),
% 3.46/1.00      inference(predicate_to_equality,[status(thm)],[c_1621]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_1366,plain,
% 3.46/1.00      ( r2_hidden(sK1,k2_xboole_0(sK1,k2_tarski(sK1,sK1))) ),
% 3.46/1.00      inference(instantiation,[status(thm)],[c_18]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(c_1367,plain,
% 3.46/1.00      ( r2_hidden(sK1,k2_xboole_0(sK1,k2_tarski(sK1,sK1))) = iProver_top ),
% 3.46/1.00      inference(predicate_to_equality,[status(thm)],[c_1366]) ).
% 3.46/1.00  
% 3.46/1.00  cnf(contradiction,plain,
% 3.46/1.00      ( $false ),
% 3.46/1.00      inference(minisat,[status(thm)],[c_6420,c_1643,c_1623,c_1367]) ).
% 3.46/1.00  
% 3.46/1.00  
% 3.46/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.46/1.00  
% 3.46/1.00  ------                               Statistics
% 3.46/1.00  
% 3.46/1.00  ------ General
% 3.46/1.00  
% 3.46/1.00  abstr_ref_over_cycles:                  0
% 3.46/1.00  abstr_ref_under_cycles:                 0
% 3.46/1.00  gc_basic_clause_elim:                   0
% 3.46/1.00  forced_gc_time:                         0
% 3.46/1.00  parsing_time:                           0.009
% 3.46/1.00  unif_index_cands_time:                  0.
% 3.46/1.00  unif_index_add_time:                    0.
% 3.46/1.00  orderings_time:                         0.
% 3.46/1.00  out_proof_time:                         0.009
% 3.46/1.00  total_time:                             0.227
% 3.46/1.00  num_of_symbols:                         40
% 3.46/1.00  num_of_terms:                           8478
% 3.46/1.00  
% 3.46/1.00  ------ Preprocessing
% 3.46/1.00  
% 3.46/1.00  num_of_splits:                          0
% 3.46/1.00  num_of_split_atoms:                     0
% 3.46/1.00  num_of_reused_defs:                     0
% 3.46/1.00  num_eq_ax_congr_red:                    9
% 3.46/1.00  num_of_sem_filtered_clauses:            1
% 3.46/1.00  num_of_subtypes:                        0
% 3.46/1.00  monotx_restored_types:                  0
% 3.46/1.00  sat_num_of_epr_types:                   0
% 3.46/1.00  sat_num_of_non_cyclic_types:            0
% 3.46/1.00  sat_guarded_non_collapsed_types:        0
% 3.46/1.00  num_pure_diseq_elim:                    0
% 3.46/1.00  simp_replaced_by:                       0
% 3.46/1.00  res_preprocessed:                       116
% 3.46/1.00  prep_upred:                             0
% 3.46/1.00  prep_unflattend:                        6
% 3.46/1.00  smt_new_axioms:                         0
% 3.46/1.00  pred_elim_cands:                        3
% 3.46/1.00  pred_elim:                              1
% 3.46/1.00  pred_elim_cl:                           1
% 3.46/1.00  pred_elim_cycles:                       3
% 3.46/1.00  merged_defs:                            8
% 3.46/1.00  merged_defs_ncl:                        0
% 3.46/1.00  bin_hyper_res:                          9
% 3.46/1.00  prep_cycles:                            4
% 3.46/1.00  pred_elim_time:                         0.001
% 3.46/1.00  splitting_time:                         0.
% 3.46/1.00  sem_filter_time:                        0.
% 3.46/1.00  monotx_time:                            0.
% 3.46/1.00  subtype_inf_time:                       0.
% 3.46/1.00  
% 3.46/1.00  ------ Problem properties
% 3.46/1.00  
% 3.46/1.00  clauses:                                25
% 3.46/1.00  conjectures:                            2
% 3.46/1.00  epr:                                    8
% 3.46/1.00  horn:                                   19
% 3.46/1.00  ground:                                 5
% 3.46/1.00  unary:                                  6
% 3.46/1.00  binary:                                 11
% 3.46/1.00  lits:                                   54
% 3.46/1.00  lits_eq:                                7
% 3.46/1.00  fd_pure:                                0
% 3.46/1.00  fd_pseudo:                              0
% 3.46/1.00  fd_cond:                                0
% 3.46/1.00  fd_pseudo_cond:                         5
% 3.46/1.00  ac_symbols:                             0
% 3.46/1.00  
% 3.46/1.00  ------ Propositional Solver
% 3.46/1.00  
% 3.46/1.00  prop_solver_calls:                      30
% 3.46/1.00  prop_fast_solver_calls:                 625
% 3.46/1.00  smt_solver_calls:                       0
% 3.46/1.00  smt_fast_solver_calls:                  0
% 3.46/1.00  prop_num_of_clauses:                    2550
% 3.46/1.00  prop_preprocess_simplified:             9164
% 3.46/1.00  prop_fo_subsumed:                       9
% 3.46/1.00  prop_solver_time:                       0.
% 3.46/1.00  smt_solver_time:                        0.
% 3.46/1.00  smt_fast_solver_time:                   0.
% 3.46/1.00  prop_fast_solver_time:                  0.
% 3.46/1.00  prop_unsat_core_time:                   0.
% 3.46/1.00  
% 3.46/1.00  ------ QBF
% 3.46/1.00  
% 3.46/1.00  qbf_q_res:                              0
% 3.46/1.00  qbf_num_tautologies:                    0
% 3.46/1.00  qbf_prep_cycles:                        0
% 3.46/1.00  
% 3.46/1.00  ------ BMC1
% 3.46/1.00  
% 3.46/1.00  bmc1_current_bound:                     -1
% 3.46/1.00  bmc1_last_solved_bound:                 -1
% 3.46/1.00  bmc1_unsat_core_size:                   -1
% 3.46/1.00  bmc1_unsat_core_parents_size:           -1
% 3.46/1.00  bmc1_merge_next_fun:                    0
% 3.46/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.46/1.00  
% 3.46/1.00  ------ Instantiation
% 3.46/1.00  
% 3.46/1.00  inst_num_of_clauses:                    722
% 3.46/1.00  inst_num_in_passive:                    524
% 3.46/1.00  inst_num_in_active:                     198
% 3.46/1.00  inst_num_in_unprocessed:                1
% 3.46/1.00  inst_num_of_loops:                      230
% 3.46/1.00  inst_num_of_learning_restarts:          0
% 3.46/1.00  inst_num_moves_active_passive:          29
% 3.46/1.00  inst_lit_activity:                      0
% 3.46/1.00  inst_lit_activity_moves:                0
% 3.46/1.00  inst_num_tautologies:                   0
% 3.46/1.00  inst_num_prop_implied:                  0
% 3.46/1.00  inst_num_existing_simplified:           0
% 3.46/1.00  inst_num_eq_res_simplified:             0
% 3.46/1.00  inst_num_child_elim:                    0
% 3.46/1.00  inst_num_of_dismatching_blockings:      637
% 3.46/1.00  inst_num_of_non_proper_insts:           894
% 3.46/1.00  inst_num_of_duplicates:                 0
% 3.46/1.00  inst_inst_num_from_inst_to_res:         0
% 3.46/1.00  inst_dismatching_checking_time:         0.
% 3.46/1.00  
% 3.46/1.00  ------ Resolution
% 3.46/1.00  
% 3.46/1.00  res_num_of_clauses:                     0
% 3.46/1.00  res_num_in_passive:                     0
% 3.46/1.00  res_num_in_active:                      0
% 3.46/1.00  res_num_of_loops:                       120
% 3.46/1.00  res_forward_subset_subsumed:            56
% 3.46/1.00  res_backward_subset_subsumed:           4
% 3.46/1.00  res_forward_subsumed:                   0
% 3.46/1.00  res_backward_subsumed:                  0
% 3.46/1.00  res_forward_subsumption_resolution:     0
% 3.46/1.00  res_backward_subsumption_resolution:    0
% 3.46/1.00  res_clause_to_clause_subsumption:       501
% 3.46/1.00  res_orphan_elimination:                 0
% 3.46/1.00  res_tautology_del:                      24
% 3.46/1.00  res_num_eq_res_simplified:              0
% 3.46/1.00  res_num_sel_changes:                    0
% 3.46/1.00  res_moves_from_active_to_pass:          0
% 3.46/1.00  
% 3.46/1.00  ------ Superposition
% 3.46/1.00  
% 3.46/1.00  sup_time_total:                         0.
% 3.46/1.00  sup_time_generating:                    0.
% 3.46/1.00  sup_time_sim_full:                      0.
% 3.46/1.00  sup_time_sim_immed:                     0.
% 3.46/1.00  
% 3.46/1.00  sup_num_of_clauses:                     83
% 3.46/1.00  sup_num_in_active:                      37
% 3.46/1.00  sup_num_in_passive:                     46
% 3.46/1.00  sup_num_of_loops:                       44
% 3.46/1.00  sup_fw_superposition:                   93
% 3.46/1.00  sup_bw_superposition:                   35
% 3.46/1.00  sup_immediate_simplified:               7
% 3.46/1.00  sup_given_eliminated:                   0
% 3.46/1.00  comparisons_done:                       0
% 3.46/1.00  comparisons_avoided:                    0
% 3.46/1.00  
% 3.46/1.00  ------ Simplifications
% 3.46/1.00  
% 3.46/1.00  
% 3.46/1.00  sim_fw_subset_subsumed:                 1
% 3.46/1.00  sim_bw_subset_subsumed:                 1
% 3.46/1.00  sim_fw_subsumed:                        8
% 3.46/1.00  sim_bw_subsumed:                        1
% 3.46/1.00  sim_fw_subsumption_res:                 0
% 3.46/1.00  sim_bw_subsumption_res:                 0
% 3.46/1.00  sim_tautology_del:                      5
% 3.46/1.00  sim_eq_tautology_del:                   3
% 3.46/1.00  sim_eq_res_simp:                        0
% 3.46/1.00  sim_fw_demodulated:                     0
% 3.46/1.00  sim_bw_demodulated:                     6
% 3.46/1.00  sim_light_normalised:                   0
% 3.46/1.00  sim_joinable_taut:                      0
% 3.46/1.00  sim_joinable_simp:                      0
% 3.46/1.00  sim_ac_normalised:                      0
% 3.46/1.00  sim_smt_subsumption:                    0
% 3.46/1.00  
%------------------------------------------------------------------------------
