%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:53:38 EST 2020

% Result     : Theorem 2.19s
% Output     : CNFRefutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 453 expanded)
%              Number of clauses        :   83 ( 125 expanded)
%              Number of leaves         :   16 ( 103 expanded)
%              Depth                    :   18
%              Number of atoms          :  394 (1568 expanded)
%              Number of equality atoms :   99 ( 219 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :   12 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
    <=> ( X0 = X1
        | r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(flattening,[],[f25])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f52,plain,(
    ! [X0] : k2_xboole_0(X0,k2_tarski(X0,X0)) = k1_ordinal1(X0) ),
    inference(definition_unfolding,[],[f38,f37])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_xboole_0(X1,k2_tarski(X1,X1)))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f42,f52])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f22])).

fof(f35,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f12,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
          <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X0,X1)
            <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(X0,X1)
          <~> r1_ordinal1(k1_ordinal1(X0),X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
            | ~ r2_hidden(X0,X1) )
          & ( r1_ordinal1(k1_ordinal1(X0),X1)
            | r2_hidden(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
            | ~ r2_hidden(X0,X1) )
          & ( r1_ordinal1(k1_ordinal1(X0),X1)
            | r2_hidden(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
            | ~ r2_hidden(X0,X1) )
          & ( r1_ordinal1(k1_ordinal1(X0),X1)
            | r2_hidden(X0,X1) )
          & v3_ordinal1(X1) )
     => ( ( ~ r1_ordinal1(k1_ordinal1(X0),sK1)
          | ~ r2_hidden(X0,sK1) )
        & ( r1_ordinal1(k1_ordinal1(X0),sK1)
          | r2_hidden(X0,sK1) )
        & v3_ordinal1(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
              | ~ r2_hidden(X0,X1) )
            & ( r1_ordinal1(k1_ordinal1(X0),X1)
              | r2_hidden(X0,X1) )
            & v3_ordinal1(X1) )
        & v3_ordinal1(X0) )
   => ( ? [X1] :
          ( ( ~ r1_ordinal1(k1_ordinal1(sK0),X1)
            | ~ r2_hidden(sK0,X1) )
          & ( r1_ordinal1(k1_ordinal1(sK0),X1)
            | r2_hidden(sK0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ( ~ r1_ordinal1(k1_ordinal1(sK0),sK1)
      | ~ r2_hidden(sK0,sK1) )
    & ( r1_ordinal1(k1_ordinal1(sK0),sK1)
      | r2_hidden(sK0,sK1) )
    & v3_ordinal1(sK1)
    & v3_ordinal1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f28,f30,f29])).

fof(f48,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f49,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f10,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k1_ordinal1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f46,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f57,plain,(
    ! [X0] :
      ( v3_ordinal1(k2_xboole_0(X0,k2_tarski(X0,X0)))
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f46,f52])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f50,plain,
    ( r1_ordinal1(k1_ordinal1(sK0),sK1)
    | r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f59,plain,
    ( r1_ordinal1(k2_xboole_0(sK0,k2_tarski(sK0,sK0)),sK1)
    | r2_hidden(sK0,sK1) ),
    inference(definition_unfolding,[],[f50,f52])).

fof(f11,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f41,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f55,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k2_xboole_0(X1,k2_tarski(X1,X1))) ) ),
    inference(definition_unfolding,[],[f41,f52])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_xboole_0(X1,k2_tarski(X1,X1)))
      | X0 != X1 ) ),
    inference(definition_unfolding,[],[f43,f52])).

fof(f62,plain,(
    ! [X1] : r2_hidden(X1,k2_xboole_0(X1,k2_tarski(X1,X1))) ),
    inference(equality_resolution,[],[f53])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f61,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f33])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f9,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f51,plain,
    ( ~ r1_ordinal1(k1_ordinal1(sK0),sK1)
    | ~ r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f58,plain,
    ( ~ r1_ordinal1(k2_xboole_0(sK0,k2_tarski(sK0,sK0)),sK1)
    | ~ r2_hidden(sK0,sK1) ),
    inference(definition_unfolding,[],[f51,f52])).

fof(f8,axiom,(
    ! [X0] : k1_ordinal1(X0) != X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : k1_ordinal1(X0) != X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f56,plain,(
    ! [X0] : k2_xboole_0(X0,k2_tarski(X0,X0)) != X0 ),
    inference(definition_unfolding,[],[f44,f52])).

cnf(c_435,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1360,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK1,k2_xboole_0(sK0,k2_tarski(sK0,sK0)))
    | k2_xboole_0(sK0,k2_tarski(sK0,sK0)) != X1
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_435])).

cnf(c_2017,plain,
    ( ~ r1_tarski(X0,k2_xboole_0(sK0,k2_tarski(sK0,sK0)))
    | r1_tarski(sK1,k2_xboole_0(sK0,k2_tarski(sK0,sK0)))
    | k2_xboole_0(sK0,k2_tarski(sK0,sK0)) != k2_xboole_0(sK0,k2_tarski(sK0,sK0))
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_1360])).

cnf(c_2020,plain,
    ( r1_tarski(sK1,k2_xboole_0(sK0,k2_tarski(sK0,sK0)))
    | ~ r1_tarski(sK0,k2_xboole_0(sK0,k2_tarski(sK0,sK0)))
    | k2_xboole_0(sK0,k2_tarski(sK0,sK0)) != k2_xboole_0(sK0,k2_tarski(sK0,sK0))
    | sK1 != sK0 ),
    inference(instantiation,[status(thm)],[c_2017])).

cnf(c_433,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_973,plain,
    ( X0 != X1
    | k2_xboole_0(X0,k2_tarski(X0,X0)) != X1
    | k2_xboole_0(X0,k2_tarski(X0,X0)) = X0 ),
    inference(instantiation,[status(thm)],[c_433])).

cnf(c_1393,plain,
    ( X0 != sK1
    | k2_xboole_0(X0,k2_tarski(X0,X0)) = X0
    | k2_xboole_0(X0,k2_tarski(X0,X0)) != sK1 ),
    inference(instantiation,[status(thm)],[c_973])).

cnf(c_1396,plain,
    ( k2_xboole_0(sK0,k2_tarski(sK0,sK0)) != sK1
    | k2_xboole_0(sK0,k2_tarski(sK0,sK0)) = sK0
    | sK0 != sK1 ),
    inference(instantiation,[status(thm)],[c_1393])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X1,k2_tarski(X1,X1))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1277,plain,
    ( r2_hidden(sK1,k2_xboole_0(sK0,k2_tarski(sK0,sK0)))
    | ~ r2_hidden(sK1,sK0) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_1007,plain,
    ( ~ r1_tarski(X0,sK1)
    | ~ r1_tarski(sK1,X0)
    | X0 = sK1 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1274,plain,
    ( ~ r1_tarski(k2_xboole_0(sK0,k2_tarski(sK0,sK0)),sK1)
    | ~ r1_tarski(sK1,k2_xboole_0(sK0,k2_tarski(sK0,sK0)))
    | k2_xboole_0(sK0,k2_tarski(sK0,sK0)) = sK1 ),
    inference(instantiation,[status(thm)],[c_1007])).

cnf(c_17,negated_conjecture,
    ( v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_16,negated_conjecture,
    ( v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_12,plain,
    ( ~ v3_ordinal1(X0)
    | v3_ordinal1(k2_xboole_0(X0,k2_tarski(X0,X0))) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_26,plain,
    ( v3_ordinal1(k2_xboole_0(sK0,k2_tarski(sK0,sK0)))
    | ~ v3_ordinal1(sK0) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_6,plain,
    ( ~ r1_ordinal1(X0,X1)
    | r1_tarski(X0,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_15,negated_conjecture,
    ( r1_ordinal1(k2_xboole_0(sK0,k2_tarski(sK0,sK0)),sK1)
    | r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_135,plain,
    ( r2_hidden(sK0,sK1)
    | r1_ordinal1(k2_xboole_0(sK0,k2_tarski(sK0,sK0)),sK1) ),
    inference(prop_impl,[status(thm)],[c_15])).

cnf(c_136,plain,
    ( r1_ordinal1(k2_xboole_0(sK0,k2_tarski(sK0,sK0)),sK1)
    | r2_hidden(sK0,sK1) ),
    inference(renaming,[status(thm)],[c_135])).

cnf(c_267,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK0,sK1)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1)
    | k2_xboole_0(sK0,k2_tarski(sK0,sK0)) != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_136])).

cnf(c_268,plain,
    ( r1_tarski(k2_xboole_0(sK0,k2_tarski(sK0,sK0)),sK1)
    | r2_hidden(sK0,sK1)
    | ~ v3_ordinal1(k2_xboole_0(sK0,k2_tarski(sK0,sK0)))
    | ~ v3_ordinal1(sK1) ),
    inference(unflattening,[status(thm)],[c_267])).

cnf(c_349,plain,
    ( r2_hidden(sK0,sK1)
    | r1_tarski(k2_xboole_0(sK0,k2_tarski(sK0,sK0)),sK1) ),
    inference(prop_impl,[status(thm)],[c_17,c_16,c_26,c_268])).

cnf(c_350,plain,
    ( r1_tarski(k2_xboole_0(sK0,k2_tarski(sK0,sK0)),sK1)
    | r2_hidden(sK0,sK1) ),
    inference(renaming,[status(thm)],[c_349])).

cnf(c_798,plain,
    ( r1_tarski(k2_xboole_0(sK0,k2_tarski(sK0,sK0)),sK1) = iProver_top
    | r2_hidden(sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_350])).

cnf(c_18,plain,
    ( v3_ordinal1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_19,plain,
    ( v3_ordinal1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_13,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_23,plain,
    ( ~ r1_tarski(sK0,sK0)
    | ~ r2_hidden(sK0,sK0) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_25,plain,
    ( v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(k2_xboole_0(X0,k2_tarski(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_27,plain,
    ( v3_ordinal1(k2_xboole_0(sK0,k2_tarski(sK0,sK0))) = iProver_top
    | v3_ordinal1(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_9,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k2_xboole_0(X1,k2_tarski(X1,X1)))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_33,plain,
    ( ~ r2_hidden(sK0,k2_xboole_0(sK0,k2_tarski(sK0,sK0)))
    | r2_hidden(sK0,sK0)
    | sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_7,plain,
    ( r2_hidden(X0,k2_xboole_0(X0,k2_tarski(X0,X0))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_39,plain,
    ( r2_hidden(sK0,k2_xboole_0(sK0,k2_tarski(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_51,plain,
    ( r1_tarski(sK0,sK0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_50,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_52,plain,
    ( r1_tarski(sK0,sK0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_50])).

cnf(c_270,plain,
    ( r1_tarski(k2_xboole_0(sK0,k2_tarski(sK0,sK0)),sK1)
    | r2_hidden(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_268,c_17,c_16,c_26])).

cnf(c_272,plain,
    ( r1_tarski(k2_xboole_0(sK0,k2_tarski(sK0,sK0)),sK1) = iProver_top
    | r2_hidden(sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_270])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_906,plain,
    ( ~ r2_hidden(sK1,sK0)
    | ~ r2_hidden(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_907,plain,
    ( r2_hidden(sK1,sK0) != iProver_top
    | r2_hidden(sK0,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_906])).

cnf(c_926,plain,
    ( ~ r1_tarski(sK1,sK0)
    | ~ r2_hidden(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_927,plain,
    ( r1_tarski(sK1,sK0) != iProver_top
    | r2_hidden(sK0,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_926])).

cnf(c_11,plain,
    ( r1_ordinal1(X0,X1)
    | r2_hidden(X1,X0)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_222,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(X1,X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1) ),
    inference(resolution,[status(thm)],[c_11,c_6])).

cnf(c_938,plain,
    ( r1_tarski(k2_xboole_0(sK0,k2_tarski(sK0,sK0)),sK1)
    | r2_hidden(sK1,k2_xboole_0(sK0,k2_tarski(sK0,sK0)))
    | ~ v3_ordinal1(k2_xboole_0(sK0,k2_tarski(sK0,sK0)))
    | ~ v3_ordinal1(sK1) ),
    inference(instantiation,[status(thm)],[c_222])).

cnf(c_939,plain,
    ( r1_tarski(k2_xboole_0(sK0,k2_tarski(sK0,sK0)),sK1) = iProver_top
    | r2_hidden(sK1,k2_xboole_0(sK0,k2_tarski(sK0,sK0))) = iProver_top
    | v3_ordinal1(k2_xboole_0(sK0,k2_tarski(sK0,sK0))) != iProver_top
    | v3_ordinal1(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_938])).

cnf(c_994,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK1,sK0)
    | sK1 != X0
    | sK0 != X1 ),
    inference(instantiation,[status(thm)],[c_435])).

cnf(c_995,plain,
    ( sK1 != X0
    | sK0 != X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_994])).

cnf(c_997,plain,
    ( sK1 != sK0
    | sK0 != sK0
    | r1_tarski(sK1,sK0) = iProver_top
    | r1_tarski(sK0,sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_995])).

cnf(c_1077,plain,
    ( r2_hidden(sK1,X0)
    | ~ r2_hidden(sK1,k2_xboole_0(X0,k2_tarski(X0,X0)))
    | sK1 = X0 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1078,plain,
    ( sK1 = X0
    | r2_hidden(sK1,X0) = iProver_top
    | r2_hidden(sK1,k2_xboole_0(X0,k2_tarski(X0,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1077])).

cnf(c_1080,plain,
    ( sK1 = sK0
    | r2_hidden(sK1,k2_xboole_0(sK0,k2_tarski(sK0,sK0))) != iProver_top
    | r2_hidden(sK1,sK0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1078])).

cnf(c_1241,plain,
    ( r1_tarski(k2_xboole_0(sK0,k2_tarski(sK0,sK0)),sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_798,c_18,c_19,c_23,c_27,c_33,c_39,c_51,c_52,c_272,c_907,c_927,c_939,c_997,c_1080])).

cnf(c_1243,plain,
    ( r1_tarski(k2_xboole_0(sK0,k2_tarski(sK0,sK0)),sK1) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1241])).

cnf(c_1204,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,k2_tarski(X0,X0)))
    | r2_hidden(k2_xboole_0(X0,k2_tarski(X0,X0)),X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(k2_xboole_0(X0,k2_tarski(X0,X0))) ),
    inference(instantiation,[status(thm)],[c_222])).

cnf(c_1206,plain,
    ( r1_tarski(sK0,k2_xboole_0(sK0,k2_tarski(sK0,sK0)))
    | r2_hidden(k2_xboole_0(sK0,k2_tarski(sK0,sK0)),sK0)
    | ~ v3_ordinal1(k2_xboole_0(sK0,k2_tarski(sK0,sK0)))
    | ~ v3_ordinal1(sK0) ),
    inference(instantiation,[status(thm)],[c_1204])).

cnf(c_432,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1171,plain,
    ( k2_xboole_0(X0,k2_tarski(X0,X0)) = k2_xboole_0(X0,k2_tarski(X0,X0)) ),
    inference(instantiation,[status(thm)],[c_432])).

cnf(c_1173,plain,
    ( k2_xboole_0(sK0,k2_tarski(sK0,sK0)) = k2_xboole_0(sK0,k2_tarski(sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_1171])).

cnf(c_1072,plain,
    ( ~ r1_tarski(X0,sK1)
    | ~ r1_tarski(sK1,X0)
    | sK1 = X0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1074,plain,
    ( ~ r1_tarski(sK1,sK0)
    | ~ r1_tarski(sK0,sK1)
    | sK1 = sK0 ),
    inference(instantiation,[status(thm)],[c_1072])).

cnf(c_1053,plain,
    ( r1_tarski(X0,sK1)
    | r2_hidden(sK1,X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(sK1) ),
    inference(instantiation,[status(thm)],[c_222])).

cnf(c_1055,plain,
    ( r1_tarski(sK0,sK1)
    | r2_hidden(sK1,sK0)
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK0) ),
    inference(instantiation,[status(thm)],[c_1053])).

cnf(c_1009,plain,
    ( ~ r1_tarski(sK1,sK0)
    | ~ r1_tarski(sK0,sK1)
    | sK0 = sK1 ),
    inference(instantiation,[status(thm)],[c_1007])).

cnf(c_991,plain,
    ( r1_tarski(sK1,sK0)
    | r2_hidden(sK0,sK1)
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK0) ),
    inference(instantiation,[status(thm)],[c_222])).

cnf(c_929,plain,
    ( ~ r1_tarski(k2_xboole_0(sK0,k2_tarski(sK0,sK0)),sK1)
    | ~ r2_hidden(sK1,k2_xboole_0(sK0,k2_tarski(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_912,plain,
    ( ~ r2_hidden(X0,k2_xboole_0(X0,k2_tarski(X0,X0)))
    | ~ r2_hidden(k2_xboole_0(X0,k2_tarski(X0,X0)),X0) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_914,plain,
    ( ~ r2_hidden(k2_xboole_0(sK0,k2_tarski(sK0,sK0)),sK0)
    | ~ r2_hidden(sK0,k2_xboole_0(sK0,k2_tarski(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_912])).

cnf(c_5,plain,
    ( r1_ordinal1(X0,X1)
    | ~ r1_tarski(X0,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_14,negated_conjecture,
    ( ~ r1_ordinal1(k2_xboole_0(sK0,k2_tarski(sK0,sK0)),sK1)
    | ~ r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_133,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ r1_ordinal1(k2_xboole_0(sK0,k2_tarski(sK0,sK0)),sK1) ),
    inference(prop_impl,[status(thm)],[c_14])).

cnf(c_134,plain,
    ( ~ r1_ordinal1(k2_xboole_0(sK0,k2_tarski(sK0,sK0)),sK1)
    | ~ r2_hidden(sK0,sK1) ),
    inference(renaming,[status(thm)],[c_133])).

cnf(c_253,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(sK0,sK1)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1)
    | k2_xboole_0(sK0,k2_tarski(sK0,sK0)) != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_134])).

cnf(c_254,plain,
    ( ~ r1_tarski(k2_xboole_0(sK0,k2_tarski(sK0,sK0)),sK1)
    | ~ r2_hidden(sK0,sK1)
    | ~ v3_ordinal1(k2_xboole_0(sK0,k2_tarski(sK0,sK0)))
    | ~ v3_ordinal1(sK1) ),
    inference(unflattening,[status(thm)],[c_253])).

cnf(c_256,plain,
    ( ~ r1_tarski(k2_xboole_0(sK0,k2_tarski(sK0,sK0)),sK1)
    | ~ r2_hidden(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_254,c_17,c_16,c_26])).

cnf(c_10,plain,
    ( k2_xboole_0(X0,k2_tarski(X0,X0)) != X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_31,plain,
    ( k2_xboole_0(sK0,k2_tarski(sK0,sK0)) != sK0 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2020,c_1396,c_1277,c_1274,c_1243,c_1206,c_1173,c_1074,c_1055,c_1009,c_991,c_929,c_914,c_256,c_39,c_31,c_26,c_16,c_17])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:06:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.19/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/0.97  
% 2.19/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.19/0.97  
% 2.19/0.97  ------  iProver source info
% 2.19/0.97  
% 2.19/0.97  git: date: 2020-06-30 10:37:57 +0100
% 2.19/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.19/0.97  git: non_committed_changes: false
% 2.19/0.97  git: last_make_outside_of_git: false
% 2.19/0.97  
% 2.19/0.97  ------ 
% 2.19/0.97  
% 2.19/0.97  ------ Input Options
% 2.19/0.97  
% 2.19/0.97  --out_options                           all
% 2.19/0.97  --tptp_safe_out                         true
% 2.19/0.97  --problem_path                          ""
% 2.19/0.97  --include_path                          ""
% 2.19/0.97  --clausifier                            res/vclausify_rel
% 2.19/0.97  --clausifier_options                    --mode clausify
% 2.19/0.97  --stdin                                 false
% 2.19/0.97  --stats_out                             all
% 2.19/0.97  
% 2.19/0.97  ------ General Options
% 2.19/0.97  
% 2.19/0.97  --fof                                   false
% 2.19/0.97  --time_out_real                         305.
% 2.19/0.97  --time_out_virtual                      -1.
% 2.19/0.97  --symbol_type_check                     false
% 2.19/0.97  --clausify_out                          false
% 2.19/0.97  --sig_cnt_out                           false
% 2.19/0.97  --trig_cnt_out                          false
% 2.19/0.97  --trig_cnt_out_tolerance                1.
% 2.19/0.97  --trig_cnt_out_sk_spl                   false
% 2.19/0.97  --abstr_cl_out                          false
% 2.19/0.97  
% 2.19/0.97  ------ Global Options
% 2.19/0.97  
% 2.19/0.97  --schedule                              default
% 2.19/0.97  --add_important_lit                     false
% 2.19/0.97  --prop_solver_per_cl                    1000
% 2.19/0.97  --min_unsat_core                        false
% 2.19/0.97  --soft_assumptions                      false
% 2.19/0.97  --soft_lemma_size                       3
% 2.19/0.97  --prop_impl_unit_size                   0
% 2.19/0.97  --prop_impl_unit                        []
% 2.19/0.97  --share_sel_clauses                     true
% 2.19/0.97  --reset_solvers                         false
% 2.19/0.97  --bc_imp_inh                            [conj_cone]
% 2.19/0.97  --conj_cone_tolerance                   3.
% 2.19/0.97  --extra_neg_conj                        none
% 2.19/0.97  --large_theory_mode                     true
% 2.19/0.97  --prolific_symb_bound                   200
% 2.19/0.97  --lt_threshold                          2000
% 2.19/0.97  --clause_weak_htbl                      true
% 2.19/0.97  --gc_record_bc_elim                     false
% 2.19/0.97  
% 2.19/0.97  ------ Preprocessing Options
% 2.19/0.97  
% 2.19/0.97  --preprocessing_flag                    true
% 2.19/0.97  --time_out_prep_mult                    0.1
% 2.19/0.97  --splitting_mode                        input
% 2.19/0.97  --splitting_grd                         true
% 2.19/0.97  --splitting_cvd                         false
% 2.19/0.97  --splitting_cvd_svl                     false
% 2.19/0.97  --splitting_nvd                         32
% 2.19/0.97  --sub_typing                            true
% 2.19/0.97  --prep_gs_sim                           true
% 2.19/0.97  --prep_unflatten                        true
% 2.19/0.97  --prep_res_sim                          true
% 2.19/0.97  --prep_upred                            true
% 2.19/0.97  --prep_sem_filter                       exhaustive
% 2.19/0.97  --prep_sem_filter_out                   false
% 2.19/0.97  --pred_elim                             true
% 2.19/0.97  --res_sim_input                         true
% 2.19/0.97  --eq_ax_congr_red                       true
% 2.19/0.97  --pure_diseq_elim                       true
% 2.19/0.97  --brand_transform                       false
% 2.19/0.97  --non_eq_to_eq                          false
% 2.19/0.97  --prep_def_merge                        true
% 2.19/0.97  --prep_def_merge_prop_impl              false
% 2.19/0.97  --prep_def_merge_mbd                    true
% 2.19/0.97  --prep_def_merge_tr_red                 false
% 2.19/0.97  --prep_def_merge_tr_cl                  false
% 2.19/0.97  --smt_preprocessing                     true
% 2.19/0.97  --smt_ac_axioms                         fast
% 2.19/0.97  --preprocessed_out                      false
% 2.19/0.97  --preprocessed_stats                    false
% 2.19/0.97  
% 2.19/0.97  ------ Abstraction refinement Options
% 2.19/0.97  
% 2.19/0.97  --abstr_ref                             []
% 2.19/0.97  --abstr_ref_prep                        false
% 2.19/0.97  --abstr_ref_until_sat                   false
% 2.19/0.97  --abstr_ref_sig_restrict                funpre
% 2.19/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.19/0.97  --abstr_ref_under                       []
% 2.19/0.97  
% 2.19/0.97  ------ SAT Options
% 2.19/0.97  
% 2.19/0.97  --sat_mode                              false
% 2.19/0.97  --sat_fm_restart_options                ""
% 2.19/0.97  --sat_gr_def                            false
% 2.19/0.97  --sat_epr_types                         true
% 2.19/0.97  --sat_non_cyclic_types                  false
% 2.19/0.97  --sat_finite_models                     false
% 2.19/0.97  --sat_fm_lemmas                         false
% 2.19/0.97  --sat_fm_prep                           false
% 2.19/0.97  --sat_fm_uc_incr                        true
% 2.19/0.97  --sat_out_model                         small
% 2.19/0.97  --sat_out_clauses                       false
% 2.19/0.97  
% 2.19/0.97  ------ QBF Options
% 2.19/0.97  
% 2.19/0.97  --qbf_mode                              false
% 2.19/0.97  --qbf_elim_univ                         false
% 2.19/0.97  --qbf_dom_inst                          none
% 2.19/0.97  --qbf_dom_pre_inst                      false
% 2.19/0.97  --qbf_sk_in                             false
% 2.19/0.97  --qbf_pred_elim                         true
% 2.19/0.97  --qbf_split                             512
% 2.19/0.97  
% 2.19/0.97  ------ BMC1 Options
% 2.19/0.97  
% 2.19/0.97  --bmc1_incremental                      false
% 2.19/0.97  --bmc1_axioms                           reachable_all
% 2.19/0.97  --bmc1_min_bound                        0
% 2.19/0.97  --bmc1_max_bound                        -1
% 2.19/0.97  --bmc1_max_bound_default                -1
% 2.19/0.97  --bmc1_symbol_reachability              true
% 2.19/0.97  --bmc1_property_lemmas                  false
% 2.19/0.97  --bmc1_k_induction                      false
% 2.19/0.97  --bmc1_non_equiv_states                 false
% 2.19/0.97  --bmc1_deadlock                         false
% 2.19/0.97  --bmc1_ucm                              false
% 2.19/0.97  --bmc1_add_unsat_core                   none
% 2.19/0.97  --bmc1_unsat_core_children              false
% 2.19/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.19/0.97  --bmc1_out_stat                         full
% 2.19/0.97  --bmc1_ground_init                      false
% 2.19/0.97  --bmc1_pre_inst_next_state              false
% 2.19/0.97  --bmc1_pre_inst_state                   false
% 2.19/0.97  --bmc1_pre_inst_reach_state             false
% 2.19/0.97  --bmc1_out_unsat_core                   false
% 2.19/0.97  --bmc1_aig_witness_out                  false
% 2.19/0.97  --bmc1_verbose                          false
% 2.19/0.97  --bmc1_dump_clauses_tptp                false
% 2.19/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.19/0.97  --bmc1_dump_file                        -
% 2.19/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.19/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.19/0.97  --bmc1_ucm_extend_mode                  1
% 2.19/0.97  --bmc1_ucm_init_mode                    2
% 2.19/0.97  --bmc1_ucm_cone_mode                    none
% 2.19/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.19/0.97  --bmc1_ucm_relax_model                  4
% 2.19/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.19/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.19/0.97  --bmc1_ucm_layered_model                none
% 2.19/0.97  --bmc1_ucm_max_lemma_size               10
% 2.19/0.97  
% 2.19/0.97  ------ AIG Options
% 2.19/0.97  
% 2.19/0.97  --aig_mode                              false
% 2.19/0.97  
% 2.19/0.97  ------ Instantiation Options
% 2.19/0.97  
% 2.19/0.97  --instantiation_flag                    true
% 2.19/0.97  --inst_sos_flag                         false
% 2.19/0.97  --inst_sos_phase                        true
% 2.19/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.19/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.19/0.97  --inst_lit_sel_side                     num_symb
% 2.19/0.97  --inst_solver_per_active                1400
% 2.19/0.97  --inst_solver_calls_frac                1.
% 2.19/0.97  --inst_passive_queue_type               priority_queues
% 2.19/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.19/0.97  --inst_passive_queues_freq              [25;2]
% 2.19/0.97  --inst_dismatching                      true
% 2.19/0.97  --inst_eager_unprocessed_to_passive     true
% 2.19/0.97  --inst_prop_sim_given                   true
% 2.19/0.97  --inst_prop_sim_new                     false
% 2.19/0.97  --inst_subs_new                         false
% 2.19/0.97  --inst_eq_res_simp                      false
% 2.19/0.97  --inst_subs_given                       false
% 2.19/0.97  --inst_orphan_elimination               true
% 2.19/0.97  --inst_learning_loop_flag               true
% 2.19/0.97  --inst_learning_start                   3000
% 2.19/0.97  --inst_learning_factor                  2
% 2.19/0.97  --inst_start_prop_sim_after_learn       3
% 2.19/0.97  --inst_sel_renew                        solver
% 2.19/0.97  --inst_lit_activity_flag                true
% 2.19/0.97  --inst_restr_to_given                   false
% 2.19/0.97  --inst_activity_threshold               500
% 2.19/0.97  --inst_out_proof                        true
% 2.19/0.97  
% 2.19/0.97  ------ Resolution Options
% 2.19/0.97  
% 2.19/0.97  --resolution_flag                       true
% 2.19/0.97  --res_lit_sel                           adaptive
% 2.19/0.97  --res_lit_sel_side                      none
% 2.19/0.97  --res_ordering                          kbo
% 2.19/0.97  --res_to_prop_solver                    active
% 2.19/0.97  --res_prop_simpl_new                    false
% 2.19/0.97  --res_prop_simpl_given                  true
% 2.19/0.97  --res_passive_queue_type                priority_queues
% 2.19/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.19/0.97  --res_passive_queues_freq               [15;5]
% 2.19/0.97  --res_forward_subs                      full
% 2.19/0.97  --res_backward_subs                     full
% 2.19/0.97  --res_forward_subs_resolution           true
% 2.19/0.97  --res_backward_subs_resolution          true
% 2.19/0.97  --res_orphan_elimination                true
% 2.19/0.97  --res_time_limit                        2.
% 2.19/0.97  --res_out_proof                         true
% 2.19/0.97  
% 2.19/0.97  ------ Superposition Options
% 2.19/0.97  
% 2.19/0.97  --superposition_flag                    true
% 2.19/0.97  --sup_passive_queue_type                priority_queues
% 2.19/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.19/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.19/0.97  --demod_completeness_check              fast
% 2.19/0.97  --demod_use_ground                      true
% 2.19/0.97  --sup_to_prop_solver                    passive
% 2.19/0.97  --sup_prop_simpl_new                    true
% 2.19/0.97  --sup_prop_simpl_given                  true
% 2.19/0.97  --sup_fun_splitting                     false
% 2.19/0.97  --sup_smt_interval                      50000
% 2.19/0.97  
% 2.19/0.97  ------ Superposition Simplification Setup
% 2.19/0.97  
% 2.19/0.97  --sup_indices_passive                   []
% 2.19/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.19/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.19/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.19/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.19/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.19/0.97  --sup_full_bw                           [BwDemod]
% 2.19/0.97  --sup_immed_triv                        [TrivRules]
% 2.19/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.19/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.19/0.97  --sup_immed_bw_main                     []
% 2.19/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.19/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.19/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.19/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.19/0.97  
% 2.19/0.97  ------ Combination Options
% 2.19/0.97  
% 2.19/0.97  --comb_res_mult                         3
% 2.19/0.97  --comb_sup_mult                         2
% 2.19/0.97  --comb_inst_mult                        10
% 2.19/0.97  
% 2.19/0.97  ------ Debug Options
% 2.19/0.97  
% 2.19/0.97  --dbg_backtrace                         false
% 2.19/0.97  --dbg_dump_prop_clauses                 false
% 2.19/0.97  --dbg_dump_prop_clauses_file            -
% 2.19/0.97  --dbg_out_stat                          false
% 2.19/0.97  ------ Parsing...
% 2.19/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.19/0.97  
% 2.19/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.19/0.97  
% 2.19/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.19/0.97  
% 2.19/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.19/0.97  ------ Proving...
% 2.19/0.97  ------ Problem Properties 
% 2.19/0.97  
% 2.19/0.97  
% 2.19/0.97  clauses                                 16
% 2.19/0.97  conjectures                             2
% 2.19/0.97  EPR                                     7
% 2.19/0.97  Horn                                    13
% 2.19/0.97  unary                                   6
% 2.19/0.97  binary                                  7
% 2.19/0.97  lits                                    30
% 2.19/0.97  lits eq                                 3
% 2.19/0.97  fd_pure                                 0
% 2.19/0.97  fd_pseudo                               0
% 2.19/0.97  fd_cond                                 0
% 2.19/0.97  fd_pseudo_cond                          2
% 2.19/0.97  AC symbols                              0
% 2.19/0.97  
% 2.19/0.97  ------ Schedule dynamic 5 is on 
% 2.19/0.97  
% 2.19/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.19/0.97  
% 2.19/0.97  
% 2.19/0.97  ------ 
% 2.19/0.97  Current options:
% 2.19/0.97  ------ 
% 2.19/0.97  
% 2.19/0.97  ------ Input Options
% 2.19/0.97  
% 2.19/0.97  --out_options                           all
% 2.19/0.97  --tptp_safe_out                         true
% 2.19/0.97  --problem_path                          ""
% 2.19/0.97  --include_path                          ""
% 2.19/0.97  --clausifier                            res/vclausify_rel
% 2.19/0.97  --clausifier_options                    --mode clausify
% 2.19/0.97  --stdin                                 false
% 2.19/0.97  --stats_out                             all
% 2.19/0.97  
% 2.19/0.97  ------ General Options
% 2.19/0.97  
% 2.19/0.97  --fof                                   false
% 2.19/0.97  --time_out_real                         305.
% 2.19/0.97  --time_out_virtual                      -1.
% 2.19/0.97  --symbol_type_check                     false
% 2.19/0.97  --clausify_out                          false
% 2.19/0.97  --sig_cnt_out                           false
% 2.19/0.97  --trig_cnt_out                          false
% 2.19/0.97  --trig_cnt_out_tolerance                1.
% 2.19/0.97  --trig_cnt_out_sk_spl                   false
% 2.19/0.97  --abstr_cl_out                          false
% 2.19/0.97  
% 2.19/0.97  ------ Global Options
% 2.19/0.97  
% 2.19/0.97  --schedule                              default
% 2.19/0.97  --add_important_lit                     false
% 2.19/0.97  --prop_solver_per_cl                    1000
% 2.19/0.97  --min_unsat_core                        false
% 2.19/0.97  --soft_assumptions                      false
% 2.19/0.97  --soft_lemma_size                       3
% 2.19/0.97  --prop_impl_unit_size                   0
% 2.19/0.97  --prop_impl_unit                        []
% 2.19/0.97  --share_sel_clauses                     true
% 2.19/0.97  --reset_solvers                         false
% 2.19/0.97  --bc_imp_inh                            [conj_cone]
% 2.19/0.97  --conj_cone_tolerance                   3.
% 2.19/0.98  --extra_neg_conj                        none
% 2.19/0.98  --large_theory_mode                     true
% 2.19/0.98  --prolific_symb_bound                   200
% 2.19/0.98  --lt_threshold                          2000
% 2.19/0.98  --clause_weak_htbl                      true
% 2.19/0.98  --gc_record_bc_elim                     false
% 2.19/0.98  
% 2.19/0.98  ------ Preprocessing Options
% 2.19/0.98  
% 2.19/0.98  --preprocessing_flag                    true
% 2.19/0.98  --time_out_prep_mult                    0.1
% 2.19/0.98  --splitting_mode                        input
% 2.19/0.98  --splitting_grd                         true
% 2.19/0.98  --splitting_cvd                         false
% 2.19/0.98  --splitting_cvd_svl                     false
% 2.19/0.98  --splitting_nvd                         32
% 2.19/0.98  --sub_typing                            true
% 2.19/0.98  --prep_gs_sim                           true
% 2.19/0.98  --prep_unflatten                        true
% 2.19/0.98  --prep_res_sim                          true
% 2.19/0.98  --prep_upred                            true
% 2.19/0.98  --prep_sem_filter                       exhaustive
% 2.19/0.98  --prep_sem_filter_out                   false
% 2.19/0.98  --pred_elim                             true
% 2.19/0.98  --res_sim_input                         true
% 2.19/0.98  --eq_ax_congr_red                       true
% 2.19/0.98  --pure_diseq_elim                       true
% 2.19/0.98  --brand_transform                       false
% 2.19/0.98  --non_eq_to_eq                          false
% 2.19/0.98  --prep_def_merge                        true
% 2.19/0.98  --prep_def_merge_prop_impl              false
% 2.19/0.98  --prep_def_merge_mbd                    true
% 2.19/0.98  --prep_def_merge_tr_red                 false
% 2.19/0.98  --prep_def_merge_tr_cl                  false
% 2.19/0.98  --smt_preprocessing                     true
% 2.19/0.98  --smt_ac_axioms                         fast
% 2.19/0.98  --preprocessed_out                      false
% 2.19/0.98  --preprocessed_stats                    false
% 2.19/0.98  
% 2.19/0.98  ------ Abstraction refinement Options
% 2.19/0.98  
% 2.19/0.98  --abstr_ref                             []
% 2.19/0.98  --abstr_ref_prep                        false
% 2.19/0.98  --abstr_ref_until_sat                   false
% 2.19/0.98  --abstr_ref_sig_restrict                funpre
% 2.19/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.19/0.98  --abstr_ref_under                       []
% 2.19/0.98  
% 2.19/0.98  ------ SAT Options
% 2.19/0.98  
% 2.19/0.98  --sat_mode                              false
% 2.19/0.98  --sat_fm_restart_options                ""
% 2.19/0.98  --sat_gr_def                            false
% 2.19/0.98  --sat_epr_types                         true
% 2.19/0.98  --sat_non_cyclic_types                  false
% 2.19/0.98  --sat_finite_models                     false
% 2.19/0.98  --sat_fm_lemmas                         false
% 2.19/0.98  --sat_fm_prep                           false
% 2.19/0.98  --sat_fm_uc_incr                        true
% 2.19/0.98  --sat_out_model                         small
% 2.19/0.98  --sat_out_clauses                       false
% 2.19/0.98  
% 2.19/0.98  ------ QBF Options
% 2.19/0.98  
% 2.19/0.98  --qbf_mode                              false
% 2.19/0.98  --qbf_elim_univ                         false
% 2.19/0.98  --qbf_dom_inst                          none
% 2.19/0.98  --qbf_dom_pre_inst                      false
% 2.19/0.98  --qbf_sk_in                             false
% 2.19/0.98  --qbf_pred_elim                         true
% 2.19/0.98  --qbf_split                             512
% 2.19/0.98  
% 2.19/0.98  ------ BMC1 Options
% 2.19/0.98  
% 2.19/0.98  --bmc1_incremental                      false
% 2.19/0.98  --bmc1_axioms                           reachable_all
% 2.19/0.98  --bmc1_min_bound                        0
% 2.19/0.98  --bmc1_max_bound                        -1
% 2.19/0.98  --bmc1_max_bound_default                -1
% 2.19/0.98  --bmc1_symbol_reachability              true
% 2.19/0.98  --bmc1_property_lemmas                  false
% 2.19/0.98  --bmc1_k_induction                      false
% 2.19/0.98  --bmc1_non_equiv_states                 false
% 2.19/0.98  --bmc1_deadlock                         false
% 2.19/0.98  --bmc1_ucm                              false
% 2.19/0.98  --bmc1_add_unsat_core                   none
% 2.19/0.98  --bmc1_unsat_core_children              false
% 2.19/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.19/0.98  --bmc1_out_stat                         full
% 2.19/0.98  --bmc1_ground_init                      false
% 2.19/0.98  --bmc1_pre_inst_next_state              false
% 2.19/0.98  --bmc1_pre_inst_state                   false
% 2.19/0.98  --bmc1_pre_inst_reach_state             false
% 2.19/0.98  --bmc1_out_unsat_core                   false
% 2.19/0.98  --bmc1_aig_witness_out                  false
% 2.19/0.98  --bmc1_verbose                          false
% 2.19/0.98  --bmc1_dump_clauses_tptp                false
% 2.19/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.19/0.98  --bmc1_dump_file                        -
% 2.19/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.19/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.19/0.98  --bmc1_ucm_extend_mode                  1
% 2.19/0.98  --bmc1_ucm_init_mode                    2
% 2.19/0.98  --bmc1_ucm_cone_mode                    none
% 2.19/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.19/0.98  --bmc1_ucm_relax_model                  4
% 2.19/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.19/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.19/0.98  --bmc1_ucm_layered_model                none
% 2.19/0.98  --bmc1_ucm_max_lemma_size               10
% 2.19/0.98  
% 2.19/0.98  ------ AIG Options
% 2.19/0.98  
% 2.19/0.98  --aig_mode                              false
% 2.19/0.98  
% 2.19/0.98  ------ Instantiation Options
% 2.19/0.98  
% 2.19/0.98  --instantiation_flag                    true
% 2.19/0.98  --inst_sos_flag                         false
% 2.19/0.98  --inst_sos_phase                        true
% 2.19/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.19/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.19/0.98  --inst_lit_sel_side                     none
% 2.19/0.98  --inst_solver_per_active                1400
% 2.19/0.98  --inst_solver_calls_frac                1.
% 2.19/0.98  --inst_passive_queue_type               priority_queues
% 2.19/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.19/0.98  --inst_passive_queues_freq              [25;2]
% 2.19/0.98  --inst_dismatching                      true
% 2.19/0.98  --inst_eager_unprocessed_to_passive     true
% 2.19/0.98  --inst_prop_sim_given                   true
% 2.19/0.98  --inst_prop_sim_new                     false
% 2.19/0.98  --inst_subs_new                         false
% 2.19/0.98  --inst_eq_res_simp                      false
% 2.19/0.98  --inst_subs_given                       false
% 2.19/0.98  --inst_orphan_elimination               true
% 2.19/0.98  --inst_learning_loop_flag               true
% 2.19/0.98  --inst_learning_start                   3000
% 2.19/0.98  --inst_learning_factor                  2
% 2.19/0.98  --inst_start_prop_sim_after_learn       3
% 2.19/0.98  --inst_sel_renew                        solver
% 2.19/0.98  --inst_lit_activity_flag                true
% 2.19/0.98  --inst_restr_to_given                   false
% 2.19/0.98  --inst_activity_threshold               500
% 2.19/0.98  --inst_out_proof                        true
% 2.19/0.98  
% 2.19/0.98  ------ Resolution Options
% 2.19/0.98  
% 2.19/0.98  --resolution_flag                       false
% 2.19/0.98  --res_lit_sel                           adaptive
% 2.19/0.98  --res_lit_sel_side                      none
% 2.19/0.98  --res_ordering                          kbo
% 2.19/0.98  --res_to_prop_solver                    active
% 2.19/0.98  --res_prop_simpl_new                    false
% 2.19/0.98  --res_prop_simpl_given                  true
% 2.19/0.98  --res_passive_queue_type                priority_queues
% 2.19/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.19/0.98  --res_passive_queues_freq               [15;5]
% 2.19/0.98  --res_forward_subs                      full
% 2.19/0.98  --res_backward_subs                     full
% 2.19/0.98  --res_forward_subs_resolution           true
% 2.19/0.98  --res_backward_subs_resolution          true
% 2.19/0.98  --res_orphan_elimination                true
% 2.19/0.98  --res_time_limit                        2.
% 2.19/0.98  --res_out_proof                         true
% 2.19/0.98  
% 2.19/0.98  ------ Superposition Options
% 2.19/0.98  
% 2.19/0.98  --superposition_flag                    true
% 2.19/0.98  --sup_passive_queue_type                priority_queues
% 2.19/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.19/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.19/0.98  --demod_completeness_check              fast
% 2.19/0.98  --demod_use_ground                      true
% 2.19/0.98  --sup_to_prop_solver                    passive
% 2.19/0.98  --sup_prop_simpl_new                    true
% 2.19/0.98  --sup_prop_simpl_given                  true
% 2.19/0.98  --sup_fun_splitting                     false
% 2.19/0.98  --sup_smt_interval                      50000
% 2.19/0.98  
% 2.19/0.98  ------ Superposition Simplification Setup
% 2.19/0.98  
% 2.19/0.98  --sup_indices_passive                   []
% 2.19/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.19/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.19/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.19/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.19/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.19/0.98  --sup_full_bw                           [BwDemod]
% 2.19/0.98  --sup_immed_triv                        [TrivRules]
% 2.19/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.19/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.19/0.98  --sup_immed_bw_main                     []
% 2.19/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.19/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.19/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.19/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.19/0.98  
% 2.19/0.98  ------ Combination Options
% 2.19/0.98  
% 2.19/0.98  --comb_res_mult                         3
% 2.19/0.98  --comb_sup_mult                         2
% 2.19/0.98  --comb_inst_mult                        10
% 2.19/0.98  
% 2.19/0.98  ------ Debug Options
% 2.19/0.98  
% 2.19/0.98  --dbg_backtrace                         false
% 2.19/0.98  --dbg_dump_prop_clauses                 false
% 2.19/0.98  --dbg_dump_prop_clauses_file            -
% 2.19/0.98  --dbg_out_stat                          false
% 2.19/0.98  
% 2.19/0.98  
% 2.19/0.98  
% 2.19/0.98  
% 2.19/0.98  ------ Proving...
% 2.19/0.98  
% 2.19/0.98  
% 2.19/0.98  % SZS status Theorem for theBenchmark.p
% 2.19/0.98  
% 2.19/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.19/0.98  
% 2.19/0.98  fof(f7,axiom,(
% 2.19/0.98    ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <=> (X0 = X1 | r2_hidden(X0,X1)))),
% 2.19/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.19/0.98  
% 2.19/0.98  fof(f25,plain,(
% 2.19/0.98    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & ((X0 = X1 | r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 2.19/0.98    inference(nnf_transformation,[],[f7])).
% 2.19/0.98  
% 2.19/0.98  fof(f26,plain,(
% 2.19/0.98    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 2.19/0.98    inference(flattening,[],[f25])).
% 2.19/0.98  
% 2.19/0.98  fof(f42,plain,(
% 2.19/0.98    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | ~r2_hidden(X0,X1)) )),
% 2.19/0.98    inference(cnf_transformation,[],[f26])).
% 2.19/0.98  
% 2.19/0.98  fof(f5,axiom,(
% 2.19/0.98    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0)),
% 2.19/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.19/0.98  
% 2.19/0.98  fof(f38,plain,(
% 2.19/0.98    ( ! [X0] : (k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0)) )),
% 2.19/0.98    inference(cnf_transformation,[],[f5])).
% 2.19/0.98  
% 2.19/0.98  fof(f4,axiom,(
% 2.19/0.98    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.19/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.19/0.98  
% 2.19/0.98  fof(f37,plain,(
% 2.19/0.98    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.19/0.98    inference(cnf_transformation,[],[f4])).
% 2.19/0.98  
% 2.19/0.98  fof(f52,plain,(
% 2.19/0.98    ( ! [X0] : (k2_xboole_0(X0,k2_tarski(X0,X0)) = k1_ordinal1(X0)) )),
% 2.19/0.98    inference(definition_unfolding,[],[f38,f37])).
% 2.19/0.98  
% 2.19/0.98  fof(f54,plain,(
% 2.19/0.98    ( ! [X0,X1] : (r2_hidden(X0,k2_xboole_0(X1,k2_tarski(X1,X1))) | ~r2_hidden(X0,X1)) )),
% 2.19/0.98    inference(definition_unfolding,[],[f42,f52])).
% 2.19/0.98  
% 2.19/0.98  fof(f2,axiom,(
% 2.19/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.19/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.19/0.98  
% 2.19/0.98  fof(f22,plain,(
% 2.19/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.19/0.98    inference(nnf_transformation,[],[f2])).
% 2.19/0.98  
% 2.19/0.98  fof(f23,plain,(
% 2.19/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.19/0.98    inference(flattening,[],[f22])).
% 2.19/0.98  
% 2.19/0.98  fof(f35,plain,(
% 2.19/0.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.19/0.98    inference(cnf_transformation,[],[f23])).
% 2.19/0.98  
% 2.19/0.98  fof(f12,conjecture,(
% 2.19/0.98    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 2.19/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.19/0.98  
% 2.19/0.98  fof(f13,negated_conjecture,(
% 2.19/0.98    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 2.19/0.98    inference(negated_conjecture,[],[f12])).
% 2.19/0.98  
% 2.19/0.98  fof(f21,plain,(
% 2.19/0.98    ? [X0] : (? [X1] : ((r2_hidden(X0,X1) <~> r1_ordinal1(k1_ordinal1(X0),X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 2.19/0.98    inference(ennf_transformation,[],[f13])).
% 2.19/0.98  
% 2.19/0.98  fof(f27,plain,(
% 2.19/0.98    ? [X0] : (? [X1] : (((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 2.19/0.98    inference(nnf_transformation,[],[f21])).
% 2.19/0.98  
% 2.19/0.98  fof(f28,plain,(
% 2.19/0.98    ? [X0] : (? [X1] : ((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 2.19/0.98    inference(flattening,[],[f27])).
% 2.19/0.98  
% 2.19/0.98  fof(f30,plain,(
% 2.19/0.98    ( ! [X0] : (? [X1] : ((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1)) & v3_ordinal1(X1)) => ((~r1_ordinal1(k1_ordinal1(X0),sK1) | ~r2_hidden(X0,sK1)) & (r1_ordinal1(k1_ordinal1(X0),sK1) | r2_hidden(X0,sK1)) & v3_ordinal1(sK1))) )),
% 2.19/0.98    introduced(choice_axiom,[])).
% 2.19/0.98  
% 2.19/0.98  fof(f29,plain,(
% 2.19/0.98    ? [X0] : (? [X1] : ((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : ((~r1_ordinal1(k1_ordinal1(sK0),X1) | ~r2_hidden(sK0,X1)) & (r1_ordinal1(k1_ordinal1(sK0),X1) | r2_hidden(sK0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(sK0))),
% 2.19/0.98    introduced(choice_axiom,[])).
% 2.19/0.98  
% 2.19/0.98  fof(f31,plain,(
% 2.19/0.98    ((~r1_ordinal1(k1_ordinal1(sK0),sK1) | ~r2_hidden(sK0,sK1)) & (r1_ordinal1(k1_ordinal1(sK0),sK1) | r2_hidden(sK0,sK1)) & v3_ordinal1(sK1)) & v3_ordinal1(sK0)),
% 2.19/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f28,f30,f29])).
% 2.19/0.98  
% 2.19/0.98  fof(f48,plain,(
% 2.19/0.98    v3_ordinal1(sK0)),
% 2.19/0.98    inference(cnf_transformation,[],[f31])).
% 2.19/0.98  
% 2.19/0.98  fof(f49,plain,(
% 2.19/0.98    v3_ordinal1(sK1)),
% 2.19/0.98    inference(cnf_transformation,[],[f31])).
% 2.19/0.98  
% 2.19/0.98  fof(f10,axiom,(
% 2.19/0.98    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k1_ordinal1(X0)))),
% 2.19/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.19/0.98  
% 2.19/0.98  fof(f19,plain,(
% 2.19/0.98    ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 2.19/0.98    inference(ennf_transformation,[],[f10])).
% 2.19/0.98  
% 2.19/0.98  fof(f46,plain,(
% 2.19/0.98    ( ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0)) )),
% 2.19/0.98    inference(cnf_transformation,[],[f19])).
% 2.19/0.98  
% 2.19/0.98  fof(f57,plain,(
% 2.19/0.98    ( ! [X0] : (v3_ordinal1(k2_xboole_0(X0,k2_tarski(X0,X0))) | ~v3_ordinal1(X0)) )),
% 2.19/0.98    inference(definition_unfolding,[],[f46,f52])).
% 2.19/0.98  
% 2.19/0.98  fof(f6,axiom,(
% 2.19/0.98    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 2.19/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.19/0.98  
% 2.19/0.98  fof(f15,plain,(
% 2.19/0.98    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 2.19/0.98    inference(ennf_transformation,[],[f6])).
% 2.19/0.98  
% 2.19/0.98  fof(f16,plain,(
% 2.19/0.98    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 2.19/0.98    inference(flattening,[],[f15])).
% 2.19/0.98  
% 2.19/0.98  fof(f24,plain,(
% 2.19/0.98    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 2.19/0.98    inference(nnf_transformation,[],[f16])).
% 2.19/0.98  
% 2.19/0.98  fof(f39,plain,(
% 2.19/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 2.19/0.98    inference(cnf_transformation,[],[f24])).
% 2.19/0.98  
% 2.19/0.98  fof(f50,plain,(
% 2.19/0.98    r1_ordinal1(k1_ordinal1(sK0),sK1) | r2_hidden(sK0,sK1)),
% 2.19/0.98    inference(cnf_transformation,[],[f31])).
% 2.19/0.98  
% 2.19/0.98  fof(f59,plain,(
% 2.19/0.98    r1_ordinal1(k2_xboole_0(sK0,k2_tarski(sK0,sK0)),sK1) | r2_hidden(sK0,sK1)),
% 2.19/0.98    inference(definition_unfolding,[],[f50,f52])).
% 2.19/0.98  
% 2.19/0.98  fof(f11,axiom,(
% 2.19/0.98    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 2.19/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.19/0.98  
% 2.19/0.98  fof(f20,plain,(
% 2.19/0.98    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 2.19/0.98    inference(ennf_transformation,[],[f11])).
% 2.19/0.98  
% 2.19/0.98  fof(f47,plain,(
% 2.19/0.98    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 2.19/0.98    inference(cnf_transformation,[],[f20])).
% 2.19/0.98  
% 2.19/0.98  fof(f41,plain,(
% 2.19/0.98    ( ! [X0,X1] : (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) )),
% 2.19/0.98    inference(cnf_transformation,[],[f26])).
% 2.19/0.98  
% 2.19/0.98  fof(f55,plain,(
% 2.19/0.98    ( ! [X0,X1] : (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k2_xboole_0(X1,k2_tarski(X1,X1)))) )),
% 2.19/0.98    inference(definition_unfolding,[],[f41,f52])).
% 2.19/0.98  
% 2.19/0.98  fof(f43,plain,(
% 2.19/0.98    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | X0 != X1) )),
% 2.19/0.98    inference(cnf_transformation,[],[f26])).
% 2.19/0.98  
% 2.19/0.98  fof(f53,plain,(
% 2.19/0.98    ( ! [X0,X1] : (r2_hidden(X0,k2_xboole_0(X1,k2_tarski(X1,X1))) | X0 != X1) )),
% 2.19/0.98    inference(definition_unfolding,[],[f43,f52])).
% 2.19/0.98  
% 2.19/0.98  fof(f62,plain,(
% 2.19/0.98    ( ! [X1] : (r2_hidden(X1,k2_xboole_0(X1,k2_tarski(X1,X1)))) )),
% 2.19/0.98    inference(equality_resolution,[],[f53])).
% 2.19/0.98  
% 2.19/0.98  fof(f33,plain,(
% 2.19/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.19/0.98    inference(cnf_transformation,[],[f23])).
% 2.19/0.98  
% 2.19/0.98  fof(f61,plain,(
% 2.19/0.98    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.19/0.98    inference(equality_resolution,[],[f33])).
% 2.19/0.98  
% 2.19/0.98  fof(f1,axiom,(
% 2.19/0.98    ! [X0,X1] : (r2_hidden(X0,X1) => ~r2_hidden(X1,X0))),
% 2.19/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.19/0.98  
% 2.19/0.98  fof(f14,plain,(
% 2.19/0.98    ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1))),
% 2.19/0.98    inference(ennf_transformation,[],[f1])).
% 2.19/0.98  
% 2.19/0.98  fof(f32,plain,(
% 2.19/0.98    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1)) )),
% 2.19/0.98    inference(cnf_transformation,[],[f14])).
% 2.19/0.98  
% 2.19/0.98  fof(f9,axiom,(
% 2.19/0.98    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 2.19/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.19/0.98  
% 2.19/0.98  fof(f17,plain,(
% 2.19/0.98    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 2.19/0.98    inference(ennf_transformation,[],[f9])).
% 2.19/0.98  
% 2.19/0.98  fof(f18,plain,(
% 2.19/0.98    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 2.19/0.98    inference(flattening,[],[f17])).
% 2.19/0.98  
% 2.19/0.98  fof(f45,plain,(
% 2.19/0.98    ( ! [X0,X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 2.19/0.98    inference(cnf_transformation,[],[f18])).
% 2.19/0.98  
% 2.19/0.98  fof(f40,plain,(
% 2.19/0.98    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 2.19/0.98    inference(cnf_transformation,[],[f24])).
% 2.19/0.98  
% 2.19/0.98  fof(f51,plain,(
% 2.19/0.98    ~r1_ordinal1(k1_ordinal1(sK0),sK1) | ~r2_hidden(sK0,sK1)),
% 2.19/0.98    inference(cnf_transformation,[],[f31])).
% 2.19/0.98  
% 2.19/0.98  fof(f58,plain,(
% 2.19/0.98    ~r1_ordinal1(k2_xboole_0(sK0,k2_tarski(sK0,sK0)),sK1) | ~r2_hidden(sK0,sK1)),
% 2.19/0.98    inference(definition_unfolding,[],[f51,f52])).
% 2.19/0.98  
% 2.19/0.98  fof(f8,axiom,(
% 2.19/0.98    ! [X0] : k1_ordinal1(X0) != X0),
% 2.19/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.19/0.98  
% 2.19/0.98  fof(f44,plain,(
% 2.19/0.98    ( ! [X0] : (k1_ordinal1(X0) != X0) )),
% 2.19/0.98    inference(cnf_transformation,[],[f8])).
% 2.19/0.98  
% 2.19/0.98  fof(f56,plain,(
% 2.19/0.98    ( ! [X0] : (k2_xboole_0(X0,k2_tarski(X0,X0)) != X0) )),
% 2.19/0.98    inference(definition_unfolding,[],[f44,f52])).
% 2.19/0.98  
% 2.19/0.98  cnf(c_435,plain,
% 2.19/0.98      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.19/0.98      theory(equality) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_1360,plain,
% 2.19/0.98      ( ~ r1_tarski(X0,X1)
% 2.19/0.98      | r1_tarski(sK1,k2_xboole_0(sK0,k2_tarski(sK0,sK0)))
% 2.19/0.98      | k2_xboole_0(sK0,k2_tarski(sK0,sK0)) != X1
% 2.19/0.98      | sK1 != X0 ),
% 2.19/0.98      inference(instantiation,[status(thm)],[c_435]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_2017,plain,
% 2.19/0.98      ( ~ r1_tarski(X0,k2_xboole_0(sK0,k2_tarski(sK0,sK0)))
% 2.19/0.98      | r1_tarski(sK1,k2_xboole_0(sK0,k2_tarski(sK0,sK0)))
% 2.19/0.98      | k2_xboole_0(sK0,k2_tarski(sK0,sK0)) != k2_xboole_0(sK0,k2_tarski(sK0,sK0))
% 2.19/0.98      | sK1 != X0 ),
% 2.19/0.98      inference(instantiation,[status(thm)],[c_1360]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_2020,plain,
% 2.19/0.98      ( r1_tarski(sK1,k2_xboole_0(sK0,k2_tarski(sK0,sK0)))
% 2.19/0.98      | ~ r1_tarski(sK0,k2_xboole_0(sK0,k2_tarski(sK0,sK0)))
% 2.19/0.98      | k2_xboole_0(sK0,k2_tarski(sK0,sK0)) != k2_xboole_0(sK0,k2_tarski(sK0,sK0))
% 2.19/0.98      | sK1 != sK0 ),
% 2.19/0.98      inference(instantiation,[status(thm)],[c_2017]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_433,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_973,plain,
% 2.19/0.98      ( X0 != X1
% 2.19/0.98      | k2_xboole_0(X0,k2_tarski(X0,X0)) != X1
% 2.19/0.98      | k2_xboole_0(X0,k2_tarski(X0,X0)) = X0 ),
% 2.19/0.98      inference(instantiation,[status(thm)],[c_433]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_1393,plain,
% 2.19/0.98      ( X0 != sK1
% 2.19/0.98      | k2_xboole_0(X0,k2_tarski(X0,X0)) = X0
% 2.19/0.98      | k2_xboole_0(X0,k2_tarski(X0,X0)) != sK1 ),
% 2.19/0.98      inference(instantiation,[status(thm)],[c_973]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_1396,plain,
% 2.19/0.98      ( k2_xboole_0(sK0,k2_tarski(sK0,sK0)) != sK1
% 2.19/0.98      | k2_xboole_0(sK0,k2_tarski(sK0,sK0)) = sK0
% 2.19/0.98      | sK0 != sK1 ),
% 2.19/0.98      inference(instantiation,[status(thm)],[c_1393]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_8,plain,
% 2.19/0.98      ( ~ r2_hidden(X0,X1)
% 2.19/0.98      | r2_hidden(X0,k2_xboole_0(X1,k2_tarski(X1,X1))) ),
% 2.19/0.98      inference(cnf_transformation,[],[f54]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_1277,plain,
% 2.19/0.98      ( r2_hidden(sK1,k2_xboole_0(sK0,k2_tarski(sK0,sK0)))
% 2.19/0.98      | ~ r2_hidden(sK1,sK0) ),
% 2.19/0.98      inference(instantiation,[status(thm)],[c_8]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_1,plain,
% 2.19/0.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 2.19/0.98      inference(cnf_transformation,[],[f35]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_1007,plain,
% 2.19/0.98      ( ~ r1_tarski(X0,sK1) | ~ r1_tarski(sK1,X0) | X0 = sK1 ),
% 2.19/0.98      inference(instantiation,[status(thm)],[c_1]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_1274,plain,
% 2.19/0.98      ( ~ r1_tarski(k2_xboole_0(sK0,k2_tarski(sK0,sK0)),sK1)
% 2.19/0.98      | ~ r1_tarski(sK1,k2_xboole_0(sK0,k2_tarski(sK0,sK0)))
% 2.19/0.98      | k2_xboole_0(sK0,k2_tarski(sK0,sK0)) = sK1 ),
% 2.19/0.98      inference(instantiation,[status(thm)],[c_1007]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_17,negated_conjecture,
% 2.19/0.98      ( v3_ordinal1(sK0) ),
% 2.19/0.98      inference(cnf_transformation,[],[f48]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_16,negated_conjecture,
% 2.19/0.98      ( v3_ordinal1(sK1) ),
% 2.19/0.98      inference(cnf_transformation,[],[f49]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_12,plain,
% 2.19/0.98      ( ~ v3_ordinal1(X0)
% 2.19/0.98      | v3_ordinal1(k2_xboole_0(X0,k2_tarski(X0,X0))) ),
% 2.19/0.98      inference(cnf_transformation,[],[f57]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_26,plain,
% 2.19/0.98      ( v3_ordinal1(k2_xboole_0(sK0,k2_tarski(sK0,sK0)))
% 2.19/0.98      | ~ v3_ordinal1(sK0) ),
% 2.19/0.98      inference(instantiation,[status(thm)],[c_12]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_6,plain,
% 2.19/0.98      ( ~ r1_ordinal1(X0,X1)
% 2.19/0.98      | r1_tarski(X0,X1)
% 2.19/0.98      | ~ v3_ordinal1(X1)
% 2.19/0.98      | ~ v3_ordinal1(X0) ),
% 2.19/0.98      inference(cnf_transformation,[],[f39]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_15,negated_conjecture,
% 2.19/0.98      ( r1_ordinal1(k2_xboole_0(sK0,k2_tarski(sK0,sK0)),sK1)
% 2.19/0.98      | r2_hidden(sK0,sK1) ),
% 2.19/0.98      inference(cnf_transformation,[],[f59]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_135,plain,
% 2.19/0.98      ( r2_hidden(sK0,sK1)
% 2.19/0.98      | r1_ordinal1(k2_xboole_0(sK0,k2_tarski(sK0,sK0)),sK1) ),
% 2.19/0.98      inference(prop_impl,[status(thm)],[c_15]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_136,plain,
% 2.19/0.98      ( r1_ordinal1(k2_xboole_0(sK0,k2_tarski(sK0,sK0)),sK1)
% 2.19/0.98      | r2_hidden(sK0,sK1) ),
% 2.19/0.98      inference(renaming,[status(thm)],[c_135]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_267,plain,
% 2.19/0.98      ( r1_tarski(X0,X1)
% 2.19/0.98      | r2_hidden(sK0,sK1)
% 2.19/0.98      | ~ v3_ordinal1(X0)
% 2.19/0.98      | ~ v3_ordinal1(X1)
% 2.19/0.98      | k2_xboole_0(sK0,k2_tarski(sK0,sK0)) != X0
% 2.19/0.98      | sK1 != X1 ),
% 2.19/0.98      inference(resolution_lifted,[status(thm)],[c_6,c_136]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_268,plain,
% 2.19/0.98      ( r1_tarski(k2_xboole_0(sK0,k2_tarski(sK0,sK0)),sK1)
% 2.19/0.98      | r2_hidden(sK0,sK1)
% 2.19/0.98      | ~ v3_ordinal1(k2_xboole_0(sK0,k2_tarski(sK0,sK0)))
% 2.19/0.98      | ~ v3_ordinal1(sK1) ),
% 2.19/0.98      inference(unflattening,[status(thm)],[c_267]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_349,plain,
% 2.19/0.98      ( r2_hidden(sK0,sK1)
% 2.19/0.98      | r1_tarski(k2_xboole_0(sK0,k2_tarski(sK0,sK0)),sK1) ),
% 2.19/0.98      inference(prop_impl,[status(thm)],[c_17,c_16,c_26,c_268]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_350,plain,
% 2.19/0.98      ( r1_tarski(k2_xboole_0(sK0,k2_tarski(sK0,sK0)),sK1)
% 2.19/0.98      | r2_hidden(sK0,sK1) ),
% 2.19/0.98      inference(renaming,[status(thm)],[c_349]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_798,plain,
% 2.19/0.98      ( r1_tarski(k2_xboole_0(sK0,k2_tarski(sK0,sK0)),sK1) = iProver_top
% 2.19/0.98      | r2_hidden(sK0,sK1) = iProver_top ),
% 2.19/0.98      inference(predicate_to_equality,[status(thm)],[c_350]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_18,plain,
% 2.19/0.98      ( v3_ordinal1(sK0) = iProver_top ),
% 2.19/0.98      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_19,plain,
% 2.19/0.98      ( v3_ordinal1(sK1) = iProver_top ),
% 2.19/0.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_13,plain,
% 2.19/0.98      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X1,X0) ),
% 2.19/0.98      inference(cnf_transformation,[],[f47]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_23,plain,
% 2.19/0.98      ( ~ r1_tarski(sK0,sK0) | ~ r2_hidden(sK0,sK0) ),
% 2.19/0.98      inference(instantiation,[status(thm)],[c_13]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_25,plain,
% 2.19/0.98      ( v3_ordinal1(X0) != iProver_top
% 2.19/0.98      | v3_ordinal1(k2_xboole_0(X0,k2_tarski(X0,X0))) = iProver_top ),
% 2.19/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_27,plain,
% 2.19/0.98      ( v3_ordinal1(k2_xboole_0(sK0,k2_tarski(sK0,sK0))) = iProver_top
% 2.19/0.98      | v3_ordinal1(sK0) != iProver_top ),
% 2.19/0.98      inference(instantiation,[status(thm)],[c_25]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_9,plain,
% 2.19/0.98      ( r2_hidden(X0,X1)
% 2.19/0.98      | ~ r2_hidden(X0,k2_xboole_0(X1,k2_tarski(X1,X1)))
% 2.19/0.98      | X0 = X1 ),
% 2.19/0.98      inference(cnf_transformation,[],[f55]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_33,plain,
% 2.19/0.98      ( ~ r2_hidden(sK0,k2_xboole_0(sK0,k2_tarski(sK0,sK0)))
% 2.19/0.98      | r2_hidden(sK0,sK0)
% 2.19/0.98      | sK0 = sK0 ),
% 2.19/0.98      inference(instantiation,[status(thm)],[c_9]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_7,plain,
% 2.19/0.98      ( r2_hidden(X0,k2_xboole_0(X0,k2_tarski(X0,X0))) ),
% 2.19/0.98      inference(cnf_transformation,[],[f62]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_39,plain,
% 2.19/0.98      ( r2_hidden(sK0,k2_xboole_0(sK0,k2_tarski(sK0,sK0))) ),
% 2.19/0.98      inference(instantiation,[status(thm)],[c_7]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_3,plain,
% 2.19/0.98      ( r1_tarski(X0,X0) ),
% 2.19/0.98      inference(cnf_transformation,[],[f61]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_51,plain,
% 2.19/0.98      ( r1_tarski(sK0,sK0) ),
% 2.19/0.98      inference(instantiation,[status(thm)],[c_3]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_50,plain,
% 2.19/0.98      ( r1_tarski(X0,X0) = iProver_top ),
% 2.19/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_52,plain,
% 2.19/0.98      ( r1_tarski(sK0,sK0) = iProver_top ),
% 2.19/0.98      inference(instantiation,[status(thm)],[c_50]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_270,plain,
% 2.19/0.98      ( r1_tarski(k2_xboole_0(sK0,k2_tarski(sK0,sK0)),sK1)
% 2.19/0.98      | r2_hidden(sK0,sK1) ),
% 2.19/0.98      inference(global_propositional_subsumption,
% 2.19/0.98                [status(thm)],
% 2.19/0.98                [c_268,c_17,c_16,c_26]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_272,plain,
% 2.19/0.98      ( r1_tarski(k2_xboole_0(sK0,k2_tarski(sK0,sK0)),sK1) = iProver_top
% 2.19/0.98      | r2_hidden(sK0,sK1) = iProver_top ),
% 2.19/0.98      inference(predicate_to_equality,[status(thm)],[c_270]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_0,plain,
% 2.19/0.98      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X1,X0) ),
% 2.19/0.98      inference(cnf_transformation,[],[f32]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_906,plain,
% 2.19/0.98      ( ~ r2_hidden(sK1,sK0) | ~ r2_hidden(sK0,sK1) ),
% 2.19/0.98      inference(instantiation,[status(thm)],[c_0]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_907,plain,
% 2.19/0.98      ( r2_hidden(sK1,sK0) != iProver_top
% 2.19/0.98      | r2_hidden(sK0,sK1) != iProver_top ),
% 2.19/0.98      inference(predicate_to_equality,[status(thm)],[c_906]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_926,plain,
% 2.19/0.98      ( ~ r1_tarski(sK1,sK0) | ~ r2_hidden(sK0,sK1) ),
% 2.19/0.98      inference(instantiation,[status(thm)],[c_13]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_927,plain,
% 2.19/0.98      ( r1_tarski(sK1,sK0) != iProver_top
% 2.19/0.98      | r2_hidden(sK0,sK1) != iProver_top ),
% 2.19/0.98      inference(predicate_to_equality,[status(thm)],[c_926]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_11,plain,
% 2.19/0.98      ( r1_ordinal1(X0,X1)
% 2.19/0.98      | r2_hidden(X1,X0)
% 2.19/0.98      | ~ v3_ordinal1(X1)
% 2.19/0.98      | ~ v3_ordinal1(X0) ),
% 2.19/0.98      inference(cnf_transformation,[],[f45]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_222,plain,
% 2.19/0.98      ( r1_tarski(X0,X1)
% 2.19/0.98      | r2_hidden(X1,X0)
% 2.19/0.98      | ~ v3_ordinal1(X0)
% 2.19/0.98      | ~ v3_ordinal1(X1) ),
% 2.19/0.98      inference(resolution,[status(thm)],[c_11,c_6]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_938,plain,
% 2.19/0.98      ( r1_tarski(k2_xboole_0(sK0,k2_tarski(sK0,sK0)),sK1)
% 2.19/0.98      | r2_hidden(sK1,k2_xboole_0(sK0,k2_tarski(sK0,sK0)))
% 2.19/0.98      | ~ v3_ordinal1(k2_xboole_0(sK0,k2_tarski(sK0,sK0)))
% 2.19/0.98      | ~ v3_ordinal1(sK1) ),
% 2.19/0.98      inference(instantiation,[status(thm)],[c_222]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_939,plain,
% 2.19/0.98      ( r1_tarski(k2_xboole_0(sK0,k2_tarski(sK0,sK0)),sK1) = iProver_top
% 2.19/0.98      | r2_hidden(sK1,k2_xboole_0(sK0,k2_tarski(sK0,sK0))) = iProver_top
% 2.19/0.98      | v3_ordinal1(k2_xboole_0(sK0,k2_tarski(sK0,sK0))) != iProver_top
% 2.19/0.98      | v3_ordinal1(sK1) != iProver_top ),
% 2.19/0.98      inference(predicate_to_equality,[status(thm)],[c_938]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_994,plain,
% 2.19/0.98      ( ~ r1_tarski(X0,X1) | r1_tarski(sK1,sK0) | sK1 != X0 | sK0 != X1 ),
% 2.19/0.98      inference(instantiation,[status(thm)],[c_435]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_995,plain,
% 2.19/0.98      ( sK1 != X0
% 2.19/0.98      | sK0 != X1
% 2.19/0.98      | r1_tarski(X0,X1) != iProver_top
% 2.19/0.98      | r1_tarski(sK1,sK0) = iProver_top ),
% 2.19/0.98      inference(predicate_to_equality,[status(thm)],[c_994]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_997,plain,
% 2.19/0.98      ( sK1 != sK0
% 2.19/0.98      | sK0 != sK0
% 2.19/0.98      | r1_tarski(sK1,sK0) = iProver_top
% 2.19/0.98      | r1_tarski(sK0,sK0) != iProver_top ),
% 2.19/0.98      inference(instantiation,[status(thm)],[c_995]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_1077,plain,
% 2.19/0.98      ( r2_hidden(sK1,X0)
% 2.19/0.98      | ~ r2_hidden(sK1,k2_xboole_0(X0,k2_tarski(X0,X0)))
% 2.19/0.98      | sK1 = X0 ),
% 2.19/0.98      inference(instantiation,[status(thm)],[c_9]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_1078,plain,
% 2.19/0.98      ( sK1 = X0
% 2.19/0.98      | r2_hidden(sK1,X0) = iProver_top
% 2.19/0.98      | r2_hidden(sK1,k2_xboole_0(X0,k2_tarski(X0,X0))) != iProver_top ),
% 2.19/0.98      inference(predicate_to_equality,[status(thm)],[c_1077]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_1080,plain,
% 2.19/0.98      ( sK1 = sK0
% 2.19/0.98      | r2_hidden(sK1,k2_xboole_0(sK0,k2_tarski(sK0,sK0))) != iProver_top
% 2.19/0.98      | r2_hidden(sK1,sK0) = iProver_top ),
% 2.19/0.98      inference(instantiation,[status(thm)],[c_1078]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_1241,plain,
% 2.19/0.98      ( r1_tarski(k2_xboole_0(sK0,k2_tarski(sK0,sK0)),sK1) = iProver_top ),
% 2.19/0.98      inference(global_propositional_subsumption,
% 2.19/0.98                [status(thm)],
% 2.19/0.98                [c_798,c_18,c_19,c_23,c_27,c_33,c_39,c_51,c_52,c_272,
% 2.19/0.98                 c_907,c_927,c_939,c_997,c_1080]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_1243,plain,
% 2.19/0.98      ( r1_tarski(k2_xboole_0(sK0,k2_tarski(sK0,sK0)),sK1) ),
% 2.19/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_1241]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_1204,plain,
% 2.19/0.98      ( r1_tarski(X0,k2_xboole_0(X0,k2_tarski(X0,X0)))
% 2.19/0.98      | r2_hidden(k2_xboole_0(X0,k2_tarski(X0,X0)),X0)
% 2.19/0.98      | ~ v3_ordinal1(X0)
% 2.19/0.98      | ~ v3_ordinal1(k2_xboole_0(X0,k2_tarski(X0,X0))) ),
% 2.19/0.98      inference(instantiation,[status(thm)],[c_222]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_1206,plain,
% 2.19/0.98      ( r1_tarski(sK0,k2_xboole_0(sK0,k2_tarski(sK0,sK0)))
% 2.19/0.98      | r2_hidden(k2_xboole_0(sK0,k2_tarski(sK0,sK0)),sK0)
% 2.19/0.98      | ~ v3_ordinal1(k2_xboole_0(sK0,k2_tarski(sK0,sK0)))
% 2.19/0.98      | ~ v3_ordinal1(sK0) ),
% 2.19/0.98      inference(instantiation,[status(thm)],[c_1204]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_432,plain,( X0 = X0 ),theory(equality) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_1171,plain,
% 2.19/0.98      ( k2_xboole_0(X0,k2_tarski(X0,X0)) = k2_xboole_0(X0,k2_tarski(X0,X0)) ),
% 2.19/0.98      inference(instantiation,[status(thm)],[c_432]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_1173,plain,
% 2.19/0.98      ( k2_xboole_0(sK0,k2_tarski(sK0,sK0)) = k2_xboole_0(sK0,k2_tarski(sK0,sK0)) ),
% 2.19/0.98      inference(instantiation,[status(thm)],[c_1171]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_1072,plain,
% 2.19/0.98      ( ~ r1_tarski(X0,sK1) | ~ r1_tarski(sK1,X0) | sK1 = X0 ),
% 2.19/0.98      inference(instantiation,[status(thm)],[c_1]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_1074,plain,
% 2.19/0.98      ( ~ r1_tarski(sK1,sK0) | ~ r1_tarski(sK0,sK1) | sK1 = sK0 ),
% 2.19/0.98      inference(instantiation,[status(thm)],[c_1072]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_1053,plain,
% 2.19/0.98      ( r1_tarski(X0,sK1)
% 2.19/0.98      | r2_hidden(sK1,X0)
% 2.19/0.98      | ~ v3_ordinal1(X0)
% 2.19/0.98      | ~ v3_ordinal1(sK1) ),
% 2.19/0.98      inference(instantiation,[status(thm)],[c_222]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_1055,plain,
% 2.19/0.98      ( r1_tarski(sK0,sK1)
% 2.19/0.98      | r2_hidden(sK1,sK0)
% 2.19/0.98      | ~ v3_ordinal1(sK1)
% 2.19/0.98      | ~ v3_ordinal1(sK0) ),
% 2.19/0.98      inference(instantiation,[status(thm)],[c_1053]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_1009,plain,
% 2.19/0.98      ( ~ r1_tarski(sK1,sK0) | ~ r1_tarski(sK0,sK1) | sK0 = sK1 ),
% 2.19/0.98      inference(instantiation,[status(thm)],[c_1007]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_991,plain,
% 2.19/0.98      ( r1_tarski(sK1,sK0)
% 2.19/0.98      | r2_hidden(sK0,sK1)
% 2.19/0.98      | ~ v3_ordinal1(sK1)
% 2.19/0.98      | ~ v3_ordinal1(sK0) ),
% 2.19/0.98      inference(instantiation,[status(thm)],[c_222]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_929,plain,
% 2.19/0.98      ( ~ r1_tarski(k2_xboole_0(sK0,k2_tarski(sK0,sK0)),sK1)
% 2.19/0.98      | ~ r2_hidden(sK1,k2_xboole_0(sK0,k2_tarski(sK0,sK0))) ),
% 2.19/0.98      inference(instantiation,[status(thm)],[c_13]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_912,plain,
% 2.19/0.98      ( ~ r2_hidden(X0,k2_xboole_0(X0,k2_tarski(X0,X0)))
% 2.19/0.98      | ~ r2_hidden(k2_xboole_0(X0,k2_tarski(X0,X0)),X0) ),
% 2.19/0.98      inference(instantiation,[status(thm)],[c_0]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_914,plain,
% 2.19/0.98      ( ~ r2_hidden(k2_xboole_0(sK0,k2_tarski(sK0,sK0)),sK0)
% 2.19/0.98      | ~ r2_hidden(sK0,k2_xboole_0(sK0,k2_tarski(sK0,sK0))) ),
% 2.19/0.98      inference(instantiation,[status(thm)],[c_912]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_5,plain,
% 2.19/0.98      ( r1_ordinal1(X0,X1)
% 2.19/0.98      | ~ r1_tarski(X0,X1)
% 2.19/0.98      | ~ v3_ordinal1(X1)
% 2.19/0.98      | ~ v3_ordinal1(X0) ),
% 2.19/0.98      inference(cnf_transformation,[],[f40]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_14,negated_conjecture,
% 2.19/0.98      ( ~ r1_ordinal1(k2_xboole_0(sK0,k2_tarski(sK0,sK0)),sK1)
% 2.19/0.98      | ~ r2_hidden(sK0,sK1) ),
% 2.19/0.98      inference(cnf_transformation,[],[f58]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_133,plain,
% 2.19/0.98      ( ~ r2_hidden(sK0,sK1)
% 2.19/0.98      | ~ r1_ordinal1(k2_xboole_0(sK0,k2_tarski(sK0,sK0)),sK1) ),
% 2.19/0.98      inference(prop_impl,[status(thm)],[c_14]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_134,plain,
% 2.19/0.98      ( ~ r1_ordinal1(k2_xboole_0(sK0,k2_tarski(sK0,sK0)),sK1)
% 2.19/0.98      | ~ r2_hidden(sK0,sK1) ),
% 2.19/0.98      inference(renaming,[status(thm)],[c_133]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_253,plain,
% 2.19/0.98      ( ~ r1_tarski(X0,X1)
% 2.19/0.98      | ~ r2_hidden(sK0,sK1)
% 2.19/0.98      | ~ v3_ordinal1(X0)
% 2.19/0.98      | ~ v3_ordinal1(X1)
% 2.19/0.98      | k2_xboole_0(sK0,k2_tarski(sK0,sK0)) != X0
% 2.19/0.98      | sK1 != X1 ),
% 2.19/0.98      inference(resolution_lifted,[status(thm)],[c_5,c_134]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_254,plain,
% 2.19/0.98      ( ~ r1_tarski(k2_xboole_0(sK0,k2_tarski(sK0,sK0)),sK1)
% 2.19/0.98      | ~ r2_hidden(sK0,sK1)
% 2.19/0.98      | ~ v3_ordinal1(k2_xboole_0(sK0,k2_tarski(sK0,sK0)))
% 2.19/0.98      | ~ v3_ordinal1(sK1) ),
% 2.19/0.98      inference(unflattening,[status(thm)],[c_253]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_256,plain,
% 2.19/0.98      ( ~ r1_tarski(k2_xboole_0(sK0,k2_tarski(sK0,sK0)),sK1)
% 2.19/0.98      | ~ r2_hidden(sK0,sK1) ),
% 2.19/0.98      inference(global_propositional_subsumption,
% 2.19/0.98                [status(thm)],
% 2.19/0.98                [c_254,c_17,c_16,c_26]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_10,plain,
% 2.19/0.98      ( k2_xboole_0(X0,k2_tarski(X0,X0)) != X0 ),
% 2.19/0.98      inference(cnf_transformation,[],[f56]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(c_31,plain,
% 2.19/0.98      ( k2_xboole_0(sK0,k2_tarski(sK0,sK0)) != sK0 ),
% 2.19/0.98      inference(instantiation,[status(thm)],[c_10]) ).
% 2.19/0.98  
% 2.19/0.98  cnf(contradiction,plain,
% 2.19/0.98      ( $false ),
% 2.19/0.98      inference(minisat,
% 2.19/0.98                [status(thm)],
% 2.19/0.98                [c_2020,c_1396,c_1277,c_1274,c_1243,c_1206,c_1173,c_1074,
% 2.19/0.98                 c_1055,c_1009,c_991,c_929,c_914,c_256,c_39,c_31,c_26,
% 2.19/0.98                 c_16,c_17]) ).
% 2.19/0.98  
% 2.19/0.98  
% 2.19/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.19/0.98  
% 2.19/0.98  ------                               Statistics
% 2.19/0.98  
% 2.19/0.98  ------ General
% 2.19/0.98  
% 2.19/0.98  abstr_ref_over_cycles:                  0
% 2.19/0.98  abstr_ref_under_cycles:                 0
% 2.19/0.98  gc_basic_clause_elim:                   0
% 2.19/0.98  forced_gc_time:                         0
% 2.19/0.98  parsing_time:                           0.009
% 2.19/0.98  unif_index_cands_time:                  0.
% 2.19/0.98  unif_index_add_time:                    0.
% 2.19/0.98  orderings_time:                         0.
% 2.19/0.98  out_proof_time:                         0.011
% 2.19/0.98  total_time:                             0.097
% 2.19/0.98  num_of_symbols:                         39
% 2.19/0.98  num_of_terms:                           1465
% 2.19/0.98  
% 2.19/0.98  ------ Preprocessing
% 2.19/0.98  
% 2.19/0.98  num_of_splits:                          0
% 2.19/0.98  num_of_split_atoms:                     0
% 2.19/0.98  num_of_reused_defs:                     0
% 2.19/0.98  num_eq_ax_congr_red:                    1
% 2.19/0.98  num_of_sem_filtered_clauses:            1
% 2.19/0.98  num_of_subtypes:                        0
% 2.19/0.98  monotx_restored_types:                  0
% 2.19/0.98  sat_num_of_epr_types:                   0
% 2.19/0.98  sat_num_of_non_cyclic_types:            0
% 2.19/0.98  sat_guarded_non_collapsed_types:        0
% 2.19/0.98  num_pure_diseq_elim:                    0
% 2.19/0.98  simp_replaced_by:                       0
% 2.19/0.98  res_preprocessed:                       80
% 2.19/0.98  prep_upred:                             0
% 2.19/0.98  prep_unflattend:                        6
% 2.19/0.98  smt_new_axioms:                         0
% 2.19/0.98  pred_elim_cands:                        3
% 2.19/0.98  pred_elim:                              1
% 2.19/0.98  pred_elim_cl:                           1
% 2.19/0.98  pred_elim_cycles:                       3
% 2.19/0.98  merged_defs:                            8
% 2.19/0.98  merged_defs_ncl:                        0
% 2.19/0.98  bin_hyper_res:                          8
% 2.19/0.98  prep_cycles:                            4
% 2.19/0.98  pred_elim_time:                         0.003
% 2.19/0.98  splitting_time:                         0.
% 2.19/0.98  sem_filter_time:                        0.
% 2.19/0.98  monotx_time:                            0.001
% 2.19/0.98  subtype_inf_time:                       0.
% 2.19/0.98  
% 2.19/0.98  ------ Problem properties
% 2.19/0.98  
% 2.19/0.98  clauses:                                16
% 2.19/0.98  conjectures:                            2
% 2.19/0.98  epr:                                    7
% 2.19/0.98  horn:                                   13
% 2.19/0.98  ground:                                 5
% 2.19/0.98  unary:                                  6
% 2.19/0.98  binary:                                 7
% 2.19/0.98  lits:                                   30
% 2.19/0.98  lits_eq:                                3
% 2.19/0.98  fd_pure:                                0
% 2.19/0.98  fd_pseudo:                              0
% 2.19/0.98  fd_cond:                                0
% 2.19/0.98  fd_pseudo_cond:                         2
% 2.19/0.98  ac_symbols:                             0
% 2.19/0.98  
% 2.19/0.98  ------ Propositional Solver
% 2.19/0.98  
% 2.19/0.98  prop_solver_calls:                      27
% 2.19/0.98  prop_fast_solver_calls:                 414
% 2.19/0.98  smt_solver_calls:                       0
% 2.19/0.98  smt_fast_solver_calls:                  0
% 2.19/0.98  prop_num_of_clauses:                    605
% 2.19/0.98  prop_preprocess_simplified:             2803
% 2.19/0.98  prop_fo_subsumed:                       12
% 2.19/0.98  prop_solver_time:                       0.
% 2.19/0.98  smt_solver_time:                        0.
% 2.19/0.98  smt_fast_solver_time:                   0.
% 2.19/0.98  prop_fast_solver_time:                  0.
% 2.19/0.98  prop_unsat_core_time:                   0.
% 2.19/0.98  
% 2.19/0.98  ------ QBF
% 2.19/0.98  
% 2.19/0.98  qbf_q_res:                              0
% 2.19/0.98  qbf_num_tautologies:                    0
% 2.19/0.98  qbf_prep_cycles:                        0
% 2.19/0.98  
% 2.19/0.98  ------ BMC1
% 2.19/0.98  
% 2.19/0.98  bmc1_current_bound:                     -1
% 2.19/0.98  bmc1_last_solved_bound:                 -1
% 2.19/0.98  bmc1_unsat_core_size:                   -1
% 2.19/0.98  bmc1_unsat_core_parents_size:           -1
% 2.19/0.98  bmc1_merge_next_fun:                    0
% 2.19/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.19/0.98  
% 2.19/0.98  ------ Instantiation
% 2.19/0.98  
% 2.19/0.98  inst_num_of_clauses:                    196
% 2.19/0.98  inst_num_in_passive:                    67
% 2.19/0.98  inst_num_in_active:                     114
% 2.19/0.98  inst_num_in_unprocessed:                14
% 2.19/0.98  inst_num_of_loops:                      138
% 2.19/0.98  inst_num_of_learning_restarts:          0
% 2.19/0.98  inst_num_moves_active_passive:          20
% 2.19/0.98  inst_lit_activity:                      0
% 2.19/0.98  inst_lit_activity_moves:                0
% 2.19/0.98  inst_num_tautologies:                   0
% 2.19/0.98  inst_num_prop_implied:                  0
% 2.19/0.98  inst_num_existing_simplified:           0
% 2.19/0.98  inst_num_eq_res_simplified:             0
% 2.19/0.98  inst_num_child_elim:                    0
% 2.19/0.98  inst_num_of_dismatching_blockings:      58
% 2.19/0.98  inst_num_of_non_proper_insts:           224
% 2.19/0.98  inst_num_of_duplicates:                 0
% 2.19/0.98  inst_inst_num_from_inst_to_res:         0
% 2.19/0.98  inst_dismatching_checking_time:         0.
% 2.19/0.98  
% 2.19/0.98  ------ Resolution
% 2.19/0.98  
% 2.19/0.98  res_num_of_clauses:                     0
% 2.19/0.98  res_num_in_passive:                     0
% 2.19/0.98  res_num_in_active:                      0
% 2.19/0.98  res_num_of_loops:                       84
% 2.19/0.98  res_forward_subset_subsumed:            28
% 2.19/0.98  res_backward_subset_subsumed:           2
% 2.19/0.98  res_forward_subsumed:                   0
% 2.19/0.98  res_backward_subsumed:                  0
% 2.19/0.98  res_forward_subsumption_resolution:     0
% 2.19/0.98  res_backward_subsumption_resolution:    0
% 2.19/0.98  res_clause_to_clause_subsumption:       179
% 2.19/0.98  res_orphan_elimination:                 0
% 2.19/0.98  res_tautology_del:                      23
% 2.19/0.98  res_num_eq_res_simplified:              0
% 2.19/0.98  res_num_sel_changes:                    0
% 2.19/0.98  res_moves_from_active_to_pass:          0
% 2.19/0.98  
% 2.19/0.98  ------ Superposition
% 2.19/0.98  
% 2.19/0.98  sup_time_total:                         0.
% 2.19/0.98  sup_time_generating:                    0.
% 2.19/0.98  sup_time_sim_full:                      0.
% 2.19/0.98  sup_time_sim_immed:                     0.
% 2.19/0.98  
% 2.19/0.98  sup_num_of_clauses:                     33
% 2.19/0.98  sup_num_in_active:                      26
% 2.19/0.98  sup_num_in_passive:                     7
% 2.19/0.98  sup_num_of_loops:                       26
% 2.19/0.98  sup_fw_superposition:                   17
% 2.19/0.98  sup_bw_superposition:                   9
% 2.19/0.98  sup_immediate_simplified:               1
% 2.19/0.98  sup_given_eliminated:                   0
% 2.19/0.98  comparisons_done:                       0
% 2.19/0.98  comparisons_avoided:                    0
% 2.19/0.98  
% 2.19/0.98  ------ Simplifications
% 2.19/0.98  
% 2.19/0.98  
% 2.19/0.98  sim_fw_subset_subsumed:                 0
% 2.19/0.98  sim_bw_subset_subsumed:                 0
% 2.19/0.98  sim_fw_subsumed:                        2
% 2.19/0.98  sim_bw_subsumed:                        0
% 2.19/0.98  sim_fw_subsumption_res:                 0
% 2.19/0.98  sim_bw_subsumption_res:                 0
% 2.19/0.98  sim_tautology_del:                      2
% 2.19/0.98  sim_eq_tautology_del:                   2
% 2.19/0.98  sim_eq_res_simp:                        0
% 2.19/0.98  sim_fw_demodulated:                     0
% 2.19/0.98  sim_bw_demodulated:                     0
% 2.19/0.98  sim_light_normalised:                   0
% 2.19/0.98  sim_joinable_taut:                      0
% 2.19/0.98  sim_joinable_simp:                      0
% 2.19/0.98  sim_ac_normalised:                      0
% 2.19/0.98  sim_smt_subsumption:                    0
% 2.19/0.98  
%------------------------------------------------------------------------------
