%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:53:38 EST 2020

% Result     : Theorem 2.72s
% Output     : CNFRefutation 2.72s
% Verified   : 
% Statistics : Number of formulae       :  132 (1191 expanded)
%              Number of clauses        :   64 ( 290 expanded)
%              Number of leaves         :   17 ( 305 expanded)
%              Depth                    :   21
%              Number of atoms          :  334 (3662 expanded)
%              Number of equality atoms :   86 ( 627 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f19,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
          <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X0,X1)
            <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(X0,X1)
          <~> r1_ordinal1(k1_ordinal1(X0),X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f43,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
            | ~ r2_hidden(X0,X1) )
          & ( r1_ordinal1(k1_ordinal1(X0),X1)
            | r2_hidden(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f44,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
            | ~ r2_hidden(X0,X1) )
          & ( r1_ordinal1(k1_ordinal1(X0),X1)
            | r2_hidden(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f43])).

fof(f46,plain,(
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

fof(f45,plain,
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

fof(f47,plain,
    ( ( ~ r1_ordinal1(k1_ordinal1(sK0),sK1)
      | ~ r2_hidden(sK0,sK1) )
    & ( r1_ordinal1(k1_ordinal1(sK0),sK1)
      | r2_hidden(sK0,sK1) )
    & v3_ordinal1(sK1)
    & v3_ordinal1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f44,f46,f45])).

fof(f77,plain,
    ( ~ r1_ordinal1(k1_ordinal1(sK0),sK1)
    | ~ r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f13,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f78,plain,(
    ! [X0] : k3_tarski(k2_tarski(X0,k2_tarski(X0,X0))) = k1_ordinal1(X0) ),
    inference(definition_unfolding,[],[f65,f63,f55])).

fof(f91,plain,
    ( ~ r1_ordinal1(k3_tarski(k2_tarski(sK0,k2_tarski(sK0,sK0))),sK1)
    | ~ r2_hidden(sK0,sK1) ),
    inference(definition_unfolding,[],[f77,f78])).

fof(f74,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f75,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f18,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k1_ordinal1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f73,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f90,plain,(
    ! [X0] :
      ( v3_ordinal1(k3_tarski(k2_tarski(X0,k2_tarski(X0,X0))))
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f73,f78])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f84,plain,(
    ! [X0,X1] :
      ( k2_tarski(X0,X0) = k3_xboole_0(X1,k2_tarski(X0,X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f58,f55,f55])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f76,plain,
    ( r1_ordinal1(k1_ordinal1(sK0),sK1)
    | r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f92,plain,
    ( r1_ordinal1(k3_tarski(k2_tarski(sK0,k2_tarski(sK0,sK0))),sK1)
    | r2_hidden(sK0,sK1) ),
    inference(definition_unfolding,[],[f76,f78])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k3_tarski(k2_tarski(X0,X1)),X2) ) ),
    inference(definition_unfolding,[],[f52,f63])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f79,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k2_tarski(X0,X0),k2_tarski(X1,X1))) ),
    inference(definition_unfolding,[],[f54,f63,f55,f55])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
    <=> ( X0 = X1
        | r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(flattening,[],[f41])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f87,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k3_tarski(k2_tarski(X1,k2_tarski(X1,X1))))
      | X0 != X1 ) ),
    inference(definition_unfolding,[],[f71,f78])).

fof(f95,plain,(
    ! [X1] : r2_hidden(X1,k3_tarski(k2_tarski(X1,k2_tarski(X1,X1)))) ),
    inference(equality_resolution,[],[f87])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X2,X0)
        & r1_tarski(k3_tarski(X0),X1) )
     => r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(k3_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(k3_tarski(X0),X1) ) ),
    inference(flattening,[],[f27])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(k3_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k2_tarski(X0,X0),X1) ) ),
    inference(definition_unfolding,[],[f56,f55])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k3_xboole_0(X0,k1_tarski(X1))
     => r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k2_tarski(X1,X1) != k3_xboole_0(X0,k2_tarski(X1,X1)) ) ),
    inference(definition_unfolding,[],[f62,f55,f55])).

fof(f69,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f89,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k3_tarski(k2_tarski(X1,k2_tarski(X1,X1)))) ) ),
    inference(definition_unfolding,[],[f69,f78])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_21,plain,
    ( r1_ordinal1(X0,X1)
    | r2_hidden(X1,X0)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_23,negated_conjecture,
    ( ~ r1_ordinal1(k3_tarski(k2_tarski(sK0,k2_tarski(sK0,sK0))),sK1)
    | ~ r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_210,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ r1_ordinal1(k3_tarski(k2_tarski(sK0,k2_tarski(sK0,sK0))),sK1) ),
    inference(prop_impl,[status(thm)],[c_23])).

cnf(c_211,plain,
    ( ~ r1_ordinal1(k3_tarski(k2_tarski(sK0,k2_tarski(sK0,sK0))),sK1)
    | ~ r2_hidden(sK0,sK1) ),
    inference(renaming,[status(thm)],[c_210])).

cnf(c_358,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK0,sK1)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1)
    | k3_tarski(k2_tarski(sK0,k2_tarski(sK0,sK0))) != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_211])).

cnf(c_359,plain,
    ( r2_hidden(sK1,k3_tarski(k2_tarski(sK0,k2_tarski(sK0,sK0))))
    | ~ r2_hidden(sK0,sK1)
    | ~ v3_ordinal1(k3_tarski(k2_tarski(sK0,k2_tarski(sK0,sK0))))
    | ~ v3_ordinal1(sK1) ),
    inference(unflattening,[status(thm)],[c_358])).

cnf(c_26,negated_conjecture,
    ( v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_25,negated_conjecture,
    ( v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_22,plain,
    ( ~ v3_ordinal1(X0)
    | v3_ordinal1(k3_tarski(k2_tarski(X0,k2_tarski(X0,X0)))) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_32,plain,
    ( v3_ordinal1(k3_tarski(k2_tarski(sK0,k2_tarski(sK0,sK0))))
    | ~ v3_ordinal1(sK0) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_361,plain,
    ( r2_hidden(sK1,k3_tarski(k2_tarski(sK0,k2_tarski(sK0,sK0))))
    | ~ r2_hidden(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_359,c_26,c_25,c_32])).

cnf(c_1177,plain,
    ( r2_hidden(sK1,k3_tarski(k2_tarski(sK0,k2_tarski(sK0,sK0)))) = iProver_top
    | r2_hidden(sK0,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_361])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,X1)
    | k3_xboole_0(X1,k2_tarski(X0,X0)) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1190,plain,
    ( k3_xboole_0(X0,k2_tarski(X1,X1)) = k2_tarski(X1,X1)
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4025,plain,
    ( k3_xboole_0(k3_tarski(k2_tarski(sK0,k2_tarski(sK0,sK0))),k2_tarski(sK1,sK1)) = k2_tarski(sK1,sK1)
    | r2_hidden(sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1177,c_1190])).

cnf(c_16,plain,
    ( ~ r1_ordinal1(X0,X1)
    | r1_tarski(X0,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_24,negated_conjecture,
    ( r1_ordinal1(k3_tarski(k2_tarski(sK0,k2_tarski(sK0,sK0))),sK1)
    | r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_212,plain,
    ( r2_hidden(sK0,sK1)
    | r1_ordinal1(k3_tarski(k2_tarski(sK0,k2_tarski(sK0,sK0))),sK1) ),
    inference(prop_impl,[status(thm)],[c_24])).

cnf(c_213,plain,
    ( r1_ordinal1(k3_tarski(k2_tarski(sK0,k2_tarski(sK0,sK0))),sK1)
    | r2_hidden(sK0,sK1) ),
    inference(renaming,[status(thm)],[c_212])).

cnf(c_386,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK0,sK1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0)
    | k3_tarski(k2_tarski(sK0,k2_tarski(sK0,sK0))) != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_213])).

cnf(c_387,plain,
    ( r1_tarski(k3_tarski(k2_tarski(sK0,k2_tarski(sK0,sK0))),sK1)
    | r2_hidden(sK0,sK1)
    | ~ v3_ordinal1(k3_tarski(k2_tarski(sK0,k2_tarski(sK0,sK0))))
    | ~ v3_ordinal1(sK1) ),
    inference(unflattening,[status(thm)],[c_386])).

cnf(c_506,plain,
    ( r2_hidden(sK0,sK1)
    | r1_tarski(k3_tarski(k2_tarski(sK0,k2_tarski(sK0,sK0))),sK1) ),
    inference(prop_impl,[status(thm)],[c_26,c_25,c_32,c_387])).

cnf(c_507,plain,
    ( r1_tarski(k3_tarski(k2_tarski(sK0,k2_tarski(sK0,sK0))),sK1)
    | r2_hidden(sK0,sK1) ),
    inference(renaming,[status(thm)],[c_506])).

cnf(c_1175,plain,
    ( r1_tarski(k3_tarski(k2_tarski(sK0,k2_tarski(sK0,sK0))),sK1) = iProver_top
    | r2_hidden(sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_507])).

cnf(c_5,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1194,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2256,plain,
    ( r1_tarski(sK0,sK1) = iProver_top
    | r2_hidden(sK0,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1175,c_1194])).

cnf(c_27,plain,
    ( v3_ordinal1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_28,plain,
    ( v3_ordinal1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_31,plain,
    ( v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(k3_tarski(k2_tarski(X0,k2_tarski(X0,X0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_33,plain,
    ( v3_ordinal1(k3_tarski(k2_tarski(sK0,k2_tarski(sK0,sK0)))) = iProver_top
    | v3_ordinal1(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_388,plain,
    ( r1_tarski(k3_tarski(k2_tarski(sK0,k2_tarski(sK0,sK0))),sK1) = iProver_top
    | r2_hidden(sK0,sK1) = iProver_top
    | v3_ordinal1(k3_tarski(k2_tarski(sK0,k2_tarski(sK0,sK0)))) != iProver_top
    | v3_ordinal1(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_387])).

cnf(c_0,plain,
    ( k3_tarski(k2_tarski(k2_tarski(X0,X0),k2_tarski(X1,X1))) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_18,plain,
    ( r2_hidden(X0,k3_tarski(k2_tarski(X0,k2_tarski(X0,X0)))) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1184,plain,
    ( r2_hidden(X0,k3_tarski(k2_tarski(X0,k2_tarski(X0,X0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1519,plain,
    ( r2_hidden(k2_tarski(X0,X0),k2_tarski(X0,k2_tarski(X0,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_1184])).

cnf(c_1521,plain,
    ( r2_hidden(k2_tarski(sK0,sK0),k2_tarski(sK0,k2_tarski(sK0,sK0))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1519])).

cnf(c_14,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k3_tarski(X2),X1)
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1387,plain,
    ( r1_tarski(k2_tarski(X0,X1),X2)
    | ~ r1_tarski(k3_tarski(X3),X2)
    | ~ r2_hidden(k2_tarski(X0,X1),X3) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1705,plain,
    ( r1_tarski(k2_tarski(X0,X1),X2)
    | ~ r1_tarski(k3_tarski(k2_tarski(X3,X4)),X2)
    | ~ r2_hidden(k2_tarski(X0,X1),k2_tarski(X3,X4)) ),
    inference(instantiation,[status(thm)],[c_1387])).

cnf(c_2499,plain,
    ( r1_tarski(k2_tarski(X0,X1),X2)
    | ~ r1_tarski(k3_tarski(k2_tarski(X3,k2_tarski(X0,X1))),X2)
    | ~ r2_hidden(k2_tarski(X0,X1),k2_tarski(X3,k2_tarski(X0,X1))) ),
    inference(instantiation,[status(thm)],[c_1705])).

cnf(c_9732,plain,
    ( r1_tarski(k2_tarski(sK0,sK0),sK1)
    | ~ r1_tarski(k3_tarski(k2_tarski(sK0,k2_tarski(sK0,sK0))),sK1)
    | ~ r2_hidden(k2_tarski(sK0,sK0),k2_tarski(sK0,k2_tarski(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_2499])).

cnf(c_9733,plain,
    ( r1_tarski(k2_tarski(sK0,sK0),sK1) = iProver_top
    | r1_tarski(k3_tarski(k2_tarski(sK0,k2_tarski(sK0,sK0))),sK1) != iProver_top
    | r2_hidden(k2_tarski(sK0,sK0),k2_tarski(sK0,k2_tarski(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9732])).

cnf(c_8,plain,
    ( ~ r1_tarski(k2_tarski(X0,X0),X1)
    | r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_11268,plain,
    ( ~ r1_tarski(k2_tarski(sK0,sK0),sK1)
    | r2_hidden(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_11269,plain,
    ( r1_tarski(k2_tarski(sK0,sK0),sK1) != iProver_top
    | r2_hidden(sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11268])).

cnf(c_11445,plain,
    ( r2_hidden(sK0,sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2256,c_27,c_28,c_33,c_388,c_1521,c_9733,c_11269])).

cnf(c_14077,plain,
    ( k3_xboole_0(k3_tarski(k2_tarski(sK0,k2_tarski(sK0,sK0))),k2_tarski(sK1,sK1)) = k2_tarski(sK1,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4025,c_27,c_28,c_33,c_388,c_1521,c_9733,c_11269])).

cnf(c_13,plain,
    ( r2_hidden(X0,X1)
    | k3_xboole_0(X1,k2_tarski(X0,X0)) != k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1186,plain,
    ( k3_xboole_0(X0,k2_tarski(X1,X1)) != k2_tarski(X1,X1)
    | r2_hidden(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_14080,plain,
    ( r2_hidden(sK1,k3_tarski(k2_tarski(sK0,k2_tarski(sK0,sK0)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_14077,c_1186])).

cnf(c_20,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_tarski(k2_tarski(X1,k2_tarski(X1,X1))))
    | X1 = X0 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1182,plain,
    ( X0 = X1
    | r2_hidden(X1,X0) = iProver_top
    | r2_hidden(X1,k3_tarski(k2_tarski(X0,k2_tarski(X0,X0)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_14365,plain,
    ( sK1 = sK0
    | r2_hidden(sK1,sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_14080,c_1182])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1342,plain,
    ( ~ r2_hidden(sK1,sK0)
    | ~ r2_hidden(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1343,plain,
    ( r2_hidden(sK1,sK0) != iProver_top
    | r2_hidden(sK0,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1342])).

cnf(c_8514,plain,
    ( sK1 = sK0
    | r2_hidden(sK1,sK0) = iProver_top
    | r2_hidden(sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1177,c_1182])).

cnf(c_14375,plain,
    ( sK1 = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_14365,c_27,c_28,c_33,c_388,c_1343,c_1521,c_8514,c_9733,c_11269])).

cnf(c_1197,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_11451,plain,
    ( r2_hidden(sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_11445,c_1197])).

cnf(c_14381,plain,
    ( r2_hidden(sK0,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_14375,c_11451])).

cnf(c_14382,plain,
    ( r2_hidden(sK0,sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_14375,c_11445])).

cnf(c_14400,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_14381,c_14382])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:17:44 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.72/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.72/0.99  
% 2.72/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.72/0.99  
% 2.72/0.99  ------  iProver source info
% 2.72/0.99  
% 2.72/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.72/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.72/0.99  git: non_committed_changes: false
% 2.72/0.99  git: last_make_outside_of_git: false
% 2.72/0.99  
% 2.72/0.99  ------ 
% 2.72/0.99  
% 2.72/0.99  ------ Input Options
% 2.72/0.99  
% 2.72/0.99  --out_options                           all
% 2.72/0.99  --tptp_safe_out                         true
% 2.72/0.99  --problem_path                          ""
% 2.72/0.99  --include_path                          ""
% 2.72/0.99  --clausifier                            res/vclausify_rel
% 2.72/0.99  --clausifier_options                    --mode clausify
% 2.72/0.99  --stdin                                 false
% 2.72/0.99  --stats_out                             all
% 2.72/0.99  
% 2.72/0.99  ------ General Options
% 2.72/0.99  
% 2.72/0.99  --fof                                   false
% 2.72/0.99  --time_out_real                         305.
% 2.72/0.99  --time_out_virtual                      -1.
% 2.72/0.99  --symbol_type_check                     false
% 2.72/0.99  --clausify_out                          false
% 2.72/0.99  --sig_cnt_out                           false
% 2.72/0.99  --trig_cnt_out                          false
% 2.72/0.99  --trig_cnt_out_tolerance                1.
% 2.72/0.99  --trig_cnt_out_sk_spl                   false
% 2.72/0.99  --abstr_cl_out                          false
% 2.72/0.99  
% 2.72/0.99  ------ Global Options
% 2.72/0.99  
% 2.72/0.99  --schedule                              default
% 2.72/0.99  --add_important_lit                     false
% 2.72/0.99  --prop_solver_per_cl                    1000
% 2.72/0.99  --min_unsat_core                        false
% 2.72/0.99  --soft_assumptions                      false
% 2.72/0.99  --soft_lemma_size                       3
% 2.72/0.99  --prop_impl_unit_size                   0
% 2.72/0.99  --prop_impl_unit                        []
% 2.72/0.99  --share_sel_clauses                     true
% 2.72/0.99  --reset_solvers                         false
% 2.72/0.99  --bc_imp_inh                            [conj_cone]
% 2.72/0.99  --conj_cone_tolerance                   3.
% 2.72/0.99  --extra_neg_conj                        none
% 2.72/0.99  --large_theory_mode                     true
% 2.72/0.99  --prolific_symb_bound                   200
% 2.72/0.99  --lt_threshold                          2000
% 2.72/0.99  --clause_weak_htbl                      true
% 2.72/0.99  --gc_record_bc_elim                     false
% 2.72/0.99  
% 2.72/0.99  ------ Preprocessing Options
% 2.72/0.99  
% 2.72/0.99  --preprocessing_flag                    true
% 2.72/0.99  --time_out_prep_mult                    0.1
% 2.72/0.99  --splitting_mode                        input
% 2.72/0.99  --splitting_grd                         true
% 2.72/0.99  --splitting_cvd                         false
% 2.72/0.99  --splitting_cvd_svl                     false
% 2.72/0.99  --splitting_nvd                         32
% 2.72/0.99  --sub_typing                            true
% 2.72/0.99  --prep_gs_sim                           true
% 2.72/0.99  --prep_unflatten                        true
% 2.72/0.99  --prep_res_sim                          true
% 2.72/0.99  --prep_upred                            true
% 2.72/0.99  --prep_sem_filter                       exhaustive
% 2.72/0.99  --prep_sem_filter_out                   false
% 2.72/0.99  --pred_elim                             true
% 2.72/0.99  --res_sim_input                         true
% 2.72/0.99  --eq_ax_congr_red                       true
% 2.72/0.99  --pure_diseq_elim                       true
% 2.72/0.99  --brand_transform                       false
% 2.72/0.99  --non_eq_to_eq                          false
% 2.72/0.99  --prep_def_merge                        true
% 2.72/0.99  --prep_def_merge_prop_impl              false
% 2.72/0.99  --prep_def_merge_mbd                    true
% 2.72/0.99  --prep_def_merge_tr_red                 false
% 2.72/0.99  --prep_def_merge_tr_cl                  false
% 2.72/0.99  --smt_preprocessing                     true
% 2.72/0.99  --smt_ac_axioms                         fast
% 2.72/0.99  --preprocessed_out                      false
% 2.72/0.99  --preprocessed_stats                    false
% 2.72/0.99  
% 2.72/0.99  ------ Abstraction refinement Options
% 2.72/0.99  
% 2.72/0.99  --abstr_ref                             []
% 2.72/0.99  --abstr_ref_prep                        false
% 2.72/0.99  --abstr_ref_until_sat                   false
% 2.72/0.99  --abstr_ref_sig_restrict                funpre
% 2.72/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.72/0.99  --abstr_ref_under                       []
% 2.72/0.99  
% 2.72/0.99  ------ SAT Options
% 2.72/0.99  
% 2.72/0.99  --sat_mode                              false
% 2.72/0.99  --sat_fm_restart_options                ""
% 2.72/0.99  --sat_gr_def                            false
% 2.72/0.99  --sat_epr_types                         true
% 2.72/0.99  --sat_non_cyclic_types                  false
% 2.72/0.99  --sat_finite_models                     false
% 2.72/0.99  --sat_fm_lemmas                         false
% 2.72/0.99  --sat_fm_prep                           false
% 2.72/0.99  --sat_fm_uc_incr                        true
% 2.72/0.99  --sat_out_model                         small
% 2.72/0.99  --sat_out_clauses                       false
% 2.72/0.99  
% 2.72/0.99  ------ QBF Options
% 2.72/0.99  
% 2.72/0.99  --qbf_mode                              false
% 2.72/0.99  --qbf_elim_univ                         false
% 2.72/0.99  --qbf_dom_inst                          none
% 2.72/0.99  --qbf_dom_pre_inst                      false
% 2.72/0.99  --qbf_sk_in                             false
% 2.72/0.99  --qbf_pred_elim                         true
% 2.72/0.99  --qbf_split                             512
% 2.72/0.99  
% 2.72/0.99  ------ BMC1 Options
% 2.72/0.99  
% 2.72/0.99  --bmc1_incremental                      false
% 2.72/0.99  --bmc1_axioms                           reachable_all
% 2.72/0.99  --bmc1_min_bound                        0
% 2.72/0.99  --bmc1_max_bound                        -1
% 2.72/0.99  --bmc1_max_bound_default                -1
% 2.72/0.99  --bmc1_symbol_reachability              true
% 2.72/0.99  --bmc1_property_lemmas                  false
% 2.72/0.99  --bmc1_k_induction                      false
% 2.72/0.99  --bmc1_non_equiv_states                 false
% 2.72/0.99  --bmc1_deadlock                         false
% 2.72/0.99  --bmc1_ucm                              false
% 2.72/0.99  --bmc1_add_unsat_core                   none
% 2.72/0.99  --bmc1_unsat_core_children              false
% 2.72/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.72/0.99  --bmc1_out_stat                         full
% 2.72/0.99  --bmc1_ground_init                      false
% 2.72/0.99  --bmc1_pre_inst_next_state              false
% 2.72/0.99  --bmc1_pre_inst_state                   false
% 2.72/0.99  --bmc1_pre_inst_reach_state             false
% 2.72/0.99  --bmc1_out_unsat_core                   false
% 2.72/0.99  --bmc1_aig_witness_out                  false
% 2.72/0.99  --bmc1_verbose                          false
% 2.72/0.99  --bmc1_dump_clauses_tptp                false
% 2.72/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.72/0.99  --bmc1_dump_file                        -
% 2.72/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.72/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.72/0.99  --bmc1_ucm_extend_mode                  1
% 2.72/0.99  --bmc1_ucm_init_mode                    2
% 2.72/0.99  --bmc1_ucm_cone_mode                    none
% 2.72/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.72/0.99  --bmc1_ucm_relax_model                  4
% 2.72/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.72/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.72/0.99  --bmc1_ucm_layered_model                none
% 2.72/0.99  --bmc1_ucm_max_lemma_size               10
% 2.72/0.99  
% 2.72/0.99  ------ AIG Options
% 2.72/0.99  
% 2.72/0.99  --aig_mode                              false
% 2.72/0.99  
% 2.72/0.99  ------ Instantiation Options
% 2.72/0.99  
% 2.72/0.99  --instantiation_flag                    true
% 2.72/0.99  --inst_sos_flag                         false
% 2.72/0.99  --inst_sos_phase                        true
% 2.72/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.72/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.72/0.99  --inst_lit_sel_side                     num_symb
% 2.72/0.99  --inst_solver_per_active                1400
% 2.72/0.99  --inst_solver_calls_frac                1.
% 2.72/0.99  --inst_passive_queue_type               priority_queues
% 2.72/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.72/0.99  --inst_passive_queues_freq              [25;2]
% 2.72/0.99  --inst_dismatching                      true
% 2.72/0.99  --inst_eager_unprocessed_to_passive     true
% 2.72/0.99  --inst_prop_sim_given                   true
% 2.72/0.99  --inst_prop_sim_new                     false
% 2.72/0.99  --inst_subs_new                         false
% 2.72/0.99  --inst_eq_res_simp                      false
% 2.72/0.99  --inst_subs_given                       false
% 2.72/0.99  --inst_orphan_elimination               true
% 2.72/0.99  --inst_learning_loop_flag               true
% 2.72/0.99  --inst_learning_start                   3000
% 2.72/0.99  --inst_learning_factor                  2
% 2.72/0.99  --inst_start_prop_sim_after_learn       3
% 2.72/0.99  --inst_sel_renew                        solver
% 2.72/0.99  --inst_lit_activity_flag                true
% 2.72/0.99  --inst_restr_to_given                   false
% 2.72/0.99  --inst_activity_threshold               500
% 2.72/0.99  --inst_out_proof                        true
% 2.72/0.99  
% 2.72/0.99  ------ Resolution Options
% 2.72/0.99  
% 2.72/0.99  --resolution_flag                       true
% 2.72/0.99  --res_lit_sel                           adaptive
% 2.72/0.99  --res_lit_sel_side                      none
% 2.72/0.99  --res_ordering                          kbo
% 2.72/0.99  --res_to_prop_solver                    active
% 2.72/0.99  --res_prop_simpl_new                    false
% 2.72/0.99  --res_prop_simpl_given                  true
% 2.72/0.99  --res_passive_queue_type                priority_queues
% 2.72/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.72/0.99  --res_passive_queues_freq               [15;5]
% 2.72/0.99  --res_forward_subs                      full
% 2.72/0.99  --res_backward_subs                     full
% 2.72/0.99  --res_forward_subs_resolution           true
% 2.72/0.99  --res_backward_subs_resolution          true
% 2.72/0.99  --res_orphan_elimination                true
% 2.72/0.99  --res_time_limit                        2.
% 2.72/0.99  --res_out_proof                         true
% 2.72/0.99  
% 2.72/0.99  ------ Superposition Options
% 2.72/0.99  
% 2.72/0.99  --superposition_flag                    true
% 2.72/0.99  --sup_passive_queue_type                priority_queues
% 2.72/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.72/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.72/0.99  --demod_completeness_check              fast
% 2.72/0.99  --demod_use_ground                      true
% 2.72/0.99  --sup_to_prop_solver                    passive
% 2.72/0.99  --sup_prop_simpl_new                    true
% 2.72/0.99  --sup_prop_simpl_given                  true
% 2.72/0.99  --sup_fun_splitting                     false
% 2.72/0.99  --sup_smt_interval                      50000
% 2.72/0.99  
% 2.72/0.99  ------ Superposition Simplification Setup
% 2.72/0.99  
% 2.72/0.99  --sup_indices_passive                   []
% 2.72/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.72/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.72/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.72/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.72/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.72/0.99  --sup_full_bw                           [BwDemod]
% 2.72/0.99  --sup_immed_triv                        [TrivRules]
% 2.72/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.72/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.72/0.99  --sup_immed_bw_main                     []
% 2.72/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.72/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.72/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.72/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.72/0.99  
% 2.72/0.99  ------ Combination Options
% 2.72/0.99  
% 2.72/0.99  --comb_res_mult                         3
% 2.72/0.99  --comb_sup_mult                         2
% 2.72/0.99  --comb_inst_mult                        10
% 2.72/0.99  
% 2.72/0.99  ------ Debug Options
% 2.72/0.99  
% 2.72/0.99  --dbg_backtrace                         false
% 2.72/0.99  --dbg_dump_prop_clauses                 false
% 2.72/0.99  --dbg_dump_prop_clauses_file            -
% 2.72/0.99  --dbg_out_stat                          false
% 2.72/0.99  ------ Parsing...
% 2.72/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.72/0.99  
% 2.72/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.72/0.99  
% 2.72/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.72/0.99  
% 2.72/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.72/0.99  ------ Proving...
% 2.72/0.99  ------ Problem Properties 
% 2.72/0.99  
% 2.72/0.99  
% 2.72/0.99  clauses                                 24
% 2.72/0.99  conjectures                             2
% 2.72/0.99  EPR                                     6
% 2.72/0.99  Horn                                    21
% 2.72/0.99  unary                                   5
% 2.72/0.99  binary                                  13
% 2.72/0.99  lits                                    50
% 2.72/0.99  lits eq                                 5
% 2.72/0.99  fd_pure                                 0
% 2.72/0.99  fd_pseudo                               0
% 2.72/0.99  fd_cond                                 0
% 2.72/0.99  fd_pseudo_cond                          2
% 2.72/0.99  AC symbols                              0
% 2.72/0.99  
% 2.72/0.99  ------ Schedule dynamic 5 is on 
% 2.72/0.99  
% 2.72/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.72/0.99  
% 2.72/0.99  
% 2.72/0.99  ------ 
% 2.72/0.99  Current options:
% 2.72/0.99  ------ 
% 2.72/0.99  
% 2.72/0.99  ------ Input Options
% 2.72/0.99  
% 2.72/0.99  --out_options                           all
% 2.72/0.99  --tptp_safe_out                         true
% 2.72/0.99  --problem_path                          ""
% 2.72/0.99  --include_path                          ""
% 2.72/0.99  --clausifier                            res/vclausify_rel
% 2.72/0.99  --clausifier_options                    --mode clausify
% 2.72/0.99  --stdin                                 false
% 2.72/0.99  --stats_out                             all
% 2.72/0.99  
% 2.72/0.99  ------ General Options
% 2.72/0.99  
% 2.72/0.99  --fof                                   false
% 2.72/0.99  --time_out_real                         305.
% 2.72/0.99  --time_out_virtual                      -1.
% 2.72/0.99  --symbol_type_check                     false
% 2.72/0.99  --clausify_out                          false
% 2.72/0.99  --sig_cnt_out                           false
% 2.72/0.99  --trig_cnt_out                          false
% 2.72/0.99  --trig_cnt_out_tolerance                1.
% 2.72/0.99  --trig_cnt_out_sk_spl                   false
% 2.72/0.99  --abstr_cl_out                          false
% 2.72/0.99  
% 2.72/0.99  ------ Global Options
% 2.72/0.99  
% 2.72/0.99  --schedule                              default
% 2.72/0.99  --add_important_lit                     false
% 2.72/0.99  --prop_solver_per_cl                    1000
% 2.72/0.99  --min_unsat_core                        false
% 2.72/0.99  --soft_assumptions                      false
% 2.72/0.99  --soft_lemma_size                       3
% 2.72/0.99  --prop_impl_unit_size                   0
% 2.72/0.99  --prop_impl_unit                        []
% 2.72/0.99  --share_sel_clauses                     true
% 2.72/0.99  --reset_solvers                         false
% 2.72/0.99  --bc_imp_inh                            [conj_cone]
% 2.72/0.99  --conj_cone_tolerance                   3.
% 2.72/0.99  --extra_neg_conj                        none
% 2.72/0.99  --large_theory_mode                     true
% 2.72/0.99  --prolific_symb_bound                   200
% 2.72/0.99  --lt_threshold                          2000
% 2.72/0.99  --clause_weak_htbl                      true
% 2.72/0.99  --gc_record_bc_elim                     false
% 2.72/0.99  
% 2.72/0.99  ------ Preprocessing Options
% 2.72/0.99  
% 2.72/0.99  --preprocessing_flag                    true
% 2.72/0.99  --time_out_prep_mult                    0.1
% 2.72/0.99  --splitting_mode                        input
% 2.72/0.99  --splitting_grd                         true
% 2.72/0.99  --splitting_cvd                         false
% 2.72/0.99  --splitting_cvd_svl                     false
% 2.72/0.99  --splitting_nvd                         32
% 2.72/0.99  --sub_typing                            true
% 2.72/0.99  --prep_gs_sim                           true
% 2.72/0.99  --prep_unflatten                        true
% 2.72/0.99  --prep_res_sim                          true
% 2.72/0.99  --prep_upred                            true
% 2.72/0.99  --prep_sem_filter                       exhaustive
% 2.72/0.99  --prep_sem_filter_out                   false
% 2.72/0.99  --pred_elim                             true
% 2.72/0.99  --res_sim_input                         true
% 2.72/0.99  --eq_ax_congr_red                       true
% 2.72/0.99  --pure_diseq_elim                       true
% 2.72/0.99  --brand_transform                       false
% 2.72/0.99  --non_eq_to_eq                          false
% 2.72/0.99  --prep_def_merge                        true
% 2.72/0.99  --prep_def_merge_prop_impl              false
% 2.72/0.99  --prep_def_merge_mbd                    true
% 2.72/0.99  --prep_def_merge_tr_red                 false
% 2.72/0.99  --prep_def_merge_tr_cl                  false
% 2.72/0.99  --smt_preprocessing                     true
% 2.72/0.99  --smt_ac_axioms                         fast
% 2.72/0.99  --preprocessed_out                      false
% 2.72/0.99  --preprocessed_stats                    false
% 2.72/0.99  
% 2.72/0.99  ------ Abstraction refinement Options
% 2.72/0.99  
% 2.72/0.99  --abstr_ref                             []
% 2.72/0.99  --abstr_ref_prep                        false
% 2.72/0.99  --abstr_ref_until_sat                   false
% 2.72/0.99  --abstr_ref_sig_restrict                funpre
% 2.72/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.72/0.99  --abstr_ref_under                       []
% 2.72/0.99  
% 2.72/0.99  ------ SAT Options
% 2.72/0.99  
% 2.72/0.99  --sat_mode                              false
% 2.72/0.99  --sat_fm_restart_options                ""
% 2.72/0.99  --sat_gr_def                            false
% 2.72/0.99  --sat_epr_types                         true
% 2.72/0.99  --sat_non_cyclic_types                  false
% 2.72/0.99  --sat_finite_models                     false
% 2.72/0.99  --sat_fm_lemmas                         false
% 2.72/0.99  --sat_fm_prep                           false
% 2.72/0.99  --sat_fm_uc_incr                        true
% 2.72/0.99  --sat_out_model                         small
% 2.72/0.99  --sat_out_clauses                       false
% 2.72/0.99  
% 2.72/0.99  ------ QBF Options
% 2.72/0.99  
% 2.72/0.99  --qbf_mode                              false
% 2.72/0.99  --qbf_elim_univ                         false
% 2.72/0.99  --qbf_dom_inst                          none
% 2.72/0.99  --qbf_dom_pre_inst                      false
% 2.72/0.99  --qbf_sk_in                             false
% 2.72/0.99  --qbf_pred_elim                         true
% 2.72/0.99  --qbf_split                             512
% 2.72/0.99  
% 2.72/0.99  ------ BMC1 Options
% 2.72/0.99  
% 2.72/0.99  --bmc1_incremental                      false
% 2.72/0.99  --bmc1_axioms                           reachable_all
% 2.72/0.99  --bmc1_min_bound                        0
% 2.72/0.99  --bmc1_max_bound                        -1
% 2.72/0.99  --bmc1_max_bound_default                -1
% 2.72/0.99  --bmc1_symbol_reachability              true
% 2.72/0.99  --bmc1_property_lemmas                  false
% 2.72/0.99  --bmc1_k_induction                      false
% 2.72/0.99  --bmc1_non_equiv_states                 false
% 2.72/0.99  --bmc1_deadlock                         false
% 2.72/0.99  --bmc1_ucm                              false
% 2.72/0.99  --bmc1_add_unsat_core                   none
% 2.72/0.99  --bmc1_unsat_core_children              false
% 2.72/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.72/0.99  --bmc1_out_stat                         full
% 2.72/0.99  --bmc1_ground_init                      false
% 2.72/0.99  --bmc1_pre_inst_next_state              false
% 2.72/0.99  --bmc1_pre_inst_state                   false
% 2.72/0.99  --bmc1_pre_inst_reach_state             false
% 2.72/0.99  --bmc1_out_unsat_core                   false
% 2.72/0.99  --bmc1_aig_witness_out                  false
% 2.72/0.99  --bmc1_verbose                          false
% 2.72/0.99  --bmc1_dump_clauses_tptp                false
% 2.72/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.72/0.99  --bmc1_dump_file                        -
% 2.72/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.72/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.72/0.99  --bmc1_ucm_extend_mode                  1
% 2.72/0.99  --bmc1_ucm_init_mode                    2
% 2.72/0.99  --bmc1_ucm_cone_mode                    none
% 2.72/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.72/0.99  --bmc1_ucm_relax_model                  4
% 2.72/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.72/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.72/0.99  --bmc1_ucm_layered_model                none
% 2.72/0.99  --bmc1_ucm_max_lemma_size               10
% 2.72/0.99  
% 2.72/0.99  ------ AIG Options
% 2.72/0.99  
% 2.72/0.99  --aig_mode                              false
% 2.72/0.99  
% 2.72/0.99  ------ Instantiation Options
% 2.72/0.99  
% 2.72/0.99  --instantiation_flag                    true
% 2.72/0.99  --inst_sos_flag                         false
% 2.72/0.99  --inst_sos_phase                        true
% 2.72/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.72/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.72/0.99  --inst_lit_sel_side                     none
% 2.72/0.99  --inst_solver_per_active                1400
% 2.72/0.99  --inst_solver_calls_frac                1.
% 2.72/0.99  --inst_passive_queue_type               priority_queues
% 2.72/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.72/0.99  --inst_passive_queues_freq              [25;2]
% 2.72/0.99  --inst_dismatching                      true
% 2.72/0.99  --inst_eager_unprocessed_to_passive     true
% 2.72/0.99  --inst_prop_sim_given                   true
% 2.72/0.99  --inst_prop_sim_new                     false
% 2.72/0.99  --inst_subs_new                         false
% 2.72/0.99  --inst_eq_res_simp                      false
% 2.72/0.99  --inst_subs_given                       false
% 2.72/0.99  --inst_orphan_elimination               true
% 2.72/0.99  --inst_learning_loop_flag               true
% 2.72/0.99  --inst_learning_start                   3000
% 2.72/0.99  --inst_learning_factor                  2
% 2.72/0.99  --inst_start_prop_sim_after_learn       3
% 2.72/0.99  --inst_sel_renew                        solver
% 2.72/0.99  --inst_lit_activity_flag                true
% 2.72/0.99  --inst_restr_to_given                   false
% 2.72/0.99  --inst_activity_threshold               500
% 2.72/0.99  --inst_out_proof                        true
% 2.72/0.99  
% 2.72/0.99  ------ Resolution Options
% 2.72/0.99  
% 2.72/0.99  --resolution_flag                       false
% 2.72/0.99  --res_lit_sel                           adaptive
% 2.72/0.99  --res_lit_sel_side                      none
% 2.72/0.99  --res_ordering                          kbo
% 2.72/0.99  --res_to_prop_solver                    active
% 2.72/0.99  --res_prop_simpl_new                    false
% 2.72/0.99  --res_prop_simpl_given                  true
% 2.72/0.99  --res_passive_queue_type                priority_queues
% 2.72/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.72/0.99  --res_passive_queues_freq               [15;5]
% 2.72/0.99  --res_forward_subs                      full
% 2.72/0.99  --res_backward_subs                     full
% 2.72/0.99  --res_forward_subs_resolution           true
% 2.72/0.99  --res_backward_subs_resolution          true
% 2.72/0.99  --res_orphan_elimination                true
% 2.72/0.99  --res_time_limit                        2.
% 2.72/0.99  --res_out_proof                         true
% 2.72/0.99  
% 2.72/0.99  ------ Superposition Options
% 2.72/0.99  
% 2.72/0.99  --superposition_flag                    true
% 2.72/0.99  --sup_passive_queue_type                priority_queues
% 2.72/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.72/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.72/0.99  --demod_completeness_check              fast
% 2.72/0.99  --demod_use_ground                      true
% 2.72/0.99  --sup_to_prop_solver                    passive
% 2.72/0.99  --sup_prop_simpl_new                    true
% 2.72/0.99  --sup_prop_simpl_given                  true
% 2.72/0.99  --sup_fun_splitting                     false
% 2.72/0.99  --sup_smt_interval                      50000
% 2.72/0.99  
% 2.72/0.99  ------ Superposition Simplification Setup
% 2.72/0.99  
% 2.72/0.99  --sup_indices_passive                   []
% 2.72/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.72/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.72/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.72/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.72/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.72/0.99  --sup_full_bw                           [BwDemod]
% 2.72/0.99  --sup_immed_triv                        [TrivRules]
% 2.72/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.72/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.72/0.99  --sup_immed_bw_main                     []
% 2.72/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.72/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.72/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.72/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.72/0.99  
% 2.72/0.99  ------ Combination Options
% 2.72/0.99  
% 2.72/0.99  --comb_res_mult                         3
% 2.72/0.99  --comb_sup_mult                         2
% 2.72/0.99  --comb_inst_mult                        10
% 2.72/0.99  
% 2.72/0.99  ------ Debug Options
% 2.72/0.99  
% 2.72/0.99  --dbg_backtrace                         false
% 2.72/0.99  --dbg_dump_prop_clauses                 false
% 2.72/0.99  --dbg_dump_prop_clauses_file            -
% 2.72/0.99  --dbg_out_stat                          false
% 2.72/0.99  
% 2.72/0.99  
% 2.72/0.99  
% 2.72/0.99  
% 2.72/0.99  ------ Proving...
% 2.72/0.99  
% 2.72/0.99  
% 2.72/0.99  % SZS status Theorem for theBenchmark.p
% 2.72/0.99  
% 2.72/0.99   Resolution empty clause
% 2.72/0.99  
% 2.72/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.72/0.99  
% 2.72/0.99  fof(f17,axiom,(
% 2.72/0.99    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 2.72/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.72/0.99  
% 2.72/0.99  fof(f31,plain,(
% 2.72/0.99    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 2.72/0.99    inference(ennf_transformation,[],[f17])).
% 2.72/0.99  
% 2.72/0.99  fof(f32,plain,(
% 2.72/0.99    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 2.72/0.99    inference(flattening,[],[f31])).
% 2.72/0.99  
% 2.72/0.99  fof(f72,plain,(
% 2.72/0.99    ( ! [X0,X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 2.72/0.99    inference(cnf_transformation,[],[f32])).
% 2.72/0.99  
% 2.72/0.99  fof(f19,conjecture,(
% 2.72/0.99    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 2.72/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.72/0.99  
% 2.72/0.99  fof(f20,negated_conjecture,(
% 2.72/0.99    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 2.72/0.99    inference(negated_conjecture,[],[f19])).
% 2.72/0.99  
% 2.72/0.99  fof(f34,plain,(
% 2.72/0.99    ? [X0] : (? [X1] : ((r2_hidden(X0,X1) <~> r1_ordinal1(k1_ordinal1(X0),X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 2.72/0.99    inference(ennf_transformation,[],[f20])).
% 2.72/0.99  
% 2.72/0.99  fof(f43,plain,(
% 2.72/0.99    ? [X0] : (? [X1] : (((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 2.72/0.99    inference(nnf_transformation,[],[f34])).
% 2.72/0.99  
% 2.72/0.99  fof(f44,plain,(
% 2.72/0.99    ? [X0] : (? [X1] : ((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 2.72/0.99    inference(flattening,[],[f43])).
% 2.72/0.99  
% 2.72/0.99  fof(f46,plain,(
% 2.72/0.99    ( ! [X0] : (? [X1] : ((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1)) & v3_ordinal1(X1)) => ((~r1_ordinal1(k1_ordinal1(X0),sK1) | ~r2_hidden(X0,sK1)) & (r1_ordinal1(k1_ordinal1(X0),sK1) | r2_hidden(X0,sK1)) & v3_ordinal1(sK1))) )),
% 2.72/0.99    introduced(choice_axiom,[])).
% 2.72/0.99  
% 2.72/0.99  fof(f45,plain,(
% 2.72/0.99    ? [X0] : (? [X1] : ((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : ((~r1_ordinal1(k1_ordinal1(sK0),X1) | ~r2_hidden(sK0,X1)) & (r1_ordinal1(k1_ordinal1(sK0),X1) | r2_hidden(sK0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(sK0))),
% 2.72/0.99    introduced(choice_axiom,[])).
% 2.72/0.99  
% 2.72/0.99  fof(f47,plain,(
% 2.72/0.99    ((~r1_ordinal1(k1_ordinal1(sK0),sK1) | ~r2_hidden(sK0,sK1)) & (r1_ordinal1(k1_ordinal1(sK0),sK1) | r2_hidden(sK0,sK1)) & v3_ordinal1(sK1)) & v3_ordinal1(sK0)),
% 2.72/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f44,f46,f45])).
% 2.72/0.99  
% 2.72/0.99  fof(f77,plain,(
% 2.72/0.99    ~r1_ordinal1(k1_ordinal1(sK0),sK1) | ~r2_hidden(sK0,sK1)),
% 2.72/0.99    inference(cnf_transformation,[],[f47])).
% 2.72/0.99  
% 2.72/0.99  fof(f13,axiom,(
% 2.72/0.99    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0)),
% 2.72/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.72/0.99  
% 2.72/0.99  fof(f65,plain,(
% 2.72/0.99    ( ! [X0] : (k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0)) )),
% 2.72/0.99    inference(cnf_transformation,[],[f13])).
% 2.72/0.99  
% 2.72/0.99  fof(f11,axiom,(
% 2.72/0.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.72/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.72/0.99  
% 2.72/0.99  fof(f63,plain,(
% 2.72/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.72/0.99    inference(cnf_transformation,[],[f11])).
% 2.72/0.99  
% 2.72/0.99  fof(f6,axiom,(
% 2.72/0.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.72/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.72/0.99  
% 2.72/0.99  fof(f55,plain,(
% 2.72/0.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.72/0.99    inference(cnf_transformation,[],[f6])).
% 2.72/0.99  
% 2.72/0.99  fof(f78,plain,(
% 2.72/0.99    ( ! [X0] : (k3_tarski(k2_tarski(X0,k2_tarski(X0,X0))) = k1_ordinal1(X0)) )),
% 2.72/0.99    inference(definition_unfolding,[],[f65,f63,f55])).
% 2.72/0.99  
% 2.72/0.99  fof(f91,plain,(
% 2.72/0.99    ~r1_ordinal1(k3_tarski(k2_tarski(sK0,k2_tarski(sK0,sK0))),sK1) | ~r2_hidden(sK0,sK1)),
% 2.72/0.99    inference(definition_unfolding,[],[f77,f78])).
% 2.72/0.99  
% 2.72/0.99  fof(f74,plain,(
% 2.72/0.99    v3_ordinal1(sK0)),
% 2.72/0.99    inference(cnf_transformation,[],[f47])).
% 2.72/0.99  
% 2.72/0.99  fof(f75,plain,(
% 2.72/0.99    v3_ordinal1(sK1)),
% 2.72/0.99    inference(cnf_transformation,[],[f47])).
% 2.72/0.99  
% 2.72/0.99  fof(f18,axiom,(
% 2.72/0.99    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k1_ordinal1(X0)))),
% 2.72/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.72/0.99  
% 2.72/0.99  fof(f33,plain,(
% 2.72/0.99    ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 2.72/0.99    inference(ennf_transformation,[],[f18])).
% 2.72/0.99  
% 2.72/0.99  fof(f73,plain,(
% 2.72/0.99    ( ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0)) )),
% 2.72/0.99    inference(cnf_transformation,[],[f33])).
% 2.72/0.99  
% 2.72/0.99  fof(f90,plain,(
% 2.72/0.99    ( ! [X0] : (v3_ordinal1(k3_tarski(k2_tarski(X0,k2_tarski(X0,X0)))) | ~v3_ordinal1(X0)) )),
% 2.72/0.99    inference(definition_unfolding,[],[f73,f78])).
% 2.72/0.99  
% 2.72/0.99  fof(f8,axiom,(
% 2.72/0.99    ! [X0,X1] : (r2_hidden(X0,X1) => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)))),
% 2.72/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.72/0.99  
% 2.72/0.99  fof(f25,plain,(
% 2.72/0.99    ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) | ~r2_hidden(X0,X1))),
% 2.72/0.99    inference(ennf_transformation,[],[f8])).
% 2.72/0.99  
% 2.72/0.99  fof(f58,plain,(
% 2.72/0.99    ( ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) | ~r2_hidden(X0,X1)) )),
% 2.72/0.99    inference(cnf_transformation,[],[f25])).
% 2.72/0.99  
% 2.72/0.99  fof(f84,plain,(
% 2.72/0.99    ( ! [X0,X1] : (k2_tarski(X0,X0) = k3_xboole_0(X1,k2_tarski(X0,X0)) | ~r2_hidden(X0,X1)) )),
% 2.72/0.99    inference(definition_unfolding,[],[f58,f55,f55])).
% 2.72/0.99  
% 2.72/0.99  fof(f14,axiom,(
% 2.72/0.99    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 2.72/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.72/0.99  
% 2.72/0.99  fof(f29,plain,(
% 2.72/0.99    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 2.72/0.99    inference(ennf_transformation,[],[f14])).
% 2.72/0.99  
% 2.72/0.99  fof(f30,plain,(
% 2.72/0.99    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 2.72/0.99    inference(flattening,[],[f29])).
% 2.72/0.99  
% 2.72/0.99  fof(f40,plain,(
% 2.72/0.99    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 2.72/0.99    inference(nnf_transformation,[],[f30])).
% 2.72/0.99  
% 2.72/0.99  fof(f66,plain,(
% 2.72/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 2.72/0.99    inference(cnf_transformation,[],[f40])).
% 2.72/0.99  
% 2.72/0.99  fof(f76,plain,(
% 2.72/0.99    r1_ordinal1(k1_ordinal1(sK0),sK1) | r2_hidden(sK0,sK1)),
% 2.72/0.99    inference(cnf_transformation,[],[f47])).
% 2.72/0.99  
% 2.72/0.99  fof(f92,plain,(
% 2.72/0.99    r1_ordinal1(k3_tarski(k2_tarski(sK0,k2_tarski(sK0,sK0))),sK1) | r2_hidden(sK0,sK1)),
% 2.72/0.99    inference(definition_unfolding,[],[f76,f78])).
% 2.72/0.99  
% 2.72/0.99  fof(f3,axiom,(
% 2.72/0.99    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 2.72/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.72/0.99  
% 2.72/0.99  fof(f22,plain,(
% 2.72/0.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 2.72/0.99    inference(ennf_transformation,[],[f3])).
% 2.72/0.99  
% 2.72/0.99  fof(f52,plain,(
% 2.72/0.99    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 2.72/0.99    inference(cnf_transformation,[],[f22])).
% 2.72/0.99  
% 2.72/0.99  fof(f80,plain,(
% 2.72/0.99    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k3_tarski(k2_tarski(X0,X1)),X2)) )),
% 2.72/0.99    inference(definition_unfolding,[],[f52,f63])).
% 2.72/0.99  
% 2.72/0.99  fof(f5,axiom,(
% 2.72/0.99    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1)),
% 2.72/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.72/0.99  
% 2.72/0.99  fof(f54,plain,(
% 2.72/0.99    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1)) )),
% 2.72/0.99    inference(cnf_transformation,[],[f5])).
% 2.72/0.99  
% 2.72/0.99  fof(f79,plain,(
% 2.72/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_tarski(k2_tarski(k2_tarski(X0,X0),k2_tarski(X1,X1)))) )),
% 2.72/0.99    inference(definition_unfolding,[],[f54,f63,f55,f55])).
% 2.72/0.99  
% 2.72/0.99  fof(f16,axiom,(
% 2.72/0.99    ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <=> (X0 = X1 | r2_hidden(X0,X1)))),
% 2.72/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.72/0.99  
% 2.72/0.99  fof(f41,plain,(
% 2.72/0.99    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & ((X0 = X1 | r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 2.72/0.99    inference(nnf_transformation,[],[f16])).
% 2.72/0.99  
% 2.72/0.99  fof(f42,plain,(
% 2.72/0.99    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 2.72/0.99    inference(flattening,[],[f41])).
% 2.72/0.99  
% 2.72/0.99  fof(f71,plain,(
% 2.72/0.99    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | X0 != X1) )),
% 2.72/0.99    inference(cnf_transformation,[],[f42])).
% 2.72/0.99  
% 2.72/0.99  fof(f87,plain,(
% 2.72/0.99    ( ! [X0,X1] : (r2_hidden(X0,k3_tarski(k2_tarski(X1,k2_tarski(X1,X1)))) | X0 != X1) )),
% 2.72/0.99    inference(definition_unfolding,[],[f71,f78])).
% 2.72/0.99  
% 2.72/0.99  fof(f95,plain,(
% 2.72/0.99    ( ! [X1] : (r2_hidden(X1,k3_tarski(k2_tarski(X1,k2_tarski(X1,X1))))) )),
% 2.72/0.99    inference(equality_resolution,[],[f87])).
% 2.72/0.99  
% 2.72/0.99  fof(f12,axiom,(
% 2.72/0.99    ! [X0,X1,X2] : ((r2_hidden(X2,X0) & r1_tarski(k3_tarski(X0),X1)) => r1_tarski(X2,X1))),
% 2.72/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.72/0.99  
% 2.72/0.99  fof(f27,plain,(
% 2.72/0.99    ! [X0,X1,X2] : (r1_tarski(X2,X1) | (~r2_hidden(X2,X0) | ~r1_tarski(k3_tarski(X0),X1)))),
% 2.72/0.99    inference(ennf_transformation,[],[f12])).
% 2.72/0.99  
% 2.72/0.99  fof(f28,plain,(
% 2.72/0.99    ! [X0,X1,X2] : (r1_tarski(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(k3_tarski(X0),X1))),
% 2.72/0.99    inference(flattening,[],[f27])).
% 2.72/0.99  
% 2.72/0.99  fof(f64,plain,(
% 2.72/0.99    ( ! [X2,X0,X1] : (r1_tarski(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(k3_tarski(X0),X1)) )),
% 2.72/0.99    inference(cnf_transformation,[],[f28])).
% 2.72/0.99  
% 2.72/0.99  fof(f7,axiom,(
% 2.72/0.99    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 2.72/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.72/0.99  
% 2.72/0.99  fof(f37,plain,(
% 2.72/0.99    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 2.72/0.99    inference(nnf_transformation,[],[f7])).
% 2.72/0.99  
% 2.72/0.99  fof(f56,plain,(
% 2.72/0.99    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)) )),
% 2.72/0.99    inference(cnf_transformation,[],[f37])).
% 2.72/0.99  
% 2.72/0.99  fof(f83,plain,(
% 2.72/0.99    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k2_tarski(X0,X0),X1)) )),
% 2.72/0.99    inference(definition_unfolding,[],[f56,f55])).
% 2.72/0.99  
% 2.72/0.99  fof(f10,axiom,(
% 2.72/0.99    ! [X0,X1] : (k1_tarski(X1) = k3_xboole_0(X0,k1_tarski(X1)) => r2_hidden(X1,X0))),
% 2.72/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.72/0.99  
% 2.72/0.99  fof(f26,plain,(
% 2.72/0.99    ! [X0,X1] : (r2_hidden(X1,X0) | k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1)))),
% 2.72/0.99    inference(ennf_transformation,[],[f10])).
% 2.72/0.99  
% 2.72/0.99  fof(f62,plain,(
% 2.72/0.99    ( ! [X0,X1] : (r2_hidden(X1,X0) | k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1))) )),
% 2.72/0.99    inference(cnf_transformation,[],[f26])).
% 2.72/0.99  
% 2.72/0.99  fof(f85,plain,(
% 2.72/0.99    ( ! [X0,X1] : (r2_hidden(X1,X0) | k2_tarski(X1,X1) != k3_xboole_0(X0,k2_tarski(X1,X1))) )),
% 2.72/0.99    inference(definition_unfolding,[],[f62,f55,f55])).
% 2.72/0.99  
% 2.72/0.99  fof(f69,plain,(
% 2.72/0.99    ( ! [X0,X1] : (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) )),
% 2.72/0.99    inference(cnf_transformation,[],[f42])).
% 2.72/0.99  
% 2.72/0.99  fof(f89,plain,(
% 2.72/0.99    ( ! [X0,X1] : (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k3_tarski(k2_tarski(X1,k2_tarski(X1,X1))))) )),
% 2.72/0.99    inference(definition_unfolding,[],[f69,f78])).
% 2.72/0.99  
% 2.72/0.99  fof(f1,axiom,(
% 2.72/0.99    ! [X0,X1] : (r2_hidden(X0,X1) => ~r2_hidden(X1,X0))),
% 2.72/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.72/0.99  
% 2.72/0.99  fof(f21,plain,(
% 2.72/0.99    ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1))),
% 2.72/0.99    inference(ennf_transformation,[],[f1])).
% 2.72/0.99  
% 2.72/0.99  fof(f48,plain,(
% 2.72/0.99    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1)) )),
% 2.72/0.99    inference(cnf_transformation,[],[f21])).
% 2.72/0.99  
% 2.72/0.99  cnf(c_21,plain,
% 2.72/0.99      ( r1_ordinal1(X0,X1)
% 2.72/0.99      | r2_hidden(X1,X0)
% 2.72/0.99      | ~ v3_ordinal1(X1)
% 2.72/0.99      | ~ v3_ordinal1(X0) ),
% 2.72/0.99      inference(cnf_transformation,[],[f72]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_23,negated_conjecture,
% 2.72/0.99      ( ~ r1_ordinal1(k3_tarski(k2_tarski(sK0,k2_tarski(sK0,sK0))),sK1)
% 2.72/0.99      | ~ r2_hidden(sK0,sK1) ),
% 2.72/0.99      inference(cnf_transformation,[],[f91]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_210,plain,
% 2.72/0.99      ( ~ r2_hidden(sK0,sK1)
% 2.72/0.99      | ~ r1_ordinal1(k3_tarski(k2_tarski(sK0,k2_tarski(sK0,sK0))),sK1) ),
% 2.72/0.99      inference(prop_impl,[status(thm)],[c_23]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_211,plain,
% 2.72/0.99      ( ~ r1_ordinal1(k3_tarski(k2_tarski(sK0,k2_tarski(sK0,sK0))),sK1)
% 2.72/0.99      | ~ r2_hidden(sK0,sK1) ),
% 2.72/0.99      inference(renaming,[status(thm)],[c_210]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_358,plain,
% 2.72/0.99      ( r2_hidden(X0,X1)
% 2.72/0.99      | ~ r2_hidden(sK0,sK1)
% 2.72/0.99      | ~ v3_ordinal1(X0)
% 2.72/0.99      | ~ v3_ordinal1(X1)
% 2.72/0.99      | k3_tarski(k2_tarski(sK0,k2_tarski(sK0,sK0))) != X1
% 2.72/0.99      | sK1 != X0 ),
% 2.72/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_211]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_359,plain,
% 2.72/0.99      ( r2_hidden(sK1,k3_tarski(k2_tarski(sK0,k2_tarski(sK0,sK0))))
% 2.72/0.99      | ~ r2_hidden(sK0,sK1)
% 2.72/0.99      | ~ v3_ordinal1(k3_tarski(k2_tarski(sK0,k2_tarski(sK0,sK0))))
% 2.72/0.99      | ~ v3_ordinal1(sK1) ),
% 2.72/0.99      inference(unflattening,[status(thm)],[c_358]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_26,negated_conjecture,
% 2.72/0.99      ( v3_ordinal1(sK0) ),
% 2.72/0.99      inference(cnf_transformation,[],[f74]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_25,negated_conjecture,
% 2.72/0.99      ( v3_ordinal1(sK1) ),
% 2.72/0.99      inference(cnf_transformation,[],[f75]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_22,plain,
% 2.72/0.99      ( ~ v3_ordinal1(X0)
% 2.72/0.99      | v3_ordinal1(k3_tarski(k2_tarski(X0,k2_tarski(X0,X0)))) ),
% 2.72/0.99      inference(cnf_transformation,[],[f90]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_32,plain,
% 2.72/0.99      ( v3_ordinal1(k3_tarski(k2_tarski(sK0,k2_tarski(sK0,sK0))))
% 2.72/0.99      | ~ v3_ordinal1(sK0) ),
% 2.72/0.99      inference(instantiation,[status(thm)],[c_22]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_361,plain,
% 2.72/0.99      ( r2_hidden(sK1,k3_tarski(k2_tarski(sK0,k2_tarski(sK0,sK0))))
% 2.72/0.99      | ~ r2_hidden(sK0,sK1) ),
% 2.72/0.99      inference(global_propositional_subsumption,
% 2.72/0.99                [status(thm)],
% 2.72/0.99                [c_359,c_26,c_25,c_32]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_1177,plain,
% 2.72/0.99      ( r2_hidden(sK1,k3_tarski(k2_tarski(sK0,k2_tarski(sK0,sK0)))) = iProver_top
% 2.72/0.99      | r2_hidden(sK0,sK1) != iProver_top ),
% 2.72/0.99      inference(predicate_to_equality,[status(thm)],[c_361]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_9,plain,
% 2.72/0.99      ( ~ r2_hidden(X0,X1)
% 2.72/0.99      | k3_xboole_0(X1,k2_tarski(X0,X0)) = k2_tarski(X0,X0) ),
% 2.72/0.99      inference(cnf_transformation,[],[f84]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_1190,plain,
% 2.72/0.99      ( k3_xboole_0(X0,k2_tarski(X1,X1)) = k2_tarski(X1,X1)
% 2.72/0.99      | r2_hidden(X1,X0) != iProver_top ),
% 2.72/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_4025,plain,
% 2.72/0.99      ( k3_xboole_0(k3_tarski(k2_tarski(sK0,k2_tarski(sK0,sK0))),k2_tarski(sK1,sK1)) = k2_tarski(sK1,sK1)
% 2.72/0.99      | r2_hidden(sK0,sK1) != iProver_top ),
% 2.72/0.99      inference(superposition,[status(thm)],[c_1177,c_1190]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_16,plain,
% 2.72/0.99      ( ~ r1_ordinal1(X0,X1)
% 2.72/0.99      | r1_tarski(X0,X1)
% 2.72/0.99      | ~ v3_ordinal1(X1)
% 2.72/0.99      | ~ v3_ordinal1(X0) ),
% 2.72/0.99      inference(cnf_transformation,[],[f66]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_24,negated_conjecture,
% 2.72/0.99      ( r1_ordinal1(k3_tarski(k2_tarski(sK0,k2_tarski(sK0,sK0))),sK1)
% 2.72/0.99      | r2_hidden(sK0,sK1) ),
% 2.72/0.99      inference(cnf_transformation,[],[f92]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_212,plain,
% 2.72/0.99      ( r2_hidden(sK0,sK1)
% 2.72/0.99      | r1_ordinal1(k3_tarski(k2_tarski(sK0,k2_tarski(sK0,sK0))),sK1) ),
% 2.72/0.99      inference(prop_impl,[status(thm)],[c_24]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_213,plain,
% 2.72/0.99      ( r1_ordinal1(k3_tarski(k2_tarski(sK0,k2_tarski(sK0,sK0))),sK1)
% 2.72/0.99      | r2_hidden(sK0,sK1) ),
% 2.72/0.99      inference(renaming,[status(thm)],[c_212]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_386,plain,
% 2.72/0.99      ( r1_tarski(X0,X1)
% 2.72/0.99      | r2_hidden(sK0,sK1)
% 2.72/0.99      | ~ v3_ordinal1(X1)
% 2.72/0.99      | ~ v3_ordinal1(X0)
% 2.72/0.99      | k3_tarski(k2_tarski(sK0,k2_tarski(sK0,sK0))) != X0
% 2.72/0.99      | sK1 != X1 ),
% 2.72/0.99      inference(resolution_lifted,[status(thm)],[c_16,c_213]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_387,plain,
% 2.72/0.99      ( r1_tarski(k3_tarski(k2_tarski(sK0,k2_tarski(sK0,sK0))),sK1)
% 2.72/0.99      | r2_hidden(sK0,sK1)
% 2.72/0.99      | ~ v3_ordinal1(k3_tarski(k2_tarski(sK0,k2_tarski(sK0,sK0))))
% 2.72/0.99      | ~ v3_ordinal1(sK1) ),
% 2.72/0.99      inference(unflattening,[status(thm)],[c_386]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_506,plain,
% 2.72/0.99      ( r2_hidden(sK0,sK1)
% 2.72/0.99      | r1_tarski(k3_tarski(k2_tarski(sK0,k2_tarski(sK0,sK0))),sK1) ),
% 2.72/0.99      inference(prop_impl,[status(thm)],[c_26,c_25,c_32,c_387]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_507,plain,
% 2.72/0.99      ( r1_tarski(k3_tarski(k2_tarski(sK0,k2_tarski(sK0,sK0))),sK1)
% 2.72/0.99      | r2_hidden(sK0,sK1) ),
% 2.72/0.99      inference(renaming,[status(thm)],[c_506]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_1175,plain,
% 2.72/0.99      ( r1_tarski(k3_tarski(k2_tarski(sK0,k2_tarski(sK0,sK0))),sK1) = iProver_top
% 2.72/0.99      | r2_hidden(sK0,sK1) = iProver_top ),
% 2.72/0.99      inference(predicate_to_equality,[status(thm)],[c_507]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_5,plain,
% 2.72/0.99      ( r1_tarski(X0,X1) | ~ r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1) ),
% 2.72/0.99      inference(cnf_transformation,[],[f80]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_1194,plain,
% 2.72/0.99      ( r1_tarski(X0,X1) = iProver_top
% 2.72/0.99      | r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1) != iProver_top ),
% 2.72/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_2256,plain,
% 2.72/0.99      ( r1_tarski(sK0,sK1) = iProver_top | r2_hidden(sK0,sK1) = iProver_top ),
% 2.72/0.99      inference(superposition,[status(thm)],[c_1175,c_1194]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_27,plain,
% 2.72/0.99      ( v3_ordinal1(sK0) = iProver_top ),
% 2.72/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_28,plain,
% 2.72/0.99      ( v3_ordinal1(sK1) = iProver_top ),
% 2.72/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_31,plain,
% 2.72/0.99      ( v3_ordinal1(X0) != iProver_top
% 2.72/0.99      | v3_ordinal1(k3_tarski(k2_tarski(X0,k2_tarski(X0,X0)))) = iProver_top ),
% 2.72/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_33,plain,
% 2.72/0.99      ( v3_ordinal1(k3_tarski(k2_tarski(sK0,k2_tarski(sK0,sK0)))) = iProver_top
% 2.72/0.99      | v3_ordinal1(sK0) != iProver_top ),
% 2.72/0.99      inference(instantiation,[status(thm)],[c_31]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_388,plain,
% 2.72/0.99      ( r1_tarski(k3_tarski(k2_tarski(sK0,k2_tarski(sK0,sK0))),sK1) = iProver_top
% 2.72/0.99      | r2_hidden(sK0,sK1) = iProver_top
% 2.72/0.99      | v3_ordinal1(k3_tarski(k2_tarski(sK0,k2_tarski(sK0,sK0)))) != iProver_top
% 2.72/0.99      | v3_ordinal1(sK1) != iProver_top ),
% 2.72/0.99      inference(predicate_to_equality,[status(thm)],[c_387]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_0,plain,
% 2.72/0.99      ( k3_tarski(k2_tarski(k2_tarski(X0,X0),k2_tarski(X1,X1))) = k2_tarski(X0,X1) ),
% 2.72/0.99      inference(cnf_transformation,[],[f79]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_18,plain,
% 2.72/0.99      ( r2_hidden(X0,k3_tarski(k2_tarski(X0,k2_tarski(X0,X0)))) ),
% 2.72/0.99      inference(cnf_transformation,[],[f95]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_1184,plain,
% 2.72/0.99      ( r2_hidden(X0,k3_tarski(k2_tarski(X0,k2_tarski(X0,X0)))) = iProver_top ),
% 2.72/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_1519,plain,
% 2.72/0.99      ( r2_hidden(k2_tarski(X0,X0),k2_tarski(X0,k2_tarski(X0,X0))) = iProver_top ),
% 2.72/0.99      inference(superposition,[status(thm)],[c_0,c_1184]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_1521,plain,
% 2.72/0.99      ( r2_hidden(k2_tarski(sK0,sK0),k2_tarski(sK0,k2_tarski(sK0,sK0))) = iProver_top ),
% 2.72/0.99      inference(instantiation,[status(thm)],[c_1519]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_14,plain,
% 2.72/0.99      ( r1_tarski(X0,X1) | ~ r1_tarski(k3_tarski(X2),X1) | ~ r2_hidden(X0,X2) ),
% 2.72/0.99      inference(cnf_transformation,[],[f64]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_1387,plain,
% 2.72/0.99      ( r1_tarski(k2_tarski(X0,X1),X2)
% 2.72/0.99      | ~ r1_tarski(k3_tarski(X3),X2)
% 2.72/0.99      | ~ r2_hidden(k2_tarski(X0,X1),X3) ),
% 2.72/0.99      inference(instantiation,[status(thm)],[c_14]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_1705,plain,
% 2.72/0.99      ( r1_tarski(k2_tarski(X0,X1),X2)
% 2.72/0.99      | ~ r1_tarski(k3_tarski(k2_tarski(X3,X4)),X2)
% 2.72/0.99      | ~ r2_hidden(k2_tarski(X0,X1),k2_tarski(X3,X4)) ),
% 2.72/0.99      inference(instantiation,[status(thm)],[c_1387]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_2499,plain,
% 2.72/0.99      ( r1_tarski(k2_tarski(X0,X1),X2)
% 2.72/0.99      | ~ r1_tarski(k3_tarski(k2_tarski(X3,k2_tarski(X0,X1))),X2)
% 2.72/0.99      | ~ r2_hidden(k2_tarski(X0,X1),k2_tarski(X3,k2_tarski(X0,X1))) ),
% 2.72/0.99      inference(instantiation,[status(thm)],[c_1705]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_9732,plain,
% 2.72/0.99      ( r1_tarski(k2_tarski(sK0,sK0),sK1)
% 2.72/0.99      | ~ r1_tarski(k3_tarski(k2_tarski(sK0,k2_tarski(sK0,sK0))),sK1)
% 2.72/0.99      | ~ r2_hidden(k2_tarski(sK0,sK0),k2_tarski(sK0,k2_tarski(sK0,sK0))) ),
% 2.72/0.99      inference(instantiation,[status(thm)],[c_2499]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_9733,plain,
% 2.72/0.99      ( r1_tarski(k2_tarski(sK0,sK0),sK1) = iProver_top
% 2.72/0.99      | r1_tarski(k3_tarski(k2_tarski(sK0,k2_tarski(sK0,sK0))),sK1) != iProver_top
% 2.72/0.99      | r2_hidden(k2_tarski(sK0,sK0),k2_tarski(sK0,k2_tarski(sK0,sK0))) != iProver_top ),
% 2.72/0.99      inference(predicate_to_equality,[status(thm)],[c_9732]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_8,plain,
% 2.72/0.99      ( ~ r1_tarski(k2_tarski(X0,X0),X1) | r2_hidden(X0,X1) ),
% 2.72/0.99      inference(cnf_transformation,[],[f83]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_11268,plain,
% 2.72/0.99      ( ~ r1_tarski(k2_tarski(sK0,sK0),sK1) | r2_hidden(sK0,sK1) ),
% 2.72/0.99      inference(instantiation,[status(thm)],[c_8]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_11269,plain,
% 2.72/0.99      ( r1_tarski(k2_tarski(sK0,sK0),sK1) != iProver_top
% 2.72/0.99      | r2_hidden(sK0,sK1) = iProver_top ),
% 2.72/0.99      inference(predicate_to_equality,[status(thm)],[c_11268]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_11445,plain,
% 2.72/0.99      ( r2_hidden(sK0,sK1) = iProver_top ),
% 2.72/0.99      inference(global_propositional_subsumption,
% 2.72/0.99                [status(thm)],
% 2.72/0.99                [c_2256,c_27,c_28,c_33,c_388,c_1521,c_9733,c_11269]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_14077,plain,
% 2.72/0.99      ( k3_xboole_0(k3_tarski(k2_tarski(sK0,k2_tarski(sK0,sK0))),k2_tarski(sK1,sK1)) = k2_tarski(sK1,sK1) ),
% 2.72/0.99      inference(global_propositional_subsumption,
% 2.72/0.99                [status(thm)],
% 2.72/0.99                [c_4025,c_27,c_28,c_33,c_388,c_1521,c_9733,c_11269]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_13,plain,
% 2.72/0.99      ( r2_hidden(X0,X1)
% 2.72/0.99      | k3_xboole_0(X1,k2_tarski(X0,X0)) != k2_tarski(X0,X0) ),
% 2.72/0.99      inference(cnf_transformation,[],[f85]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_1186,plain,
% 2.72/0.99      ( k3_xboole_0(X0,k2_tarski(X1,X1)) != k2_tarski(X1,X1)
% 2.72/0.99      | r2_hidden(X1,X0) = iProver_top ),
% 2.72/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_14080,plain,
% 2.72/0.99      ( r2_hidden(sK1,k3_tarski(k2_tarski(sK0,k2_tarski(sK0,sK0)))) = iProver_top ),
% 2.72/0.99      inference(superposition,[status(thm)],[c_14077,c_1186]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_20,plain,
% 2.72/0.99      ( r2_hidden(X0,X1)
% 2.72/0.99      | ~ r2_hidden(X0,k3_tarski(k2_tarski(X1,k2_tarski(X1,X1))))
% 2.72/0.99      | X1 = X0 ),
% 2.72/0.99      inference(cnf_transformation,[],[f89]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_1182,plain,
% 2.72/0.99      ( X0 = X1
% 2.72/0.99      | r2_hidden(X1,X0) = iProver_top
% 2.72/0.99      | r2_hidden(X1,k3_tarski(k2_tarski(X0,k2_tarski(X0,X0)))) != iProver_top ),
% 2.72/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_14365,plain,
% 2.72/0.99      ( sK1 = sK0 | r2_hidden(sK1,sK0) = iProver_top ),
% 2.72/0.99      inference(superposition,[status(thm)],[c_14080,c_1182]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_1,plain,
% 2.72/0.99      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X1,X0) ),
% 2.72/0.99      inference(cnf_transformation,[],[f48]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_1342,plain,
% 2.72/0.99      ( ~ r2_hidden(sK1,sK0) | ~ r2_hidden(sK0,sK1) ),
% 2.72/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_1343,plain,
% 2.72/0.99      ( r2_hidden(sK1,sK0) != iProver_top | r2_hidden(sK0,sK1) != iProver_top ),
% 2.72/0.99      inference(predicate_to_equality,[status(thm)],[c_1342]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_8514,plain,
% 2.72/0.99      ( sK1 = sK0
% 2.72/0.99      | r2_hidden(sK1,sK0) = iProver_top
% 2.72/0.99      | r2_hidden(sK0,sK1) != iProver_top ),
% 2.72/0.99      inference(superposition,[status(thm)],[c_1177,c_1182]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_14375,plain,
% 2.72/0.99      ( sK1 = sK0 ),
% 2.72/0.99      inference(global_propositional_subsumption,
% 2.72/0.99                [status(thm)],
% 2.72/0.99                [c_14365,c_27,c_28,c_33,c_388,c_1343,c_1521,c_8514,c_9733,
% 2.72/0.99                 c_11269]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_1197,plain,
% 2.72/0.99      ( r2_hidden(X0,X1) != iProver_top | r2_hidden(X1,X0) != iProver_top ),
% 2.72/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_11451,plain,
% 2.72/0.99      ( r2_hidden(sK1,sK0) != iProver_top ),
% 2.72/0.99      inference(superposition,[status(thm)],[c_11445,c_1197]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_14381,plain,
% 2.72/0.99      ( r2_hidden(sK0,sK0) != iProver_top ),
% 2.72/0.99      inference(demodulation,[status(thm)],[c_14375,c_11451]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_14382,plain,
% 2.72/0.99      ( r2_hidden(sK0,sK0) = iProver_top ),
% 2.72/0.99      inference(demodulation,[status(thm)],[c_14375,c_11445]) ).
% 2.72/0.99  
% 2.72/0.99  cnf(c_14400,plain,
% 2.72/0.99      ( $false ),
% 2.72/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_14381,c_14382]) ).
% 2.72/0.99  
% 2.72/0.99  
% 2.72/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.72/0.99  
% 2.72/0.99  ------                               Statistics
% 2.72/0.99  
% 2.72/0.99  ------ General
% 2.72/0.99  
% 2.72/0.99  abstr_ref_over_cycles:                  0
% 2.72/0.99  abstr_ref_under_cycles:                 0
% 2.72/0.99  gc_basic_clause_elim:                   0
% 2.72/0.99  forced_gc_time:                         0
% 2.72/0.99  parsing_time:                           0.009
% 2.72/0.99  unif_index_cands_time:                  0.
% 2.72/0.99  unif_index_add_time:                    0.
% 2.72/0.99  orderings_time:                         0.
% 2.72/0.99  out_proof_time:                         0.01
% 2.72/0.99  total_time:                             0.35
% 2.72/0.99  num_of_symbols:                         40
% 2.72/0.99  num_of_terms:                           16515
% 2.72/0.99  
% 2.72/0.99  ------ Preprocessing
% 2.72/0.99  
% 2.72/0.99  num_of_splits:                          0
% 2.72/0.99  num_of_split_atoms:                     0
% 2.72/0.99  num_of_reused_defs:                     0
% 2.72/0.99  num_eq_ax_congr_red:                    4
% 2.72/0.99  num_of_sem_filtered_clauses:            1
% 2.72/0.99  num_of_subtypes:                        0
% 2.72/0.99  monotx_restored_types:                  0
% 2.72/0.99  sat_num_of_epr_types:                   0
% 2.72/0.99  sat_num_of_non_cyclic_types:            0
% 2.72/0.99  sat_guarded_non_collapsed_types:        0
% 2.72/0.99  num_pure_diseq_elim:                    0
% 2.72/0.99  simp_replaced_by:                       0
% 2.72/0.99  res_preprocessed:                       114
% 2.72/0.99  prep_upred:                             0
% 2.72/0.99  prep_unflattend:                        6
% 2.72/0.99  smt_new_axioms:                         0
% 2.72/0.99  pred_elim_cands:                        3
% 2.72/0.99  pred_elim:                              1
% 2.72/0.99  pred_elim_cl:                           1
% 2.72/0.99  pred_elim_cycles:                       3
% 2.72/0.99  merged_defs:                            24
% 2.72/0.99  merged_defs_ncl:                        0
% 2.72/0.99  bin_hyper_res:                          24
% 2.72/0.99  prep_cycles:                            4
% 2.72/0.99  pred_elim_time:                         0.001
% 2.72/0.99  splitting_time:                         0.
% 2.72/0.99  sem_filter_time:                        0.
% 2.72/0.99  monotx_time:                            0.001
% 2.72/0.99  subtype_inf_time:                       0.
% 2.72/0.99  
% 2.72/0.99  ------ Problem properties
% 2.72/0.99  
% 2.72/0.99  clauses:                                24
% 2.72/0.99  conjectures:                            2
% 2.72/0.99  epr:                                    6
% 2.72/0.99  horn:                                   21
% 2.72/0.99  ground:                                 5
% 2.72/0.99  unary:                                  5
% 2.72/0.99  binary:                                 13
% 2.72/0.99  lits:                                   50
% 2.72/0.99  lits_eq:                                5
% 2.72/0.99  fd_pure:                                0
% 2.72/0.99  fd_pseudo:                              0
% 2.72/0.99  fd_cond:                                0
% 2.72/0.99  fd_pseudo_cond:                         2
% 2.72/0.99  ac_symbols:                             0
% 2.72/0.99  
% 2.72/0.99  ------ Propositional Solver
% 2.72/0.99  
% 2.72/0.99  prop_solver_calls:                      27
% 2.72/0.99  prop_fast_solver_calls:                 657
% 2.72/0.99  smt_solver_calls:                       0
% 2.72/0.99  smt_fast_solver_calls:                  0
% 2.72/0.99  prop_num_of_clauses:                    4088
% 2.72/0.99  prop_preprocess_simplified:             14264
% 2.72/0.99  prop_fo_subsumed:                       9
% 2.72/0.99  prop_solver_time:                       0.
% 2.72/0.99  smt_solver_time:                        0.
% 2.72/0.99  smt_fast_solver_time:                   0.
% 2.72/0.99  prop_fast_solver_time:                  0.
% 2.72/0.99  prop_unsat_core_time:                   0.
% 2.72/0.99  
% 2.72/0.99  ------ QBF
% 2.72/0.99  
% 2.72/0.99  qbf_q_res:                              0
% 2.72/0.99  qbf_num_tautologies:                    0
% 2.72/0.99  qbf_prep_cycles:                        0
% 2.72/0.99  
% 2.72/0.99  ------ BMC1
% 2.72/0.99  
% 2.72/0.99  bmc1_current_bound:                     -1
% 2.72/0.99  bmc1_last_solved_bound:                 -1
% 2.72/0.99  bmc1_unsat_core_size:                   -1
% 2.72/0.99  bmc1_unsat_core_parents_size:           -1
% 2.72/0.99  bmc1_merge_next_fun:                    0
% 2.72/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.72/0.99  
% 2.72/0.99  ------ Instantiation
% 2.72/0.99  
% 2.72/0.99  inst_num_of_clauses:                    1349
% 2.72/0.99  inst_num_in_passive:                    704
% 2.72/0.99  inst_num_in_active:                     420
% 2.72/0.99  inst_num_in_unprocessed:                225
% 2.72/0.99  inst_num_of_loops:                      430
% 2.72/0.99  inst_num_of_learning_restarts:          0
% 2.72/0.99  inst_num_moves_active_passive:          10
% 2.72/0.99  inst_lit_activity:                      0
% 2.72/0.99  inst_lit_activity_moves:                0
% 2.72/0.99  inst_num_tautologies:                   0
% 2.72/0.99  inst_num_prop_implied:                  0
% 2.72/0.99  inst_num_existing_simplified:           0
% 2.72/0.99  inst_num_eq_res_simplified:             0
% 2.72/0.99  inst_num_child_elim:                    0
% 2.72/0.99  inst_num_of_dismatching_blockings:      1863
% 2.72/0.99  inst_num_of_non_proper_insts:           2037
% 2.72/0.99  inst_num_of_duplicates:                 0
% 2.72/0.99  inst_inst_num_from_inst_to_res:         0
% 2.72/0.99  inst_dismatching_checking_time:         0.
% 2.72/0.99  
% 2.72/0.99  ------ Resolution
% 2.72/0.99  
% 2.72/0.99  res_num_of_clauses:                     0
% 2.72/0.99  res_num_in_passive:                     0
% 2.72/0.99  res_num_in_active:                      0
% 2.72/0.99  res_num_of_loops:                       118
% 2.72/0.99  res_forward_subset_subsumed:            219
% 2.72/0.99  res_backward_subset_subsumed:           0
% 2.72/0.99  res_forward_subsumed:                   0
% 2.72/0.99  res_backward_subsumed:                  0
% 2.72/0.99  res_forward_subsumption_resolution:     0
% 2.72/0.99  res_backward_subsumption_resolution:    0
% 2.72/0.99  res_clause_to_clause_subsumption:       1152
% 2.72/0.99  res_orphan_elimination:                 0
% 2.72/0.99  res_tautology_del:                      106
% 2.72/0.99  res_num_eq_res_simplified:              0
% 2.72/0.99  res_num_sel_changes:                    0
% 2.72/0.99  res_moves_from_active_to_pass:          0
% 2.72/0.99  
% 2.72/0.99  ------ Superposition
% 2.72/0.99  
% 2.72/0.99  sup_time_total:                         0.
% 2.72/0.99  sup_time_generating:                    0.
% 2.72/0.99  sup_time_sim_full:                      0.
% 2.72/0.99  sup_time_sim_immed:                     0.
% 2.72/0.99  
% 2.72/0.99  sup_num_of_clauses:                     190
% 2.72/0.99  sup_num_in_active:                      76
% 2.72/0.99  sup_num_in_passive:                     114
% 2.72/0.99  sup_num_of_loops:                       85
% 2.72/0.99  sup_fw_superposition:                   145
% 2.72/0.99  sup_bw_superposition:                   125
% 2.72/0.99  sup_immediate_simplified:               15
% 2.72/0.99  sup_given_eliminated:                   0
% 2.72/0.99  comparisons_done:                       0
% 2.72/0.99  comparisons_avoided:                    0
% 2.72/0.99  
% 2.72/0.99  ------ Simplifications
% 2.72/0.99  
% 2.72/0.99  
% 2.72/0.99  sim_fw_subset_subsumed:                 4
% 2.72/0.99  sim_bw_subset_subsumed:                 3
% 2.72/0.99  sim_fw_subsumed:                        13
% 2.72/0.99  sim_bw_subsumed:                        1
% 2.72/0.99  sim_fw_subsumption_res:                 1
% 2.72/0.99  sim_bw_subsumption_res:                 1
% 2.72/0.99  sim_tautology_del:                      7
% 2.72/0.99  sim_eq_tautology_del:                   5
% 2.72/0.99  sim_eq_res_simp:                        0
% 2.72/0.99  sim_fw_demodulated:                     0
% 2.72/0.99  sim_bw_demodulated:                     8
% 2.72/0.99  sim_light_normalised:                   0
% 2.72/0.99  sim_joinable_taut:                      0
% 2.72/0.99  sim_joinable_simp:                      0
% 2.72/0.99  sim_ac_normalised:                      0
% 2.72/0.99  sim_smt_subsumption:                    0
% 2.72/0.99  
%------------------------------------------------------------------------------
