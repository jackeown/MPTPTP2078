%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0275+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:54 EST 2020

% Result     : Theorem 0.65s
% Output     : CNFRefutation 0.65s
% Verified   : 
% Statistics : Number of formulae       :   43 ( 117 expanded)
%              Number of clauses        :   23 (  43 expanded)
%              Number of leaves         :    4 (  20 expanded)
%              Depth                    :   11
%              Number of atoms          :  128 ( 413 expanded)
%              Number of equality atoms :   41 ( 123 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f7])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f15,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f16,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f3,conjecture,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0
      <=> ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f5,plain,(
    ? [X0,X1,X2] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0
    <~> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2)
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0 )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2)
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0 )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0 ) ) ),
    inference(flattening,[],[f9])).

fof(f11,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r2_hidden(X1,X2)
          | ~ r2_hidden(X0,X2)
          | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0 )
        & ( ( r2_hidden(X1,X2)
            & r2_hidden(X0,X2) )
          | k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0 ) )
   => ( ( ~ r2_hidden(sK1,sK2)
        | ~ r2_hidden(sK0,sK2)
        | k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_xboole_0 )
      & ( ( r2_hidden(sK1,sK2)
          & r2_hidden(sK0,sK2) )
        | k4_xboole_0(k2_tarski(sK0,sK1),sK2) = k1_xboole_0 ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,
    ( ( ~ r2_hidden(sK1,sK2)
      | ~ r2_hidden(sK0,sK2)
      | k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_xboole_0 )
    & ( ( r2_hidden(sK1,sK2)
        & r2_hidden(sK0,sK2) )
      | k4_xboole_0(k2_tarski(sK0,sK1),sK2) = k1_xboole_0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f11])).

fof(f20,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ r2_hidden(sK0,sK2)
    | k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f12])).

fof(f19,plain,
    ( r2_hidden(sK1,sK2)
    | k4_xboole_0(k2_tarski(sK0,sK1),sK2) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f12])).

fof(f18,plain,
    ( r2_hidden(sK0,sK2)
    | k4_xboole_0(k2_tarski(sK0,sK1),sK2) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f12])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X1)
    | r1_tarski(k2_tarski(X2,X0),X1) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_193,plain,
    ( ~ r2_hidden(X0_36,X0_37)
    | ~ r2_hidden(X1_36,X0_37)
    | r1_tarski(k2_tarski(X1_36,X0_36),X0_37) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_376,plain,
    ( ~ r2_hidden(sK0,sK2)
    | ~ r2_hidden(sK1,sK2)
    | r1_tarski(k2_tarski(sK0,sK1),sK2) ),
    inference(instantiation,[status(thm)],[c_193])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f14])).

cnf(c_195,plain,
    ( ~ r1_tarski(X0_39,X0_37)
    | k4_xboole_0(X0_39,X0_37) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_346,plain,
    ( ~ r1_tarski(k2_tarski(X0_36,X1_36),X0_37)
    | k4_xboole_0(k2_tarski(X0_36,X1_36),X0_37) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_195])).

cnf(c_363,plain,
    ( ~ r1_tarski(k2_tarski(sK0,sK1),sK2)
    | k4_xboole_0(k2_tarski(sK0,sK1),sK2) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_346])).

cnf(c_1,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f13])).

cnf(c_62,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_1])).

cnf(c_4,plain,
    ( r2_hidden(X0,X1)
    | ~ r1_tarski(k2_tarski(X0,X2),X1) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_144,plain,
    ( r2_hidden(X0,X1)
    | X1 != X2
    | k2_tarski(X0,X3) != X4
    | k4_xboole_0(X4,X2) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_62,c_4])).

cnf(c_145,plain,
    ( r2_hidden(X0,X1)
    | k4_xboole_0(k2_tarski(X0,X2),X1) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_144])).

cnf(c_3,plain,
    ( r2_hidden(X0,X1)
    | ~ r1_tarski(k2_tarski(X2,X0),X1) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_117,plain,
    ( r2_hidden(X0,X1)
    | X1 != X2
    | k2_tarski(X3,X0) != X4
    | k4_xboole_0(X4,X2) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_62,c_3])).

cnf(c_118,plain,
    ( r2_hidden(X0,X1)
    | k4_xboole_0(k2_tarski(X2,X0),X1) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_117])).

cnf(c_5,negated_conjecture,
    ( ~ r2_hidden(sK0,sK2)
    | ~ r2_hidden(sK1,sK2)
    | k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f20])).

cnf(c_171,plain,
    ( ~ r2_hidden(sK0,sK2)
    | k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_118,c_5])).

cnf(c_180,plain,
    ( k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_145,c_171])).

cnf(c_189,plain,
    ( k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_180])).

cnf(c_6,negated_conjecture,
    ( r2_hidden(sK1,sK2)
    | k4_xboole_0(k2_tarski(sK0,sK1),sK2) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f19])).

cnf(c_173,plain,
    ( r2_hidden(sK1,sK2) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_118,c_6])).

cnf(c_7,negated_conjecture,
    ( r2_hidden(sK0,sK2)
    | k4_xboole_0(k2_tarski(sK0,sK1),sK2) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f18])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_376,c_363,c_189,c_180,c_173,c_7])).


%------------------------------------------------------------------------------
