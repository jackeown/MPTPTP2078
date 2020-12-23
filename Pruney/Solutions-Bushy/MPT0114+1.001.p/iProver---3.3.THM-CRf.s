%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0114+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:30 EST 2020

% Result     : Theorem 0.62s
% Output     : CNFRefutation 0.62s
% Verified   : 
% Statistics : Number of formulae       :   40 ( 109 expanded)
%              Number of clauses        :   17 (  27 expanded)
%              Number of leaves         :    5 (  23 expanded)
%              Depth                    :   13
%              Number of atoms          :  114 ( 367 expanded)
%              Number of equality atoms :    2 (  10 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f16,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k5_xboole_0(X1,X2))
    <=> ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,k5_xboole_0(X1,X2))
      <=> ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
          & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( r1_tarski(X0,k5_xboole_0(X1,X2))
    <~> ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k3_xboole_0(X1,X2))
        | ~ r1_tarski(X0,k2_xboole_0(X1,X2))
        | ~ r1_tarski(X0,k5_xboole_0(X1,X2)) )
      & ( ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
          & r1_tarski(X0,k2_xboole_0(X1,X2)) )
        | r1_tarski(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k3_xboole_0(X1,X2))
        | ~ r1_tarski(X0,k2_xboole_0(X1,X2))
        | ~ r1_tarski(X0,k5_xboole_0(X1,X2)) )
      & ( ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
          & r1_tarski(X0,k2_xboole_0(X1,X2)) )
        | r1_tarski(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(flattening,[],[f10])).

fof(f12,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_xboole_0(X0,k3_xboole_0(X1,X2))
          | ~ r1_tarski(X0,k2_xboole_0(X1,X2))
          | ~ r1_tarski(X0,k5_xboole_0(X1,X2)) )
        & ( ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
            & r1_tarski(X0,k2_xboole_0(X1,X2)) )
          | r1_tarski(X0,k5_xboole_0(X1,X2)) ) )
   => ( ( ~ r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
        | ~ r1_tarski(sK0,k2_xboole_0(sK1,sK2))
        | ~ r1_tarski(sK0,k5_xboole_0(sK1,sK2)) )
      & ( ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
          & r1_tarski(sK0,k2_xboole_0(sK1,sK2)) )
        | r1_tarski(sK0,k5_xboole_0(sK1,sK2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( ( ~ r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
      | ~ r1_tarski(sK0,k2_xboole_0(sK1,sK2))
      | ~ r1_tarski(sK0,k5_xboole_0(sK1,sK2)) )
    & ( ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
        & r1_tarski(sK0,k2_xboole_0(sK1,sK2)) )
      | r1_tarski(sK0,k5_xboole_0(sK1,sK2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f12])).

fof(f20,plain,
    ( ~ r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ~ r1_tarski(sK0,k2_xboole_0(sK1,sK2))
    | ~ r1_tarski(sK0,k5_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f21,plain,
    ( ~ r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ~ r1_tarski(sK0,k2_xboole_0(sK1,sK2))
    | ~ r1_tarski(sK0,k4_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2))) ),
    inference(definition_unfolding,[],[f20,f14])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f7])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f15,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f19,plain,
    ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | r1_tarski(sK0,k5_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f22,plain,
    ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | r1_tarski(sK0,k4_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2))) ),
    inference(definition_unfolding,[],[f19,f14])).

fof(f18,plain,
    ( r1_tarski(sK0,k2_xboole_0(sK1,sK2))
    | r1_tarski(sK0,k5_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f23,plain,
    ( r1_tarski(sK0,k2_xboole_0(sK1,sK2))
    | r1_tarski(sK0,k4_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2))) ),
    inference(definition_unfolding,[],[f18,f14])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
    | r1_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_3,negated_conjecture,
    ( ~ r1_tarski(sK0,k2_xboole_0(sK1,sK2))
    | ~ r1_tarski(sK0,k4_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2)))
    | ~ r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_77,plain,
    ( ~ r1_tarski(sK0,k2_xboole_0(sK1,sK2))
    | ~ r1_tarski(sK0,k4_xboole_0(X0,k3_xboole_0(sK1,sK2)))
    | ~ r1_tarski(sK0,k4_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2))) ),
    inference(resolution,[status(thm)],[c_0,c_3])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k4_xboole_0(X1,X2))
    | ~ r1_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_64,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,k4_xboole_0(X2,X3))
    | r1_tarski(X0,k4_xboole_0(X1,X3)) ),
    inference(resolution,[status(thm)],[c_0,c_2])).

cnf(c_84,plain,
    ( ~ r1_tarski(sK0,k2_xboole_0(sK1,sK2))
    | ~ r1_tarski(sK0,k4_xboole_0(X0,k3_xboole_0(sK1,sK2))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_77,c_64])).

cnf(c_147,plain,
    ( ~ r1_tarski(sK0,k2_xboole_0(sK1,sK2))
    | ~ r1_tarski(sK0,k4_xboole_0(X0_37,k3_xboole_0(sK1,sK2))) ),
    inference(subtyping,[status(esa)],[c_84])).

cnf(c_183,plain,
    ( ~ r1_tarski(sK0,k2_xboole_0(sK1,sK2))
    | ~ r1_tarski(sK0,k4_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_147])).

cnf(c_1,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_149,plain,
    ( r1_tarski(X0_36,X0_37)
    | ~ r1_tarski(X0_36,k4_xboole_0(X0_37,X0_38)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_170,plain,
    ( r1_tarski(sK0,k2_xboole_0(sK1,sK2))
    | ~ r1_tarski(sK0,k4_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_149])).

cnf(c_4,negated_conjecture,
    ( r1_tarski(sK0,k4_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2)))
    | r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_92,plain,
    ( ~ r1_tarski(sK0,X0)
    | r1_tarski(sK0,k4_xboole_0(X0,k3_xboole_0(sK1,sK2)))
    | r1_tarski(sK0,k4_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2))) ),
    inference(resolution,[status(thm)],[c_2,c_4])).

cnf(c_5,negated_conjecture,
    ( r1_tarski(sK0,k2_xboole_0(sK1,sK2))
    | r1_tarski(sK0,k4_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2))) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_96,plain,
    ( ~ r1_tarski(sK0,X0)
    | r1_tarski(sK0,k4_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_92,c_5,c_84])).

cnf(c_117,plain,
    ( r1_tarski(sK0,k4_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2))) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_96,c_5])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_183,c_170,c_117])).


%------------------------------------------------------------------------------
