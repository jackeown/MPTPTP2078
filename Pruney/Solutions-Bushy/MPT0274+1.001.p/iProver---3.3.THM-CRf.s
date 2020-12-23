%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0274+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:42:53 EST 2020

% Result     : Theorem 0.88s
% Output     : CNFRefutation 0.88s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 313 expanded)
%              Number of clauses        :   43 ( 151 expanded)
%              Number of leaves         :    6 (  51 expanded)
%              Depth                    :   16
%              Number of atoms          :  163 ( 905 expanded)
%              Number of equality atoms :   79 ( 405 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_xboole_0(k2_tarski(X0,X2),X1)
        & ~ r2_hidden(X2,X1)
        & ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(k2_tarski(X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k2_tarski(X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f1,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
      <=> ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <~> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X1,X2)
        | r2_hidden(X0,X2)
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X1,X2)
        | r2_hidden(X0,X2)
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f11])).

fof(f13,plain,
    ( ? [X0,X1,X2] :
        ( ( r2_hidden(X1,X2)
          | r2_hidden(X0,X2)
          | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) )
        & ( ( ~ r2_hidden(X1,X2)
            & ~ r2_hidden(X0,X2) )
          | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) ) )
   => ( ( r2_hidden(sK1,sK2)
        | r2_hidden(sK0,sK2)
        | k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) )
      & ( ( ~ r2_hidden(sK1,sK2)
          & ~ r2_hidden(sK0,sK2) )
        | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( ( r2_hidden(sK1,sK2)
      | r2_hidden(sK0,sK2)
      | k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) )
    & ( ( ~ r2_hidden(sK1,sK2)
        & ~ r2_hidden(sK0,sK2) )
      | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f13])).

fof(f20,plain,
    ( ~ r2_hidden(sK0,sK2)
    | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f21,plain,
    ( ~ r2_hidden(sK1,sK2)
    | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ~ ( r2_hidden(X0,X2)
        & r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f16,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f22,plain,
    ( r2_hidden(sK1,sK2)
    | r2_hidden(sK0,sK2)
    | k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_2,plain,
    ( r1_xboole_0(k2_tarski(X0,X1),X2)
    | r2_hidden(X0,X2)
    | r2_hidden(X1,X2) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_146,plain,
    ( r1_xboole_0(k2_tarski(X0_35,X1_35),X0_36)
    | r2_hidden(X0_35,X0_36)
    | r2_hidden(X1_35,X0_36) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_348,plain,
    ( r1_xboole_0(k2_tarski(X0_35,X1_35),X0_36) = iProver_top
    | r2_hidden(X0_35,X0_36) = iProver_top
    | r2_hidden(X1_35,X0_36) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_146])).

cnf(c_4,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f18])).

cnf(c_144,plain,
    ( ~ r1_xboole_0(X0_37,X0_36)
    | k4_xboole_0(X0_37,X0_36) = X0_37 ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_350,plain,
    ( k4_xboole_0(X0_37,X0_36) = X0_37
    | r1_xboole_0(X0_37,X0_36) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_144])).

cnf(c_639,plain,
    ( k4_xboole_0(k2_tarski(X0_35,X1_35),X0_36) = k2_tarski(X0_35,X1_35)
    | r2_hidden(X0_35,X0_36) = iProver_top
    | r2_hidden(X1_35,X0_36) = iProver_top ),
    inference(superposition,[status(thm)],[c_348,c_350])).

cnf(c_0,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_148,plain,
    ( k2_tarski(X0_35,X1_35) = k2_tarski(X1_35,X0_35) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_7,negated_conjecture,
    ( ~ r2_hidden(sK0,sK2)
    | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_141,negated_conjecture,
    ( ~ r2_hidden(sK0,sK2)
    | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_353,plain,
    ( k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2)
    | r2_hidden(sK0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_141])).

cnf(c_449,plain,
    ( k4_xboole_0(k2_tarski(sK1,sK0),sK2) = k2_tarski(sK1,sK0)
    | r2_hidden(sK0,sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_148,c_353])).

cnf(c_716,plain,
    ( k4_xboole_0(k2_tarski(X0_35,sK0),sK2) = k2_tarski(X0_35,sK0)
    | k4_xboole_0(k2_tarski(sK1,sK0),sK2) = k2_tarski(sK1,sK0)
    | r2_hidden(X0_35,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_639,c_449])).

cnf(c_6,negated_conjecture,
    ( ~ r2_hidden(sK1,sK2)
    | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_142,negated_conjecture,
    ( ~ r2_hidden(sK1,sK2)
    | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_352,plain,
    ( k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2)
    | r2_hidden(sK1,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_142])).

cnf(c_450,plain,
    ( k4_xboole_0(k2_tarski(sK1,sK0),sK2) = k2_tarski(sK1,sK0)
    | r2_hidden(sK1,sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_148,c_352])).

cnf(c_719,plain,
    ( k4_xboole_0(k2_tarski(sK1,X0_35),sK2) = k2_tarski(sK1,X0_35)
    | k4_xboole_0(k2_tarski(sK1,sK0),sK2) = k2_tarski(sK1,sK0)
    | r2_hidden(X0_35,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_639,c_450])).

cnf(c_757,plain,
    ( k4_xboole_0(k2_tarski(sK1,sK0),sK2) = k2_tarski(sK1,sK0)
    | r2_hidden(sK0,sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_719])).

cnf(c_761,plain,
    ( k4_xboole_0(k2_tarski(sK1,sK0),sK2) = k2_tarski(sK1,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_716,c_449,c_757])).

cnf(c_3,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) != X0 ),
    inference(cnf_transformation,[],[f19])).

cnf(c_145,plain,
    ( r1_xboole_0(X0_37,X0_36)
    | k4_xboole_0(X0_37,X0_36) != X0_37 ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_349,plain,
    ( k4_xboole_0(X0_37,X0_36) != X0_37
    | r1_xboole_0(X0_37,X0_36) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_145])).

cnf(c_766,plain,
    ( r1_xboole_0(k2_tarski(sK1,sK0),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_761,c_349])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(k2_tarski(X0,X1),X2)
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_147,plain,
    ( ~ r1_xboole_0(k2_tarski(X0_35,X1_35),X0_36)
    | ~ r2_hidden(X0_35,X0_36) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_347,plain,
    ( r1_xboole_0(k2_tarski(X0_35,X1_35),X0_36) != iProver_top
    | r2_hidden(X0_35,X0_36) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_147])).

cnf(c_567,plain,
    ( r1_xboole_0(k2_tarski(X0_35,X1_35),X0_36) != iProver_top
    | r2_hidden(X1_35,X0_36) != iProver_top ),
    inference(superposition,[status(thm)],[c_148,c_347])).

cnf(c_845,plain,
    ( r2_hidden(sK0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_766,c_567])).

cnf(c_815,plain,
    ( ~ r1_xboole_0(k2_tarski(sK1,X0_35),sK2)
    | ~ r2_hidden(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_147])).

cnf(c_817,plain,
    ( ~ r1_xboole_0(k2_tarski(sK1,sK0),sK2)
    | ~ r2_hidden(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_815])).

cnf(c_767,plain,
    ( r1_xboole_0(k2_tarski(sK1,sK0),sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_766])).

cnf(c_649,plain,
    ( k4_xboole_0(k2_tarski(sK0,sK0),sK2) = k2_tarski(sK0,sK0)
    | r2_hidden(sK0,sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_639])).

cnf(c_575,plain,
    ( r1_xboole_0(k2_tarski(X0_35,X1_35),X0_36)
    | k4_xboole_0(k2_tarski(X0_35,X1_35),X0_36) != k2_tarski(X0_35,X1_35) ),
    inference(instantiation,[status(thm)],[c_145])).

cnf(c_577,plain,
    ( r1_xboole_0(k2_tarski(sK0,sK0),sK2)
    | k4_xboole_0(k2_tarski(sK0,sK0),sK2) != k2_tarski(sK0,sK0) ),
    inference(instantiation,[status(thm)],[c_575])).

cnf(c_5,negated_conjecture,
    ( r2_hidden(sK0,sK2)
    | r2_hidden(sK1,sK2)
    | k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_143,negated_conjecture,
    ( r2_hidden(sK0,sK2)
    | r2_hidden(sK1,sK2)
    | k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_351,plain,
    ( k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)
    | r2_hidden(sK0,sK2) = iProver_top
    | r2_hidden(sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_143])).

cnf(c_448,plain,
    ( k4_xboole_0(k2_tarski(sK1,sK0),sK2) != k2_tarski(sK1,sK0)
    | r2_hidden(sK0,sK2) = iProver_top
    | r2_hidden(sK1,sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_148,c_351])).

cnf(c_465,plain,
    ( r2_hidden(sK0,sK2)
    | r2_hidden(sK1,sK2)
    | k4_xboole_0(k2_tarski(sK1,sK0),sK2) != k2_tarski(sK1,sK0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_448])).

cnf(c_160,plain,
    ( ~ r1_xboole_0(k2_tarski(sK0,sK0),sK2)
    | ~ r2_hidden(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_147])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_845,c_817,c_767,c_761,c_649,c_577,c_465,c_160])).


%------------------------------------------------------------------------------
