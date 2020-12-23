%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:43:25 EST 2020

% Result     : Theorem 3.88s
% Output     : CNFRefutation 3.88s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 171 expanded)
%              Number of clauses        :   42 (  52 expanded)
%              Number of leaves         :   10 (  41 expanded)
%              Depth                    :   19
%              Number of atoms          :  257 ( 662 expanded)
%              Number of equality atoms :   64 ( 120 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f15])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f16])).

fof(f18,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f18])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f27,f31])).

fof(f24,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f41,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f24,f31])).

fof(f46,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f41])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f28,f31])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f9])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f29,f31])).

fof(f7,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1))) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1)))
          & v1_relat_1(X1) )
     => ( ~ r1_tarski(k3_relat_1(k3_xboole_0(X0,sK2)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(sK2)))
        & v1_relat_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1)))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(k3_xboole_0(sK1,X1)),k3_xboole_0(k3_relat_1(sK1),k3_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ~ r1_tarski(k3_relat_1(k3_xboole_0(sK1,sK2)),k3_xboole_0(k3_relat_1(sK1),k3_relat_1(sK2)))
    & v1_relat_1(sK2)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f14,f21,f20])).

fof(f36,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0(sK1,sK2)),k3_xboole_0(k3_relat_1(sK1),k3_relat_1(sK2))) ),
    inference(cnf_transformation,[],[f22])).

fof(f44,plain,(
    ~ r1_tarski(k3_relat_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k3_relat_1(sK1),k4_xboole_0(k3_relat_1(sK1),k3_relat_1(sK2)))) ),
    inference(definition_unfolding,[],[f36,f31,f31])).

fof(f35,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f34,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k4_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k4_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_355,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_989,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X1
    | r2_hidden(sK0(X0,X1,X1),X1) = iProver_top
    | iProver_top != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_355])).

cnf(c_991,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X1
    | r2_hidden(sK0(X0,X1,X1),X1) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_989])).

cnf(c_4,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_352,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3659,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(X1,k4_xboole_0(X1,X2))
    | r2_hidden(sK0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X1,X2))),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_991,c_352])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X1)
    | ~ r2_hidden(sK0(X0,X1,X2),X0)
    | ~ r2_hidden(sK0(X0,X1,X2),X2)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_356,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
    | r2_hidden(sK0(X0,X1,X2),X0) != iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) != iProver_top
    | r2_hidden(sK0(X0,X1,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3679,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(X1,k4_xboole_0(X1,X0))
    | r2_hidden(sK0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(X1,k4_xboole_0(X1,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3659,c_356])).

cnf(c_3944,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3679,c_991])).

cnf(c_7,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_349,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3965,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3944,c_349])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_347,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_350,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_10,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k3_relat_1(sK1),k4_xboole_0(k3_relat_1(sK1),k3_relat_1(sK2)))) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_346,plain,
    ( r1_tarski(k3_relat_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k3_relat_1(sK1),k4_xboole_0(k3_relat_1(sK1),k3_relat_1(sK2)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_749,plain,
    ( r1_tarski(k3_relat_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k3_relat_1(sK2)) != iProver_top
    | r1_tarski(k3_relat_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k3_relat_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_350,c_346])).

cnf(c_1151,plain,
    ( r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK2) != iProver_top
    | r1_tarski(k3_relat_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k3_relat_1(sK1)) != iProver_top
    | v1_relat_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_347,c_749])).

cnf(c_651,plain,
    ( ~ r1_tarski(k3_relat_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k3_relat_1(sK2))
    | ~ r1_tarski(k3_relat_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k3_relat_1(sK1)) ),
    inference(resolution,[status(thm)],[c_10,c_6])).

cnf(c_772,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK2)
    | ~ r1_tarski(k3_relat_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k3_relat_1(sK1))
    | ~ v1_relat_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[status(thm)],[c_651,c_9])).

cnf(c_11,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_1047,plain,
    ( ~ v1_relat_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
    | ~ r1_tarski(k3_relat_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k3_relat_1(sK1))
    | ~ r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_772,c_11])).

cnf(c_1048,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK2)
    | ~ r1_tarski(k3_relat_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k3_relat_1(sK1))
    | ~ v1_relat_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    inference(renaming,[status(thm)],[c_1047])).

cnf(c_1161,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK2)
    | ~ r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1)
    | ~ v1_relat_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[status(thm)],[c_1048,c_9])).

cnf(c_12,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_1164,plain,
    ( ~ v1_relat_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
    | ~ r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1)
    | ~ r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1161,c_12])).

cnf(c_1165,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK2)
    | ~ r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1)
    | ~ v1_relat_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    inference(renaming,[status(thm)],[c_1164])).

cnf(c_1171,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK2)
    | ~ v1_relat_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1165,c_7])).

cnf(c_1172,plain,
    ( r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK2) != iProver_top
    | v1_relat_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1171])).

cnf(c_2044,plain,
    ( v1_relat_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) != iProver_top
    | r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1151,c_1172])).

cnf(c_2045,plain,
    ( r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK2) != iProver_top
    | v1_relat_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2044])).

cnf(c_4504,plain,
    ( v1_relat_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3965,c_2045])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_818,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2808,plain,
    ( v1_relat_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_818])).

cnf(c_2809,plain,
    ( v1_relat_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) = iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2808])).

cnf(c_13,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4504,c_2809,c_13])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:46:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.88/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.88/1.02  
% 3.88/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.88/1.02  
% 3.88/1.02  ------  iProver source info
% 3.88/1.02  
% 3.88/1.02  git: date: 2020-06-30 10:37:57 +0100
% 3.88/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.88/1.02  git: non_committed_changes: false
% 3.88/1.02  git: last_make_outside_of_git: false
% 3.88/1.02  
% 3.88/1.02  ------ 
% 3.88/1.02  
% 3.88/1.02  ------ Input Options
% 3.88/1.02  
% 3.88/1.02  --out_options                           all
% 3.88/1.02  --tptp_safe_out                         true
% 3.88/1.02  --problem_path                          ""
% 3.88/1.02  --include_path                          ""
% 3.88/1.02  --clausifier                            res/vclausify_rel
% 3.88/1.02  --clausifier_options                    --mode clausify
% 3.88/1.02  --stdin                                 false
% 3.88/1.02  --stats_out                             sel
% 3.88/1.02  
% 3.88/1.02  ------ General Options
% 3.88/1.02  
% 3.88/1.02  --fof                                   false
% 3.88/1.02  --time_out_real                         604.99
% 3.88/1.02  --time_out_virtual                      -1.
% 3.88/1.02  --symbol_type_check                     false
% 3.88/1.02  --clausify_out                          false
% 3.88/1.02  --sig_cnt_out                           false
% 3.88/1.02  --trig_cnt_out                          false
% 3.88/1.02  --trig_cnt_out_tolerance                1.
% 3.88/1.02  --trig_cnt_out_sk_spl                   false
% 3.88/1.02  --abstr_cl_out                          false
% 3.88/1.02  
% 3.88/1.02  ------ Global Options
% 3.88/1.02  
% 3.88/1.02  --schedule                              none
% 3.88/1.02  --add_important_lit                     false
% 3.88/1.02  --prop_solver_per_cl                    1000
% 3.88/1.02  --min_unsat_core                        false
% 3.88/1.02  --soft_assumptions                      false
% 3.88/1.02  --soft_lemma_size                       3
% 3.88/1.02  --prop_impl_unit_size                   0
% 3.88/1.02  --prop_impl_unit                        []
% 3.88/1.02  --share_sel_clauses                     true
% 3.88/1.02  --reset_solvers                         false
% 3.88/1.02  --bc_imp_inh                            [conj_cone]
% 3.88/1.02  --conj_cone_tolerance                   3.
% 3.88/1.02  --extra_neg_conj                        none
% 3.88/1.02  --large_theory_mode                     true
% 3.88/1.02  --prolific_symb_bound                   200
% 3.88/1.02  --lt_threshold                          2000
% 3.88/1.02  --clause_weak_htbl                      true
% 3.88/1.02  --gc_record_bc_elim                     false
% 3.88/1.02  
% 3.88/1.02  ------ Preprocessing Options
% 3.88/1.02  
% 3.88/1.02  --preprocessing_flag                    true
% 3.88/1.02  --time_out_prep_mult                    0.1
% 3.88/1.02  --splitting_mode                        input
% 3.88/1.02  --splitting_grd                         true
% 3.88/1.02  --splitting_cvd                         false
% 3.88/1.02  --splitting_cvd_svl                     false
% 3.88/1.02  --splitting_nvd                         32
% 3.88/1.02  --sub_typing                            true
% 3.88/1.02  --prep_gs_sim                           false
% 3.88/1.02  --prep_unflatten                        true
% 3.88/1.02  --prep_res_sim                          true
% 3.88/1.02  --prep_upred                            true
% 3.88/1.02  --prep_sem_filter                       exhaustive
% 3.88/1.02  --prep_sem_filter_out                   false
% 3.88/1.02  --pred_elim                             false
% 3.88/1.02  --res_sim_input                         true
% 3.88/1.02  --eq_ax_congr_red                       true
% 3.88/1.02  --pure_diseq_elim                       true
% 3.88/1.02  --brand_transform                       false
% 3.88/1.02  --non_eq_to_eq                          false
% 3.88/1.02  --prep_def_merge                        true
% 3.88/1.02  --prep_def_merge_prop_impl              false
% 3.88/1.02  --prep_def_merge_mbd                    true
% 3.88/1.02  --prep_def_merge_tr_red                 false
% 3.88/1.02  --prep_def_merge_tr_cl                  false
% 3.88/1.02  --smt_preprocessing                     true
% 3.88/1.02  --smt_ac_axioms                         fast
% 3.88/1.02  --preprocessed_out                      false
% 3.88/1.02  --preprocessed_stats                    false
% 3.88/1.02  
% 3.88/1.02  ------ Abstraction refinement Options
% 3.88/1.02  
% 3.88/1.02  --abstr_ref                             []
% 3.88/1.02  --abstr_ref_prep                        false
% 3.88/1.02  --abstr_ref_until_sat                   false
% 3.88/1.02  --abstr_ref_sig_restrict                funpre
% 3.88/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.88/1.02  --abstr_ref_under                       []
% 3.88/1.02  
% 3.88/1.02  ------ SAT Options
% 3.88/1.02  
% 3.88/1.02  --sat_mode                              false
% 3.88/1.02  --sat_fm_restart_options                ""
% 3.88/1.02  --sat_gr_def                            false
% 3.88/1.02  --sat_epr_types                         true
% 3.88/1.02  --sat_non_cyclic_types                  false
% 3.88/1.02  --sat_finite_models                     false
% 3.88/1.02  --sat_fm_lemmas                         false
% 3.88/1.02  --sat_fm_prep                           false
% 3.88/1.02  --sat_fm_uc_incr                        true
% 3.88/1.02  --sat_out_model                         small
% 3.88/1.02  --sat_out_clauses                       false
% 3.88/1.02  
% 3.88/1.02  ------ QBF Options
% 3.88/1.02  
% 3.88/1.02  --qbf_mode                              false
% 3.88/1.02  --qbf_elim_univ                         false
% 3.88/1.02  --qbf_dom_inst                          none
% 3.88/1.02  --qbf_dom_pre_inst                      false
% 3.88/1.02  --qbf_sk_in                             false
% 3.88/1.02  --qbf_pred_elim                         true
% 3.88/1.02  --qbf_split                             512
% 3.88/1.02  
% 3.88/1.02  ------ BMC1 Options
% 3.88/1.02  
% 3.88/1.02  --bmc1_incremental                      false
% 3.88/1.02  --bmc1_axioms                           reachable_all
% 3.88/1.02  --bmc1_min_bound                        0
% 3.88/1.02  --bmc1_max_bound                        -1
% 3.88/1.02  --bmc1_max_bound_default                -1
% 3.88/1.02  --bmc1_symbol_reachability              true
% 3.88/1.02  --bmc1_property_lemmas                  false
% 3.88/1.02  --bmc1_k_induction                      false
% 3.88/1.02  --bmc1_non_equiv_states                 false
% 3.88/1.02  --bmc1_deadlock                         false
% 3.88/1.02  --bmc1_ucm                              false
% 3.88/1.02  --bmc1_add_unsat_core                   none
% 3.88/1.02  --bmc1_unsat_core_children              false
% 3.88/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.88/1.02  --bmc1_out_stat                         full
% 3.88/1.02  --bmc1_ground_init                      false
% 3.88/1.02  --bmc1_pre_inst_next_state              false
% 3.88/1.02  --bmc1_pre_inst_state                   false
% 3.88/1.02  --bmc1_pre_inst_reach_state             false
% 3.88/1.02  --bmc1_out_unsat_core                   false
% 3.88/1.02  --bmc1_aig_witness_out                  false
% 3.88/1.02  --bmc1_verbose                          false
% 3.88/1.02  --bmc1_dump_clauses_tptp                false
% 3.88/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.88/1.02  --bmc1_dump_file                        -
% 3.88/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.88/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.88/1.02  --bmc1_ucm_extend_mode                  1
% 3.88/1.02  --bmc1_ucm_init_mode                    2
% 3.88/1.02  --bmc1_ucm_cone_mode                    none
% 3.88/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.88/1.02  --bmc1_ucm_relax_model                  4
% 3.88/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.88/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.88/1.02  --bmc1_ucm_layered_model                none
% 3.88/1.02  --bmc1_ucm_max_lemma_size               10
% 3.88/1.02  
% 3.88/1.02  ------ AIG Options
% 3.88/1.02  
% 3.88/1.02  --aig_mode                              false
% 3.88/1.02  
% 3.88/1.02  ------ Instantiation Options
% 3.88/1.02  
% 3.88/1.02  --instantiation_flag                    true
% 3.88/1.02  --inst_sos_flag                         false
% 3.88/1.02  --inst_sos_phase                        true
% 3.88/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.88/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.88/1.02  --inst_lit_sel_side                     num_symb
% 3.88/1.02  --inst_solver_per_active                1400
% 3.88/1.02  --inst_solver_calls_frac                1.
% 3.88/1.02  --inst_passive_queue_type               priority_queues
% 3.88/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.88/1.02  --inst_passive_queues_freq              [25;2]
% 3.88/1.02  --inst_dismatching                      true
% 3.88/1.02  --inst_eager_unprocessed_to_passive     true
% 3.88/1.02  --inst_prop_sim_given                   true
% 3.88/1.02  --inst_prop_sim_new                     false
% 3.88/1.02  --inst_subs_new                         false
% 3.88/1.02  --inst_eq_res_simp                      false
% 3.88/1.02  --inst_subs_given                       false
% 3.88/1.02  --inst_orphan_elimination               true
% 3.88/1.02  --inst_learning_loop_flag               true
% 3.88/1.02  --inst_learning_start                   3000
% 3.88/1.02  --inst_learning_factor                  2
% 3.88/1.02  --inst_start_prop_sim_after_learn       3
% 3.88/1.02  --inst_sel_renew                        solver
% 3.88/1.02  --inst_lit_activity_flag                true
% 3.88/1.02  --inst_restr_to_given                   false
% 3.88/1.02  --inst_activity_threshold               500
% 3.88/1.02  --inst_out_proof                        true
% 3.88/1.02  
% 3.88/1.02  ------ Resolution Options
% 3.88/1.02  
% 3.88/1.02  --resolution_flag                       true
% 3.88/1.02  --res_lit_sel                           adaptive
% 3.88/1.02  --res_lit_sel_side                      none
% 3.88/1.02  --res_ordering                          kbo
% 3.88/1.02  --res_to_prop_solver                    active
% 3.88/1.02  --res_prop_simpl_new                    false
% 3.88/1.02  --res_prop_simpl_given                  true
% 3.88/1.02  --res_passive_queue_type                priority_queues
% 3.88/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.88/1.02  --res_passive_queues_freq               [15;5]
% 3.88/1.02  --res_forward_subs                      full
% 3.88/1.02  --res_backward_subs                     full
% 3.88/1.02  --res_forward_subs_resolution           true
% 3.88/1.02  --res_backward_subs_resolution          true
% 3.88/1.02  --res_orphan_elimination                true
% 3.88/1.02  --res_time_limit                        2.
% 3.88/1.02  --res_out_proof                         true
% 3.88/1.02  
% 3.88/1.02  ------ Superposition Options
% 3.88/1.02  
% 3.88/1.02  --superposition_flag                    true
% 3.88/1.02  --sup_passive_queue_type                priority_queues
% 3.88/1.02  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.88/1.02  --sup_passive_queues_freq               [1;4]
% 3.88/1.02  --demod_completeness_check              fast
% 3.88/1.02  --demod_use_ground                      true
% 3.88/1.02  --sup_to_prop_solver                    passive
% 3.88/1.02  --sup_prop_simpl_new                    true
% 3.88/1.02  --sup_prop_simpl_given                  true
% 3.88/1.02  --sup_fun_splitting                     false
% 3.88/1.02  --sup_smt_interval                      50000
% 3.88/1.02  
% 3.88/1.02  ------ Superposition Simplification Setup
% 3.88/1.02  
% 3.88/1.02  --sup_indices_passive                   []
% 3.88/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.88/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.88/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.88/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.88/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.88/1.02  --sup_full_bw                           [BwDemod]
% 3.88/1.02  --sup_immed_triv                        [TrivRules]
% 3.88/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.88/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.88/1.02  --sup_immed_bw_main                     []
% 3.88/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.88/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.88/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.88/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.88/1.02  
% 3.88/1.02  ------ Combination Options
% 3.88/1.02  
% 3.88/1.02  --comb_res_mult                         3
% 3.88/1.02  --comb_sup_mult                         2
% 3.88/1.02  --comb_inst_mult                        10
% 3.88/1.02  
% 3.88/1.02  ------ Debug Options
% 3.88/1.02  
% 3.88/1.02  --dbg_backtrace                         false
% 3.88/1.02  --dbg_dump_prop_clauses                 false
% 3.88/1.02  --dbg_dump_prop_clauses_file            -
% 3.88/1.02  --dbg_out_stat                          false
% 3.88/1.02  ------ Parsing...
% 3.88/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.88/1.02  
% 3.88/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.88/1.02  
% 3.88/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.88/1.02  
% 3.88/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.88/1.02  ------ Proving...
% 3.88/1.02  ------ Problem Properties 
% 3.88/1.02  
% 3.88/1.02  
% 3.88/1.02  clauses                                 13
% 3.88/1.02  conjectures                             3
% 3.88/1.02  EPR                                     2
% 3.88/1.02  Horn                                    11
% 3.88/1.02  unary                                   4
% 3.88/1.02  binary                                  3
% 3.88/1.02  lits                                    30
% 3.88/1.02  lits eq                                 3
% 3.88/1.02  fd_pure                                 0
% 3.88/1.02  fd_pseudo                               0
% 3.88/1.02  fd_cond                                 0
% 3.88/1.02  fd_pseudo_cond                          3
% 3.88/1.02  AC symbols                              0
% 3.88/1.02  
% 3.88/1.02  ------ Input Options Time Limit: Unbounded
% 3.88/1.02  
% 3.88/1.02  
% 3.88/1.02  ------ 
% 3.88/1.02  Current options:
% 3.88/1.02  ------ 
% 3.88/1.02  
% 3.88/1.02  ------ Input Options
% 3.88/1.02  
% 3.88/1.02  --out_options                           all
% 3.88/1.02  --tptp_safe_out                         true
% 3.88/1.02  --problem_path                          ""
% 3.88/1.02  --include_path                          ""
% 3.88/1.02  --clausifier                            res/vclausify_rel
% 3.88/1.02  --clausifier_options                    --mode clausify
% 3.88/1.02  --stdin                                 false
% 3.88/1.02  --stats_out                             sel
% 3.88/1.02  
% 3.88/1.02  ------ General Options
% 3.88/1.02  
% 3.88/1.02  --fof                                   false
% 3.88/1.02  --time_out_real                         604.99
% 3.88/1.02  --time_out_virtual                      -1.
% 3.88/1.02  --symbol_type_check                     false
% 3.88/1.02  --clausify_out                          false
% 3.88/1.02  --sig_cnt_out                           false
% 3.88/1.02  --trig_cnt_out                          false
% 3.88/1.02  --trig_cnt_out_tolerance                1.
% 3.88/1.02  --trig_cnt_out_sk_spl                   false
% 3.88/1.02  --abstr_cl_out                          false
% 3.88/1.02  
% 3.88/1.02  ------ Global Options
% 3.88/1.02  
% 3.88/1.02  --schedule                              none
% 3.88/1.02  --add_important_lit                     false
% 3.88/1.02  --prop_solver_per_cl                    1000
% 3.88/1.02  --min_unsat_core                        false
% 3.88/1.02  --soft_assumptions                      false
% 3.88/1.02  --soft_lemma_size                       3
% 3.88/1.02  --prop_impl_unit_size                   0
% 3.88/1.02  --prop_impl_unit                        []
% 3.88/1.02  --share_sel_clauses                     true
% 3.88/1.02  --reset_solvers                         false
% 3.88/1.02  --bc_imp_inh                            [conj_cone]
% 3.88/1.02  --conj_cone_tolerance                   3.
% 3.88/1.02  --extra_neg_conj                        none
% 3.88/1.02  --large_theory_mode                     true
% 3.88/1.02  --prolific_symb_bound                   200
% 3.88/1.02  --lt_threshold                          2000
% 3.88/1.02  --clause_weak_htbl                      true
% 3.88/1.02  --gc_record_bc_elim                     false
% 3.88/1.02  
% 3.88/1.02  ------ Preprocessing Options
% 3.88/1.02  
% 3.88/1.02  --preprocessing_flag                    true
% 3.88/1.02  --time_out_prep_mult                    0.1
% 3.88/1.02  --splitting_mode                        input
% 3.88/1.02  --splitting_grd                         true
% 3.88/1.02  --splitting_cvd                         false
% 3.88/1.02  --splitting_cvd_svl                     false
% 3.88/1.02  --splitting_nvd                         32
% 3.88/1.02  --sub_typing                            true
% 3.88/1.02  --prep_gs_sim                           false
% 3.88/1.02  --prep_unflatten                        true
% 3.88/1.02  --prep_res_sim                          true
% 3.88/1.02  --prep_upred                            true
% 3.88/1.02  --prep_sem_filter                       exhaustive
% 3.88/1.02  --prep_sem_filter_out                   false
% 3.88/1.02  --pred_elim                             false
% 3.88/1.02  --res_sim_input                         true
% 3.88/1.02  --eq_ax_congr_red                       true
% 3.88/1.02  --pure_diseq_elim                       true
% 3.88/1.02  --brand_transform                       false
% 3.88/1.02  --non_eq_to_eq                          false
% 3.88/1.02  --prep_def_merge                        true
% 3.88/1.02  --prep_def_merge_prop_impl              false
% 3.88/1.02  --prep_def_merge_mbd                    true
% 3.88/1.02  --prep_def_merge_tr_red                 false
% 3.88/1.02  --prep_def_merge_tr_cl                  false
% 3.88/1.02  --smt_preprocessing                     true
% 3.88/1.02  --smt_ac_axioms                         fast
% 3.88/1.02  --preprocessed_out                      false
% 3.88/1.02  --preprocessed_stats                    false
% 3.88/1.02  
% 3.88/1.02  ------ Abstraction refinement Options
% 3.88/1.02  
% 3.88/1.02  --abstr_ref                             []
% 3.88/1.02  --abstr_ref_prep                        false
% 3.88/1.02  --abstr_ref_until_sat                   false
% 3.88/1.02  --abstr_ref_sig_restrict                funpre
% 3.88/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.88/1.02  --abstr_ref_under                       []
% 3.88/1.02  
% 3.88/1.02  ------ SAT Options
% 3.88/1.02  
% 3.88/1.02  --sat_mode                              false
% 3.88/1.02  --sat_fm_restart_options                ""
% 3.88/1.02  --sat_gr_def                            false
% 3.88/1.02  --sat_epr_types                         true
% 3.88/1.02  --sat_non_cyclic_types                  false
% 3.88/1.02  --sat_finite_models                     false
% 3.88/1.02  --sat_fm_lemmas                         false
% 3.88/1.02  --sat_fm_prep                           false
% 3.88/1.02  --sat_fm_uc_incr                        true
% 3.88/1.02  --sat_out_model                         small
% 3.88/1.02  --sat_out_clauses                       false
% 3.88/1.02  
% 3.88/1.02  ------ QBF Options
% 3.88/1.02  
% 3.88/1.02  --qbf_mode                              false
% 3.88/1.02  --qbf_elim_univ                         false
% 3.88/1.02  --qbf_dom_inst                          none
% 3.88/1.02  --qbf_dom_pre_inst                      false
% 3.88/1.02  --qbf_sk_in                             false
% 3.88/1.02  --qbf_pred_elim                         true
% 3.88/1.02  --qbf_split                             512
% 3.88/1.02  
% 3.88/1.02  ------ BMC1 Options
% 3.88/1.02  
% 3.88/1.02  --bmc1_incremental                      false
% 3.88/1.02  --bmc1_axioms                           reachable_all
% 3.88/1.02  --bmc1_min_bound                        0
% 3.88/1.02  --bmc1_max_bound                        -1
% 3.88/1.02  --bmc1_max_bound_default                -1
% 3.88/1.02  --bmc1_symbol_reachability              true
% 3.88/1.02  --bmc1_property_lemmas                  false
% 3.88/1.02  --bmc1_k_induction                      false
% 3.88/1.02  --bmc1_non_equiv_states                 false
% 3.88/1.02  --bmc1_deadlock                         false
% 3.88/1.02  --bmc1_ucm                              false
% 3.88/1.02  --bmc1_add_unsat_core                   none
% 3.88/1.02  --bmc1_unsat_core_children              false
% 3.88/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.88/1.02  --bmc1_out_stat                         full
% 3.88/1.02  --bmc1_ground_init                      false
% 3.88/1.02  --bmc1_pre_inst_next_state              false
% 3.88/1.02  --bmc1_pre_inst_state                   false
% 3.88/1.02  --bmc1_pre_inst_reach_state             false
% 3.88/1.02  --bmc1_out_unsat_core                   false
% 3.88/1.02  --bmc1_aig_witness_out                  false
% 3.88/1.02  --bmc1_verbose                          false
% 3.88/1.02  --bmc1_dump_clauses_tptp                false
% 3.88/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.88/1.02  --bmc1_dump_file                        -
% 3.88/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.88/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.88/1.02  --bmc1_ucm_extend_mode                  1
% 3.88/1.02  --bmc1_ucm_init_mode                    2
% 3.88/1.02  --bmc1_ucm_cone_mode                    none
% 3.88/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.88/1.02  --bmc1_ucm_relax_model                  4
% 3.88/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.88/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.88/1.02  --bmc1_ucm_layered_model                none
% 3.88/1.02  --bmc1_ucm_max_lemma_size               10
% 3.88/1.02  
% 3.88/1.02  ------ AIG Options
% 3.88/1.02  
% 3.88/1.02  --aig_mode                              false
% 3.88/1.02  
% 3.88/1.02  ------ Instantiation Options
% 3.88/1.02  
% 3.88/1.02  --instantiation_flag                    true
% 3.88/1.02  --inst_sos_flag                         false
% 3.88/1.02  --inst_sos_phase                        true
% 3.88/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.88/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.88/1.02  --inst_lit_sel_side                     num_symb
% 3.88/1.02  --inst_solver_per_active                1400
% 3.88/1.02  --inst_solver_calls_frac                1.
% 3.88/1.02  --inst_passive_queue_type               priority_queues
% 3.88/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.88/1.02  --inst_passive_queues_freq              [25;2]
% 3.88/1.02  --inst_dismatching                      true
% 3.88/1.02  --inst_eager_unprocessed_to_passive     true
% 3.88/1.02  --inst_prop_sim_given                   true
% 3.88/1.02  --inst_prop_sim_new                     false
% 3.88/1.02  --inst_subs_new                         false
% 3.88/1.02  --inst_eq_res_simp                      false
% 3.88/1.02  --inst_subs_given                       false
% 3.88/1.02  --inst_orphan_elimination               true
% 3.88/1.02  --inst_learning_loop_flag               true
% 3.88/1.02  --inst_learning_start                   3000
% 3.88/1.02  --inst_learning_factor                  2
% 3.88/1.02  --inst_start_prop_sim_after_learn       3
% 3.88/1.02  --inst_sel_renew                        solver
% 3.88/1.02  --inst_lit_activity_flag                true
% 3.88/1.02  --inst_restr_to_given                   false
% 3.88/1.02  --inst_activity_threshold               500
% 3.88/1.02  --inst_out_proof                        true
% 3.88/1.02  
% 3.88/1.02  ------ Resolution Options
% 3.88/1.02  
% 3.88/1.02  --resolution_flag                       true
% 3.88/1.02  --res_lit_sel                           adaptive
% 3.88/1.02  --res_lit_sel_side                      none
% 3.88/1.02  --res_ordering                          kbo
% 3.88/1.02  --res_to_prop_solver                    active
% 3.88/1.02  --res_prop_simpl_new                    false
% 3.88/1.02  --res_prop_simpl_given                  true
% 3.88/1.02  --res_passive_queue_type                priority_queues
% 3.88/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.88/1.02  --res_passive_queues_freq               [15;5]
% 3.88/1.02  --res_forward_subs                      full
% 3.88/1.02  --res_backward_subs                     full
% 3.88/1.02  --res_forward_subs_resolution           true
% 3.88/1.02  --res_backward_subs_resolution          true
% 3.88/1.02  --res_orphan_elimination                true
% 3.88/1.02  --res_time_limit                        2.
% 3.88/1.02  --res_out_proof                         true
% 3.88/1.02  
% 3.88/1.02  ------ Superposition Options
% 3.88/1.02  
% 3.88/1.02  --superposition_flag                    true
% 3.88/1.02  --sup_passive_queue_type                priority_queues
% 3.88/1.02  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.88/1.02  --sup_passive_queues_freq               [1;4]
% 3.88/1.02  --demod_completeness_check              fast
% 3.88/1.02  --demod_use_ground                      true
% 3.88/1.02  --sup_to_prop_solver                    passive
% 3.88/1.02  --sup_prop_simpl_new                    true
% 3.88/1.02  --sup_prop_simpl_given                  true
% 3.88/1.02  --sup_fun_splitting                     false
% 3.88/1.02  --sup_smt_interval                      50000
% 3.88/1.02  
% 3.88/1.02  ------ Superposition Simplification Setup
% 3.88/1.02  
% 3.88/1.02  --sup_indices_passive                   []
% 3.88/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.88/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.88/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.88/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.88/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.88/1.02  --sup_full_bw                           [BwDemod]
% 3.88/1.02  --sup_immed_triv                        [TrivRules]
% 3.88/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.88/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.88/1.02  --sup_immed_bw_main                     []
% 3.88/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.88/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.88/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.88/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.88/1.02  
% 3.88/1.02  ------ Combination Options
% 3.88/1.02  
% 3.88/1.02  --comb_res_mult                         3
% 3.88/1.02  --comb_sup_mult                         2
% 3.88/1.02  --comb_inst_mult                        10
% 3.88/1.02  
% 3.88/1.02  ------ Debug Options
% 3.88/1.02  
% 3.88/1.02  --dbg_backtrace                         false
% 3.88/1.02  --dbg_dump_prop_clauses                 false
% 3.88/1.02  --dbg_dump_prop_clauses_file            -
% 3.88/1.02  --dbg_out_stat                          false
% 3.88/1.02  
% 3.88/1.02  
% 3.88/1.02  
% 3.88/1.02  
% 3.88/1.02  ------ Proving...
% 3.88/1.02  
% 3.88/1.02  
% 3.88/1.02  % SZS status Theorem for theBenchmark.p
% 3.88/1.02  
% 3.88/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 3.88/1.02  
% 3.88/1.02  fof(f1,axiom,(
% 3.88/1.02    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.88/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.88/1.02  
% 3.88/1.02  fof(f15,plain,(
% 3.88/1.02    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.88/1.02    inference(nnf_transformation,[],[f1])).
% 3.88/1.02  
% 3.88/1.02  fof(f16,plain,(
% 3.88/1.02    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.88/1.02    inference(flattening,[],[f15])).
% 3.88/1.02  
% 3.88/1.02  fof(f17,plain,(
% 3.88/1.02    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.88/1.02    inference(rectify,[],[f16])).
% 3.88/1.02  
% 3.88/1.02  fof(f18,plain,(
% 3.88/1.02    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 3.88/1.02    introduced(choice_axiom,[])).
% 3.88/1.02  
% 3.88/1.02  fof(f19,plain,(
% 3.88/1.02    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.88/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f18])).
% 3.88/1.02  
% 3.88/1.02  fof(f27,plain,(
% 3.88/1.02    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.88/1.02    inference(cnf_transformation,[],[f19])).
% 3.88/1.02  
% 3.88/1.02  fof(f4,axiom,(
% 3.88/1.02    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.88/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.88/1.02  
% 3.88/1.02  fof(f31,plain,(
% 3.88/1.02    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.88/1.02    inference(cnf_transformation,[],[f4])).
% 3.88/1.02  
% 3.88/1.02  fof(f38,plain,(
% 3.88/1.02    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.88/1.02    inference(definition_unfolding,[],[f27,f31])).
% 3.88/1.02  
% 3.88/1.02  fof(f24,plain,(
% 3.88/1.02    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 3.88/1.02    inference(cnf_transformation,[],[f19])).
% 3.88/1.02  
% 3.88/1.02  fof(f41,plain,(
% 3.88/1.02    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2) )),
% 3.88/1.02    inference(definition_unfolding,[],[f24,f31])).
% 3.88/1.02  
% 3.88/1.02  fof(f46,plain,(
% 3.88/1.02    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 3.88/1.02    inference(equality_resolution,[],[f41])).
% 3.88/1.02  
% 3.88/1.02  fof(f28,plain,(
% 3.88/1.02    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.88/1.02    inference(cnf_transformation,[],[f19])).
% 3.88/1.02  
% 3.88/1.02  fof(f37,plain,(
% 3.88/1.02    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.88/1.02    inference(definition_unfolding,[],[f28,f31])).
% 3.88/1.02  
% 3.88/1.02  fof(f3,axiom,(
% 3.88/1.02    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 3.88/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.88/1.02  
% 3.88/1.02  fof(f30,plain,(
% 3.88/1.02    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 3.88/1.02    inference(cnf_transformation,[],[f3])).
% 3.88/1.02  
% 3.88/1.02  fof(f6,axiom,(
% 3.88/1.02    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 3.88/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.88/1.02  
% 3.88/1.02  fof(f12,plain,(
% 3.88/1.02    ! [X0] : (! [X1] : ((r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.88/1.02    inference(ennf_transformation,[],[f6])).
% 3.88/1.02  
% 3.88/1.02  fof(f13,plain,(
% 3.88/1.02    ! [X0] : (! [X1] : (r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.88/1.02    inference(flattening,[],[f12])).
% 3.88/1.02  
% 3.88/1.02  fof(f33,plain,(
% 3.88/1.02    ( ! [X0,X1] : (r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.88/1.02    inference(cnf_transformation,[],[f13])).
% 3.88/1.02  
% 3.88/1.02  fof(f2,axiom,(
% 3.88/1.02    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 3.88/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.88/1.02  
% 3.88/1.02  fof(f9,plain,(
% 3.88/1.02    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 3.88/1.02    inference(ennf_transformation,[],[f2])).
% 3.88/1.02  
% 3.88/1.02  fof(f10,plain,(
% 3.88/1.02    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 3.88/1.02    inference(flattening,[],[f9])).
% 3.88/1.02  
% 3.88/1.02  fof(f29,plain,(
% 3.88/1.02    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 3.88/1.02    inference(cnf_transformation,[],[f10])).
% 3.88/1.02  
% 3.88/1.02  fof(f43,plain,(
% 3.88/1.02    ( ! [X2,X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 3.88/1.02    inference(definition_unfolding,[],[f29,f31])).
% 3.88/1.02  
% 3.88/1.02  fof(f7,conjecture,(
% 3.88/1.02    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1)))))),
% 3.88/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.88/1.02  
% 3.88/1.02  fof(f8,negated_conjecture,(
% 3.88/1.02    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1)))))),
% 3.88/1.02    inference(negated_conjecture,[],[f7])).
% 3.88/1.02  
% 3.88/1.02  fof(f14,plain,(
% 3.88/1.02    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 3.88/1.02    inference(ennf_transformation,[],[f8])).
% 3.88/1.02  
% 3.88/1.02  fof(f21,plain,(
% 3.88/1.02    ( ! [X0] : (? [X1] : (~r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1))) & v1_relat_1(X1)) => (~r1_tarski(k3_relat_1(k3_xboole_0(X0,sK2)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(sK2))) & v1_relat_1(sK2))) )),
% 3.88/1.02    introduced(choice_axiom,[])).
% 3.88/1.02  
% 3.88/1.02  fof(f20,plain,(
% 3.88/1.02    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k3_relat_1(k3_xboole_0(sK1,X1)),k3_xboole_0(k3_relat_1(sK1),k3_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(sK1))),
% 3.88/1.02    introduced(choice_axiom,[])).
% 3.88/1.02  
% 3.88/1.02  fof(f22,plain,(
% 3.88/1.02    (~r1_tarski(k3_relat_1(k3_xboole_0(sK1,sK2)),k3_xboole_0(k3_relat_1(sK1),k3_relat_1(sK2))) & v1_relat_1(sK2)) & v1_relat_1(sK1)),
% 3.88/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f14,f21,f20])).
% 3.88/1.02  
% 3.88/1.02  fof(f36,plain,(
% 3.88/1.02    ~r1_tarski(k3_relat_1(k3_xboole_0(sK1,sK2)),k3_xboole_0(k3_relat_1(sK1),k3_relat_1(sK2)))),
% 3.88/1.02    inference(cnf_transformation,[],[f22])).
% 3.88/1.02  
% 3.88/1.02  fof(f44,plain,(
% 3.88/1.02    ~r1_tarski(k3_relat_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k3_relat_1(sK1),k4_xboole_0(k3_relat_1(sK1),k3_relat_1(sK2))))),
% 3.88/1.02    inference(definition_unfolding,[],[f36,f31,f31])).
% 3.88/1.02  
% 3.88/1.02  fof(f35,plain,(
% 3.88/1.02    v1_relat_1(sK2)),
% 3.88/1.02    inference(cnf_transformation,[],[f22])).
% 3.88/1.02  
% 3.88/1.02  fof(f34,plain,(
% 3.88/1.02    v1_relat_1(sK1)),
% 3.88/1.02    inference(cnf_transformation,[],[f22])).
% 3.88/1.02  
% 3.88/1.02  fof(f5,axiom,(
% 3.88/1.02    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k4_xboole_0(X0,X1)))),
% 3.88/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.88/1.02  
% 3.88/1.02  fof(f11,plain,(
% 3.88/1.02    ! [X0,X1] : (v1_relat_1(k4_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 3.88/1.02    inference(ennf_transformation,[],[f5])).
% 3.88/1.02  
% 3.88/1.02  fof(f32,plain,(
% 3.88/1.02    ( ! [X0,X1] : (v1_relat_1(k4_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 3.88/1.02    inference(cnf_transformation,[],[f11])).
% 3.88/1.02  
% 3.88/1.02  cnf(c_1,plain,
% 3.88/1.02      ( r2_hidden(sK0(X0,X1,X2),X1)
% 3.88/1.02      | r2_hidden(sK0(X0,X1,X2),X2)
% 3.88/1.02      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
% 3.88/1.02      inference(cnf_transformation,[],[f38]) ).
% 3.88/1.02  
% 3.88/1.02  cnf(c_355,plain,
% 3.88/1.02      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
% 3.88/1.02      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top
% 3.88/1.02      | r2_hidden(sK0(X0,X1,X2),X1) = iProver_top ),
% 3.88/1.02      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.88/1.02  
% 3.88/1.02  cnf(c_989,plain,
% 3.88/1.02      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X1
% 3.88/1.02      | r2_hidden(sK0(X0,X1,X1),X1) = iProver_top
% 3.88/1.02      | iProver_top != iProver_top ),
% 3.88/1.02      inference(equality_factoring,[status(thm)],[c_355]) ).
% 3.88/1.02  
% 3.88/1.02  cnf(c_991,plain,
% 3.88/1.02      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X1
% 3.88/1.02      | r2_hidden(sK0(X0,X1,X1),X1) = iProver_top ),
% 3.88/1.02      inference(equality_resolution_simp,[status(thm)],[c_989]) ).
% 3.88/1.02  
% 3.88/1.02  cnf(c_4,plain,
% 3.88/1.02      ( r2_hidden(X0,X1)
% 3.88/1.02      | ~ r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
% 3.88/1.02      inference(cnf_transformation,[],[f46]) ).
% 3.88/1.02  
% 3.88/1.02  cnf(c_352,plain,
% 3.88/1.02      ( r2_hidden(X0,X1) = iProver_top
% 3.88/1.02      | r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) != iProver_top ),
% 3.88/1.02      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.88/1.02  
% 3.88/1.02  cnf(c_3659,plain,
% 3.88/1.02      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(X1,k4_xboole_0(X1,X2))
% 3.88/1.02      | r2_hidden(sK0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X1,X2))),X2) = iProver_top ),
% 3.88/1.02      inference(superposition,[status(thm)],[c_991,c_352]) ).
% 3.88/1.02  
% 3.88/1.02  cnf(c_0,plain,
% 3.88/1.02      ( ~ r2_hidden(sK0(X0,X1,X2),X1)
% 3.88/1.02      | ~ r2_hidden(sK0(X0,X1,X2),X0)
% 3.88/1.02      | ~ r2_hidden(sK0(X0,X1,X2),X2)
% 3.88/1.02      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
% 3.88/1.02      inference(cnf_transformation,[],[f37]) ).
% 3.88/1.02  
% 3.88/1.02  cnf(c_356,plain,
% 3.88/1.02      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
% 3.88/1.02      | r2_hidden(sK0(X0,X1,X2),X0) != iProver_top
% 3.88/1.02      | r2_hidden(sK0(X0,X1,X2),X2) != iProver_top
% 3.88/1.02      | r2_hidden(sK0(X0,X1,X2),X1) != iProver_top ),
% 3.88/1.02      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.88/1.02  
% 3.88/1.02  cnf(c_3679,plain,
% 3.88/1.02      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(X1,k4_xboole_0(X1,X0))
% 3.88/1.02      | r2_hidden(sK0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(X1,k4_xboole_0(X1,X0))) != iProver_top ),
% 3.88/1.02      inference(superposition,[status(thm)],[c_3659,c_356]) ).
% 3.88/1.02  
% 3.88/1.02  cnf(c_3944,plain,
% 3.88/1.02      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 3.88/1.02      inference(forward_subsumption_resolution,
% 3.88/1.02                [status(thm)],
% 3.88/1.02                [c_3679,c_991]) ).
% 3.88/1.02  
% 3.88/1.02  cnf(c_7,plain,
% 3.88/1.02      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 3.88/1.02      inference(cnf_transformation,[],[f30]) ).
% 3.88/1.02  
% 3.88/1.02  cnf(c_349,plain,
% 3.88/1.02      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 3.88/1.02      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.88/1.02  
% 3.88/1.02  cnf(c_3965,plain,
% 3.88/1.02      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = iProver_top ),
% 3.88/1.02      inference(superposition,[status(thm)],[c_3944,c_349]) ).
% 3.88/1.02  
% 3.88/1.02  cnf(c_9,plain,
% 3.88/1.02      ( ~ r1_tarski(X0,X1)
% 3.88/1.02      | r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
% 3.88/1.02      | ~ v1_relat_1(X0)
% 3.88/1.02      | ~ v1_relat_1(X1) ),
% 3.88/1.02      inference(cnf_transformation,[],[f33]) ).
% 3.88/1.02  
% 3.88/1.02  cnf(c_347,plain,
% 3.88/1.02      ( r1_tarski(X0,X1) != iProver_top
% 3.88/1.02      | r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) = iProver_top
% 3.88/1.02      | v1_relat_1(X0) != iProver_top
% 3.88/1.02      | v1_relat_1(X1) != iProver_top ),
% 3.88/1.02      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.88/1.02  
% 3.88/1.02  cnf(c_6,plain,
% 3.88/1.02      ( ~ r1_tarski(X0,X1)
% 3.88/1.02      | ~ r1_tarski(X0,X2)
% 3.88/1.02      | r1_tarski(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
% 3.88/1.02      inference(cnf_transformation,[],[f43]) ).
% 3.88/1.02  
% 3.88/1.02  cnf(c_350,plain,
% 3.88/1.02      ( r1_tarski(X0,X1) != iProver_top
% 3.88/1.02      | r1_tarski(X0,X2) != iProver_top
% 3.88/1.02      | r1_tarski(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) = iProver_top ),
% 3.88/1.02      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.88/1.02  
% 3.88/1.02  cnf(c_10,negated_conjecture,
% 3.88/1.02      ( ~ r1_tarski(k3_relat_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k3_relat_1(sK1),k4_xboole_0(k3_relat_1(sK1),k3_relat_1(sK2)))) ),
% 3.88/1.02      inference(cnf_transformation,[],[f44]) ).
% 3.88/1.02  
% 3.88/1.02  cnf(c_346,plain,
% 3.88/1.02      ( r1_tarski(k3_relat_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k3_relat_1(sK1),k4_xboole_0(k3_relat_1(sK1),k3_relat_1(sK2)))) != iProver_top ),
% 3.88/1.02      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.88/1.02  
% 3.88/1.02  cnf(c_749,plain,
% 3.88/1.02      ( r1_tarski(k3_relat_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k3_relat_1(sK2)) != iProver_top
% 3.88/1.02      | r1_tarski(k3_relat_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k3_relat_1(sK1)) != iProver_top ),
% 3.88/1.02      inference(superposition,[status(thm)],[c_350,c_346]) ).
% 3.88/1.02  
% 3.88/1.02  cnf(c_1151,plain,
% 3.88/1.02      ( r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK2) != iProver_top
% 3.88/1.02      | r1_tarski(k3_relat_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k3_relat_1(sK1)) != iProver_top
% 3.88/1.02      | v1_relat_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) != iProver_top
% 3.88/1.02      | v1_relat_1(sK2) != iProver_top ),
% 3.88/1.02      inference(superposition,[status(thm)],[c_347,c_749]) ).
% 3.88/1.02  
% 3.88/1.02  cnf(c_651,plain,
% 3.88/1.02      ( ~ r1_tarski(k3_relat_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k3_relat_1(sK2))
% 3.88/1.02      | ~ r1_tarski(k3_relat_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k3_relat_1(sK1)) ),
% 3.88/1.02      inference(resolution,[status(thm)],[c_10,c_6]) ).
% 3.88/1.02  
% 3.88/1.02  cnf(c_772,plain,
% 3.88/1.02      ( ~ r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK2)
% 3.88/1.02      | ~ r1_tarski(k3_relat_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k3_relat_1(sK1))
% 3.88/1.02      | ~ v1_relat_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
% 3.88/1.02      | ~ v1_relat_1(sK2) ),
% 3.88/1.02      inference(resolution,[status(thm)],[c_651,c_9]) ).
% 3.88/1.02  
% 3.88/1.02  cnf(c_11,negated_conjecture,
% 3.88/1.02      ( v1_relat_1(sK2) ),
% 3.88/1.02      inference(cnf_transformation,[],[f35]) ).
% 3.88/1.02  
% 3.88/1.02  cnf(c_1047,plain,
% 3.88/1.02      ( ~ v1_relat_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
% 3.88/1.02      | ~ r1_tarski(k3_relat_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k3_relat_1(sK1))
% 3.88/1.02      | ~ r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK2) ),
% 3.88/1.02      inference(global_propositional_subsumption,
% 3.88/1.02                [status(thm)],
% 3.88/1.02                [c_772,c_11]) ).
% 3.88/1.02  
% 3.88/1.02  cnf(c_1048,plain,
% 3.88/1.02      ( ~ r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK2)
% 3.88/1.02      | ~ r1_tarski(k3_relat_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k3_relat_1(sK1))
% 3.88/1.02      | ~ v1_relat_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
% 3.88/1.02      inference(renaming,[status(thm)],[c_1047]) ).
% 3.88/1.02  
% 3.88/1.02  cnf(c_1161,plain,
% 3.88/1.02      ( ~ r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK2)
% 3.88/1.02      | ~ r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1)
% 3.88/1.02      | ~ v1_relat_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
% 3.88/1.02      | ~ v1_relat_1(sK1) ),
% 3.88/1.02      inference(resolution,[status(thm)],[c_1048,c_9]) ).
% 3.88/1.02  
% 3.88/1.02  cnf(c_12,negated_conjecture,
% 3.88/1.02      ( v1_relat_1(sK1) ),
% 3.88/1.02      inference(cnf_transformation,[],[f34]) ).
% 3.88/1.02  
% 3.88/1.02  cnf(c_1164,plain,
% 3.88/1.02      ( ~ v1_relat_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
% 3.88/1.02      | ~ r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1)
% 3.88/1.02      | ~ r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK2) ),
% 3.88/1.02      inference(global_propositional_subsumption,
% 3.88/1.02                [status(thm)],
% 3.88/1.02                [c_1161,c_12]) ).
% 3.88/1.02  
% 3.88/1.02  cnf(c_1165,plain,
% 3.88/1.02      ( ~ r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK2)
% 3.88/1.02      | ~ r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1)
% 3.88/1.02      | ~ v1_relat_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
% 3.88/1.02      inference(renaming,[status(thm)],[c_1164]) ).
% 3.88/1.02  
% 3.88/1.02  cnf(c_1171,plain,
% 3.88/1.02      ( ~ r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK2)
% 3.88/1.02      | ~ v1_relat_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
% 3.88/1.02      inference(forward_subsumption_resolution,
% 3.88/1.02                [status(thm)],
% 3.88/1.02                [c_1165,c_7]) ).
% 3.88/1.02  
% 3.88/1.02  cnf(c_1172,plain,
% 3.88/1.02      ( r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK2) != iProver_top
% 3.88/1.02      | v1_relat_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) != iProver_top ),
% 3.88/1.02      inference(predicate_to_equality,[status(thm)],[c_1171]) ).
% 3.88/1.02  
% 3.88/1.02  cnf(c_2044,plain,
% 3.88/1.02      ( v1_relat_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) != iProver_top
% 3.88/1.02      | r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK2) != iProver_top ),
% 3.88/1.02      inference(global_propositional_subsumption,
% 3.88/1.02                [status(thm)],
% 3.88/1.02                [c_1151,c_1172]) ).
% 3.88/1.02  
% 3.88/1.02  cnf(c_2045,plain,
% 3.88/1.02      ( r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK2) != iProver_top
% 3.88/1.02      | v1_relat_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) != iProver_top ),
% 3.88/1.02      inference(renaming,[status(thm)],[c_2044]) ).
% 3.88/1.02  
% 3.88/1.02  cnf(c_4504,plain,
% 3.88/1.02      ( v1_relat_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) != iProver_top ),
% 3.88/1.02      inference(superposition,[status(thm)],[c_3965,c_2045]) ).
% 3.88/1.02  
% 3.88/1.02  cnf(c_8,plain,
% 3.88/1.02      ( ~ v1_relat_1(X0) | v1_relat_1(k4_xboole_0(X0,X1)) ),
% 3.88/1.02      inference(cnf_transformation,[],[f32]) ).
% 3.88/1.02  
% 3.88/1.02  cnf(c_818,plain,
% 3.88/1.02      ( ~ v1_relat_1(X0)
% 3.88/1.02      | v1_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 3.88/1.02      inference(instantiation,[status(thm)],[c_8]) ).
% 3.88/1.02  
% 3.88/1.02  cnf(c_2808,plain,
% 3.88/1.02      ( v1_relat_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
% 3.88/1.02      | ~ v1_relat_1(sK1) ),
% 3.88/1.02      inference(instantiation,[status(thm)],[c_818]) ).
% 3.88/1.02  
% 3.88/1.02  cnf(c_2809,plain,
% 3.88/1.02      ( v1_relat_1(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) = iProver_top
% 3.88/1.02      | v1_relat_1(sK1) != iProver_top ),
% 3.88/1.02      inference(predicate_to_equality,[status(thm)],[c_2808]) ).
% 3.88/1.02  
% 3.88/1.02  cnf(c_13,plain,
% 3.88/1.02      ( v1_relat_1(sK1) = iProver_top ),
% 3.88/1.02      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.88/1.02  
% 3.88/1.02  cnf(contradiction,plain,
% 3.88/1.02      ( $false ),
% 3.88/1.02      inference(minisat,[status(thm)],[c_4504,c_2809,c_13]) ).
% 3.88/1.02  
% 3.88/1.02  
% 3.88/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 3.88/1.02  
% 3.88/1.02  ------                               Statistics
% 3.88/1.02  
% 3.88/1.02  ------ Selected
% 3.88/1.02  
% 3.88/1.02  total_time:                             0.223
% 3.88/1.02  
%------------------------------------------------------------------------------
