%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0444+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:19 EST 2020

% Result     : Theorem 2.13s
% Output     : CNFRefutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 106 expanded)
%              Number of clauses        :   27 (  29 expanded)
%              Number of leaves         :   10 (  26 expanded)
%              Depth                    :   11
%              Number of atoms          :  228 ( 498 expanded)
%              Number of equality atoms :   42 (  75 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f14,plain,(
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
    inference(rectify,[],[f13])).

fof(f15,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
          | ~ r2_hidden(sK1(X0,X1,X2),X0)
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(sK1(X0,X1,X2),X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
            | ~ r2_hidden(sK1(X0,X1,X2),X0)
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK1(X0,X1,X2),X1)
              & r2_hidden(sK1(X0,X1,X2),X0) )
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f14,f15])).

fof(f29,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f38,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f29])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f8,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f10,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f10])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f4,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f7,plain,(
    ~ ! [X0,X1] : r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f9,plain,(
    ? [X0,X1] : ~ r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) ),
    inference(ennf_transformation,[],[f7])).

fof(f23,plain,
    ( ? [X0,X1] : ~ r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))
   => ~ r1_tarski(k2_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k2_relat_1(sK5),k2_relat_1(sK6))) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k2_relat_1(sK5),k2_relat_1(sK6))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f9,f23])).

fof(f37,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k2_relat_1(sK5),k2_relat_1(sK6))) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f17])).

fof(f21,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK4(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
     => r2_hidden(k4_tarski(sK3(X0,X1),X2),X0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK2(X0,X1)),X0)
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK2(X0,X1)),X0)
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK2(X0,X1)),X0)
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0)
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK4(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f18,f21,f20,f19])).

fof(f34,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f41,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k2_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X6,X5),X0) ) ),
    inference(equality_resolution,[],[f34])).

fof(f27,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f40,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f27])).

fof(f28,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f39,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f28])).

fof(f33,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK4(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f42,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK4(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f33])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f11])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_465,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X0,k3_xboole_0(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_12,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k2_relat_1(sK5),k2_relat_1(sK6))) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_158,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | k3_xboole_0(k2_relat_1(sK5),k2_relat_1(sK6)) != X1
    | k2_relat_1(k3_xboole_0(sK5,sK6)) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_12])).

cnf(c_159,plain,
    ( ~ r2_hidden(sK0(k2_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k2_relat_1(sK5),k2_relat_1(sK6))),k3_xboole_0(k2_relat_1(sK5),k2_relat_1(sK6))) ),
    inference(unflattening,[status(thm)],[c_158])).

cnf(c_457,plain,
    ( r2_hidden(sK0(k2_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k2_relat_1(sK5),k2_relat_1(sK6))),k3_xboole_0(k2_relat_1(sK5),k2_relat_1(sK6))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_159])).

cnf(c_989,plain,
    ( r2_hidden(sK0(k2_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k2_relat_1(sK5),k2_relat_1(sK6))),k2_relat_1(sK6)) != iProver_top
    | r2_hidden(sK0(k2_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k2_relat_1(sK5),k2_relat_1(sK6))),k2_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_465,c_457])).

cnf(c_10,plain,
    ( r2_hidden(X0,k2_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_664,plain,
    ( ~ r2_hidden(k4_tarski(sK4(k3_xboole_0(sK5,sK6),sK0(k2_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k2_relat_1(sK5),k2_relat_1(sK6)))),sK0(k2_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k2_relat_1(sK5),k2_relat_1(sK6)))),sK5)
    | r2_hidden(sK0(k2_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k2_relat_1(sK5),k2_relat_1(sK6))),k2_relat_1(sK5)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_665,plain,
    ( r2_hidden(k4_tarski(sK4(k3_xboole_0(sK5,sK6),sK0(k2_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k2_relat_1(sK5),k2_relat_1(sK6)))),sK0(k2_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k2_relat_1(sK5),k2_relat_1(sK6)))),sK5) != iProver_top
    | r2_hidden(sK0(k2_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k2_relat_1(sK5),k2_relat_1(sK6))),k2_relat_1(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_664])).

cnf(c_651,plain,
    ( ~ r2_hidden(k4_tarski(sK4(k3_xboole_0(sK5,sK6),sK0(k2_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k2_relat_1(sK5),k2_relat_1(sK6)))),sK0(k2_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k2_relat_1(sK5),k2_relat_1(sK6)))),sK6)
    | r2_hidden(sK0(k2_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k2_relat_1(sK5),k2_relat_1(sK6))),k2_relat_1(sK6)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_652,plain,
    ( r2_hidden(k4_tarski(sK4(k3_xboole_0(sK5,sK6),sK0(k2_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k2_relat_1(sK5),k2_relat_1(sK6)))),sK0(k2_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k2_relat_1(sK5),k2_relat_1(sK6)))),sK6) != iProver_top
    | r2_hidden(sK0(k2_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k2_relat_1(sK5),k2_relat_1(sK6))),k2_relat_1(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_651])).

cnf(c_7,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_588,plain,
    ( ~ r2_hidden(k4_tarski(sK4(k3_xboole_0(sK5,sK6),sK0(k2_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k2_relat_1(sK5),k2_relat_1(sK6)))),sK0(k2_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k2_relat_1(sK5),k2_relat_1(sK6)))),k3_xboole_0(sK5,sK6))
    | r2_hidden(k4_tarski(sK4(k3_xboole_0(sK5,sK6),sK0(k2_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k2_relat_1(sK5),k2_relat_1(sK6)))),sK0(k2_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k2_relat_1(sK5),k2_relat_1(sK6)))),sK5) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_589,plain,
    ( r2_hidden(k4_tarski(sK4(k3_xboole_0(sK5,sK6),sK0(k2_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k2_relat_1(sK5),k2_relat_1(sK6)))),sK0(k2_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k2_relat_1(sK5),k2_relat_1(sK6)))),k3_xboole_0(sK5,sK6)) != iProver_top
    | r2_hidden(k4_tarski(sK4(k3_xboole_0(sK5,sK6),sK0(k2_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k2_relat_1(sK5),k2_relat_1(sK6)))),sK0(k2_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k2_relat_1(sK5),k2_relat_1(sK6)))),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_588])).

cnf(c_6,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_585,plain,
    ( ~ r2_hidden(k4_tarski(sK4(k3_xboole_0(sK5,sK6),sK0(k2_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k2_relat_1(sK5),k2_relat_1(sK6)))),sK0(k2_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k2_relat_1(sK5),k2_relat_1(sK6)))),k3_xboole_0(sK5,sK6))
    | r2_hidden(k4_tarski(sK4(k3_xboole_0(sK5,sK6),sK0(k2_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k2_relat_1(sK5),k2_relat_1(sK6)))),sK0(k2_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k2_relat_1(sK5),k2_relat_1(sK6)))),sK6) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_586,plain,
    ( r2_hidden(k4_tarski(sK4(k3_xboole_0(sK5,sK6),sK0(k2_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k2_relat_1(sK5),k2_relat_1(sK6)))),sK0(k2_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k2_relat_1(sK5),k2_relat_1(sK6)))),k3_xboole_0(sK5,sK6)) != iProver_top
    | r2_hidden(k4_tarski(sK4(k3_xboole_0(sK5,sK6),sK0(k2_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k2_relat_1(sK5),k2_relat_1(sK6)))),sK0(k2_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k2_relat_1(sK5),k2_relat_1(sK6)))),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_585])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(k4_tarski(sK4(X1,X0),X0),X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_552,plain,
    ( r2_hidden(k4_tarski(sK4(k3_xboole_0(sK5,sK6),sK0(k2_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k2_relat_1(sK5),k2_relat_1(sK6)))),sK0(k2_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k2_relat_1(sK5),k2_relat_1(sK6)))),k3_xboole_0(sK5,sK6))
    | ~ r2_hidden(sK0(k2_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k2_relat_1(sK5),k2_relat_1(sK6))),k2_relat_1(k3_xboole_0(sK5,sK6))) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_553,plain,
    ( r2_hidden(k4_tarski(sK4(k3_xboole_0(sK5,sK6),sK0(k2_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k2_relat_1(sK5),k2_relat_1(sK6)))),sK0(k2_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k2_relat_1(sK5),k2_relat_1(sK6)))),k3_xboole_0(sK5,sK6)) = iProver_top
    | r2_hidden(sK0(k2_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k2_relat_1(sK5),k2_relat_1(sK6))),k2_relat_1(k3_xboole_0(sK5,sK6))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_552])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_151,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | k3_xboole_0(k2_relat_1(sK5),k2_relat_1(sK6)) != X1
    | k2_relat_1(k3_xboole_0(sK5,sK6)) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_12])).

cnf(c_152,plain,
    ( r2_hidden(sK0(k2_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k2_relat_1(sK5),k2_relat_1(sK6))),k2_relat_1(k3_xboole_0(sK5,sK6))) ),
    inference(unflattening,[status(thm)],[c_151])).

cnf(c_153,plain,
    ( r2_hidden(sK0(k2_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k2_relat_1(sK5),k2_relat_1(sK6))),k2_relat_1(k3_xboole_0(sK5,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_152])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_989,c_665,c_652,c_589,c_586,c_553,c_153])).


%------------------------------------------------------------------------------
