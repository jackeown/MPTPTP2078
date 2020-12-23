%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0433+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:17 EST 2020

% Result     : Theorem 2.28s
% Output     : CNFRefutation 2.28s
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
fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
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
    inference(nnf_transformation,[],[f4])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f21,plain,(
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
    inference(rectify,[],[f20])).

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(sK4(X0,X1,X2),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f22])).

fof(f35,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f42,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f35])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f11,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f11])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f5,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f8,plain,(
    ~ ! [X0,X1] : r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f10,plain,(
    ? [X0,X1] : ~ r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) ),
    inference(ennf_transformation,[],[f8])).

fof(f24,plain,
    ( ? [X0,X1] : ~ r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))
   => ~ r1_tarski(k1_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k1_relat_1(sK5),k1_relat_1(sK6))) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ~ r1_tarski(k1_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k1_relat_1(sK5),k1_relat_1(sK6))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f10,f24])).

fof(f39,plain,(
    ~ r1_tarski(k1_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k1_relat_1(sK5),k1_relat_1(sK6))) ),
    inference(cnf_transformation,[],[f25])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f13])).

fof(f17,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK2(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK1(X0,X1),X3),X0)
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK1(X0,X1),X4),X0)
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK1(X0,X1),X3),X0)
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f14,f17,f16,f15])).

fof(f30,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f40,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f30])).

fof(f33,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f44,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f33])).

fof(f34,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f43,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f34])).

fof(f29,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f41,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK3(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f29])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f12])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_462,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X0,k3_xboole_0(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_13,negated_conjecture,
    ( ~ r1_tarski(k1_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k1_relat_1(sK5),k1_relat_1(sK6))) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_160,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | k3_xboole_0(k1_relat_1(sK5),k1_relat_1(sK6)) != X1
    | k1_relat_1(k3_xboole_0(sK5,sK6)) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_13])).

cnf(c_161,plain,
    ( ~ r2_hidden(sK0(k1_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k1_relat_1(sK5),k1_relat_1(sK6))),k3_xboole_0(k1_relat_1(sK5),k1_relat_1(sK6))) ),
    inference(unflattening,[status(thm)],[c_160])).

cnf(c_458,plain,
    ( r2_hidden(sK0(k1_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k1_relat_1(sK5),k1_relat_1(sK6))),k3_xboole_0(k1_relat_1(sK5),k1_relat_1(sK6))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_161])).

cnf(c_1007,plain,
    ( r2_hidden(sK0(k1_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k1_relat_1(sK5),k1_relat_1(sK6))),k1_relat_1(sK6)) != iProver_top
    | r2_hidden(sK0(k1_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k1_relat_1(sK5),k1_relat_1(sK6))),k1_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_462,c_458])).

cnf(c_5,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_661,plain,
    ( ~ r2_hidden(k4_tarski(sK0(k1_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k1_relat_1(sK5),k1_relat_1(sK6))),sK3(k3_xboole_0(sK5,sK6),sK0(k1_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k1_relat_1(sK5),k1_relat_1(sK6))))),sK5)
    | r2_hidden(sK0(k1_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k1_relat_1(sK5),k1_relat_1(sK6))),k1_relat_1(sK5)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_662,plain,
    ( r2_hidden(k4_tarski(sK0(k1_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k1_relat_1(sK5),k1_relat_1(sK6))),sK3(k3_xboole_0(sK5,sK6),sK0(k1_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k1_relat_1(sK5),k1_relat_1(sK6))))),sK5) != iProver_top
    | r2_hidden(sK0(k1_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k1_relat_1(sK5),k1_relat_1(sK6))),k1_relat_1(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_661])).

cnf(c_648,plain,
    ( ~ r2_hidden(k4_tarski(sK0(k1_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k1_relat_1(sK5),k1_relat_1(sK6))),sK3(k3_xboole_0(sK5,sK6),sK0(k1_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k1_relat_1(sK5),k1_relat_1(sK6))))),sK6)
    | r2_hidden(sK0(k1_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k1_relat_1(sK5),k1_relat_1(sK6))),k1_relat_1(sK6)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_649,plain,
    ( r2_hidden(k4_tarski(sK0(k1_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k1_relat_1(sK5),k1_relat_1(sK6))),sK3(k3_xboole_0(sK5,sK6),sK0(k1_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k1_relat_1(sK5),k1_relat_1(sK6))))),sK6) != iProver_top
    | r2_hidden(sK0(k1_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k1_relat_1(sK5),k1_relat_1(sK6))),k1_relat_1(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_648])).

cnf(c_12,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_592,plain,
    ( ~ r2_hidden(k4_tarski(sK0(k1_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k1_relat_1(sK5),k1_relat_1(sK6))),sK3(k3_xboole_0(sK5,sK6),sK0(k1_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k1_relat_1(sK5),k1_relat_1(sK6))))),k3_xboole_0(sK5,sK6))
    | r2_hidden(k4_tarski(sK0(k1_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k1_relat_1(sK5),k1_relat_1(sK6))),sK3(k3_xboole_0(sK5,sK6),sK0(k1_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k1_relat_1(sK5),k1_relat_1(sK6))))),sK5) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_593,plain,
    ( r2_hidden(k4_tarski(sK0(k1_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k1_relat_1(sK5),k1_relat_1(sK6))),sK3(k3_xboole_0(sK5,sK6),sK0(k1_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k1_relat_1(sK5),k1_relat_1(sK6))))),k3_xboole_0(sK5,sK6)) != iProver_top
    | r2_hidden(k4_tarski(sK0(k1_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k1_relat_1(sK5),k1_relat_1(sK6))),sK3(k3_xboole_0(sK5,sK6),sK0(k1_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k1_relat_1(sK5),k1_relat_1(sK6))))),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_592])).

cnf(c_11,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_589,plain,
    ( ~ r2_hidden(k4_tarski(sK0(k1_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k1_relat_1(sK5),k1_relat_1(sK6))),sK3(k3_xboole_0(sK5,sK6),sK0(k1_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k1_relat_1(sK5),k1_relat_1(sK6))))),k3_xboole_0(sK5,sK6))
    | r2_hidden(k4_tarski(sK0(k1_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k1_relat_1(sK5),k1_relat_1(sK6))),sK3(k3_xboole_0(sK5,sK6),sK0(k1_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k1_relat_1(sK5),k1_relat_1(sK6))))),sK6) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_590,plain,
    ( r2_hidden(k4_tarski(sK0(k1_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k1_relat_1(sK5),k1_relat_1(sK6))),sK3(k3_xboole_0(sK5,sK6),sK0(k1_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k1_relat_1(sK5),k1_relat_1(sK6))))),k3_xboole_0(sK5,sK6)) != iProver_top
    | r2_hidden(k4_tarski(sK0(k1_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k1_relat_1(sK5),k1_relat_1(sK6))),sK3(k3_xboole_0(sK5,sK6),sK0(k1_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k1_relat_1(sK5),k1_relat_1(sK6))))),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_589])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,sK3(X1,X0)),X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_555,plain,
    ( r2_hidden(k4_tarski(sK0(k1_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k1_relat_1(sK5),k1_relat_1(sK6))),sK3(k3_xboole_0(sK5,sK6),sK0(k1_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k1_relat_1(sK5),k1_relat_1(sK6))))),k3_xboole_0(sK5,sK6))
    | ~ r2_hidden(sK0(k1_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k1_relat_1(sK5),k1_relat_1(sK6))),k1_relat_1(k3_xboole_0(sK5,sK6))) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_556,plain,
    ( r2_hidden(k4_tarski(sK0(k1_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k1_relat_1(sK5),k1_relat_1(sK6))),sK3(k3_xboole_0(sK5,sK6),sK0(k1_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k1_relat_1(sK5),k1_relat_1(sK6))))),k3_xboole_0(sK5,sK6)) = iProver_top
    | r2_hidden(sK0(k1_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k1_relat_1(sK5),k1_relat_1(sK6))),k1_relat_1(k3_xboole_0(sK5,sK6))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_555])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_153,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | k3_xboole_0(k1_relat_1(sK5),k1_relat_1(sK6)) != X1
    | k1_relat_1(k3_xboole_0(sK5,sK6)) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_13])).

cnf(c_154,plain,
    ( r2_hidden(sK0(k1_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k1_relat_1(sK5),k1_relat_1(sK6))),k1_relat_1(k3_xboole_0(sK5,sK6))) ),
    inference(unflattening,[status(thm)],[c_153])).

cnf(c_155,plain,
    ( r2_hidden(sK0(k1_relat_1(k3_xboole_0(sK5,sK6)),k3_xboole_0(k1_relat_1(sK5),k1_relat_1(sK6))),k1_relat_1(k3_xboole_0(sK5,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_154])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1007,c_662,c_649,c_593,c_590,c_556,c_155])).


%------------------------------------------------------------------------------
