%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0735+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:01 EST 2020

% Result     : Theorem 3.58s
% Output     : CNFRefutation 3.58s
% Verified   : 
% Statistics : Number of formulae       :  158 (1550 expanded)
%              Number of clauses        :  105 ( 436 expanded)
%              Number of leaves         :   15 ( 336 expanded)
%              Depth                    :   25
%              Number of atoms          :  515 (7341 expanded)
%              Number of equality atoms :   77 ( 903 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   12 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f29,f30])).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f5,axiom,(
    ! [X0] :
      ( v2_ordinal1(X0)
    <=> ! [X1,X2] :
          ~ ( ~ r2_hidden(X2,X1)
            & X1 != X2
            & ~ r2_hidden(X1,X2)
            & r2_hidden(X2,X0)
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( v2_ordinal1(X0)
    <=> ! [X1,X2] :
          ( r2_hidden(X2,X1)
          | X1 = X2
          | r2_hidden(X1,X2)
          | ~ r2_hidden(X2,X0)
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f24,plain,(
    ! [X0] :
      ( ( v2_ordinal1(X0)
        | ? [X1,X2] :
            ( ~ r2_hidden(X2,X1)
            & X1 != X2
            & ~ r2_hidden(X1,X2)
            & r2_hidden(X2,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X1,X2] :
            ( r2_hidden(X2,X1)
            | X1 = X2
            | r2_hidden(X1,X2)
            | ~ r2_hidden(X2,X0)
            | ~ r2_hidden(X1,X0) )
        | ~ v2_ordinal1(X0) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f25,plain,(
    ! [X0] :
      ( ( v2_ordinal1(X0)
        | ? [X1,X2] :
            ( ~ r2_hidden(X2,X1)
            & X1 != X2
            & ~ r2_hidden(X1,X2)
            & r2_hidden(X2,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X3,X4] :
            ( r2_hidden(X4,X3)
            | X3 = X4
            | r2_hidden(X3,X4)
            | ~ r2_hidden(X4,X0)
            | ~ r2_hidden(X3,X0) )
        | ~ v2_ordinal1(X0) ) ) ),
    inference(rectify,[],[f24])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( ~ r2_hidden(X2,X1)
          & X1 != X2
          & ~ r2_hidden(X1,X2)
          & r2_hidden(X2,X0)
          & r2_hidden(X1,X0) )
     => ( ~ r2_hidden(sK2(X0),sK1(X0))
        & sK1(X0) != sK2(X0)
        & ~ r2_hidden(sK1(X0),sK2(X0))
        & r2_hidden(sK2(X0),X0)
        & r2_hidden(sK1(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ( v2_ordinal1(X0)
        | ( ~ r2_hidden(sK2(X0),sK1(X0))
          & sK1(X0) != sK2(X0)
          & ~ r2_hidden(sK1(X0),sK2(X0))
          & r2_hidden(sK2(X0),X0)
          & r2_hidden(sK1(X0),X0) ) )
      & ( ! [X3,X4] :
            ( r2_hidden(X4,X3)
            | X3 = X4
            | r2_hidden(X3,X4)
            | ~ r2_hidden(X4,X0)
            | ~ r2_hidden(X3,X0) )
        | ~ v2_ordinal1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f25,f26])).

fof(f43,plain,(
    ! [X0] :
      ( v2_ordinal1(X0)
      | r2_hidden(sK2(X0),X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f41,plain,(
    ! [X4,X0,X3] :
      ( r2_hidden(X4,X3)
      | X3 = X4
      | r2_hidden(X3,X4)
      | ~ r2_hidden(X4,X0)
      | ~ r2_hidden(X3,X0)
      | ~ v2_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( v3_ordinal1(X1)
     => ( r2_hidden(X0,X1)
       => v3_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v3_ordinal1(X1)
       => ( r2_hidden(X0,X1)
         => v3_ordinal1(X0) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ~ v3_ordinal1(X0)
      & r2_hidden(X0,X1)
      & v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ~ v3_ordinal1(X0)
      & r2_hidden(X0,X1)
      & v3_ordinal1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f32,plain,
    ( ? [X0,X1] :
        ( ~ v3_ordinal1(X0)
        & r2_hidden(X0,X1)
        & v3_ordinal1(X1) )
   => ( ~ v3_ordinal1(sK4)
      & r2_hidden(sK4,sK5)
      & v3_ordinal1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ~ v3_ordinal1(sK4)
    & r2_hidden(sK4,sK5)
    & v3_ordinal1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f19,f32])).

fof(f52,plain,(
    r2_hidden(sK4,sK5) ),
    inference(cnf_transformation,[],[f33])).

fof(f2,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v2_ordinal1(X0)
        & v1_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ( v2_ordinal1(X0)
        & v1_ordinal1(X0) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f36,plain,(
    ! [X0] :
      ( v2_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f51,plain,(
    v3_ordinal1(sK5) ),
    inference(cnf_transformation,[],[f33])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r1_tarski(X1,X0)
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f20,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ? [X1] :
            ( ~ r1_tarski(X1,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X1] :
            ( r1_tarski(X1,X0)
            | ~ r2_hidden(X1,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f21,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ? [X1] :
            ( ~ r1_tarski(X1,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X2] :
            ( r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(rectify,[],[f20])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X1,X0)
          & r2_hidden(X1,X0) )
     => ( ~ r1_tarski(sK0(X0),X0)
        & r2_hidden(sK0(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ( ~ r1_tarski(sK0(X0),X0)
          & r2_hidden(sK0(X0),X0) ) )
      & ( ! [X2] :
            ( r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f22])).

fof(f38,plain,(
    ! [X2,X0] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f35,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f42,plain,(
    ! [X0] :
      ( v2_ordinal1(X0)
      | r2_hidden(sK1(X0),X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f44,plain,(
    ! [X0] :
      ( v2_ordinal1(X0)
      | ~ r2_hidden(sK1(X0),sK2(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f45,plain,(
    ! [X0] :
      ( v2_ordinal1(X0)
      | sK1(X0) != sK2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f46,plain,(
    ! [X0] :
      ( v2_ordinal1(X0)
      | ~ r2_hidden(sK2(X0),sK1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v2_ordinal1(X0)
        & v1_ordinal1(X0) )
     => v3_ordinal1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( v3_ordinal1(X0)
      | ~ v2_ordinal1(X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f13,plain,(
    ! [X0] :
      ( v3_ordinal1(X0)
      | ~ v2_ordinal1(X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f37,plain,(
    ! [X0] :
      ( v3_ordinal1(X0)
      | ~ v2_ordinal1(X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f53,plain,(
    ~ v3_ordinal1(sK4) ),
    inference(cnf_transformation,[],[f33])).

fof(f39,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f40,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ r1_tarski(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ~ ( r2_hidden(X2,X0)
        & r2_hidden(X1,X2)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_15,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_10,plain,
    ( r2_hidden(sK2(X0),X0)
    | v2_ordinal1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_2246,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_hidden(sK2(X0),X1)
    | v2_ordinal1(X0) ),
    inference(resolution,[status(thm)],[c_15,c_10])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_1651,plain,
    ( ~ r2_hidden(X0,sK2(X0))
    | v2_ordinal1(X0) ),
    inference(resolution,[status(thm)],[c_0,c_10])).

cnf(c_2486,plain,
    ( ~ r1_tarski(X0,sK2(sK2(X0)))
    | v2_ordinal1(X0)
    | v2_ordinal1(sK2(X0)) ),
    inference(resolution,[status(thm)],[c_2246,c_1651])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X1)
    | r2_hidden(X2,X0)
    | r2_hidden(X0,X2)
    | ~ v2_ordinal1(X1)
    | X2 = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_18,negated_conjecture,
    ( r2_hidden(sK4,sK5) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_3819,plain,
    ( ~ r2_hidden(X0,sK5)
    | r2_hidden(X0,sK4)
    | r2_hidden(sK4,X0)
    | ~ v2_ordinal1(sK5)
    | sK4 = X0 ),
    inference(resolution,[status(thm)],[c_12,c_18])).

cnf(c_1,plain,
    ( ~ v3_ordinal1(X0)
    | v2_ordinal1(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_19,negated_conjecture,
    ( v3_ordinal1(sK5) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_239,plain,
    ( v2_ordinal1(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_19])).

cnf(c_240,plain,
    ( v2_ordinal1(sK5) ),
    inference(unflattening,[status(thm)],[c_239])).

cnf(c_1494,plain,
    ( r2_hidden(sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1499,plain,
    ( X0 = X1
    | r2_hidden(X1,X2) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X1,X0) = iProver_top
    | v2_ordinal1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2618,plain,
    ( sK4 = X0
    | r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(X0,sK4) = iProver_top
    | r2_hidden(sK4,X0) = iProver_top
    | v2_ordinal1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1494,c_1499])).

cnf(c_2621,plain,
    ( ~ r2_hidden(X0,sK5)
    | r2_hidden(X0,sK4)
    | r2_hidden(sK4,X0)
    | ~ v2_ordinal1(sK5)
    | sK4 = X0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2618])).

cnf(c_4010,plain,
    ( r2_hidden(sK4,X0)
    | r2_hidden(X0,sK4)
    | ~ r2_hidden(X0,sK5)
    | sK4 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3819,c_240,c_2621])).

cnf(c_4011,plain,
    ( ~ r2_hidden(X0,sK5)
    | r2_hidden(X0,sK4)
    | r2_hidden(sK4,X0)
    | sK4 = X0 ),
    inference(renaming,[status(thm)],[c_4010])).

cnf(c_1136,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_4034,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK4,X1)
    | ~ r2_hidden(X0,sK5)
    | r2_hidden(X0,sK4)
    | r2_hidden(sK4,X0) ),
    inference(resolution,[status(thm)],[c_4011,c_1136])).

cnf(c_13,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(sK3(X0,X1),X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_14,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK3(X0,X1),X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_2171,plain,
    ( r1_tarski(X0,X0) ),
    inference(resolution,[status(thm)],[c_13,c_14])).

cnf(c_4243,plain,
    ( r1_tarski(sK4,X0)
    | ~ r2_hidden(X0,sK5)
    | r2_hidden(X0,sK4)
    | r2_hidden(sK4,X0) ),
    inference(resolution,[status(thm)],[c_4034,c_2171])).

cnf(c_6331,plain,
    ( ~ r2_hidden(sK2(sK2(sK4)),sK5)
    | r2_hidden(sK2(sK2(sK4)),sK4)
    | r2_hidden(sK4,sK2(sK2(sK4)))
    | v2_ordinal1(sK2(sK4))
    | v2_ordinal1(sK4) ),
    inference(resolution,[status(thm)],[c_2486,c_4243])).

cnf(c_6,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(X0,X1)
    | ~ v1_ordinal1(X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_2,plain,
    ( v1_ordinal1(X0)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_232,plain,
    ( v1_ordinal1(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_19])).

cnf(c_233,plain,
    ( v1_ordinal1(sK5) ),
    inference(unflattening,[status(thm)],[c_232])).

cnf(c_284,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(X0,X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_233])).

cnf(c_285,plain,
    ( r1_tarski(X0,sK5)
    | ~ r2_hidden(X0,sK5) ),
    inference(unflattening,[status(thm)],[c_284])).

cnf(c_287,plain,
    ( r1_tarski(sK4,sK5)
    | ~ r2_hidden(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_285])).

cnf(c_1133,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1131,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3797,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_1133,c_1131])).

cnf(c_4035,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,sK5)
    | r2_hidden(X0,sK4)
    | r2_hidden(sK4,X0)
    | r2_hidden(sK4,X1) ),
    inference(resolution,[status(thm)],[c_4011,c_3797])).

cnf(c_4412,plain,
    ( ~ r1_tarski(X0,sK5)
    | ~ r2_hidden(sK2(X0),X1)
    | r2_hidden(sK2(X0),sK4)
    | r2_hidden(sK4,X1)
    | r2_hidden(sK4,sK2(X0))
    | v2_ordinal1(X0) ),
    inference(resolution,[status(thm)],[c_4035,c_2246])).

cnf(c_11,plain,
    ( r2_hidden(sK1(X0),X0)
    | v2_ordinal1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_9,plain,
    ( ~ r2_hidden(sK1(X0),sK2(X0))
    | v2_ordinal1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_8,plain,
    ( v2_ordinal1(X0)
    | sK1(X0) != sK2(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_7,plain,
    ( ~ r2_hidden(sK2(X0),sK1(X0))
    | v2_ordinal1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1700,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_1131])).

cnf(c_1624,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X1,X0)
    | ~ r2_hidden(X0,sK5)
    | ~ r2_hidden(X1,sK5)
    | ~ v2_ordinal1(sK5)
    | X1 = X0 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1708,plain,
    ( r2_hidden(sK1(X0),sK2(X0))
    | ~ r2_hidden(sK1(X0),sK5)
    | r2_hidden(sK2(X0),sK1(X0))
    | ~ r2_hidden(sK2(X0),sK5)
    | ~ v2_ordinal1(sK5)
    | sK1(X0) = sK2(X0) ),
    inference(instantiation,[status(thm)],[c_1624])).

cnf(c_1592,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(sK1(X0),X0)
    | r2_hidden(sK1(X0),X1) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1928,plain,
    ( ~ r1_tarski(X0,sK5)
    | ~ r2_hidden(sK1(X0),X0)
    | r2_hidden(sK1(X0),sK5) ),
    inference(instantiation,[status(thm)],[c_1592])).

cnf(c_1619,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK4,sK5)
    | X1 != sK5
    | X0 != sK4 ),
    inference(instantiation,[status(thm)],[c_1133])).

cnf(c_1699,plain,
    ( r2_hidden(X0,sK5)
    | ~ r2_hidden(sK4,sK5)
    | X0 != sK4
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_1619])).

cnf(c_2278,plain,
    ( r2_hidden(sK2(X0),sK5)
    | ~ r2_hidden(sK4,sK5)
    | sK2(X0) != sK4
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_1699])).

cnf(c_1501,plain,
    ( r2_hidden(sK2(X0),X0) = iProver_top
    | v2_ordinal1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1496,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2450,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(sK2(X0),X1) = iProver_top
    | v2_ordinal1(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1501,c_1496])).

cnf(c_241,plain,
    ( v2_ordinal1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_240])).

cnf(c_6203,plain,
    ( r2_hidden(sK4,X0) = iProver_top
    | r2_hidden(X0,sK4) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top
    | sK4 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2618,c_241])).

cnf(c_6204,plain,
    ( sK4 = X0
    | r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(X0,sK4) = iProver_top
    | r2_hidden(sK4,X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_6203])).

cnf(c_6212,plain,
    ( sK2(X0) = sK4
    | r1_tarski(X0,sK5) != iProver_top
    | r2_hidden(sK2(X0),sK4) = iProver_top
    | r2_hidden(sK4,sK2(X0)) = iProver_top
    | v2_ordinal1(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2450,c_6204])).

cnf(c_6221,plain,
    ( ~ r1_tarski(X0,sK5)
    | r2_hidden(sK2(X0),sK4)
    | r2_hidden(sK4,sK2(X0))
    | v2_ordinal1(X0)
    | sK2(X0) = sK4 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6212])).

cnf(c_6594,plain,
    ( r2_hidden(sK2(X0),sK4)
    | ~ r1_tarski(X0,sK5)
    | r2_hidden(sK4,sK2(X0))
    | v2_ordinal1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4412,c_18,c_11,c_9,c_8,c_7,c_240,c_1700,c_1708,c_1928,c_2278,c_6221])).

cnf(c_6595,plain,
    ( ~ r1_tarski(X0,sK5)
    | r2_hidden(sK2(X0),sK4)
    | r2_hidden(sK4,sK2(X0))
    | v2_ordinal1(X0) ),
    inference(renaming,[status(thm)],[c_6594])).

cnf(c_6621,plain,
    ( ~ r1_tarski(X0,sK5)
    | ~ r1_tarski(sK4,X1)
    | r2_hidden(sK2(X0),X1)
    | r2_hidden(sK4,sK2(X0))
    | v2_ordinal1(X0) ),
    inference(resolution,[status(thm)],[c_6595,c_15])).

cnf(c_1589,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(sK2(X0),X0)
    | r2_hidden(sK2(X0),X1) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_8844,plain,
    ( ~ r1_tarski(X0,sK5)
    | ~ r2_hidden(sK2(X0),X0)
    | r2_hidden(sK2(X0),sK5) ),
    inference(instantiation,[status(thm)],[c_1589])).

cnf(c_9016,plain,
    ( ~ r1_tarski(X0,sK5)
    | v2_ordinal1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6621,c_11,c_10,c_9,c_8,c_7,c_240,c_1708,c_1928,c_8844])).

cnf(c_9019,plain,
    ( ~ r1_tarski(sK4,sK5)
    | v2_ordinal1(sK4) ),
    inference(instantiation,[status(thm)],[c_9016])).

cnf(c_10199,plain,
    ( v2_ordinal1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6331,c_18,c_287,c_9019])).

cnf(c_3,plain,
    ( ~ v1_ordinal1(X0)
    | v3_ordinal1(X0)
    | ~ v2_ordinal1(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_17,negated_conjecture,
    ( ~ v3_ordinal1(sK4) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_222,plain,
    ( ~ v1_ordinal1(X0)
    | ~ v2_ordinal1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_17])).

cnf(c_223,plain,
    ( ~ v1_ordinal1(sK4)
    | ~ v2_ordinal1(sK4) ),
    inference(unflattening,[status(thm)],[c_222])).

cnf(c_10213,plain,
    ( ~ v1_ordinal1(sK4) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_10199,c_223])).

cnf(c_5,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_ordinal1(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_2244,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_hidden(sK0(X0),X1)
    | v1_ordinal1(X0) ),
    inference(resolution,[status(thm)],[c_15,c_5])).

cnf(c_1994,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(X0,sK3(X0,X1)) ),
    inference(resolution,[status(thm)],[c_14,c_0])).

cnf(c_2379,plain,
    ( ~ r1_tarski(X0,sK3(sK0(X0),X1))
    | r1_tarski(sK0(X0),X1)
    | v1_ordinal1(X0) ),
    inference(resolution,[status(thm)],[c_2244,c_1994])).

cnf(c_7468,plain,
    ( r1_tarski(sK0(sK4),X0)
    | ~ r2_hidden(sK3(sK0(sK4),X0),sK5)
    | r2_hidden(sK3(sK0(sK4),X0),sK4)
    | r2_hidden(sK4,sK3(sK0(sK4),X0))
    | v1_ordinal1(sK4) ),
    inference(resolution,[status(thm)],[c_2379,c_4243])).

cnf(c_10295,plain,
    ( r1_tarski(sK0(sK4),X0)
    | ~ r2_hidden(sK3(sK0(sK4),X0),sK5)
    | r2_hidden(sK3(sK0(sK4),X0),sK4)
    | r2_hidden(sK4,sK3(sK0(sK4),X0)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_10213,c_7468])).

cnf(c_2250,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,X2)
    | r2_hidden(sK3(X0,X2),X1) ),
    inference(resolution,[status(thm)],[c_15,c_14])).

cnf(c_11200,plain,
    ( r1_tarski(sK0(sK4),X0)
    | ~ r1_tarski(sK0(sK4),sK5)
    | r2_hidden(sK3(sK0(sK4),X0),sK4)
    | r2_hidden(sK4,sK3(sK0(sK4),X0)) ),
    inference(resolution,[status(thm)],[c_10295,c_2250])).

cnf(c_57,plain,
    ( ~ v1_ordinal1(sK4)
    | v3_ordinal1(sK4)
    | ~ v2_ordinal1(sK4) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_4,plain,
    ( ~ r1_tarski(sK0(X0),X0)
    | v1_ordinal1(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_306,plain,
    ( ~ r1_tarski(sK0(X0),X0)
    | ~ v2_ordinal1(sK4)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_223])).

cnf(c_307,plain,
    ( ~ r1_tarski(sK0(sK4),sK4)
    | ~ v2_ordinal1(sK4) ),
    inference(unflattening,[status(thm)],[c_306])).

cnf(c_368,plain,
    ( r2_hidden(sK3(X0,X1),X0)
    | v1_ordinal1(X2)
    | X1 != X2
    | sK0(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_14])).

cnf(c_369,plain,
    ( r2_hidden(sK3(sK0(X0),X0),sK0(X0))
    | v1_ordinal1(X0) ),
    inference(unflattening,[status(thm)],[c_368])).

cnf(c_371,plain,
    ( r2_hidden(sK3(sK0(sK4),sK4),sK0(sK4))
    | v1_ordinal1(sK4) ),
    inference(instantiation,[status(thm)],[c_369])).

cnf(c_380,plain,
    ( ~ r2_hidden(sK3(X0,X1),X1)
    | v1_ordinal1(X2)
    | X1 != X2
    | sK0(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_13])).

cnf(c_381,plain,
    ( ~ r2_hidden(sK3(sK0(X0),X0),X0)
    | v1_ordinal1(X0) ),
    inference(unflattening,[status(thm)],[c_380])).

cnf(c_383,plain,
    ( ~ r2_hidden(sK3(sK0(sK4),sK4),sK4)
    | v1_ordinal1(sK4) ),
    inference(instantiation,[status(thm)],[c_381])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ r2_hidden(X1,X2) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_2664,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X1,sK0(X0))
    | v1_ordinal1(X0) ),
    inference(resolution,[status(thm)],[c_16,c_5])).

cnf(c_2791,plain,
    ( r1_tarski(sK0(X0),X1)
    | ~ r2_hidden(X0,sK3(sK0(X0),X1))
    | v1_ordinal1(X0) ),
    inference(resolution,[status(thm)],[c_2664,c_14])).

cnf(c_2793,plain,
    ( r1_tarski(sK0(sK4),sK4)
    | ~ r2_hidden(sK4,sK3(sK0(sK4),sK4))
    | v1_ordinal1(sK4) ),
    inference(instantiation,[status(thm)],[c_2791])).

cnf(c_7470,plain,
    ( r1_tarski(sK0(sK4),sK4)
    | ~ r2_hidden(sK3(sK0(sK4),sK4),sK5)
    | r2_hidden(sK3(sK0(sK4),sK4),sK4)
    | r2_hidden(sK4,sK3(sK0(sK4),sK4))
    | v1_ordinal1(sK4) ),
    inference(instantiation,[status(thm)],[c_7468])).

cnf(c_3585,plain,
    ( ~ r1_tarski(sK0(X0),X1)
    | r2_hidden(sK3(sK0(X0),X0),X1)
    | ~ r2_hidden(sK3(sK0(X0),X0),sK0(X0)) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_10803,plain,
    ( ~ r1_tarski(sK0(X0),sK5)
    | ~ r2_hidden(sK3(sK0(X0),X0),sK0(X0))
    | r2_hidden(sK3(sK0(X0),X0),sK5) ),
    inference(instantiation,[status(thm)],[c_3585])).

cnf(c_10806,plain,
    ( ~ r1_tarski(sK0(sK4),sK5)
    | ~ r2_hidden(sK3(sK0(sK4),sK4),sK0(sK4))
    | r2_hidden(sK3(sK0(sK4),sK4),sK5) ),
    inference(instantiation,[status(thm)],[c_10803])).

cnf(c_14362,plain,
    ( ~ r1_tarski(sK0(sK4),sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11200,c_18,c_17,c_57,c_287,c_307,c_371,c_383,c_2793,c_7470,c_9019,c_10806])).

cnf(c_14374,plain,
    ( ~ r2_hidden(sK0(sK4),sK5)
    | ~ v1_ordinal1(sK5) ),
    inference(resolution,[status(thm)],[c_14362,c_6])).

cnf(c_2296,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(sK0(X0),X0)
    | r2_hidden(sK0(X0),X1) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_5854,plain,
    ( ~ r1_tarski(X0,sK5)
    | ~ r2_hidden(sK0(X0),X0)
    | r2_hidden(sK0(X0),sK5) ),
    inference(instantiation,[status(thm)],[c_2296])).

cnf(c_5856,plain,
    ( ~ r1_tarski(sK4,sK5)
    | r2_hidden(sK0(sK4),sK5)
    | ~ r2_hidden(sK0(sK4),sK4) ),
    inference(instantiation,[status(thm)],[c_5854])).

cnf(c_296,plain,
    ( r2_hidden(sK0(X0),X0)
    | ~ v2_ordinal1(sK4)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_223])).

cnf(c_297,plain,
    ( r2_hidden(sK0(sK4),sK4)
    | ~ v2_ordinal1(sK4) ),
    inference(unflattening,[status(thm)],[c_296])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_14374,c_9019,c_5856,c_297,c_287,c_233,c_18])).


%------------------------------------------------------------------------------
