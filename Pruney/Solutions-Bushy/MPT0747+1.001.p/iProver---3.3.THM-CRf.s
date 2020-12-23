%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0747+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:02 EST 2020

% Result     : Theorem 1.08s
% Output     : CNFRefutation 1.08s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 192 expanded)
%              Number of clauses        :   58 (  66 expanded)
%              Number of leaves         :   12 (  38 expanded)
%              Depth                    :   10
%              Number of atoms          :  310 ( 658 expanded)
%              Number of equality atoms :   89 ( 113 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0,X1] :
      ( v3_ordinal1(X1)
     => ( r2_hidden(X0,X1)
       => v3_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f20,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f8,conjecture,(
    ! [X0] :
      ~ ! [X1] :
          ( r2_hidden(X1,X0)
        <=> v3_ordinal1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ~ ! [X1] :
            ( r2_hidden(X1,X0)
          <=> v3_ordinal1(X1) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f23,plain,(
    ? [X0] :
    ! [X1] :
      ( r2_hidden(X1,X0)
    <=> v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f30,plain,(
    ? [X0] :
    ! [X1] :
      ( ( r2_hidden(X1,X0)
        | ~ v3_ordinal1(X1) )
      & ( v3_ordinal1(X1)
        | ~ r2_hidden(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f31,plain,
    ( ? [X0] :
      ! [X1] :
        ( ( r2_hidden(X1,X0)
          | ~ v3_ordinal1(X1) )
        & ( v3_ordinal1(X1)
          | ~ r2_hidden(X1,X0) ) )
   => ! [X1] :
        ( ( r2_hidden(X1,sK4)
          | ~ v3_ordinal1(X1) )
        & ( v3_ordinal1(X1)
          | ~ r2_hidden(X1,sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X1] :
      ( ( r2_hidden(X1,sK4)
        | ~ v3_ordinal1(X1) )
      & ( v3_ordinal1(X1)
        | ~ r2_hidden(X1,sK4) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f30,f31])).

fof(f47,plain,(
    ! [X1] :
      ( r2_hidden(X1,sK4)
      | ~ v3_ordinal1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) )
     => v1_ordinal1(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f16,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ? [X1] :
          ( ~ r1_tarski(X1,X0)
          & r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X1,X0)
          & r2_hidden(X1,X0) )
     => ( ~ r1_tarski(sK0(X0),X0)
        & r2_hidden(sK0(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ( ~ r1_tarski(sK0(X0),X0)
        & r2_hidden(sK0(X0),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f24])).

fof(f36,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ r1_tarski(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f5])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f28])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f46,plain,(
    ! [X1] :
      ( v3_ordinal1(X1)
      | ~ r2_hidden(X1,sK4) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f7,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | X0 = X1
      | r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f4,axiom,(
    ! [X0] :
      ( v2_ordinal1(X0)
    <=> ! [X1,X2] :
          ~ ( ~ r2_hidden(X2,X1)
            & X1 != X2
            & ~ r2_hidden(X1,X2)
            & r2_hidden(X2,X0)
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ~ ( ~ r2_hidden(X2,X1)
            & X1 != X2
            & ~ r2_hidden(X1,X2)
            & r2_hidden(X2,X0)
            & r2_hidden(X1,X0) )
     => v2_ordinal1(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f4])).

fof(f17,plain,(
    ! [X0] :
      ( v2_ordinal1(X0)
      | ? [X1,X2] :
          ( ~ r2_hidden(X2,X1)
          & X1 != X2
          & ~ r2_hidden(X1,X2)
          & r2_hidden(X2,X0)
          & r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f10])).

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
      ( v2_ordinal1(X0)
      | ( ~ r2_hidden(sK2(X0),sK1(X0))
        & sK1(X0) != sK2(X0)
        & ~ r2_hidden(sK1(X0),sK2(X0))
        & r2_hidden(sK2(X0),X0)
        & r2_hidden(sK1(X0),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f17,f26])).

fof(f41,plain,(
    ! [X0] :
      ( v2_ordinal1(X0)
      | ~ r2_hidden(sK2(X0),sK1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v2_ordinal1(X0)
        & v1_ordinal1(X0) )
     => v3_ordinal1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( v3_ordinal1(X0)
      | ~ v2_ordinal1(X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f15,plain,(
    ! [X0] :
      ( v3_ordinal1(X0)
      | ~ v2_ordinal1(X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f34,plain,(
    ! [X0] :
      ( v3_ordinal1(X0)
      | ~ v2_ordinal1(X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f40,plain,(
    ! [X0] :
      ( v2_ordinal1(X0)
      | sK1(X0) != sK2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f39,plain,(
    ! [X0] :
      ( v2_ordinal1(X0)
      | ~ r2_hidden(sK1(X0),sK2(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f38,plain,(
    ! [X0] :
      ( v2_ordinal1(X0)
      | r2_hidden(sK2(X0),X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f37,plain,(
    ! [X0] :
      ( v2_ordinal1(X0)
      | r2_hidden(sK1(X0),X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f35,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v3_ordinal1(X1)
    | v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1172,plain,
    ( ~ r2_hidden(X0,sK0(sK4))
    | v3_ordinal1(X0)
    | ~ v3_ordinal1(sK0(sK4)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1234,plain,
    ( ~ r2_hidden(sK3(sK0(sK4),sK4),sK0(sK4))
    | v3_ordinal1(sK3(sK0(sK4),sK4))
    | ~ v3_ordinal1(sK0(sK4)) ),
    inference(instantiation,[status(thm)],[c_1172])).

cnf(c_1236,plain,
    ( r2_hidden(sK3(sK0(sK4),sK4),sK0(sK4)) != iProver_top
    | v3_ordinal1(sK3(sK0(sK4),sK4)) = iProver_top
    | v3_ordinal1(sK0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1234])).

cnf(c_13,negated_conjecture,
    ( r2_hidden(X0,sK4)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_938,plain,
    ( r2_hidden(X0,sK4) = iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2,plain,
    ( ~ r1_tarski(sK0(X0),X0)
    | v1_ordinal1(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_9,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(sK3(X0,X1),X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_220,plain,
    ( ~ r2_hidden(sK3(X0,X1),X1)
    | v1_ordinal1(X2)
    | X1 != X2
    | sK0(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_9])).

cnf(c_221,plain,
    ( ~ r2_hidden(sK3(sK0(X0),X0),X0)
    | v1_ordinal1(X0) ),
    inference(unflattening,[status(thm)],[c_220])).

cnf(c_935,plain,
    ( r2_hidden(sK3(sK0(X0),X0),X0) != iProver_top
    | v1_ordinal1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_221])).

cnf(c_1191,plain,
    ( v1_ordinal1(sK4) = iProver_top
    | v3_ordinal1(sK3(sK0(sK4),sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_938,c_935])).

cnf(c_14,negated_conjecture,
    ( ~ r2_hidden(X0,sK4)
    | v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1130,plain,
    ( ~ r2_hidden(sK0(sK4),sK4)
    | v3_ordinal1(sK0(sK4)) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1133,plain,
    ( r2_hidden(sK0(sK4),sK4) != iProver_top
    | v3_ordinal1(sK0(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1130])).

cnf(c_12,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X1,X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1084,plain,
    ( r2_hidden(sK1(X0),sK2(X0))
    | r2_hidden(sK2(X0),sK1(X0))
    | ~ v3_ordinal1(sK1(X0))
    | ~ v3_ordinal1(sK2(X0))
    | sK1(X0) = sK2(X0) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1085,plain,
    ( sK1(X0) = sK2(X0)
    | r2_hidden(sK1(X0),sK2(X0)) = iProver_top
    | r2_hidden(sK2(X0),sK1(X0)) = iProver_top
    | v3_ordinal1(sK1(X0)) != iProver_top
    | v3_ordinal1(sK2(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1084])).

cnf(c_1087,plain,
    ( sK1(sK4) = sK2(sK4)
    | r2_hidden(sK1(sK4),sK2(sK4)) = iProver_top
    | r2_hidden(sK2(sK4),sK1(sK4)) = iProver_top
    | v3_ordinal1(sK1(sK4)) != iProver_top
    | v3_ordinal1(sK2(sK4)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1085])).

cnf(c_1051,plain,
    ( ~ r2_hidden(sK1(sK4),sK4)
    | v3_ordinal1(sK1(sK4)) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1054,plain,
    ( r2_hidden(sK1(sK4),sK4) != iProver_top
    | v3_ordinal1(sK1(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1051])).

cnf(c_1045,plain,
    ( ~ r2_hidden(sK2(sK4),sK4)
    | v3_ordinal1(sK2(sK4)) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1048,plain,
    ( r2_hidden(sK2(sK4),sK4) != iProver_top
    | v3_ordinal1(sK2(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1045])).

cnf(c_4,plain,
    ( ~ r2_hidden(sK2(X0),sK1(X0))
    | v2_ordinal1(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1,plain,
    ( ~ v1_ordinal1(X0)
    | ~ v2_ordinal1(X0)
    | v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_345,plain,
    ( ~ r2_hidden(sK2(X0),sK1(X0))
    | ~ v1_ordinal1(X0)
    | v3_ordinal1(X0) ),
    inference(resolution,[status(thm)],[c_4,c_1])).

cnf(c_346,plain,
    ( r2_hidden(sK2(X0),sK1(X0)) != iProver_top
    | v1_ordinal1(X0) != iProver_top
    | v3_ordinal1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_345])).

cnf(c_348,plain,
    ( r2_hidden(sK2(sK4),sK1(sK4)) != iProver_top
    | v1_ordinal1(sK4) != iProver_top
    | v3_ordinal1(sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_346])).

cnf(c_5,plain,
    ( v2_ordinal1(X0)
    | sK1(X0) != sK2(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_331,plain,
    ( ~ v1_ordinal1(X0)
    | v3_ordinal1(X0)
    | sK1(X0) != sK2(X0) ),
    inference(resolution,[status(thm)],[c_5,c_1])).

cnf(c_332,plain,
    ( sK1(X0) != sK2(X0)
    | v1_ordinal1(X0) != iProver_top
    | v3_ordinal1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_331])).

cnf(c_334,plain,
    ( sK1(sK4) != sK2(sK4)
    | v1_ordinal1(sK4) != iProver_top
    | v3_ordinal1(sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_332])).

cnf(c_6,plain,
    ( ~ r2_hidden(sK1(X0),sK2(X0))
    | v2_ordinal1(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_317,plain,
    ( ~ r2_hidden(sK1(X0),sK2(X0))
    | ~ v1_ordinal1(X0)
    | v3_ordinal1(X0) ),
    inference(resolution,[status(thm)],[c_6,c_1])).

cnf(c_318,plain,
    ( r2_hidden(sK1(X0),sK2(X0)) != iProver_top
    | v1_ordinal1(X0) != iProver_top
    | v3_ordinal1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_317])).

cnf(c_320,plain,
    ( r2_hidden(sK1(sK4),sK2(sK4)) != iProver_top
    | v1_ordinal1(sK4) != iProver_top
    | v3_ordinal1(sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_318])).

cnf(c_7,plain,
    ( r2_hidden(sK2(X0),X0)
    | v2_ordinal1(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_303,plain,
    ( r2_hidden(sK2(X0),X0)
    | ~ v1_ordinal1(X0)
    | v3_ordinal1(X0) ),
    inference(resolution,[status(thm)],[c_7,c_1])).

cnf(c_304,plain,
    ( r2_hidden(sK2(X0),X0) = iProver_top
    | v1_ordinal1(X0) != iProver_top
    | v3_ordinal1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_303])).

cnf(c_306,plain,
    ( r2_hidden(sK2(sK4),sK4) = iProver_top
    | v1_ordinal1(sK4) != iProver_top
    | v3_ordinal1(sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_304])).

cnf(c_8,plain,
    ( r2_hidden(sK1(X0),X0)
    | v2_ordinal1(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_289,plain,
    ( r2_hidden(sK1(X0),X0)
    | ~ v1_ordinal1(X0)
    | v3_ordinal1(X0) ),
    inference(resolution,[status(thm)],[c_8,c_1])).

cnf(c_290,plain,
    ( r2_hidden(sK1(X0),X0) = iProver_top
    | v1_ordinal1(X0) != iProver_top
    | v3_ordinal1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_289])).

cnf(c_292,plain,
    ( r2_hidden(sK1(sK4),sK4) = iProver_top
    | v1_ordinal1(sK4) != iProver_top
    | v3_ordinal1(sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_290])).

cnf(c_10,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK3(X0,X1),X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_208,plain,
    ( r2_hidden(sK3(X0,X1),X0)
    | v1_ordinal1(X2)
    | X1 != X2
    | sK0(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_10])).

cnf(c_209,plain,
    ( r2_hidden(sK3(sK0(X0),X0),sK0(X0))
    | v1_ordinal1(X0) ),
    inference(unflattening,[status(thm)],[c_208])).

cnf(c_210,plain,
    ( r2_hidden(sK3(sK0(X0),X0),sK0(X0)) = iProver_top
    | v1_ordinal1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_209])).

cnf(c_212,plain,
    ( r2_hidden(sK3(sK0(sK4),sK4),sK0(sK4)) = iProver_top
    | v1_ordinal1(sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_210])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_53,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_55,plain,
    ( r2_hidden(sK4,sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_53])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_ordinal1(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_44,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_ordinal1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_46,plain,
    ( r2_hidden(sK0(sK4),sK4) = iProver_top
    | v1_ordinal1(sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_44])).

cnf(c_18,plain,
    ( r2_hidden(X0,sK4) = iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_20,plain,
    ( r2_hidden(sK4,sK4) = iProver_top
    | v3_ordinal1(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1236,c_1191,c_1133,c_1087,c_1054,c_1048,c_348,c_334,c_320,c_306,c_292,c_212,c_55,c_46,c_20])).


%------------------------------------------------------------------------------
