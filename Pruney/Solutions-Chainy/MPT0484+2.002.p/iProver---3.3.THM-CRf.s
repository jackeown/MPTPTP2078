%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:44:37 EST 2020

% Result     : Theorem 1.18s
% Output     : CNFRefutation 1.18s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 147 expanded)
%              Number of clauses        :   39 (  47 expanded)
%              Number of leaves         :   10 (  28 expanded)
%              Depth                    :   15
%              Number of atoms          :  249 ( 483 expanded)
%              Number of equality atoms :   57 ( 107 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(k2_relat_1(X1),X0)
         => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f15,plain,(
    ? [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) != X1
      & r1_tarski(k2_relat_1(X1),X0)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f16,plain,(
    ? [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) != X1
      & r1_tarski(k2_relat_1(X1),X0)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f29,plain,
    ( ? [X0,X1] :
        ( k5_relat_1(X1,k6_relat_1(X0)) != X1
        & r1_tarski(k2_relat_1(X1),X0)
        & v1_relat_1(X1) )
   => ( k5_relat_1(sK4,k6_relat_1(sK3)) != sK4
      & r1_tarski(k2_relat_1(sK4),sK3)
      & v1_relat_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( k5_relat_1(sK4,k6_relat_1(sK3)) != sK4
    & r1_tarski(k2_relat_1(sK4),sK3)
    & v1_relat_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f16,f29])).

fof(f48,plain,(
    r1_tarski(k2_relat_1(sK4),sK3) ),
    inference(cnf_transformation,[],[f30])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X0)
             => r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X1)
              | ~ r2_hidden(k4_tarski(X2,X3),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                & r2_hidden(k4_tarski(X2,X3),X0) ) )
          & ( ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
                | ~ r2_hidden(k4_tarski(X2,X3),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                & r2_hidden(k4_tarski(X2,X3),X0) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f23])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ~ r2_hidden(k4_tarski(X2,X3),X1)
          & r2_hidden(k4_tarski(X2,X3),X0) )
     => ( ~ r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1)
        & r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ( ~ r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1)
              & r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f24,f25])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f47,plain,(
    v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f30])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k2_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f11])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k2_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f17])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f19])).

fof(f31,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))
      <=> ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))
      <=> ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X1,X2) ) )
      | ~ v1_relat_1(X3) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))
          | ~ r2_hidden(k4_tarski(X0,X1),X3)
          | ~ r2_hidden(X1,X2) )
        & ( ( r2_hidden(k4_tarski(X0,X1),X3)
            & r2_hidden(X1,X2) )
          | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) ) )
      | ~ v1_relat_1(X3) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))
          | ~ r2_hidden(k4_tarski(X0,X1),X3)
          | ~ r2_hidden(X1,X2) )
        & ( ( r2_hidden(k4_tarski(X0,X1),X3)
            & r2_hidden(X1,X2) )
          | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) ) )
      | ~ v1_relat_1(X3) ) ),
    inference(flattening,[],[f27])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))
      | ~ r2_hidden(k4_tarski(X0,X1),X3)
      | ~ r2_hidden(X1,X2)
      | ~ v1_relat_1(X3) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f21])).

fof(f36,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f49,plain,(
    k5_relat_1(sK4,k6_relat_1(sK3)) != sK4 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_17,negated_conjecture,
    ( r1_tarski(k2_relat_1(sK4),sK3) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_719,plain,
    ( r1_tarski(k2_relat_1(sK4),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_7,plain,
    ( r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
    | r1_tarski(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_18,negated_conjecture,
    ( v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_204,plain,
    ( r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
    | r1_tarski(X0,X1)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_18])).

cnf(c_205,plain,
    ( r2_hidden(k4_tarski(sK1(sK4,X0),sK2(sK4,X0)),sK4)
    | r1_tarski(sK4,X0) ),
    inference(unflattening,[status(thm)],[c_204])).

cnf(c_717,plain,
    ( r2_hidden(k4_tarski(sK1(sK4,X0),sK2(sK4,X0)),sK4) = iProver_top
    | r1_tarski(sK4,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_205])).

cnf(c_9,plain,
    ( r2_hidden(X0,k2_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_260,plain,
    ( r2_hidden(X0,k2_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_18])).

cnf(c_261,plain,
    ( r2_hidden(X0,k2_relat_1(sK4))
    | ~ r2_hidden(k4_tarski(X1,X0),sK4) ),
    inference(unflattening,[status(thm)],[c_260])).

cnf(c_712,plain,
    ( r2_hidden(X0,k2_relat_1(sK4)) = iProver_top
    | r2_hidden(k4_tarski(X1,X0),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_261])).

cnf(c_1322,plain,
    ( r2_hidden(sK2(sK4,X0),k2_relat_1(sK4)) = iProver_top
    | r1_tarski(sK4,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_717,c_712])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_722,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2241,plain,
    ( r2_hidden(sK2(sK4,X0),X1) = iProver_top
    | r1_tarski(k2_relat_1(sK4),X1) != iProver_top
    | r1_tarski(sK4,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1322,c_722])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),X3)
    | r2_hidden(k4_tarski(X2,X0),k5_relat_1(X3,k6_relat_1(X1)))
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_284,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),X3)
    | r2_hidden(k4_tarski(X2,X0),k5_relat_1(X3,k6_relat_1(X1)))
    | sK4 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_18])).

cnf(c_285,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k4_tarski(X2,X0),k5_relat_1(sK4,k6_relat_1(X1)))
    | ~ r2_hidden(k4_tarski(X2,X0),sK4) ),
    inference(unflattening,[status(thm)],[c_284])).

cnf(c_710,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(k4_tarski(X2,X0),k5_relat_1(sK4,k6_relat_1(X1))) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_285])).

cnf(c_6,plain,
    ( ~ r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1)
    | r1_tarski(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_214,plain,
    ( ~ r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1)
    | r1_tarski(X0,X1)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_18])).

cnf(c_215,plain,
    ( ~ r2_hidden(k4_tarski(sK1(sK4,X0),sK2(sK4,X0)),X0)
    | r1_tarski(sK4,X0) ),
    inference(unflattening,[status(thm)],[c_214])).

cnf(c_716,plain,
    ( r2_hidden(k4_tarski(sK1(sK4,X0),sK2(sK4,X0)),X0) != iProver_top
    | r1_tarski(sK4,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_215])).

cnf(c_998,plain,
    ( r2_hidden(k4_tarski(sK1(sK4,k5_relat_1(sK4,k6_relat_1(X0))),sK2(sK4,k5_relat_1(sK4,k6_relat_1(X0)))),sK4) != iProver_top
    | r2_hidden(sK2(sK4,k5_relat_1(sK4,k6_relat_1(X0))),X0) != iProver_top
    | r1_tarski(sK4,k5_relat_1(sK4,k6_relat_1(X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_710,c_716])).

cnf(c_1237,plain,
    ( r2_hidden(k4_tarski(sK1(sK4,k5_relat_1(sK4,k6_relat_1(X0))),sK2(sK4,k5_relat_1(sK4,k6_relat_1(X0)))),sK4)
    | r1_tarski(sK4,k5_relat_1(sK4,k6_relat_1(X0))) ),
    inference(instantiation,[status(thm)],[c_205])).

cnf(c_1238,plain,
    ( r2_hidden(k4_tarski(sK1(sK4,k5_relat_1(sK4,k6_relat_1(X0))),sK2(sK4,k5_relat_1(sK4,k6_relat_1(X0)))),sK4) = iProver_top
    | r1_tarski(sK4,k5_relat_1(sK4,k6_relat_1(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1237])).

cnf(c_1453,plain,
    ( r2_hidden(sK2(sK4,k5_relat_1(sK4,k6_relat_1(X0))),X0) != iProver_top
    | r1_tarski(sK4,k5_relat_1(sK4,k6_relat_1(X0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_998,c_1238])).

cnf(c_2638,plain,
    ( r1_tarski(k2_relat_1(sK4),X0) != iProver_top
    | r1_tarski(sK4,k5_relat_1(sK4,k6_relat_1(X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2241,c_1453])).

cnf(c_15,plain,
    ( r1_tarski(k5_relat_1(X0,k6_relat_1(X1)),X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_195,plain,
    ( r1_tarski(k5_relat_1(X0,k6_relat_1(X1)),X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_18])).

cnf(c_196,plain,
    ( r1_tarski(k5_relat_1(sK4,k6_relat_1(X0)),sK4) ),
    inference(unflattening,[status(thm)],[c_195])).

cnf(c_718,plain,
    ( r1_tarski(k5_relat_1(sK4,k6_relat_1(X0)),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_196])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_721,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1197,plain,
    ( k5_relat_1(sK4,k6_relat_1(X0)) = sK4
    | r1_tarski(sK4,k5_relat_1(sK4,k6_relat_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_718,c_721])).

cnf(c_2981,plain,
    ( k5_relat_1(sK4,k6_relat_1(X0)) = sK4
    | r1_tarski(k2_relat_1(sK4),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2638,c_1197])).

cnf(c_3215,plain,
    ( k5_relat_1(sK4,k6_relat_1(sK3)) = sK4 ),
    inference(superposition,[status(thm)],[c_719,c_2981])).

cnf(c_16,negated_conjecture,
    ( k5_relat_1(sK4,k6_relat_1(sK3)) != sK4 ),
    inference(cnf_transformation,[],[f49])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3215,c_16])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:56:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.18/0.95  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.18/0.95  
% 1.18/0.95  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.18/0.95  
% 1.18/0.95  ------  iProver source info
% 1.18/0.95  
% 1.18/0.95  git: date: 2020-06-30 10:37:57 +0100
% 1.18/0.95  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.18/0.95  git: non_committed_changes: false
% 1.18/0.95  git: last_make_outside_of_git: false
% 1.18/0.95  
% 1.18/0.95  ------ 
% 1.18/0.95  
% 1.18/0.95  ------ Input Options
% 1.18/0.95  
% 1.18/0.95  --out_options                           all
% 1.18/0.95  --tptp_safe_out                         true
% 1.18/0.95  --problem_path                          ""
% 1.18/0.95  --include_path                          ""
% 1.18/0.95  --clausifier                            res/vclausify_rel
% 1.18/0.95  --clausifier_options                    --mode clausify
% 1.18/0.95  --stdin                                 false
% 1.18/0.95  --stats_out                             all
% 1.18/0.95  
% 1.18/0.95  ------ General Options
% 1.18/0.95  
% 1.18/0.95  --fof                                   false
% 1.18/0.95  --time_out_real                         305.
% 1.18/0.95  --time_out_virtual                      -1.
% 1.18/0.95  --symbol_type_check                     false
% 1.18/0.95  --clausify_out                          false
% 1.18/0.95  --sig_cnt_out                           false
% 1.18/0.95  --trig_cnt_out                          false
% 1.18/0.95  --trig_cnt_out_tolerance                1.
% 1.18/0.95  --trig_cnt_out_sk_spl                   false
% 1.18/0.95  --abstr_cl_out                          false
% 1.18/0.95  
% 1.18/0.95  ------ Global Options
% 1.18/0.95  
% 1.18/0.95  --schedule                              default
% 1.18/0.95  --add_important_lit                     false
% 1.18/0.95  --prop_solver_per_cl                    1000
% 1.18/0.95  --min_unsat_core                        false
% 1.18/0.95  --soft_assumptions                      false
% 1.18/0.95  --soft_lemma_size                       3
% 1.18/0.95  --prop_impl_unit_size                   0
% 1.18/0.95  --prop_impl_unit                        []
% 1.18/0.95  --share_sel_clauses                     true
% 1.18/0.95  --reset_solvers                         false
% 1.18/0.95  --bc_imp_inh                            [conj_cone]
% 1.18/0.95  --conj_cone_tolerance                   3.
% 1.18/0.95  --extra_neg_conj                        none
% 1.18/0.95  --large_theory_mode                     true
% 1.18/0.95  --prolific_symb_bound                   200
% 1.18/0.95  --lt_threshold                          2000
% 1.18/0.95  --clause_weak_htbl                      true
% 1.18/0.95  --gc_record_bc_elim                     false
% 1.18/0.95  
% 1.18/0.95  ------ Preprocessing Options
% 1.18/0.95  
% 1.18/0.95  --preprocessing_flag                    true
% 1.18/0.95  --time_out_prep_mult                    0.1
% 1.18/0.95  --splitting_mode                        input
% 1.18/0.95  --splitting_grd                         true
% 1.18/0.95  --splitting_cvd                         false
% 1.18/0.95  --splitting_cvd_svl                     false
% 1.18/0.95  --splitting_nvd                         32
% 1.18/0.95  --sub_typing                            true
% 1.18/0.95  --prep_gs_sim                           true
% 1.18/0.95  --prep_unflatten                        true
% 1.18/0.95  --prep_res_sim                          true
% 1.18/0.95  --prep_upred                            true
% 1.18/0.95  --prep_sem_filter                       exhaustive
% 1.18/0.95  --prep_sem_filter_out                   false
% 1.18/0.95  --pred_elim                             true
% 1.18/0.95  --res_sim_input                         true
% 1.18/0.95  --eq_ax_congr_red                       true
% 1.18/0.95  --pure_diseq_elim                       true
% 1.18/0.95  --brand_transform                       false
% 1.18/0.95  --non_eq_to_eq                          false
% 1.18/0.95  --prep_def_merge                        true
% 1.18/0.95  --prep_def_merge_prop_impl              false
% 1.18/0.95  --prep_def_merge_mbd                    true
% 1.18/0.95  --prep_def_merge_tr_red                 false
% 1.18/0.95  --prep_def_merge_tr_cl                  false
% 1.18/0.95  --smt_preprocessing                     true
% 1.18/0.95  --smt_ac_axioms                         fast
% 1.18/0.95  --preprocessed_out                      false
% 1.18/0.95  --preprocessed_stats                    false
% 1.18/0.95  
% 1.18/0.95  ------ Abstraction refinement Options
% 1.18/0.95  
% 1.18/0.95  --abstr_ref                             []
% 1.18/0.95  --abstr_ref_prep                        false
% 1.18/0.95  --abstr_ref_until_sat                   false
% 1.18/0.95  --abstr_ref_sig_restrict                funpre
% 1.18/0.95  --abstr_ref_af_restrict_to_split_sk     false
% 1.18/0.95  --abstr_ref_under                       []
% 1.18/0.95  
% 1.18/0.95  ------ SAT Options
% 1.18/0.95  
% 1.18/0.95  --sat_mode                              false
% 1.18/0.95  --sat_fm_restart_options                ""
% 1.18/0.95  --sat_gr_def                            false
% 1.18/0.95  --sat_epr_types                         true
% 1.18/0.95  --sat_non_cyclic_types                  false
% 1.18/0.95  --sat_finite_models                     false
% 1.18/0.95  --sat_fm_lemmas                         false
% 1.18/0.95  --sat_fm_prep                           false
% 1.18/0.95  --sat_fm_uc_incr                        true
% 1.18/0.95  --sat_out_model                         small
% 1.18/0.95  --sat_out_clauses                       false
% 1.18/0.95  
% 1.18/0.95  ------ QBF Options
% 1.18/0.95  
% 1.18/0.95  --qbf_mode                              false
% 1.18/0.95  --qbf_elim_univ                         false
% 1.18/0.95  --qbf_dom_inst                          none
% 1.18/0.95  --qbf_dom_pre_inst                      false
% 1.18/0.95  --qbf_sk_in                             false
% 1.18/0.95  --qbf_pred_elim                         true
% 1.18/0.95  --qbf_split                             512
% 1.18/0.95  
% 1.18/0.95  ------ BMC1 Options
% 1.18/0.95  
% 1.18/0.95  --bmc1_incremental                      false
% 1.18/0.95  --bmc1_axioms                           reachable_all
% 1.18/0.95  --bmc1_min_bound                        0
% 1.18/0.95  --bmc1_max_bound                        -1
% 1.18/0.95  --bmc1_max_bound_default                -1
% 1.18/0.95  --bmc1_symbol_reachability              true
% 1.18/0.95  --bmc1_property_lemmas                  false
% 1.18/0.95  --bmc1_k_induction                      false
% 1.18/0.95  --bmc1_non_equiv_states                 false
% 1.18/0.95  --bmc1_deadlock                         false
% 1.18/0.95  --bmc1_ucm                              false
% 1.18/0.95  --bmc1_add_unsat_core                   none
% 1.18/0.95  --bmc1_unsat_core_children              false
% 1.18/0.95  --bmc1_unsat_core_extrapolate_axioms    false
% 1.18/0.95  --bmc1_out_stat                         full
% 1.18/0.95  --bmc1_ground_init                      false
% 1.18/0.95  --bmc1_pre_inst_next_state              false
% 1.18/0.95  --bmc1_pre_inst_state                   false
% 1.18/0.95  --bmc1_pre_inst_reach_state             false
% 1.18/0.95  --bmc1_out_unsat_core                   false
% 1.18/0.95  --bmc1_aig_witness_out                  false
% 1.18/0.95  --bmc1_verbose                          false
% 1.18/0.95  --bmc1_dump_clauses_tptp                false
% 1.18/0.95  --bmc1_dump_unsat_core_tptp             false
% 1.18/0.95  --bmc1_dump_file                        -
% 1.18/0.95  --bmc1_ucm_expand_uc_limit              128
% 1.18/0.95  --bmc1_ucm_n_expand_iterations          6
% 1.18/0.95  --bmc1_ucm_extend_mode                  1
% 1.18/0.95  --bmc1_ucm_init_mode                    2
% 1.18/0.95  --bmc1_ucm_cone_mode                    none
% 1.18/0.95  --bmc1_ucm_reduced_relation_type        0
% 1.18/0.95  --bmc1_ucm_relax_model                  4
% 1.18/0.95  --bmc1_ucm_full_tr_after_sat            true
% 1.18/0.95  --bmc1_ucm_expand_neg_assumptions       false
% 1.18/0.95  --bmc1_ucm_layered_model                none
% 1.18/0.95  --bmc1_ucm_max_lemma_size               10
% 1.18/0.95  
% 1.18/0.95  ------ AIG Options
% 1.18/0.95  
% 1.18/0.95  --aig_mode                              false
% 1.18/0.95  
% 1.18/0.95  ------ Instantiation Options
% 1.18/0.95  
% 1.18/0.95  --instantiation_flag                    true
% 1.18/0.95  --inst_sos_flag                         false
% 1.18/0.95  --inst_sos_phase                        true
% 1.18/0.95  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.18/0.95  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.18/0.95  --inst_lit_sel_side                     num_symb
% 1.18/0.95  --inst_solver_per_active                1400
% 1.18/0.95  --inst_solver_calls_frac                1.
% 1.18/0.95  --inst_passive_queue_type               priority_queues
% 1.18/0.95  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.18/0.95  --inst_passive_queues_freq              [25;2]
% 1.18/0.95  --inst_dismatching                      true
% 1.18/0.95  --inst_eager_unprocessed_to_passive     true
% 1.18/0.95  --inst_prop_sim_given                   true
% 1.18/0.95  --inst_prop_sim_new                     false
% 1.18/0.95  --inst_subs_new                         false
% 1.18/0.95  --inst_eq_res_simp                      false
% 1.18/0.95  --inst_subs_given                       false
% 1.18/0.95  --inst_orphan_elimination               true
% 1.18/0.95  --inst_learning_loop_flag               true
% 1.18/0.95  --inst_learning_start                   3000
% 1.18/0.95  --inst_learning_factor                  2
% 1.18/0.95  --inst_start_prop_sim_after_learn       3
% 1.18/0.95  --inst_sel_renew                        solver
% 1.18/0.95  --inst_lit_activity_flag                true
% 1.18/0.95  --inst_restr_to_given                   false
% 1.18/0.95  --inst_activity_threshold               500
% 1.18/0.95  --inst_out_proof                        true
% 1.18/0.95  
% 1.18/0.95  ------ Resolution Options
% 1.18/0.95  
% 1.18/0.95  --resolution_flag                       true
% 1.18/0.95  --res_lit_sel                           adaptive
% 1.18/0.95  --res_lit_sel_side                      none
% 1.18/0.95  --res_ordering                          kbo
% 1.18/0.95  --res_to_prop_solver                    active
% 1.18/0.95  --res_prop_simpl_new                    false
% 1.18/0.95  --res_prop_simpl_given                  true
% 1.18/0.95  --res_passive_queue_type                priority_queues
% 1.18/0.95  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.18/0.95  --res_passive_queues_freq               [15;5]
% 1.18/0.95  --res_forward_subs                      full
% 1.18/0.95  --res_backward_subs                     full
% 1.18/0.95  --res_forward_subs_resolution           true
% 1.18/0.95  --res_backward_subs_resolution          true
% 1.18/0.95  --res_orphan_elimination                true
% 1.18/0.95  --res_time_limit                        2.
% 1.18/0.95  --res_out_proof                         true
% 1.18/0.95  
% 1.18/0.95  ------ Superposition Options
% 1.18/0.95  
% 1.18/0.95  --superposition_flag                    true
% 1.18/0.95  --sup_passive_queue_type                priority_queues
% 1.18/0.95  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.18/0.95  --sup_passive_queues_freq               [8;1;4]
% 1.18/0.95  --demod_completeness_check              fast
% 1.18/0.95  --demod_use_ground                      true
% 1.18/0.95  --sup_to_prop_solver                    passive
% 1.18/0.95  --sup_prop_simpl_new                    true
% 1.18/0.95  --sup_prop_simpl_given                  true
% 1.18/0.95  --sup_fun_splitting                     false
% 1.18/0.95  --sup_smt_interval                      50000
% 1.18/0.95  
% 1.18/0.95  ------ Superposition Simplification Setup
% 1.18/0.95  
% 1.18/0.95  --sup_indices_passive                   []
% 1.18/0.95  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.18/0.95  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.18/0.95  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.18/0.95  --sup_full_triv                         [TrivRules;PropSubs]
% 1.18/0.95  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.18/0.95  --sup_full_bw                           [BwDemod]
% 1.18/0.95  --sup_immed_triv                        [TrivRules]
% 1.18/0.95  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.18/0.95  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.18/0.95  --sup_immed_bw_main                     []
% 1.18/0.95  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.18/0.95  --sup_input_triv                        [Unflattening;TrivRules]
% 1.18/0.95  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.18/0.95  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.18/0.95  
% 1.18/0.95  ------ Combination Options
% 1.18/0.95  
% 1.18/0.95  --comb_res_mult                         3
% 1.18/0.95  --comb_sup_mult                         2
% 1.18/0.95  --comb_inst_mult                        10
% 1.18/0.95  
% 1.18/0.95  ------ Debug Options
% 1.18/0.95  
% 1.18/0.95  --dbg_backtrace                         false
% 1.18/0.95  --dbg_dump_prop_clauses                 false
% 1.18/0.95  --dbg_dump_prop_clauses_file            -
% 1.18/0.95  --dbg_out_stat                          false
% 1.18/0.95  ------ Parsing...
% 1.18/0.95  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.18/0.95  
% 1.18/0.95  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 1.18/0.95  
% 1.18/0.95  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.18/0.95  
% 1.18/0.95  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.18/0.95  ------ Proving...
% 1.18/0.95  ------ Problem Properties 
% 1.18/0.95  
% 1.18/0.95  
% 1.18/0.95  clauses                                 16
% 1.18/0.95  conjectures                             2
% 1.18/0.95  EPR                                     3
% 1.18/0.95  Horn                                    14
% 1.18/0.95  unary                                   5
% 1.18/0.95  binary                                  8
% 1.18/0.95  lits                                    30
% 1.18/0.95  lits eq                                 2
% 1.18/0.95  fd_pure                                 0
% 1.18/0.95  fd_pseudo                               0
% 1.18/0.95  fd_cond                                 0
% 1.18/0.95  fd_pseudo_cond                          1
% 1.18/0.95  AC symbols                              0
% 1.18/0.95  
% 1.18/0.95  ------ Schedule dynamic 5 is on 
% 1.18/0.95  
% 1.18/0.95  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.18/0.95  
% 1.18/0.95  
% 1.18/0.95  ------ 
% 1.18/0.95  Current options:
% 1.18/0.95  ------ 
% 1.18/0.95  
% 1.18/0.95  ------ Input Options
% 1.18/0.95  
% 1.18/0.95  --out_options                           all
% 1.18/0.95  --tptp_safe_out                         true
% 1.18/0.95  --problem_path                          ""
% 1.18/0.95  --include_path                          ""
% 1.18/0.95  --clausifier                            res/vclausify_rel
% 1.18/0.95  --clausifier_options                    --mode clausify
% 1.18/0.95  --stdin                                 false
% 1.18/0.95  --stats_out                             all
% 1.18/0.95  
% 1.18/0.95  ------ General Options
% 1.18/0.95  
% 1.18/0.95  --fof                                   false
% 1.18/0.95  --time_out_real                         305.
% 1.18/0.95  --time_out_virtual                      -1.
% 1.18/0.95  --symbol_type_check                     false
% 1.18/0.95  --clausify_out                          false
% 1.18/0.95  --sig_cnt_out                           false
% 1.18/0.95  --trig_cnt_out                          false
% 1.18/0.95  --trig_cnt_out_tolerance                1.
% 1.18/0.95  --trig_cnt_out_sk_spl                   false
% 1.18/0.95  --abstr_cl_out                          false
% 1.18/0.95  
% 1.18/0.95  ------ Global Options
% 1.18/0.95  
% 1.18/0.95  --schedule                              default
% 1.18/0.95  --add_important_lit                     false
% 1.18/0.95  --prop_solver_per_cl                    1000
% 1.18/0.95  --min_unsat_core                        false
% 1.18/0.95  --soft_assumptions                      false
% 1.18/0.95  --soft_lemma_size                       3
% 1.18/0.95  --prop_impl_unit_size                   0
% 1.18/0.95  --prop_impl_unit                        []
% 1.18/0.95  --share_sel_clauses                     true
% 1.18/0.95  --reset_solvers                         false
% 1.18/0.95  --bc_imp_inh                            [conj_cone]
% 1.18/0.95  --conj_cone_tolerance                   3.
% 1.18/0.95  --extra_neg_conj                        none
% 1.18/0.95  --large_theory_mode                     true
% 1.18/0.95  --prolific_symb_bound                   200
% 1.18/0.95  --lt_threshold                          2000
% 1.18/0.95  --clause_weak_htbl                      true
% 1.18/0.95  --gc_record_bc_elim                     false
% 1.18/0.95  
% 1.18/0.95  ------ Preprocessing Options
% 1.18/0.95  
% 1.18/0.95  --preprocessing_flag                    true
% 1.18/0.95  --time_out_prep_mult                    0.1
% 1.18/0.95  --splitting_mode                        input
% 1.18/0.95  --splitting_grd                         true
% 1.18/0.95  --splitting_cvd                         false
% 1.18/0.95  --splitting_cvd_svl                     false
% 1.18/0.95  --splitting_nvd                         32
% 1.18/0.95  --sub_typing                            true
% 1.18/0.95  --prep_gs_sim                           true
% 1.18/0.95  --prep_unflatten                        true
% 1.18/0.95  --prep_res_sim                          true
% 1.18/0.95  --prep_upred                            true
% 1.18/0.95  --prep_sem_filter                       exhaustive
% 1.18/0.95  --prep_sem_filter_out                   false
% 1.18/0.95  --pred_elim                             true
% 1.18/0.95  --res_sim_input                         true
% 1.18/0.95  --eq_ax_congr_red                       true
% 1.18/0.95  --pure_diseq_elim                       true
% 1.18/0.95  --brand_transform                       false
% 1.18/0.95  --non_eq_to_eq                          false
% 1.18/0.95  --prep_def_merge                        true
% 1.18/0.95  --prep_def_merge_prop_impl              false
% 1.18/0.95  --prep_def_merge_mbd                    true
% 1.18/0.95  --prep_def_merge_tr_red                 false
% 1.18/0.95  --prep_def_merge_tr_cl                  false
% 1.18/0.95  --smt_preprocessing                     true
% 1.18/0.95  --smt_ac_axioms                         fast
% 1.18/0.95  --preprocessed_out                      false
% 1.18/0.95  --preprocessed_stats                    false
% 1.18/0.95  
% 1.18/0.95  ------ Abstraction refinement Options
% 1.18/0.95  
% 1.18/0.95  --abstr_ref                             []
% 1.18/0.95  --abstr_ref_prep                        false
% 1.18/0.95  --abstr_ref_until_sat                   false
% 1.18/0.95  --abstr_ref_sig_restrict                funpre
% 1.18/0.95  --abstr_ref_af_restrict_to_split_sk     false
% 1.18/0.95  --abstr_ref_under                       []
% 1.18/0.95  
% 1.18/0.95  ------ SAT Options
% 1.18/0.95  
% 1.18/0.95  --sat_mode                              false
% 1.18/0.95  --sat_fm_restart_options                ""
% 1.18/0.95  --sat_gr_def                            false
% 1.18/0.95  --sat_epr_types                         true
% 1.18/0.95  --sat_non_cyclic_types                  false
% 1.18/0.95  --sat_finite_models                     false
% 1.18/0.95  --sat_fm_lemmas                         false
% 1.18/0.95  --sat_fm_prep                           false
% 1.18/0.95  --sat_fm_uc_incr                        true
% 1.18/0.95  --sat_out_model                         small
% 1.18/0.95  --sat_out_clauses                       false
% 1.18/0.95  
% 1.18/0.95  ------ QBF Options
% 1.18/0.95  
% 1.18/0.95  --qbf_mode                              false
% 1.18/0.95  --qbf_elim_univ                         false
% 1.18/0.95  --qbf_dom_inst                          none
% 1.18/0.95  --qbf_dom_pre_inst                      false
% 1.18/0.95  --qbf_sk_in                             false
% 1.18/0.95  --qbf_pred_elim                         true
% 1.18/0.95  --qbf_split                             512
% 1.18/0.95  
% 1.18/0.95  ------ BMC1 Options
% 1.18/0.95  
% 1.18/0.95  --bmc1_incremental                      false
% 1.18/0.95  --bmc1_axioms                           reachable_all
% 1.18/0.95  --bmc1_min_bound                        0
% 1.18/0.95  --bmc1_max_bound                        -1
% 1.18/0.95  --bmc1_max_bound_default                -1
% 1.18/0.95  --bmc1_symbol_reachability              true
% 1.18/0.95  --bmc1_property_lemmas                  false
% 1.18/0.95  --bmc1_k_induction                      false
% 1.18/0.95  --bmc1_non_equiv_states                 false
% 1.18/0.95  --bmc1_deadlock                         false
% 1.18/0.95  --bmc1_ucm                              false
% 1.18/0.95  --bmc1_add_unsat_core                   none
% 1.18/0.95  --bmc1_unsat_core_children              false
% 1.18/0.95  --bmc1_unsat_core_extrapolate_axioms    false
% 1.18/0.95  --bmc1_out_stat                         full
% 1.18/0.95  --bmc1_ground_init                      false
% 1.18/0.95  --bmc1_pre_inst_next_state              false
% 1.18/0.95  --bmc1_pre_inst_state                   false
% 1.18/0.95  --bmc1_pre_inst_reach_state             false
% 1.18/0.95  --bmc1_out_unsat_core                   false
% 1.18/0.95  --bmc1_aig_witness_out                  false
% 1.18/0.95  --bmc1_verbose                          false
% 1.18/0.95  --bmc1_dump_clauses_tptp                false
% 1.18/0.95  --bmc1_dump_unsat_core_tptp             false
% 1.18/0.95  --bmc1_dump_file                        -
% 1.18/0.95  --bmc1_ucm_expand_uc_limit              128
% 1.18/0.95  --bmc1_ucm_n_expand_iterations          6
% 1.18/0.95  --bmc1_ucm_extend_mode                  1
% 1.18/0.95  --bmc1_ucm_init_mode                    2
% 1.18/0.95  --bmc1_ucm_cone_mode                    none
% 1.18/0.95  --bmc1_ucm_reduced_relation_type        0
% 1.18/0.95  --bmc1_ucm_relax_model                  4
% 1.18/0.95  --bmc1_ucm_full_tr_after_sat            true
% 1.18/0.95  --bmc1_ucm_expand_neg_assumptions       false
% 1.18/0.95  --bmc1_ucm_layered_model                none
% 1.18/0.95  --bmc1_ucm_max_lemma_size               10
% 1.18/0.95  
% 1.18/0.95  ------ AIG Options
% 1.18/0.95  
% 1.18/0.95  --aig_mode                              false
% 1.18/0.95  
% 1.18/0.95  ------ Instantiation Options
% 1.18/0.95  
% 1.18/0.95  --instantiation_flag                    true
% 1.18/0.95  --inst_sos_flag                         false
% 1.18/0.95  --inst_sos_phase                        true
% 1.18/0.95  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.18/0.95  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.18/0.95  --inst_lit_sel_side                     none
% 1.18/0.95  --inst_solver_per_active                1400
% 1.18/0.95  --inst_solver_calls_frac                1.
% 1.18/0.95  --inst_passive_queue_type               priority_queues
% 1.18/0.95  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.18/0.95  --inst_passive_queues_freq              [25;2]
% 1.18/0.95  --inst_dismatching                      true
% 1.18/0.95  --inst_eager_unprocessed_to_passive     true
% 1.18/0.95  --inst_prop_sim_given                   true
% 1.18/0.95  --inst_prop_sim_new                     false
% 1.18/0.95  --inst_subs_new                         false
% 1.18/0.95  --inst_eq_res_simp                      false
% 1.18/0.95  --inst_subs_given                       false
% 1.18/0.95  --inst_orphan_elimination               true
% 1.18/0.95  --inst_learning_loop_flag               true
% 1.18/0.95  --inst_learning_start                   3000
% 1.18/0.95  --inst_learning_factor                  2
% 1.18/0.95  --inst_start_prop_sim_after_learn       3
% 1.18/0.95  --inst_sel_renew                        solver
% 1.18/0.95  --inst_lit_activity_flag                true
% 1.18/0.95  --inst_restr_to_given                   false
% 1.18/0.95  --inst_activity_threshold               500
% 1.18/0.95  --inst_out_proof                        true
% 1.18/0.95  
% 1.18/0.95  ------ Resolution Options
% 1.18/0.95  
% 1.18/0.95  --resolution_flag                       false
% 1.18/0.95  --res_lit_sel                           adaptive
% 1.18/0.95  --res_lit_sel_side                      none
% 1.18/0.95  --res_ordering                          kbo
% 1.18/0.95  --res_to_prop_solver                    active
% 1.18/0.95  --res_prop_simpl_new                    false
% 1.18/0.95  --res_prop_simpl_given                  true
% 1.18/0.95  --res_passive_queue_type                priority_queues
% 1.18/0.95  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.18/0.95  --res_passive_queues_freq               [15;5]
% 1.18/0.95  --res_forward_subs                      full
% 1.18/0.95  --res_backward_subs                     full
% 1.18/0.95  --res_forward_subs_resolution           true
% 1.18/0.95  --res_backward_subs_resolution          true
% 1.18/0.95  --res_orphan_elimination                true
% 1.18/0.95  --res_time_limit                        2.
% 1.18/0.95  --res_out_proof                         true
% 1.18/0.95  
% 1.18/0.95  ------ Superposition Options
% 1.18/0.95  
% 1.18/0.95  --superposition_flag                    true
% 1.18/0.95  --sup_passive_queue_type                priority_queues
% 1.18/0.95  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.18/0.95  --sup_passive_queues_freq               [8;1;4]
% 1.18/0.95  --demod_completeness_check              fast
% 1.18/0.95  --demod_use_ground                      true
% 1.18/0.95  --sup_to_prop_solver                    passive
% 1.18/0.95  --sup_prop_simpl_new                    true
% 1.18/0.95  --sup_prop_simpl_given                  true
% 1.18/0.95  --sup_fun_splitting                     false
% 1.18/0.95  --sup_smt_interval                      50000
% 1.18/0.95  
% 1.18/0.95  ------ Superposition Simplification Setup
% 1.18/0.95  
% 1.18/0.95  --sup_indices_passive                   []
% 1.18/0.95  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.18/0.95  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.18/0.95  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.18/0.95  --sup_full_triv                         [TrivRules;PropSubs]
% 1.18/0.95  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.18/0.95  --sup_full_bw                           [BwDemod]
% 1.18/0.95  --sup_immed_triv                        [TrivRules]
% 1.18/0.95  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.18/0.95  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.18/0.95  --sup_immed_bw_main                     []
% 1.18/0.95  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.18/0.95  --sup_input_triv                        [Unflattening;TrivRules]
% 1.18/0.95  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.18/0.95  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.18/0.95  
% 1.18/0.95  ------ Combination Options
% 1.18/0.95  
% 1.18/0.95  --comb_res_mult                         3
% 1.18/0.95  --comb_sup_mult                         2
% 1.18/0.95  --comb_inst_mult                        10
% 1.18/0.95  
% 1.18/0.95  ------ Debug Options
% 1.18/0.95  
% 1.18/0.95  --dbg_backtrace                         false
% 1.18/0.95  --dbg_dump_prop_clauses                 false
% 1.18/0.95  --dbg_dump_prop_clauses_file            -
% 1.18/0.95  --dbg_out_stat                          false
% 1.18/0.95  
% 1.18/0.95  
% 1.18/0.95  
% 1.18/0.95  
% 1.18/0.95  ------ Proving...
% 1.18/0.95  
% 1.18/0.95  
% 1.18/0.95  % SZS status Theorem for theBenchmark.p
% 1.18/0.95  
% 1.18/0.95  % SZS output start CNFRefutation for theBenchmark.p
% 1.18/0.95  
% 1.18/0.95  fof(f7,conjecture,(
% 1.18/0.95    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 1.18/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.18/0.95  
% 1.18/0.95  fof(f8,negated_conjecture,(
% 1.18/0.95    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 1.18/0.95    inference(negated_conjecture,[],[f7])).
% 1.18/0.95  
% 1.18/0.95  fof(f15,plain,(
% 1.18/0.95    ? [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) != X1 & r1_tarski(k2_relat_1(X1),X0)) & v1_relat_1(X1))),
% 1.18/0.95    inference(ennf_transformation,[],[f8])).
% 1.18/0.95  
% 1.18/0.95  fof(f16,plain,(
% 1.18/0.95    ? [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) != X1 & r1_tarski(k2_relat_1(X1),X0) & v1_relat_1(X1))),
% 1.18/0.95    inference(flattening,[],[f15])).
% 1.18/0.95  
% 1.18/0.95  fof(f29,plain,(
% 1.18/0.95    ? [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) != X1 & r1_tarski(k2_relat_1(X1),X0) & v1_relat_1(X1)) => (k5_relat_1(sK4,k6_relat_1(sK3)) != sK4 & r1_tarski(k2_relat_1(sK4),sK3) & v1_relat_1(sK4))),
% 1.18/0.95    introduced(choice_axiom,[])).
% 1.18/0.95  
% 1.18/0.95  fof(f30,plain,(
% 1.18/0.95    k5_relat_1(sK4,k6_relat_1(sK3)) != sK4 & r1_tarski(k2_relat_1(sK4),sK3) & v1_relat_1(sK4)),
% 1.18/0.95    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f16,f29])).
% 1.18/0.95  
% 1.18/0.95  fof(f48,plain,(
% 1.18/0.95    r1_tarski(k2_relat_1(sK4),sK3)),
% 1.18/0.95    inference(cnf_transformation,[],[f30])).
% 1.18/0.95  
% 1.18/0.95  fof(f3,axiom,(
% 1.18/0.95    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X0) => r2_hidden(k4_tarski(X2,X3),X1))))),
% 1.18/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.18/0.95  
% 1.18/0.95  fof(f10,plain,(
% 1.18/0.95    ! [X0] : (! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0))) | ~v1_relat_1(X0))),
% 1.18/0.95    inference(ennf_transformation,[],[f3])).
% 1.18/0.95  
% 1.18/0.95  fof(f23,plain,(
% 1.18/0.95    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | ? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0))) & (! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 1.18/0.95    inference(nnf_transformation,[],[f10])).
% 1.18/0.95  
% 1.18/0.95  fof(f24,plain,(
% 1.18/0.95    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | ? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0))) & (! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 1.18/0.95    inference(rectify,[],[f23])).
% 1.18/0.95  
% 1.18/0.95  fof(f25,plain,(
% 1.18/0.95    ! [X1,X0] : (? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0)) => (~r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1) & r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)))),
% 1.18/0.95    introduced(choice_axiom,[])).
% 1.18/0.95  
% 1.18/0.95  fof(f26,plain,(
% 1.18/0.95    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | (~r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1) & r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0))) & (! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 1.18/0.95    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f24,f25])).
% 1.18/0.95  
% 1.18/0.95  fof(f38,plain,(
% 1.18/0.95    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) | ~v1_relat_1(X0)) )),
% 1.18/0.95    inference(cnf_transformation,[],[f26])).
% 1.18/0.95  
% 1.18/0.95  fof(f47,plain,(
% 1.18/0.95    v1_relat_1(sK4)),
% 1.18/0.95    inference(cnf_transformation,[],[f30])).
% 1.18/0.95  
% 1.18/0.95  fof(f4,axiom,(
% 1.18/0.95    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2)))))),
% 1.18/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.18/0.95  
% 1.18/0.95  fof(f11,plain,(
% 1.18/0.95    ! [X0,X1,X2] : (((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 1.18/0.95    inference(ennf_transformation,[],[f4])).
% 1.18/0.95  
% 1.18/0.95  fof(f12,plain,(
% 1.18/0.95    ! [X0,X1,X2] : ((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 1.18/0.95    inference(flattening,[],[f11])).
% 1.18/0.95  
% 1.18/0.95  fof(f41,plain,(
% 1.18/0.95    ( ! [X2,X0,X1] : (r2_hidden(X1,k2_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 1.18/0.95    inference(cnf_transformation,[],[f12])).
% 1.18/0.95  
% 1.18/0.95  fof(f1,axiom,(
% 1.18/0.95    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.18/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.18/0.95  
% 1.18/0.95  fof(f9,plain,(
% 1.18/0.95    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.18/0.95    inference(ennf_transformation,[],[f1])).
% 1.18/0.95  
% 1.18/0.95  fof(f17,plain,(
% 1.18/0.95    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.18/0.95    inference(nnf_transformation,[],[f9])).
% 1.18/0.95  
% 1.18/0.95  fof(f18,plain,(
% 1.18/0.95    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.18/0.95    inference(rectify,[],[f17])).
% 1.18/0.95  
% 1.18/0.95  fof(f19,plain,(
% 1.18/0.95    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 1.18/0.95    introduced(choice_axiom,[])).
% 1.18/0.95  
% 1.18/0.95  fof(f20,plain,(
% 1.18/0.95    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.18/0.95    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f19])).
% 1.18/0.95  
% 1.18/0.95  fof(f31,plain,(
% 1.18/0.95    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 1.18/0.95    inference(cnf_transformation,[],[f20])).
% 1.18/0.95  
% 1.18/0.95  fof(f5,axiom,(
% 1.18/0.95    ! [X0,X1,X2,X3] : (v1_relat_1(X3) => (r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) <=> (r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X1,X2))))),
% 1.18/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.18/0.95  
% 1.18/0.95  fof(f13,plain,(
% 1.18/0.95    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) <=> (r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X1,X2))) | ~v1_relat_1(X3))),
% 1.18/0.95    inference(ennf_transformation,[],[f5])).
% 1.18/0.95  
% 1.18/0.95  fof(f27,plain,(
% 1.18/0.95    ! [X0,X1,X2,X3] : (((r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) | (~r2_hidden(k4_tarski(X0,X1),X3) | ~r2_hidden(X1,X2))) & ((r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X1,X2)) | ~r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))))) | ~v1_relat_1(X3))),
% 1.18/0.95    inference(nnf_transformation,[],[f13])).
% 1.18/0.95  
% 1.18/0.95  fof(f28,plain,(
% 1.18/0.95    ! [X0,X1,X2,X3] : (((r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X3) | ~r2_hidden(X1,X2)) & ((r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X1,X2)) | ~r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))))) | ~v1_relat_1(X3))),
% 1.18/0.95    inference(flattening,[],[f27])).
% 1.18/0.95  
% 1.18/0.95  fof(f44,plain,(
% 1.18/0.95    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X3) | ~r2_hidden(X1,X2) | ~v1_relat_1(X3)) )),
% 1.18/0.95    inference(cnf_transformation,[],[f28])).
% 1.18/0.95  
% 1.18/0.95  fof(f39,plain,(
% 1.18/0.95    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1) | ~v1_relat_1(X0)) )),
% 1.18/0.95    inference(cnf_transformation,[],[f26])).
% 1.18/0.95  
% 1.18/0.95  fof(f6,axiom,(
% 1.18/0.95    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)))),
% 1.18/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.18/0.95  
% 1.18/0.95  fof(f14,plain,(
% 1.18/0.95    ! [X0,X1] : ((r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)) | ~v1_relat_1(X1))),
% 1.18/0.95    inference(ennf_transformation,[],[f6])).
% 1.18/0.95  
% 1.18/0.95  fof(f45,plain,(
% 1.18/0.95    ( ! [X0,X1] : (r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) | ~v1_relat_1(X1)) )),
% 1.18/0.95    inference(cnf_transformation,[],[f14])).
% 1.18/0.95  
% 1.18/0.95  fof(f2,axiom,(
% 1.18/0.95    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.18/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.18/0.95  
% 1.18/0.95  fof(f21,plain,(
% 1.18/0.95    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.18/0.95    inference(nnf_transformation,[],[f2])).
% 1.18/0.95  
% 1.18/0.95  fof(f22,plain,(
% 1.18/0.95    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.18/0.95    inference(flattening,[],[f21])).
% 1.18/0.95  
% 1.18/0.95  fof(f36,plain,(
% 1.18/0.95    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 1.18/0.95    inference(cnf_transformation,[],[f22])).
% 1.18/0.95  
% 1.18/0.95  fof(f49,plain,(
% 1.18/0.95    k5_relat_1(sK4,k6_relat_1(sK3)) != sK4),
% 1.18/0.95    inference(cnf_transformation,[],[f30])).
% 1.18/0.95  
% 1.18/0.95  cnf(c_17,negated_conjecture,
% 1.18/0.95      ( r1_tarski(k2_relat_1(sK4),sK3) ),
% 1.18/0.95      inference(cnf_transformation,[],[f48]) ).
% 1.18/0.95  
% 1.18/0.95  cnf(c_719,plain,
% 1.18/0.95      ( r1_tarski(k2_relat_1(sK4),sK3) = iProver_top ),
% 1.18/0.95      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 1.18/0.95  
% 1.18/0.95  cnf(c_7,plain,
% 1.18/0.95      ( r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
% 1.18/0.95      | r1_tarski(X0,X1)
% 1.18/0.95      | ~ v1_relat_1(X0) ),
% 1.18/0.95      inference(cnf_transformation,[],[f38]) ).
% 1.18/0.95  
% 1.18/0.95  cnf(c_18,negated_conjecture,
% 1.18/0.95      ( v1_relat_1(sK4) ),
% 1.18/0.95      inference(cnf_transformation,[],[f47]) ).
% 1.18/0.95  
% 1.18/0.95  cnf(c_204,plain,
% 1.18/0.95      ( r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
% 1.18/0.95      | r1_tarski(X0,X1)
% 1.18/0.95      | sK4 != X0 ),
% 1.18/0.95      inference(resolution_lifted,[status(thm)],[c_7,c_18]) ).
% 1.18/0.95  
% 1.18/0.95  cnf(c_205,plain,
% 1.18/0.95      ( r2_hidden(k4_tarski(sK1(sK4,X0),sK2(sK4,X0)),sK4)
% 1.18/0.95      | r1_tarski(sK4,X0) ),
% 1.18/0.95      inference(unflattening,[status(thm)],[c_204]) ).
% 1.18/0.95  
% 1.18/0.95  cnf(c_717,plain,
% 1.18/0.95      ( r2_hidden(k4_tarski(sK1(sK4,X0),sK2(sK4,X0)),sK4) = iProver_top
% 1.18/0.95      | r1_tarski(sK4,X0) = iProver_top ),
% 1.18/0.95      inference(predicate_to_equality,[status(thm)],[c_205]) ).
% 1.18/0.95  
% 1.18/0.95  cnf(c_9,plain,
% 1.18/0.95      ( r2_hidden(X0,k2_relat_1(X1))
% 1.18/0.95      | ~ r2_hidden(k4_tarski(X2,X0),X1)
% 1.18/0.95      | ~ v1_relat_1(X1) ),
% 1.18/0.95      inference(cnf_transformation,[],[f41]) ).
% 1.18/0.95  
% 1.18/0.95  cnf(c_260,plain,
% 1.18/0.95      ( r2_hidden(X0,k2_relat_1(X1))
% 1.18/0.95      | ~ r2_hidden(k4_tarski(X2,X0),X1)
% 1.18/0.95      | sK4 != X1 ),
% 1.18/0.95      inference(resolution_lifted,[status(thm)],[c_9,c_18]) ).
% 1.18/0.95  
% 1.18/0.95  cnf(c_261,plain,
% 1.18/0.95      ( r2_hidden(X0,k2_relat_1(sK4))
% 1.18/0.95      | ~ r2_hidden(k4_tarski(X1,X0),sK4) ),
% 1.18/0.95      inference(unflattening,[status(thm)],[c_260]) ).
% 1.18/0.95  
% 1.18/0.95  cnf(c_712,plain,
% 1.18/0.95      ( r2_hidden(X0,k2_relat_1(sK4)) = iProver_top
% 1.18/0.95      | r2_hidden(k4_tarski(X1,X0),sK4) != iProver_top ),
% 1.18/0.95      inference(predicate_to_equality,[status(thm)],[c_261]) ).
% 1.18/0.95  
% 1.18/0.95  cnf(c_1322,plain,
% 1.18/0.95      ( r2_hidden(sK2(sK4,X0),k2_relat_1(sK4)) = iProver_top
% 1.18/0.95      | r1_tarski(sK4,X0) = iProver_top ),
% 1.18/0.95      inference(superposition,[status(thm)],[c_717,c_712]) ).
% 1.18/0.95  
% 1.18/0.95  cnf(c_2,plain,
% 1.18/0.95      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 1.18/0.95      inference(cnf_transformation,[],[f31]) ).
% 1.18/0.95  
% 1.18/0.95  cnf(c_722,plain,
% 1.18/0.95      ( r2_hidden(X0,X1) != iProver_top
% 1.18/0.95      | r2_hidden(X0,X2) = iProver_top
% 1.18/0.95      | r1_tarski(X1,X2) != iProver_top ),
% 1.18/0.95      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 1.18/0.95  
% 1.18/0.95  cnf(c_2241,plain,
% 1.18/0.95      ( r2_hidden(sK2(sK4,X0),X1) = iProver_top
% 1.18/0.95      | r1_tarski(k2_relat_1(sK4),X1) != iProver_top
% 1.18/0.95      | r1_tarski(sK4,X0) = iProver_top ),
% 1.18/0.95      inference(superposition,[status(thm)],[c_1322,c_722]) ).
% 1.18/0.95  
% 1.18/0.95  cnf(c_11,plain,
% 1.18/0.95      ( ~ r2_hidden(X0,X1)
% 1.18/0.95      | ~ r2_hidden(k4_tarski(X2,X0),X3)
% 1.18/0.95      | r2_hidden(k4_tarski(X2,X0),k5_relat_1(X3,k6_relat_1(X1)))
% 1.18/0.95      | ~ v1_relat_1(X3) ),
% 1.18/0.95      inference(cnf_transformation,[],[f44]) ).
% 1.18/0.95  
% 1.18/0.95  cnf(c_284,plain,
% 1.18/0.95      ( ~ r2_hidden(X0,X1)
% 1.18/0.95      | ~ r2_hidden(k4_tarski(X2,X0),X3)
% 1.18/0.95      | r2_hidden(k4_tarski(X2,X0),k5_relat_1(X3,k6_relat_1(X1)))
% 1.18/0.95      | sK4 != X3 ),
% 1.18/0.95      inference(resolution_lifted,[status(thm)],[c_11,c_18]) ).
% 1.18/0.95  
% 1.18/0.95  cnf(c_285,plain,
% 1.18/0.95      ( ~ r2_hidden(X0,X1)
% 1.18/0.95      | r2_hidden(k4_tarski(X2,X0),k5_relat_1(sK4,k6_relat_1(X1)))
% 1.18/0.95      | ~ r2_hidden(k4_tarski(X2,X0),sK4) ),
% 1.18/0.95      inference(unflattening,[status(thm)],[c_284]) ).
% 1.18/0.95  
% 1.18/0.95  cnf(c_710,plain,
% 1.18/0.95      ( r2_hidden(X0,X1) != iProver_top
% 1.18/0.95      | r2_hidden(k4_tarski(X2,X0),k5_relat_1(sK4,k6_relat_1(X1))) = iProver_top
% 1.18/0.95      | r2_hidden(k4_tarski(X2,X0),sK4) != iProver_top ),
% 1.18/0.95      inference(predicate_to_equality,[status(thm)],[c_285]) ).
% 1.18/0.95  
% 1.18/0.95  cnf(c_6,plain,
% 1.18/0.95      ( ~ r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1)
% 1.18/0.95      | r1_tarski(X0,X1)
% 1.18/0.95      | ~ v1_relat_1(X0) ),
% 1.18/0.95      inference(cnf_transformation,[],[f39]) ).
% 1.18/0.95  
% 1.18/0.95  cnf(c_214,plain,
% 1.18/0.95      ( ~ r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1)
% 1.18/0.95      | r1_tarski(X0,X1)
% 1.18/0.95      | sK4 != X0 ),
% 1.18/0.95      inference(resolution_lifted,[status(thm)],[c_6,c_18]) ).
% 1.18/0.95  
% 1.18/0.95  cnf(c_215,plain,
% 1.18/0.95      ( ~ r2_hidden(k4_tarski(sK1(sK4,X0),sK2(sK4,X0)),X0)
% 1.18/0.95      | r1_tarski(sK4,X0) ),
% 1.18/0.95      inference(unflattening,[status(thm)],[c_214]) ).
% 1.18/0.95  
% 1.18/0.95  cnf(c_716,plain,
% 1.18/0.95      ( r2_hidden(k4_tarski(sK1(sK4,X0),sK2(sK4,X0)),X0) != iProver_top
% 1.18/0.95      | r1_tarski(sK4,X0) = iProver_top ),
% 1.18/0.95      inference(predicate_to_equality,[status(thm)],[c_215]) ).
% 1.18/0.95  
% 1.18/0.95  cnf(c_998,plain,
% 1.18/0.95      ( r2_hidden(k4_tarski(sK1(sK4,k5_relat_1(sK4,k6_relat_1(X0))),sK2(sK4,k5_relat_1(sK4,k6_relat_1(X0)))),sK4) != iProver_top
% 1.18/0.95      | r2_hidden(sK2(sK4,k5_relat_1(sK4,k6_relat_1(X0))),X0) != iProver_top
% 1.18/0.95      | r1_tarski(sK4,k5_relat_1(sK4,k6_relat_1(X0))) = iProver_top ),
% 1.18/0.95      inference(superposition,[status(thm)],[c_710,c_716]) ).
% 1.18/0.95  
% 1.18/0.95  cnf(c_1237,plain,
% 1.18/0.95      ( r2_hidden(k4_tarski(sK1(sK4,k5_relat_1(sK4,k6_relat_1(X0))),sK2(sK4,k5_relat_1(sK4,k6_relat_1(X0)))),sK4)
% 1.18/0.95      | r1_tarski(sK4,k5_relat_1(sK4,k6_relat_1(X0))) ),
% 1.18/0.95      inference(instantiation,[status(thm)],[c_205]) ).
% 1.18/0.95  
% 1.18/0.95  cnf(c_1238,plain,
% 1.18/0.95      ( r2_hidden(k4_tarski(sK1(sK4,k5_relat_1(sK4,k6_relat_1(X0))),sK2(sK4,k5_relat_1(sK4,k6_relat_1(X0)))),sK4) = iProver_top
% 1.18/0.95      | r1_tarski(sK4,k5_relat_1(sK4,k6_relat_1(X0))) = iProver_top ),
% 1.18/0.95      inference(predicate_to_equality,[status(thm)],[c_1237]) ).
% 1.18/0.95  
% 1.18/0.95  cnf(c_1453,plain,
% 1.18/0.95      ( r2_hidden(sK2(sK4,k5_relat_1(sK4,k6_relat_1(X0))),X0) != iProver_top
% 1.18/0.95      | r1_tarski(sK4,k5_relat_1(sK4,k6_relat_1(X0))) = iProver_top ),
% 1.18/0.95      inference(global_propositional_subsumption,
% 1.18/0.95                [status(thm)],
% 1.18/0.95                [c_998,c_1238]) ).
% 1.18/0.95  
% 1.18/0.95  cnf(c_2638,plain,
% 1.18/0.95      ( r1_tarski(k2_relat_1(sK4),X0) != iProver_top
% 1.18/0.95      | r1_tarski(sK4,k5_relat_1(sK4,k6_relat_1(X0))) = iProver_top ),
% 1.18/0.95      inference(superposition,[status(thm)],[c_2241,c_1453]) ).
% 1.18/0.95  
% 1.18/0.95  cnf(c_15,plain,
% 1.18/0.95      ( r1_tarski(k5_relat_1(X0,k6_relat_1(X1)),X0) | ~ v1_relat_1(X0) ),
% 1.18/0.95      inference(cnf_transformation,[],[f45]) ).
% 1.18/0.95  
% 1.18/0.95  cnf(c_195,plain,
% 1.18/0.95      ( r1_tarski(k5_relat_1(X0,k6_relat_1(X1)),X0) | sK4 != X0 ),
% 1.18/0.95      inference(resolution_lifted,[status(thm)],[c_15,c_18]) ).
% 1.18/0.95  
% 1.18/0.95  cnf(c_196,plain,
% 1.18/0.95      ( r1_tarski(k5_relat_1(sK4,k6_relat_1(X0)),sK4) ),
% 1.18/0.95      inference(unflattening,[status(thm)],[c_195]) ).
% 1.18/0.95  
% 1.18/0.95  cnf(c_718,plain,
% 1.18/0.95      ( r1_tarski(k5_relat_1(sK4,k6_relat_1(X0)),sK4) = iProver_top ),
% 1.18/0.95      inference(predicate_to_equality,[status(thm)],[c_196]) ).
% 1.18/0.95  
% 1.18/0.95  cnf(c_3,plain,
% 1.18/0.95      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 1.18/0.95      inference(cnf_transformation,[],[f36]) ).
% 1.18/0.95  
% 1.18/0.95  cnf(c_721,plain,
% 1.18/0.95      ( X0 = X1
% 1.18/0.95      | r1_tarski(X1,X0) != iProver_top
% 1.18/0.95      | r1_tarski(X0,X1) != iProver_top ),
% 1.18/0.95      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 1.18/0.95  
% 1.18/0.95  cnf(c_1197,plain,
% 1.18/0.95      ( k5_relat_1(sK4,k6_relat_1(X0)) = sK4
% 1.18/0.95      | r1_tarski(sK4,k5_relat_1(sK4,k6_relat_1(X0))) != iProver_top ),
% 1.18/0.95      inference(superposition,[status(thm)],[c_718,c_721]) ).
% 1.18/0.95  
% 1.18/0.95  cnf(c_2981,plain,
% 1.18/0.95      ( k5_relat_1(sK4,k6_relat_1(X0)) = sK4
% 1.18/0.95      | r1_tarski(k2_relat_1(sK4),X0) != iProver_top ),
% 1.18/0.95      inference(superposition,[status(thm)],[c_2638,c_1197]) ).
% 1.18/0.95  
% 1.18/0.95  cnf(c_3215,plain,
% 1.18/0.95      ( k5_relat_1(sK4,k6_relat_1(sK3)) = sK4 ),
% 1.18/0.95      inference(superposition,[status(thm)],[c_719,c_2981]) ).
% 1.18/0.95  
% 1.18/0.95  cnf(c_16,negated_conjecture,
% 1.18/0.95      ( k5_relat_1(sK4,k6_relat_1(sK3)) != sK4 ),
% 1.18/0.95      inference(cnf_transformation,[],[f49]) ).
% 1.18/0.95  
% 1.18/0.95  cnf(contradiction,plain,
% 1.18/0.95      ( $false ),
% 1.18/0.95      inference(minisat,[status(thm)],[c_3215,c_16]) ).
% 1.18/0.95  
% 1.18/0.95  
% 1.18/0.95  % SZS output end CNFRefutation for theBenchmark.p
% 1.18/0.95  
% 1.18/0.95  ------                               Statistics
% 1.18/0.95  
% 1.18/0.95  ------ General
% 1.18/0.95  
% 1.18/0.95  abstr_ref_over_cycles:                  0
% 1.18/0.95  abstr_ref_under_cycles:                 0
% 1.18/0.95  gc_basic_clause_elim:                   0
% 1.18/0.95  forced_gc_time:                         0
% 1.18/0.95  parsing_time:                           0.013
% 1.18/0.95  unif_index_cands_time:                  0.
% 1.18/0.95  unif_index_add_time:                    0.
% 1.18/0.95  orderings_time:                         0.
% 1.18/0.95  out_proof_time:                         0.01
% 1.18/0.95  total_time:                             0.178
% 1.18/0.95  num_of_symbols:                         44
% 1.18/0.95  num_of_terms:                           2906
% 1.18/0.95  
% 1.18/0.95  ------ Preprocessing
% 1.18/0.95  
% 1.18/0.95  num_of_splits:                          0
% 1.18/0.95  num_of_split_atoms:                     0
% 1.18/0.95  num_of_reused_defs:                     0
% 1.18/0.95  num_eq_ax_congr_red:                    15
% 1.18/0.95  num_of_sem_filtered_clauses:            1
% 1.18/0.95  num_of_subtypes:                        0
% 1.18/0.95  monotx_restored_types:                  0
% 1.18/0.95  sat_num_of_epr_types:                   0
% 1.18/0.95  sat_num_of_non_cyclic_types:            0
% 1.18/0.95  sat_guarded_non_collapsed_types:        0
% 1.18/0.95  num_pure_diseq_elim:                    0
% 1.18/0.95  simp_replaced_by:                       0
% 1.18/0.95  res_preprocessed:                       89
% 1.18/0.95  prep_upred:                             0
% 1.18/0.95  prep_unflattend:                        10
% 1.18/0.95  smt_new_axioms:                         0
% 1.18/0.95  pred_elim_cands:                        2
% 1.18/0.95  pred_elim:                              1
% 1.18/0.95  pred_elim_cl:                           2
% 1.18/0.95  pred_elim_cycles:                       3
% 1.18/0.95  merged_defs:                            0
% 1.18/0.95  merged_defs_ncl:                        0
% 1.18/0.95  bin_hyper_res:                          0
% 1.18/0.95  prep_cycles:                            4
% 1.18/0.95  pred_elim_time:                         0.004
% 1.18/0.95  splitting_time:                         0.
% 1.18/0.95  sem_filter_time:                        0.
% 1.18/0.95  monotx_time:                            0.001
% 1.18/0.95  subtype_inf_time:                       0.
% 1.18/0.95  
% 1.18/0.95  ------ Problem properties
% 1.18/0.95  
% 1.18/0.95  clauses:                                16
% 1.18/0.95  conjectures:                            2
% 1.18/0.95  epr:                                    3
% 1.18/0.95  horn:                                   14
% 1.18/0.95  ground:                                 2
% 1.18/0.95  unary:                                  5
% 1.18/0.95  binary:                                 8
% 1.18/0.95  lits:                                   30
% 1.18/0.95  lits_eq:                                2
% 1.18/0.95  fd_pure:                                0
% 1.18/0.95  fd_pseudo:                              0
% 1.18/0.95  fd_cond:                                0
% 1.18/0.95  fd_pseudo_cond:                         1
% 1.18/0.95  ac_symbols:                             0
% 1.18/0.95  
% 1.18/0.95  ------ Propositional Solver
% 1.18/0.95  
% 1.18/0.95  prop_solver_calls:                      28
% 1.18/0.95  prop_fast_solver_calls:                 512
% 1.18/0.95  smt_solver_calls:                       0
% 1.18/0.95  smt_fast_solver_calls:                  0
% 1.18/0.95  prop_num_of_clauses:                    1108
% 1.18/0.95  prop_preprocess_simplified:             4419
% 1.18/0.95  prop_fo_subsumed:                       1
% 1.18/0.95  prop_solver_time:                       0.
% 1.18/0.95  smt_solver_time:                        0.
% 1.18/0.95  smt_fast_solver_time:                   0.
% 1.18/0.95  prop_fast_solver_time:                  0.
% 1.18/0.95  prop_unsat_core_time:                   0.
% 1.18/0.95  
% 1.18/0.95  ------ QBF
% 1.18/0.95  
% 1.18/0.95  qbf_q_res:                              0
% 1.18/0.95  qbf_num_tautologies:                    0
% 1.18/0.95  qbf_prep_cycles:                        0
% 1.18/0.95  
% 1.18/0.95  ------ BMC1
% 1.18/0.95  
% 1.18/0.95  bmc1_current_bound:                     -1
% 1.18/0.95  bmc1_last_solved_bound:                 -1
% 1.18/0.95  bmc1_unsat_core_size:                   -1
% 1.18/0.95  bmc1_unsat_core_parents_size:           -1
% 1.18/0.95  bmc1_merge_next_fun:                    0
% 1.18/0.95  bmc1_unsat_core_clauses_time:           0.
% 1.18/0.95  
% 1.18/0.95  ------ Instantiation
% 1.18/0.95  
% 1.18/0.95  inst_num_of_clauses:                    391
% 1.18/0.95  inst_num_in_passive:                    57
% 1.18/0.95  inst_num_in_active:                     193
% 1.18/0.95  inst_num_in_unprocessed:                141
% 1.18/0.95  inst_num_of_loops:                      230
% 1.18/0.95  inst_num_of_learning_restarts:          0
% 1.18/0.95  inst_num_moves_active_passive:          34
% 1.18/0.95  inst_lit_activity:                      0
% 1.18/0.95  inst_lit_activity_moves:                0
% 1.18/0.95  inst_num_tautologies:                   0
% 1.18/0.95  inst_num_prop_implied:                  0
% 1.18/0.95  inst_num_existing_simplified:           0
% 1.18/0.95  inst_num_eq_res_simplified:             0
% 1.18/0.95  inst_num_child_elim:                    0
% 1.18/0.95  inst_num_of_dismatching_blockings:      68
% 1.18/0.95  inst_num_of_non_proper_insts:           319
% 1.18/0.95  inst_num_of_duplicates:                 0
% 1.18/0.95  inst_inst_num_from_inst_to_res:         0
% 1.18/0.95  inst_dismatching_checking_time:         0.
% 1.18/0.95  
% 1.18/0.95  ------ Resolution
% 1.18/0.95  
% 1.18/0.95  res_num_of_clauses:                     0
% 1.18/0.95  res_num_in_passive:                     0
% 1.18/0.95  res_num_in_active:                      0
% 1.18/0.95  res_num_of_loops:                       93
% 1.18/0.95  res_forward_subset_subsumed:            41
% 1.18/0.95  res_backward_subset_subsumed:           0
% 1.18/0.95  res_forward_subsumed:                   1
% 1.18/0.95  res_backward_subsumed:                  0
% 1.18/0.95  res_forward_subsumption_resolution:     0
% 1.18/0.95  res_backward_subsumption_resolution:    0
% 1.18/0.95  res_clause_to_clause_subsumption:       458
% 1.18/0.95  res_orphan_elimination:                 0
% 1.18/0.95  res_tautology_del:                      28
% 1.18/0.95  res_num_eq_res_simplified:              0
% 1.18/0.95  res_num_sel_changes:                    0
% 1.18/0.95  res_moves_from_active_to_pass:          0
% 1.18/0.95  
% 1.18/0.95  ------ Superposition
% 1.18/0.95  
% 1.18/0.95  sup_time_total:                         0.
% 1.18/0.95  sup_time_generating:                    0.
% 1.18/0.95  sup_time_sim_full:                      0.
% 1.18/0.95  sup_time_sim_immed:                     0.
% 1.18/0.95  
% 1.18/0.95  sup_num_of_clauses:                     58
% 1.18/0.95  sup_num_in_active:                      44
% 1.18/0.95  sup_num_in_passive:                     14
% 1.18/0.95  sup_num_of_loops:                       44
% 1.18/0.95  sup_fw_superposition:                   30
% 1.18/0.95  sup_bw_superposition:                   56
% 1.18/0.95  sup_immediate_simplified:               19
% 1.18/0.95  sup_given_eliminated:                   1
% 1.18/0.95  comparisons_done:                       0
% 1.18/0.95  comparisons_avoided:                    0
% 1.18/0.95  
% 1.18/0.95  ------ Simplifications
% 1.18/0.95  
% 1.18/0.95  
% 1.18/0.95  sim_fw_subset_subsumed:                 7
% 1.18/0.95  sim_bw_subset_subsumed:                 0
% 1.18/0.95  sim_fw_subsumed:                        8
% 1.18/0.95  sim_bw_subsumed:                        0
% 1.18/0.95  sim_fw_subsumption_res:                 0
% 1.18/0.95  sim_bw_subsumption_res:                 0
% 1.18/0.95  sim_tautology_del:                      7
% 1.18/0.95  sim_eq_tautology_del:                   2
% 1.18/0.95  sim_eq_res_simp:                        0
% 1.18/0.95  sim_fw_demodulated:                     0
% 1.18/0.95  sim_bw_demodulated:                     3
% 1.18/0.95  sim_light_normalised:                   4
% 1.18/0.95  sim_joinable_taut:                      0
% 1.18/0.95  sim_joinable_simp:                      0
% 1.18/0.95  sim_ac_normalised:                      0
% 1.18/0.95  sim_smt_subsumption:                    0
% 1.18/0.95  
%------------------------------------------------------------------------------
