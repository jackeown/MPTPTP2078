%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0573+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:38 EST 2020

% Result     : Theorem 3.80s
% Output     : CNFRefutation 3.80s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 162 expanded)
%              Number of clauses        :   34 (  41 expanded)
%              Number of leaves         :   11 (  41 expanded)
%              Depth                    :   13
%              Number of atoms          :  316 ( 793 expanded)
%              Number of equality atoms :   35 (  83 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal clause size      :   15 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f19])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f20])).

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(sK4(X0,X1,X2),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f22])).

fof(f36,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f46,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k6_subset_1(X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f36,f40])).

fof(f52,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k6_subset_1(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X3,X4),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) ) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X5] :
                      ( r2_hidden(X5,X1)
                      & r2_hidden(k4_tarski(X3,X5),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X6,X7),X0) ) )
                & ( ? [X8] :
                      ( r2_hidden(X8,X1)
                      & r2_hidden(k4_tarski(X6,X8),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f11])).

fof(f15,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r2_hidden(k4_tarski(X6,X8),X0) )
     => ( r2_hidden(sK2(X0,X1,X6),X1)
        & r2_hidden(k4_tarski(X6,sK2(X0,X1,X6)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r2_hidden(k4_tarski(X3,X5),X0) )
     => ( r2_hidden(sK1(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X3,sK1(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(X4,X1)
                | ~ r2_hidden(k4_tarski(X3,X4),X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( r2_hidden(X5,X1)
                & r2_hidden(k4_tarski(X3,X5),X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( ~ r2_hidden(X4,X1)
              | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),X4),X0) )
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r2_hidden(X5,X1)
              & r2_hidden(k4_tarski(sK0(X0,X1,X2),X5),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),X4),X0) )
                | ~ r2_hidden(sK0(X0,X1,X2),X2) )
              & ( ( r2_hidden(sK1(X0,X1,X2),X1)
                  & r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X0) )
                | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X6,X7),X0) ) )
                & ( ( r2_hidden(sK2(X0,X1,X6),X1)
                    & r2_hidden(k4_tarski(X6,sK2(X0,X1,X6)),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f15,f14,f13])).

fof(f28,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X6,X7),X0)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f49,plain,(
    ! [X6,X0,X7,X1] :
      ( r2_hidden(X6,k10_relat_1(X0,X1))
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X6,X7),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f28])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)),k10_relat_1(X2,k6_subset_1(X0,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => r1_tarski(k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)),k10_relat_1(X2,k6_subset_1(X0,X1))) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)),k10_relat_1(X2,k6_subset_1(X0,X1)))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f24,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)),k10_relat_1(X2,k6_subset_1(X0,X1)))
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k6_subset_1(k10_relat_1(sK7,sK5),k10_relat_1(sK7,sK6)),k10_relat_1(sK7,k6_subset_1(sK5,sK6)))
      & v1_relat_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ~ r1_tarski(k6_subset_1(k10_relat_1(sK7,sK5),k10_relat_1(sK7,sK6)),k10_relat_1(sK7,k6_subset_1(sK5,sK6)))
    & v1_relat_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f10,f24])).

fof(f41,plain,(
    v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f25])).

fof(f27,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f50,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X6),X1)
      | ~ r2_hidden(X6,k10_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f27])).

fof(f26,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(k4_tarski(X6,sK2(X0,X1,X6)),X0)
      | ~ r2_hidden(X6,X2)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f51,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k4_tarski(X6,sK2(X0,X1,X6)),X0)
      | ~ r2_hidden(X6,k10_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f26])).

fof(f34,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f48,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k6_subset_1(X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f34,f40])).

fof(f54,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k6_subset_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f48])).

fof(f35,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f47,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k6_subset_1(X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f35,f40])).

fof(f53,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k6_subset_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f47])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f17,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f9,f17])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f42,plain,(
    ~ r1_tarski(k6_subset_1(k10_relat_1(sK7,sK5),k10_relat_1(sK7,sK6)),k10_relat_1(sK7,k6_subset_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f25])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k6_subset_1(X1,X2)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_880,plain,
    ( r2_hidden(sK2(sK7,sK5,sK3(k6_subset_1(k10_relat_1(sK7,sK5),k10_relat_1(sK7,sK6)),k10_relat_1(sK7,k6_subset_1(sK5,sK6)))),X0)
    | r2_hidden(sK2(sK7,sK5,sK3(k6_subset_1(k10_relat_1(sK7,sK5),k10_relat_1(sK7,sK6)),k10_relat_1(sK7,k6_subset_1(sK5,sK6)))),k6_subset_1(sK5,X0))
    | ~ r2_hidden(sK2(sK7,sK5,sK3(k6_subset_1(k10_relat_1(sK7,sK5),k10_relat_1(sK7,sK6)),k10_relat_1(sK7,k6_subset_1(sK5,sK6)))),sK5) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_7329,plain,
    ( r2_hidden(sK2(sK7,sK5,sK3(k6_subset_1(k10_relat_1(sK7,sK5),k10_relat_1(sK7,sK6)),k10_relat_1(sK7,k6_subset_1(sK5,sK6)))),k6_subset_1(sK5,sK6))
    | r2_hidden(sK2(sK7,sK5,sK3(k6_subset_1(k10_relat_1(sK7,sK5),k10_relat_1(sK7,sK6)),k10_relat_1(sK7,k6_subset_1(sK5,sK6)))),sK6)
    | ~ r2_hidden(sK2(sK7,sK5,sK3(k6_subset_1(k10_relat_1(sK7,sK5),k10_relat_1(sK7,sK6)),k10_relat_1(sK7,k6_subset_1(sK5,sK6)))),sK5) ),
    inference(instantiation,[status(thm)],[c_880])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(X3,X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X3)
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_15,negated_conjecture,
    ( v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_245,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(X3,X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X3)
    | sK7 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_15])).

cnf(c_246,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k10_relat_1(sK7,X1))
    | ~ r2_hidden(k4_tarski(X2,X0),sK7) ),
    inference(unflattening,[status(thm)],[c_245])).

cnf(c_1149,plain,
    ( r2_hidden(X0,k10_relat_1(sK7,X1))
    | ~ r2_hidden(sK2(sK7,sK5,sK3(k6_subset_1(k10_relat_1(sK7,sK5),k10_relat_1(sK7,sK6)),k10_relat_1(sK7,k6_subset_1(sK5,sK6)))),X1)
    | ~ r2_hidden(k4_tarski(X0,sK2(sK7,sK5,sK3(k6_subset_1(k10_relat_1(sK7,sK5),k10_relat_1(sK7,sK6)),k10_relat_1(sK7,k6_subset_1(sK5,sK6))))),sK7) ),
    inference(instantiation,[status(thm)],[c_246])).

cnf(c_2785,plain,
    ( ~ r2_hidden(sK2(sK7,sK5,sK3(k6_subset_1(k10_relat_1(sK7,sK5),k10_relat_1(sK7,sK6)),k10_relat_1(sK7,k6_subset_1(sK5,sK6)))),X0)
    | r2_hidden(sK3(k6_subset_1(k10_relat_1(sK7,sK5),k10_relat_1(sK7,sK6)),k10_relat_1(sK7,k6_subset_1(sK5,sK6))),k10_relat_1(sK7,X0))
    | ~ r2_hidden(k4_tarski(sK3(k6_subset_1(k10_relat_1(sK7,sK5),k10_relat_1(sK7,sK6)),k10_relat_1(sK7,k6_subset_1(sK5,sK6))),sK2(sK7,sK5,sK3(k6_subset_1(k10_relat_1(sK7,sK5),k10_relat_1(sK7,sK6)),k10_relat_1(sK7,k6_subset_1(sK5,sK6))))),sK7) ),
    inference(instantiation,[status(thm)],[c_1149])).

cnf(c_4031,plain,
    ( ~ r2_hidden(sK2(sK7,sK5,sK3(k6_subset_1(k10_relat_1(sK7,sK5),k10_relat_1(sK7,sK6)),k10_relat_1(sK7,k6_subset_1(sK5,sK6)))),sK6)
    | r2_hidden(sK3(k6_subset_1(k10_relat_1(sK7,sK5),k10_relat_1(sK7,sK6)),k10_relat_1(sK7,k6_subset_1(sK5,sK6))),k10_relat_1(sK7,sK6))
    | ~ r2_hidden(k4_tarski(sK3(k6_subset_1(k10_relat_1(sK7,sK5),k10_relat_1(sK7,sK6)),k10_relat_1(sK7,k6_subset_1(sK5,sK6))),sK2(sK7,sK5,sK3(k6_subset_1(k10_relat_1(sK7,sK5),k10_relat_1(sK7,sK6)),k10_relat_1(sK7,k6_subset_1(sK5,sK6))))),sK7) ),
    inference(instantiation,[status(thm)],[c_2785])).

cnf(c_710,plain,
    ( ~ r2_hidden(X0,k6_subset_1(X1,X2))
    | r2_hidden(X3,k10_relat_1(sK7,k6_subset_1(X1,X2)))
    | ~ r2_hidden(k4_tarski(X3,X0),sK7) ),
    inference(instantiation,[status(thm)],[c_246])).

cnf(c_860,plain,
    ( ~ r2_hidden(sK2(sK7,sK5,sK3(k6_subset_1(k10_relat_1(sK7,sK5),k10_relat_1(sK7,sK6)),k10_relat_1(sK7,k6_subset_1(sK5,sK6)))),k6_subset_1(X0,X1))
    | r2_hidden(sK3(k6_subset_1(k10_relat_1(sK7,sK5),k10_relat_1(sK7,sK6)),k10_relat_1(sK7,k6_subset_1(sK5,sK6))),k10_relat_1(sK7,k6_subset_1(X0,X1)))
    | ~ r2_hidden(k4_tarski(sK3(k6_subset_1(k10_relat_1(sK7,sK5),k10_relat_1(sK7,sK6)),k10_relat_1(sK7,k6_subset_1(sK5,sK6))),sK2(sK7,sK5,sK3(k6_subset_1(k10_relat_1(sK7,sK5),k10_relat_1(sK7,sK6)),k10_relat_1(sK7,k6_subset_1(sK5,sK6))))),sK7) ),
    inference(instantiation,[status(thm)],[c_710])).

cnf(c_2451,plain,
    ( ~ r2_hidden(sK2(sK7,sK5,sK3(k6_subset_1(k10_relat_1(sK7,sK5),k10_relat_1(sK7,sK6)),k10_relat_1(sK7,k6_subset_1(sK5,sK6)))),k6_subset_1(sK5,sK6))
    | r2_hidden(sK3(k6_subset_1(k10_relat_1(sK7,sK5),k10_relat_1(sK7,sK6)),k10_relat_1(sK7,k6_subset_1(sK5,sK6))),k10_relat_1(sK7,k6_subset_1(sK5,sK6)))
    | ~ r2_hidden(k4_tarski(sK3(k6_subset_1(k10_relat_1(sK7,sK5),k10_relat_1(sK7,sK6)),k10_relat_1(sK7,k6_subset_1(sK5,sK6))),sK2(sK7,sK5,sK3(k6_subset_1(k10_relat_1(sK7,sK5),k10_relat_1(sK7,sK6)),k10_relat_1(sK7,k6_subset_1(sK5,sK6))))),sK7) ),
    inference(instantiation,[status(thm)],[c_860])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK2(X1,X2,X0),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_272,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(sK2(X1,X2,X0),X2)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_15])).

cnf(c_273,plain,
    ( ~ r2_hidden(X0,k10_relat_1(sK7,X1))
    | r2_hidden(sK2(sK7,X1,X0),X1) ),
    inference(unflattening,[status(thm)],[c_272])).

cnf(c_788,plain,
    ( r2_hidden(sK2(sK7,sK5,sK3(k6_subset_1(k10_relat_1(sK7,sK5),k10_relat_1(sK7,sK6)),k10_relat_1(sK7,k6_subset_1(sK5,sK6)))),sK5)
    | ~ r2_hidden(sK3(k6_subset_1(k10_relat_1(sK7,sK5),k10_relat_1(sK7,sK6)),k10_relat_1(sK7,k6_subset_1(sK5,sK6))),k10_relat_1(sK7,sK5)) ),
    inference(instantiation,[status(thm)],[c_273])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(k4_tarski(X0,sK2(X1,X2,X0)),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_260,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(k4_tarski(X0,sK2(X1,X2,X0)),X1)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_15])).

cnf(c_261,plain,
    ( ~ r2_hidden(X0,k10_relat_1(sK7,X1))
    | r2_hidden(k4_tarski(X0,sK2(sK7,X1,X0)),sK7) ),
    inference(unflattening,[status(thm)],[c_260])).

cnf(c_789,plain,
    ( ~ r2_hidden(sK3(k6_subset_1(k10_relat_1(sK7,sK5),k10_relat_1(sK7,sK6)),k10_relat_1(sK7,k6_subset_1(sK5,sK6))),k10_relat_1(sK7,sK5))
    | r2_hidden(k4_tarski(sK3(k6_subset_1(k10_relat_1(sK7,sK5),k10_relat_1(sK7,sK6)),k10_relat_1(sK7,k6_subset_1(sK5,sK6))),sK2(sK7,sK5,sK3(k6_subset_1(k10_relat_1(sK7,sK5),k10_relat_1(sK7,sK6)),k10_relat_1(sK7,k6_subset_1(sK5,sK6))))),sK7) ),
    inference(instantiation,[status(thm)],[c_261])).

cnf(c_13,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k6_subset_1(X1,X2)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_691,plain,
    ( ~ r2_hidden(X0,k6_subset_1(k10_relat_1(sK7,X1),X2))
    | r2_hidden(X0,k10_relat_1(sK7,X1)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_745,plain,
    ( ~ r2_hidden(sK3(k6_subset_1(k10_relat_1(sK7,sK5),k10_relat_1(sK7,sK6)),k10_relat_1(sK7,k6_subset_1(sK5,sK6))),k6_subset_1(k10_relat_1(sK7,sK5),k10_relat_1(sK7,sK6)))
    | r2_hidden(sK3(k6_subset_1(k10_relat_1(sK7,sK5),k10_relat_1(sK7,sK6)),k10_relat_1(sK7,k6_subset_1(sK5,sK6))),k10_relat_1(sK7,sK5)) ),
    inference(instantiation,[status(thm)],[c_691])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k6_subset_1(X2,X1)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_678,plain,
    ( ~ r2_hidden(sK3(k6_subset_1(k10_relat_1(sK7,sK5),k10_relat_1(sK7,sK6)),k10_relat_1(sK7,k6_subset_1(sK5,sK6))),k6_subset_1(k10_relat_1(sK7,sK5),k10_relat_1(sK7,sK6)))
    | ~ r2_hidden(sK3(k6_subset_1(k10_relat_1(sK7,sK5),k10_relat_1(sK7,sK6)),k10_relat_1(sK7,k6_subset_1(sK5,sK6))),k10_relat_1(sK7,sK6)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_6,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(sK3(X0,X1),X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_14,negated_conjecture,
    ( ~ r1_tarski(k6_subset_1(k10_relat_1(sK7,sK5),k10_relat_1(sK7,sK6)),k10_relat_1(sK7,k6_subset_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_186,plain,
    ( ~ r2_hidden(sK3(X0,X1),X1)
    | k6_subset_1(k10_relat_1(sK7,sK5),k10_relat_1(sK7,sK6)) != X0
    | k10_relat_1(sK7,k6_subset_1(sK5,sK6)) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_14])).

cnf(c_187,plain,
    ( ~ r2_hidden(sK3(k6_subset_1(k10_relat_1(sK7,sK5),k10_relat_1(sK7,sK6)),k10_relat_1(sK7,k6_subset_1(sK5,sK6))),k10_relat_1(sK7,k6_subset_1(sK5,sK6))) ),
    inference(unflattening,[status(thm)],[c_186])).

cnf(c_7,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK3(X0,X1),X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_179,plain,
    ( r2_hidden(sK3(X0,X1),X0)
    | k6_subset_1(k10_relat_1(sK7,sK5),k10_relat_1(sK7,sK6)) != X0
    | k10_relat_1(sK7,k6_subset_1(sK5,sK6)) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_14])).

cnf(c_180,plain,
    ( r2_hidden(sK3(k6_subset_1(k10_relat_1(sK7,sK5),k10_relat_1(sK7,sK6)),k10_relat_1(sK7,k6_subset_1(sK5,sK6))),k6_subset_1(k10_relat_1(sK7,sK5),k10_relat_1(sK7,sK6))) ),
    inference(unflattening,[status(thm)],[c_179])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7329,c_4031,c_2451,c_788,c_789,c_745,c_678,c_187,c_180])).


%------------------------------------------------------------------------------
