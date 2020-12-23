%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0445+1.001 : TPTP v7.4.0. Released v7.4.0.
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

% Result     : Theorem 2.69s
% Output     : CNFRefutation 2.69s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 130 expanded)
%              Number of clauses        :   24 (  31 expanded)
%              Number of leaves         :   11 (  33 expanded)
%              Depth                    :   12
%              Number of atoms          :  234 ( 547 expanded)
%              Number of equality atoms :   34 (  73 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
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

fof(f34,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f43,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k6_subset_1(X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f34,f38])).

fof(f48,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k6_subset_1(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f43])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f14,plain,(
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
    inference(rectify,[],[f13])).

fof(f17,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK3(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
     => r2_hidden(k4_tarski(sK2(X0,X1),X2),X0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK1(X0,X1)),X0)
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK1(X0,X1)),X0)
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK1(X0,X1)),X0)
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0)
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK3(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f14,f17,f16,f15])).

fof(f29,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X6,X5),X0)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f46,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k2_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X6,X5),X0) ) ),
    inference(equality_resolution,[],[f29])).

fof(f1,axiom,(
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
    inference(unused_predicate_definition_removal,[],[f1])).

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

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f5,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f8,plain,(
    ~ ! [X0,X1] : r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f10,plain,(
    ? [X0,X1] : ~ r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) ),
    inference(ennf_transformation,[],[f8])).

fof(f24,plain,
    ( ? [X0,X1] : ~ r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1)))
   => ~ r1_tarski(k6_subset_1(k2_relat_1(sK5),k2_relat_1(sK6)),k2_relat_1(k6_subset_1(sK5,sK6))) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ~ r1_tarski(k6_subset_1(k2_relat_1(sK5),k2_relat_1(sK6)),k2_relat_1(k6_subset_1(sK5,sK6))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f10,f24])).

fof(f39,plain,(
    ~ r1_tarski(k6_subset_1(k2_relat_1(sK5),k2_relat_1(sK6)),k2_relat_1(k6_subset_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f25])).

fof(f33,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f44,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k6_subset_1(X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f33,f38])).

fof(f49,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k6_subset_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f44])).

fof(f28,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK3(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f47,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK3(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f28])).

fof(f32,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f45,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k6_subset_1(X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f32,f38])).

fof(f50,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k6_subset_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f45])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f12])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k6_subset_1(X1,X2)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_682,plain,
    ( r2_hidden(k4_tarski(sK3(sK5,sK0(k6_subset_1(k2_relat_1(sK5),k2_relat_1(sK6)),k2_relat_1(k6_subset_1(sK5,sK6)))),sK0(k6_subset_1(k2_relat_1(sK5),k2_relat_1(sK6)),k2_relat_1(k6_subset_1(sK5,sK6)))),X0)
    | r2_hidden(k4_tarski(sK3(sK5,sK0(k6_subset_1(k2_relat_1(sK5),k2_relat_1(sK6)),k2_relat_1(k6_subset_1(sK5,sK6)))),sK0(k6_subset_1(k2_relat_1(sK5),k2_relat_1(sK6)),k2_relat_1(k6_subset_1(sK5,sK6)))),k6_subset_1(sK5,X0))
    | ~ r2_hidden(k4_tarski(sK3(sK5,sK0(k6_subset_1(k2_relat_1(sK5),k2_relat_1(sK6)),k2_relat_1(k6_subset_1(sK5,sK6)))),sK0(k6_subset_1(k2_relat_1(sK5),k2_relat_1(sK6)),k2_relat_1(k6_subset_1(sK5,sK6)))),sK5) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_3634,plain,
    ( r2_hidden(k4_tarski(sK3(sK5,sK0(k6_subset_1(k2_relat_1(sK5),k2_relat_1(sK6)),k2_relat_1(k6_subset_1(sK5,sK6)))),sK0(k6_subset_1(k2_relat_1(sK5),k2_relat_1(sK6)),k2_relat_1(k6_subset_1(sK5,sK6)))),k6_subset_1(sK5,sK6))
    | r2_hidden(k4_tarski(sK3(sK5,sK0(k6_subset_1(k2_relat_1(sK5),k2_relat_1(sK6)),k2_relat_1(k6_subset_1(sK5,sK6)))),sK0(k6_subset_1(k2_relat_1(sK5),k2_relat_1(sK6)),k2_relat_1(k6_subset_1(sK5,sK6)))),sK6)
    | ~ r2_hidden(k4_tarski(sK3(sK5,sK0(k6_subset_1(k2_relat_1(sK5),k2_relat_1(sK6)),k2_relat_1(k6_subset_1(sK5,sK6)))),sK0(k6_subset_1(k2_relat_1(sK5),k2_relat_1(sK6)),k2_relat_1(k6_subset_1(sK5,sK6)))),sK5) ),
    inference(instantiation,[status(thm)],[c_682])).

cnf(c_4,plain,
    ( r2_hidden(X0,k2_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_971,plain,
    ( ~ r2_hidden(k4_tarski(sK3(sK5,sK0(k6_subset_1(k2_relat_1(sK5),k2_relat_1(sK6)),k2_relat_1(k6_subset_1(sK5,sK6)))),sK0(k6_subset_1(k2_relat_1(sK5),k2_relat_1(sK6)),k2_relat_1(k6_subset_1(sK5,sK6)))),X0)
    | r2_hidden(sK0(k6_subset_1(k2_relat_1(sK5),k2_relat_1(sK6)),k2_relat_1(k6_subset_1(sK5,sK6))),k2_relat_1(X0)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1687,plain,
    ( ~ r2_hidden(k4_tarski(sK3(sK5,sK0(k6_subset_1(k2_relat_1(sK5),k2_relat_1(sK6)),k2_relat_1(k6_subset_1(sK5,sK6)))),sK0(k6_subset_1(k2_relat_1(sK5),k2_relat_1(sK6)),k2_relat_1(k6_subset_1(sK5,sK6)))),sK6)
    | r2_hidden(sK0(k6_subset_1(k2_relat_1(sK5),k2_relat_1(sK6)),k2_relat_1(k6_subset_1(sK5,sK6))),k2_relat_1(sK6)) ),
    inference(instantiation,[status(thm)],[c_971])).

cnf(c_1682,plain,
    ( ~ r2_hidden(k4_tarski(sK3(sK5,sK0(k6_subset_1(k2_relat_1(sK5),k2_relat_1(sK6)),k2_relat_1(k6_subset_1(sK5,sK6)))),sK0(k6_subset_1(k2_relat_1(sK5),k2_relat_1(sK6)),k2_relat_1(k6_subset_1(sK5,sK6)))),k6_subset_1(sK5,sK6))
    | r2_hidden(sK0(k6_subset_1(k2_relat_1(sK5),k2_relat_1(sK6)),k2_relat_1(k6_subset_1(sK5,sK6))),k2_relat_1(k6_subset_1(sK5,sK6))) ),
    inference(instantiation,[status(thm)],[c_971])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_12,negated_conjecture,
    ( ~ r1_tarski(k6_subset_1(k2_relat_1(sK5),k2_relat_1(sK6)),k2_relat_1(k6_subset_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_149,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | k6_subset_1(k2_relat_1(sK5),k2_relat_1(sK6)) != X0
    | k2_relat_1(k6_subset_1(sK5,sK6)) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_12])).

cnf(c_150,plain,
    ( r2_hidden(sK0(k6_subset_1(k2_relat_1(sK5),k2_relat_1(sK6)),k2_relat_1(k6_subset_1(sK5,sK6))),k6_subset_1(k2_relat_1(sK5),k2_relat_1(sK6))) ),
    inference(unflattening,[status(thm)],[c_149])).

cnf(c_456,plain,
    ( r2_hidden(sK0(k6_subset_1(k2_relat_1(sK5),k2_relat_1(sK6)),k2_relat_1(k6_subset_1(sK5,sK6))),k6_subset_1(k2_relat_1(sK5),k2_relat_1(sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_150])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k6_subset_1(X2,X1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_458,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k6_subset_1(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_737,plain,
    ( r2_hidden(sK0(k6_subset_1(k2_relat_1(sK5),k2_relat_1(sK6)),k2_relat_1(k6_subset_1(sK5,sK6))),k2_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_456,c_458])).

cnf(c_738,plain,
    ( ~ r2_hidden(sK0(k6_subset_1(k2_relat_1(sK5),k2_relat_1(sK6)),k2_relat_1(k6_subset_1(sK5,sK6))),k2_relat_1(sK6)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_737])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(k4_tarski(sK3(X1,X0),X0),X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_579,plain,
    ( r2_hidden(k4_tarski(sK3(sK5,sK0(k6_subset_1(k2_relat_1(sK5),k2_relat_1(sK6)),k2_relat_1(k6_subset_1(sK5,sK6)))),sK0(k6_subset_1(k2_relat_1(sK5),k2_relat_1(sK6)),k2_relat_1(k6_subset_1(sK5,sK6)))),sK5)
    | ~ r2_hidden(sK0(k6_subset_1(k2_relat_1(sK5),k2_relat_1(sK6)),k2_relat_1(k6_subset_1(sK5,sK6))),k2_relat_1(sK5)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_11,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k6_subset_1(X1,X2)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_555,plain,
    ( ~ r2_hidden(sK0(k6_subset_1(k2_relat_1(sK5),k2_relat_1(sK6)),k2_relat_1(k6_subset_1(sK5,sK6))),k6_subset_1(k2_relat_1(sK5),k2_relat_1(sK6)))
    | r2_hidden(sK0(k6_subset_1(k2_relat_1(sK5),k2_relat_1(sK6)),k2_relat_1(k6_subset_1(sK5,sK6))),k2_relat_1(sK5)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_156,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | k6_subset_1(k2_relat_1(sK5),k2_relat_1(sK6)) != X0
    | k2_relat_1(k6_subset_1(sK5,sK6)) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_12])).

cnf(c_157,plain,
    ( ~ r2_hidden(sK0(k6_subset_1(k2_relat_1(sK5),k2_relat_1(sK6)),k2_relat_1(k6_subset_1(sK5,sK6))),k2_relat_1(k6_subset_1(sK5,sK6))) ),
    inference(unflattening,[status(thm)],[c_156])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3634,c_1687,c_1682,c_738,c_579,c_555,c_157,c_150])).


%------------------------------------------------------------------------------
