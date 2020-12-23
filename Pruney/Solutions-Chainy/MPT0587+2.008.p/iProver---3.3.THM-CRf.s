%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:48:02 EST 2020

% Result     : Theorem 3.60s
% Output     : CNFRefutation 3.60s
% Verified   : 
% Statistics : Number of formulae       :   64 (  86 expanded)
%              Number of clauses        :   24 (  24 expanded)
%              Number of leaves         :   13 (  21 expanded)
%              Depth                    :   11
%              Number of atoms          :  227 ( 293 expanded)
%              Number of equality atoms :   52 (  70 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f15,plain,(
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
    inference(rectify,[],[f14])).

fof(f16,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).

fof(f25,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f42,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f36,f34])).

fof(f43,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))) ),
    inference(definition_unfolding,[],[f33,f42])).

fof(f49,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))) != X2 ) ),
    inference(definition_unfolding,[],[f25,f43])).

fof(f53,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1)))) ) ),
    inference(equality_resolution,[],[f49])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f50,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))) = k6_subset_1(X0,X1) ),
    inference(definition_unfolding,[],[f35,f43])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f18,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK1(X0,X1),X1)
          | ~ r2_hidden(sK1(X0,X1),X0) )
        & ( r2_hidden(sK1(X0,X1),X1)
          | r2_hidden(sK1(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK1(X0,X1),X1)
          | ~ r2_hidden(sK1(X0,X1),X0) )
        & ( r2_hidden(sK1(X0,X1),X1)
          | r2_hidden(sK1(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f18,f19])).

fof(f32,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r2_hidden(sK1(X0,X1),X1)
      | ~ r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f31,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK1(X0,X1),X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0))) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f12,plain,(
    ? [X0,X1] :
      ( k6_subset_1(k1_relat_1(X1),X0) != k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0)))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f23,plain,
    ( ? [X0,X1] :
        ( k6_subset_1(k1_relat_1(X1),X0) != k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0)))
        & v1_relat_1(X1) )
   => ( k6_subset_1(k1_relat_1(sK3),sK2) != k1_relat_1(k7_relat_1(sK3,k6_subset_1(k1_relat_1(sK3),sK2)))
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( k6_subset_1(k1_relat_1(sK3),sK2) != k1_relat_1(k7_relat_1(sK3,k6_subset_1(k1_relat_1(sK3),sK2)))
    & v1_relat_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f12,f23])).

fof(f41,plain,(
    k6_subset_1(k1_relat_1(sK3),sK2) != k1_relat_1(k7_relat_1(sK3,k6_subset_1(k1_relat_1(sK3),sK2))) ),
    inference(cnf_transformation,[],[f24])).

fof(f40,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_relat_1(X2))
    | r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_656,plain,
    ( ~ r2_hidden(sK1(k1_relat_1(k7_relat_1(sK3,k6_subset_1(k1_relat_1(sK3),sK2))),k6_subset_1(k1_relat_1(sK3),sK2)),X0)
    | ~ r2_hidden(sK1(k1_relat_1(k7_relat_1(sK3,k6_subset_1(k1_relat_1(sK3),sK2))),k6_subset_1(k1_relat_1(sK3),sK2)),k1_relat_1(X1))
    | r2_hidden(sK1(k1_relat_1(k7_relat_1(sK3,k6_subset_1(k1_relat_1(sK3),sK2))),k6_subset_1(k1_relat_1(sK3),sK2)),k1_relat_1(k7_relat_1(X1,X0)))
    | ~ v1_relat_1(X1) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_10062,plain,
    ( ~ r2_hidden(sK1(k1_relat_1(k7_relat_1(sK3,k6_subset_1(k1_relat_1(sK3),sK2))),k6_subset_1(k1_relat_1(sK3),sK2)),k6_subset_1(k1_relat_1(sK3),sK2))
    | ~ r2_hidden(sK1(k1_relat_1(k7_relat_1(sK3,k6_subset_1(k1_relat_1(sK3),sK2))),k6_subset_1(k1_relat_1(sK3),sK2)),k1_relat_1(X0))
    | r2_hidden(sK1(k1_relat_1(k7_relat_1(sK3,k6_subset_1(k1_relat_1(sK3),sK2))),k6_subset_1(k1_relat_1(sK3),sK2)),k1_relat_1(k7_relat_1(X0,k6_subset_1(k1_relat_1(sK3),sK2))))
    | ~ v1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_656])).

cnf(c_10064,plain,
    ( ~ r2_hidden(sK1(k1_relat_1(k7_relat_1(sK3,k6_subset_1(k1_relat_1(sK3),sK2))),k6_subset_1(k1_relat_1(sK3),sK2)),k6_subset_1(k1_relat_1(sK3),sK2))
    | r2_hidden(sK1(k1_relat_1(k7_relat_1(sK3,k6_subset_1(k1_relat_1(sK3),sK2))),k6_subset_1(k1_relat_1(sK3),sK2)),k1_relat_1(k7_relat_1(sK3,k6_subset_1(k1_relat_1(sK3),sK2))))
    | ~ r2_hidden(sK1(k1_relat_1(k7_relat_1(sK3,k6_subset_1(k1_relat_1(sK3),sK2))),k6_subset_1(k1_relat_1(sK3),sK2)),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_10062])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2410,plain,
    ( r2_hidden(sK1(k1_relat_1(k7_relat_1(sK3,k6_subset_1(k1_relat_1(sK3),sK2))),k6_subset_1(k1_relat_1(sK3),sK2)),X0)
    | ~ r2_hidden(sK1(k1_relat_1(k7_relat_1(sK3,k6_subset_1(k1_relat_1(sK3),sK2))),k6_subset_1(k1_relat_1(sK3),sK2)),k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1)))) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_6923,plain,
    ( ~ r2_hidden(sK1(k1_relat_1(k7_relat_1(sK3,k6_subset_1(k1_relat_1(sK3),sK2))),k6_subset_1(k1_relat_1(sK3),sK2)),k5_xboole_0(k1_relat_1(sK3),k1_setfam_1(k1_enumset1(k1_relat_1(sK3),k1_relat_1(sK3),sK2))))
    | r2_hidden(sK1(k1_relat_1(k7_relat_1(sK3,k6_subset_1(k1_relat_1(sK3),sK2))),k6_subset_1(k1_relat_1(sK3),sK2)),k1_relat_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_2410])).

cnf(c_8,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_777,plain,
    ( k5_xboole_0(k1_relat_1(sK3),k1_setfam_1(k1_enumset1(k1_relat_1(sK3),k1_relat_1(sK3),sK2))) = k6_subset_1(k1_relat_1(sK3),sK2) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_120,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_498,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK1(k1_relat_1(k7_relat_1(sK3,k6_subset_1(k1_relat_1(sK3),sK2))),k6_subset_1(k1_relat_1(sK3),sK2)),k6_subset_1(k1_relat_1(sK3),sK2))
    | X1 != k6_subset_1(k1_relat_1(sK3),sK2)
    | X0 != sK1(k1_relat_1(k7_relat_1(sK3,k6_subset_1(k1_relat_1(sK3),sK2))),k6_subset_1(k1_relat_1(sK3),sK2)) ),
    inference(instantiation,[status(thm)],[c_120])).

cnf(c_611,plain,
    ( r2_hidden(sK1(k1_relat_1(k7_relat_1(sK3,k6_subset_1(k1_relat_1(sK3),sK2))),k6_subset_1(k1_relat_1(sK3),sK2)),X0)
    | ~ r2_hidden(sK1(k1_relat_1(k7_relat_1(sK3,k6_subset_1(k1_relat_1(sK3),sK2))),k6_subset_1(k1_relat_1(sK3),sK2)),k6_subset_1(k1_relat_1(sK3),sK2))
    | X0 != k6_subset_1(k1_relat_1(sK3),sK2)
    | sK1(k1_relat_1(k7_relat_1(sK3,k6_subset_1(k1_relat_1(sK3),sK2))),k6_subset_1(k1_relat_1(sK3),sK2)) != sK1(k1_relat_1(k7_relat_1(sK3,k6_subset_1(k1_relat_1(sK3),sK2))),k6_subset_1(k1_relat_1(sK3),sK2)) ),
    inference(instantiation,[status(thm)],[c_498])).

cnf(c_776,plain,
    ( ~ r2_hidden(sK1(k1_relat_1(k7_relat_1(sK3,k6_subset_1(k1_relat_1(sK3),sK2))),k6_subset_1(k1_relat_1(sK3),sK2)),k6_subset_1(k1_relat_1(sK3),sK2))
    | r2_hidden(sK1(k1_relat_1(k7_relat_1(sK3,k6_subset_1(k1_relat_1(sK3),sK2))),k6_subset_1(k1_relat_1(sK3),sK2)),k5_xboole_0(k1_relat_1(sK3),k1_setfam_1(k1_enumset1(k1_relat_1(sK3),k1_relat_1(sK3),sK2))))
    | sK1(k1_relat_1(k7_relat_1(sK3,k6_subset_1(k1_relat_1(sK3),sK2))),k6_subset_1(k1_relat_1(sK3),sK2)) != sK1(k1_relat_1(k7_relat_1(sK3,k6_subset_1(k1_relat_1(sK3),sK2))),k6_subset_1(k1_relat_1(sK3),sK2))
    | k5_xboole_0(k1_relat_1(sK3),k1_setfam_1(k1_enumset1(k1_relat_1(sK3),k1_relat_1(sK3),sK2))) != k6_subset_1(k1_relat_1(sK3),sK2) ),
    inference(instantiation,[status(thm)],[c_611])).

cnf(c_116,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_612,plain,
    ( sK1(k1_relat_1(k7_relat_1(sK3,k6_subset_1(k1_relat_1(sK3),sK2))),k6_subset_1(k1_relat_1(sK3),sK2)) = sK1(k1_relat_1(k7_relat_1(sK3,k6_subset_1(k1_relat_1(sK3),sK2))),k6_subset_1(k1_relat_1(sK3),sK2)) ),
    inference(instantiation,[status(thm)],[c_116])).

cnf(c_11,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_575,plain,
    ( r2_hidden(sK1(k1_relat_1(k7_relat_1(sK3,k6_subset_1(k1_relat_1(sK3),sK2))),k6_subset_1(k1_relat_1(sK3),sK2)),k6_subset_1(k1_relat_1(sK3),sK2))
    | ~ r2_hidden(sK1(k1_relat_1(k7_relat_1(sK3,k6_subset_1(k1_relat_1(sK3),sK2))),k6_subset_1(k1_relat_1(sK3),sK2)),k1_relat_1(k7_relat_1(sK3,k6_subset_1(k1_relat_1(sK3),sK2))))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_6,plain,
    ( ~ r2_hidden(sK1(X0,X1),X1)
    | ~ r2_hidden(sK1(X0,X1),X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_567,plain,
    ( ~ r2_hidden(sK1(k1_relat_1(k7_relat_1(sK3,k6_subset_1(k1_relat_1(sK3),sK2))),k6_subset_1(k1_relat_1(sK3),sK2)),k6_subset_1(k1_relat_1(sK3),sK2))
    | ~ r2_hidden(sK1(k1_relat_1(k7_relat_1(sK3,k6_subset_1(k1_relat_1(sK3),sK2))),k6_subset_1(k1_relat_1(sK3),sK2)),k1_relat_1(k7_relat_1(sK3,k6_subset_1(k1_relat_1(sK3),sK2))))
    | k6_subset_1(k1_relat_1(sK3),sK2) = k1_relat_1(k7_relat_1(sK3,k6_subset_1(k1_relat_1(sK3),sK2))) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_7,plain,
    ( r2_hidden(sK1(X0,X1),X1)
    | r2_hidden(sK1(X0,X1),X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_470,plain,
    ( r2_hidden(sK1(k1_relat_1(k7_relat_1(sK3,k6_subset_1(k1_relat_1(sK3),sK2))),k6_subset_1(k1_relat_1(sK3),sK2)),k6_subset_1(k1_relat_1(sK3),sK2))
    | r2_hidden(sK1(k1_relat_1(k7_relat_1(sK3,k6_subset_1(k1_relat_1(sK3),sK2))),k6_subset_1(k1_relat_1(sK3),sK2)),k1_relat_1(k7_relat_1(sK3,k6_subset_1(k1_relat_1(sK3),sK2))))
    | k6_subset_1(k1_relat_1(sK3),sK2) = k1_relat_1(k7_relat_1(sK3,k6_subset_1(k1_relat_1(sK3),sK2))) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_12,negated_conjecture,
    ( k6_subset_1(k1_relat_1(sK3),sK2) != k1_relat_1(k7_relat_1(sK3,k6_subset_1(k1_relat_1(sK3),sK2))) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_13,negated_conjecture,
    ( v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f40])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10064,c_6923,c_777,c_776,c_612,c_575,c_567,c_470,c_12,c_13])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:24:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.60/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.60/1.00  
% 3.60/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.60/1.00  
% 3.60/1.00  ------  iProver source info
% 3.60/1.00  
% 3.60/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.60/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.60/1.00  git: non_committed_changes: false
% 3.60/1.00  git: last_make_outside_of_git: false
% 3.60/1.00  
% 3.60/1.00  ------ 
% 3.60/1.00  ------ Parsing...
% 3.60/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.60/1.00  
% 3.60/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.60/1.00  
% 3.60/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.60/1.00  
% 3.60/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.60/1.00  ------ Proving...
% 3.60/1.00  ------ Problem Properties 
% 3.60/1.00  
% 3.60/1.00  
% 3.60/1.00  clauses                                 14
% 3.60/1.00  conjectures                             2
% 3.60/1.00  EPR                                     1
% 3.60/1.00  Horn                                    9
% 3.60/1.00  unary                                   3
% 3.60/1.00  binary                                  2
% 3.60/1.00  lits                                    36
% 3.60/1.00  lits eq                                 7
% 3.60/1.00  fd_pure                                 0
% 3.60/1.00  fd_pseudo                               0
% 3.60/1.00  fd_cond                                 0
% 3.60/1.00  fd_pseudo_cond                          5
% 3.60/1.00  AC symbols                              0
% 3.60/1.00  
% 3.60/1.00  ------ Input Options Time Limit: Unbounded
% 3.60/1.00  
% 3.60/1.00  
% 3.60/1.00  ------ 
% 3.60/1.00  Current options:
% 3.60/1.00  ------ 
% 3.60/1.00  
% 3.60/1.00  
% 3.60/1.00  
% 3.60/1.00  
% 3.60/1.00  ------ Proving...
% 3.60/1.00  
% 3.60/1.00  
% 3.60/1.00  % SZS status Theorem for theBenchmark.p
% 3.60/1.00  
% 3.60/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.60/1.00  
% 3.60/1.00  fof(f7,axiom,(
% 3.60/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))))),
% 3.60/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/1.00  
% 3.60/1.00  fof(f11,plain,(
% 3.60/1.00    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))) | ~v1_relat_1(X2))),
% 3.60/1.00    inference(ennf_transformation,[],[f7])).
% 3.60/1.00  
% 3.60/1.00  fof(f21,plain,(
% 3.60/1.00    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | (~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1))) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 3.60/1.00    inference(nnf_transformation,[],[f11])).
% 3.60/1.00  
% 3.60/1.00  fof(f22,plain,(
% 3.60/1.00    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1)) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 3.60/1.00    inference(flattening,[],[f21])).
% 3.60/1.00  
% 3.60/1.00  fof(f39,plain,(
% 3.60/1.00    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1) | ~v1_relat_1(X2)) )),
% 3.60/1.00    inference(cnf_transformation,[],[f22])).
% 3.60/1.00  
% 3.60/1.00  fof(f1,axiom,(
% 3.60/1.00    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.60/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/1.00  
% 3.60/1.00  fof(f13,plain,(
% 3.60/1.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.60/1.00    inference(nnf_transformation,[],[f1])).
% 3.60/1.00  
% 3.60/1.00  fof(f14,plain,(
% 3.60/1.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.60/1.00    inference(flattening,[],[f13])).
% 3.60/1.00  
% 3.60/1.00  fof(f15,plain,(
% 3.60/1.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.60/1.00    inference(rectify,[],[f14])).
% 3.60/1.00  
% 3.60/1.00  fof(f16,plain,(
% 3.60/1.00    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 3.60/1.00    introduced(choice_axiom,[])).
% 3.60/1.00  
% 3.60/1.00  fof(f17,plain,(
% 3.60/1.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.60/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).
% 3.60/1.00  
% 3.60/1.00  fof(f25,plain,(
% 3.60/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 3.60/1.00    inference(cnf_transformation,[],[f17])).
% 3.60/1.00  
% 3.60/1.00  fof(f3,axiom,(
% 3.60/1.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.60/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/1.00  
% 3.60/1.00  fof(f33,plain,(
% 3.60/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.60/1.00    inference(cnf_transformation,[],[f3])).
% 3.60/1.00  
% 3.60/1.00  fof(f6,axiom,(
% 3.60/1.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.60/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/1.00  
% 3.60/1.00  fof(f36,plain,(
% 3.60/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.60/1.00    inference(cnf_transformation,[],[f6])).
% 3.60/1.00  
% 3.60/1.00  fof(f4,axiom,(
% 3.60/1.00    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.60/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/1.00  
% 3.60/1.00  fof(f34,plain,(
% 3.60/1.00    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.60/1.00    inference(cnf_transformation,[],[f4])).
% 3.60/1.00  
% 3.60/1.00  fof(f42,plain,(
% 3.60/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 3.60/1.00    inference(definition_unfolding,[],[f36,f34])).
% 3.60/1.00  
% 3.60/1.00  fof(f43,plain,(
% 3.60/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1)))) )),
% 3.60/1.00    inference(definition_unfolding,[],[f33,f42])).
% 3.60/1.00  
% 3.60/1.00  fof(f49,plain,(
% 3.60/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))) != X2) )),
% 3.60/1.00    inference(definition_unfolding,[],[f25,f43])).
% 3.60/1.00  
% 3.60/1.00  fof(f53,plain,(
% 3.60/1.00    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))))) )),
% 3.60/1.00    inference(equality_resolution,[],[f49])).
% 3.60/1.00  
% 3.60/1.00  fof(f5,axiom,(
% 3.60/1.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 3.60/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/1.00  
% 3.60/1.00  fof(f35,plain,(
% 3.60/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 3.60/1.00    inference(cnf_transformation,[],[f5])).
% 3.60/1.00  
% 3.60/1.00  fof(f50,plain,(
% 3.60/1.00    ( ! [X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))) = k6_subset_1(X0,X1)) )),
% 3.60/1.00    inference(definition_unfolding,[],[f35,f43])).
% 3.60/1.00  
% 3.60/1.00  fof(f37,plain,(
% 3.60/1.00    ( ! [X2,X0,X1] : (r2_hidden(X0,X1) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~v1_relat_1(X2)) )),
% 3.60/1.00    inference(cnf_transformation,[],[f22])).
% 3.60/1.00  
% 3.60/1.00  fof(f2,axiom,(
% 3.60/1.00    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 3.60/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/1.00  
% 3.60/1.00  fof(f10,plain,(
% 3.60/1.00    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 3.60/1.00    inference(ennf_transformation,[],[f2])).
% 3.60/1.00  
% 3.60/1.00  fof(f18,plain,(
% 3.60/1.00    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 3.60/1.00    inference(nnf_transformation,[],[f10])).
% 3.60/1.00  
% 3.60/1.00  fof(f19,plain,(
% 3.60/1.00    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK1(X0,X1),X1) | ~r2_hidden(sK1(X0,X1),X0)) & (r2_hidden(sK1(X0,X1),X1) | r2_hidden(sK1(X0,X1),X0))))),
% 3.60/1.00    introduced(choice_axiom,[])).
% 3.60/1.00  
% 3.60/1.00  fof(f20,plain,(
% 3.60/1.00    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK1(X0,X1),X1) | ~r2_hidden(sK1(X0,X1),X0)) & (r2_hidden(sK1(X0,X1),X1) | r2_hidden(sK1(X0,X1),X0))))),
% 3.60/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f18,f19])).
% 3.60/1.00  
% 3.60/1.00  fof(f32,plain,(
% 3.60/1.00    ( ! [X0,X1] : (X0 = X1 | ~r2_hidden(sK1(X0,X1),X1) | ~r2_hidden(sK1(X0,X1),X0)) )),
% 3.60/1.00    inference(cnf_transformation,[],[f20])).
% 3.60/1.00  
% 3.60/1.00  fof(f31,plain,(
% 3.60/1.00    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK1(X0,X1),X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 3.60/1.00    inference(cnf_transformation,[],[f20])).
% 3.60/1.00  
% 3.60/1.00  fof(f8,conjecture,(
% 3.60/1.00    ! [X0,X1] : (v1_relat_1(X1) => k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0))))),
% 3.60/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/1.00  
% 3.60/1.00  fof(f9,negated_conjecture,(
% 3.60/1.00    ~! [X0,X1] : (v1_relat_1(X1) => k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0))))),
% 3.60/1.00    inference(negated_conjecture,[],[f8])).
% 3.60/1.00  
% 3.60/1.00  fof(f12,plain,(
% 3.60/1.00    ? [X0,X1] : (k6_subset_1(k1_relat_1(X1),X0) != k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0))) & v1_relat_1(X1))),
% 3.60/1.00    inference(ennf_transformation,[],[f9])).
% 3.60/1.00  
% 3.60/1.00  fof(f23,plain,(
% 3.60/1.00    ? [X0,X1] : (k6_subset_1(k1_relat_1(X1),X0) != k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0))) & v1_relat_1(X1)) => (k6_subset_1(k1_relat_1(sK3),sK2) != k1_relat_1(k7_relat_1(sK3,k6_subset_1(k1_relat_1(sK3),sK2))) & v1_relat_1(sK3))),
% 3.60/1.00    introduced(choice_axiom,[])).
% 3.60/1.00  
% 3.60/1.00  fof(f24,plain,(
% 3.60/1.00    k6_subset_1(k1_relat_1(sK3),sK2) != k1_relat_1(k7_relat_1(sK3,k6_subset_1(k1_relat_1(sK3),sK2))) & v1_relat_1(sK3)),
% 3.60/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f12,f23])).
% 3.60/1.00  
% 3.60/1.00  fof(f41,plain,(
% 3.60/1.00    k6_subset_1(k1_relat_1(sK3),sK2) != k1_relat_1(k7_relat_1(sK3,k6_subset_1(k1_relat_1(sK3),sK2)))),
% 3.60/1.00    inference(cnf_transformation,[],[f24])).
% 3.60/1.00  
% 3.60/1.00  fof(f40,plain,(
% 3.60/1.00    v1_relat_1(sK3)),
% 3.60/1.00    inference(cnf_transformation,[],[f24])).
% 3.60/1.00  
% 3.60/1.00  cnf(c_9,plain,
% 3.60/1.00      ( ~ r2_hidden(X0,X1)
% 3.60/1.00      | ~ r2_hidden(X0,k1_relat_1(X2))
% 3.60/1.00      | r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
% 3.60/1.00      | ~ v1_relat_1(X2) ),
% 3.60/1.00      inference(cnf_transformation,[],[f39]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_656,plain,
% 3.60/1.00      ( ~ r2_hidden(sK1(k1_relat_1(k7_relat_1(sK3,k6_subset_1(k1_relat_1(sK3),sK2))),k6_subset_1(k1_relat_1(sK3),sK2)),X0)
% 3.60/1.00      | ~ r2_hidden(sK1(k1_relat_1(k7_relat_1(sK3,k6_subset_1(k1_relat_1(sK3),sK2))),k6_subset_1(k1_relat_1(sK3),sK2)),k1_relat_1(X1))
% 3.60/1.00      | r2_hidden(sK1(k1_relat_1(k7_relat_1(sK3,k6_subset_1(k1_relat_1(sK3),sK2))),k6_subset_1(k1_relat_1(sK3),sK2)),k1_relat_1(k7_relat_1(X1,X0)))
% 3.60/1.00      | ~ v1_relat_1(X1) ),
% 3.60/1.00      inference(instantiation,[status(thm)],[c_9]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_10062,plain,
% 3.60/1.00      ( ~ r2_hidden(sK1(k1_relat_1(k7_relat_1(sK3,k6_subset_1(k1_relat_1(sK3),sK2))),k6_subset_1(k1_relat_1(sK3),sK2)),k6_subset_1(k1_relat_1(sK3),sK2))
% 3.60/1.00      | ~ r2_hidden(sK1(k1_relat_1(k7_relat_1(sK3,k6_subset_1(k1_relat_1(sK3),sK2))),k6_subset_1(k1_relat_1(sK3),sK2)),k1_relat_1(X0))
% 3.60/1.00      | r2_hidden(sK1(k1_relat_1(k7_relat_1(sK3,k6_subset_1(k1_relat_1(sK3),sK2))),k6_subset_1(k1_relat_1(sK3),sK2)),k1_relat_1(k7_relat_1(X0,k6_subset_1(k1_relat_1(sK3),sK2))))
% 3.60/1.00      | ~ v1_relat_1(X0) ),
% 3.60/1.00      inference(instantiation,[status(thm)],[c_656]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_10064,plain,
% 3.60/1.00      ( ~ r2_hidden(sK1(k1_relat_1(k7_relat_1(sK3,k6_subset_1(k1_relat_1(sK3),sK2))),k6_subset_1(k1_relat_1(sK3),sK2)),k6_subset_1(k1_relat_1(sK3),sK2))
% 3.60/1.00      | r2_hidden(sK1(k1_relat_1(k7_relat_1(sK3,k6_subset_1(k1_relat_1(sK3),sK2))),k6_subset_1(k1_relat_1(sK3),sK2)),k1_relat_1(k7_relat_1(sK3,k6_subset_1(k1_relat_1(sK3),sK2))))
% 3.60/1.00      | ~ r2_hidden(sK1(k1_relat_1(k7_relat_1(sK3,k6_subset_1(k1_relat_1(sK3),sK2))),k6_subset_1(k1_relat_1(sK3),sK2)),k1_relat_1(sK3))
% 3.60/1.00      | ~ v1_relat_1(sK3) ),
% 3.60/1.00      inference(instantiation,[status(thm)],[c_10062]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_5,plain,
% 3.60/1.00      ( r2_hidden(X0,X1)
% 3.60/1.00      | ~ r2_hidden(X0,k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))) ),
% 3.60/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_2410,plain,
% 3.60/1.00      ( r2_hidden(sK1(k1_relat_1(k7_relat_1(sK3,k6_subset_1(k1_relat_1(sK3),sK2))),k6_subset_1(k1_relat_1(sK3),sK2)),X0)
% 3.60/1.00      | ~ r2_hidden(sK1(k1_relat_1(k7_relat_1(sK3,k6_subset_1(k1_relat_1(sK3),sK2))),k6_subset_1(k1_relat_1(sK3),sK2)),k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1)))) ),
% 3.60/1.00      inference(instantiation,[status(thm)],[c_5]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_6923,plain,
% 3.60/1.00      ( ~ r2_hidden(sK1(k1_relat_1(k7_relat_1(sK3,k6_subset_1(k1_relat_1(sK3),sK2))),k6_subset_1(k1_relat_1(sK3),sK2)),k5_xboole_0(k1_relat_1(sK3),k1_setfam_1(k1_enumset1(k1_relat_1(sK3),k1_relat_1(sK3),sK2))))
% 3.60/1.00      | r2_hidden(sK1(k1_relat_1(k7_relat_1(sK3,k6_subset_1(k1_relat_1(sK3),sK2))),k6_subset_1(k1_relat_1(sK3),sK2)),k1_relat_1(sK3)) ),
% 3.60/1.00      inference(instantiation,[status(thm)],[c_2410]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_8,plain,
% 3.60/1.00      ( k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))) = k6_subset_1(X0,X1) ),
% 3.60/1.00      inference(cnf_transformation,[],[f50]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_777,plain,
% 3.60/1.00      ( k5_xboole_0(k1_relat_1(sK3),k1_setfam_1(k1_enumset1(k1_relat_1(sK3),k1_relat_1(sK3),sK2))) = k6_subset_1(k1_relat_1(sK3),sK2) ),
% 3.60/1.00      inference(instantiation,[status(thm)],[c_8]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_120,plain,
% 3.60/1.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.60/1.00      theory(equality) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_498,plain,
% 3.60/1.00      ( r2_hidden(X0,X1)
% 3.60/1.00      | ~ r2_hidden(sK1(k1_relat_1(k7_relat_1(sK3,k6_subset_1(k1_relat_1(sK3),sK2))),k6_subset_1(k1_relat_1(sK3),sK2)),k6_subset_1(k1_relat_1(sK3),sK2))
% 3.60/1.00      | X1 != k6_subset_1(k1_relat_1(sK3),sK2)
% 3.60/1.00      | X0 != sK1(k1_relat_1(k7_relat_1(sK3,k6_subset_1(k1_relat_1(sK3),sK2))),k6_subset_1(k1_relat_1(sK3),sK2)) ),
% 3.60/1.00      inference(instantiation,[status(thm)],[c_120]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_611,plain,
% 3.60/1.00      ( r2_hidden(sK1(k1_relat_1(k7_relat_1(sK3,k6_subset_1(k1_relat_1(sK3),sK2))),k6_subset_1(k1_relat_1(sK3),sK2)),X0)
% 3.60/1.00      | ~ r2_hidden(sK1(k1_relat_1(k7_relat_1(sK3,k6_subset_1(k1_relat_1(sK3),sK2))),k6_subset_1(k1_relat_1(sK3),sK2)),k6_subset_1(k1_relat_1(sK3),sK2))
% 3.60/1.00      | X0 != k6_subset_1(k1_relat_1(sK3),sK2)
% 3.60/1.00      | sK1(k1_relat_1(k7_relat_1(sK3,k6_subset_1(k1_relat_1(sK3),sK2))),k6_subset_1(k1_relat_1(sK3),sK2)) != sK1(k1_relat_1(k7_relat_1(sK3,k6_subset_1(k1_relat_1(sK3),sK2))),k6_subset_1(k1_relat_1(sK3),sK2)) ),
% 3.60/1.00      inference(instantiation,[status(thm)],[c_498]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_776,plain,
% 3.60/1.00      ( ~ r2_hidden(sK1(k1_relat_1(k7_relat_1(sK3,k6_subset_1(k1_relat_1(sK3),sK2))),k6_subset_1(k1_relat_1(sK3),sK2)),k6_subset_1(k1_relat_1(sK3),sK2))
% 3.60/1.00      | r2_hidden(sK1(k1_relat_1(k7_relat_1(sK3,k6_subset_1(k1_relat_1(sK3),sK2))),k6_subset_1(k1_relat_1(sK3),sK2)),k5_xboole_0(k1_relat_1(sK3),k1_setfam_1(k1_enumset1(k1_relat_1(sK3),k1_relat_1(sK3),sK2))))
% 3.60/1.00      | sK1(k1_relat_1(k7_relat_1(sK3,k6_subset_1(k1_relat_1(sK3),sK2))),k6_subset_1(k1_relat_1(sK3),sK2)) != sK1(k1_relat_1(k7_relat_1(sK3,k6_subset_1(k1_relat_1(sK3),sK2))),k6_subset_1(k1_relat_1(sK3),sK2))
% 3.60/1.00      | k5_xboole_0(k1_relat_1(sK3),k1_setfam_1(k1_enumset1(k1_relat_1(sK3),k1_relat_1(sK3),sK2))) != k6_subset_1(k1_relat_1(sK3),sK2) ),
% 3.60/1.00      inference(instantiation,[status(thm)],[c_611]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_116,plain,( X0 = X0 ),theory(equality) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_612,plain,
% 3.60/1.00      ( sK1(k1_relat_1(k7_relat_1(sK3,k6_subset_1(k1_relat_1(sK3),sK2))),k6_subset_1(k1_relat_1(sK3),sK2)) = sK1(k1_relat_1(k7_relat_1(sK3,k6_subset_1(k1_relat_1(sK3),sK2))),k6_subset_1(k1_relat_1(sK3),sK2)) ),
% 3.60/1.00      inference(instantiation,[status(thm)],[c_116]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_11,plain,
% 3.60/1.00      ( r2_hidden(X0,X1)
% 3.60/1.00      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
% 3.60/1.00      | ~ v1_relat_1(X2) ),
% 3.60/1.00      inference(cnf_transformation,[],[f37]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_575,plain,
% 3.60/1.00      ( r2_hidden(sK1(k1_relat_1(k7_relat_1(sK3,k6_subset_1(k1_relat_1(sK3),sK2))),k6_subset_1(k1_relat_1(sK3),sK2)),k6_subset_1(k1_relat_1(sK3),sK2))
% 3.60/1.00      | ~ r2_hidden(sK1(k1_relat_1(k7_relat_1(sK3,k6_subset_1(k1_relat_1(sK3),sK2))),k6_subset_1(k1_relat_1(sK3),sK2)),k1_relat_1(k7_relat_1(sK3,k6_subset_1(k1_relat_1(sK3),sK2))))
% 3.60/1.00      | ~ v1_relat_1(sK3) ),
% 3.60/1.00      inference(instantiation,[status(thm)],[c_11]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_6,plain,
% 3.60/1.00      ( ~ r2_hidden(sK1(X0,X1),X1)
% 3.60/1.00      | ~ r2_hidden(sK1(X0,X1),X0)
% 3.60/1.00      | X1 = X0 ),
% 3.60/1.00      inference(cnf_transformation,[],[f32]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_567,plain,
% 3.60/1.00      ( ~ r2_hidden(sK1(k1_relat_1(k7_relat_1(sK3,k6_subset_1(k1_relat_1(sK3),sK2))),k6_subset_1(k1_relat_1(sK3),sK2)),k6_subset_1(k1_relat_1(sK3),sK2))
% 3.60/1.00      | ~ r2_hidden(sK1(k1_relat_1(k7_relat_1(sK3,k6_subset_1(k1_relat_1(sK3),sK2))),k6_subset_1(k1_relat_1(sK3),sK2)),k1_relat_1(k7_relat_1(sK3,k6_subset_1(k1_relat_1(sK3),sK2))))
% 3.60/1.00      | k6_subset_1(k1_relat_1(sK3),sK2) = k1_relat_1(k7_relat_1(sK3,k6_subset_1(k1_relat_1(sK3),sK2))) ),
% 3.60/1.00      inference(instantiation,[status(thm)],[c_6]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_7,plain,
% 3.60/1.00      ( r2_hidden(sK1(X0,X1),X1) | r2_hidden(sK1(X0,X1),X0) | X1 = X0 ),
% 3.60/1.00      inference(cnf_transformation,[],[f31]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_470,plain,
% 3.60/1.00      ( r2_hidden(sK1(k1_relat_1(k7_relat_1(sK3,k6_subset_1(k1_relat_1(sK3),sK2))),k6_subset_1(k1_relat_1(sK3),sK2)),k6_subset_1(k1_relat_1(sK3),sK2))
% 3.60/1.00      | r2_hidden(sK1(k1_relat_1(k7_relat_1(sK3,k6_subset_1(k1_relat_1(sK3),sK2))),k6_subset_1(k1_relat_1(sK3),sK2)),k1_relat_1(k7_relat_1(sK3,k6_subset_1(k1_relat_1(sK3),sK2))))
% 3.60/1.00      | k6_subset_1(k1_relat_1(sK3),sK2) = k1_relat_1(k7_relat_1(sK3,k6_subset_1(k1_relat_1(sK3),sK2))) ),
% 3.60/1.00      inference(instantiation,[status(thm)],[c_7]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_12,negated_conjecture,
% 3.60/1.00      ( k6_subset_1(k1_relat_1(sK3),sK2) != k1_relat_1(k7_relat_1(sK3,k6_subset_1(k1_relat_1(sK3),sK2))) ),
% 3.60/1.00      inference(cnf_transformation,[],[f41]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(c_13,negated_conjecture,
% 3.60/1.00      ( v1_relat_1(sK3) ),
% 3.60/1.00      inference(cnf_transformation,[],[f40]) ).
% 3.60/1.00  
% 3.60/1.00  cnf(contradiction,plain,
% 3.60/1.00      ( $false ),
% 3.60/1.00      inference(minisat,
% 3.60/1.00                [status(thm)],
% 3.60/1.00                [c_10064,c_6923,c_777,c_776,c_612,c_575,c_567,c_470,c_12,
% 3.60/1.00                 c_13]) ).
% 3.60/1.00  
% 3.60/1.00  
% 3.60/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.60/1.00  
% 3.60/1.00  ------                               Statistics
% 3.60/1.00  
% 3.60/1.00  ------ Selected
% 3.60/1.00  
% 3.60/1.00  total_time:                             0.329
% 3.60/1.00  
%------------------------------------------------------------------------------
