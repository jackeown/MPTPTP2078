%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0550+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:33 EST 2020

% Result     : Theorem 1.89s
% Output     : CNFRefutation 1.89s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 115 expanded)
%              Number of clauses        :   36 (  39 expanded)
%              Number of leaves         :   15 (  28 expanded)
%              Depth                    :   12
%              Number of atoms          :  261 ( 404 expanded)
%              Number of equality atoms :   45 (  99 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X3,X0),X2)
              & r2_hidden(X3,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X4,X0),X2)
              & r2_hidden(X4,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f26])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK3(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2)
        & r2_hidden(sK3(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2)
            & r2_hidden(sK3(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f28])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X3,X0),X2)
      | ~ r2_hidden(X3,k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( k9_relat_1(X1,X0) = k1_xboole_0
          & r1_tarski(X0,k1_relat_1(X1))
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ~ ( k9_relat_1(X1,X0) = k1_xboole_0
            & r1_tarski(X0,k1_relat_1(X1))
            & k1_xboole_0 != X0 ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f18,plain,(
    ? [X0,X1] :
      ( k9_relat_1(X1,X0) = k1_xboole_0
      & r1_tarski(X0,k1_relat_1(X1))
      & k1_xboole_0 != X0
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f19,plain,(
    ? [X0,X1] :
      ( k9_relat_1(X1,X0) = k1_xboole_0
      & r1_tarski(X0,k1_relat_1(X1))
      & k1_xboole_0 != X0
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f30,plain,
    ( ? [X0,X1] :
        ( k9_relat_1(X1,X0) = k1_xboole_0
        & r1_tarski(X0,k1_relat_1(X1))
        & k1_xboole_0 != X0
        & v1_relat_1(X1) )
   => ( k9_relat_1(sK5,sK4) = k1_xboole_0
      & r1_tarski(sK4,k1_relat_1(sK5))
      & k1_xboole_0 != sK4
      & v1_relat_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( k9_relat_1(sK5,sK4) = k1_xboole_0
    & r1_tarski(sK4,k1_relat_1(sK5))
    & k1_xboole_0 != sK4
    & v1_relat_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f19,f30])).

fof(f46,plain,(
    v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f31])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f21,plain,(
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
    inference(rectify,[],[f20])).

fof(f24,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK2(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK1(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK0(X0,X1),X3),X0)
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK0(X0,X1),X4),X0)
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK0(X0,X1),X3),X0)
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X0)
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK2(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f24,f23,f22])).

fof(f34,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f50,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f34])).

fof(f33,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK2(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f51,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK2(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f33])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f48,plain,(
    r1_tarski(sK4,k1_relat_1(sK5)) ),
    inference(cnf_transformation,[],[f31])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(o_1_4_relat_1(X0),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] : m1_subset_1(o_1_4_relat_1(X0),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f44,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f3,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f49,plain,(
    k9_relat_1(sK5,sK4) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f31])).

fof(f47,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_466,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1853,plain,
    ( v1_xboole_0(X0)
    | ~ v1_xboole_0(o_0_0_xboole_0)
    | X0 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_466])).

cnf(c_1855,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ v1_xboole_0(o_0_0_xboole_0)
    | k1_xboole_0 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1853])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_899,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK5,sK4))
    | ~ v1_xboole_0(k9_relat_1(sK5,sK4)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1708,plain,
    ( ~ r2_hidden(sK2(sK5,o_1_4_relat_1(sK4)),k9_relat_1(sK5,sK4))
    | ~ v1_xboole_0(k9_relat_1(sK5,sK4)) ),
    inference(instantiation,[status(thm)],[c_899])).

cnf(c_1034,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k9_relat_1(sK5,sK4))
    | k9_relat_1(sK5,sK4) != X0 ),
    inference(instantiation,[status(thm)],[c_466])).

cnf(c_1036,plain,
    ( v1_xboole_0(k9_relat_1(sK5,sK4))
    | ~ v1_xboole_0(k1_xboole_0)
    | k9_relat_1(sK5,sK4) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1034])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k9_relat_1(X3,X1))
    | ~ r2_hidden(X0,k1_relat_1(X3))
    | ~ r2_hidden(k4_tarski(X0,X2),X3)
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_17,negated_conjecture,
    ( v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_258,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k9_relat_1(X3,X1))
    | ~ r2_hidden(X0,k1_relat_1(X3))
    | ~ r2_hidden(k4_tarski(X0,X2),X3)
    | sK5 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_17])).

cnf(c_259,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k9_relat_1(sK5,X1))
    | ~ r2_hidden(X0,k1_relat_1(sK5))
    | ~ r2_hidden(k4_tarski(X0,X2),sK5) ),
    inference(unflattening,[status(thm)],[c_258])).

cnf(c_3,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_271,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k9_relat_1(sK5,X1))
    | ~ r2_hidden(k4_tarski(X0,X2),sK5) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_259,c_3])).

cnf(c_834,plain,
    ( r2_hidden(X0,k9_relat_1(sK5,sK4))
    | ~ r2_hidden(k4_tarski(o_1_4_relat_1(sK4),X0),sK5)
    | ~ r2_hidden(o_1_4_relat_1(sK4),sK4) ),
    inference(instantiation,[status(thm)],[c_271])).

cnf(c_987,plain,
    ( r2_hidden(sK2(sK5,o_1_4_relat_1(sK4)),k9_relat_1(sK5,sK4))
    | ~ r2_hidden(k4_tarski(o_1_4_relat_1(sK4),sK2(sK5,o_1_4_relat_1(sK4))),sK5)
    | ~ r2_hidden(o_1_4_relat_1(sK4),sK4) ),
    inference(instantiation,[status(thm)],[c_834])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,sK2(X1,X0)),X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_852,plain,
    ( r2_hidden(k4_tarski(o_1_4_relat_1(sK4),sK2(sK5,o_1_4_relat_1(sK4))),sK5)
    | ~ r2_hidden(o_1_4_relat_1(sK4),k1_relat_1(sK5)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_15,negated_conjecture,
    ( r1_tarski(sK4,k1_relat_1(sK5)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_185,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | k1_relat_1(sK5) != X2
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_15])).

cnf(c_186,plain,
    ( r2_hidden(X0,k1_relat_1(sK5))
    | ~ r2_hidden(X0,sK4) ),
    inference(unflattening,[status(thm)],[c_185])).

cnf(c_843,plain,
    ( r2_hidden(o_1_4_relat_1(sK4),k1_relat_1(sK5))
    | ~ r2_hidden(o_1_4_relat_1(sK4),sK4) ),
    inference(instantiation,[status(thm)],[c_186])).

cnf(c_6,plain,
    ( m1_subset_1(o_1_4_relat_1(X0),X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_200,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | X1 != X2
    | o_1_4_relat_1(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_11])).

cnf(c_201,plain,
    ( r2_hidden(o_1_4_relat_1(X0),X0)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_200])).

cnf(c_822,plain,
    ( r2_hidden(o_1_4_relat_1(sK4),sK4)
    | v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_201])).

cnf(c_12,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_804,plain,
    ( ~ v1_xboole_0(sK4)
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_5,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_235,plain,
    ( k1_xboole_0 = X0
    | o_0_0_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_12])).

cnf(c_236,plain,
    ( k1_xboole_0 = o_0_0_xboole_0 ),
    inference(unflattening,[status(thm)],[c_235])).

cnf(c_14,negated_conjecture,
    ( k9_relat_1(sK5,sK4) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_16,negated_conjecture,
    ( k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f47])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1855,c_1708,c_1036,c_987,c_852,c_843,c_822,c_804,c_236,c_5,c_14,c_16])).


%------------------------------------------------------------------------------
