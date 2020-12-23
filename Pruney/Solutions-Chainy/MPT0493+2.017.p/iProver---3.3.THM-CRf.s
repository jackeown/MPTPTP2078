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
% DateTime   : Thu Dec  3 11:44:44 EST 2020

% Result     : Theorem 0.36s
% Output     : CNFRefutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 122 expanded)
%              Number of clauses        :   41 (  45 expanded)
%              Number of leaves         :   11 (  27 expanded)
%              Depth                    :   13
%              Number of atoms          :  264 ( 440 expanded)
%              Number of equality atoms :   84 ( 131 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(X0,k1_relat_1(X1))
         => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f13,plain,(
    ? [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) != X0
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f14,plain,(
    ? [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) != X0
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f22,plain,
    ( ? [X0,X1] :
        ( k1_relat_1(k7_relat_1(X1,X0)) != X0
        & r1_tarski(X0,k1_relat_1(X1))
        & v1_relat_1(X1) )
   => ( k1_relat_1(k7_relat_1(sK2,sK1)) != sK1
      & r1_tarski(sK1,k1_relat_1(sK2))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( k1_relat_1(k7_relat_1(sK2,sK1)) != sK1
    & r1_tarski(sK1,k1_relat_1(sK2))
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f14,f22])).

fof(f37,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f38,plain,(
    r1_tarski(sK1,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f23])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(nnf_transformation,[],[f2])).

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

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f33,f32])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f28,f40])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f30,f40])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f31,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f47,plain,(
    ! [X0] : k1_setfam_1(k1_enumset1(X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f31,f40])).

fof(f39,plain,(
    k1_relat_1(k7_relat_1(sK2,sK1)) != sK1 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_relat_1(X2))
    | r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_13,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_159,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_relat_1(X2))
    | r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_13])).

cnf(c_160,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k1_relat_1(k7_relat_1(sK2,X1)))
    | ~ r2_hidden(X0,k1_relat_1(sK2)) ),
    inference(unflattening,[status(thm)],[c_159])).

cnf(c_1569,plain,
    ( ~ r2_hidden(sK0(sK1,X0,k1_relat_1(k7_relat_1(sK2,sK1))),X1)
    | r2_hidden(sK0(sK1,X0,k1_relat_1(k7_relat_1(sK2,sK1))),k1_relat_1(k7_relat_1(sK2,X1)))
    | ~ r2_hidden(sK0(sK1,X0,k1_relat_1(k7_relat_1(sK2,sK1))),k1_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_160])).

cnf(c_1571,plain,
    ( r2_hidden(sK0(sK1,sK1,k1_relat_1(k7_relat_1(sK2,sK1))),k1_relat_1(k7_relat_1(sK2,sK1)))
    | ~ r2_hidden(sK0(sK1,sK1,k1_relat_1(k7_relat_1(sK2,sK1))),k1_relat_1(sK2))
    | ~ r2_hidden(sK0(sK1,sK1,k1_relat_1(k7_relat_1(sK2,sK1))),sK1) ),
    inference(instantiation,[status(thm)],[c_1569])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_12,negated_conjecture,
    ( r1_tarski(sK1,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_132,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | k1_relat_1(sK2) != X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_12])).

cnf(c_133,plain,
    ( r2_hidden(X0,k1_relat_1(sK2))
    | ~ r2_hidden(X0,sK1) ),
    inference(unflattening,[status(thm)],[c_132])).

cnf(c_1089,plain,
    ( r2_hidden(sK0(sK1,X0,k1_relat_1(k7_relat_1(sK2,sK1))),k1_relat_1(sK2))
    | ~ r2_hidden(sK0(sK1,X0,k1_relat_1(k7_relat_1(sK2,sK1))),sK1) ),
    inference(instantiation,[status(thm)],[c_133])).

cnf(c_1093,plain,
    ( r2_hidden(sK0(sK1,sK1,k1_relat_1(k7_relat_1(sK2,sK1))),k1_relat_1(sK2))
    | ~ r2_hidden(sK0(sK1,sK1,k1_relat_1(k7_relat_1(sK2,sK1))),sK1) ),
    inference(instantiation,[status(thm)],[c_1089])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0,X1,X2),X0)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k1_setfam_1(k1_enumset1(X0,X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_451,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = X2
    | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_10,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_147,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_13])).

cnf(c_148,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(sK2,X1))) ),
    inference(unflattening,[status(thm)],[c_147])).

cnf(c_446,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k1_relat_1(k7_relat_1(sK2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_148])).

cnf(c_742,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k1_relat_1(k7_relat_1(sK2,X2))
    | r2_hidden(sK0(X0,X1,k1_relat_1(k7_relat_1(sK2,X2))),X0) = iProver_top
    | r2_hidden(sK0(X0,X1,k1_relat_1(k7_relat_1(sK2,X2))),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_451,c_446])).

cnf(c_809,plain,
    ( r2_hidden(sK0(X0,X1,k1_relat_1(k7_relat_1(sK2,X2))),X0)
    | r2_hidden(sK0(X0,X1,k1_relat_1(k7_relat_1(sK2,X2))),X2)
    | k1_setfam_1(k1_enumset1(X0,X0,X1)) = k1_relat_1(k7_relat_1(sK2,X2)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_742])).

cnf(c_811,plain,
    ( r2_hidden(sK0(sK1,sK1,k1_relat_1(k7_relat_1(sK2,sK1))),sK1)
    | k1_setfam_1(k1_enumset1(sK1,sK1,sK1)) = k1_relat_1(k7_relat_1(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_809])).

cnf(c_270,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_694,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,X1)) != X2
    | sK1 != X2
    | sK1 = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(instantiation,[status(thm)],[c_270])).

cnf(c_695,plain,
    ( k1_setfam_1(k1_enumset1(sK1,sK1,sK1)) != sK1
    | sK1 = k1_setfam_1(k1_enumset1(sK1,sK1,sK1))
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_694])).

cnf(c_531,plain,
    ( k1_relat_1(k7_relat_1(sK2,sK1)) != X0
    | k1_relat_1(k7_relat_1(sK2,sK1)) = sK1
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_270])).

cnf(c_684,plain,
    ( k1_relat_1(k7_relat_1(sK2,sK1)) != k1_setfam_1(k1_enumset1(X0,X0,X1))
    | k1_relat_1(k7_relat_1(sK2,sK1)) = sK1
    | sK1 != k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(instantiation,[status(thm)],[c_531])).

cnf(c_685,plain,
    ( k1_relat_1(k7_relat_1(sK2,sK1)) != k1_setfam_1(k1_enumset1(sK1,sK1,sK1))
    | k1_relat_1(k7_relat_1(sK2,sK1)) = sK1
    | sK1 != k1_setfam_1(k1_enumset1(sK1,sK1,sK1)) ),
    inference(instantiation,[status(thm)],[c_684])).

cnf(c_1,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X1)
    | ~ r2_hidden(sK0(X0,X1,X2),X0)
    | ~ r2_hidden(sK0(X0,X1,X2),X2)
    | k1_setfam_1(k1_enumset1(X0,X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_588,plain,
    ( ~ r2_hidden(sK0(X0,X1,k1_relat_1(k7_relat_1(sK2,sK1))),X1)
    | ~ r2_hidden(sK0(X0,X1,k1_relat_1(k7_relat_1(sK2,sK1))),X0)
    | ~ r2_hidden(sK0(X0,X1,k1_relat_1(k7_relat_1(sK2,sK1))),k1_relat_1(k7_relat_1(sK2,sK1)))
    | k1_setfam_1(k1_enumset1(X0,X0,X1)) = k1_relat_1(k7_relat_1(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_599,plain,
    ( ~ r2_hidden(sK0(sK1,sK1,k1_relat_1(k7_relat_1(sK2,sK1))),k1_relat_1(k7_relat_1(sK2,sK1)))
    | ~ r2_hidden(sK0(sK1,sK1,k1_relat_1(k7_relat_1(sK2,sK1))),sK1)
    | k1_setfam_1(k1_enumset1(sK1,sK1,sK1)) = k1_relat_1(k7_relat_1(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_588])).

cnf(c_538,plain,
    ( X0 != X1
    | k1_relat_1(k7_relat_1(sK2,sK1)) != X1
    | k1_relat_1(k7_relat_1(sK2,sK1)) = X0 ),
    inference(instantiation,[status(thm)],[c_270])).

cnf(c_564,plain,
    ( X0 != k1_relat_1(k7_relat_1(sK2,sK1))
    | k1_relat_1(k7_relat_1(sK2,sK1)) = X0
    | k1_relat_1(k7_relat_1(sK2,sK1)) != k1_relat_1(k7_relat_1(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_538])).

cnf(c_587,plain,
    ( k1_relat_1(k7_relat_1(sK2,sK1)) != k1_relat_1(k7_relat_1(sK2,sK1))
    | k1_relat_1(k7_relat_1(sK2,sK1)) = k1_setfam_1(k1_enumset1(X0,X0,X1))
    | k1_setfam_1(k1_enumset1(X0,X0,X1)) != k1_relat_1(k7_relat_1(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_564])).

cnf(c_591,plain,
    ( k1_relat_1(k7_relat_1(sK2,sK1)) != k1_relat_1(k7_relat_1(sK2,sK1))
    | k1_relat_1(k7_relat_1(sK2,sK1)) = k1_setfam_1(k1_enumset1(sK1,sK1,sK1))
    | k1_setfam_1(k1_enumset1(sK1,sK1,sK1)) != k1_relat_1(k7_relat_1(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_587])).

cnf(c_269,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_537,plain,
    ( k1_relat_1(k7_relat_1(sK2,sK1)) = k1_relat_1(k7_relat_1(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_269])).

cnf(c_280,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_269])).

cnf(c_7,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_25,plain,
    ( k1_setfam_1(k1_enumset1(sK1,sK1,sK1)) = sK1 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_11,negated_conjecture,
    ( k1_relat_1(k7_relat_1(sK2,sK1)) != sK1 ),
    inference(cnf_transformation,[],[f39])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1571,c_1093,c_811,c_695,c_685,c_599,c_591,c_537,c_280,c_25,c_11])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : iproveropt_run.sh %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:41:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  % Running in FOF mode
% 0.36/1.03  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.36/1.03  
% 0.36/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.36/1.03  
% 0.36/1.03  ------  iProver source info
% 0.36/1.03  
% 0.36/1.03  git: date: 2020-06-30 10:37:57 +0100
% 0.36/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.36/1.03  git: non_committed_changes: false
% 0.36/1.03  git: last_make_outside_of_git: false
% 0.36/1.03  
% 0.36/1.03  ------ 
% 0.36/1.03  
% 0.36/1.03  ------ Input Options
% 0.36/1.03  
% 0.36/1.03  --out_options                           all
% 0.36/1.03  --tptp_safe_out                         true
% 0.36/1.03  --problem_path                          ""
% 0.36/1.03  --include_path                          ""
% 0.36/1.03  --clausifier                            res/vclausify_rel
% 0.36/1.03  --clausifier_options                    --mode clausify
% 0.36/1.03  --stdin                                 false
% 0.36/1.03  --stats_out                             all
% 0.36/1.03  
% 0.36/1.03  ------ General Options
% 0.36/1.03  
% 0.36/1.03  --fof                                   false
% 0.36/1.03  --time_out_real                         305.
% 0.36/1.03  --time_out_virtual                      -1.
% 0.36/1.03  --symbol_type_check                     false
% 0.36/1.03  --clausify_out                          false
% 0.36/1.03  --sig_cnt_out                           false
% 0.36/1.03  --trig_cnt_out                          false
% 0.36/1.03  --trig_cnt_out_tolerance                1.
% 0.36/1.03  --trig_cnt_out_sk_spl                   false
% 0.36/1.03  --abstr_cl_out                          false
% 0.36/1.03  
% 0.36/1.03  ------ Global Options
% 0.36/1.03  
% 0.36/1.03  --schedule                              default
% 0.36/1.03  --add_important_lit                     false
% 0.36/1.03  --prop_solver_per_cl                    1000
% 0.36/1.03  --min_unsat_core                        false
% 0.36/1.03  --soft_assumptions                      false
% 0.36/1.03  --soft_lemma_size                       3
% 0.36/1.03  --prop_impl_unit_size                   0
% 0.36/1.03  --prop_impl_unit                        []
% 0.36/1.03  --share_sel_clauses                     true
% 0.36/1.03  --reset_solvers                         false
% 0.36/1.03  --bc_imp_inh                            [conj_cone]
% 0.36/1.03  --conj_cone_tolerance                   3.
% 0.36/1.03  --extra_neg_conj                        none
% 0.36/1.03  --large_theory_mode                     true
% 0.36/1.03  --prolific_symb_bound                   200
% 0.36/1.03  --lt_threshold                          2000
% 0.36/1.03  --clause_weak_htbl                      true
% 0.36/1.03  --gc_record_bc_elim                     false
% 0.36/1.03  
% 0.36/1.03  ------ Preprocessing Options
% 0.36/1.03  
% 0.36/1.03  --preprocessing_flag                    true
% 0.36/1.03  --time_out_prep_mult                    0.1
% 0.36/1.03  --splitting_mode                        input
% 0.36/1.03  --splitting_grd                         true
% 0.36/1.03  --splitting_cvd                         false
% 0.36/1.03  --splitting_cvd_svl                     false
% 0.36/1.03  --splitting_nvd                         32
% 0.36/1.03  --sub_typing                            true
% 0.36/1.03  --prep_gs_sim                           true
% 0.36/1.03  --prep_unflatten                        true
% 0.36/1.03  --prep_res_sim                          true
% 0.36/1.03  --prep_upred                            true
% 0.36/1.03  --prep_sem_filter                       exhaustive
% 0.36/1.03  --prep_sem_filter_out                   false
% 0.36/1.03  --pred_elim                             true
% 0.36/1.03  --res_sim_input                         true
% 0.36/1.03  --eq_ax_congr_red                       true
% 0.36/1.03  --pure_diseq_elim                       true
% 0.36/1.03  --brand_transform                       false
% 0.36/1.03  --non_eq_to_eq                          false
% 0.36/1.03  --prep_def_merge                        true
% 0.36/1.03  --prep_def_merge_prop_impl              false
% 0.36/1.03  --prep_def_merge_mbd                    true
% 0.36/1.03  --prep_def_merge_tr_red                 false
% 0.36/1.03  --prep_def_merge_tr_cl                  false
% 0.36/1.03  --smt_preprocessing                     true
% 0.36/1.03  --smt_ac_axioms                         fast
% 0.36/1.03  --preprocessed_out                      false
% 0.36/1.03  --preprocessed_stats                    false
% 0.36/1.03  
% 0.36/1.03  ------ Abstraction refinement Options
% 0.36/1.03  
% 0.36/1.03  --abstr_ref                             []
% 0.36/1.03  --abstr_ref_prep                        false
% 0.36/1.03  --abstr_ref_until_sat                   false
% 0.36/1.03  --abstr_ref_sig_restrict                funpre
% 0.36/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 0.36/1.03  --abstr_ref_under                       []
% 0.36/1.03  
% 0.36/1.03  ------ SAT Options
% 0.36/1.03  
% 0.36/1.03  --sat_mode                              false
% 0.36/1.03  --sat_fm_restart_options                ""
% 0.36/1.03  --sat_gr_def                            false
% 0.36/1.03  --sat_epr_types                         true
% 0.36/1.03  --sat_non_cyclic_types                  false
% 0.36/1.03  --sat_finite_models                     false
% 0.36/1.03  --sat_fm_lemmas                         false
% 0.36/1.03  --sat_fm_prep                           false
% 0.36/1.03  --sat_fm_uc_incr                        true
% 0.36/1.03  --sat_out_model                         small
% 0.36/1.03  --sat_out_clauses                       false
% 0.36/1.03  
% 0.36/1.03  ------ QBF Options
% 0.36/1.03  
% 0.36/1.03  --qbf_mode                              false
% 0.36/1.03  --qbf_elim_univ                         false
% 0.36/1.03  --qbf_dom_inst                          none
% 0.36/1.03  --qbf_dom_pre_inst                      false
% 0.36/1.03  --qbf_sk_in                             false
% 0.36/1.03  --qbf_pred_elim                         true
% 0.36/1.03  --qbf_split                             512
% 0.36/1.03  
% 0.36/1.03  ------ BMC1 Options
% 0.36/1.03  
% 0.36/1.03  --bmc1_incremental                      false
% 0.36/1.03  --bmc1_axioms                           reachable_all
% 0.36/1.03  --bmc1_min_bound                        0
% 0.36/1.03  --bmc1_max_bound                        -1
% 0.36/1.03  --bmc1_max_bound_default                -1
% 0.36/1.03  --bmc1_symbol_reachability              true
% 0.36/1.03  --bmc1_property_lemmas                  false
% 0.36/1.03  --bmc1_k_induction                      false
% 0.36/1.03  --bmc1_non_equiv_states                 false
% 0.36/1.03  --bmc1_deadlock                         false
% 0.36/1.03  --bmc1_ucm                              false
% 0.36/1.03  --bmc1_add_unsat_core                   none
% 0.36/1.03  --bmc1_unsat_core_children              false
% 0.36/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 0.36/1.03  --bmc1_out_stat                         full
% 0.36/1.03  --bmc1_ground_init                      false
% 0.36/1.03  --bmc1_pre_inst_next_state              false
% 0.36/1.03  --bmc1_pre_inst_state                   false
% 0.36/1.03  --bmc1_pre_inst_reach_state             false
% 0.36/1.03  --bmc1_out_unsat_core                   false
% 0.36/1.03  --bmc1_aig_witness_out                  false
% 0.36/1.03  --bmc1_verbose                          false
% 0.36/1.03  --bmc1_dump_clauses_tptp                false
% 0.36/1.03  --bmc1_dump_unsat_core_tptp             false
% 0.36/1.03  --bmc1_dump_file                        -
% 0.36/1.03  --bmc1_ucm_expand_uc_limit              128
% 0.36/1.03  --bmc1_ucm_n_expand_iterations          6
% 0.36/1.03  --bmc1_ucm_extend_mode                  1
% 0.36/1.03  --bmc1_ucm_init_mode                    2
% 0.36/1.03  --bmc1_ucm_cone_mode                    none
% 0.36/1.03  --bmc1_ucm_reduced_relation_type        0
% 0.36/1.03  --bmc1_ucm_relax_model                  4
% 0.36/1.03  --bmc1_ucm_full_tr_after_sat            true
% 0.36/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 0.36/1.03  --bmc1_ucm_layered_model                none
% 0.36/1.03  --bmc1_ucm_max_lemma_size               10
% 0.36/1.03  
% 0.36/1.03  ------ AIG Options
% 0.36/1.03  
% 0.36/1.03  --aig_mode                              false
% 0.36/1.03  
% 0.36/1.03  ------ Instantiation Options
% 0.36/1.03  
% 0.36/1.03  --instantiation_flag                    true
% 0.36/1.03  --inst_sos_flag                         false
% 0.36/1.03  --inst_sos_phase                        true
% 0.36/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.36/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.36/1.03  --inst_lit_sel_side                     num_symb
% 0.36/1.03  --inst_solver_per_active                1400
% 0.36/1.03  --inst_solver_calls_frac                1.
% 0.36/1.03  --inst_passive_queue_type               priority_queues
% 0.36/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.36/1.03  --inst_passive_queues_freq              [25;2]
% 0.36/1.03  --inst_dismatching                      true
% 0.36/1.03  --inst_eager_unprocessed_to_passive     true
% 0.36/1.03  --inst_prop_sim_given                   true
% 0.36/1.03  --inst_prop_sim_new                     false
% 0.36/1.03  --inst_subs_new                         false
% 0.36/1.03  --inst_eq_res_simp                      false
% 0.36/1.03  --inst_subs_given                       false
% 0.36/1.03  --inst_orphan_elimination               true
% 0.36/1.03  --inst_learning_loop_flag               true
% 0.36/1.03  --inst_learning_start                   3000
% 0.36/1.03  --inst_learning_factor                  2
% 0.36/1.03  --inst_start_prop_sim_after_learn       3
% 0.36/1.03  --inst_sel_renew                        solver
% 0.36/1.03  --inst_lit_activity_flag                true
% 0.36/1.03  --inst_restr_to_given                   false
% 0.36/1.03  --inst_activity_threshold               500
% 0.36/1.03  --inst_out_proof                        true
% 0.36/1.03  
% 0.36/1.03  ------ Resolution Options
% 0.36/1.03  
% 0.36/1.03  --resolution_flag                       true
% 0.36/1.03  --res_lit_sel                           adaptive
% 0.36/1.03  --res_lit_sel_side                      none
% 0.36/1.03  --res_ordering                          kbo
% 0.36/1.03  --res_to_prop_solver                    active
% 0.36/1.03  --res_prop_simpl_new                    false
% 0.36/1.03  --res_prop_simpl_given                  true
% 0.36/1.03  --res_passive_queue_type                priority_queues
% 0.36/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.36/1.03  --res_passive_queues_freq               [15;5]
% 0.36/1.03  --res_forward_subs                      full
% 0.36/1.03  --res_backward_subs                     full
% 0.36/1.03  --res_forward_subs_resolution           true
% 0.36/1.03  --res_backward_subs_resolution          true
% 0.36/1.03  --res_orphan_elimination                true
% 0.36/1.03  --res_time_limit                        2.
% 0.36/1.03  --res_out_proof                         true
% 0.36/1.03  
% 0.36/1.03  ------ Superposition Options
% 0.36/1.03  
% 0.36/1.03  --superposition_flag                    true
% 0.36/1.03  --sup_passive_queue_type                priority_queues
% 0.36/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.36/1.03  --sup_passive_queues_freq               [8;1;4]
% 0.36/1.03  --demod_completeness_check              fast
% 0.36/1.03  --demod_use_ground                      true
% 0.36/1.03  --sup_to_prop_solver                    passive
% 0.36/1.03  --sup_prop_simpl_new                    true
% 0.36/1.03  --sup_prop_simpl_given                  true
% 0.36/1.03  --sup_fun_splitting                     false
% 0.36/1.03  --sup_smt_interval                      50000
% 0.36/1.03  
% 0.36/1.03  ------ Superposition Simplification Setup
% 0.36/1.03  
% 0.36/1.03  --sup_indices_passive                   []
% 0.36/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.36/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.36/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.36/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 0.36/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.36/1.03  --sup_full_bw                           [BwDemod]
% 0.36/1.03  --sup_immed_triv                        [TrivRules]
% 0.36/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.36/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.36/1.03  --sup_immed_bw_main                     []
% 0.36/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.36/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 0.36/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.36/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.36/1.03  
% 0.36/1.03  ------ Combination Options
% 0.36/1.03  
% 0.36/1.03  --comb_res_mult                         3
% 0.36/1.03  --comb_sup_mult                         2
% 0.36/1.03  --comb_inst_mult                        10
% 0.36/1.03  
% 0.36/1.03  ------ Debug Options
% 0.36/1.03  
% 0.36/1.03  --dbg_backtrace                         false
% 0.36/1.03  --dbg_dump_prop_clauses                 false
% 0.36/1.03  --dbg_dump_prop_clauses_file            -
% 0.36/1.03  --dbg_out_stat                          false
% 0.36/1.03  ------ Parsing...
% 0.36/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.36/1.03  
% 0.36/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 0.36/1.03  
% 0.36/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.36/1.03  
% 0.36/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.36/1.03  ------ Proving...
% 0.36/1.03  ------ Problem Properties 
% 0.36/1.03  
% 0.36/1.03  
% 0.36/1.03  clauses                                 12
% 0.36/1.03  conjectures                             1
% 0.36/1.04  EPR                                     0
% 0.36/1.04  Horn                                    10
% 0.36/1.04  unary                                   2
% 0.36/1.04  binary                                  5
% 0.36/1.04  lits                                    28
% 0.36/1.04  lits eq                                 5
% 0.36/1.04  fd_pure                                 0
% 0.36/1.04  fd_pseudo                               0
% 0.36/1.04  fd_cond                                 0
% 0.36/1.04  fd_pseudo_cond                          3
% 0.36/1.04  AC symbols                              0
% 0.36/1.04  
% 0.36/1.04  ------ Schedule dynamic 5 is on 
% 0.36/1.04  
% 0.36/1.04  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.36/1.04  
% 0.36/1.04  
% 0.36/1.04  ------ 
% 0.36/1.04  Current options:
% 0.36/1.04  ------ 
% 0.36/1.04  
% 0.36/1.04  ------ Input Options
% 0.36/1.04  
% 0.36/1.04  --out_options                           all
% 0.36/1.04  --tptp_safe_out                         true
% 0.36/1.04  --problem_path                          ""
% 0.36/1.04  --include_path                          ""
% 0.36/1.04  --clausifier                            res/vclausify_rel
% 0.36/1.04  --clausifier_options                    --mode clausify
% 0.36/1.04  --stdin                                 false
% 0.36/1.04  --stats_out                             all
% 0.36/1.04  
% 0.36/1.04  ------ General Options
% 0.36/1.04  
% 0.36/1.04  --fof                                   false
% 0.36/1.04  --time_out_real                         305.
% 0.36/1.04  --time_out_virtual                      -1.
% 0.36/1.04  --symbol_type_check                     false
% 0.36/1.04  --clausify_out                          false
% 0.36/1.04  --sig_cnt_out                           false
% 0.36/1.04  --trig_cnt_out                          false
% 0.36/1.04  --trig_cnt_out_tolerance                1.
% 0.36/1.04  --trig_cnt_out_sk_spl                   false
% 0.36/1.04  --abstr_cl_out                          false
% 0.36/1.04  
% 0.36/1.04  ------ Global Options
% 0.36/1.04  
% 0.36/1.04  --schedule                              default
% 0.36/1.04  --add_important_lit                     false
% 0.36/1.04  --prop_solver_per_cl                    1000
% 0.36/1.04  --min_unsat_core                        false
% 0.36/1.04  --soft_assumptions                      false
% 0.36/1.04  --soft_lemma_size                       3
% 0.36/1.04  --prop_impl_unit_size                   0
% 0.36/1.04  --prop_impl_unit                        []
% 0.36/1.04  --share_sel_clauses                     true
% 0.36/1.04  --reset_solvers                         false
% 0.36/1.04  --bc_imp_inh                            [conj_cone]
% 0.36/1.04  --conj_cone_tolerance                   3.
% 0.36/1.04  --extra_neg_conj                        none
% 0.36/1.04  --large_theory_mode                     true
% 0.36/1.04  --prolific_symb_bound                   200
% 0.36/1.04  --lt_threshold                          2000
% 0.36/1.04  --clause_weak_htbl                      true
% 0.36/1.04  --gc_record_bc_elim                     false
% 0.36/1.04  
% 0.36/1.04  ------ Preprocessing Options
% 0.36/1.04  
% 0.36/1.04  --preprocessing_flag                    true
% 0.36/1.04  --time_out_prep_mult                    0.1
% 0.36/1.04  --splitting_mode                        input
% 0.36/1.04  --splitting_grd                         true
% 0.36/1.04  --splitting_cvd                         false
% 0.36/1.04  --splitting_cvd_svl                     false
% 0.36/1.04  --splitting_nvd                         32
% 0.36/1.04  --sub_typing                            true
% 0.36/1.04  --prep_gs_sim                           true
% 0.36/1.04  --prep_unflatten                        true
% 0.36/1.04  --prep_res_sim                          true
% 0.36/1.04  --prep_upred                            true
% 0.36/1.04  --prep_sem_filter                       exhaustive
% 0.36/1.04  --prep_sem_filter_out                   false
% 0.36/1.04  --pred_elim                             true
% 0.36/1.04  --res_sim_input                         true
% 0.36/1.04  --eq_ax_congr_red                       true
% 0.36/1.04  --pure_diseq_elim                       true
% 0.36/1.04  --brand_transform                       false
% 0.36/1.04  --non_eq_to_eq                          false
% 0.36/1.04  --prep_def_merge                        true
% 0.36/1.04  --prep_def_merge_prop_impl              false
% 0.36/1.04  --prep_def_merge_mbd                    true
% 0.36/1.04  --prep_def_merge_tr_red                 false
% 0.36/1.04  --prep_def_merge_tr_cl                  false
% 0.36/1.04  --smt_preprocessing                     true
% 0.36/1.04  --smt_ac_axioms                         fast
% 0.36/1.04  --preprocessed_out                      false
% 0.36/1.04  --preprocessed_stats                    false
% 0.36/1.04  
% 0.36/1.04  ------ Abstraction refinement Options
% 0.36/1.04  
% 0.36/1.04  --abstr_ref                             []
% 0.36/1.04  --abstr_ref_prep                        false
% 0.36/1.04  --abstr_ref_until_sat                   false
% 0.36/1.04  --abstr_ref_sig_restrict                funpre
% 0.36/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 0.36/1.04  --abstr_ref_under                       []
% 0.36/1.04  
% 0.36/1.04  ------ SAT Options
% 0.36/1.04  
% 0.36/1.04  --sat_mode                              false
% 0.36/1.04  --sat_fm_restart_options                ""
% 0.36/1.04  --sat_gr_def                            false
% 0.36/1.04  --sat_epr_types                         true
% 0.36/1.04  --sat_non_cyclic_types                  false
% 0.36/1.04  --sat_finite_models                     false
% 0.36/1.04  --sat_fm_lemmas                         false
% 0.36/1.04  --sat_fm_prep                           false
% 0.36/1.04  --sat_fm_uc_incr                        true
% 0.36/1.04  --sat_out_model                         small
% 0.36/1.04  --sat_out_clauses                       false
% 0.36/1.04  
% 0.36/1.04  ------ QBF Options
% 0.36/1.04  
% 0.36/1.04  --qbf_mode                              false
% 0.36/1.04  --qbf_elim_univ                         false
% 0.36/1.04  --qbf_dom_inst                          none
% 0.36/1.04  --qbf_dom_pre_inst                      false
% 0.36/1.04  --qbf_sk_in                             false
% 0.36/1.04  --qbf_pred_elim                         true
% 0.36/1.04  --qbf_split                             512
% 0.36/1.04  
% 0.36/1.04  ------ BMC1 Options
% 0.36/1.04  
% 0.36/1.04  --bmc1_incremental                      false
% 0.36/1.04  --bmc1_axioms                           reachable_all
% 0.36/1.04  --bmc1_min_bound                        0
% 0.36/1.04  --bmc1_max_bound                        -1
% 0.36/1.04  --bmc1_max_bound_default                -1
% 0.36/1.04  --bmc1_symbol_reachability              true
% 0.36/1.04  --bmc1_property_lemmas                  false
% 0.36/1.04  --bmc1_k_induction                      false
% 0.36/1.04  --bmc1_non_equiv_states                 false
% 0.36/1.04  --bmc1_deadlock                         false
% 0.36/1.04  --bmc1_ucm                              false
% 0.36/1.04  --bmc1_add_unsat_core                   none
% 0.36/1.04  --bmc1_unsat_core_children              false
% 0.36/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 0.36/1.04  --bmc1_out_stat                         full
% 0.36/1.04  --bmc1_ground_init                      false
% 0.36/1.04  --bmc1_pre_inst_next_state              false
% 0.36/1.04  --bmc1_pre_inst_state                   false
% 0.36/1.04  --bmc1_pre_inst_reach_state             false
% 0.36/1.04  --bmc1_out_unsat_core                   false
% 0.36/1.04  --bmc1_aig_witness_out                  false
% 0.36/1.04  --bmc1_verbose                          false
% 0.36/1.04  --bmc1_dump_clauses_tptp                false
% 0.36/1.04  --bmc1_dump_unsat_core_tptp             false
% 0.36/1.04  --bmc1_dump_file                        -
% 0.36/1.04  --bmc1_ucm_expand_uc_limit              128
% 0.36/1.04  --bmc1_ucm_n_expand_iterations          6
% 0.36/1.04  --bmc1_ucm_extend_mode                  1
% 0.36/1.04  --bmc1_ucm_init_mode                    2
% 0.36/1.04  --bmc1_ucm_cone_mode                    none
% 0.36/1.04  --bmc1_ucm_reduced_relation_type        0
% 0.36/1.04  --bmc1_ucm_relax_model                  4
% 0.36/1.04  --bmc1_ucm_full_tr_after_sat            true
% 0.36/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 0.36/1.04  --bmc1_ucm_layered_model                none
% 0.36/1.04  --bmc1_ucm_max_lemma_size               10
% 0.36/1.04  
% 0.36/1.04  ------ AIG Options
% 0.36/1.04  
% 0.36/1.04  --aig_mode                              false
% 0.36/1.04  
% 0.36/1.04  ------ Instantiation Options
% 0.36/1.04  
% 0.36/1.04  --instantiation_flag                    true
% 0.36/1.04  --inst_sos_flag                         false
% 0.36/1.04  --inst_sos_phase                        true
% 0.36/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.36/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.36/1.04  --inst_lit_sel_side                     none
% 0.36/1.04  --inst_solver_per_active                1400
% 0.36/1.04  --inst_solver_calls_frac                1.
% 0.36/1.04  --inst_passive_queue_type               priority_queues
% 0.36/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.36/1.04  --inst_passive_queues_freq              [25;2]
% 0.36/1.04  --inst_dismatching                      true
% 0.36/1.04  --inst_eager_unprocessed_to_passive     true
% 0.36/1.04  --inst_prop_sim_given                   true
% 0.36/1.04  --inst_prop_sim_new                     false
% 0.36/1.04  --inst_subs_new                         false
% 0.36/1.04  --inst_eq_res_simp                      false
% 0.36/1.04  --inst_subs_given                       false
% 0.36/1.04  --inst_orphan_elimination               true
% 0.36/1.04  --inst_learning_loop_flag               true
% 0.36/1.04  --inst_learning_start                   3000
% 0.36/1.04  --inst_learning_factor                  2
% 0.36/1.04  --inst_start_prop_sim_after_learn       3
% 0.36/1.04  --inst_sel_renew                        solver
% 0.36/1.04  --inst_lit_activity_flag                true
% 0.36/1.04  --inst_restr_to_given                   false
% 0.36/1.04  --inst_activity_threshold               500
% 0.36/1.04  --inst_out_proof                        true
% 0.36/1.04  
% 0.36/1.04  ------ Resolution Options
% 0.36/1.04  
% 0.36/1.04  --resolution_flag                       false
% 0.36/1.04  --res_lit_sel                           adaptive
% 0.36/1.04  --res_lit_sel_side                      none
% 0.36/1.04  --res_ordering                          kbo
% 0.36/1.04  --res_to_prop_solver                    active
% 0.36/1.04  --res_prop_simpl_new                    false
% 0.36/1.04  --res_prop_simpl_given                  true
% 0.36/1.04  --res_passive_queue_type                priority_queues
% 0.36/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.36/1.04  --res_passive_queues_freq               [15;5]
% 0.36/1.04  --res_forward_subs                      full
% 0.36/1.04  --res_backward_subs                     full
% 0.36/1.04  --res_forward_subs_resolution           true
% 0.36/1.04  --res_backward_subs_resolution          true
% 0.36/1.04  --res_orphan_elimination                true
% 0.36/1.04  --res_time_limit                        2.
% 0.36/1.04  --res_out_proof                         true
% 0.36/1.04  
% 0.36/1.04  ------ Superposition Options
% 0.36/1.04  
% 0.36/1.04  --superposition_flag                    true
% 0.36/1.04  --sup_passive_queue_type                priority_queues
% 0.36/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.36/1.04  --sup_passive_queues_freq               [8;1;4]
% 0.36/1.04  --demod_completeness_check              fast
% 0.36/1.04  --demod_use_ground                      true
% 0.36/1.04  --sup_to_prop_solver                    passive
% 0.36/1.04  --sup_prop_simpl_new                    true
% 0.36/1.04  --sup_prop_simpl_given                  true
% 0.36/1.04  --sup_fun_splitting                     false
% 0.36/1.04  --sup_smt_interval                      50000
% 0.36/1.04  
% 0.36/1.04  ------ Superposition Simplification Setup
% 0.36/1.04  
% 0.36/1.04  --sup_indices_passive                   []
% 0.36/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.36/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.36/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.36/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 0.36/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.36/1.04  --sup_full_bw                           [BwDemod]
% 0.36/1.04  --sup_immed_triv                        [TrivRules]
% 0.36/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.36/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.36/1.04  --sup_immed_bw_main                     []
% 0.36/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.36/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 0.36/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.36/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.36/1.04  
% 0.36/1.04  ------ Combination Options
% 0.36/1.04  
% 0.36/1.04  --comb_res_mult                         3
% 0.36/1.04  --comb_sup_mult                         2
% 0.36/1.04  --comb_inst_mult                        10
% 0.36/1.04  
% 0.36/1.04  ------ Debug Options
% 0.36/1.04  
% 0.36/1.04  --dbg_backtrace                         false
% 0.36/1.04  --dbg_dump_prop_clauses                 false
% 0.36/1.04  --dbg_dump_prop_clauses_file            -
% 0.36/1.04  --dbg_out_stat                          false
% 0.36/1.04  
% 0.36/1.04  
% 0.36/1.04  
% 0.36/1.04  
% 0.36/1.04  ------ Proving...
% 0.36/1.04  
% 0.36/1.04  
% 0.36/1.04  % SZS status Theorem for theBenchmark.p
% 0.36/1.04  
% 0.36/1.04  % SZS output start CNFRefutation for theBenchmark.p
% 0.36/1.04  
% 0.36/1.04  fof(f6,axiom,(
% 0.36/1.04    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))))),
% 0.36/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.36/1.04  
% 0.36/1.04  fof(f12,plain,(
% 0.36/1.04    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))) | ~v1_relat_1(X2))),
% 0.36/1.04    inference(ennf_transformation,[],[f6])).
% 0.36/1.04  
% 0.36/1.04  fof(f20,plain,(
% 0.36/1.04    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | (~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1))) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 0.36/1.04    inference(nnf_transformation,[],[f12])).
% 0.36/1.04  
% 0.36/1.04  fof(f21,plain,(
% 0.36/1.04    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1)) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 0.36/1.04    inference(flattening,[],[f20])).
% 0.36/1.04  
% 0.36/1.04  fof(f36,plain,(
% 0.36/1.04    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1) | ~v1_relat_1(X2)) )),
% 0.36/1.04    inference(cnf_transformation,[],[f21])).
% 0.36/1.04  
% 0.36/1.04  fof(f7,conjecture,(
% 0.36/1.04    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 0.36/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.36/1.04  
% 0.36/1.04  fof(f8,negated_conjecture,(
% 0.36/1.04    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 0.36/1.04    inference(negated_conjecture,[],[f7])).
% 0.36/1.04  
% 0.36/1.04  fof(f13,plain,(
% 0.36/1.04    ? [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) != X0 & r1_tarski(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 0.36/1.04    inference(ennf_transformation,[],[f8])).
% 0.36/1.04  
% 0.36/1.04  fof(f14,plain,(
% 0.36/1.04    ? [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) != X0 & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1))),
% 0.36/1.04    inference(flattening,[],[f13])).
% 0.36/1.04  
% 0.36/1.04  fof(f22,plain,(
% 0.36/1.04    ? [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) != X0 & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1)) => (k1_relat_1(k7_relat_1(sK2,sK1)) != sK1 & r1_tarski(sK1,k1_relat_1(sK2)) & v1_relat_1(sK2))),
% 0.36/1.04    introduced(choice_axiom,[])).
% 0.36/1.04  
% 0.36/1.04  fof(f23,plain,(
% 0.36/1.04    k1_relat_1(k7_relat_1(sK2,sK1)) != sK1 & r1_tarski(sK1,k1_relat_1(sK2)) & v1_relat_1(sK2)),
% 0.36/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f14,f22])).
% 0.36/1.04  
% 0.36/1.04  fof(f37,plain,(
% 0.36/1.04    v1_relat_1(sK2)),
% 0.36/1.04    inference(cnf_transformation,[],[f23])).
% 0.36/1.04  
% 0.36/1.04  fof(f1,axiom,(
% 0.36/1.04    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.36/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.36/1.04  
% 0.36/1.04  fof(f10,plain,(
% 0.36/1.04    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.36/1.04    inference(unused_predicate_definition_removal,[],[f1])).
% 0.36/1.04  
% 0.36/1.04  fof(f11,plain,(
% 0.36/1.04    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1))),
% 0.36/1.04    inference(ennf_transformation,[],[f10])).
% 0.36/1.04  
% 0.36/1.04  fof(f24,plain,(
% 0.36/1.04    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 0.36/1.04    inference(cnf_transformation,[],[f11])).
% 0.36/1.04  
% 0.36/1.04  fof(f38,plain,(
% 0.36/1.04    r1_tarski(sK1,k1_relat_1(sK2))),
% 0.36/1.04    inference(cnf_transformation,[],[f23])).
% 0.36/1.04  
% 0.36/1.04  fof(f2,axiom,(
% 0.36/1.04    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.36/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.36/1.04  
% 0.36/1.04  fof(f15,plain,(
% 0.36/1.04    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.36/1.04    inference(nnf_transformation,[],[f2])).
% 0.36/1.04  
% 0.36/1.04  fof(f16,plain,(
% 0.36/1.04    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.36/1.04    inference(flattening,[],[f15])).
% 0.36/1.04  
% 0.36/1.04  fof(f17,plain,(
% 0.36/1.04    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.36/1.04    inference(rectify,[],[f16])).
% 0.36/1.04  
% 0.36/1.04  fof(f18,plain,(
% 0.36/1.04    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 0.36/1.04    introduced(choice_axiom,[])).
% 0.36/1.04  
% 0.36/1.04  fof(f19,plain,(
% 0.36/1.04    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.36/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f18])).
% 0.36/1.04  
% 0.36/1.04  fof(f28,plain,(
% 0.36/1.04    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 0.36/1.04    inference(cnf_transformation,[],[f19])).
% 0.36/1.04  
% 0.36/1.04  fof(f5,axiom,(
% 0.36/1.04    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.36/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.36/1.04  
% 0.36/1.04  fof(f33,plain,(
% 0.36/1.04    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.36/1.04    inference(cnf_transformation,[],[f5])).
% 0.36/1.04  
% 0.36/1.04  fof(f4,axiom,(
% 0.36/1.04    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.36/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.36/1.04  
% 0.36/1.04  fof(f32,plain,(
% 0.36/1.04    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.36/1.04    inference(cnf_transformation,[],[f4])).
% 0.36/1.04  
% 0.36/1.04  fof(f40,plain,(
% 0.36/1.04    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 0.36/1.04    inference(definition_unfolding,[],[f33,f32])).
% 0.36/1.04  
% 0.36/1.04  fof(f43,plain,(
% 0.36/1.04    ( ! [X2,X0,X1] : (k1_setfam_1(k1_enumset1(X0,X0,X1)) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 0.36/1.04    inference(definition_unfolding,[],[f28,f40])).
% 0.36/1.04  
% 0.36/1.04  fof(f34,plain,(
% 0.36/1.04    ( ! [X2,X0,X1] : (r2_hidden(X0,X1) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~v1_relat_1(X2)) )),
% 0.36/1.04    inference(cnf_transformation,[],[f21])).
% 0.36/1.04  
% 0.36/1.04  fof(f30,plain,(
% 0.36/1.04    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 0.36/1.04    inference(cnf_transformation,[],[f19])).
% 0.36/1.04  
% 0.36/1.04  fof(f41,plain,(
% 0.36/1.04    ( ! [X2,X0,X1] : (k1_setfam_1(k1_enumset1(X0,X0,X1)) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 0.36/1.04    inference(definition_unfolding,[],[f30,f40])).
% 0.36/1.04  
% 0.36/1.04  fof(f3,axiom,(
% 0.36/1.04    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 0.36/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.36/1.04  
% 0.36/1.04  fof(f9,plain,(
% 0.36/1.04    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.36/1.04    inference(rectify,[],[f3])).
% 0.36/1.04  
% 0.36/1.04  fof(f31,plain,(
% 0.36/1.04    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.36/1.04    inference(cnf_transformation,[],[f9])).
% 0.36/1.04  
% 0.36/1.04  fof(f47,plain,(
% 0.36/1.04    ( ! [X0] : (k1_setfam_1(k1_enumset1(X0,X0,X0)) = X0) )),
% 0.36/1.04    inference(definition_unfolding,[],[f31,f40])).
% 0.36/1.04  
% 0.36/1.04  fof(f39,plain,(
% 0.36/1.04    k1_relat_1(k7_relat_1(sK2,sK1)) != sK1),
% 0.36/1.04    inference(cnf_transformation,[],[f23])).
% 0.36/1.04  
% 0.36/1.04  cnf(c_8,plain,
% 0.36/1.04      ( ~ r2_hidden(X0,X1)
% 0.36/1.04      | ~ r2_hidden(X0,k1_relat_1(X2))
% 0.36/1.04      | r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
% 0.36/1.04      | ~ v1_relat_1(X2) ),
% 0.36/1.04      inference(cnf_transformation,[],[f36]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_13,negated_conjecture,
% 0.36/1.04      ( v1_relat_1(sK2) ),
% 0.36/1.04      inference(cnf_transformation,[],[f37]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_159,plain,
% 0.36/1.04      ( ~ r2_hidden(X0,X1)
% 0.36/1.04      | ~ r2_hidden(X0,k1_relat_1(X2))
% 0.36/1.04      | r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
% 0.36/1.04      | sK2 != X2 ),
% 0.36/1.04      inference(resolution_lifted,[status(thm)],[c_8,c_13]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_160,plain,
% 0.36/1.04      ( ~ r2_hidden(X0,X1)
% 0.36/1.04      | r2_hidden(X0,k1_relat_1(k7_relat_1(sK2,X1)))
% 0.36/1.04      | ~ r2_hidden(X0,k1_relat_1(sK2)) ),
% 0.36/1.04      inference(unflattening,[status(thm)],[c_159]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_1569,plain,
% 0.36/1.04      ( ~ r2_hidden(sK0(sK1,X0,k1_relat_1(k7_relat_1(sK2,sK1))),X1)
% 0.36/1.04      | r2_hidden(sK0(sK1,X0,k1_relat_1(k7_relat_1(sK2,sK1))),k1_relat_1(k7_relat_1(sK2,X1)))
% 0.36/1.04      | ~ r2_hidden(sK0(sK1,X0,k1_relat_1(k7_relat_1(sK2,sK1))),k1_relat_1(sK2)) ),
% 0.36/1.04      inference(instantiation,[status(thm)],[c_160]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_1571,plain,
% 0.36/1.04      ( r2_hidden(sK0(sK1,sK1,k1_relat_1(k7_relat_1(sK2,sK1))),k1_relat_1(k7_relat_1(sK2,sK1)))
% 0.36/1.04      | ~ r2_hidden(sK0(sK1,sK1,k1_relat_1(k7_relat_1(sK2,sK1))),k1_relat_1(sK2))
% 0.36/1.04      | ~ r2_hidden(sK0(sK1,sK1,k1_relat_1(k7_relat_1(sK2,sK1))),sK1) ),
% 0.36/1.04      inference(instantiation,[status(thm)],[c_1569]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_0,plain,
% 0.36/1.04      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 0.36/1.04      inference(cnf_transformation,[],[f24]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_12,negated_conjecture,
% 0.36/1.04      ( r1_tarski(sK1,k1_relat_1(sK2)) ),
% 0.36/1.04      inference(cnf_transformation,[],[f38]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_132,plain,
% 0.36/1.04      ( ~ r2_hidden(X0,X1)
% 0.36/1.04      | r2_hidden(X0,X2)
% 0.36/1.04      | k1_relat_1(sK2) != X2
% 0.36/1.04      | sK1 != X1 ),
% 0.36/1.04      inference(resolution_lifted,[status(thm)],[c_0,c_12]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_133,plain,
% 0.36/1.04      ( r2_hidden(X0,k1_relat_1(sK2)) | ~ r2_hidden(X0,sK1) ),
% 0.36/1.04      inference(unflattening,[status(thm)],[c_132]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_1089,plain,
% 0.36/1.04      ( r2_hidden(sK0(sK1,X0,k1_relat_1(k7_relat_1(sK2,sK1))),k1_relat_1(sK2))
% 0.36/1.04      | ~ r2_hidden(sK0(sK1,X0,k1_relat_1(k7_relat_1(sK2,sK1))),sK1) ),
% 0.36/1.04      inference(instantiation,[status(thm)],[c_133]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_1093,plain,
% 0.36/1.04      ( r2_hidden(sK0(sK1,sK1,k1_relat_1(k7_relat_1(sK2,sK1))),k1_relat_1(sK2))
% 0.36/1.04      | ~ r2_hidden(sK0(sK1,sK1,k1_relat_1(k7_relat_1(sK2,sK1))),sK1) ),
% 0.36/1.04      inference(instantiation,[status(thm)],[c_1089]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_3,plain,
% 0.36/1.04      ( r2_hidden(sK0(X0,X1,X2),X0)
% 0.36/1.04      | r2_hidden(sK0(X0,X1,X2),X2)
% 0.36/1.04      | k1_setfam_1(k1_enumset1(X0,X0,X1)) = X2 ),
% 0.36/1.04      inference(cnf_transformation,[],[f43]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_451,plain,
% 0.36/1.04      ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = X2
% 0.36/1.04      | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top
% 0.36/1.04      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
% 0.36/1.04      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_10,plain,
% 0.36/1.04      ( r2_hidden(X0,X1)
% 0.36/1.04      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
% 0.36/1.04      | ~ v1_relat_1(X2) ),
% 0.36/1.04      inference(cnf_transformation,[],[f34]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_147,plain,
% 0.36/1.04      ( r2_hidden(X0,X1)
% 0.36/1.04      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
% 0.36/1.04      | sK2 != X2 ),
% 0.36/1.04      inference(resolution_lifted,[status(thm)],[c_10,c_13]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_148,plain,
% 0.36/1.04      ( r2_hidden(X0,X1)
% 0.36/1.04      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(sK2,X1))) ),
% 0.36/1.04      inference(unflattening,[status(thm)],[c_147]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_446,plain,
% 0.36/1.04      ( r2_hidden(X0,X1) = iProver_top
% 0.36/1.04      | r2_hidden(X0,k1_relat_1(k7_relat_1(sK2,X1))) != iProver_top ),
% 0.36/1.04      inference(predicate_to_equality,[status(thm)],[c_148]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_742,plain,
% 0.36/1.04      ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k1_relat_1(k7_relat_1(sK2,X2))
% 0.36/1.04      | r2_hidden(sK0(X0,X1,k1_relat_1(k7_relat_1(sK2,X2))),X0) = iProver_top
% 0.36/1.04      | r2_hidden(sK0(X0,X1,k1_relat_1(k7_relat_1(sK2,X2))),X2) = iProver_top ),
% 0.36/1.04      inference(superposition,[status(thm)],[c_451,c_446]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_809,plain,
% 0.36/1.04      ( r2_hidden(sK0(X0,X1,k1_relat_1(k7_relat_1(sK2,X2))),X0)
% 0.36/1.04      | r2_hidden(sK0(X0,X1,k1_relat_1(k7_relat_1(sK2,X2))),X2)
% 0.36/1.04      | k1_setfam_1(k1_enumset1(X0,X0,X1)) = k1_relat_1(k7_relat_1(sK2,X2)) ),
% 0.36/1.04      inference(predicate_to_equality_rev,[status(thm)],[c_742]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_811,plain,
% 0.36/1.04      ( r2_hidden(sK0(sK1,sK1,k1_relat_1(k7_relat_1(sK2,sK1))),sK1)
% 0.36/1.04      | k1_setfam_1(k1_enumset1(sK1,sK1,sK1)) = k1_relat_1(k7_relat_1(sK2,sK1)) ),
% 0.36/1.04      inference(instantiation,[status(thm)],[c_809]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_270,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_694,plain,
% 0.36/1.04      ( k1_setfam_1(k1_enumset1(X0,X0,X1)) != X2
% 0.36/1.04      | sK1 != X2
% 0.36/1.04      | sK1 = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
% 0.36/1.04      inference(instantiation,[status(thm)],[c_270]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_695,plain,
% 0.36/1.04      ( k1_setfam_1(k1_enumset1(sK1,sK1,sK1)) != sK1
% 0.36/1.04      | sK1 = k1_setfam_1(k1_enumset1(sK1,sK1,sK1))
% 0.36/1.04      | sK1 != sK1 ),
% 0.36/1.04      inference(instantiation,[status(thm)],[c_694]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_531,plain,
% 0.36/1.04      ( k1_relat_1(k7_relat_1(sK2,sK1)) != X0
% 0.36/1.04      | k1_relat_1(k7_relat_1(sK2,sK1)) = sK1
% 0.36/1.04      | sK1 != X0 ),
% 0.36/1.04      inference(instantiation,[status(thm)],[c_270]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_684,plain,
% 0.36/1.04      ( k1_relat_1(k7_relat_1(sK2,sK1)) != k1_setfam_1(k1_enumset1(X0,X0,X1))
% 0.36/1.04      | k1_relat_1(k7_relat_1(sK2,sK1)) = sK1
% 0.36/1.04      | sK1 != k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
% 0.36/1.04      inference(instantiation,[status(thm)],[c_531]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_685,plain,
% 0.36/1.04      ( k1_relat_1(k7_relat_1(sK2,sK1)) != k1_setfam_1(k1_enumset1(sK1,sK1,sK1))
% 0.36/1.04      | k1_relat_1(k7_relat_1(sK2,sK1)) = sK1
% 0.36/1.04      | sK1 != k1_setfam_1(k1_enumset1(sK1,sK1,sK1)) ),
% 0.36/1.04      inference(instantiation,[status(thm)],[c_684]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_1,plain,
% 0.36/1.04      ( ~ r2_hidden(sK0(X0,X1,X2),X1)
% 0.36/1.04      | ~ r2_hidden(sK0(X0,X1,X2),X0)
% 0.36/1.04      | ~ r2_hidden(sK0(X0,X1,X2),X2)
% 0.36/1.04      | k1_setfam_1(k1_enumset1(X0,X0,X1)) = X2 ),
% 0.36/1.04      inference(cnf_transformation,[],[f41]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_588,plain,
% 0.36/1.04      ( ~ r2_hidden(sK0(X0,X1,k1_relat_1(k7_relat_1(sK2,sK1))),X1)
% 0.36/1.04      | ~ r2_hidden(sK0(X0,X1,k1_relat_1(k7_relat_1(sK2,sK1))),X0)
% 0.36/1.04      | ~ r2_hidden(sK0(X0,X1,k1_relat_1(k7_relat_1(sK2,sK1))),k1_relat_1(k7_relat_1(sK2,sK1)))
% 0.36/1.04      | k1_setfam_1(k1_enumset1(X0,X0,X1)) = k1_relat_1(k7_relat_1(sK2,sK1)) ),
% 0.36/1.04      inference(instantiation,[status(thm)],[c_1]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_599,plain,
% 0.36/1.04      ( ~ r2_hidden(sK0(sK1,sK1,k1_relat_1(k7_relat_1(sK2,sK1))),k1_relat_1(k7_relat_1(sK2,sK1)))
% 0.36/1.04      | ~ r2_hidden(sK0(sK1,sK1,k1_relat_1(k7_relat_1(sK2,sK1))),sK1)
% 0.36/1.04      | k1_setfam_1(k1_enumset1(sK1,sK1,sK1)) = k1_relat_1(k7_relat_1(sK2,sK1)) ),
% 0.36/1.04      inference(instantiation,[status(thm)],[c_588]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_538,plain,
% 0.36/1.04      ( X0 != X1
% 0.36/1.04      | k1_relat_1(k7_relat_1(sK2,sK1)) != X1
% 0.36/1.04      | k1_relat_1(k7_relat_1(sK2,sK1)) = X0 ),
% 0.36/1.04      inference(instantiation,[status(thm)],[c_270]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_564,plain,
% 0.36/1.04      ( X0 != k1_relat_1(k7_relat_1(sK2,sK1))
% 0.36/1.04      | k1_relat_1(k7_relat_1(sK2,sK1)) = X0
% 0.36/1.04      | k1_relat_1(k7_relat_1(sK2,sK1)) != k1_relat_1(k7_relat_1(sK2,sK1)) ),
% 0.36/1.04      inference(instantiation,[status(thm)],[c_538]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_587,plain,
% 0.36/1.04      ( k1_relat_1(k7_relat_1(sK2,sK1)) != k1_relat_1(k7_relat_1(sK2,sK1))
% 0.36/1.04      | k1_relat_1(k7_relat_1(sK2,sK1)) = k1_setfam_1(k1_enumset1(X0,X0,X1))
% 0.36/1.04      | k1_setfam_1(k1_enumset1(X0,X0,X1)) != k1_relat_1(k7_relat_1(sK2,sK1)) ),
% 0.36/1.04      inference(instantiation,[status(thm)],[c_564]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_591,plain,
% 0.36/1.04      ( k1_relat_1(k7_relat_1(sK2,sK1)) != k1_relat_1(k7_relat_1(sK2,sK1))
% 0.36/1.04      | k1_relat_1(k7_relat_1(sK2,sK1)) = k1_setfam_1(k1_enumset1(sK1,sK1,sK1))
% 0.36/1.04      | k1_setfam_1(k1_enumset1(sK1,sK1,sK1)) != k1_relat_1(k7_relat_1(sK2,sK1)) ),
% 0.36/1.04      inference(instantiation,[status(thm)],[c_587]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_269,plain,( X0 = X0 ),theory(equality) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_537,plain,
% 0.36/1.04      ( k1_relat_1(k7_relat_1(sK2,sK1)) = k1_relat_1(k7_relat_1(sK2,sK1)) ),
% 0.36/1.04      inference(instantiation,[status(thm)],[c_269]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_280,plain,
% 0.36/1.04      ( sK1 = sK1 ),
% 0.36/1.04      inference(instantiation,[status(thm)],[c_269]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_7,plain,
% 0.36/1.04      ( k1_setfam_1(k1_enumset1(X0,X0,X0)) = X0 ),
% 0.36/1.04      inference(cnf_transformation,[],[f47]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_25,plain,
% 0.36/1.04      ( k1_setfam_1(k1_enumset1(sK1,sK1,sK1)) = sK1 ),
% 0.36/1.04      inference(instantiation,[status(thm)],[c_7]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(c_11,negated_conjecture,
% 0.36/1.04      ( k1_relat_1(k7_relat_1(sK2,sK1)) != sK1 ),
% 0.36/1.04      inference(cnf_transformation,[],[f39]) ).
% 0.36/1.04  
% 0.36/1.04  cnf(contradiction,plain,
% 0.36/1.04      ( $false ),
% 0.36/1.04      inference(minisat,
% 0.36/1.04                [status(thm)],
% 0.36/1.04                [c_1571,c_1093,c_811,c_695,c_685,c_599,c_591,c_537,c_280,
% 0.36/1.04                 c_25,c_11]) ).
% 0.36/1.04  
% 0.36/1.04  
% 0.36/1.04  % SZS output end CNFRefutation for theBenchmark.p
% 0.36/1.04  
% 0.36/1.04  ------                               Statistics
% 0.36/1.04  
% 0.36/1.04  ------ General
% 0.36/1.04  
% 0.36/1.04  abstr_ref_over_cycles:                  0
% 0.36/1.04  abstr_ref_under_cycles:                 0
% 0.36/1.04  gc_basic_clause_elim:                   0
% 0.36/1.04  forced_gc_time:                         0
% 0.36/1.04  parsing_time:                           0.011
% 0.36/1.04  unif_index_cands_time:                  0.
% 0.36/1.04  unif_index_add_time:                    0.
% 0.36/1.04  orderings_time:                         0.
% 0.36/1.04  out_proof_time:                         0.01
% 0.36/1.04  total_time:                             0.091
% 0.36/1.04  num_of_symbols:                         41
% 0.36/1.04  num_of_terms:                           1711
% 0.36/1.04  
% 0.36/1.04  ------ Preprocessing
% 0.36/1.04  
% 0.36/1.04  num_of_splits:                          0
% 0.36/1.04  num_of_split_atoms:                     0
% 0.36/1.04  num_of_reused_defs:                     0
% 0.36/1.04  num_eq_ax_congr_red:                    18
% 0.36/1.04  num_of_sem_filtered_clauses:            1
% 0.36/1.04  num_of_subtypes:                        0
% 0.36/1.04  monotx_restored_types:                  0
% 0.36/1.04  sat_num_of_epr_types:                   0
% 0.36/1.04  sat_num_of_non_cyclic_types:            0
% 0.36/1.04  sat_guarded_non_collapsed_types:        0
% 0.36/1.04  num_pure_diseq_elim:                    0
% 0.36/1.04  simp_replaced_by:                       0
% 0.36/1.04  res_preprocessed:                       63
% 0.36/1.04  prep_upred:                             0
% 0.36/1.04  prep_unflattend:                        5
% 0.36/1.04  smt_new_axioms:                         0
% 0.36/1.04  pred_elim_cands:                        1
% 0.36/1.04  pred_elim:                              2
% 0.36/1.04  pred_elim_cl:                           2
% 0.36/1.04  pred_elim_cycles:                       4
% 0.36/1.04  merged_defs:                            0
% 0.36/1.04  merged_defs_ncl:                        0
% 0.36/1.04  bin_hyper_res:                          0
% 0.36/1.04  prep_cycles:                            4
% 0.36/1.04  pred_elim_time:                         0.001
% 0.36/1.04  splitting_time:                         0.
% 0.36/1.04  sem_filter_time:                        0.
% 0.36/1.04  monotx_time:                            0.
% 0.36/1.04  subtype_inf_time:                       0.
% 0.36/1.04  
% 0.36/1.04  ------ Problem properties
% 0.36/1.04  
% 0.36/1.04  clauses:                                12
% 0.36/1.04  conjectures:                            1
% 0.36/1.04  epr:                                    0
% 0.36/1.04  horn:                                   10
% 0.36/1.04  ground:                                 1
% 0.36/1.04  unary:                                  2
% 0.36/1.04  binary:                                 5
% 0.36/1.04  lits:                                   28
% 0.36/1.04  lits_eq:                                5
% 0.36/1.04  fd_pure:                                0
% 0.36/1.04  fd_pseudo:                              0
% 0.36/1.04  fd_cond:                                0
% 0.36/1.04  fd_pseudo_cond:                         3
% 0.36/1.04  ac_symbols:                             0
% 0.36/1.04  
% 0.36/1.04  ------ Propositional Solver
% 0.36/1.04  
% 0.36/1.04  prop_solver_calls:                      28
% 0.36/1.04  prop_fast_solver_calls:                 358
% 0.36/1.04  smt_solver_calls:                       0
% 0.36/1.04  smt_fast_solver_calls:                  0
% 0.36/1.04  prop_num_of_clauses:                    467
% 0.36/1.04  prop_preprocess_simplified:             2211
% 0.36/1.04  prop_fo_subsumed:                       0
% 0.36/1.04  prop_solver_time:                       0.
% 0.36/1.04  smt_solver_time:                        0.
% 0.36/1.04  smt_fast_solver_time:                   0.
% 0.36/1.04  prop_fast_solver_time:                  0.
% 0.36/1.04  prop_unsat_core_time:                   0.
% 0.36/1.04  
% 0.36/1.04  ------ QBF
% 0.36/1.04  
% 0.36/1.04  qbf_q_res:                              0
% 0.36/1.04  qbf_num_tautologies:                    0
% 0.36/1.04  qbf_prep_cycles:                        0
% 0.36/1.04  
% 0.36/1.04  ------ BMC1
% 0.36/1.04  
% 0.36/1.04  bmc1_current_bound:                     -1
% 0.36/1.04  bmc1_last_solved_bound:                 -1
% 0.36/1.04  bmc1_unsat_core_size:                   -1
% 0.36/1.04  bmc1_unsat_core_parents_size:           -1
% 0.36/1.04  bmc1_merge_next_fun:                    0
% 0.36/1.04  bmc1_unsat_core_clauses_time:           0.
% 0.36/1.04  
% 0.36/1.04  ------ Instantiation
% 0.36/1.04  
% 0.36/1.04  inst_num_of_clauses:                    159
% 0.36/1.04  inst_num_in_passive:                    71
% 0.36/1.04  inst_num_in_active:                     85
% 0.36/1.04  inst_num_in_unprocessed:                2
% 0.36/1.04  inst_num_of_loops:                      98
% 0.36/1.04  inst_num_of_learning_restarts:          0
% 0.36/1.04  inst_num_moves_active_passive:          7
% 0.36/1.04  inst_lit_activity:                      0
% 0.36/1.04  inst_lit_activity_moves:                0
% 0.36/1.04  inst_num_tautologies:                   0
% 0.36/1.04  inst_num_prop_implied:                  0
% 0.36/1.04  inst_num_existing_simplified:           0
% 0.36/1.04  inst_num_eq_res_simplified:             0
% 0.36/1.04  inst_num_child_elim:                    0
% 0.36/1.04  inst_num_of_dismatching_blockings:      39
% 0.36/1.04  inst_num_of_non_proper_insts:           120
% 0.36/1.04  inst_num_of_duplicates:                 0
% 0.36/1.04  inst_inst_num_from_inst_to_res:         0
% 0.36/1.04  inst_dismatching_checking_time:         0.
% 0.36/1.04  
% 0.36/1.04  ------ Resolution
% 0.36/1.04  
% 0.36/1.04  res_num_of_clauses:                     0
% 0.36/1.04  res_num_in_passive:                     0
% 0.36/1.04  res_num_in_active:                      0
% 0.36/1.04  res_num_of_loops:                       67
% 0.36/1.04  res_forward_subset_subsumed:            32
% 0.36/1.04  res_backward_subset_subsumed:           0
% 0.36/1.04  res_forward_subsumed:                   0
% 0.36/1.04  res_backward_subsumed:                  0
% 0.36/1.04  res_forward_subsumption_resolution:     0
% 0.36/1.04  res_backward_subsumption_resolution:    0
% 0.36/1.04  res_clause_to_clause_subsumption:       323
% 0.36/1.04  res_orphan_elimination:                 0
% 0.36/1.04  res_tautology_del:                      24
% 0.36/1.04  res_num_eq_res_simplified:              0
% 0.36/1.04  res_num_sel_changes:                    0
% 0.36/1.04  res_moves_from_active_to_pass:          0
% 0.36/1.04  
% 0.36/1.04  ------ Superposition
% 0.36/1.04  
% 0.36/1.04  sup_time_total:                         0.
% 0.36/1.04  sup_time_generating:                    0.
% 0.36/1.04  sup_time_sim_full:                      0.
% 0.36/1.04  sup_time_sim_immed:                     0.
% 0.36/1.04  
% 0.36/1.04  sup_num_of_clauses:                     45
% 0.36/1.04  sup_num_in_active:                      18
% 0.36/1.04  sup_num_in_passive:                     27
% 0.36/1.04  sup_num_of_loops:                       18
% 0.36/1.04  sup_fw_superposition:                   37
% 0.36/1.04  sup_bw_superposition:                   20
% 0.36/1.04  sup_immediate_simplified:               9
% 0.36/1.04  sup_given_eliminated:                   0
% 0.36/1.04  comparisons_done:                       0
% 0.36/1.04  comparisons_avoided:                    0
% 0.36/1.04  
% 0.36/1.04  ------ Simplifications
% 0.36/1.04  
% 0.36/1.04  
% 0.36/1.04  sim_fw_subset_subsumed:                 0
% 0.36/1.04  sim_bw_subset_subsumed:                 0
% 0.36/1.04  sim_fw_subsumed:                        9
% 0.36/1.04  sim_bw_subsumed:                        0
% 0.36/1.04  sim_fw_subsumption_res:                 0
% 0.36/1.04  sim_bw_subsumption_res:                 0
% 0.36/1.04  sim_tautology_del:                      16
% 0.36/1.04  sim_eq_tautology_del:                   0
% 0.36/1.04  sim_eq_res_simp:                        2
% 0.36/1.04  sim_fw_demodulated:                     1
% 0.36/1.04  sim_bw_demodulated:                     0
% 0.36/1.04  sim_light_normalised:                   0
% 0.36/1.04  sim_joinable_taut:                      0
% 0.36/1.04  sim_joinable_simp:                      0
% 0.36/1.04  sim_ac_normalised:                      0
% 0.36/1.04  sim_smt_subsumption:                    0
% 0.36/1.04  
%------------------------------------------------------------------------------
