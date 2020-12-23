%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:46:40 EST 2020

% Result     : Theorem 55.83s
% Output     : CNFRefutation 55.83s
% Verified   : 
% Statistics : Number of formulae       :  178 ( 682 expanded)
%              Number of clauses        :  130 ( 302 expanded)
%              Number of leaves         :   17 ( 152 expanded)
%              Depth                    :   22
%              Number of atoms          :  493 (1518 expanded)
%              Number of equality atoms :  218 ( 505 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    6 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f25])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( ( r1_tarski(X0,X1)
              & r1_tarski(X2,X3) )
           => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1))
          | ~ r1_tarski(X0,X1)
          | ~ r1_tarski(X2,X3)
          | ~ v1_relat_1(X3) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1))
          | ~ r1_tarski(X0,X1)
          | ~ r1_tarski(X2,X3)
          | ~ v1_relat_1(X3) )
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1))
      | ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X2,X3)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f29,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k9_relat_1(sK3,k3_xboole_0(sK1,sK2)),k3_xboole_0(k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK2)))
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,k3_xboole_0(sK1,sK2)),k3_xboole_0(k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK2)))
    & v1_relat_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f24,f29])).

fof(f44,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f30])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f46,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f36,f35])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k1_enumset1(X0,X0,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f38,f46])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k1_setfam_1(k1_enumset1(X1,X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f34,f46])).

fof(f31,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f45,plain,(
    ~ r1_tarski(k9_relat_1(sK3,k3_xboole_0(sK1,sK2)),k3_xboole_0(k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK2))) ),
    inference(cnf_transformation,[],[f30])).

fof(f49,plain,(
    ~ r1_tarski(k9_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))),k1_setfam_1(k1_enumset1(k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK2)))) ),
    inference(definition_unfolding,[],[f45,f46,f46])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_166,plain,
    ( ~ r2_hidden(sK0(X0_41,X1_41),X1_41)
    | r1_tarski(X0_41,X1_41) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_220274,plain,
    ( ~ r2_hidden(sK0(sK2,sK2),sK2)
    | r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_166])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_165,plain,
    ( r2_hidden(sK0(X0_41,X1_41),X0_41)
    | r1_tarski(X0_41,X1_41) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_162500,plain,
    ( r2_hidden(sK0(X0_41,sK2),X0_41)
    | r1_tarski(X0_41,sK2) ),
    inference(instantiation,[status(thm)],[c_165])).

cnf(c_220273,plain,
    ( r2_hidden(sK0(sK2,sK2),sK2)
    | r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_162500])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X3)
    | r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_160,plain,
    ( ~ r1_tarski(X0_41,X1_41)
    | ~ r1_tarski(X2_41,X3_41)
    | r1_tarski(k7_relat_1(X2_41,X0_41),k7_relat_1(X3_41,X1_41))
    | ~ v1_relat_1(X2_41)
    | ~ v1_relat_1(X3_41) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_451,plain,
    ( r1_tarski(X0_41,X1_41) != iProver_top
    | r1_tarski(X2_41,X3_41) != iProver_top
    | r1_tarski(k7_relat_1(X2_41,X0_41),k7_relat_1(X3_41,X1_41)) = iProver_top
    | v1_relat_1(X2_41) != iProver_top
    | v1_relat_1(X3_41) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_160])).

cnf(c_12,negated_conjecture,
    ( v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_154,negated_conjecture,
    ( v1_relat_1(sK3) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_457,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_154])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_159,plain,
    ( ~ v1_relat_1(X0_41)
    | k2_relat_1(k7_relat_1(X0_41,X1_41)) = k9_relat_1(X0_41,X1_41) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_452,plain,
    ( k2_relat_1(k7_relat_1(X0_41,X1_41)) = k9_relat_1(X0_41,X1_41)
    | v1_relat_1(X0_41) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_159])).

cnf(c_663,plain,
    ( k2_relat_1(k7_relat_1(sK3,X0_41)) = k9_relat_1(sK3,X0_41) ),
    inference(superposition,[status(thm)],[c_457,c_452])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_162,plain,
    ( ~ v1_relat_1(X0_41)
    | v1_relat_1(k7_relat_1(X0_41,X1_41)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_449,plain,
    ( v1_relat_1(X0_41) != iProver_top
    | v1_relat_1(k7_relat_1(X0_41,X1_41)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_162])).

cnf(c_664,plain,
    ( k2_relat_1(k7_relat_1(k7_relat_1(X0_41,X1_41),X2_41)) = k9_relat_1(k7_relat_1(X0_41,X1_41),X2_41)
    | v1_relat_1(X0_41) != iProver_top ),
    inference(superposition,[status(thm)],[c_449,c_452])).

cnf(c_790,plain,
    ( k2_relat_1(k7_relat_1(k7_relat_1(sK3,X0_41),X1_41)) = k9_relat_1(k7_relat_1(sK3,X0_41),X1_41) ),
    inference(superposition,[status(thm)],[c_457,c_664])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_158,plain,
    ( ~ r1_tarski(X0_41,X1_41)
    | r1_tarski(k2_relat_1(X0_41),k2_relat_1(X1_41))
    | ~ v1_relat_1(X0_41)
    | ~ v1_relat_1(X1_41) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_453,plain,
    ( r1_tarski(X0_41,X1_41) != iProver_top
    | r1_tarski(k2_relat_1(X0_41),k2_relat_1(X1_41)) = iProver_top
    | v1_relat_1(X0_41) != iProver_top
    | v1_relat_1(X1_41) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_158])).

cnf(c_1099,plain,
    ( r1_tarski(k9_relat_1(k7_relat_1(sK3,X0_41),X1_41),k2_relat_1(X2_41)) = iProver_top
    | r1_tarski(k7_relat_1(k7_relat_1(sK3,X0_41),X1_41),X2_41) != iProver_top
    | v1_relat_1(X2_41) != iProver_top
    | v1_relat_1(k7_relat_1(k7_relat_1(sK3,X0_41),X1_41)) != iProver_top ),
    inference(superposition,[status(thm)],[c_790,c_453])).

cnf(c_13,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))) = k7_relat_1(k7_relat_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_161,plain,
    ( ~ v1_relat_1(X0_41)
    | k7_relat_1(X0_41,k1_setfam_1(k1_enumset1(X1_41,X1_41,X2_41))) = k7_relat_1(k7_relat_1(X0_41,X1_41),X2_41) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_450,plain,
    ( k7_relat_1(X0_41,k1_setfam_1(k1_enumset1(X1_41,X1_41,X2_41))) = k7_relat_1(k7_relat_1(X0_41,X1_41),X2_41)
    | v1_relat_1(X0_41) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_161])).

cnf(c_946,plain,
    ( k7_relat_1(sK3,k1_setfam_1(k1_enumset1(X0_41,X0_41,X1_41))) = k7_relat_1(k7_relat_1(sK3,X0_41),X1_41) ),
    inference(superposition,[status(thm)],[c_457,c_450])).

cnf(c_1215,plain,
    ( v1_relat_1(k7_relat_1(k7_relat_1(sK3,X0_41),X1_41)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_946,c_449])).

cnf(c_5016,plain,
    ( v1_relat_1(X2_41) != iProver_top
    | r1_tarski(k7_relat_1(k7_relat_1(sK3,X0_41),X1_41),X2_41) != iProver_top
    | r1_tarski(k9_relat_1(k7_relat_1(sK3,X0_41),X1_41),k2_relat_1(X2_41)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1099,c_13,c_1215])).

cnf(c_5017,plain,
    ( r1_tarski(k9_relat_1(k7_relat_1(sK3,X0_41),X1_41),k2_relat_1(X2_41)) = iProver_top
    | r1_tarski(k7_relat_1(k7_relat_1(sK3,X0_41),X1_41),X2_41) != iProver_top
    | v1_relat_1(X2_41) != iProver_top ),
    inference(renaming,[status(thm)],[c_5016])).

cnf(c_5026,plain,
    ( r1_tarski(k9_relat_1(k7_relat_1(sK3,X0_41),X1_41),k9_relat_1(sK3,X2_41)) = iProver_top
    | r1_tarski(k7_relat_1(k7_relat_1(sK3,X0_41),X1_41),k7_relat_1(sK3,X2_41)) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,X2_41)) != iProver_top ),
    inference(superposition,[status(thm)],[c_663,c_5017])).

cnf(c_6249,plain,
    ( r1_tarski(X0_41,X1_41) != iProver_top
    | r1_tarski(k9_relat_1(k7_relat_1(sK3,X2_41),X0_41),k9_relat_1(sK3,X1_41)) = iProver_top
    | r1_tarski(k7_relat_1(sK3,X2_41),sK3) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,X1_41)) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,X2_41)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_451,c_5026])).

cnf(c_106440,plain,
    ( v1_relat_1(k7_relat_1(sK3,X2_41)) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,X1_41)) != iProver_top
    | r1_tarski(k7_relat_1(sK3,X2_41),sK3) != iProver_top
    | r1_tarski(k9_relat_1(k7_relat_1(sK3,X2_41),X0_41),k9_relat_1(sK3,X1_41)) = iProver_top
    | r1_tarski(X0_41,X1_41) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6249,c_13])).

cnf(c_106441,plain,
    ( r1_tarski(X0_41,X1_41) != iProver_top
    | r1_tarski(k9_relat_1(k7_relat_1(sK3,X2_41),X0_41),k9_relat_1(sK3,X1_41)) = iProver_top
    | r1_tarski(k7_relat_1(sK3,X2_41),sK3) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,X1_41)) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,X2_41)) != iProver_top ),
    inference(renaming,[status(thm)],[c_106440])).

cnf(c_446,plain,
    ( r2_hidden(sK0(X0_41,X1_41),X0_41) = iProver_top
    | r1_tarski(X0_41,X1_41) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_165])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_163,plain,
    ( ~ r1_tarski(X0_41,X1_41)
    | ~ r1_tarski(X0_41,X2_41)
    | r1_tarski(X0_41,k1_setfam_1(k1_enumset1(X1_41,X1_41,X2_41))) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_448,plain,
    ( r1_tarski(X0_41,X1_41) != iProver_top
    | r1_tarski(X0_41,X2_41) != iProver_top
    | r1_tarski(X0_41,k1_setfam_1(k1_enumset1(X1_41,X1_41,X2_41))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_163])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_164,plain,
    ( ~ r2_hidden(X0_43,X0_41)
    | r2_hidden(X0_43,X1_41)
    | ~ r1_tarski(X0_41,X1_41) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_447,plain,
    ( r2_hidden(X0_43,X0_41) != iProver_top
    | r2_hidden(X0_43,X1_41) = iProver_top
    | r1_tarski(X0_41,X1_41) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_164])).

cnf(c_963,plain,
    ( r2_hidden(X0_43,X0_41) != iProver_top
    | r2_hidden(X0_43,k1_setfam_1(k1_enumset1(X1_41,X1_41,X2_41))) = iProver_top
    | r1_tarski(X0_41,X1_41) != iProver_top
    | r1_tarski(X0_41,X2_41) != iProver_top ),
    inference(superposition,[status(thm)],[c_448,c_447])).

cnf(c_5303,plain,
    ( r2_hidden(X0_43,k2_relat_1(X0_41)) != iProver_top
    | r2_hidden(X0_43,k1_setfam_1(k1_enumset1(k2_relat_1(X1_41),k2_relat_1(X1_41),X2_41))) = iProver_top
    | r1_tarski(X0_41,X1_41) != iProver_top
    | r1_tarski(k2_relat_1(X0_41),X2_41) != iProver_top
    | v1_relat_1(X0_41) != iProver_top
    | v1_relat_1(X1_41) != iProver_top ),
    inference(superposition,[status(thm)],[c_453,c_963])).

cnf(c_78913,plain,
    ( r2_hidden(sK0(k2_relat_1(X0_41),X1_41),k1_setfam_1(k1_enumset1(k2_relat_1(X2_41),k2_relat_1(X2_41),X3_41))) = iProver_top
    | r1_tarski(X0_41,X2_41) != iProver_top
    | r1_tarski(k2_relat_1(X0_41),X3_41) != iProver_top
    | r1_tarski(k2_relat_1(X0_41),X1_41) = iProver_top
    | v1_relat_1(X0_41) != iProver_top
    | v1_relat_1(X2_41) != iProver_top ),
    inference(superposition,[status(thm)],[c_446,c_5303])).

cnf(c_445,plain,
    ( r2_hidden(sK0(X0_41,X1_41),X1_41) != iProver_top
    | r1_tarski(X0_41,X1_41) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_166])).

cnf(c_98635,plain,
    ( r1_tarski(X0_41,X1_41) != iProver_top
    | r1_tarski(k2_relat_1(X0_41),X2_41) != iProver_top
    | r1_tarski(k2_relat_1(X0_41),k1_setfam_1(k1_enumset1(k2_relat_1(X1_41),k2_relat_1(X1_41),X2_41))) = iProver_top
    | v1_relat_1(X0_41) != iProver_top
    | v1_relat_1(X1_41) != iProver_top ),
    inference(superposition,[status(thm)],[c_78913,c_445])).

cnf(c_99034,plain,
    ( r1_tarski(k9_relat_1(k7_relat_1(sK3,X0_41),X1_41),k1_setfam_1(k1_enumset1(k2_relat_1(X2_41),k2_relat_1(X2_41),X3_41))) = iProver_top
    | r1_tarski(k7_relat_1(k7_relat_1(sK3,X0_41),X1_41),X2_41) != iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK3,X0_41),X1_41)),X3_41) != iProver_top
    | v1_relat_1(X2_41) != iProver_top
    | v1_relat_1(k7_relat_1(k7_relat_1(sK3,X0_41),X1_41)) != iProver_top ),
    inference(superposition,[status(thm)],[c_790,c_98635])).

cnf(c_99552,plain,
    ( r1_tarski(k9_relat_1(k7_relat_1(sK3,X0_41),X1_41),X2_41) != iProver_top
    | r1_tarski(k9_relat_1(k7_relat_1(sK3,X0_41),X1_41),k1_setfam_1(k1_enumset1(k2_relat_1(X3_41),k2_relat_1(X3_41),X2_41))) = iProver_top
    | r1_tarski(k7_relat_1(k7_relat_1(sK3,X0_41),X1_41),X3_41) != iProver_top
    | v1_relat_1(X3_41) != iProver_top
    | v1_relat_1(k7_relat_1(k7_relat_1(sK3,X0_41),X1_41)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_99034,c_790])).

cnf(c_130923,plain,
    ( v1_relat_1(X3_41) != iProver_top
    | r1_tarski(k7_relat_1(k7_relat_1(sK3,X0_41),X1_41),X3_41) != iProver_top
    | r1_tarski(k9_relat_1(k7_relat_1(sK3,X0_41),X1_41),k1_setfam_1(k1_enumset1(k2_relat_1(X3_41),k2_relat_1(X3_41),X2_41))) = iProver_top
    | r1_tarski(k9_relat_1(k7_relat_1(sK3,X0_41),X1_41),X2_41) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_99552,c_13,c_1215])).

cnf(c_130924,plain,
    ( r1_tarski(k9_relat_1(k7_relat_1(sK3,X0_41),X1_41),X2_41) != iProver_top
    | r1_tarski(k9_relat_1(k7_relat_1(sK3,X0_41),X1_41),k1_setfam_1(k1_enumset1(k2_relat_1(X3_41),k2_relat_1(X3_41),X2_41))) = iProver_top
    | r1_tarski(k7_relat_1(k7_relat_1(sK3,X0_41),X1_41),X3_41) != iProver_top
    | v1_relat_1(X3_41) != iProver_top ),
    inference(renaming,[status(thm)],[c_130923])).

cnf(c_130949,plain,
    ( r1_tarski(k9_relat_1(k7_relat_1(sK3,X0_41),X1_41),X2_41) != iProver_top
    | r1_tarski(k9_relat_1(k7_relat_1(sK3,X0_41),X1_41),k1_setfam_1(k1_enumset1(k9_relat_1(sK3,X3_41),k9_relat_1(sK3,X3_41),X2_41))) = iProver_top
    | r1_tarski(k7_relat_1(k7_relat_1(sK3,X0_41),X1_41),k7_relat_1(sK3,X3_41)) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,X3_41)) != iProver_top ),
    inference(superposition,[status(thm)],[c_663,c_130924])).

cnf(c_1217,plain,
    ( k9_relat_1(sK3,k1_setfam_1(k1_enumset1(X0_41,X0_41,X1_41))) = k2_relat_1(k7_relat_1(k7_relat_1(sK3,X0_41),X1_41)) ),
    inference(superposition,[status(thm)],[c_946,c_663])).

cnf(c_1219,plain,
    ( k9_relat_1(sK3,k1_setfam_1(k1_enumset1(X0_41,X0_41,X1_41))) = k9_relat_1(k7_relat_1(sK3,X0_41),X1_41) ),
    inference(light_normalisation,[status(thm)],[c_1217,c_790])).

cnf(c_11,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))),k1_setfam_1(k1_enumset1(k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK2)))) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_155,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))),k1_setfam_1(k1_enumset1(k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK2)))) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_456,plain,
    ( r1_tarski(k9_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))),k1_setfam_1(k1_enumset1(k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK2)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_155])).

cnf(c_1351,plain,
    ( r1_tarski(k9_relat_1(k7_relat_1(sK3,sK1),sK2),k1_setfam_1(k1_enumset1(k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK2)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1219,c_456])).

cnf(c_132024,plain,
    ( r1_tarski(k9_relat_1(k7_relat_1(sK3,sK1),sK2),k9_relat_1(sK3,sK2)) != iProver_top
    | r1_tarski(k7_relat_1(k7_relat_1(sK3,sK1),sK2),k7_relat_1(sK3,sK1)) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_130949,c_1351])).

cnf(c_18349,plain,
    ( v1_relat_1(k7_relat_1(sK3,sK1))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_162])).

cnf(c_18350,plain,
    ( v1_relat_1(k7_relat_1(sK3,sK1)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18349])).

cnf(c_172,plain,
    ( ~ r1_tarski(X0_41,X1_41)
    | r1_tarski(X2_41,X3_41)
    | X2_41 != X0_41
    | X3_41 != X1_41 ),
    theory(equality)).

cnf(c_168,plain,
    ( X0_41 = X0_41 ),
    theory(equality)).

cnf(c_1391,plain,
    ( ~ r1_tarski(X0_41,X1_41)
    | r1_tarski(X2_41,X1_41)
    | X2_41 != X0_41 ),
    inference(resolution,[status(thm)],[c_172,c_168])).

cnf(c_178,plain,
    ( X0_41 != X1_41
    | k2_relat_1(X0_41) = k2_relat_1(X1_41) ),
    theory(equality)).

cnf(c_1416,plain,
    ( ~ r1_tarski(k2_relat_1(X0_41),X1_41)
    | r1_tarski(k2_relat_1(X2_41),X1_41)
    | X2_41 != X0_41 ),
    inference(resolution,[status(thm)],[c_1391,c_178])).

cnf(c_1558,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(X0_41,k1_setfam_1(k1_enumset1(X1_41,X1_41,X2_41)))),X3_41)
    | ~ r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(X0_41,X1_41),X2_41)),X3_41)
    | ~ v1_relat_1(X0_41) ),
    inference(resolution,[status(thm)],[c_1416,c_161])).

cnf(c_171,plain,
    ( X0_41 != X1_41
    | X2_41 != X1_41
    | X2_41 = X0_41 ),
    theory(equality)).

cnf(c_1845,plain,
    ( X0_41 != X1_41
    | X1_41 = X0_41 ),
    inference(resolution,[status(thm)],[c_171,c_168])).

cnf(c_2927,plain,
    ( ~ v1_relat_1(X0_41)
    | k9_relat_1(X0_41,X1_41) = k2_relat_1(k7_relat_1(X0_41,X1_41)) ),
    inference(resolution,[status(thm)],[c_1845,c_159])).

cnf(c_3323,plain,
    ( r1_tarski(k9_relat_1(X0_41,X1_41),X2_41)
    | ~ r1_tarski(k2_relat_1(k7_relat_1(X0_41,X1_41)),X2_41)
    | ~ v1_relat_1(X0_41) ),
    inference(resolution,[status(thm)],[c_2927,c_1391])).

cnf(c_35413,plain,
    ( r1_tarski(k9_relat_1(X0_41,k1_setfam_1(k1_enumset1(X1_41,X1_41,X2_41))),X3_41)
    | ~ r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(X0_41,X1_41),X2_41)),X3_41)
    | ~ v1_relat_1(X0_41) ),
    inference(resolution,[status(thm)],[c_1558,c_3323])).

cnf(c_109102,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK3,sK1),sK2)),k1_setfam_1(k1_enumset1(k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK2))))
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[status(thm)],[c_35413,c_155])).

cnf(c_644,plain,
    ( k1_setfam_1(k1_enumset1(k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK2))) = k1_setfam_1(k1_enumset1(k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK2))) ),
    inference(instantiation,[status(thm)],[c_168])).

cnf(c_747,plain,
    ( k9_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))) = k9_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_168])).

cnf(c_737,plain,
    ( X0_41 != X1_41
    | k9_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))) != X1_41
    | k9_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))) = X0_41 ),
    inference(instantiation,[status(thm)],[c_171])).

cnf(c_913,plain,
    ( X0_41 != k9_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2)))
    | k9_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))) = X0_41
    | k9_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))) != k9_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_737])).

cnf(c_1160,plain,
    ( k9_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))) != k9_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2)))
    | k9_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))) = k2_relat_1(k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))))
    | k2_relat_1(k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2)))) != k9_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_913])).

cnf(c_1161,plain,
    ( ~ v1_relat_1(sK3)
    | k2_relat_1(k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2)))) = k9_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_159])).

cnf(c_599,plain,
    ( ~ r1_tarski(X0_41,X1_41)
    | r1_tarski(k9_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))),k1_setfam_1(k1_enumset1(k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK2))))
    | k9_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))) != X0_41
    | k1_setfam_1(k1_enumset1(k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK2))) != X1_41 ),
    inference(instantiation,[status(thm)],[c_172])).

cnf(c_643,plain,
    ( ~ r1_tarski(X0_41,k1_setfam_1(k1_enumset1(k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK2))))
    | r1_tarski(k9_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))),k1_setfam_1(k1_enumset1(k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK2))))
    | k9_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))) != X0_41
    | k1_setfam_1(k1_enumset1(k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK2))) != k1_setfam_1(k1_enumset1(k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK2))) ),
    inference(instantiation,[status(thm)],[c_599])).

cnf(c_1606,plain,
    ( r1_tarski(k9_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))),k1_setfam_1(k1_enumset1(k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK2))))
    | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2)))),k1_setfam_1(k1_enumset1(k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK2))))
    | k9_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))) != k2_relat_1(k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))))
    | k1_setfam_1(k1_enumset1(k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK2))) != k1_setfam_1(k1_enumset1(k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK2))) ),
    inference(instantiation,[status(thm)],[c_643])).

cnf(c_2964,plain,
    ( k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))) != X0_41
    | k2_relat_1(k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2)))) = k2_relat_1(X0_41) ),
    inference(instantiation,[status(thm)],[c_178])).

cnf(c_5693,plain,
    ( k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))) != k7_relat_1(k7_relat_1(sK3,sK1),sK2)
    | k2_relat_1(k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2)))) = k2_relat_1(k7_relat_1(k7_relat_1(sK3,sK1),sK2)) ),
    inference(instantiation,[status(thm)],[c_2964])).

cnf(c_5694,plain,
    ( ~ v1_relat_1(sK3)
    | k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))) = k7_relat_1(k7_relat_1(sK3,sK1),sK2) ),
    inference(instantiation,[status(thm)],[c_161])).

cnf(c_1885,plain,
    ( ~ r1_tarski(X0_41,X1_41)
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2)))),k1_setfam_1(k1_enumset1(k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK2))))
    | k2_relat_1(k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2)))) != X0_41
    | k1_setfam_1(k1_enumset1(k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK2))) != X1_41 ),
    inference(instantiation,[status(thm)],[c_172])).

cnf(c_2842,plain,
    ( ~ r1_tarski(X0_41,k1_setfam_1(k1_enumset1(k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK2))))
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2)))),k1_setfam_1(k1_enumset1(k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK2))))
    | k2_relat_1(k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2)))) != X0_41
    | k1_setfam_1(k1_enumset1(k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK2))) != k1_setfam_1(k1_enumset1(k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK2))) ),
    inference(instantiation,[status(thm)],[c_1885])).

cnf(c_9287,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK3,sK1),sK2)),k1_setfam_1(k1_enumset1(k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK2))))
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2)))),k1_setfam_1(k1_enumset1(k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK2))))
    | k2_relat_1(k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2)))) != k2_relat_1(k7_relat_1(k7_relat_1(sK3,sK1),sK2))
    | k1_setfam_1(k1_enumset1(k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK2))) != k1_setfam_1(k1_enumset1(k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK2))) ),
    inference(instantiation,[status(thm)],[c_2842])).

cnf(c_109205,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK3,sK1),sK2)),k1_setfam_1(k1_enumset1(k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK2)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_109102,c_12,c_11,c_644,c_747,c_1160,c_1161,c_1606,c_5693,c_5694,c_9287])).

cnf(c_109499,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK3,sK1),sK2)),k9_relat_1(sK3,sK2))
    | ~ r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK3,sK1),sK2)),k9_relat_1(sK3,sK1)) ),
    inference(resolution,[status(thm)],[c_109205,c_163])).

cnf(c_1052,plain,
    ( k9_relat_1(sK3,sK1) = k9_relat_1(sK3,sK1) ),
    inference(instantiation,[status(thm)],[c_168])).

cnf(c_1453,plain,
    ( k9_relat_1(sK3,sK2) = k9_relat_1(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_168])).

cnf(c_1890,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2)))),k9_relat_1(sK3,sK2))
    | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2)))),k9_relat_1(sK3,sK1))
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2)))),k1_setfam_1(k1_enumset1(k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK2)))) ),
    inference(instantiation,[status(thm)],[c_163])).

cnf(c_854,plain,
    ( X0_41 != X1_41
    | k9_relat_1(sK3,sK1) != X1_41
    | k9_relat_1(sK3,sK1) = X0_41 ),
    inference(instantiation,[status(thm)],[c_171])).

cnf(c_1419,plain,
    ( X0_41 != k9_relat_1(sK3,sK1)
    | k9_relat_1(sK3,sK1) = X0_41
    | k9_relat_1(sK3,sK1) != k9_relat_1(sK3,sK1) ),
    inference(instantiation,[status(thm)],[c_854])).

cnf(c_2121,plain,
    ( k9_relat_1(sK3,sK1) != k9_relat_1(sK3,sK1)
    | k9_relat_1(sK3,sK1) = k2_relat_1(k7_relat_1(sK3,sK1))
    | k2_relat_1(k7_relat_1(sK3,sK1)) != k9_relat_1(sK3,sK1) ),
    inference(instantiation,[status(thm)],[c_1419])).

cnf(c_2122,plain,
    ( ~ v1_relat_1(sK3)
    | k2_relat_1(k7_relat_1(sK3,sK1)) = k9_relat_1(sK3,sK1) ),
    inference(instantiation,[status(thm)],[c_159])).

cnf(c_2624,plain,
    ( v1_relat_1(k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_162])).

cnf(c_2959,plain,
    ( k2_relat_1(k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2)))) = k2_relat_1(k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2)))) ),
    inference(instantiation,[status(thm)],[c_168])).

cnf(c_6449,plain,
    ( ~ r1_tarski(k7_relat_1(X0_41,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))),k7_relat_1(sK3,sK1))
    | r1_tarski(k2_relat_1(k7_relat_1(X0_41,k1_setfam_1(k1_enumset1(sK1,sK1,sK2)))),k2_relat_1(k7_relat_1(sK3,sK1)))
    | ~ v1_relat_1(k7_relat_1(X0_41,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))))
    | ~ v1_relat_1(k7_relat_1(sK3,sK1)) ),
    inference(instantiation,[status(thm)],[c_158])).

cnf(c_6451,plain,
    ( ~ r1_tarski(k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))),k7_relat_1(sK3,sK1))
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2)))),k2_relat_1(k7_relat_1(sK3,sK1)))
    | ~ v1_relat_1(k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))))
    | ~ v1_relat_1(k7_relat_1(sK3,sK1)) ),
    inference(instantiation,[status(thm)],[c_6449])).

cnf(c_9574,plain,
    ( k7_relat_1(sK3,sK1) = k7_relat_1(sK3,sK1) ),
    inference(instantiation,[status(thm)],[c_168])).

cnf(c_1928,plain,
    ( ~ r1_tarski(X0_41,X1_41)
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2)))),X2_41)
    | X2_41 != X1_41
    | k2_relat_1(k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2)))) != X0_41 ),
    inference(instantiation,[status(thm)],[c_172])).

cnf(c_2958,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2)))),X0_41)
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2)))),X1_41)
    | X1_41 != X0_41
    | k2_relat_1(k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2)))) != k2_relat_1(k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2)))) ),
    inference(instantiation,[status(thm)],[c_1928])).

cnf(c_7644,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2)))),X0_41)
    | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2)))),k2_relat_1(X1_41))
    | X0_41 != k2_relat_1(X1_41)
    | k2_relat_1(k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2)))) != k2_relat_1(k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2)))) ),
    inference(instantiation,[status(thm)],[c_2958])).

cnf(c_19198,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2)))),k9_relat_1(sK3,sK1))
    | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2)))),k2_relat_1(k7_relat_1(sK3,sK1)))
    | k9_relat_1(sK3,sK1) != k2_relat_1(k7_relat_1(sK3,sK1))
    | k2_relat_1(k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2)))) != k2_relat_1(k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2)))) ),
    inference(instantiation,[status(thm)],[c_7644])).

cnf(c_10,plain,
    ( r1_tarski(k7_relat_1(X0,X1),X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_156,plain,
    ( r1_tarski(k7_relat_1(X0_41,X1_41),X0_41)
    | ~ v1_relat_1(X0_41) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_25552,plain,
    ( r1_tarski(k7_relat_1(k7_relat_1(sK3,sK1),sK2),k7_relat_1(sK3,sK1))
    | ~ v1_relat_1(k7_relat_1(sK3,sK1)) ),
    inference(instantiation,[status(thm)],[c_156])).

cnf(c_2672,plain,
    ( ~ r1_tarski(X0_41,X1_41)
    | r1_tarski(X2_41,k9_relat_1(sK3,sK2))
    | X2_41 != X0_41
    | k9_relat_1(sK3,sK2) != X1_41 ),
    inference(instantiation,[status(thm)],[c_172])).

cnf(c_8375,plain,
    ( ~ r1_tarski(X0_41,k9_relat_1(sK3,sK2))
    | r1_tarski(X1_41,k9_relat_1(sK3,sK2))
    | X1_41 != X0_41
    | k9_relat_1(sK3,sK2) != k9_relat_1(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_2672])).

cnf(c_24885,plain,
    ( ~ r1_tarski(X0_41,k9_relat_1(sK3,sK2))
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2)))),k9_relat_1(sK3,sK2))
    | k9_relat_1(sK3,sK2) != k9_relat_1(sK3,sK2)
    | k2_relat_1(k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2)))) != X0_41 ),
    inference(instantiation,[status(thm)],[c_8375])).

cnf(c_35786,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK3,sK1),sK2)),k9_relat_1(sK3,sK2))
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2)))),k9_relat_1(sK3,sK2))
    | k9_relat_1(sK3,sK2) != k9_relat_1(sK3,sK2)
    | k2_relat_1(k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2)))) != k2_relat_1(k7_relat_1(k7_relat_1(sK3,sK1),sK2)) ),
    inference(instantiation,[status(thm)],[c_24885])).

cnf(c_5187,plain,
    ( ~ r1_tarski(X0_41,X1_41)
    | r1_tarski(k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))),X2_41)
    | X2_41 != X1_41
    | k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))) != X0_41 ),
    inference(instantiation,[status(thm)],[c_172])).

cnf(c_9308,plain,
    ( ~ r1_tarski(k7_relat_1(k7_relat_1(sK3,sK1),sK2),X0_41)
    | r1_tarski(k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))),X1_41)
    | X1_41 != X0_41
    | k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))) != k7_relat_1(k7_relat_1(sK3,sK1),sK2) ),
    inference(instantiation,[status(thm)],[c_5187])).

cnf(c_25551,plain,
    ( ~ r1_tarski(k7_relat_1(k7_relat_1(sK3,sK1),sK2),k7_relat_1(sK3,sK1))
    | r1_tarski(k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))),X0_41)
    | X0_41 != k7_relat_1(sK3,sK1)
    | k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))) != k7_relat_1(k7_relat_1(sK3,sK1),sK2) ),
    inference(instantiation,[status(thm)],[c_9308])).

cnf(c_69122,plain,
    ( ~ r1_tarski(k7_relat_1(k7_relat_1(sK3,sK1),sK2),k7_relat_1(sK3,sK1))
    | r1_tarski(k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))),k7_relat_1(sK3,sK1))
    | k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))) != k7_relat_1(k7_relat_1(sK3,sK1),sK2)
    | k7_relat_1(sK3,sK1) != k7_relat_1(sK3,sK1) ),
    inference(instantiation,[status(thm)],[c_25551])).

cnf(c_109504,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK3,sK1),sK2)),k9_relat_1(sK3,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_109499,c_12,c_11,c_644,c_747,c_1052,c_1160,c_1161,c_1453,c_1606,c_1890,c_2121,c_2122,c_2624,c_2959,c_5693,c_5694,c_6451,c_9574,c_18349,c_19198,c_25552,c_35786,c_69122])).

cnf(c_1405,plain,
    ( ~ r1_tarski(k9_relat_1(X0_41,X1_41),X2_41)
    | r1_tarski(k2_relat_1(k7_relat_1(X0_41,X1_41)),X2_41)
    | ~ v1_relat_1(X0_41) ),
    inference(resolution,[status(thm)],[c_1391,c_159])).

cnf(c_110476,plain,
    ( ~ r1_tarski(k9_relat_1(k7_relat_1(sK3,sK1),sK2),k9_relat_1(sK3,sK2))
    | ~ v1_relat_1(k7_relat_1(sK3,sK1)) ),
    inference(resolution,[status(thm)],[c_109504,c_1405])).

cnf(c_110477,plain,
    ( r1_tarski(k9_relat_1(k7_relat_1(sK3,sK1),sK2),k9_relat_1(sK3,sK2)) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_110476])).

cnf(c_132419,plain,
    ( r1_tarski(k9_relat_1(k7_relat_1(sK3,sK1),sK2),k9_relat_1(sK3,sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_132024,c_13,c_18350,c_110477])).

cnf(c_132424,plain,
    ( r1_tarski(k7_relat_1(sK3,sK1),sK3) != iProver_top
    | r1_tarski(sK2,sK2) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_106441,c_132419])).

cnf(c_132425,plain,
    ( ~ r1_tarski(k7_relat_1(sK3,sK1),sK3)
    | ~ r1_tarski(sK2,sK2)
    | ~ v1_relat_1(k7_relat_1(sK3,sK2))
    | ~ v1_relat_1(k7_relat_1(sK3,sK1)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_132424])).

cnf(c_47873,plain,
    ( r1_tarski(k7_relat_1(sK3,sK1),sK3)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_156])).

cnf(c_30201,plain,
    ( v1_relat_1(k7_relat_1(sK3,sK2))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_162])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_220274,c_220273,c_132425,c_47873,c_30201,c_18349,c_12])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:33:24 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 55.83/7.45  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 55.83/7.45  
% 55.83/7.45  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 55.83/7.45  
% 55.83/7.45  ------  iProver source info
% 55.83/7.45  
% 55.83/7.45  git: date: 2020-06-30 10:37:57 +0100
% 55.83/7.45  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 55.83/7.45  git: non_committed_changes: false
% 55.83/7.45  git: last_make_outside_of_git: false
% 55.83/7.45  
% 55.83/7.45  ------ 
% 55.83/7.45  ------ Parsing...
% 55.83/7.45  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 55.83/7.45  
% 55.83/7.45  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 55.83/7.45  
% 55.83/7.45  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 55.83/7.45  
% 55.83/7.45  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 55.83/7.45  ------ Proving...
% 55.83/7.45  ------ Problem Properties 
% 55.83/7.45  
% 55.83/7.45  
% 55.83/7.45  clauses                                 13
% 55.83/7.45  conjectures                             2
% 55.83/7.45  EPR                                     2
% 55.83/7.45  Horn                                    12
% 55.83/7.45  unary                                   2
% 55.83/7.45  binary                                  6
% 55.83/7.45  lits                                    33
% 55.83/7.45  lits eq                                 2
% 55.83/7.45  fd_pure                                 0
% 55.83/7.45  fd_pseudo                               0
% 55.83/7.45  fd_cond                                 0
% 55.83/7.45  fd_pseudo_cond                          0
% 55.83/7.45  AC symbols                              0
% 55.83/7.45  
% 55.83/7.45  ------ Input Options Time Limit: Unbounded
% 55.83/7.45  
% 55.83/7.45  
% 55.83/7.45  ------ 
% 55.83/7.45  Current options:
% 55.83/7.45  ------ 
% 55.83/7.45  
% 55.83/7.45  
% 55.83/7.45  
% 55.83/7.45  
% 55.83/7.45  ------ Proving...
% 55.83/7.45  
% 55.83/7.45  
% 55.83/7.45  % SZS status Theorem for theBenchmark.p
% 55.83/7.45  
% 55.83/7.45  % SZS output start CNFRefutation for theBenchmark.p
% 55.83/7.45  
% 55.83/7.45  fof(f1,axiom,(
% 55.83/7.45    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 55.83/7.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.83/7.45  
% 55.83/7.45  fof(f13,plain,(
% 55.83/7.45    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 55.83/7.45    inference(ennf_transformation,[],[f1])).
% 55.83/7.45  
% 55.83/7.45  fof(f25,plain,(
% 55.83/7.45    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 55.83/7.45    inference(nnf_transformation,[],[f13])).
% 55.83/7.45  
% 55.83/7.45  fof(f26,plain,(
% 55.83/7.45    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 55.83/7.45    inference(rectify,[],[f25])).
% 55.83/7.45  
% 55.83/7.45  fof(f27,plain,(
% 55.83/7.45    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 55.83/7.45    introduced(choice_axiom,[])).
% 55.83/7.45  
% 55.83/7.45  fof(f28,plain,(
% 55.83/7.45    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 55.83/7.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).
% 55.83/7.45  
% 55.83/7.45  fof(f33,plain,(
% 55.83/7.45    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 55.83/7.45    inference(cnf_transformation,[],[f28])).
% 55.83/7.45  
% 55.83/7.45  fof(f32,plain,(
% 55.83/7.45    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 55.83/7.45    inference(cnf_transformation,[],[f28])).
% 55.83/7.45  
% 55.83/7.45  fof(f7,axiom,(
% 55.83/7.45    ! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)))))),
% 55.83/7.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.83/7.45  
% 55.83/7.45  fof(f18,plain,(
% 55.83/7.45    ! [X0,X1,X2] : (! [X3] : ((r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) | (~r1_tarski(X0,X1) | ~r1_tarski(X2,X3))) | ~v1_relat_1(X3)) | ~v1_relat_1(X2))),
% 55.83/7.45    inference(ennf_transformation,[],[f7])).
% 55.83/7.45  
% 55.83/7.45  fof(f19,plain,(
% 55.83/7.45    ! [X0,X1,X2] : (! [X3] : (r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) | ~r1_tarski(X0,X1) | ~r1_tarski(X2,X3) | ~v1_relat_1(X3)) | ~v1_relat_1(X2))),
% 55.83/7.45    inference(flattening,[],[f18])).
% 55.83/7.45  
% 55.83/7.45  fof(f39,plain,(
% 55.83/7.45    ( ! [X2,X0,X3,X1] : (r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) | ~r1_tarski(X0,X1) | ~r1_tarski(X2,X3) | ~v1_relat_1(X3) | ~v1_relat_1(X2)) )),
% 55.83/7.45    inference(cnf_transformation,[],[f19])).
% 55.83/7.45  
% 55.83/7.45  fof(f11,conjecture,(
% 55.83/7.45    ! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 55.83/7.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.83/7.45  
% 55.83/7.45  fof(f12,negated_conjecture,(
% 55.83/7.45    ~! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 55.83/7.45    inference(negated_conjecture,[],[f11])).
% 55.83/7.45  
% 55.83/7.45  fof(f24,plain,(
% 55.83/7.45    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) & v1_relat_1(X2))),
% 55.83/7.45    inference(ennf_transformation,[],[f12])).
% 55.83/7.45  
% 55.83/7.45  fof(f29,plain,(
% 55.83/7.45    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) & v1_relat_1(X2)) => (~r1_tarski(k9_relat_1(sK3,k3_xboole_0(sK1,sK2)),k3_xboole_0(k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK2))) & v1_relat_1(sK3))),
% 55.83/7.45    introduced(choice_axiom,[])).
% 55.83/7.45  
% 55.83/7.45  fof(f30,plain,(
% 55.83/7.45    ~r1_tarski(k9_relat_1(sK3,k3_xboole_0(sK1,sK2)),k3_xboole_0(k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK2))) & v1_relat_1(sK3)),
% 55.83/7.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f24,f29])).
% 55.83/7.45  
% 55.83/7.45  fof(f44,plain,(
% 55.83/7.45    v1_relat_1(sK3)),
% 55.83/7.45    inference(cnf_transformation,[],[f30])).
% 55.83/7.45  
% 55.83/7.45  fof(f8,axiom,(
% 55.83/7.45    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 55.83/7.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.83/7.45  
% 55.83/7.45  fof(f20,plain,(
% 55.83/7.45    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 55.83/7.45    inference(ennf_transformation,[],[f8])).
% 55.83/7.45  
% 55.83/7.45  fof(f40,plain,(
% 55.83/7.45    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 55.83/7.45    inference(cnf_transformation,[],[f20])).
% 55.83/7.45  
% 55.83/7.45  fof(f5,axiom,(
% 55.83/7.45    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 55.83/7.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.83/7.45  
% 55.83/7.45  fof(f16,plain,(
% 55.83/7.45    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 55.83/7.45    inference(ennf_transformation,[],[f5])).
% 55.83/7.45  
% 55.83/7.45  fof(f37,plain,(
% 55.83/7.45    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 55.83/7.45    inference(cnf_transformation,[],[f16])).
% 55.83/7.45  
% 55.83/7.45  fof(f9,axiom,(
% 55.83/7.45    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 55.83/7.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.83/7.45  
% 55.83/7.45  fof(f21,plain,(
% 55.83/7.45    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 55.83/7.45    inference(ennf_transformation,[],[f9])).
% 55.83/7.45  
% 55.83/7.45  fof(f22,plain,(
% 55.83/7.45    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 55.83/7.45    inference(flattening,[],[f21])).
% 55.83/7.45  
% 55.83/7.45  fof(f42,plain,(
% 55.83/7.45    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 55.83/7.45    inference(cnf_transformation,[],[f22])).
% 55.83/7.45  
% 55.83/7.45  fof(f6,axiom,(
% 55.83/7.45    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1))),
% 55.83/7.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.83/7.45  
% 55.83/7.45  fof(f17,plain,(
% 55.83/7.45    ! [X0,X1,X2] : (k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2))),
% 55.83/7.45    inference(ennf_transformation,[],[f6])).
% 55.83/7.45  
% 55.83/7.45  fof(f38,plain,(
% 55.83/7.45    ( ! [X2,X0,X1] : (k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 55.83/7.45    inference(cnf_transformation,[],[f17])).
% 55.83/7.45  
% 55.83/7.45  fof(f4,axiom,(
% 55.83/7.45    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 55.83/7.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.83/7.45  
% 55.83/7.45  fof(f36,plain,(
% 55.83/7.45    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 55.83/7.45    inference(cnf_transformation,[],[f4])).
% 55.83/7.45  
% 55.83/7.45  fof(f3,axiom,(
% 55.83/7.45    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 55.83/7.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.83/7.45  
% 55.83/7.45  fof(f35,plain,(
% 55.83/7.45    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 55.83/7.45    inference(cnf_transformation,[],[f3])).
% 55.83/7.45  
% 55.83/7.45  fof(f46,plain,(
% 55.83/7.45    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 55.83/7.45    inference(definition_unfolding,[],[f36,f35])).
% 55.83/7.45  
% 55.83/7.45  fof(f48,plain,(
% 55.83/7.45    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k1_enumset1(X0,X0,X1))) | ~v1_relat_1(X2)) )),
% 55.83/7.45    inference(definition_unfolding,[],[f38,f46])).
% 55.83/7.45  
% 55.83/7.45  fof(f2,axiom,(
% 55.83/7.45    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 55.83/7.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.83/7.45  
% 55.83/7.45  fof(f14,plain,(
% 55.83/7.45    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 55.83/7.45    inference(ennf_transformation,[],[f2])).
% 55.83/7.45  
% 55.83/7.45  fof(f15,plain,(
% 55.83/7.45    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 55.83/7.45    inference(flattening,[],[f14])).
% 55.83/7.45  
% 55.83/7.45  fof(f34,plain,(
% 55.83/7.45    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 55.83/7.45    inference(cnf_transformation,[],[f15])).
% 55.83/7.45  
% 55.83/7.45  fof(f47,plain,(
% 55.83/7.45    ( ! [X2,X0,X1] : (r1_tarski(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 55.83/7.45    inference(definition_unfolding,[],[f34,f46])).
% 55.83/7.45  
% 55.83/7.45  fof(f31,plain,(
% 55.83/7.45    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 55.83/7.45    inference(cnf_transformation,[],[f28])).
% 55.83/7.45  
% 55.83/7.45  fof(f45,plain,(
% 55.83/7.45    ~r1_tarski(k9_relat_1(sK3,k3_xboole_0(sK1,sK2)),k3_xboole_0(k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK2)))),
% 55.83/7.45    inference(cnf_transformation,[],[f30])).
% 55.83/7.45  
% 55.83/7.45  fof(f49,plain,(
% 55.83/7.45    ~r1_tarski(k9_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))),k1_setfam_1(k1_enumset1(k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK2))))),
% 55.83/7.45    inference(definition_unfolding,[],[f45,f46,f46])).
% 55.83/7.45  
% 55.83/7.45  fof(f10,axiom,(
% 55.83/7.45    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 55.83/7.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.83/7.45  
% 55.83/7.45  fof(f23,plain,(
% 55.83/7.45    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 55.83/7.45    inference(ennf_transformation,[],[f10])).
% 55.83/7.45  
% 55.83/7.45  fof(f43,plain,(
% 55.83/7.45    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 55.83/7.45    inference(cnf_transformation,[],[f23])).
% 55.83/7.45  
% 55.83/7.45  cnf(c_0,plain,
% 55.83/7.45      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 55.83/7.45      inference(cnf_transformation,[],[f33]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_166,plain,
% 55.83/7.45      ( ~ r2_hidden(sK0(X0_41,X1_41),X1_41) | r1_tarski(X0_41,X1_41) ),
% 55.83/7.45      inference(subtyping,[status(esa)],[c_0]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_220274,plain,
% 55.83/7.45      ( ~ r2_hidden(sK0(sK2,sK2),sK2) | r1_tarski(sK2,sK2) ),
% 55.83/7.45      inference(instantiation,[status(thm)],[c_166]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_1,plain,
% 55.83/7.45      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 55.83/7.45      inference(cnf_transformation,[],[f32]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_165,plain,
% 55.83/7.45      ( r2_hidden(sK0(X0_41,X1_41),X0_41) | r1_tarski(X0_41,X1_41) ),
% 55.83/7.45      inference(subtyping,[status(esa)],[c_1]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_162500,plain,
% 55.83/7.45      ( r2_hidden(sK0(X0_41,sK2),X0_41) | r1_tarski(X0_41,sK2) ),
% 55.83/7.45      inference(instantiation,[status(thm)],[c_165]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_220273,plain,
% 55.83/7.45      ( r2_hidden(sK0(sK2,sK2),sK2) | r1_tarski(sK2,sK2) ),
% 55.83/7.45      inference(instantiation,[status(thm)],[c_162500]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_6,plain,
% 55.83/7.45      ( ~ r1_tarski(X0,X1)
% 55.83/7.45      | ~ r1_tarski(X2,X3)
% 55.83/7.45      | r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1))
% 55.83/7.45      | ~ v1_relat_1(X2)
% 55.83/7.45      | ~ v1_relat_1(X3) ),
% 55.83/7.45      inference(cnf_transformation,[],[f39]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_160,plain,
% 55.83/7.45      ( ~ r1_tarski(X0_41,X1_41)
% 55.83/7.45      | ~ r1_tarski(X2_41,X3_41)
% 55.83/7.45      | r1_tarski(k7_relat_1(X2_41,X0_41),k7_relat_1(X3_41,X1_41))
% 55.83/7.45      | ~ v1_relat_1(X2_41)
% 55.83/7.45      | ~ v1_relat_1(X3_41) ),
% 55.83/7.45      inference(subtyping,[status(esa)],[c_6]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_451,plain,
% 55.83/7.45      ( r1_tarski(X0_41,X1_41) != iProver_top
% 55.83/7.45      | r1_tarski(X2_41,X3_41) != iProver_top
% 55.83/7.45      | r1_tarski(k7_relat_1(X2_41,X0_41),k7_relat_1(X3_41,X1_41)) = iProver_top
% 55.83/7.45      | v1_relat_1(X2_41) != iProver_top
% 55.83/7.45      | v1_relat_1(X3_41) != iProver_top ),
% 55.83/7.45      inference(predicate_to_equality,[status(thm)],[c_160]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_12,negated_conjecture,
% 55.83/7.45      ( v1_relat_1(sK3) ),
% 55.83/7.45      inference(cnf_transformation,[],[f44]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_154,negated_conjecture,
% 55.83/7.45      ( v1_relat_1(sK3) ),
% 55.83/7.45      inference(subtyping,[status(esa)],[c_12]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_457,plain,
% 55.83/7.45      ( v1_relat_1(sK3) = iProver_top ),
% 55.83/7.45      inference(predicate_to_equality,[status(thm)],[c_154]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_7,plain,
% 55.83/7.45      ( ~ v1_relat_1(X0)
% 55.83/7.45      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 55.83/7.45      inference(cnf_transformation,[],[f40]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_159,plain,
% 55.83/7.45      ( ~ v1_relat_1(X0_41)
% 55.83/7.45      | k2_relat_1(k7_relat_1(X0_41,X1_41)) = k9_relat_1(X0_41,X1_41) ),
% 55.83/7.45      inference(subtyping,[status(esa)],[c_7]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_452,plain,
% 55.83/7.45      ( k2_relat_1(k7_relat_1(X0_41,X1_41)) = k9_relat_1(X0_41,X1_41)
% 55.83/7.45      | v1_relat_1(X0_41) != iProver_top ),
% 55.83/7.45      inference(predicate_to_equality,[status(thm)],[c_159]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_663,plain,
% 55.83/7.45      ( k2_relat_1(k7_relat_1(sK3,X0_41)) = k9_relat_1(sK3,X0_41) ),
% 55.83/7.45      inference(superposition,[status(thm)],[c_457,c_452]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_4,plain,
% 55.83/7.45      ( ~ v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1)) ),
% 55.83/7.45      inference(cnf_transformation,[],[f37]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_162,plain,
% 55.83/7.45      ( ~ v1_relat_1(X0_41) | v1_relat_1(k7_relat_1(X0_41,X1_41)) ),
% 55.83/7.45      inference(subtyping,[status(esa)],[c_4]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_449,plain,
% 55.83/7.45      ( v1_relat_1(X0_41) != iProver_top
% 55.83/7.45      | v1_relat_1(k7_relat_1(X0_41,X1_41)) = iProver_top ),
% 55.83/7.45      inference(predicate_to_equality,[status(thm)],[c_162]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_664,plain,
% 55.83/7.45      ( k2_relat_1(k7_relat_1(k7_relat_1(X0_41,X1_41),X2_41)) = k9_relat_1(k7_relat_1(X0_41,X1_41),X2_41)
% 55.83/7.45      | v1_relat_1(X0_41) != iProver_top ),
% 55.83/7.45      inference(superposition,[status(thm)],[c_449,c_452]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_790,plain,
% 55.83/7.45      ( k2_relat_1(k7_relat_1(k7_relat_1(sK3,X0_41),X1_41)) = k9_relat_1(k7_relat_1(sK3,X0_41),X1_41) ),
% 55.83/7.45      inference(superposition,[status(thm)],[c_457,c_664]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_8,plain,
% 55.83/7.45      ( ~ r1_tarski(X0,X1)
% 55.83/7.45      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
% 55.83/7.45      | ~ v1_relat_1(X0)
% 55.83/7.45      | ~ v1_relat_1(X1) ),
% 55.83/7.45      inference(cnf_transformation,[],[f42]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_158,plain,
% 55.83/7.45      ( ~ r1_tarski(X0_41,X1_41)
% 55.83/7.45      | r1_tarski(k2_relat_1(X0_41),k2_relat_1(X1_41))
% 55.83/7.45      | ~ v1_relat_1(X0_41)
% 55.83/7.45      | ~ v1_relat_1(X1_41) ),
% 55.83/7.45      inference(subtyping,[status(esa)],[c_8]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_453,plain,
% 55.83/7.45      ( r1_tarski(X0_41,X1_41) != iProver_top
% 55.83/7.45      | r1_tarski(k2_relat_1(X0_41),k2_relat_1(X1_41)) = iProver_top
% 55.83/7.45      | v1_relat_1(X0_41) != iProver_top
% 55.83/7.45      | v1_relat_1(X1_41) != iProver_top ),
% 55.83/7.45      inference(predicate_to_equality,[status(thm)],[c_158]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_1099,plain,
% 55.83/7.45      ( r1_tarski(k9_relat_1(k7_relat_1(sK3,X0_41),X1_41),k2_relat_1(X2_41)) = iProver_top
% 55.83/7.45      | r1_tarski(k7_relat_1(k7_relat_1(sK3,X0_41),X1_41),X2_41) != iProver_top
% 55.83/7.45      | v1_relat_1(X2_41) != iProver_top
% 55.83/7.45      | v1_relat_1(k7_relat_1(k7_relat_1(sK3,X0_41),X1_41)) != iProver_top ),
% 55.83/7.45      inference(superposition,[status(thm)],[c_790,c_453]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_13,plain,
% 55.83/7.45      ( v1_relat_1(sK3) = iProver_top ),
% 55.83/7.45      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_5,plain,
% 55.83/7.45      ( ~ v1_relat_1(X0)
% 55.83/7.45      | k7_relat_1(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))) = k7_relat_1(k7_relat_1(X0,X1),X2) ),
% 55.83/7.45      inference(cnf_transformation,[],[f48]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_161,plain,
% 55.83/7.45      ( ~ v1_relat_1(X0_41)
% 55.83/7.45      | k7_relat_1(X0_41,k1_setfam_1(k1_enumset1(X1_41,X1_41,X2_41))) = k7_relat_1(k7_relat_1(X0_41,X1_41),X2_41) ),
% 55.83/7.45      inference(subtyping,[status(esa)],[c_5]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_450,plain,
% 55.83/7.45      ( k7_relat_1(X0_41,k1_setfam_1(k1_enumset1(X1_41,X1_41,X2_41))) = k7_relat_1(k7_relat_1(X0_41,X1_41),X2_41)
% 55.83/7.45      | v1_relat_1(X0_41) != iProver_top ),
% 55.83/7.45      inference(predicate_to_equality,[status(thm)],[c_161]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_946,plain,
% 55.83/7.45      ( k7_relat_1(sK3,k1_setfam_1(k1_enumset1(X0_41,X0_41,X1_41))) = k7_relat_1(k7_relat_1(sK3,X0_41),X1_41) ),
% 55.83/7.45      inference(superposition,[status(thm)],[c_457,c_450]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_1215,plain,
% 55.83/7.45      ( v1_relat_1(k7_relat_1(k7_relat_1(sK3,X0_41),X1_41)) = iProver_top
% 55.83/7.45      | v1_relat_1(sK3) != iProver_top ),
% 55.83/7.45      inference(superposition,[status(thm)],[c_946,c_449]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_5016,plain,
% 55.83/7.45      ( v1_relat_1(X2_41) != iProver_top
% 55.83/7.45      | r1_tarski(k7_relat_1(k7_relat_1(sK3,X0_41),X1_41),X2_41) != iProver_top
% 55.83/7.45      | r1_tarski(k9_relat_1(k7_relat_1(sK3,X0_41),X1_41),k2_relat_1(X2_41)) = iProver_top ),
% 55.83/7.45      inference(global_propositional_subsumption,
% 55.83/7.45                [status(thm)],
% 55.83/7.45                [c_1099,c_13,c_1215]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_5017,plain,
% 55.83/7.45      ( r1_tarski(k9_relat_1(k7_relat_1(sK3,X0_41),X1_41),k2_relat_1(X2_41)) = iProver_top
% 55.83/7.45      | r1_tarski(k7_relat_1(k7_relat_1(sK3,X0_41),X1_41),X2_41) != iProver_top
% 55.83/7.45      | v1_relat_1(X2_41) != iProver_top ),
% 55.83/7.45      inference(renaming,[status(thm)],[c_5016]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_5026,plain,
% 55.83/7.45      ( r1_tarski(k9_relat_1(k7_relat_1(sK3,X0_41),X1_41),k9_relat_1(sK3,X2_41)) = iProver_top
% 55.83/7.45      | r1_tarski(k7_relat_1(k7_relat_1(sK3,X0_41),X1_41),k7_relat_1(sK3,X2_41)) != iProver_top
% 55.83/7.45      | v1_relat_1(k7_relat_1(sK3,X2_41)) != iProver_top ),
% 55.83/7.45      inference(superposition,[status(thm)],[c_663,c_5017]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_6249,plain,
% 55.83/7.45      ( r1_tarski(X0_41,X1_41) != iProver_top
% 55.83/7.45      | r1_tarski(k9_relat_1(k7_relat_1(sK3,X2_41),X0_41),k9_relat_1(sK3,X1_41)) = iProver_top
% 55.83/7.45      | r1_tarski(k7_relat_1(sK3,X2_41),sK3) != iProver_top
% 55.83/7.45      | v1_relat_1(k7_relat_1(sK3,X1_41)) != iProver_top
% 55.83/7.45      | v1_relat_1(k7_relat_1(sK3,X2_41)) != iProver_top
% 55.83/7.45      | v1_relat_1(sK3) != iProver_top ),
% 55.83/7.45      inference(superposition,[status(thm)],[c_451,c_5026]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_106440,plain,
% 55.83/7.45      ( v1_relat_1(k7_relat_1(sK3,X2_41)) != iProver_top
% 55.83/7.45      | v1_relat_1(k7_relat_1(sK3,X1_41)) != iProver_top
% 55.83/7.45      | r1_tarski(k7_relat_1(sK3,X2_41),sK3) != iProver_top
% 55.83/7.45      | r1_tarski(k9_relat_1(k7_relat_1(sK3,X2_41),X0_41),k9_relat_1(sK3,X1_41)) = iProver_top
% 55.83/7.45      | r1_tarski(X0_41,X1_41) != iProver_top ),
% 55.83/7.45      inference(global_propositional_subsumption,
% 55.83/7.45                [status(thm)],
% 55.83/7.45                [c_6249,c_13]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_106441,plain,
% 55.83/7.45      ( r1_tarski(X0_41,X1_41) != iProver_top
% 55.83/7.45      | r1_tarski(k9_relat_1(k7_relat_1(sK3,X2_41),X0_41),k9_relat_1(sK3,X1_41)) = iProver_top
% 55.83/7.45      | r1_tarski(k7_relat_1(sK3,X2_41),sK3) != iProver_top
% 55.83/7.45      | v1_relat_1(k7_relat_1(sK3,X1_41)) != iProver_top
% 55.83/7.45      | v1_relat_1(k7_relat_1(sK3,X2_41)) != iProver_top ),
% 55.83/7.45      inference(renaming,[status(thm)],[c_106440]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_446,plain,
% 55.83/7.45      ( r2_hidden(sK0(X0_41,X1_41),X0_41) = iProver_top
% 55.83/7.45      | r1_tarski(X0_41,X1_41) = iProver_top ),
% 55.83/7.45      inference(predicate_to_equality,[status(thm)],[c_165]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_3,plain,
% 55.83/7.45      ( ~ r1_tarski(X0,X1)
% 55.83/7.45      | ~ r1_tarski(X0,X2)
% 55.83/7.45      | r1_tarski(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))) ),
% 55.83/7.45      inference(cnf_transformation,[],[f47]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_163,plain,
% 55.83/7.45      ( ~ r1_tarski(X0_41,X1_41)
% 55.83/7.45      | ~ r1_tarski(X0_41,X2_41)
% 55.83/7.45      | r1_tarski(X0_41,k1_setfam_1(k1_enumset1(X1_41,X1_41,X2_41))) ),
% 55.83/7.45      inference(subtyping,[status(esa)],[c_3]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_448,plain,
% 55.83/7.45      ( r1_tarski(X0_41,X1_41) != iProver_top
% 55.83/7.45      | r1_tarski(X0_41,X2_41) != iProver_top
% 55.83/7.45      | r1_tarski(X0_41,k1_setfam_1(k1_enumset1(X1_41,X1_41,X2_41))) = iProver_top ),
% 55.83/7.45      inference(predicate_to_equality,[status(thm)],[c_163]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_2,plain,
% 55.83/7.45      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 55.83/7.45      inference(cnf_transformation,[],[f31]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_164,plain,
% 55.83/7.45      ( ~ r2_hidden(X0_43,X0_41)
% 55.83/7.45      | r2_hidden(X0_43,X1_41)
% 55.83/7.45      | ~ r1_tarski(X0_41,X1_41) ),
% 55.83/7.45      inference(subtyping,[status(esa)],[c_2]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_447,plain,
% 55.83/7.45      ( r2_hidden(X0_43,X0_41) != iProver_top
% 55.83/7.45      | r2_hidden(X0_43,X1_41) = iProver_top
% 55.83/7.45      | r1_tarski(X0_41,X1_41) != iProver_top ),
% 55.83/7.45      inference(predicate_to_equality,[status(thm)],[c_164]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_963,plain,
% 55.83/7.45      ( r2_hidden(X0_43,X0_41) != iProver_top
% 55.83/7.45      | r2_hidden(X0_43,k1_setfam_1(k1_enumset1(X1_41,X1_41,X2_41))) = iProver_top
% 55.83/7.45      | r1_tarski(X0_41,X1_41) != iProver_top
% 55.83/7.45      | r1_tarski(X0_41,X2_41) != iProver_top ),
% 55.83/7.45      inference(superposition,[status(thm)],[c_448,c_447]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_5303,plain,
% 55.83/7.45      ( r2_hidden(X0_43,k2_relat_1(X0_41)) != iProver_top
% 55.83/7.45      | r2_hidden(X0_43,k1_setfam_1(k1_enumset1(k2_relat_1(X1_41),k2_relat_1(X1_41),X2_41))) = iProver_top
% 55.83/7.45      | r1_tarski(X0_41,X1_41) != iProver_top
% 55.83/7.45      | r1_tarski(k2_relat_1(X0_41),X2_41) != iProver_top
% 55.83/7.45      | v1_relat_1(X0_41) != iProver_top
% 55.83/7.45      | v1_relat_1(X1_41) != iProver_top ),
% 55.83/7.45      inference(superposition,[status(thm)],[c_453,c_963]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_78913,plain,
% 55.83/7.45      ( r2_hidden(sK0(k2_relat_1(X0_41),X1_41),k1_setfam_1(k1_enumset1(k2_relat_1(X2_41),k2_relat_1(X2_41),X3_41))) = iProver_top
% 55.83/7.45      | r1_tarski(X0_41,X2_41) != iProver_top
% 55.83/7.45      | r1_tarski(k2_relat_1(X0_41),X3_41) != iProver_top
% 55.83/7.45      | r1_tarski(k2_relat_1(X0_41),X1_41) = iProver_top
% 55.83/7.45      | v1_relat_1(X0_41) != iProver_top
% 55.83/7.45      | v1_relat_1(X2_41) != iProver_top ),
% 55.83/7.45      inference(superposition,[status(thm)],[c_446,c_5303]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_445,plain,
% 55.83/7.45      ( r2_hidden(sK0(X0_41,X1_41),X1_41) != iProver_top
% 55.83/7.45      | r1_tarski(X0_41,X1_41) = iProver_top ),
% 55.83/7.45      inference(predicate_to_equality,[status(thm)],[c_166]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_98635,plain,
% 55.83/7.45      ( r1_tarski(X0_41,X1_41) != iProver_top
% 55.83/7.45      | r1_tarski(k2_relat_1(X0_41),X2_41) != iProver_top
% 55.83/7.45      | r1_tarski(k2_relat_1(X0_41),k1_setfam_1(k1_enumset1(k2_relat_1(X1_41),k2_relat_1(X1_41),X2_41))) = iProver_top
% 55.83/7.45      | v1_relat_1(X0_41) != iProver_top
% 55.83/7.45      | v1_relat_1(X1_41) != iProver_top ),
% 55.83/7.45      inference(superposition,[status(thm)],[c_78913,c_445]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_99034,plain,
% 55.83/7.45      ( r1_tarski(k9_relat_1(k7_relat_1(sK3,X0_41),X1_41),k1_setfam_1(k1_enumset1(k2_relat_1(X2_41),k2_relat_1(X2_41),X3_41))) = iProver_top
% 55.83/7.45      | r1_tarski(k7_relat_1(k7_relat_1(sK3,X0_41),X1_41),X2_41) != iProver_top
% 55.83/7.45      | r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK3,X0_41),X1_41)),X3_41) != iProver_top
% 55.83/7.45      | v1_relat_1(X2_41) != iProver_top
% 55.83/7.45      | v1_relat_1(k7_relat_1(k7_relat_1(sK3,X0_41),X1_41)) != iProver_top ),
% 55.83/7.45      inference(superposition,[status(thm)],[c_790,c_98635]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_99552,plain,
% 55.83/7.45      ( r1_tarski(k9_relat_1(k7_relat_1(sK3,X0_41),X1_41),X2_41) != iProver_top
% 55.83/7.45      | r1_tarski(k9_relat_1(k7_relat_1(sK3,X0_41),X1_41),k1_setfam_1(k1_enumset1(k2_relat_1(X3_41),k2_relat_1(X3_41),X2_41))) = iProver_top
% 55.83/7.45      | r1_tarski(k7_relat_1(k7_relat_1(sK3,X0_41),X1_41),X3_41) != iProver_top
% 55.83/7.45      | v1_relat_1(X3_41) != iProver_top
% 55.83/7.45      | v1_relat_1(k7_relat_1(k7_relat_1(sK3,X0_41),X1_41)) != iProver_top ),
% 55.83/7.45      inference(light_normalisation,[status(thm)],[c_99034,c_790]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_130923,plain,
% 55.83/7.45      ( v1_relat_1(X3_41) != iProver_top
% 55.83/7.45      | r1_tarski(k7_relat_1(k7_relat_1(sK3,X0_41),X1_41),X3_41) != iProver_top
% 55.83/7.45      | r1_tarski(k9_relat_1(k7_relat_1(sK3,X0_41),X1_41),k1_setfam_1(k1_enumset1(k2_relat_1(X3_41),k2_relat_1(X3_41),X2_41))) = iProver_top
% 55.83/7.45      | r1_tarski(k9_relat_1(k7_relat_1(sK3,X0_41),X1_41),X2_41) != iProver_top ),
% 55.83/7.45      inference(global_propositional_subsumption,
% 55.83/7.45                [status(thm)],
% 55.83/7.45                [c_99552,c_13,c_1215]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_130924,plain,
% 55.83/7.45      ( r1_tarski(k9_relat_1(k7_relat_1(sK3,X0_41),X1_41),X2_41) != iProver_top
% 55.83/7.45      | r1_tarski(k9_relat_1(k7_relat_1(sK3,X0_41),X1_41),k1_setfam_1(k1_enumset1(k2_relat_1(X3_41),k2_relat_1(X3_41),X2_41))) = iProver_top
% 55.83/7.45      | r1_tarski(k7_relat_1(k7_relat_1(sK3,X0_41),X1_41),X3_41) != iProver_top
% 55.83/7.45      | v1_relat_1(X3_41) != iProver_top ),
% 55.83/7.45      inference(renaming,[status(thm)],[c_130923]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_130949,plain,
% 55.83/7.45      ( r1_tarski(k9_relat_1(k7_relat_1(sK3,X0_41),X1_41),X2_41) != iProver_top
% 55.83/7.45      | r1_tarski(k9_relat_1(k7_relat_1(sK3,X0_41),X1_41),k1_setfam_1(k1_enumset1(k9_relat_1(sK3,X3_41),k9_relat_1(sK3,X3_41),X2_41))) = iProver_top
% 55.83/7.45      | r1_tarski(k7_relat_1(k7_relat_1(sK3,X0_41),X1_41),k7_relat_1(sK3,X3_41)) != iProver_top
% 55.83/7.45      | v1_relat_1(k7_relat_1(sK3,X3_41)) != iProver_top ),
% 55.83/7.45      inference(superposition,[status(thm)],[c_663,c_130924]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_1217,plain,
% 55.83/7.45      ( k9_relat_1(sK3,k1_setfam_1(k1_enumset1(X0_41,X0_41,X1_41))) = k2_relat_1(k7_relat_1(k7_relat_1(sK3,X0_41),X1_41)) ),
% 55.83/7.45      inference(superposition,[status(thm)],[c_946,c_663]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_1219,plain,
% 55.83/7.45      ( k9_relat_1(sK3,k1_setfam_1(k1_enumset1(X0_41,X0_41,X1_41))) = k9_relat_1(k7_relat_1(sK3,X0_41),X1_41) ),
% 55.83/7.45      inference(light_normalisation,[status(thm)],[c_1217,c_790]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_11,negated_conjecture,
% 55.83/7.45      ( ~ r1_tarski(k9_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))),k1_setfam_1(k1_enumset1(k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK2)))) ),
% 55.83/7.45      inference(cnf_transformation,[],[f49]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_155,negated_conjecture,
% 55.83/7.45      ( ~ r1_tarski(k9_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))),k1_setfam_1(k1_enumset1(k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK2)))) ),
% 55.83/7.45      inference(subtyping,[status(esa)],[c_11]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_456,plain,
% 55.83/7.45      ( r1_tarski(k9_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))),k1_setfam_1(k1_enumset1(k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK2)))) != iProver_top ),
% 55.83/7.45      inference(predicate_to_equality,[status(thm)],[c_155]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_1351,plain,
% 55.83/7.45      ( r1_tarski(k9_relat_1(k7_relat_1(sK3,sK1),sK2),k1_setfam_1(k1_enumset1(k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK2)))) != iProver_top ),
% 55.83/7.45      inference(demodulation,[status(thm)],[c_1219,c_456]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_132024,plain,
% 55.83/7.45      ( r1_tarski(k9_relat_1(k7_relat_1(sK3,sK1),sK2),k9_relat_1(sK3,sK2)) != iProver_top
% 55.83/7.45      | r1_tarski(k7_relat_1(k7_relat_1(sK3,sK1),sK2),k7_relat_1(sK3,sK1)) != iProver_top
% 55.83/7.45      | v1_relat_1(k7_relat_1(sK3,sK1)) != iProver_top ),
% 55.83/7.45      inference(superposition,[status(thm)],[c_130949,c_1351]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_18349,plain,
% 55.83/7.45      ( v1_relat_1(k7_relat_1(sK3,sK1)) | ~ v1_relat_1(sK3) ),
% 55.83/7.45      inference(instantiation,[status(thm)],[c_162]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_18350,plain,
% 55.83/7.45      ( v1_relat_1(k7_relat_1(sK3,sK1)) = iProver_top
% 55.83/7.45      | v1_relat_1(sK3) != iProver_top ),
% 55.83/7.45      inference(predicate_to_equality,[status(thm)],[c_18349]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_172,plain,
% 55.83/7.45      ( ~ r1_tarski(X0_41,X1_41)
% 55.83/7.45      | r1_tarski(X2_41,X3_41)
% 55.83/7.45      | X2_41 != X0_41
% 55.83/7.45      | X3_41 != X1_41 ),
% 55.83/7.45      theory(equality) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_168,plain,( X0_41 = X0_41 ),theory(equality) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_1391,plain,
% 55.83/7.45      ( ~ r1_tarski(X0_41,X1_41)
% 55.83/7.45      | r1_tarski(X2_41,X1_41)
% 55.83/7.45      | X2_41 != X0_41 ),
% 55.83/7.45      inference(resolution,[status(thm)],[c_172,c_168]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_178,plain,
% 55.83/7.45      ( X0_41 != X1_41 | k2_relat_1(X0_41) = k2_relat_1(X1_41) ),
% 55.83/7.45      theory(equality) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_1416,plain,
% 55.83/7.45      ( ~ r1_tarski(k2_relat_1(X0_41),X1_41)
% 55.83/7.45      | r1_tarski(k2_relat_1(X2_41),X1_41)
% 55.83/7.45      | X2_41 != X0_41 ),
% 55.83/7.45      inference(resolution,[status(thm)],[c_1391,c_178]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_1558,plain,
% 55.83/7.45      ( r1_tarski(k2_relat_1(k7_relat_1(X0_41,k1_setfam_1(k1_enumset1(X1_41,X1_41,X2_41)))),X3_41)
% 55.83/7.45      | ~ r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(X0_41,X1_41),X2_41)),X3_41)
% 55.83/7.45      | ~ v1_relat_1(X0_41) ),
% 55.83/7.45      inference(resolution,[status(thm)],[c_1416,c_161]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_171,plain,
% 55.83/7.45      ( X0_41 != X1_41 | X2_41 != X1_41 | X2_41 = X0_41 ),
% 55.83/7.45      theory(equality) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_1845,plain,
% 55.83/7.45      ( X0_41 != X1_41 | X1_41 = X0_41 ),
% 55.83/7.45      inference(resolution,[status(thm)],[c_171,c_168]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_2927,plain,
% 55.83/7.45      ( ~ v1_relat_1(X0_41)
% 55.83/7.45      | k9_relat_1(X0_41,X1_41) = k2_relat_1(k7_relat_1(X0_41,X1_41)) ),
% 55.83/7.45      inference(resolution,[status(thm)],[c_1845,c_159]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_3323,plain,
% 55.83/7.45      ( r1_tarski(k9_relat_1(X0_41,X1_41),X2_41)
% 55.83/7.45      | ~ r1_tarski(k2_relat_1(k7_relat_1(X0_41,X1_41)),X2_41)
% 55.83/7.45      | ~ v1_relat_1(X0_41) ),
% 55.83/7.45      inference(resolution,[status(thm)],[c_2927,c_1391]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_35413,plain,
% 55.83/7.45      ( r1_tarski(k9_relat_1(X0_41,k1_setfam_1(k1_enumset1(X1_41,X1_41,X2_41))),X3_41)
% 55.83/7.45      | ~ r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(X0_41,X1_41),X2_41)),X3_41)
% 55.83/7.45      | ~ v1_relat_1(X0_41) ),
% 55.83/7.45      inference(resolution,[status(thm)],[c_1558,c_3323]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_109102,plain,
% 55.83/7.45      ( ~ r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK3,sK1),sK2)),k1_setfam_1(k1_enumset1(k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK2))))
% 55.83/7.45      | ~ v1_relat_1(sK3) ),
% 55.83/7.45      inference(resolution,[status(thm)],[c_35413,c_155]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_644,plain,
% 55.83/7.45      ( k1_setfam_1(k1_enumset1(k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK2))) = k1_setfam_1(k1_enumset1(k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK2))) ),
% 55.83/7.45      inference(instantiation,[status(thm)],[c_168]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_747,plain,
% 55.83/7.45      ( k9_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))) = k9_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))) ),
% 55.83/7.45      inference(instantiation,[status(thm)],[c_168]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_737,plain,
% 55.83/7.45      ( X0_41 != X1_41
% 55.83/7.45      | k9_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))) != X1_41
% 55.83/7.45      | k9_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))) = X0_41 ),
% 55.83/7.45      inference(instantiation,[status(thm)],[c_171]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_913,plain,
% 55.83/7.45      ( X0_41 != k9_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2)))
% 55.83/7.45      | k9_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))) = X0_41
% 55.83/7.45      | k9_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))) != k9_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))) ),
% 55.83/7.45      inference(instantiation,[status(thm)],[c_737]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_1160,plain,
% 55.83/7.45      ( k9_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))) != k9_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2)))
% 55.83/7.45      | k9_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))) = k2_relat_1(k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))))
% 55.83/7.45      | k2_relat_1(k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2)))) != k9_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))) ),
% 55.83/7.45      inference(instantiation,[status(thm)],[c_913]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_1161,plain,
% 55.83/7.45      ( ~ v1_relat_1(sK3)
% 55.83/7.45      | k2_relat_1(k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2)))) = k9_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))) ),
% 55.83/7.45      inference(instantiation,[status(thm)],[c_159]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_599,plain,
% 55.83/7.45      ( ~ r1_tarski(X0_41,X1_41)
% 55.83/7.45      | r1_tarski(k9_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))),k1_setfam_1(k1_enumset1(k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK2))))
% 55.83/7.45      | k9_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))) != X0_41
% 55.83/7.45      | k1_setfam_1(k1_enumset1(k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK2))) != X1_41 ),
% 55.83/7.45      inference(instantiation,[status(thm)],[c_172]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_643,plain,
% 55.83/7.45      ( ~ r1_tarski(X0_41,k1_setfam_1(k1_enumset1(k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK2))))
% 55.83/7.45      | r1_tarski(k9_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))),k1_setfam_1(k1_enumset1(k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK2))))
% 55.83/7.45      | k9_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))) != X0_41
% 55.83/7.45      | k1_setfam_1(k1_enumset1(k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK2))) != k1_setfam_1(k1_enumset1(k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK2))) ),
% 55.83/7.45      inference(instantiation,[status(thm)],[c_599]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_1606,plain,
% 55.83/7.45      ( r1_tarski(k9_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))),k1_setfam_1(k1_enumset1(k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK2))))
% 55.83/7.45      | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2)))),k1_setfam_1(k1_enumset1(k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK2))))
% 55.83/7.45      | k9_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))) != k2_relat_1(k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))))
% 55.83/7.45      | k1_setfam_1(k1_enumset1(k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK2))) != k1_setfam_1(k1_enumset1(k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK2))) ),
% 55.83/7.45      inference(instantiation,[status(thm)],[c_643]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_2964,plain,
% 55.83/7.45      ( k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))) != X0_41
% 55.83/7.45      | k2_relat_1(k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2)))) = k2_relat_1(X0_41) ),
% 55.83/7.45      inference(instantiation,[status(thm)],[c_178]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_5693,plain,
% 55.83/7.45      ( k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))) != k7_relat_1(k7_relat_1(sK3,sK1),sK2)
% 55.83/7.45      | k2_relat_1(k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2)))) = k2_relat_1(k7_relat_1(k7_relat_1(sK3,sK1),sK2)) ),
% 55.83/7.45      inference(instantiation,[status(thm)],[c_2964]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_5694,plain,
% 55.83/7.45      ( ~ v1_relat_1(sK3)
% 55.83/7.45      | k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))) = k7_relat_1(k7_relat_1(sK3,sK1),sK2) ),
% 55.83/7.45      inference(instantiation,[status(thm)],[c_161]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_1885,plain,
% 55.83/7.45      ( ~ r1_tarski(X0_41,X1_41)
% 55.83/7.45      | r1_tarski(k2_relat_1(k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2)))),k1_setfam_1(k1_enumset1(k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK2))))
% 55.83/7.45      | k2_relat_1(k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2)))) != X0_41
% 55.83/7.45      | k1_setfam_1(k1_enumset1(k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK2))) != X1_41 ),
% 55.83/7.45      inference(instantiation,[status(thm)],[c_172]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_2842,plain,
% 55.83/7.45      ( ~ r1_tarski(X0_41,k1_setfam_1(k1_enumset1(k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK2))))
% 55.83/7.45      | r1_tarski(k2_relat_1(k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2)))),k1_setfam_1(k1_enumset1(k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK2))))
% 55.83/7.45      | k2_relat_1(k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2)))) != X0_41
% 55.83/7.45      | k1_setfam_1(k1_enumset1(k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK2))) != k1_setfam_1(k1_enumset1(k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK2))) ),
% 55.83/7.45      inference(instantiation,[status(thm)],[c_1885]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_9287,plain,
% 55.83/7.45      ( ~ r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK3,sK1),sK2)),k1_setfam_1(k1_enumset1(k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK2))))
% 55.83/7.45      | r1_tarski(k2_relat_1(k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2)))),k1_setfam_1(k1_enumset1(k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK2))))
% 55.83/7.45      | k2_relat_1(k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2)))) != k2_relat_1(k7_relat_1(k7_relat_1(sK3,sK1),sK2))
% 55.83/7.45      | k1_setfam_1(k1_enumset1(k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK2))) != k1_setfam_1(k1_enumset1(k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK2))) ),
% 55.83/7.45      inference(instantiation,[status(thm)],[c_2842]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_109205,plain,
% 55.83/7.45      ( ~ r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK3,sK1),sK2)),k1_setfam_1(k1_enumset1(k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK2)))) ),
% 55.83/7.45      inference(global_propositional_subsumption,
% 55.83/7.45                [status(thm)],
% 55.83/7.45                [c_109102,c_12,c_11,c_644,c_747,c_1160,c_1161,c_1606,
% 55.83/7.45                 c_5693,c_5694,c_9287]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_109499,plain,
% 55.83/7.45      ( ~ r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK3,sK1),sK2)),k9_relat_1(sK3,sK2))
% 55.83/7.45      | ~ r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK3,sK1),sK2)),k9_relat_1(sK3,sK1)) ),
% 55.83/7.45      inference(resolution,[status(thm)],[c_109205,c_163]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_1052,plain,
% 55.83/7.45      ( k9_relat_1(sK3,sK1) = k9_relat_1(sK3,sK1) ),
% 55.83/7.45      inference(instantiation,[status(thm)],[c_168]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_1453,plain,
% 55.83/7.45      ( k9_relat_1(sK3,sK2) = k9_relat_1(sK3,sK2) ),
% 55.83/7.45      inference(instantiation,[status(thm)],[c_168]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_1890,plain,
% 55.83/7.45      ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2)))),k9_relat_1(sK3,sK2))
% 55.83/7.45      | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2)))),k9_relat_1(sK3,sK1))
% 55.83/7.45      | r1_tarski(k2_relat_1(k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2)))),k1_setfam_1(k1_enumset1(k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK2)))) ),
% 55.83/7.45      inference(instantiation,[status(thm)],[c_163]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_854,plain,
% 55.83/7.45      ( X0_41 != X1_41
% 55.83/7.45      | k9_relat_1(sK3,sK1) != X1_41
% 55.83/7.45      | k9_relat_1(sK3,sK1) = X0_41 ),
% 55.83/7.45      inference(instantiation,[status(thm)],[c_171]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_1419,plain,
% 55.83/7.45      ( X0_41 != k9_relat_1(sK3,sK1)
% 55.83/7.45      | k9_relat_1(sK3,sK1) = X0_41
% 55.83/7.45      | k9_relat_1(sK3,sK1) != k9_relat_1(sK3,sK1) ),
% 55.83/7.45      inference(instantiation,[status(thm)],[c_854]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_2121,plain,
% 55.83/7.45      ( k9_relat_1(sK3,sK1) != k9_relat_1(sK3,sK1)
% 55.83/7.45      | k9_relat_1(sK3,sK1) = k2_relat_1(k7_relat_1(sK3,sK1))
% 55.83/7.45      | k2_relat_1(k7_relat_1(sK3,sK1)) != k9_relat_1(sK3,sK1) ),
% 55.83/7.45      inference(instantiation,[status(thm)],[c_1419]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_2122,plain,
% 55.83/7.45      ( ~ v1_relat_1(sK3)
% 55.83/7.45      | k2_relat_1(k7_relat_1(sK3,sK1)) = k9_relat_1(sK3,sK1) ),
% 55.83/7.45      inference(instantiation,[status(thm)],[c_159]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_2624,plain,
% 55.83/7.45      ( v1_relat_1(k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))))
% 55.83/7.45      | ~ v1_relat_1(sK3) ),
% 55.83/7.45      inference(instantiation,[status(thm)],[c_162]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_2959,plain,
% 55.83/7.45      ( k2_relat_1(k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2)))) = k2_relat_1(k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2)))) ),
% 55.83/7.45      inference(instantiation,[status(thm)],[c_168]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_6449,plain,
% 55.83/7.45      ( ~ r1_tarski(k7_relat_1(X0_41,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))),k7_relat_1(sK3,sK1))
% 55.83/7.45      | r1_tarski(k2_relat_1(k7_relat_1(X0_41,k1_setfam_1(k1_enumset1(sK1,sK1,sK2)))),k2_relat_1(k7_relat_1(sK3,sK1)))
% 55.83/7.45      | ~ v1_relat_1(k7_relat_1(X0_41,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))))
% 55.83/7.45      | ~ v1_relat_1(k7_relat_1(sK3,sK1)) ),
% 55.83/7.45      inference(instantiation,[status(thm)],[c_158]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_6451,plain,
% 55.83/7.45      ( ~ r1_tarski(k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))),k7_relat_1(sK3,sK1))
% 55.83/7.45      | r1_tarski(k2_relat_1(k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2)))),k2_relat_1(k7_relat_1(sK3,sK1)))
% 55.83/7.45      | ~ v1_relat_1(k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))))
% 55.83/7.45      | ~ v1_relat_1(k7_relat_1(sK3,sK1)) ),
% 55.83/7.45      inference(instantiation,[status(thm)],[c_6449]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_9574,plain,
% 55.83/7.45      ( k7_relat_1(sK3,sK1) = k7_relat_1(sK3,sK1) ),
% 55.83/7.45      inference(instantiation,[status(thm)],[c_168]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_1928,plain,
% 55.83/7.45      ( ~ r1_tarski(X0_41,X1_41)
% 55.83/7.45      | r1_tarski(k2_relat_1(k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2)))),X2_41)
% 55.83/7.45      | X2_41 != X1_41
% 55.83/7.45      | k2_relat_1(k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2)))) != X0_41 ),
% 55.83/7.45      inference(instantiation,[status(thm)],[c_172]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_2958,plain,
% 55.83/7.45      ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2)))),X0_41)
% 55.83/7.45      | r1_tarski(k2_relat_1(k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2)))),X1_41)
% 55.83/7.45      | X1_41 != X0_41
% 55.83/7.45      | k2_relat_1(k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2)))) != k2_relat_1(k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2)))) ),
% 55.83/7.45      inference(instantiation,[status(thm)],[c_1928]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_7644,plain,
% 55.83/7.45      ( r1_tarski(k2_relat_1(k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2)))),X0_41)
% 55.83/7.45      | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2)))),k2_relat_1(X1_41))
% 55.83/7.45      | X0_41 != k2_relat_1(X1_41)
% 55.83/7.45      | k2_relat_1(k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2)))) != k2_relat_1(k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2)))) ),
% 55.83/7.45      inference(instantiation,[status(thm)],[c_2958]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_19198,plain,
% 55.83/7.45      ( r1_tarski(k2_relat_1(k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2)))),k9_relat_1(sK3,sK1))
% 55.83/7.45      | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2)))),k2_relat_1(k7_relat_1(sK3,sK1)))
% 55.83/7.45      | k9_relat_1(sK3,sK1) != k2_relat_1(k7_relat_1(sK3,sK1))
% 55.83/7.45      | k2_relat_1(k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2)))) != k2_relat_1(k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2)))) ),
% 55.83/7.45      inference(instantiation,[status(thm)],[c_7644]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_10,plain,
% 55.83/7.45      ( r1_tarski(k7_relat_1(X0,X1),X0) | ~ v1_relat_1(X0) ),
% 55.83/7.45      inference(cnf_transformation,[],[f43]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_156,plain,
% 55.83/7.45      ( r1_tarski(k7_relat_1(X0_41,X1_41),X0_41) | ~ v1_relat_1(X0_41) ),
% 55.83/7.45      inference(subtyping,[status(esa)],[c_10]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_25552,plain,
% 55.83/7.45      ( r1_tarski(k7_relat_1(k7_relat_1(sK3,sK1),sK2),k7_relat_1(sK3,sK1))
% 55.83/7.45      | ~ v1_relat_1(k7_relat_1(sK3,sK1)) ),
% 55.83/7.45      inference(instantiation,[status(thm)],[c_156]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_2672,plain,
% 55.83/7.45      ( ~ r1_tarski(X0_41,X1_41)
% 55.83/7.45      | r1_tarski(X2_41,k9_relat_1(sK3,sK2))
% 55.83/7.45      | X2_41 != X0_41
% 55.83/7.45      | k9_relat_1(sK3,sK2) != X1_41 ),
% 55.83/7.45      inference(instantiation,[status(thm)],[c_172]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_8375,plain,
% 55.83/7.45      ( ~ r1_tarski(X0_41,k9_relat_1(sK3,sK2))
% 55.83/7.45      | r1_tarski(X1_41,k9_relat_1(sK3,sK2))
% 55.83/7.45      | X1_41 != X0_41
% 55.83/7.45      | k9_relat_1(sK3,sK2) != k9_relat_1(sK3,sK2) ),
% 55.83/7.45      inference(instantiation,[status(thm)],[c_2672]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_24885,plain,
% 55.83/7.45      ( ~ r1_tarski(X0_41,k9_relat_1(sK3,sK2))
% 55.83/7.45      | r1_tarski(k2_relat_1(k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2)))),k9_relat_1(sK3,sK2))
% 55.83/7.45      | k9_relat_1(sK3,sK2) != k9_relat_1(sK3,sK2)
% 55.83/7.45      | k2_relat_1(k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2)))) != X0_41 ),
% 55.83/7.45      inference(instantiation,[status(thm)],[c_8375]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_35786,plain,
% 55.83/7.45      ( ~ r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK3,sK1),sK2)),k9_relat_1(sK3,sK2))
% 55.83/7.45      | r1_tarski(k2_relat_1(k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2)))),k9_relat_1(sK3,sK2))
% 55.83/7.45      | k9_relat_1(sK3,sK2) != k9_relat_1(sK3,sK2)
% 55.83/7.45      | k2_relat_1(k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2)))) != k2_relat_1(k7_relat_1(k7_relat_1(sK3,sK1),sK2)) ),
% 55.83/7.45      inference(instantiation,[status(thm)],[c_24885]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_5187,plain,
% 55.83/7.45      ( ~ r1_tarski(X0_41,X1_41)
% 55.83/7.45      | r1_tarski(k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))),X2_41)
% 55.83/7.45      | X2_41 != X1_41
% 55.83/7.45      | k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))) != X0_41 ),
% 55.83/7.45      inference(instantiation,[status(thm)],[c_172]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_9308,plain,
% 55.83/7.45      ( ~ r1_tarski(k7_relat_1(k7_relat_1(sK3,sK1),sK2),X0_41)
% 55.83/7.45      | r1_tarski(k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))),X1_41)
% 55.83/7.45      | X1_41 != X0_41
% 55.83/7.45      | k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))) != k7_relat_1(k7_relat_1(sK3,sK1),sK2) ),
% 55.83/7.45      inference(instantiation,[status(thm)],[c_5187]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_25551,plain,
% 55.83/7.45      ( ~ r1_tarski(k7_relat_1(k7_relat_1(sK3,sK1),sK2),k7_relat_1(sK3,sK1))
% 55.83/7.45      | r1_tarski(k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))),X0_41)
% 55.83/7.45      | X0_41 != k7_relat_1(sK3,sK1)
% 55.83/7.45      | k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))) != k7_relat_1(k7_relat_1(sK3,sK1),sK2) ),
% 55.83/7.45      inference(instantiation,[status(thm)],[c_9308]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_69122,plain,
% 55.83/7.45      ( ~ r1_tarski(k7_relat_1(k7_relat_1(sK3,sK1),sK2),k7_relat_1(sK3,sK1))
% 55.83/7.45      | r1_tarski(k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))),k7_relat_1(sK3,sK1))
% 55.83/7.45      | k7_relat_1(sK3,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))) != k7_relat_1(k7_relat_1(sK3,sK1),sK2)
% 55.83/7.45      | k7_relat_1(sK3,sK1) != k7_relat_1(sK3,sK1) ),
% 55.83/7.45      inference(instantiation,[status(thm)],[c_25551]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_109504,plain,
% 55.83/7.45      ( ~ r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK3,sK1),sK2)),k9_relat_1(sK3,sK2)) ),
% 55.83/7.45      inference(global_propositional_subsumption,
% 55.83/7.45                [status(thm)],
% 55.83/7.45                [c_109499,c_12,c_11,c_644,c_747,c_1052,c_1160,c_1161,
% 55.83/7.45                 c_1453,c_1606,c_1890,c_2121,c_2122,c_2624,c_2959,c_5693,
% 55.83/7.45                 c_5694,c_6451,c_9574,c_18349,c_19198,c_25552,c_35786,
% 55.83/7.45                 c_69122]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_1405,plain,
% 55.83/7.45      ( ~ r1_tarski(k9_relat_1(X0_41,X1_41),X2_41)
% 55.83/7.45      | r1_tarski(k2_relat_1(k7_relat_1(X0_41,X1_41)),X2_41)
% 55.83/7.45      | ~ v1_relat_1(X0_41) ),
% 55.83/7.45      inference(resolution,[status(thm)],[c_1391,c_159]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_110476,plain,
% 55.83/7.45      ( ~ r1_tarski(k9_relat_1(k7_relat_1(sK3,sK1),sK2),k9_relat_1(sK3,sK2))
% 55.83/7.45      | ~ v1_relat_1(k7_relat_1(sK3,sK1)) ),
% 55.83/7.45      inference(resolution,[status(thm)],[c_109504,c_1405]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_110477,plain,
% 55.83/7.45      ( r1_tarski(k9_relat_1(k7_relat_1(sK3,sK1),sK2),k9_relat_1(sK3,sK2)) != iProver_top
% 55.83/7.45      | v1_relat_1(k7_relat_1(sK3,sK1)) != iProver_top ),
% 55.83/7.45      inference(predicate_to_equality,[status(thm)],[c_110476]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_132419,plain,
% 55.83/7.45      ( r1_tarski(k9_relat_1(k7_relat_1(sK3,sK1),sK2),k9_relat_1(sK3,sK2)) != iProver_top ),
% 55.83/7.45      inference(global_propositional_subsumption,
% 55.83/7.45                [status(thm)],
% 55.83/7.45                [c_132024,c_13,c_18350,c_110477]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_132424,plain,
% 55.83/7.45      ( r1_tarski(k7_relat_1(sK3,sK1),sK3) != iProver_top
% 55.83/7.45      | r1_tarski(sK2,sK2) != iProver_top
% 55.83/7.45      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top
% 55.83/7.45      | v1_relat_1(k7_relat_1(sK3,sK1)) != iProver_top ),
% 55.83/7.45      inference(superposition,[status(thm)],[c_106441,c_132419]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_132425,plain,
% 55.83/7.45      ( ~ r1_tarski(k7_relat_1(sK3,sK1),sK3)
% 55.83/7.45      | ~ r1_tarski(sK2,sK2)
% 55.83/7.45      | ~ v1_relat_1(k7_relat_1(sK3,sK2))
% 55.83/7.45      | ~ v1_relat_1(k7_relat_1(sK3,sK1)) ),
% 55.83/7.45      inference(predicate_to_equality_rev,[status(thm)],[c_132424]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_47873,plain,
% 55.83/7.45      ( r1_tarski(k7_relat_1(sK3,sK1),sK3) | ~ v1_relat_1(sK3) ),
% 55.83/7.45      inference(instantiation,[status(thm)],[c_156]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(c_30201,plain,
% 55.83/7.45      ( v1_relat_1(k7_relat_1(sK3,sK2)) | ~ v1_relat_1(sK3) ),
% 55.83/7.45      inference(instantiation,[status(thm)],[c_162]) ).
% 55.83/7.45  
% 55.83/7.45  cnf(contradiction,plain,
% 55.83/7.45      ( $false ),
% 55.83/7.45      inference(minisat,
% 55.83/7.45                [status(thm)],
% 55.83/7.45                [c_220274,c_220273,c_132425,c_47873,c_30201,c_18349,c_12]) ).
% 55.83/7.45  
% 55.83/7.45  
% 55.83/7.45  % SZS output end CNFRefutation for theBenchmark.p
% 55.83/7.45  
% 55.83/7.45  ------                               Statistics
% 55.83/7.45  
% 55.83/7.45  ------ Selected
% 55.83/7.45  
% 55.83/7.45  total_time:                             6.957
% 55.83/7.45  
%------------------------------------------------------------------------------
