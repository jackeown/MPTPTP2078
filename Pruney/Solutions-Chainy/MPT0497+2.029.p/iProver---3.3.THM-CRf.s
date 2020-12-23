%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:44:51 EST 2020

% Result     : Theorem 0.82s
% Output     : CNFRefutation 0.82s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 131 expanded)
%              Number of clauses        :   52 (  58 expanded)
%              Number of leaves         :   11 (  26 expanded)
%              Depth                    :   15
%              Number of atoms          :  196 ( 366 expanded)
%              Number of equality atoms :  128 ( 201 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f19,f21])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k7_relat_1(X1,X0)
        <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <~> r1_xboole_0(k1_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 != k7_relat_1(X1,X0) )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 = k7_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 != k7_relat_1(X1,X0) )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 = k7_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f17,plain,
    ( ? [X0,X1] :
        ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k7_relat_1(X1,X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 = k7_relat_1(X1,X0) )
        & v1_relat_1(X1) )
   => ( ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
        | k1_xboole_0 != k7_relat_1(sK1,sK0) )
      & ( r1_xboole_0(k1_relat_1(sK1),sK0)
        | k1_xboole_0 = k7_relat_1(sK1,sK0) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
      | k1_xboole_0 != k7_relat_1(sK1,sK0) )
    & ( r1_xboole_0(k1_relat_1(sK1),sK0)
      | k1_xboole_0 = k7_relat_1(sK1,sK0) )
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f17])).

fof(f29,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f28,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_tarski(k1_relat_1(X1),X0)) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f27,f21])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f11,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f22,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k1_setfam_1(k2_tarski(X0,X1)) ) ),
    inference(definition_unfolding,[],[f20,f21])).

fof(f30,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
    | k1_xboole_0 != k7_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f4,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

cnf(c_234,plain,
    ( X0_38 != X1_38
    | X2_38 != X1_38
    | X2_38 = X0_38 ),
    theory(equality)).

cnf(c_754,plain,
    ( k1_relat_1(X0_38) != X1_38
    | k1_xboole_0 != X1_38
    | k1_xboole_0 = k1_relat_1(X0_38) ),
    inference(instantiation,[status(thm)],[c_234])).

cnf(c_755,plain,
    ( k1_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_754])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_76,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_1])).

cnf(c_9,negated_conjecture,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_80,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    inference(prop_impl,[status(thm)],[c_9])).

cnf(c_150,plain,
    ( k7_relat_1(sK1,sK0) = k1_xboole_0
    | k1_relat_1(sK1) != X0
    | k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_76,c_80])).

cnf(c_151,plain,
    ( k7_relat_1(sK1,sK0) = k1_xboole_0
    | k1_setfam_1(k2_tarski(k1_relat_1(sK1),sK0)) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_150])).

cnf(c_181,plain,
    ( k7_relat_1(sK1,sK0) = k1_xboole_0
    | k1_setfam_1(k2_tarski(k1_relat_1(sK1),sK0)) = k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_151])).

cnf(c_222,plain,
    ( k7_relat_1(sK1,sK0) = k1_xboole_0
    | k1_setfam_1(k2_tarski(k1_relat_1(sK1),sK0)) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_181])).

cnf(c_10,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_224,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_410,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_224])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | k1_setfam_1(k2_tarski(k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_225,plain,
    ( ~ v1_relat_1(X0_38)
    | k1_setfam_1(k2_tarski(k1_relat_1(X0_38),X0_39)) = k1_relat_1(k7_relat_1(X0_38,X0_39)) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_409,plain,
    ( k1_setfam_1(k2_tarski(k1_relat_1(X0_38),X0_39)) = k1_relat_1(k7_relat_1(X0_38,X0_39))
    | v1_relat_1(X0_38) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_225])).

cnf(c_662,plain,
    ( k1_setfam_1(k2_tarski(k1_relat_1(sK1),X0_39)) = k1_relat_1(k7_relat_1(sK1,X0_39)) ),
    inference(superposition,[status(thm)],[c_410,c_409])).

cnf(c_676,plain,
    ( k7_relat_1(sK1,sK0) = k1_xboole_0
    | k1_relat_1(k7_relat_1(sK1,sK0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_222,c_662])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_226,plain,
    ( ~ v1_relat_1(X0_38)
    | k1_relat_1(X0_38) != k1_xboole_0
    | k1_xboole_0 = X0_38 ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_408,plain,
    ( k1_relat_1(X0_38) != k1_xboole_0
    | k1_xboole_0 = X0_38
    | v1_relat_1(X0_38) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_226])).

cnf(c_714,plain,
    ( k7_relat_1(sK1,sK0) = k1_xboole_0
    | v1_relat_1(k7_relat_1(sK1,sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_676,c_408])).

cnf(c_240,plain,
    ( X0_38 != X1_38
    | k1_relat_1(X0_38) = k1_relat_1(X1_38) ),
    theory(equality)).

cnf(c_639,plain,
    ( k7_relat_1(sK1,sK0) != X0_38
    | k1_relat_1(k7_relat_1(sK1,sK0)) = k1_relat_1(X0_38) ),
    inference(instantiation,[status(thm)],[c_240])).

cnf(c_641,plain,
    ( k7_relat_1(sK1,sK0) != k1_xboole_0
    | k1_relat_1(k7_relat_1(sK1,sK0)) = k1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_639])).

cnf(c_544,plain,
    ( k1_relat_1(k7_relat_1(sK1,sK0)) != X0_38
    | k1_xboole_0 != X0_38
    | k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_234])).

cnf(c_638,plain,
    ( k1_relat_1(k7_relat_1(sK1,sK0)) != k1_relat_1(X0_38)
    | k1_xboole_0 != k1_relat_1(X0_38)
    | k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_544])).

cnf(c_640,plain,
    ( k1_relat_1(k7_relat_1(sK1,sK0)) != k1_relat_1(k1_xboole_0)
    | k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0))
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_638])).

cnf(c_474,plain,
    ( k1_setfam_1(k2_tarski(k1_relat_1(sK1),sK0)) != X0_38
    | k1_setfam_1(k2_tarski(k1_relat_1(sK1),sK0)) = k1_xboole_0
    | k1_xboole_0 != X0_38 ),
    inference(instantiation,[status(thm)],[c_234])).

cnf(c_513,plain,
    ( k1_setfam_1(k2_tarski(k1_relat_1(sK1),sK0)) != k1_relat_1(k7_relat_1(sK1,sK0))
    | k1_setfam_1(k2_tarski(k1_relat_1(sK1),sK0)) = k1_xboole_0
    | k1_xboole_0 != k1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_474])).

cnf(c_469,plain,
    ( ~ v1_relat_1(sK1)
    | k1_setfam_1(k2_tarski(k1_relat_1(sK1),X0_39)) = k1_relat_1(k7_relat_1(sK1,X0_39)) ),
    inference(instantiation,[status(thm)],[c_225])).

cnf(c_471,plain,
    ( ~ v1_relat_1(sK1)
    | k1_setfam_1(k2_tarski(k1_relat_1(sK1),sK0)) = k1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_469])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_230,plain,
    ( ~ v1_relat_1(X0_38)
    | v1_relat_1(k7_relat_1(X0_38,X0_39)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_456,plain,
    ( v1_relat_1(k7_relat_1(sK1,X0_39))
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_230])).

cnf(c_457,plain,
    ( v1_relat_1(k7_relat_1(sK1,X0_39)) = iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_456])).

cnf(c_459,plain,
    ( v1_relat_1(k7_relat_1(sK1,sK0)) = iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_457])).

cnf(c_0,plain,
    ( r1_xboole_0(X0,X1)
    | k1_setfam_1(k2_tarski(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_74,plain,
    ( r1_xboole_0(X0,X1)
    | k1_setfam_1(k2_tarski(X0,X1)) != k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_0])).

cnf(c_8,negated_conjecture,
    ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
    | k1_xboole_0 != k7_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_78,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
    | k1_xboole_0 != k7_relat_1(sK1,sK0) ),
    inference(prop_impl,[status(thm)],[c_8])).

cnf(c_142,plain,
    ( k7_relat_1(sK1,sK0) != k1_xboole_0
    | k1_relat_1(sK1) != X0
    | k1_setfam_1(k2_tarski(X0,X1)) != k1_xboole_0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_74,c_78])).

cnf(c_143,plain,
    ( k7_relat_1(sK1,sK0) != k1_xboole_0
    | k1_setfam_1(k2_tarski(k1_relat_1(sK1),sK0)) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_142])).

cnf(c_179,plain,
    ( k7_relat_1(sK1,sK0) != k1_xboole_0
    | k1_setfam_1(k2_tarski(k1_relat_1(sK1),sK0)) != k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_143])).

cnf(c_223,plain,
    ( k7_relat_1(sK1,sK0) != k1_xboole_0
    | k1_setfam_1(k2_tarski(k1_relat_1(sK1),sK0)) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_179])).

cnf(c_4,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_228,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_232,plain,
    ( X0_38 = X0_38 ),
    theory(equality)).

cnf(c_248,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_232])).

cnf(c_11,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_755,c_714,c_641,c_640,c_513,c_471,c_459,c_223,c_228,c_248,c_11,c_10])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:24:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 0.82/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.82/0.98  
% 0.82/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.82/0.98  
% 0.82/0.98  ------  iProver source info
% 0.82/0.98  
% 0.82/0.98  git: date: 2020-06-30 10:37:57 +0100
% 0.82/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.82/0.98  git: non_committed_changes: false
% 0.82/0.98  git: last_make_outside_of_git: false
% 0.82/0.98  
% 0.82/0.98  ------ 
% 0.82/0.98  
% 0.82/0.98  ------ Input Options
% 0.82/0.98  
% 0.82/0.98  --out_options                           all
% 0.82/0.98  --tptp_safe_out                         true
% 0.82/0.98  --problem_path                          ""
% 0.82/0.98  --include_path                          ""
% 0.82/0.98  --clausifier                            res/vclausify_rel
% 0.82/0.98  --clausifier_options                    --mode clausify
% 0.82/0.98  --stdin                                 false
% 0.82/0.98  --stats_out                             all
% 0.82/0.98  
% 0.82/0.98  ------ General Options
% 0.82/0.98  
% 0.82/0.98  --fof                                   false
% 0.82/0.98  --time_out_real                         305.
% 0.82/0.98  --time_out_virtual                      -1.
% 0.82/0.98  --symbol_type_check                     false
% 0.82/0.98  --clausify_out                          false
% 0.82/0.98  --sig_cnt_out                           false
% 0.82/0.98  --trig_cnt_out                          false
% 0.82/0.98  --trig_cnt_out_tolerance                1.
% 0.82/0.98  --trig_cnt_out_sk_spl                   false
% 0.82/0.98  --abstr_cl_out                          false
% 0.82/0.98  
% 0.82/0.98  ------ Global Options
% 0.82/0.98  
% 0.82/0.98  --schedule                              default
% 0.82/0.98  --add_important_lit                     false
% 0.82/0.98  --prop_solver_per_cl                    1000
% 0.82/0.98  --min_unsat_core                        false
% 0.82/0.98  --soft_assumptions                      false
% 0.82/0.98  --soft_lemma_size                       3
% 0.82/0.98  --prop_impl_unit_size                   0
% 0.82/0.98  --prop_impl_unit                        []
% 0.82/0.98  --share_sel_clauses                     true
% 0.82/0.98  --reset_solvers                         false
% 0.82/0.98  --bc_imp_inh                            [conj_cone]
% 0.82/0.98  --conj_cone_tolerance                   3.
% 0.82/0.98  --extra_neg_conj                        none
% 0.82/0.98  --large_theory_mode                     true
% 0.82/0.98  --prolific_symb_bound                   200
% 0.82/0.98  --lt_threshold                          2000
% 0.82/0.98  --clause_weak_htbl                      true
% 0.82/0.98  --gc_record_bc_elim                     false
% 0.82/0.98  
% 0.82/0.98  ------ Preprocessing Options
% 0.82/0.98  
% 0.82/0.98  --preprocessing_flag                    true
% 0.82/0.98  --time_out_prep_mult                    0.1
% 0.82/0.98  --splitting_mode                        input
% 0.82/0.98  --splitting_grd                         true
% 0.82/0.98  --splitting_cvd                         false
% 0.82/0.98  --splitting_cvd_svl                     false
% 0.82/0.98  --splitting_nvd                         32
% 0.82/0.98  --sub_typing                            true
% 0.82/0.98  --prep_gs_sim                           true
% 0.82/0.98  --prep_unflatten                        true
% 0.82/0.98  --prep_res_sim                          true
% 0.82/0.98  --prep_upred                            true
% 0.82/0.98  --prep_sem_filter                       exhaustive
% 0.82/0.98  --prep_sem_filter_out                   false
% 0.82/0.98  --pred_elim                             true
% 0.82/0.98  --res_sim_input                         true
% 0.82/0.98  --eq_ax_congr_red                       true
% 0.82/0.98  --pure_diseq_elim                       true
% 0.82/0.98  --brand_transform                       false
% 0.82/0.98  --non_eq_to_eq                          false
% 0.82/0.98  --prep_def_merge                        true
% 0.82/0.98  --prep_def_merge_prop_impl              false
% 0.82/0.98  --prep_def_merge_mbd                    true
% 0.82/0.98  --prep_def_merge_tr_red                 false
% 0.82/0.98  --prep_def_merge_tr_cl                  false
% 0.82/0.98  --smt_preprocessing                     true
% 0.82/0.98  --smt_ac_axioms                         fast
% 0.82/0.98  --preprocessed_out                      false
% 0.82/0.98  --preprocessed_stats                    false
% 0.82/0.98  
% 0.82/0.98  ------ Abstraction refinement Options
% 0.82/0.98  
% 0.82/0.98  --abstr_ref                             []
% 0.82/0.98  --abstr_ref_prep                        false
% 0.82/0.98  --abstr_ref_until_sat                   false
% 0.82/0.98  --abstr_ref_sig_restrict                funpre
% 0.82/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 0.82/0.98  --abstr_ref_under                       []
% 0.82/0.98  
% 0.82/0.98  ------ SAT Options
% 0.82/0.98  
% 0.82/0.98  --sat_mode                              false
% 0.82/0.98  --sat_fm_restart_options                ""
% 0.82/0.98  --sat_gr_def                            false
% 0.82/0.98  --sat_epr_types                         true
% 0.82/0.98  --sat_non_cyclic_types                  false
% 0.82/0.98  --sat_finite_models                     false
% 0.82/0.98  --sat_fm_lemmas                         false
% 0.82/0.98  --sat_fm_prep                           false
% 0.82/0.98  --sat_fm_uc_incr                        true
% 0.82/0.98  --sat_out_model                         small
% 0.82/0.98  --sat_out_clauses                       false
% 0.82/0.98  
% 0.82/0.98  ------ QBF Options
% 0.82/0.98  
% 0.82/0.98  --qbf_mode                              false
% 0.82/0.98  --qbf_elim_univ                         false
% 0.82/0.98  --qbf_dom_inst                          none
% 0.82/0.98  --qbf_dom_pre_inst                      false
% 0.82/0.98  --qbf_sk_in                             false
% 0.82/0.98  --qbf_pred_elim                         true
% 0.82/0.98  --qbf_split                             512
% 0.82/0.98  
% 0.82/0.98  ------ BMC1 Options
% 0.82/0.98  
% 0.82/0.98  --bmc1_incremental                      false
% 0.82/0.98  --bmc1_axioms                           reachable_all
% 0.82/0.98  --bmc1_min_bound                        0
% 0.82/0.98  --bmc1_max_bound                        -1
% 0.82/0.98  --bmc1_max_bound_default                -1
% 0.82/0.98  --bmc1_symbol_reachability              true
% 0.82/0.98  --bmc1_property_lemmas                  false
% 0.82/0.98  --bmc1_k_induction                      false
% 0.82/0.98  --bmc1_non_equiv_states                 false
% 0.82/0.98  --bmc1_deadlock                         false
% 0.82/0.98  --bmc1_ucm                              false
% 0.82/0.98  --bmc1_add_unsat_core                   none
% 0.82/0.98  --bmc1_unsat_core_children              false
% 0.82/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 0.82/0.98  --bmc1_out_stat                         full
% 0.82/0.98  --bmc1_ground_init                      false
% 0.82/0.98  --bmc1_pre_inst_next_state              false
% 0.82/0.98  --bmc1_pre_inst_state                   false
% 0.82/0.98  --bmc1_pre_inst_reach_state             false
% 0.82/0.98  --bmc1_out_unsat_core                   false
% 0.82/0.98  --bmc1_aig_witness_out                  false
% 0.82/0.98  --bmc1_verbose                          false
% 0.82/0.98  --bmc1_dump_clauses_tptp                false
% 0.82/0.98  --bmc1_dump_unsat_core_tptp             false
% 0.82/0.98  --bmc1_dump_file                        -
% 0.82/0.98  --bmc1_ucm_expand_uc_limit              128
% 0.82/0.98  --bmc1_ucm_n_expand_iterations          6
% 0.82/0.98  --bmc1_ucm_extend_mode                  1
% 0.82/0.98  --bmc1_ucm_init_mode                    2
% 0.82/0.98  --bmc1_ucm_cone_mode                    none
% 0.82/0.98  --bmc1_ucm_reduced_relation_type        0
% 0.82/0.98  --bmc1_ucm_relax_model                  4
% 0.82/0.98  --bmc1_ucm_full_tr_after_sat            true
% 0.82/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 0.82/0.98  --bmc1_ucm_layered_model                none
% 0.82/0.98  --bmc1_ucm_max_lemma_size               10
% 0.82/0.98  
% 0.82/0.98  ------ AIG Options
% 0.82/0.98  
% 0.82/0.98  --aig_mode                              false
% 0.82/0.98  
% 0.82/0.98  ------ Instantiation Options
% 0.82/0.98  
% 0.82/0.98  --instantiation_flag                    true
% 0.82/0.98  --inst_sos_flag                         false
% 0.82/0.98  --inst_sos_phase                        true
% 0.82/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.82/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.82/0.98  --inst_lit_sel_side                     num_symb
% 0.82/0.98  --inst_solver_per_active                1400
% 0.82/0.98  --inst_solver_calls_frac                1.
% 0.82/0.98  --inst_passive_queue_type               priority_queues
% 0.82/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.82/0.98  --inst_passive_queues_freq              [25;2]
% 0.82/0.98  --inst_dismatching                      true
% 0.82/0.98  --inst_eager_unprocessed_to_passive     true
% 0.82/0.98  --inst_prop_sim_given                   true
% 0.82/0.98  --inst_prop_sim_new                     false
% 0.82/0.98  --inst_subs_new                         false
% 0.82/0.98  --inst_eq_res_simp                      false
% 0.82/0.98  --inst_subs_given                       false
% 0.82/0.98  --inst_orphan_elimination               true
% 0.82/0.98  --inst_learning_loop_flag               true
% 0.82/0.98  --inst_learning_start                   3000
% 0.82/0.98  --inst_learning_factor                  2
% 0.82/0.98  --inst_start_prop_sim_after_learn       3
% 0.82/0.98  --inst_sel_renew                        solver
% 0.82/0.98  --inst_lit_activity_flag                true
% 0.82/0.98  --inst_restr_to_given                   false
% 0.82/0.98  --inst_activity_threshold               500
% 0.82/0.98  --inst_out_proof                        true
% 0.82/0.98  
% 0.82/0.98  ------ Resolution Options
% 0.82/0.98  
% 0.82/0.98  --resolution_flag                       true
% 0.82/0.98  --res_lit_sel                           adaptive
% 0.82/0.98  --res_lit_sel_side                      none
% 0.82/0.98  --res_ordering                          kbo
% 0.82/0.98  --res_to_prop_solver                    active
% 0.82/0.98  --res_prop_simpl_new                    false
% 0.82/0.98  --res_prop_simpl_given                  true
% 0.82/0.98  --res_passive_queue_type                priority_queues
% 0.82/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.82/0.98  --res_passive_queues_freq               [15;5]
% 0.82/0.98  --res_forward_subs                      full
% 0.82/0.98  --res_backward_subs                     full
% 0.82/0.98  --res_forward_subs_resolution           true
% 0.82/0.98  --res_backward_subs_resolution          true
% 0.82/0.98  --res_orphan_elimination                true
% 0.82/0.98  --res_time_limit                        2.
% 0.82/0.98  --res_out_proof                         true
% 0.82/0.98  
% 0.82/0.98  ------ Superposition Options
% 0.82/0.98  
% 0.82/0.98  --superposition_flag                    true
% 0.82/0.98  --sup_passive_queue_type                priority_queues
% 0.82/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.82/0.98  --sup_passive_queues_freq               [8;1;4]
% 0.82/0.98  --demod_completeness_check              fast
% 0.82/0.98  --demod_use_ground                      true
% 0.82/0.98  --sup_to_prop_solver                    passive
% 0.82/0.98  --sup_prop_simpl_new                    true
% 0.82/0.98  --sup_prop_simpl_given                  true
% 0.82/0.98  --sup_fun_splitting                     false
% 0.82/0.98  --sup_smt_interval                      50000
% 0.82/0.98  
% 0.82/0.98  ------ Superposition Simplification Setup
% 0.82/0.98  
% 0.82/0.98  --sup_indices_passive                   []
% 0.82/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.82/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.82/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.82/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 0.82/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.82/0.98  --sup_full_bw                           [BwDemod]
% 0.82/0.98  --sup_immed_triv                        [TrivRules]
% 0.82/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.82/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.82/0.98  --sup_immed_bw_main                     []
% 0.82/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.82/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 0.82/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.82/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.82/0.98  
% 0.82/0.98  ------ Combination Options
% 0.82/0.98  
% 0.82/0.98  --comb_res_mult                         3
% 0.82/0.98  --comb_sup_mult                         2
% 0.82/0.98  --comb_inst_mult                        10
% 0.82/0.98  
% 0.82/0.98  ------ Debug Options
% 0.82/0.98  
% 0.82/0.98  --dbg_backtrace                         false
% 0.82/0.98  --dbg_dump_prop_clauses                 false
% 0.82/0.98  --dbg_dump_prop_clauses_file            -
% 0.82/0.98  --dbg_out_stat                          false
% 0.82/0.98  ------ Parsing...
% 0.82/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.82/0.98  
% 0.82/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 0.82/0.98  
% 0.82/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.82/0.98  
% 0.82/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.82/0.98  ------ Proving...
% 0.82/0.98  ------ Problem Properties 
% 0.82/0.98  
% 0.82/0.98  
% 0.82/0.98  clauses                                 9
% 0.82/0.98  conjectures                             1
% 0.82/0.98  EPR                                     1
% 0.82/0.99  Horn                                    8
% 0.82/0.99  unary                                   3
% 0.82/0.99  binary                                  4
% 0.82/0.99  lits                                    17
% 0.82/0.99  lits eq                                 11
% 0.82/0.99  fd_pure                                 0
% 0.82/0.99  fd_pseudo                               0
% 0.82/0.99  fd_cond                                 2
% 0.82/0.99  fd_pseudo_cond                          0
% 0.82/0.99  AC symbols                              0
% 0.82/0.99  
% 0.82/0.99  ------ Schedule dynamic 5 is on 
% 0.82/0.99  
% 0.82/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.82/0.99  
% 0.82/0.99  
% 0.82/0.99  ------ 
% 0.82/0.99  Current options:
% 0.82/0.99  ------ 
% 0.82/0.99  
% 0.82/0.99  ------ Input Options
% 0.82/0.99  
% 0.82/0.99  --out_options                           all
% 0.82/0.99  --tptp_safe_out                         true
% 0.82/0.99  --problem_path                          ""
% 0.82/0.99  --include_path                          ""
% 0.82/0.99  --clausifier                            res/vclausify_rel
% 0.82/0.99  --clausifier_options                    --mode clausify
% 0.82/0.99  --stdin                                 false
% 0.82/0.99  --stats_out                             all
% 0.82/0.99  
% 0.82/0.99  ------ General Options
% 0.82/0.99  
% 0.82/0.99  --fof                                   false
% 0.82/0.99  --time_out_real                         305.
% 0.82/0.99  --time_out_virtual                      -1.
% 0.82/0.99  --symbol_type_check                     false
% 0.82/0.99  --clausify_out                          false
% 0.82/0.99  --sig_cnt_out                           false
% 0.82/0.99  --trig_cnt_out                          false
% 0.82/0.99  --trig_cnt_out_tolerance                1.
% 0.82/0.99  --trig_cnt_out_sk_spl                   false
% 0.82/0.99  --abstr_cl_out                          false
% 0.82/0.99  
% 0.82/0.99  ------ Global Options
% 0.82/0.99  
% 0.82/0.99  --schedule                              default
% 0.82/0.99  --add_important_lit                     false
% 0.82/0.99  --prop_solver_per_cl                    1000
% 0.82/0.99  --min_unsat_core                        false
% 0.82/0.99  --soft_assumptions                      false
% 0.82/0.99  --soft_lemma_size                       3
% 0.82/0.99  --prop_impl_unit_size                   0
% 0.82/0.99  --prop_impl_unit                        []
% 0.82/0.99  --share_sel_clauses                     true
% 0.82/0.99  --reset_solvers                         false
% 0.82/0.99  --bc_imp_inh                            [conj_cone]
% 0.82/0.99  --conj_cone_tolerance                   3.
% 0.82/0.99  --extra_neg_conj                        none
% 0.82/0.99  --large_theory_mode                     true
% 0.82/0.99  --prolific_symb_bound                   200
% 0.82/0.99  --lt_threshold                          2000
% 0.82/0.99  --clause_weak_htbl                      true
% 0.82/0.99  --gc_record_bc_elim                     false
% 0.82/0.99  
% 0.82/0.99  ------ Preprocessing Options
% 0.82/0.99  
% 0.82/0.99  --preprocessing_flag                    true
% 0.82/0.99  --time_out_prep_mult                    0.1
% 0.82/0.99  --splitting_mode                        input
% 0.82/0.99  --splitting_grd                         true
% 0.82/0.99  --splitting_cvd                         false
% 0.82/0.99  --splitting_cvd_svl                     false
% 0.82/0.99  --splitting_nvd                         32
% 0.82/0.99  --sub_typing                            true
% 0.82/0.99  --prep_gs_sim                           true
% 0.82/0.99  --prep_unflatten                        true
% 0.82/0.99  --prep_res_sim                          true
% 0.82/0.99  --prep_upred                            true
% 0.82/0.99  --prep_sem_filter                       exhaustive
% 0.82/0.99  --prep_sem_filter_out                   false
% 0.82/0.99  --pred_elim                             true
% 0.82/0.99  --res_sim_input                         true
% 0.82/0.99  --eq_ax_congr_red                       true
% 0.82/0.99  --pure_diseq_elim                       true
% 0.82/0.99  --brand_transform                       false
% 0.82/0.99  --non_eq_to_eq                          false
% 0.82/0.99  --prep_def_merge                        true
% 0.82/0.99  --prep_def_merge_prop_impl              false
% 0.82/0.99  --prep_def_merge_mbd                    true
% 0.82/0.99  --prep_def_merge_tr_red                 false
% 0.82/0.99  --prep_def_merge_tr_cl                  false
% 0.82/0.99  --smt_preprocessing                     true
% 0.82/0.99  --smt_ac_axioms                         fast
% 0.82/0.99  --preprocessed_out                      false
% 0.82/0.99  --preprocessed_stats                    false
% 0.82/0.99  
% 0.82/0.99  ------ Abstraction refinement Options
% 0.82/0.99  
% 0.82/0.99  --abstr_ref                             []
% 0.82/0.99  --abstr_ref_prep                        false
% 0.82/0.99  --abstr_ref_until_sat                   false
% 0.82/0.99  --abstr_ref_sig_restrict                funpre
% 0.82/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 0.82/0.99  --abstr_ref_under                       []
% 0.82/0.99  
% 0.82/0.99  ------ SAT Options
% 0.82/0.99  
% 0.82/0.99  --sat_mode                              false
% 0.82/0.99  --sat_fm_restart_options                ""
% 0.82/0.99  --sat_gr_def                            false
% 0.82/0.99  --sat_epr_types                         true
% 0.82/0.99  --sat_non_cyclic_types                  false
% 0.82/0.99  --sat_finite_models                     false
% 0.82/0.99  --sat_fm_lemmas                         false
% 0.82/0.99  --sat_fm_prep                           false
% 0.82/0.99  --sat_fm_uc_incr                        true
% 0.82/0.99  --sat_out_model                         small
% 0.82/0.99  --sat_out_clauses                       false
% 0.82/0.99  
% 0.82/0.99  ------ QBF Options
% 0.82/0.99  
% 0.82/0.99  --qbf_mode                              false
% 0.82/0.99  --qbf_elim_univ                         false
% 0.82/0.99  --qbf_dom_inst                          none
% 0.82/0.99  --qbf_dom_pre_inst                      false
% 0.82/0.99  --qbf_sk_in                             false
% 0.82/0.99  --qbf_pred_elim                         true
% 0.82/0.99  --qbf_split                             512
% 0.82/0.99  
% 0.82/0.99  ------ BMC1 Options
% 0.82/0.99  
% 0.82/0.99  --bmc1_incremental                      false
% 0.82/0.99  --bmc1_axioms                           reachable_all
% 0.82/0.99  --bmc1_min_bound                        0
% 0.82/0.99  --bmc1_max_bound                        -1
% 0.82/0.99  --bmc1_max_bound_default                -1
% 0.82/0.99  --bmc1_symbol_reachability              true
% 0.82/0.99  --bmc1_property_lemmas                  false
% 0.82/0.99  --bmc1_k_induction                      false
% 0.82/0.99  --bmc1_non_equiv_states                 false
% 0.82/0.99  --bmc1_deadlock                         false
% 0.82/0.99  --bmc1_ucm                              false
% 0.82/0.99  --bmc1_add_unsat_core                   none
% 0.82/0.99  --bmc1_unsat_core_children              false
% 0.82/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 0.82/0.99  --bmc1_out_stat                         full
% 0.82/0.99  --bmc1_ground_init                      false
% 0.82/0.99  --bmc1_pre_inst_next_state              false
% 0.82/0.99  --bmc1_pre_inst_state                   false
% 0.82/0.99  --bmc1_pre_inst_reach_state             false
% 0.82/0.99  --bmc1_out_unsat_core                   false
% 0.82/0.99  --bmc1_aig_witness_out                  false
% 0.82/0.99  --bmc1_verbose                          false
% 0.82/0.99  --bmc1_dump_clauses_tptp                false
% 0.82/0.99  --bmc1_dump_unsat_core_tptp             false
% 0.82/0.99  --bmc1_dump_file                        -
% 0.82/0.99  --bmc1_ucm_expand_uc_limit              128
% 0.82/0.99  --bmc1_ucm_n_expand_iterations          6
% 0.82/0.99  --bmc1_ucm_extend_mode                  1
% 0.82/0.99  --bmc1_ucm_init_mode                    2
% 0.82/0.99  --bmc1_ucm_cone_mode                    none
% 0.82/0.99  --bmc1_ucm_reduced_relation_type        0
% 0.82/0.99  --bmc1_ucm_relax_model                  4
% 0.82/0.99  --bmc1_ucm_full_tr_after_sat            true
% 0.82/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 0.82/0.99  --bmc1_ucm_layered_model                none
% 0.82/0.99  --bmc1_ucm_max_lemma_size               10
% 0.82/0.99  
% 0.82/0.99  ------ AIG Options
% 0.82/0.99  
% 0.82/0.99  --aig_mode                              false
% 0.82/0.99  
% 0.82/0.99  ------ Instantiation Options
% 0.82/0.99  
% 0.82/0.99  --instantiation_flag                    true
% 0.82/0.99  --inst_sos_flag                         false
% 0.82/0.99  --inst_sos_phase                        true
% 0.82/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.82/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.82/0.99  --inst_lit_sel_side                     none
% 0.82/0.99  --inst_solver_per_active                1400
% 0.82/0.99  --inst_solver_calls_frac                1.
% 0.82/0.99  --inst_passive_queue_type               priority_queues
% 0.82/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.82/0.99  --inst_passive_queues_freq              [25;2]
% 0.82/0.99  --inst_dismatching                      true
% 0.82/0.99  --inst_eager_unprocessed_to_passive     true
% 0.82/0.99  --inst_prop_sim_given                   true
% 0.82/0.99  --inst_prop_sim_new                     false
% 0.82/0.99  --inst_subs_new                         false
% 0.82/0.99  --inst_eq_res_simp                      false
% 0.82/0.99  --inst_subs_given                       false
% 0.82/0.99  --inst_orphan_elimination               true
% 0.82/0.99  --inst_learning_loop_flag               true
% 0.82/0.99  --inst_learning_start                   3000
% 0.82/0.99  --inst_learning_factor                  2
% 0.82/0.99  --inst_start_prop_sim_after_learn       3
% 0.82/0.99  --inst_sel_renew                        solver
% 0.82/0.99  --inst_lit_activity_flag                true
% 0.82/0.99  --inst_restr_to_given                   false
% 0.82/0.99  --inst_activity_threshold               500
% 0.82/0.99  --inst_out_proof                        true
% 0.82/0.99  
% 0.82/0.99  ------ Resolution Options
% 0.82/0.99  
% 0.82/0.99  --resolution_flag                       false
% 0.82/0.99  --res_lit_sel                           adaptive
% 0.82/0.99  --res_lit_sel_side                      none
% 0.82/0.99  --res_ordering                          kbo
% 0.82/0.99  --res_to_prop_solver                    active
% 0.82/0.99  --res_prop_simpl_new                    false
% 0.82/0.99  --res_prop_simpl_given                  true
% 0.82/0.99  --res_passive_queue_type                priority_queues
% 0.82/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.82/0.99  --res_passive_queues_freq               [15;5]
% 0.82/0.99  --res_forward_subs                      full
% 0.82/0.99  --res_backward_subs                     full
% 0.82/0.99  --res_forward_subs_resolution           true
% 0.82/0.99  --res_backward_subs_resolution          true
% 0.82/0.99  --res_orphan_elimination                true
% 0.82/0.99  --res_time_limit                        2.
% 0.82/0.99  --res_out_proof                         true
% 0.82/0.99  
% 0.82/0.99  ------ Superposition Options
% 0.82/0.99  
% 0.82/0.99  --superposition_flag                    true
% 0.82/0.99  --sup_passive_queue_type                priority_queues
% 0.82/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.82/0.99  --sup_passive_queues_freq               [8;1;4]
% 0.82/0.99  --demod_completeness_check              fast
% 0.82/0.99  --demod_use_ground                      true
% 0.82/0.99  --sup_to_prop_solver                    passive
% 0.82/0.99  --sup_prop_simpl_new                    true
% 0.82/0.99  --sup_prop_simpl_given                  true
% 0.82/0.99  --sup_fun_splitting                     false
% 0.82/0.99  --sup_smt_interval                      50000
% 0.82/0.99  
% 0.82/0.99  ------ Superposition Simplification Setup
% 0.82/0.99  
% 0.82/0.99  --sup_indices_passive                   []
% 0.82/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.82/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.82/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.82/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 0.82/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.82/0.99  --sup_full_bw                           [BwDemod]
% 0.82/0.99  --sup_immed_triv                        [TrivRules]
% 0.82/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.82/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.82/0.99  --sup_immed_bw_main                     []
% 0.82/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.82/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 0.82/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.82/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.82/0.99  
% 0.82/0.99  ------ Combination Options
% 0.82/0.99  
% 0.82/0.99  --comb_res_mult                         3
% 0.82/0.99  --comb_sup_mult                         2
% 0.82/0.99  --comb_inst_mult                        10
% 0.82/0.99  
% 0.82/0.99  ------ Debug Options
% 0.82/0.99  
% 0.82/0.99  --dbg_backtrace                         false
% 0.82/0.99  --dbg_dump_prop_clauses                 false
% 0.82/0.99  --dbg_dump_prop_clauses_file            -
% 0.82/0.99  --dbg_out_stat                          false
% 0.82/0.99  
% 0.82/0.99  
% 0.82/0.99  
% 0.82/0.99  
% 0.82/0.99  ------ Proving...
% 0.82/0.99  
% 0.82/0.99  
% 0.82/0.99  % SZS status Theorem for theBenchmark.p
% 0.82/0.99  
% 0.82/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 0.82/0.99  
% 0.82/0.99  fof(f1,axiom,(
% 0.82/0.99    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.82/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.82/0.99  
% 0.82/0.99  fof(f14,plain,(
% 0.82/0.99    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.82/0.99    inference(nnf_transformation,[],[f1])).
% 0.82/0.99  
% 0.82/0.99  fof(f19,plain,(
% 0.82/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.82/0.99    inference(cnf_transformation,[],[f14])).
% 0.82/0.99  
% 0.82/0.99  fof(f2,axiom,(
% 0.82/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.82/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.82/0.99  
% 0.82/0.99  fof(f21,plain,(
% 0.82/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.82/0.99    inference(cnf_transformation,[],[f2])).
% 0.82/0.99  
% 0.82/0.99  fof(f32,plain,(
% 0.82/0.99    ( ! [X0,X1] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.82/0.99    inference(definition_unfolding,[],[f19,f21])).
% 0.82/0.99  
% 0.82/0.99  fof(f7,conjecture,(
% 0.82/0.99    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.82/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.82/0.99  
% 0.82/0.99  fof(f8,negated_conjecture,(
% 0.82/0.99    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.82/0.99    inference(negated_conjecture,[],[f7])).
% 0.82/0.99  
% 0.82/0.99  fof(f13,plain,(
% 0.82/0.99    ? [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <~> r1_xboole_0(k1_relat_1(X1),X0)) & v1_relat_1(X1))),
% 0.82/0.99    inference(ennf_transformation,[],[f8])).
% 0.82/0.99  
% 0.82/0.99  fof(f15,plain,(
% 0.82/0.99    ? [X0,X1] : (((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0))) & v1_relat_1(X1))),
% 0.82/0.99    inference(nnf_transformation,[],[f13])).
% 0.82/0.99  
% 0.82/0.99  fof(f16,plain,(
% 0.82/0.99    ? [X0,X1] : ((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0)) & v1_relat_1(X1))),
% 0.82/0.99    inference(flattening,[],[f15])).
% 0.82/0.99  
% 0.82/0.99  fof(f17,plain,(
% 0.82/0.99    ? [X0,X1] : ((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0)) & v1_relat_1(X1)) => ((~r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 != k7_relat_1(sK1,sK0)) & (r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k7_relat_1(sK1,sK0)) & v1_relat_1(sK1))),
% 0.82/0.99    introduced(choice_axiom,[])).
% 0.82/0.99  
% 0.82/0.99  fof(f18,plain,(
% 0.82/0.99    (~r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 != k7_relat_1(sK1,sK0)) & (r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k7_relat_1(sK1,sK0)) & v1_relat_1(sK1)),
% 0.82/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f17])).
% 0.82/0.99  
% 0.82/0.99  fof(f29,plain,(
% 0.82/0.99    r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k7_relat_1(sK1,sK0)),
% 0.82/0.99    inference(cnf_transformation,[],[f18])).
% 0.82/0.99  
% 0.82/0.99  fof(f28,plain,(
% 0.82/0.99    v1_relat_1(sK1)),
% 0.82/0.99    inference(cnf_transformation,[],[f18])).
% 0.82/0.99  
% 0.82/0.99  fof(f6,axiom,(
% 0.82/0.99    ! [X0,X1] : (v1_relat_1(X1) => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)))),
% 0.82/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.82/0.99  
% 0.82/0.99  fof(f12,plain,(
% 0.82/0.99    ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 0.82/0.99    inference(ennf_transformation,[],[f6])).
% 0.82/0.99  
% 0.82/0.99  fof(f27,plain,(
% 0.82/0.99    ( ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 0.82/0.99    inference(cnf_transformation,[],[f12])).
% 0.82/0.99  
% 0.82/0.99  fof(f33,plain,(
% 0.82/0.99    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(k1_relat_1(X1),X0)) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 0.82/0.99    inference(definition_unfolding,[],[f27,f21])).
% 0.82/0.99  
% 0.82/0.99  fof(f5,axiom,(
% 0.82/0.99    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.82/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.82/0.99  
% 0.82/0.99  fof(f10,plain,(
% 0.82/0.99    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.82/0.99    inference(ennf_transformation,[],[f5])).
% 0.82/0.99  
% 0.82/0.99  fof(f11,plain,(
% 0.82/0.99    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.82/0.99    inference(flattening,[],[f10])).
% 0.82/0.99  
% 0.82/0.99  fof(f25,plain,(
% 0.82/0.99    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.82/0.99    inference(cnf_transformation,[],[f11])).
% 0.82/0.99  
% 0.82/0.99  fof(f3,axiom,(
% 0.82/0.99    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.82/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.82/0.99  
% 0.82/0.99  fof(f9,plain,(
% 0.82/0.99    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.82/0.99    inference(ennf_transformation,[],[f3])).
% 0.82/0.99  
% 0.82/0.99  fof(f22,plain,(
% 0.82/0.99    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.82/0.99    inference(cnf_transformation,[],[f9])).
% 0.82/0.99  
% 0.82/0.99  fof(f20,plain,(
% 0.82/0.99    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.82/0.99    inference(cnf_transformation,[],[f14])).
% 0.82/0.99  
% 0.82/0.99  fof(f31,plain,(
% 0.82/0.99    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.82/0.99    inference(definition_unfolding,[],[f20,f21])).
% 0.82/0.99  
% 0.82/0.99  fof(f30,plain,(
% 0.82/0.99    ~r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 != k7_relat_1(sK1,sK0)),
% 0.82/0.99    inference(cnf_transformation,[],[f18])).
% 0.82/0.99  
% 0.82/0.99  fof(f4,axiom,(
% 0.82/0.99    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.82/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.82/0.99  
% 0.82/0.99  fof(f23,plain,(
% 0.82/0.99    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.82/0.99    inference(cnf_transformation,[],[f4])).
% 0.82/0.99  
% 0.82/0.99  cnf(c_234,plain,
% 0.82/0.99      ( X0_38 != X1_38 | X2_38 != X1_38 | X2_38 = X0_38 ),
% 0.82/0.99      theory(equality) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_754,plain,
% 0.82/0.99      ( k1_relat_1(X0_38) != X1_38
% 0.82/0.99      | k1_xboole_0 != X1_38
% 0.82/0.99      | k1_xboole_0 = k1_relat_1(X0_38) ),
% 0.82/0.99      inference(instantiation,[status(thm)],[c_234]) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_755,plain,
% 0.82/0.99      ( k1_relat_1(k1_xboole_0) != k1_xboole_0
% 0.82/0.99      | k1_xboole_0 = k1_relat_1(k1_xboole_0)
% 0.82/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 0.82/0.99      inference(instantiation,[status(thm)],[c_754]) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_1,plain,
% 0.82/0.99      ( ~ r1_xboole_0(X0,X1)
% 0.82/0.99      | k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0 ),
% 0.82/0.99      inference(cnf_transformation,[],[f32]) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_76,plain,
% 0.82/0.99      ( ~ r1_xboole_0(X0,X1)
% 0.82/0.99      | k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0 ),
% 0.82/0.99      inference(prop_impl,[status(thm)],[c_1]) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_9,negated_conjecture,
% 0.82/0.99      ( r1_xboole_0(k1_relat_1(sK1),sK0)
% 0.82/0.99      | k1_xboole_0 = k7_relat_1(sK1,sK0) ),
% 0.82/0.99      inference(cnf_transformation,[],[f29]) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_80,plain,
% 0.82/0.99      ( r1_xboole_0(k1_relat_1(sK1),sK0)
% 0.82/0.99      | k1_xboole_0 = k7_relat_1(sK1,sK0) ),
% 0.82/0.99      inference(prop_impl,[status(thm)],[c_9]) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_150,plain,
% 0.82/0.99      ( k7_relat_1(sK1,sK0) = k1_xboole_0
% 0.82/0.99      | k1_relat_1(sK1) != X0
% 0.82/0.99      | k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0
% 0.82/0.99      | sK0 != X1 ),
% 0.82/0.99      inference(resolution_lifted,[status(thm)],[c_76,c_80]) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_151,plain,
% 0.82/0.99      ( k7_relat_1(sK1,sK0) = k1_xboole_0
% 0.82/0.99      | k1_setfam_1(k2_tarski(k1_relat_1(sK1),sK0)) = k1_xboole_0 ),
% 0.82/0.99      inference(unflattening,[status(thm)],[c_150]) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_181,plain,
% 0.82/0.99      ( k7_relat_1(sK1,sK0) = k1_xboole_0
% 0.82/0.99      | k1_setfam_1(k2_tarski(k1_relat_1(sK1),sK0)) = k1_xboole_0 ),
% 0.82/0.99      inference(prop_impl,[status(thm)],[c_151]) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_222,plain,
% 0.82/0.99      ( k7_relat_1(sK1,sK0) = k1_xboole_0
% 0.82/0.99      | k1_setfam_1(k2_tarski(k1_relat_1(sK1),sK0)) = k1_xboole_0 ),
% 0.82/0.99      inference(subtyping,[status(esa)],[c_181]) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_10,negated_conjecture,
% 0.82/0.99      ( v1_relat_1(sK1) ),
% 0.82/0.99      inference(cnf_transformation,[],[f28]) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_224,negated_conjecture,
% 0.82/0.99      ( v1_relat_1(sK1) ),
% 0.82/0.99      inference(subtyping,[status(esa)],[c_10]) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_410,plain,
% 0.82/0.99      ( v1_relat_1(sK1) = iProver_top ),
% 0.82/0.99      inference(predicate_to_equality,[status(thm)],[c_224]) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_7,plain,
% 0.82/0.99      ( ~ v1_relat_1(X0)
% 0.82/0.99      | k1_setfam_1(k2_tarski(k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1)) ),
% 0.82/0.99      inference(cnf_transformation,[],[f33]) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_225,plain,
% 0.82/0.99      ( ~ v1_relat_1(X0_38)
% 0.82/0.99      | k1_setfam_1(k2_tarski(k1_relat_1(X0_38),X0_39)) = k1_relat_1(k7_relat_1(X0_38,X0_39)) ),
% 0.82/0.99      inference(subtyping,[status(esa)],[c_7]) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_409,plain,
% 0.82/0.99      ( k1_setfam_1(k2_tarski(k1_relat_1(X0_38),X0_39)) = k1_relat_1(k7_relat_1(X0_38,X0_39))
% 0.82/0.99      | v1_relat_1(X0_38) != iProver_top ),
% 0.82/0.99      inference(predicate_to_equality,[status(thm)],[c_225]) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_662,plain,
% 0.82/0.99      ( k1_setfam_1(k2_tarski(k1_relat_1(sK1),X0_39)) = k1_relat_1(k7_relat_1(sK1,X0_39)) ),
% 0.82/0.99      inference(superposition,[status(thm)],[c_410,c_409]) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_676,plain,
% 0.82/0.99      ( k7_relat_1(sK1,sK0) = k1_xboole_0
% 0.82/0.99      | k1_relat_1(k7_relat_1(sK1,sK0)) = k1_xboole_0 ),
% 0.82/0.99      inference(superposition,[status(thm)],[c_222,c_662]) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_6,plain,
% 0.82/0.99      ( ~ v1_relat_1(X0)
% 0.82/0.99      | k1_relat_1(X0) != k1_xboole_0
% 0.82/0.99      | k1_xboole_0 = X0 ),
% 0.82/0.99      inference(cnf_transformation,[],[f25]) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_226,plain,
% 0.82/0.99      ( ~ v1_relat_1(X0_38)
% 0.82/0.99      | k1_relat_1(X0_38) != k1_xboole_0
% 0.82/0.99      | k1_xboole_0 = X0_38 ),
% 0.82/0.99      inference(subtyping,[status(esa)],[c_6]) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_408,plain,
% 0.82/0.99      ( k1_relat_1(X0_38) != k1_xboole_0
% 0.82/0.99      | k1_xboole_0 = X0_38
% 0.82/0.99      | v1_relat_1(X0_38) != iProver_top ),
% 0.82/0.99      inference(predicate_to_equality,[status(thm)],[c_226]) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_714,plain,
% 0.82/0.99      ( k7_relat_1(sK1,sK0) = k1_xboole_0
% 0.82/0.99      | v1_relat_1(k7_relat_1(sK1,sK0)) != iProver_top ),
% 0.82/0.99      inference(superposition,[status(thm)],[c_676,c_408]) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_240,plain,
% 0.82/0.99      ( X0_38 != X1_38 | k1_relat_1(X0_38) = k1_relat_1(X1_38) ),
% 0.82/0.99      theory(equality) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_639,plain,
% 0.82/0.99      ( k7_relat_1(sK1,sK0) != X0_38
% 0.82/0.99      | k1_relat_1(k7_relat_1(sK1,sK0)) = k1_relat_1(X0_38) ),
% 0.82/0.99      inference(instantiation,[status(thm)],[c_240]) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_641,plain,
% 0.82/0.99      ( k7_relat_1(sK1,sK0) != k1_xboole_0
% 0.82/0.99      | k1_relat_1(k7_relat_1(sK1,sK0)) = k1_relat_1(k1_xboole_0) ),
% 0.82/0.99      inference(instantiation,[status(thm)],[c_639]) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_544,plain,
% 0.82/0.99      ( k1_relat_1(k7_relat_1(sK1,sK0)) != X0_38
% 0.82/0.99      | k1_xboole_0 != X0_38
% 0.82/0.99      | k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0)) ),
% 0.82/0.99      inference(instantiation,[status(thm)],[c_234]) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_638,plain,
% 0.82/0.99      ( k1_relat_1(k7_relat_1(sK1,sK0)) != k1_relat_1(X0_38)
% 0.82/0.99      | k1_xboole_0 != k1_relat_1(X0_38)
% 0.82/0.99      | k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0)) ),
% 0.82/0.99      inference(instantiation,[status(thm)],[c_544]) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_640,plain,
% 0.82/0.99      ( k1_relat_1(k7_relat_1(sK1,sK0)) != k1_relat_1(k1_xboole_0)
% 0.82/0.99      | k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0))
% 0.82/0.99      | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
% 0.82/0.99      inference(instantiation,[status(thm)],[c_638]) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_474,plain,
% 0.82/0.99      ( k1_setfam_1(k2_tarski(k1_relat_1(sK1),sK0)) != X0_38
% 0.82/0.99      | k1_setfam_1(k2_tarski(k1_relat_1(sK1),sK0)) = k1_xboole_0
% 0.82/0.99      | k1_xboole_0 != X0_38 ),
% 0.82/0.99      inference(instantiation,[status(thm)],[c_234]) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_513,plain,
% 0.82/0.99      ( k1_setfam_1(k2_tarski(k1_relat_1(sK1),sK0)) != k1_relat_1(k7_relat_1(sK1,sK0))
% 0.82/0.99      | k1_setfam_1(k2_tarski(k1_relat_1(sK1),sK0)) = k1_xboole_0
% 0.82/0.99      | k1_xboole_0 != k1_relat_1(k7_relat_1(sK1,sK0)) ),
% 0.82/0.99      inference(instantiation,[status(thm)],[c_474]) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_469,plain,
% 0.82/0.99      ( ~ v1_relat_1(sK1)
% 0.82/0.99      | k1_setfam_1(k2_tarski(k1_relat_1(sK1),X0_39)) = k1_relat_1(k7_relat_1(sK1,X0_39)) ),
% 0.82/0.99      inference(instantiation,[status(thm)],[c_225]) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_471,plain,
% 0.82/0.99      ( ~ v1_relat_1(sK1)
% 0.82/0.99      | k1_setfam_1(k2_tarski(k1_relat_1(sK1),sK0)) = k1_relat_1(k7_relat_1(sK1,sK0)) ),
% 0.82/0.99      inference(instantiation,[status(thm)],[c_469]) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_2,plain,
% 0.82/0.99      ( ~ v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1)) ),
% 0.82/0.99      inference(cnf_transformation,[],[f22]) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_230,plain,
% 0.82/0.99      ( ~ v1_relat_1(X0_38) | v1_relat_1(k7_relat_1(X0_38,X0_39)) ),
% 0.82/0.99      inference(subtyping,[status(esa)],[c_2]) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_456,plain,
% 0.82/0.99      ( v1_relat_1(k7_relat_1(sK1,X0_39)) | ~ v1_relat_1(sK1) ),
% 0.82/0.99      inference(instantiation,[status(thm)],[c_230]) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_457,plain,
% 0.82/0.99      ( v1_relat_1(k7_relat_1(sK1,X0_39)) = iProver_top
% 0.82/0.99      | v1_relat_1(sK1) != iProver_top ),
% 0.82/0.99      inference(predicate_to_equality,[status(thm)],[c_456]) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_459,plain,
% 0.82/0.99      ( v1_relat_1(k7_relat_1(sK1,sK0)) = iProver_top
% 0.82/0.99      | v1_relat_1(sK1) != iProver_top ),
% 0.82/0.99      inference(instantiation,[status(thm)],[c_457]) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_0,plain,
% 0.82/0.99      ( r1_xboole_0(X0,X1)
% 0.82/0.99      | k1_setfam_1(k2_tarski(X0,X1)) != k1_xboole_0 ),
% 0.82/0.99      inference(cnf_transformation,[],[f31]) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_74,plain,
% 0.82/0.99      ( r1_xboole_0(X0,X1)
% 0.82/0.99      | k1_setfam_1(k2_tarski(X0,X1)) != k1_xboole_0 ),
% 0.82/0.99      inference(prop_impl,[status(thm)],[c_0]) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_8,negated_conjecture,
% 0.82/0.99      ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
% 0.82/0.99      | k1_xboole_0 != k7_relat_1(sK1,sK0) ),
% 0.82/0.99      inference(cnf_transformation,[],[f30]) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_78,plain,
% 0.82/0.99      ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
% 0.82/0.99      | k1_xboole_0 != k7_relat_1(sK1,sK0) ),
% 0.82/0.99      inference(prop_impl,[status(thm)],[c_8]) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_142,plain,
% 0.82/0.99      ( k7_relat_1(sK1,sK0) != k1_xboole_0
% 0.82/0.99      | k1_relat_1(sK1) != X0
% 0.82/0.99      | k1_setfam_1(k2_tarski(X0,X1)) != k1_xboole_0
% 0.82/0.99      | sK0 != X1 ),
% 0.82/0.99      inference(resolution_lifted,[status(thm)],[c_74,c_78]) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_143,plain,
% 0.82/0.99      ( k7_relat_1(sK1,sK0) != k1_xboole_0
% 0.82/0.99      | k1_setfam_1(k2_tarski(k1_relat_1(sK1),sK0)) != k1_xboole_0 ),
% 0.82/0.99      inference(unflattening,[status(thm)],[c_142]) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_179,plain,
% 0.82/0.99      ( k7_relat_1(sK1,sK0) != k1_xboole_0
% 0.82/0.99      | k1_setfam_1(k2_tarski(k1_relat_1(sK1),sK0)) != k1_xboole_0 ),
% 0.82/0.99      inference(prop_impl,[status(thm)],[c_143]) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_223,plain,
% 0.82/0.99      ( k7_relat_1(sK1,sK0) != k1_xboole_0
% 0.82/0.99      | k1_setfam_1(k2_tarski(k1_relat_1(sK1),sK0)) != k1_xboole_0 ),
% 0.82/0.99      inference(subtyping,[status(esa)],[c_179]) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_4,plain,
% 0.82/0.99      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 0.82/0.99      inference(cnf_transformation,[],[f23]) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_228,plain,
% 0.82/0.99      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 0.82/0.99      inference(subtyping,[status(esa)],[c_4]) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_232,plain,( X0_38 = X0_38 ),theory(equality) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_248,plain,
% 0.82/0.99      ( k1_xboole_0 = k1_xboole_0 ),
% 0.82/0.99      inference(instantiation,[status(thm)],[c_232]) ).
% 0.82/0.99  
% 0.82/0.99  cnf(c_11,plain,
% 0.82/0.99      ( v1_relat_1(sK1) = iProver_top ),
% 0.82/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 0.82/0.99  
% 0.82/0.99  cnf(contradiction,plain,
% 0.82/0.99      ( $false ),
% 0.82/0.99      inference(minisat,
% 0.82/0.99                [status(thm)],
% 0.82/0.99                [c_755,c_714,c_641,c_640,c_513,c_471,c_459,c_223,c_228,
% 0.82/0.99                 c_248,c_11,c_10]) ).
% 0.82/0.99  
% 0.82/0.99  
% 0.82/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 0.82/0.99  
% 0.82/0.99  ------                               Statistics
% 0.82/0.99  
% 0.82/0.99  ------ General
% 0.82/0.99  
% 0.82/0.99  abstr_ref_over_cycles:                  0
% 0.82/0.99  abstr_ref_under_cycles:                 0
% 0.82/0.99  gc_basic_clause_elim:                   0
% 0.82/0.99  forced_gc_time:                         0
% 0.82/0.99  parsing_time:                           0.007
% 0.82/0.99  unif_index_cands_time:                  0.
% 0.82/0.99  unif_index_add_time:                    0.
% 0.82/0.99  orderings_time:                         0.
% 0.82/0.99  out_proof_time:                         0.009
% 0.82/0.99  total_time:                             0.053
% 0.82/0.99  num_of_symbols:                         41
% 0.82/0.99  num_of_terms:                           645
% 0.82/0.99  
% 0.82/0.99  ------ Preprocessing
% 0.82/0.99  
% 0.82/0.99  num_of_splits:                          0
% 0.82/0.99  num_of_split_atoms:                     0
% 0.82/0.99  num_of_reused_defs:                     0
% 0.82/0.99  num_eq_ax_congr_red:                    3
% 0.82/0.99  num_of_sem_filtered_clauses:            1
% 0.82/0.99  num_of_subtypes:                        3
% 0.82/0.99  monotx_restored_types:                  0
% 0.82/0.99  sat_num_of_epr_types:                   0
% 0.82/0.99  sat_num_of_non_cyclic_types:            0
% 0.82/0.99  sat_guarded_non_collapsed_types:        1
% 0.82/0.99  num_pure_diseq_elim:                    0
% 0.82/0.99  simp_replaced_by:                       0
% 0.82/0.99  res_preprocessed:                       57
% 0.82/0.99  prep_upred:                             0
% 0.82/0.99  prep_unflattend:                        4
% 0.82/0.99  smt_new_axioms:                         0
% 0.82/0.99  pred_elim_cands:                        1
% 0.82/0.99  pred_elim:                              1
% 0.82/0.99  pred_elim_cl:                           2
% 0.82/0.99  pred_elim_cycles:                       3
% 0.82/0.99  merged_defs:                            10
% 0.82/0.99  merged_defs_ncl:                        0
% 0.82/0.99  bin_hyper_res:                          10
% 0.82/0.99  prep_cycles:                            4
% 0.82/0.99  pred_elim_time:                         0.
% 0.82/0.99  splitting_time:                         0.
% 0.82/0.99  sem_filter_time:                        0.
% 0.82/0.99  monotx_time:                            0.
% 0.82/0.99  subtype_inf_time:                       0.
% 0.82/0.99  
% 0.82/0.99  ------ Problem properties
% 0.82/0.99  
% 0.82/0.99  clauses:                                9
% 0.82/0.99  conjectures:                            1
% 0.82/0.99  epr:                                    1
% 0.82/0.99  horn:                                   8
% 0.82/0.99  ground:                                 5
% 0.82/0.99  unary:                                  3
% 0.82/0.99  binary:                                 4
% 0.82/0.99  lits:                                   17
% 0.82/0.99  lits_eq:                                11
% 0.82/0.99  fd_pure:                                0
% 0.82/0.99  fd_pseudo:                              0
% 0.82/0.99  fd_cond:                                2
% 0.82/0.99  fd_pseudo_cond:                         0
% 0.82/0.99  ac_symbols:                             0
% 0.82/0.99  
% 0.82/0.99  ------ Propositional Solver
% 0.82/0.99  
% 0.82/0.99  prop_solver_calls:                      27
% 0.82/0.99  prop_fast_solver_calls:                 245
% 0.82/0.99  smt_solver_calls:                       0
% 0.82/0.99  smt_fast_solver_calls:                  0
% 0.82/0.99  prop_num_of_clauses:                    257
% 0.82/0.99  prop_preprocess_simplified:             1322
% 0.82/0.99  prop_fo_subsumed:                       1
% 0.82/0.99  prop_solver_time:                       0.
% 0.82/0.99  smt_solver_time:                        0.
% 0.82/0.99  smt_fast_solver_time:                   0.
% 0.82/0.99  prop_fast_solver_time:                  0.
% 0.82/0.99  prop_unsat_core_time:                   0.
% 0.82/0.99  
% 0.82/0.99  ------ QBF
% 0.82/0.99  
% 0.82/0.99  qbf_q_res:                              0
% 0.82/0.99  qbf_num_tautologies:                    0
% 0.82/0.99  qbf_prep_cycles:                        0
% 0.82/0.99  
% 0.82/0.99  ------ BMC1
% 0.82/0.99  
% 0.82/0.99  bmc1_current_bound:                     -1
% 0.82/0.99  bmc1_last_solved_bound:                 -1
% 0.82/0.99  bmc1_unsat_core_size:                   -1
% 0.82/0.99  bmc1_unsat_core_parents_size:           -1
% 0.82/0.99  bmc1_merge_next_fun:                    0
% 0.82/0.99  bmc1_unsat_core_clauses_time:           0.
% 0.82/0.99  
% 0.82/0.99  ------ Instantiation
% 0.82/0.99  
% 0.82/0.99  inst_num_of_clauses:                    97
% 0.82/0.99  inst_num_in_passive:                    20
% 0.82/0.99  inst_num_in_active:                     57
% 0.82/0.99  inst_num_in_unprocessed:                19
% 0.82/0.99  inst_num_of_loops:                      66
% 0.82/0.99  inst_num_of_learning_restarts:          0
% 0.82/0.99  inst_num_moves_active_passive:          5
% 0.82/0.99  inst_lit_activity:                      0
% 0.82/0.99  inst_lit_activity_moves:                0
% 0.82/0.99  inst_num_tautologies:                   0
% 0.82/0.99  inst_num_prop_implied:                  0
% 0.82/0.99  inst_num_existing_simplified:           0
% 0.82/0.99  inst_num_eq_res_simplified:             0
% 0.82/0.99  inst_num_child_elim:                    0
% 0.82/0.99  inst_num_of_dismatching_blockings:      2
% 0.82/0.99  inst_num_of_non_proper_insts:           48
% 0.82/0.99  inst_num_of_duplicates:                 0
% 0.82/0.99  inst_inst_num_from_inst_to_res:         0
% 0.82/0.99  inst_dismatching_checking_time:         0.
% 0.82/0.99  
% 0.82/0.99  ------ Resolution
% 0.82/0.99  
% 0.82/0.99  res_num_of_clauses:                     0
% 0.82/0.99  res_num_in_passive:                     0
% 0.82/0.99  res_num_in_active:                      0
% 0.82/0.99  res_num_of_loops:                       61
% 0.82/0.99  res_forward_subset_subsumed:            5
% 0.82/0.99  res_backward_subset_subsumed:           0
% 0.82/0.99  res_forward_subsumed:                   0
% 0.82/0.99  res_backward_subsumed:                  0
% 0.82/0.99  res_forward_subsumption_resolution:     0
% 0.82/0.99  res_backward_subsumption_resolution:    0
% 0.82/0.99  res_clause_to_clause_subsumption:       13
% 0.82/0.99  res_orphan_elimination:                 0
% 0.82/0.99  res_tautology_del:                      27
% 0.82/0.99  res_num_eq_res_simplified:              0
% 0.82/0.99  res_num_sel_changes:                    0
% 0.82/0.99  res_moves_from_active_to_pass:          0
% 0.82/0.99  
% 0.82/0.99  ------ Superposition
% 0.82/0.99  
% 0.82/0.99  sup_time_total:                         0.
% 0.82/0.99  sup_time_generating:                    0.
% 0.82/0.99  sup_time_sim_full:                      0.
% 0.82/0.99  sup_time_sim_immed:                     0.
% 0.82/0.99  
% 0.82/0.99  sup_num_of_clauses:                     13
% 0.82/0.99  sup_num_in_active:                      9
% 0.82/0.99  sup_num_in_passive:                     4
% 0.82/0.99  sup_num_of_loops:                       12
% 0.82/0.99  sup_fw_superposition:                   6
% 0.82/0.99  sup_bw_superposition:                   3
% 0.82/0.99  sup_immediate_simplified:               0
% 0.82/0.99  sup_given_eliminated:                   0
% 0.82/0.99  comparisons_done:                       0
% 0.82/0.99  comparisons_avoided:                    0
% 0.82/0.99  
% 0.82/0.99  ------ Simplifications
% 0.82/0.99  
% 0.82/0.99  
% 0.82/0.99  sim_fw_subset_subsumed:                 0
% 0.82/0.99  sim_bw_subset_subsumed:                 3
% 0.82/0.99  sim_fw_subsumed:                        0
% 0.82/0.99  sim_bw_subsumed:                        0
% 0.82/0.99  sim_fw_subsumption_res:                 0
% 0.82/0.99  sim_bw_subsumption_res:                 0
% 0.82/0.99  sim_tautology_del:                      1
% 0.82/0.99  sim_eq_tautology_del:                   1
% 0.82/0.99  sim_eq_res_simp:                        0
% 0.82/0.99  sim_fw_demodulated:                     0
% 0.82/0.99  sim_bw_demodulated:                     1
% 0.82/0.99  sim_light_normalised:                   0
% 0.82/0.99  sim_joinable_taut:                      0
% 0.82/0.99  sim_joinable_simp:                      0
% 0.82/0.99  sim_ac_normalised:                      0
% 0.82/0.99  sim_smt_subsumption:                    0
% 0.82/0.99  
%------------------------------------------------------------------------------
