%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:48:06 EST 2020

% Result     : Theorem 2.87s
% Output     : CNFRefutation 2.87s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 120 expanded)
%              Number of clauses        :   56 (  62 expanded)
%              Number of leaves         :   13 (  27 expanded)
%              Depth                    :   12
%              Number of atoms          :  174 ( 236 expanded)
%              Number of equality atoms :  123 ( 163 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f16,plain,(
    ? [X0,X1] :
      ( k7_relat_1(X1,X0) != k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f17,plain,
    ( ? [X0,X1] :
        ( k7_relat_1(X1,X0) != k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
        & v1_relat_1(X1) )
   => ( k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f17])).

fof(f27,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X0)) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f25,f22])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f30,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f20,f22])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f24,f22])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f19,f22,f22])).

fof(f28,plain,(
    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f34,plain,(
    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),sK0))) ),
    inference(definition_unfolding,[],[f28,f22])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f23,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

cnf(c_110,plain,
    ( X0_35 != X1_35
    | X2_35 != X1_35
    | X2_35 = X0_35 ),
    theory(equality)).

cnf(c_326,plain,
    ( X0_35 != X1_35
    | k7_relat_1(sK1,sK0) != X1_35
    | k7_relat_1(sK1,sK0) = X0_35 ),
    inference(instantiation,[status(thm)],[c_110])).

cnf(c_369,plain,
    ( X0_35 != k7_relat_1(sK1,sK0)
    | k7_relat_1(sK1,sK0) = X0_35
    | k7_relat_1(sK1,sK0) != k7_relat_1(sK1,sK0) ),
    inference(instantiation,[status(thm)],[c_326])).

cnf(c_498,plain,
    ( k7_relat_1(X0_35,X0_36) != k7_relat_1(sK1,sK0)
    | k7_relat_1(sK1,sK0) = k7_relat_1(X0_35,X0_36)
    | k7_relat_1(sK1,sK0) != k7_relat_1(sK1,sK0) ),
    inference(instantiation,[status(thm)],[c_369])).

cnf(c_872,plain,
    ( k7_relat_1(k7_relat_1(X0_35,X0_36),X1_36) != k7_relat_1(sK1,sK0)
    | k7_relat_1(sK1,sK0) = k7_relat_1(k7_relat_1(X0_35,X0_36),X1_36)
    | k7_relat_1(sK1,sK0) != k7_relat_1(sK1,sK0) ),
    inference(instantiation,[status(thm)],[c_498])).

cnf(c_4919,plain,
    ( k7_relat_1(k7_relat_1(X0_35,sK0),k1_relat_1(sK1)) != k7_relat_1(sK1,sK0)
    | k7_relat_1(sK1,sK0) = k7_relat_1(k7_relat_1(X0_35,sK0),k1_relat_1(sK1))
    | k7_relat_1(sK1,sK0) != k7_relat_1(sK1,sK0) ),
    inference(instantiation,[status(thm)],[c_872])).

cnf(c_4920,plain,
    ( k7_relat_1(k7_relat_1(sK1,sK0),k1_relat_1(sK1)) != k7_relat_1(sK1,sK0)
    | k7_relat_1(sK1,sK0) = k7_relat_1(k7_relat_1(sK1,sK0),k1_relat_1(sK1))
    | k7_relat_1(sK1,sK0) != k7_relat_1(sK1,sK0) ),
    inference(instantiation,[status(thm)],[c_4919])).

cnf(c_8,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_98,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_258,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_98])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | k4_xboole_0(k1_relat_1(X0),k4_xboole_0(k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_101,plain,
    ( ~ v1_relat_1(X0_35)
    | k4_xboole_0(k1_relat_1(X0_35),k4_xboole_0(k1_relat_1(X0_35),X0_36)) = k1_relat_1(k7_relat_1(X0_35,X0_36)) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_256,plain,
    ( k4_xboole_0(k1_relat_1(X0_35),k4_xboole_0(k1_relat_1(X0_35),X0_36)) = k1_relat_1(k7_relat_1(X0_35,X0_36))
    | v1_relat_1(X0_35) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_101])).

cnf(c_635,plain,
    ( k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),X0_36)) = k1_relat_1(k7_relat_1(sK1,X0_36)) ),
    inference(superposition,[status(thm)],[c_258,c_256])).

cnf(c_1,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_105,plain,
    ( r1_tarski(k4_xboole_0(X0_36,k4_xboole_0(X0_36,X1_36)),X0_36) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_253,plain,
    ( r1_tarski(k4_xboole_0(X0_36,k4_xboole_0(X0_36,X1_36)),X0_36) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_105])).

cnf(c_739,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK1,X0_36)),k1_relat_1(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_635,c_253])).

cnf(c_6,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_100,plain,
    ( ~ r1_tarski(k1_relat_1(X0_35),X0_36)
    | ~ v1_relat_1(X0_35)
    | k7_relat_1(X0_35,X0_36) = X0_35 ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_257,plain,
    ( k7_relat_1(X0_35,X0_36) = X0_35
    | r1_tarski(k1_relat_1(X0_35),X0_36) != iProver_top
    | v1_relat_1(X0_35) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_100])).

cnf(c_1250,plain,
    ( k7_relat_1(k7_relat_1(sK1,X0_36),k1_relat_1(sK1)) = k7_relat_1(sK1,X0_36)
    | v1_relat_1(k7_relat_1(sK1,X0_36)) != iProver_top ),
    inference(superposition,[status(thm)],[c_739,c_257])).

cnf(c_1275,plain,
    ( k7_relat_1(k7_relat_1(sK1,sK0),k1_relat_1(sK1)) = k7_relat_1(sK1,sK0)
    | v1_relat_1(k7_relat_1(sK1,sK0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1250])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k7_relat_1(k7_relat_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_102,plain,
    ( ~ v1_relat_1(X0_35)
    | k7_relat_1(X0_35,k4_xboole_0(X0_36,k4_xboole_0(X0_36,X1_36))) = k7_relat_1(k7_relat_1(X0_35,X0_36),X1_36) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1220,plain,
    ( ~ v1_relat_1(X0_35)
    | k7_relat_1(X0_35,k4_xboole_0(sK0,k4_xboole_0(sK0,k1_relat_1(sK1)))) = k7_relat_1(k7_relat_1(X0_35,sK0),k1_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_102])).

cnf(c_1223,plain,
    ( ~ v1_relat_1(sK1)
    | k7_relat_1(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,k1_relat_1(sK1)))) = k7_relat_1(k7_relat_1(sK1,sK0),k1_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_1220])).

cnf(c_374,plain,
    ( X0_35 != k7_relat_1(X1_35,X0_36)
    | k7_relat_1(sK1,sK0) = X0_35
    | k7_relat_1(sK1,sK0) != k7_relat_1(X1_35,X0_36) ),
    inference(instantiation,[status(thm)],[c_326])).

cnf(c_536,plain,
    ( k7_relat_1(X0_35,X0_36) != k7_relat_1(X1_35,X1_36)
    | k7_relat_1(sK1,sK0) != k7_relat_1(X1_35,X1_36)
    | k7_relat_1(sK1,sK0) = k7_relat_1(X0_35,X0_36) ),
    inference(instantiation,[status(thm)],[c_374])).

cnf(c_1103,plain,
    ( k7_relat_1(X0_35,k4_xboole_0(sK0,k4_xboole_0(sK0,k1_relat_1(sK1)))) != k7_relat_1(X1_35,X0_36)
    | k7_relat_1(sK1,sK0) != k7_relat_1(X1_35,X0_36)
    | k7_relat_1(sK1,sK0) = k7_relat_1(X0_35,k4_xboole_0(sK0,k4_xboole_0(sK0,k1_relat_1(sK1)))) ),
    inference(instantiation,[status(thm)],[c_536])).

cnf(c_1219,plain,
    ( k7_relat_1(X0_35,k4_xboole_0(sK0,k4_xboole_0(sK0,k1_relat_1(sK1)))) != k7_relat_1(k7_relat_1(X0_35,sK0),k1_relat_1(sK1))
    | k7_relat_1(sK1,sK0) = k7_relat_1(X0_35,k4_xboole_0(sK0,k4_xboole_0(sK0,k1_relat_1(sK1))))
    | k7_relat_1(sK1,sK0) != k7_relat_1(k7_relat_1(X0_35,sK0),k1_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_1103])).

cnf(c_1221,plain,
    ( k7_relat_1(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,k1_relat_1(sK1)))) != k7_relat_1(k7_relat_1(sK1,sK0),k1_relat_1(sK1))
    | k7_relat_1(sK1,sK0) != k7_relat_1(k7_relat_1(sK1,sK0),k1_relat_1(sK1))
    | k7_relat_1(sK1,sK0) = k7_relat_1(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,k1_relat_1(sK1)))) ),
    inference(instantiation,[status(thm)],[c_1219])).

cnf(c_304,plain,
    ( k7_relat_1(sK1,k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),sK0))) != X0_35
    | k7_relat_1(sK1,sK0) != X0_35
    | k7_relat_1(sK1,sK0) = k7_relat_1(sK1,k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),sK0))) ),
    inference(instantiation,[status(thm)],[c_110])).

cnf(c_327,plain,
    ( k7_relat_1(sK1,k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),sK0))) != k7_relat_1(X0_35,X0_36)
    | k7_relat_1(sK1,sK0) != k7_relat_1(X0_35,X0_36)
    | k7_relat_1(sK1,sK0) = k7_relat_1(sK1,k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),sK0))) ),
    inference(instantiation,[status(thm)],[c_304])).

cnf(c_694,plain,
    ( k7_relat_1(sK1,k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),sK0))) != k7_relat_1(X0_35,k4_xboole_0(sK0,k4_xboole_0(sK0,k1_relat_1(sK1))))
    | k7_relat_1(sK1,sK0) != k7_relat_1(X0_35,k4_xboole_0(sK0,k4_xboole_0(sK0,k1_relat_1(sK1))))
    | k7_relat_1(sK1,sK0) = k7_relat_1(sK1,k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),sK0))) ),
    inference(instantiation,[status(thm)],[c_327])).

cnf(c_695,plain,
    ( k7_relat_1(sK1,k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),sK0))) != k7_relat_1(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,k1_relat_1(sK1))))
    | k7_relat_1(sK1,sK0) = k7_relat_1(sK1,k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),sK0)))
    | k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,k1_relat_1(sK1)))) ),
    inference(instantiation,[status(thm)],[c_694])).

cnf(c_114,plain,
    ( X0_36 != X1_36
    | X0_35 != X1_35
    | k7_relat_1(X0_35,X0_36) = k7_relat_1(X1_35,X1_36) ),
    theory(equality)).

cnf(c_381,plain,
    ( k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),sK0)) != X0_36
    | k7_relat_1(sK1,k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),sK0))) = k7_relat_1(X0_35,X0_36)
    | sK1 != X0_35 ),
    inference(instantiation,[status(thm)],[c_114])).

cnf(c_513,plain,
    ( k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),sK0)) != k4_xboole_0(sK0,k4_xboole_0(sK0,k1_relat_1(sK1)))
    | k7_relat_1(sK1,k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),sK0))) = k7_relat_1(X0_35,k4_xboole_0(sK0,k4_xboole_0(sK0,k1_relat_1(sK1))))
    | sK1 != X0_35 ),
    inference(instantiation,[status(thm)],[c_381])).

cnf(c_514,plain,
    ( k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),sK0)) != k4_xboole_0(sK0,k4_xboole_0(sK0,k1_relat_1(sK1)))
    | k7_relat_1(sK1,k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),sK0))) = k7_relat_1(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,k1_relat_1(sK1))))
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_513])).

cnf(c_0,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_106,plain,
    ( k4_xboole_0(X0_36,k4_xboole_0(X0_36,X1_36)) = k4_xboole_0(X1_36,k4_xboole_0(X1_36,X0_36)) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_356,plain,
    ( k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),sK0)) = k4_xboole_0(sK0,k4_xboole_0(sK0,k1_relat_1(sK1))) ),
    inference(instantiation,[status(thm)],[c_106])).

cnf(c_7,negated_conjecture,
    ( k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),sK0))) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_99,negated_conjecture,
    ( k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),sK0))) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_103,plain,
    ( ~ v1_relat_1(X0_35)
    | v1_relat_1(k7_relat_1(X0_35,X0_36)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_130,plain,
    ( v1_relat_1(X0_35) != iProver_top
    | v1_relat_1(k7_relat_1(X0_35,X0_36)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_103])).

cnf(c_132,plain,
    ( v1_relat_1(k7_relat_1(sK1,sK0)) = iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_130])).

cnf(c_109,plain,
    ( X0_36 = X0_36 ),
    theory(equality)).

cnf(c_124,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_109])).

cnf(c_108,plain,
    ( X0_35 = X0_35 ),
    theory(equality)).

cnf(c_123,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_108])).

cnf(c_119,plain,
    ( sK0 != sK0
    | k7_relat_1(sK1,sK0) = k7_relat_1(sK1,sK0)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_114])).

cnf(c_9,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4920,c_1275,c_1223,c_1221,c_695,c_514,c_356,c_99,c_132,c_124,c_123,c_119,c_9,c_8])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n011.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 18:58:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.87/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.87/0.98  
% 2.87/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.87/0.98  
% 2.87/0.98  ------  iProver source info
% 2.87/0.98  
% 2.87/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.87/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.87/0.98  git: non_committed_changes: false
% 2.87/0.98  git: last_make_outside_of_git: false
% 2.87/0.98  
% 2.87/0.98  ------ 
% 2.87/0.98  
% 2.87/0.98  ------ Input Options
% 2.87/0.98  
% 2.87/0.98  --out_options                           all
% 2.87/0.98  --tptp_safe_out                         true
% 2.87/0.98  --problem_path                          ""
% 2.87/0.98  --include_path                          ""
% 2.87/0.98  --clausifier                            res/vclausify_rel
% 2.87/0.98  --clausifier_options                    --mode clausify
% 2.87/0.98  --stdin                                 false
% 2.87/0.98  --stats_out                             all
% 2.87/0.98  
% 2.87/0.98  ------ General Options
% 2.87/0.98  
% 2.87/0.98  --fof                                   false
% 2.87/0.98  --time_out_real                         305.
% 2.87/0.98  --time_out_virtual                      -1.
% 2.87/0.98  --symbol_type_check                     false
% 2.87/0.98  --clausify_out                          false
% 2.87/0.98  --sig_cnt_out                           false
% 2.87/0.98  --trig_cnt_out                          false
% 2.87/0.98  --trig_cnt_out_tolerance                1.
% 2.87/0.98  --trig_cnt_out_sk_spl                   false
% 2.87/0.98  --abstr_cl_out                          false
% 2.87/0.98  
% 2.87/0.98  ------ Global Options
% 2.87/0.98  
% 2.87/0.98  --schedule                              default
% 2.87/0.98  --add_important_lit                     false
% 2.87/0.98  --prop_solver_per_cl                    1000
% 2.87/0.98  --min_unsat_core                        false
% 2.87/0.98  --soft_assumptions                      false
% 2.87/0.98  --soft_lemma_size                       3
% 2.87/0.98  --prop_impl_unit_size                   0
% 2.87/0.98  --prop_impl_unit                        []
% 2.87/0.98  --share_sel_clauses                     true
% 2.87/0.98  --reset_solvers                         false
% 2.87/0.98  --bc_imp_inh                            [conj_cone]
% 2.87/0.98  --conj_cone_tolerance                   3.
% 2.87/0.98  --extra_neg_conj                        none
% 2.87/0.98  --large_theory_mode                     true
% 2.87/0.98  --prolific_symb_bound                   200
% 2.87/0.98  --lt_threshold                          2000
% 2.87/0.98  --clause_weak_htbl                      true
% 2.87/0.98  --gc_record_bc_elim                     false
% 2.87/0.98  
% 2.87/0.98  ------ Preprocessing Options
% 2.87/0.98  
% 2.87/0.98  --preprocessing_flag                    true
% 2.87/0.98  --time_out_prep_mult                    0.1
% 2.87/0.98  --splitting_mode                        input
% 2.87/0.98  --splitting_grd                         true
% 2.87/0.98  --splitting_cvd                         false
% 2.87/0.98  --splitting_cvd_svl                     false
% 2.87/0.98  --splitting_nvd                         32
% 2.87/0.98  --sub_typing                            true
% 2.87/0.98  --prep_gs_sim                           true
% 2.87/0.98  --prep_unflatten                        true
% 2.87/0.98  --prep_res_sim                          true
% 2.87/0.98  --prep_upred                            true
% 2.87/0.98  --prep_sem_filter                       exhaustive
% 2.87/0.98  --prep_sem_filter_out                   false
% 2.87/0.98  --pred_elim                             true
% 2.87/0.98  --res_sim_input                         true
% 2.87/0.98  --eq_ax_congr_red                       true
% 2.87/0.98  --pure_diseq_elim                       true
% 2.87/0.98  --brand_transform                       false
% 2.87/0.98  --non_eq_to_eq                          false
% 2.87/0.98  --prep_def_merge                        true
% 2.87/0.98  --prep_def_merge_prop_impl              false
% 2.87/0.98  --prep_def_merge_mbd                    true
% 2.87/0.98  --prep_def_merge_tr_red                 false
% 2.87/0.98  --prep_def_merge_tr_cl                  false
% 2.87/0.98  --smt_preprocessing                     true
% 2.87/0.98  --smt_ac_axioms                         fast
% 2.87/0.98  --preprocessed_out                      false
% 2.87/0.98  --preprocessed_stats                    false
% 2.87/0.98  
% 2.87/0.98  ------ Abstraction refinement Options
% 2.87/0.98  
% 2.87/0.98  --abstr_ref                             []
% 2.87/0.98  --abstr_ref_prep                        false
% 2.87/0.98  --abstr_ref_until_sat                   false
% 2.87/0.98  --abstr_ref_sig_restrict                funpre
% 2.87/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.87/0.98  --abstr_ref_under                       []
% 2.87/0.98  
% 2.87/0.98  ------ SAT Options
% 2.87/0.98  
% 2.87/0.98  --sat_mode                              false
% 2.87/0.98  --sat_fm_restart_options                ""
% 2.87/0.98  --sat_gr_def                            false
% 2.87/0.98  --sat_epr_types                         true
% 2.87/0.98  --sat_non_cyclic_types                  false
% 2.87/0.98  --sat_finite_models                     false
% 2.87/0.98  --sat_fm_lemmas                         false
% 2.87/0.98  --sat_fm_prep                           false
% 2.87/0.98  --sat_fm_uc_incr                        true
% 2.87/0.98  --sat_out_model                         small
% 2.87/0.98  --sat_out_clauses                       false
% 2.87/0.98  
% 2.87/0.98  ------ QBF Options
% 2.87/0.98  
% 2.87/0.98  --qbf_mode                              false
% 2.87/0.98  --qbf_elim_univ                         false
% 2.87/0.98  --qbf_dom_inst                          none
% 2.87/0.98  --qbf_dom_pre_inst                      false
% 2.87/0.98  --qbf_sk_in                             false
% 2.87/0.98  --qbf_pred_elim                         true
% 2.87/0.98  --qbf_split                             512
% 2.87/0.98  
% 2.87/0.98  ------ BMC1 Options
% 2.87/0.98  
% 2.87/0.98  --bmc1_incremental                      false
% 2.87/0.98  --bmc1_axioms                           reachable_all
% 2.87/0.98  --bmc1_min_bound                        0
% 2.87/0.98  --bmc1_max_bound                        -1
% 2.87/0.98  --bmc1_max_bound_default                -1
% 2.87/0.98  --bmc1_symbol_reachability              true
% 2.87/0.98  --bmc1_property_lemmas                  false
% 2.87/0.98  --bmc1_k_induction                      false
% 2.87/0.98  --bmc1_non_equiv_states                 false
% 2.87/0.98  --bmc1_deadlock                         false
% 2.87/0.98  --bmc1_ucm                              false
% 2.87/0.98  --bmc1_add_unsat_core                   none
% 2.87/0.98  --bmc1_unsat_core_children              false
% 2.87/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.87/0.98  --bmc1_out_stat                         full
% 2.87/0.98  --bmc1_ground_init                      false
% 2.87/0.98  --bmc1_pre_inst_next_state              false
% 2.87/0.98  --bmc1_pre_inst_state                   false
% 2.87/0.98  --bmc1_pre_inst_reach_state             false
% 2.87/0.98  --bmc1_out_unsat_core                   false
% 2.87/0.98  --bmc1_aig_witness_out                  false
% 2.87/0.98  --bmc1_verbose                          false
% 2.87/0.98  --bmc1_dump_clauses_tptp                false
% 2.87/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.87/0.98  --bmc1_dump_file                        -
% 2.87/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.87/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.87/0.98  --bmc1_ucm_extend_mode                  1
% 2.87/0.98  --bmc1_ucm_init_mode                    2
% 2.87/0.98  --bmc1_ucm_cone_mode                    none
% 2.87/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.87/0.98  --bmc1_ucm_relax_model                  4
% 2.87/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.87/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.87/0.98  --bmc1_ucm_layered_model                none
% 2.87/0.98  --bmc1_ucm_max_lemma_size               10
% 2.87/0.98  
% 2.87/0.98  ------ AIG Options
% 2.87/0.98  
% 2.87/0.98  --aig_mode                              false
% 2.87/0.98  
% 2.87/0.98  ------ Instantiation Options
% 2.87/0.98  
% 2.87/0.98  --instantiation_flag                    true
% 2.87/0.98  --inst_sos_flag                         false
% 2.87/0.98  --inst_sos_phase                        true
% 2.87/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.87/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.87/0.98  --inst_lit_sel_side                     num_symb
% 2.87/0.98  --inst_solver_per_active                1400
% 2.87/0.98  --inst_solver_calls_frac                1.
% 2.87/0.98  --inst_passive_queue_type               priority_queues
% 2.87/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.87/0.98  --inst_passive_queues_freq              [25;2]
% 2.87/0.98  --inst_dismatching                      true
% 2.87/0.98  --inst_eager_unprocessed_to_passive     true
% 2.87/0.98  --inst_prop_sim_given                   true
% 2.87/0.98  --inst_prop_sim_new                     false
% 2.87/0.98  --inst_subs_new                         false
% 2.87/0.98  --inst_eq_res_simp                      false
% 2.87/0.98  --inst_subs_given                       false
% 2.87/0.98  --inst_orphan_elimination               true
% 2.87/0.98  --inst_learning_loop_flag               true
% 2.87/0.98  --inst_learning_start                   3000
% 2.87/0.98  --inst_learning_factor                  2
% 2.87/0.98  --inst_start_prop_sim_after_learn       3
% 2.87/0.98  --inst_sel_renew                        solver
% 2.87/0.98  --inst_lit_activity_flag                true
% 2.87/0.98  --inst_restr_to_given                   false
% 2.87/0.98  --inst_activity_threshold               500
% 2.87/0.98  --inst_out_proof                        true
% 2.87/0.98  
% 2.87/0.98  ------ Resolution Options
% 2.87/0.98  
% 2.87/0.98  --resolution_flag                       true
% 2.87/0.98  --res_lit_sel                           adaptive
% 2.87/0.98  --res_lit_sel_side                      none
% 2.87/0.98  --res_ordering                          kbo
% 2.87/0.98  --res_to_prop_solver                    active
% 2.87/0.98  --res_prop_simpl_new                    false
% 2.87/0.98  --res_prop_simpl_given                  true
% 2.87/0.98  --res_passive_queue_type                priority_queues
% 2.87/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.87/0.98  --res_passive_queues_freq               [15;5]
% 2.87/0.98  --res_forward_subs                      full
% 2.87/0.98  --res_backward_subs                     full
% 2.87/0.98  --res_forward_subs_resolution           true
% 2.87/0.98  --res_backward_subs_resolution          true
% 2.87/0.98  --res_orphan_elimination                true
% 2.87/0.98  --res_time_limit                        2.
% 2.87/0.98  --res_out_proof                         true
% 2.87/0.98  
% 2.87/0.98  ------ Superposition Options
% 2.87/0.98  
% 2.87/0.98  --superposition_flag                    true
% 2.87/0.98  --sup_passive_queue_type                priority_queues
% 2.87/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.87/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.87/0.98  --demod_completeness_check              fast
% 2.87/0.98  --demod_use_ground                      true
% 2.87/0.98  --sup_to_prop_solver                    passive
% 2.87/0.98  --sup_prop_simpl_new                    true
% 2.87/0.98  --sup_prop_simpl_given                  true
% 2.87/0.98  --sup_fun_splitting                     false
% 2.87/0.98  --sup_smt_interval                      50000
% 2.87/0.98  
% 2.87/0.98  ------ Superposition Simplification Setup
% 2.87/0.98  
% 2.87/0.98  --sup_indices_passive                   []
% 2.87/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.87/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.87/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.87/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.87/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.87/0.98  --sup_full_bw                           [BwDemod]
% 2.87/0.98  --sup_immed_triv                        [TrivRules]
% 2.87/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.87/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.87/0.98  --sup_immed_bw_main                     []
% 2.87/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.87/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.87/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.87/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.87/0.98  
% 2.87/0.98  ------ Combination Options
% 2.87/0.98  
% 2.87/0.98  --comb_res_mult                         3
% 2.87/0.98  --comb_sup_mult                         2
% 2.87/0.98  --comb_inst_mult                        10
% 2.87/0.98  
% 2.87/0.98  ------ Debug Options
% 2.87/0.98  
% 2.87/0.98  --dbg_backtrace                         false
% 2.87/0.98  --dbg_dump_prop_clauses                 false
% 2.87/0.98  --dbg_dump_prop_clauses_file            -
% 2.87/0.98  --dbg_out_stat                          false
% 2.87/0.98  ------ Parsing...
% 2.87/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.87/0.98  
% 2.87/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.87/0.98  
% 2.87/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.87/0.98  
% 2.87/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.87/0.98  ------ Proving...
% 2.87/0.98  ------ Problem Properties 
% 2.87/0.98  
% 2.87/0.98  
% 2.87/0.98  clauses                                 9
% 2.87/0.98  conjectures                             2
% 2.87/0.98  EPR                                     1
% 2.87/0.98  Horn                                    9
% 2.87/0.98  unary                                   5
% 2.87/0.98  binary                                  3
% 2.87/0.98  lits                                    14
% 2.87/0.98  lits eq                                 6
% 2.87/0.98  fd_pure                                 0
% 2.87/0.98  fd_pseudo                               0
% 2.87/0.98  fd_cond                                 0
% 2.87/0.98  fd_pseudo_cond                          0
% 2.87/0.98  AC symbols                              0
% 2.87/0.98  
% 2.87/0.98  ------ Schedule dynamic 5 is on 
% 2.87/0.98  
% 2.87/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.87/0.98  
% 2.87/0.98  
% 2.87/0.98  ------ 
% 2.87/0.98  Current options:
% 2.87/0.98  ------ 
% 2.87/0.98  
% 2.87/0.98  ------ Input Options
% 2.87/0.98  
% 2.87/0.98  --out_options                           all
% 2.87/0.98  --tptp_safe_out                         true
% 2.87/0.98  --problem_path                          ""
% 2.87/0.98  --include_path                          ""
% 2.87/0.98  --clausifier                            res/vclausify_rel
% 2.87/0.98  --clausifier_options                    --mode clausify
% 2.87/0.98  --stdin                                 false
% 2.87/0.98  --stats_out                             all
% 2.87/0.98  
% 2.87/0.98  ------ General Options
% 2.87/0.98  
% 2.87/0.98  --fof                                   false
% 2.87/0.98  --time_out_real                         305.
% 2.87/0.98  --time_out_virtual                      -1.
% 2.87/0.98  --symbol_type_check                     false
% 2.87/0.98  --clausify_out                          false
% 2.87/0.98  --sig_cnt_out                           false
% 2.87/0.98  --trig_cnt_out                          false
% 2.87/0.98  --trig_cnt_out_tolerance                1.
% 2.87/0.98  --trig_cnt_out_sk_spl                   false
% 2.87/0.98  --abstr_cl_out                          false
% 2.87/0.98  
% 2.87/0.98  ------ Global Options
% 2.87/0.98  
% 2.87/0.98  --schedule                              default
% 2.87/0.98  --add_important_lit                     false
% 2.87/0.98  --prop_solver_per_cl                    1000
% 2.87/0.98  --min_unsat_core                        false
% 2.87/0.98  --soft_assumptions                      false
% 2.87/0.98  --soft_lemma_size                       3
% 2.87/0.98  --prop_impl_unit_size                   0
% 2.87/0.98  --prop_impl_unit                        []
% 2.87/0.98  --share_sel_clauses                     true
% 2.87/0.98  --reset_solvers                         false
% 2.87/0.98  --bc_imp_inh                            [conj_cone]
% 2.87/0.98  --conj_cone_tolerance                   3.
% 2.87/0.98  --extra_neg_conj                        none
% 2.87/0.98  --large_theory_mode                     true
% 2.87/0.98  --prolific_symb_bound                   200
% 2.87/0.98  --lt_threshold                          2000
% 2.87/0.98  --clause_weak_htbl                      true
% 2.87/0.98  --gc_record_bc_elim                     false
% 2.87/0.98  
% 2.87/0.98  ------ Preprocessing Options
% 2.87/0.98  
% 2.87/0.98  --preprocessing_flag                    true
% 2.87/0.98  --time_out_prep_mult                    0.1
% 2.87/0.98  --splitting_mode                        input
% 2.87/0.98  --splitting_grd                         true
% 2.87/0.98  --splitting_cvd                         false
% 2.87/0.98  --splitting_cvd_svl                     false
% 2.87/0.98  --splitting_nvd                         32
% 2.87/0.98  --sub_typing                            true
% 2.87/0.98  --prep_gs_sim                           true
% 2.87/0.98  --prep_unflatten                        true
% 2.87/0.98  --prep_res_sim                          true
% 2.87/0.98  --prep_upred                            true
% 2.87/0.98  --prep_sem_filter                       exhaustive
% 2.87/0.98  --prep_sem_filter_out                   false
% 2.87/0.98  --pred_elim                             true
% 2.87/0.98  --res_sim_input                         true
% 2.87/0.98  --eq_ax_congr_red                       true
% 2.87/0.98  --pure_diseq_elim                       true
% 2.87/0.98  --brand_transform                       false
% 2.87/0.98  --non_eq_to_eq                          false
% 2.87/0.98  --prep_def_merge                        true
% 2.87/0.98  --prep_def_merge_prop_impl              false
% 2.87/0.98  --prep_def_merge_mbd                    true
% 2.87/0.98  --prep_def_merge_tr_red                 false
% 2.87/0.98  --prep_def_merge_tr_cl                  false
% 2.87/0.98  --smt_preprocessing                     true
% 2.87/0.98  --smt_ac_axioms                         fast
% 2.87/0.98  --preprocessed_out                      false
% 2.87/0.98  --preprocessed_stats                    false
% 2.87/0.98  
% 2.87/0.98  ------ Abstraction refinement Options
% 2.87/0.98  
% 2.87/0.98  --abstr_ref                             []
% 2.87/0.98  --abstr_ref_prep                        false
% 2.87/0.98  --abstr_ref_until_sat                   false
% 2.87/0.98  --abstr_ref_sig_restrict                funpre
% 2.87/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.87/0.98  --abstr_ref_under                       []
% 2.87/0.98  
% 2.87/0.98  ------ SAT Options
% 2.87/0.98  
% 2.87/0.98  --sat_mode                              false
% 2.87/0.98  --sat_fm_restart_options                ""
% 2.87/0.98  --sat_gr_def                            false
% 2.87/0.98  --sat_epr_types                         true
% 2.87/0.98  --sat_non_cyclic_types                  false
% 2.87/0.98  --sat_finite_models                     false
% 2.87/0.98  --sat_fm_lemmas                         false
% 2.87/0.98  --sat_fm_prep                           false
% 2.87/0.98  --sat_fm_uc_incr                        true
% 2.87/0.98  --sat_out_model                         small
% 2.87/0.98  --sat_out_clauses                       false
% 2.87/0.98  
% 2.87/0.98  ------ QBF Options
% 2.87/0.98  
% 2.87/0.98  --qbf_mode                              false
% 2.87/0.98  --qbf_elim_univ                         false
% 2.87/0.98  --qbf_dom_inst                          none
% 2.87/0.98  --qbf_dom_pre_inst                      false
% 2.87/0.98  --qbf_sk_in                             false
% 2.87/0.98  --qbf_pred_elim                         true
% 2.87/0.98  --qbf_split                             512
% 2.87/0.98  
% 2.87/0.98  ------ BMC1 Options
% 2.87/0.98  
% 2.87/0.98  --bmc1_incremental                      false
% 2.87/0.98  --bmc1_axioms                           reachable_all
% 2.87/0.98  --bmc1_min_bound                        0
% 2.87/0.98  --bmc1_max_bound                        -1
% 2.87/0.98  --bmc1_max_bound_default                -1
% 2.87/0.98  --bmc1_symbol_reachability              true
% 2.87/0.98  --bmc1_property_lemmas                  false
% 2.87/0.98  --bmc1_k_induction                      false
% 2.87/0.98  --bmc1_non_equiv_states                 false
% 2.87/0.98  --bmc1_deadlock                         false
% 2.87/0.98  --bmc1_ucm                              false
% 2.87/0.98  --bmc1_add_unsat_core                   none
% 2.87/0.98  --bmc1_unsat_core_children              false
% 2.87/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.87/0.98  --bmc1_out_stat                         full
% 2.87/0.98  --bmc1_ground_init                      false
% 2.87/0.98  --bmc1_pre_inst_next_state              false
% 2.87/0.98  --bmc1_pre_inst_state                   false
% 2.87/0.98  --bmc1_pre_inst_reach_state             false
% 2.87/0.98  --bmc1_out_unsat_core                   false
% 2.87/0.98  --bmc1_aig_witness_out                  false
% 2.87/0.98  --bmc1_verbose                          false
% 2.87/0.98  --bmc1_dump_clauses_tptp                false
% 2.87/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.87/0.98  --bmc1_dump_file                        -
% 2.87/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.87/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.87/0.98  --bmc1_ucm_extend_mode                  1
% 2.87/0.98  --bmc1_ucm_init_mode                    2
% 2.87/0.98  --bmc1_ucm_cone_mode                    none
% 2.87/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.87/0.98  --bmc1_ucm_relax_model                  4
% 2.87/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.87/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.87/0.98  --bmc1_ucm_layered_model                none
% 2.87/0.98  --bmc1_ucm_max_lemma_size               10
% 2.87/0.98  
% 2.87/0.98  ------ AIG Options
% 2.87/0.98  
% 2.87/0.98  --aig_mode                              false
% 2.87/0.98  
% 2.87/0.98  ------ Instantiation Options
% 2.87/0.98  
% 2.87/0.98  --instantiation_flag                    true
% 2.87/0.98  --inst_sos_flag                         false
% 2.87/0.98  --inst_sos_phase                        true
% 2.87/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.87/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.87/0.98  --inst_lit_sel_side                     none
% 2.87/0.98  --inst_solver_per_active                1400
% 2.87/0.98  --inst_solver_calls_frac                1.
% 2.87/0.98  --inst_passive_queue_type               priority_queues
% 2.87/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.87/0.98  --inst_passive_queues_freq              [25;2]
% 2.87/0.98  --inst_dismatching                      true
% 2.87/0.98  --inst_eager_unprocessed_to_passive     true
% 2.87/0.98  --inst_prop_sim_given                   true
% 2.87/0.98  --inst_prop_sim_new                     false
% 2.87/0.98  --inst_subs_new                         false
% 2.87/0.98  --inst_eq_res_simp                      false
% 2.87/0.98  --inst_subs_given                       false
% 2.87/0.98  --inst_orphan_elimination               true
% 2.87/0.98  --inst_learning_loop_flag               true
% 2.87/0.98  --inst_learning_start                   3000
% 2.87/0.98  --inst_learning_factor                  2
% 2.87/0.98  --inst_start_prop_sim_after_learn       3
% 2.87/0.98  --inst_sel_renew                        solver
% 2.87/0.98  --inst_lit_activity_flag                true
% 2.87/0.98  --inst_restr_to_given                   false
% 2.87/0.98  --inst_activity_threshold               500
% 2.87/0.98  --inst_out_proof                        true
% 2.87/0.98  
% 2.87/0.98  ------ Resolution Options
% 2.87/0.98  
% 2.87/0.98  --resolution_flag                       false
% 2.87/0.98  --res_lit_sel                           adaptive
% 2.87/0.98  --res_lit_sel_side                      none
% 2.87/0.98  --res_ordering                          kbo
% 2.87/0.98  --res_to_prop_solver                    active
% 2.87/0.98  --res_prop_simpl_new                    false
% 2.87/0.98  --res_prop_simpl_given                  true
% 2.87/0.98  --res_passive_queue_type                priority_queues
% 2.87/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.87/0.98  --res_passive_queues_freq               [15;5]
% 2.87/0.98  --res_forward_subs                      full
% 2.87/0.98  --res_backward_subs                     full
% 2.87/0.98  --res_forward_subs_resolution           true
% 2.87/0.98  --res_backward_subs_resolution          true
% 2.87/0.98  --res_orphan_elimination                true
% 2.87/0.98  --res_time_limit                        2.
% 2.87/0.98  --res_out_proof                         true
% 2.87/0.98  
% 2.87/0.98  ------ Superposition Options
% 2.87/0.98  
% 2.87/0.98  --superposition_flag                    true
% 2.87/0.98  --sup_passive_queue_type                priority_queues
% 2.87/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.87/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.87/0.98  --demod_completeness_check              fast
% 2.87/0.98  --demod_use_ground                      true
% 2.87/0.98  --sup_to_prop_solver                    passive
% 2.87/0.98  --sup_prop_simpl_new                    true
% 2.87/0.98  --sup_prop_simpl_given                  true
% 2.87/0.98  --sup_fun_splitting                     false
% 2.87/0.98  --sup_smt_interval                      50000
% 2.87/0.98  
% 2.87/0.98  ------ Superposition Simplification Setup
% 2.87/0.98  
% 2.87/0.98  --sup_indices_passive                   []
% 2.87/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.87/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.87/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.87/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.87/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.87/0.98  --sup_full_bw                           [BwDemod]
% 2.87/0.98  --sup_immed_triv                        [TrivRules]
% 2.87/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.87/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.87/0.98  --sup_immed_bw_main                     []
% 2.87/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.87/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.87/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.87/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.87/0.98  
% 2.87/0.98  ------ Combination Options
% 2.87/0.98  
% 2.87/0.98  --comb_res_mult                         3
% 2.87/0.98  --comb_sup_mult                         2
% 2.87/0.98  --comb_inst_mult                        10
% 2.87/0.98  
% 2.87/0.98  ------ Debug Options
% 2.87/0.98  
% 2.87/0.98  --dbg_backtrace                         false
% 2.87/0.98  --dbg_dump_prop_clauses                 false
% 2.87/0.98  --dbg_dump_prop_clauses_file            -
% 2.87/0.98  --dbg_out_stat                          false
% 2.87/0.98  
% 2.87/0.98  
% 2.87/0.98  
% 2.87/0.98  
% 2.87/0.98  ------ Proving...
% 2.87/0.98  
% 2.87/0.98  
% 2.87/0.98  % SZS status Theorem for theBenchmark.p
% 2.87/0.98  
% 2.87/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.87/0.98  
% 2.87/0.98  fof(f9,conjecture,(
% 2.87/0.98    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)))),
% 2.87/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.87/0.98  
% 2.87/0.98  fof(f10,negated_conjecture,(
% 2.87/0.98    ~! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)))),
% 2.87/0.98    inference(negated_conjecture,[],[f9])).
% 2.87/0.98  
% 2.87/0.98  fof(f16,plain,(
% 2.87/0.98    ? [X0,X1] : (k7_relat_1(X1,X0) != k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) & v1_relat_1(X1))),
% 2.87/0.98    inference(ennf_transformation,[],[f10])).
% 2.87/0.98  
% 2.87/0.98  fof(f17,plain,(
% 2.87/0.98    ? [X0,X1] : (k7_relat_1(X1,X0) != k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) & v1_relat_1(X1)) => (k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0)) & v1_relat_1(sK1))),
% 2.87/0.98    introduced(choice_axiom,[])).
% 2.87/0.98  
% 2.87/0.98  fof(f18,plain,(
% 2.87/0.98    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0)) & v1_relat_1(sK1)),
% 2.87/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f17])).
% 2.87/0.98  
% 2.87/0.98  fof(f27,plain,(
% 2.87/0.98    v1_relat_1(sK1)),
% 2.87/0.98    inference(cnf_transformation,[],[f18])).
% 2.87/0.98  
% 2.87/0.98  fof(f7,axiom,(
% 2.87/0.98    ! [X0,X1] : (v1_relat_1(X1) => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)))),
% 2.87/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.87/0.98  
% 2.87/0.98  fof(f13,plain,(
% 2.87/0.98    ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 2.87/0.98    inference(ennf_transformation,[],[f7])).
% 2.87/0.98  
% 2.87/0.98  fof(f25,plain,(
% 2.87/0.98    ( ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 2.87/0.98    inference(cnf_transformation,[],[f13])).
% 2.87/0.98  
% 2.87/0.98  fof(f4,axiom,(
% 2.87/0.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.87/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.87/0.98  
% 2.87/0.98  fof(f22,plain,(
% 2.87/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.87/0.98    inference(cnf_transformation,[],[f4])).
% 2.87/0.98  
% 2.87/0.98  fof(f33,plain,(
% 2.87/0.98    ( ! [X0,X1] : (k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X0)) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 2.87/0.98    inference(definition_unfolding,[],[f25,f22])).
% 2.87/0.98  
% 2.87/0.98  fof(f2,axiom,(
% 2.87/0.98    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 2.87/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.87/0.98  
% 2.87/0.98  fof(f20,plain,(
% 2.87/0.98    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 2.87/0.98    inference(cnf_transformation,[],[f2])).
% 2.87/0.98  
% 2.87/0.98  fof(f30,plain,(
% 2.87/0.98    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) )),
% 2.87/0.98    inference(definition_unfolding,[],[f20,f22])).
% 2.87/0.98  
% 2.87/0.98  fof(f8,axiom,(
% 2.87/0.98    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 2.87/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.87/0.98  
% 2.87/0.98  fof(f14,plain,(
% 2.87/0.98    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.87/0.98    inference(ennf_transformation,[],[f8])).
% 2.87/0.98  
% 2.87/0.98  fof(f15,plain,(
% 2.87/0.98    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 2.87/0.98    inference(flattening,[],[f14])).
% 2.87/0.98  
% 2.87/0.98  fof(f26,plain,(
% 2.87/0.98    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 2.87/0.98    inference(cnf_transformation,[],[f15])).
% 2.87/0.98  
% 2.87/0.98  fof(f6,axiom,(
% 2.87/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1))),
% 2.87/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.87/0.98  
% 2.87/0.98  fof(f12,plain,(
% 2.87/0.98    ! [X0,X1,X2] : (k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2))),
% 2.87/0.98    inference(ennf_transformation,[],[f6])).
% 2.87/0.98  
% 2.87/0.98  fof(f24,plain,(
% 2.87/0.98    ( ! [X2,X0,X1] : (k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 2.87/0.98    inference(cnf_transformation,[],[f12])).
% 2.87/0.98  
% 2.87/0.98  fof(f32,plain,(
% 2.87/0.98    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~v1_relat_1(X2)) )),
% 2.87/0.98    inference(definition_unfolding,[],[f24,f22])).
% 2.87/0.98  
% 2.87/0.98  fof(f1,axiom,(
% 2.87/0.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.87/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.87/0.98  
% 2.87/0.98  fof(f19,plain,(
% 2.87/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.87/0.98    inference(cnf_transformation,[],[f1])).
% 2.87/0.98  
% 2.87/0.98  fof(f29,plain,(
% 2.87/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 2.87/0.98    inference(definition_unfolding,[],[f19,f22,f22])).
% 2.87/0.98  
% 2.87/0.98  fof(f28,plain,(
% 2.87/0.98    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0))),
% 2.87/0.98    inference(cnf_transformation,[],[f18])).
% 2.87/0.98  
% 2.87/0.98  fof(f34,plain,(
% 2.87/0.98    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),sK0)))),
% 2.87/0.98    inference(definition_unfolding,[],[f28,f22])).
% 2.87/0.98  
% 2.87/0.98  fof(f5,axiom,(
% 2.87/0.98    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 2.87/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.87/0.98  
% 2.87/0.98  fof(f11,plain,(
% 2.87/0.98    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 2.87/0.98    inference(ennf_transformation,[],[f5])).
% 2.87/0.98  
% 2.87/0.98  fof(f23,plain,(
% 2.87/0.98    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 2.87/0.98    inference(cnf_transformation,[],[f11])).
% 2.87/0.98  
% 2.87/0.98  cnf(c_110,plain,
% 2.87/0.98      ( X0_35 != X1_35 | X2_35 != X1_35 | X2_35 = X0_35 ),
% 2.87/0.98      theory(equality) ).
% 2.87/0.98  
% 2.87/0.98  cnf(c_326,plain,
% 2.87/0.98      ( X0_35 != X1_35
% 2.87/0.98      | k7_relat_1(sK1,sK0) != X1_35
% 2.87/0.98      | k7_relat_1(sK1,sK0) = X0_35 ),
% 2.87/0.98      inference(instantiation,[status(thm)],[c_110]) ).
% 2.87/0.98  
% 2.87/0.98  cnf(c_369,plain,
% 2.87/0.98      ( X0_35 != k7_relat_1(sK1,sK0)
% 2.87/0.98      | k7_relat_1(sK1,sK0) = X0_35
% 2.87/0.98      | k7_relat_1(sK1,sK0) != k7_relat_1(sK1,sK0) ),
% 2.87/0.98      inference(instantiation,[status(thm)],[c_326]) ).
% 2.87/0.98  
% 2.87/0.98  cnf(c_498,plain,
% 2.87/0.98      ( k7_relat_1(X0_35,X0_36) != k7_relat_1(sK1,sK0)
% 2.87/0.98      | k7_relat_1(sK1,sK0) = k7_relat_1(X0_35,X0_36)
% 2.87/0.98      | k7_relat_1(sK1,sK0) != k7_relat_1(sK1,sK0) ),
% 2.87/0.98      inference(instantiation,[status(thm)],[c_369]) ).
% 2.87/0.98  
% 2.87/0.98  cnf(c_872,plain,
% 2.87/0.98      ( k7_relat_1(k7_relat_1(X0_35,X0_36),X1_36) != k7_relat_1(sK1,sK0)
% 2.87/0.98      | k7_relat_1(sK1,sK0) = k7_relat_1(k7_relat_1(X0_35,X0_36),X1_36)
% 2.87/0.98      | k7_relat_1(sK1,sK0) != k7_relat_1(sK1,sK0) ),
% 2.87/0.98      inference(instantiation,[status(thm)],[c_498]) ).
% 2.87/0.98  
% 2.87/0.98  cnf(c_4919,plain,
% 2.87/0.98      ( k7_relat_1(k7_relat_1(X0_35,sK0),k1_relat_1(sK1)) != k7_relat_1(sK1,sK0)
% 2.87/0.98      | k7_relat_1(sK1,sK0) = k7_relat_1(k7_relat_1(X0_35,sK0),k1_relat_1(sK1))
% 2.87/0.98      | k7_relat_1(sK1,sK0) != k7_relat_1(sK1,sK0) ),
% 2.87/0.98      inference(instantiation,[status(thm)],[c_872]) ).
% 2.87/0.98  
% 2.87/0.98  cnf(c_4920,plain,
% 2.87/0.98      ( k7_relat_1(k7_relat_1(sK1,sK0),k1_relat_1(sK1)) != k7_relat_1(sK1,sK0)
% 2.87/0.98      | k7_relat_1(sK1,sK0) = k7_relat_1(k7_relat_1(sK1,sK0),k1_relat_1(sK1))
% 2.87/0.98      | k7_relat_1(sK1,sK0) != k7_relat_1(sK1,sK0) ),
% 2.87/0.98      inference(instantiation,[status(thm)],[c_4919]) ).
% 2.87/0.98  
% 2.87/0.98  cnf(c_8,negated_conjecture,
% 2.87/0.98      ( v1_relat_1(sK1) ),
% 2.87/0.98      inference(cnf_transformation,[],[f27]) ).
% 2.87/0.98  
% 2.87/0.98  cnf(c_98,negated_conjecture,
% 2.87/0.98      ( v1_relat_1(sK1) ),
% 2.87/0.98      inference(subtyping,[status(esa)],[c_8]) ).
% 2.87/0.98  
% 2.87/0.98  cnf(c_258,plain,
% 2.87/0.98      ( v1_relat_1(sK1) = iProver_top ),
% 2.87/0.98      inference(predicate_to_equality,[status(thm)],[c_98]) ).
% 2.87/0.98  
% 2.87/0.98  cnf(c_5,plain,
% 2.87/0.98      ( ~ v1_relat_1(X0)
% 2.87/0.98      | k4_xboole_0(k1_relat_1(X0),k4_xboole_0(k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1)) ),
% 2.87/0.98      inference(cnf_transformation,[],[f33]) ).
% 2.87/0.98  
% 2.87/0.98  cnf(c_101,plain,
% 2.87/0.98      ( ~ v1_relat_1(X0_35)
% 2.87/0.98      | k4_xboole_0(k1_relat_1(X0_35),k4_xboole_0(k1_relat_1(X0_35),X0_36)) = k1_relat_1(k7_relat_1(X0_35,X0_36)) ),
% 2.87/0.98      inference(subtyping,[status(esa)],[c_5]) ).
% 2.87/0.98  
% 2.87/0.98  cnf(c_256,plain,
% 2.87/0.98      ( k4_xboole_0(k1_relat_1(X0_35),k4_xboole_0(k1_relat_1(X0_35),X0_36)) = k1_relat_1(k7_relat_1(X0_35,X0_36))
% 2.87/0.98      | v1_relat_1(X0_35) != iProver_top ),
% 2.87/0.98      inference(predicate_to_equality,[status(thm)],[c_101]) ).
% 2.87/0.98  
% 2.87/0.98  cnf(c_635,plain,
% 2.87/0.98      ( k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),X0_36)) = k1_relat_1(k7_relat_1(sK1,X0_36)) ),
% 2.87/0.98      inference(superposition,[status(thm)],[c_258,c_256]) ).
% 2.87/0.98  
% 2.87/0.98  cnf(c_1,plain,
% 2.87/0.98      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
% 2.87/0.98      inference(cnf_transformation,[],[f30]) ).
% 2.87/0.98  
% 2.87/0.98  cnf(c_105,plain,
% 2.87/0.98      ( r1_tarski(k4_xboole_0(X0_36,k4_xboole_0(X0_36,X1_36)),X0_36) ),
% 2.87/0.98      inference(subtyping,[status(esa)],[c_1]) ).
% 2.87/0.98  
% 2.87/0.98  cnf(c_253,plain,
% 2.87/0.98      ( r1_tarski(k4_xboole_0(X0_36,k4_xboole_0(X0_36,X1_36)),X0_36) = iProver_top ),
% 2.87/0.98      inference(predicate_to_equality,[status(thm)],[c_105]) ).
% 2.87/0.98  
% 2.87/0.98  cnf(c_739,plain,
% 2.87/0.98      ( r1_tarski(k1_relat_1(k7_relat_1(sK1,X0_36)),k1_relat_1(sK1)) = iProver_top ),
% 2.87/0.98      inference(superposition,[status(thm)],[c_635,c_253]) ).
% 2.87/0.98  
% 2.87/0.98  cnf(c_6,plain,
% 2.87/0.98      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 2.87/0.98      | ~ v1_relat_1(X0)
% 2.87/0.98      | k7_relat_1(X0,X1) = X0 ),
% 2.87/0.98      inference(cnf_transformation,[],[f26]) ).
% 2.87/0.98  
% 2.87/0.98  cnf(c_100,plain,
% 2.87/0.98      ( ~ r1_tarski(k1_relat_1(X0_35),X0_36)
% 2.87/0.98      | ~ v1_relat_1(X0_35)
% 2.87/0.98      | k7_relat_1(X0_35,X0_36) = X0_35 ),
% 2.87/0.98      inference(subtyping,[status(esa)],[c_6]) ).
% 2.87/0.98  
% 2.87/0.98  cnf(c_257,plain,
% 2.87/0.98      ( k7_relat_1(X0_35,X0_36) = X0_35
% 2.87/0.98      | r1_tarski(k1_relat_1(X0_35),X0_36) != iProver_top
% 2.87/0.98      | v1_relat_1(X0_35) != iProver_top ),
% 2.87/0.98      inference(predicate_to_equality,[status(thm)],[c_100]) ).
% 2.87/0.98  
% 2.87/0.98  cnf(c_1250,plain,
% 2.87/0.98      ( k7_relat_1(k7_relat_1(sK1,X0_36),k1_relat_1(sK1)) = k7_relat_1(sK1,X0_36)
% 2.87/0.98      | v1_relat_1(k7_relat_1(sK1,X0_36)) != iProver_top ),
% 2.87/0.98      inference(superposition,[status(thm)],[c_739,c_257]) ).
% 2.87/0.98  
% 2.87/0.98  cnf(c_1275,plain,
% 2.87/0.98      ( k7_relat_1(k7_relat_1(sK1,sK0),k1_relat_1(sK1)) = k7_relat_1(sK1,sK0)
% 2.87/0.98      | v1_relat_1(k7_relat_1(sK1,sK0)) != iProver_top ),
% 2.87/0.98      inference(instantiation,[status(thm)],[c_1250]) ).
% 2.87/0.98  
% 2.87/0.98  cnf(c_4,plain,
% 2.87/0.98      ( ~ v1_relat_1(X0)
% 2.87/0.98      | k7_relat_1(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k7_relat_1(k7_relat_1(X0,X1),X2) ),
% 2.87/0.98      inference(cnf_transformation,[],[f32]) ).
% 2.87/0.98  
% 2.87/0.98  cnf(c_102,plain,
% 2.87/0.98      ( ~ v1_relat_1(X0_35)
% 2.87/0.98      | k7_relat_1(X0_35,k4_xboole_0(X0_36,k4_xboole_0(X0_36,X1_36))) = k7_relat_1(k7_relat_1(X0_35,X0_36),X1_36) ),
% 2.87/0.98      inference(subtyping,[status(esa)],[c_4]) ).
% 2.87/0.98  
% 2.87/0.98  cnf(c_1220,plain,
% 2.87/0.98      ( ~ v1_relat_1(X0_35)
% 2.87/0.98      | k7_relat_1(X0_35,k4_xboole_0(sK0,k4_xboole_0(sK0,k1_relat_1(sK1)))) = k7_relat_1(k7_relat_1(X0_35,sK0),k1_relat_1(sK1)) ),
% 2.87/0.98      inference(instantiation,[status(thm)],[c_102]) ).
% 2.87/0.98  
% 2.87/0.98  cnf(c_1223,plain,
% 2.87/0.98      ( ~ v1_relat_1(sK1)
% 2.87/0.98      | k7_relat_1(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,k1_relat_1(sK1)))) = k7_relat_1(k7_relat_1(sK1,sK0),k1_relat_1(sK1)) ),
% 2.87/0.98      inference(instantiation,[status(thm)],[c_1220]) ).
% 2.87/0.98  
% 2.87/0.98  cnf(c_374,plain,
% 2.87/0.98      ( X0_35 != k7_relat_1(X1_35,X0_36)
% 2.87/0.98      | k7_relat_1(sK1,sK0) = X0_35
% 2.87/0.98      | k7_relat_1(sK1,sK0) != k7_relat_1(X1_35,X0_36) ),
% 2.87/0.98      inference(instantiation,[status(thm)],[c_326]) ).
% 2.87/0.98  
% 2.87/0.98  cnf(c_536,plain,
% 2.87/0.98      ( k7_relat_1(X0_35,X0_36) != k7_relat_1(X1_35,X1_36)
% 2.87/0.98      | k7_relat_1(sK1,sK0) != k7_relat_1(X1_35,X1_36)
% 2.87/0.98      | k7_relat_1(sK1,sK0) = k7_relat_1(X0_35,X0_36) ),
% 2.87/0.98      inference(instantiation,[status(thm)],[c_374]) ).
% 2.87/0.98  
% 2.87/0.98  cnf(c_1103,plain,
% 2.87/0.98      ( k7_relat_1(X0_35,k4_xboole_0(sK0,k4_xboole_0(sK0,k1_relat_1(sK1)))) != k7_relat_1(X1_35,X0_36)
% 2.87/0.98      | k7_relat_1(sK1,sK0) != k7_relat_1(X1_35,X0_36)
% 2.87/0.98      | k7_relat_1(sK1,sK0) = k7_relat_1(X0_35,k4_xboole_0(sK0,k4_xboole_0(sK0,k1_relat_1(sK1)))) ),
% 2.87/0.98      inference(instantiation,[status(thm)],[c_536]) ).
% 2.87/0.98  
% 2.87/0.98  cnf(c_1219,plain,
% 2.87/0.98      ( k7_relat_1(X0_35,k4_xboole_0(sK0,k4_xboole_0(sK0,k1_relat_1(sK1)))) != k7_relat_1(k7_relat_1(X0_35,sK0),k1_relat_1(sK1))
% 2.87/0.98      | k7_relat_1(sK1,sK0) = k7_relat_1(X0_35,k4_xboole_0(sK0,k4_xboole_0(sK0,k1_relat_1(sK1))))
% 2.87/0.98      | k7_relat_1(sK1,sK0) != k7_relat_1(k7_relat_1(X0_35,sK0),k1_relat_1(sK1)) ),
% 2.87/0.98      inference(instantiation,[status(thm)],[c_1103]) ).
% 2.87/0.98  
% 2.87/0.98  cnf(c_1221,plain,
% 2.87/0.98      ( k7_relat_1(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,k1_relat_1(sK1)))) != k7_relat_1(k7_relat_1(sK1,sK0),k1_relat_1(sK1))
% 2.87/0.98      | k7_relat_1(sK1,sK0) != k7_relat_1(k7_relat_1(sK1,sK0),k1_relat_1(sK1))
% 2.87/0.98      | k7_relat_1(sK1,sK0) = k7_relat_1(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,k1_relat_1(sK1)))) ),
% 2.87/0.98      inference(instantiation,[status(thm)],[c_1219]) ).
% 2.87/0.98  
% 2.87/0.98  cnf(c_304,plain,
% 2.87/0.98      ( k7_relat_1(sK1,k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),sK0))) != X0_35
% 2.87/0.98      | k7_relat_1(sK1,sK0) != X0_35
% 2.87/0.98      | k7_relat_1(sK1,sK0) = k7_relat_1(sK1,k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),sK0))) ),
% 2.87/0.98      inference(instantiation,[status(thm)],[c_110]) ).
% 2.87/0.98  
% 2.87/0.98  cnf(c_327,plain,
% 2.87/0.98      ( k7_relat_1(sK1,k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),sK0))) != k7_relat_1(X0_35,X0_36)
% 2.87/0.98      | k7_relat_1(sK1,sK0) != k7_relat_1(X0_35,X0_36)
% 2.87/0.98      | k7_relat_1(sK1,sK0) = k7_relat_1(sK1,k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),sK0))) ),
% 2.87/0.98      inference(instantiation,[status(thm)],[c_304]) ).
% 2.87/0.98  
% 2.87/0.98  cnf(c_694,plain,
% 2.87/0.98      ( k7_relat_1(sK1,k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),sK0))) != k7_relat_1(X0_35,k4_xboole_0(sK0,k4_xboole_0(sK0,k1_relat_1(sK1))))
% 2.87/0.98      | k7_relat_1(sK1,sK0) != k7_relat_1(X0_35,k4_xboole_0(sK0,k4_xboole_0(sK0,k1_relat_1(sK1))))
% 2.87/0.98      | k7_relat_1(sK1,sK0) = k7_relat_1(sK1,k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),sK0))) ),
% 2.87/0.98      inference(instantiation,[status(thm)],[c_327]) ).
% 2.87/0.98  
% 2.87/0.98  cnf(c_695,plain,
% 2.87/0.98      ( k7_relat_1(sK1,k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),sK0))) != k7_relat_1(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,k1_relat_1(sK1))))
% 2.87/0.98      | k7_relat_1(sK1,sK0) = k7_relat_1(sK1,k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),sK0)))
% 2.87/0.98      | k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,k1_relat_1(sK1)))) ),
% 2.87/0.98      inference(instantiation,[status(thm)],[c_694]) ).
% 2.87/0.98  
% 2.87/0.98  cnf(c_114,plain,
% 2.87/0.98      ( X0_36 != X1_36
% 2.87/0.98      | X0_35 != X1_35
% 2.87/0.98      | k7_relat_1(X0_35,X0_36) = k7_relat_1(X1_35,X1_36) ),
% 2.87/0.98      theory(equality) ).
% 2.87/0.98  
% 2.87/0.98  cnf(c_381,plain,
% 2.87/0.98      ( k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),sK0)) != X0_36
% 2.87/0.98      | k7_relat_1(sK1,k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),sK0))) = k7_relat_1(X0_35,X0_36)
% 2.87/0.98      | sK1 != X0_35 ),
% 2.87/0.98      inference(instantiation,[status(thm)],[c_114]) ).
% 2.87/0.98  
% 2.87/0.98  cnf(c_513,plain,
% 2.87/0.98      ( k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),sK0)) != k4_xboole_0(sK0,k4_xboole_0(sK0,k1_relat_1(sK1)))
% 2.87/0.98      | k7_relat_1(sK1,k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),sK0))) = k7_relat_1(X0_35,k4_xboole_0(sK0,k4_xboole_0(sK0,k1_relat_1(sK1))))
% 2.87/0.98      | sK1 != X0_35 ),
% 2.87/0.98      inference(instantiation,[status(thm)],[c_381]) ).
% 2.87/0.98  
% 2.87/0.98  cnf(c_514,plain,
% 2.87/0.98      ( k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),sK0)) != k4_xboole_0(sK0,k4_xboole_0(sK0,k1_relat_1(sK1)))
% 2.87/0.98      | k7_relat_1(sK1,k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),sK0))) = k7_relat_1(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,k1_relat_1(sK1))))
% 2.87/0.98      | sK1 != sK1 ),
% 2.87/0.98      inference(instantiation,[status(thm)],[c_513]) ).
% 2.87/0.98  
% 2.87/0.98  cnf(c_0,plain,
% 2.87/0.98      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 2.87/0.98      inference(cnf_transformation,[],[f29]) ).
% 2.87/0.98  
% 2.87/0.98  cnf(c_106,plain,
% 2.87/0.98      ( k4_xboole_0(X0_36,k4_xboole_0(X0_36,X1_36)) = k4_xboole_0(X1_36,k4_xboole_0(X1_36,X0_36)) ),
% 2.87/0.98      inference(subtyping,[status(esa)],[c_0]) ).
% 2.87/0.98  
% 2.87/0.98  cnf(c_356,plain,
% 2.87/0.98      ( k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),sK0)) = k4_xboole_0(sK0,k4_xboole_0(sK0,k1_relat_1(sK1))) ),
% 2.87/0.98      inference(instantiation,[status(thm)],[c_106]) ).
% 2.87/0.98  
% 2.87/0.98  cnf(c_7,negated_conjecture,
% 2.87/0.98      ( k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),sK0))) ),
% 2.87/0.98      inference(cnf_transformation,[],[f34]) ).
% 2.87/0.98  
% 2.87/0.98  cnf(c_99,negated_conjecture,
% 2.87/0.98      ( k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),sK0))) ),
% 2.87/0.98      inference(subtyping,[status(esa)],[c_7]) ).
% 2.87/0.98  
% 2.87/0.98  cnf(c_3,plain,
% 2.87/0.98      ( ~ v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1)) ),
% 2.87/0.98      inference(cnf_transformation,[],[f23]) ).
% 2.87/0.98  
% 2.87/0.98  cnf(c_103,plain,
% 2.87/0.98      ( ~ v1_relat_1(X0_35) | v1_relat_1(k7_relat_1(X0_35,X0_36)) ),
% 2.87/0.98      inference(subtyping,[status(esa)],[c_3]) ).
% 2.87/0.98  
% 2.87/0.98  cnf(c_130,plain,
% 2.87/0.98      ( v1_relat_1(X0_35) != iProver_top
% 2.87/0.98      | v1_relat_1(k7_relat_1(X0_35,X0_36)) = iProver_top ),
% 2.87/0.98      inference(predicate_to_equality,[status(thm)],[c_103]) ).
% 2.87/0.98  
% 2.87/0.98  cnf(c_132,plain,
% 2.87/0.98      ( v1_relat_1(k7_relat_1(sK1,sK0)) = iProver_top
% 2.87/0.98      | v1_relat_1(sK1) != iProver_top ),
% 2.87/0.98      inference(instantiation,[status(thm)],[c_130]) ).
% 2.87/0.98  
% 2.87/0.98  cnf(c_109,plain,( X0_36 = X0_36 ),theory(equality) ).
% 2.87/0.98  
% 2.87/0.98  cnf(c_124,plain,
% 2.87/0.98      ( sK0 = sK0 ),
% 2.87/0.98      inference(instantiation,[status(thm)],[c_109]) ).
% 2.87/0.98  
% 2.87/0.98  cnf(c_108,plain,( X0_35 = X0_35 ),theory(equality) ).
% 2.87/0.98  
% 2.87/0.98  cnf(c_123,plain,
% 2.87/0.98      ( sK1 = sK1 ),
% 2.87/0.98      inference(instantiation,[status(thm)],[c_108]) ).
% 2.87/0.98  
% 2.87/0.98  cnf(c_119,plain,
% 2.87/0.98      ( sK0 != sK0
% 2.87/0.98      | k7_relat_1(sK1,sK0) = k7_relat_1(sK1,sK0)
% 2.87/0.98      | sK1 != sK1 ),
% 2.87/0.98      inference(instantiation,[status(thm)],[c_114]) ).
% 2.87/0.98  
% 2.87/0.98  cnf(c_9,plain,
% 2.87/0.98      ( v1_relat_1(sK1) = iProver_top ),
% 2.87/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.87/0.98  
% 2.87/0.98  cnf(contradiction,plain,
% 2.87/0.98      ( $false ),
% 2.87/0.98      inference(minisat,
% 2.87/0.98                [status(thm)],
% 2.87/0.98                [c_4920,c_1275,c_1223,c_1221,c_695,c_514,c_356,c_99,
% 2.87/0.98                 c_132,c_124,c_123,c_119,c_9,c_8]) ).
% 2.87/0.98  
% 2.87/0.98  
% 2.87/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.87/0.98  
% 2.87/0.98  ------                               Statistics
% 2.87/0.98  
% 2.87/0.98  ------ General
% 2.87/0.98  
% 2.87/0.98  abstr_ref_over_cycles:                  0
% 2.87/0.98  abstr_ref_under_cycles:                 0
% 2.87/0.98  gc_basic_clause_elim:                   0
% 2.87/0.98  forced_gc_time:                         0
% 2.87/0.98  parsing_time:                           0.009
% 2.87/0.98  unif_index_cands_time:                  0.
% 2.87/0.98  unif_index_add_time:                    0.
% 2.87/0.98  orderings_time:                         0.
% 2.87/0.98  out_proof_time:                         0.007
% 2.87/0.98  total_time:                             0.186
% 2.87/0.98  num_of_symbols:                         40
% 2.87/0.98  num_of_terms:                           5504
% 2.87/0.98  
% 2.87/0.98  ------ Preprocessing
% 2.87/0.98  
% 2.87/0.98  num_of_splits:                          0
% 2.87/0.98  num_of_split_atoms:                     0
% 2.87/0.98  num_of_reused_defs:                     0
% 2.87/0.98  num_eq_ax_congr_red:                    2
% 2.87/0.98  num_of_sem_filtered_clauses:            1
% 2.87/0.98  num_of_subtypes:                        2
% 2.87/0.98  monotx_restored_types:                  0
% 2.87/0.98  sat_num_of_epr_types:                   0
% 2.87/0.98  sat_num_of_non_cyclic_types:            0
% 2.87/0.98  sat_guarded_non_collapsed_types:        1
% 2.87/0.98  num_pure_diseq_elim:                    0
% 2.87/0.99  simp_replaced_by:                       0
% 2.87/0.99  res_preprocessed:                       46
% 2.87/0.99  prep_upred:                             0
% 2.87/0.99  prep_unflattend:                        1
% 2.87/0.99  smt_new_axioms:                         0
% 2.87/0.99  pred_elim_cands:                        2
% 2.87/0.99  pred_elim:                              0
% 2.87/0.99  pred_elim_cl:                           0
% 2.87/0.99  pred_elim_cycles:                       1
% 2.87/0.99  merged_defs:                            0
% 2.87/0.99  merged_defs_ncl:                        0
% 2.87/0.99  bin_hyper_res:                          0
% 2.87/0.99  prep_cycles:                            3
% 2.87/0.99  pred_elim_time:                         0.001
% 2.87/0.99  splitting_time:                         0.
% 2.87/0.99  sem_filter_time:                        0.
% 2.87/0.99  monotx_time:                            0.
% 2.87/0.99  subtype_inf_time:                       0.
% 2.87/0.99  
% 2.87/0.99  ------ Problem properties
% 2.87/0.99  
% 2.87/0.99  clauses:                                9
% 2.87/0.99  conjectures:                            2
% 2.87/0.99  epr:                                    1
% 2.87/0.99  horn:                                   9
% 2.87/0.99  ground:                                 2
% 2.87/0.99  unary:                                  5
% 2.87/0.99  binary:                                 3
% 2.87/0.99  lits:                                   14
% 2.87/0.99  lits_eq:                                6
% 2.87/0.99  fd_pure:                                0
% 2.87/0.99  fd_pseudo:                              0
% 2.87/0.99  fd_cond:                                0
% 2.87/0.99  fd_pseudo_cond:                         0
% 2.87/0.99  ac_symbols:                             0
% 2.87/0.99  
% 2.87/0.99  ------ Propositional Solver
% 2.87/0.99  
% 2.87/0.99  prop_solver_calls:                      27
% 2.87/0.99  prop_fast_solver_calls:                 235
% 2.87/0.99  smt_solver_calls:                       0
% 2.87/0.99  smt_fast_solver_calls:                  0
% 2.87/0.99  prop_num_of_clauses:                    1172
% 2.87/0.99  prop_preprocess_simplified:             2457
% 2.87/0.99  prop_fo_subsumed:                       1
% 2.87/0.99  prop_solver_time:                       0.
% 2.87/0.99  smt_solver_time:                        0.
% 2.87/0.99  smt_fast_solver_time:                   0.
% 2.87/0.99  prop_fast_solver_time:                  0.
% 2.87/0.99  prop_unsat_core_time:                   0.
% 2.87/0.99  
% 2.87/0.99  ------ QBF
% 2.87/0.99  
% 2.87/0.99  qbf_q_res:                              0
% 2.87/0.99  qbf_num_tautologies:                    0
% 2.87/0.99  qbf_prep_cycles:                        0
% 2.87/0.99  
% 2.87/0.99  ------ BMC1
% 2.87/0.99  
% 2.87/0.99  bmc1_current_bound:                     -1
% 2.87/0.99  bmc1_last_solved_bound:                 -1
% 2.87/0.99  bmc1_unsat_core_size:                   -1
% 2.87/0.99  bmc1_unsat_core_parents_size:           -1
% 2.87/0.99  bmc1_merge_next_fun:                    0
% 2.87/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.87/0.99  
% 2.87/0.99  ------ Instantiation
% 2.87/0.99  
% 2.87/0.99  inst_num_of_clauses:                    493
% 2.87/0.99  inst_num_in_passive:                    113
% 2.87/0.99  inst_num_in_active:                     241
% 2.87/0.99  inst_num_in_unprocessed:                139
% 2.87/0.99  inst_num_of_loops:                      250
% 2.87/0.99  inst_num_of_learning_restarts:          0
% 2.87/0.99  inst_num_moves_active_passive:          3
% 2.87/0.99  inst_lit_activity:                      0
% 2.87/0.99  inst_lit_activity_moves:                0
% 2.87/0.99  inst_num_tautologies:                   0
% 2.87/0.99  inst_num_prop_implied:                  0
% 2.87/0.99  inst_num_existing_simplified:           0
% 2.87/0.99  inst_num_eq_res_simplified:             0
% 2.87/0.99  inst_num_child_elim:                    0
% 2.87/0.99  inst_num_of_dismatching_blockings:      833
% 2.87/0.99  inst_num_of_non_proper_insts:           892
% 2.87/0.99  inst_num_of_duplicates:                 0
% 2.87/0.99  inst_inst_num_from_inst_to_res:         0
% 2.87/0.99  inst_dismatching_checking_time:         0.
% 2.87/0.99  
% 2.87/0.99  ------ Resolution
% 2.87/0.99  
% 2.87/0.99  res_num_of_clauses:                     0
% 2.87/0.99  res_num_in_passive:                     0
% 2.87/0.99  res_num_in_active:                      0
% 2.87/0.99  res_num_of_loops:                       49
% 2.87/0.99  res_forward_subset_subsumed:            226
% 2.87/0.99  res_backward_subset_subsumed:           4
% 2.87/0.99  res_forward_subsumed:                   0
% 2.87/0.99  res_backward_subsumed:                  0
% 2.87/0.99  res_forward_subsumption_resolution:     0
% 2.87/0.99  res_backward_subsumption_resolution:    0
% 2.87/0.99  res_clause_to_clause_subsumption:       1331
% 2.87/0.99  res_orphan_elimination:                 0
% 2.87/0.99  res_tautology_del:                      139
% 2.87/0.99  res_num_eq_res_simplified:              0
% 2.87/0.99  res_num_sel_changes:                    0
% 2.87/0.99  res_moves_from_active_to_pass:          0
% 2.87/0.99  
% 2.87/0.99  ------ Superposition
% 2.87/0.99  
% 2.87/0.99  sup_time_total:                         0.
% 2.87/0.99  sup_time_generating:                    0.
% 2.87/0.99  sup_time_sim_full:                      0.
% 2.87/0.99  sup_time_sim_immed:                     0.
% 2.87/0.99  
% 2.87/0.99  sup_num_of_clauses:                     187
% 2.87/0.99  sup_num_in_active:                      45
% 2.87/0.99  sup_num_in_passive:                     142
% 2.87/0.99  sup_num_of_loops:                       48
% 2.87/0.99  sup_fw_superposition:                   419
% 2.87/0.99  sup_bw_superposition:                   290
% 2.87/0.99  sup_immediate_simplified:               343
% 2.87/0.99  sup_given_eliminated:                   0
% 2.87/0.99  comparisons_done:                       0
% 2.87/0.99  comparisons_avoided:                    0
% 2.87/0.99  
% 2.87/0.99  ------ Simplifications
% 2.87/0.99  
% 2.87/0.99  
% 2.87/0.99  sim_fw_subset_subsumed:                 1
% 2.87/0.99  sim_bw_subset_subsumed:                 2
% 2.87/0.99  sim_fw_subsumed:                        63
% 2.87/0.99  sim_bw_subsumed:                        13
% 2.87/0.99  sim_fw_subsumption_res:                 0
% 2.87/0.99  sim_bw_subsumption_res:                 0
% 2.87/0.99  sim_tautology_del:                      0
% 2.87/0.99  sim_eq_tautology_del:                   36
% 2.87/0.99  sim_eq_res_simp:                        0
% 2.87/0.99  sim_fw_demodulated:                     81
% 2.87/0.99  sim_bw_demodulated:                     16
% 2.87/0.99  sim_light_normalised:                   235
% 2.87/0.99  sim_joinable_taut:                      0
% 2.87/0.99  sim_joinable_simp:                      0
% 2.87/0.99  sim_ac_normalised:                      0
% 2.87/0.99  sim_smt_subsumption:                    0
% 2.87/0.99  
%------------------------------------------------------------------------------
