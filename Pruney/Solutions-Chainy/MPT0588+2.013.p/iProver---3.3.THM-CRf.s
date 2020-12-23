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
% DateTime   : Thu Dec  3 11:48:05 EST 2020

% Result     : Theorem 2.98s
% Output     : CNFRefutation 2.98s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 150 expanded)
%              Number of clauses        :   44 (  50 expanded)
%              Number of leaves         :   16 (  39 expanded)
%              Depth                    :   15
%              Number of atoms          :  181 ( 261 expanded)
%              Number of equality atoms :   83 ( 146 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    5 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f21,plain,(
    ? [X0,X1] :
      ( k7_relat_1(X1,X0) != k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f22,plain,
    ( ? [X0,X1] :
        ( k7_relat_1(X1,X0) != k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
        & v1_relat_1(X1) )
   => ( k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f22])).

fof(f35,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f37,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f26,f27])).

fof(f40,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f25,f37,f37])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f28,f37])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f29,f38])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f24,f38])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f30,f38])).

fof(f36,plain,(
    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f43,plain,(
    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k1_setfam_1(k2_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),sK0))) ),
    inference(definition_unfolding,[],[f36,f38])).

cnf(c_9,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_102,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_302,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_102])).

cnf(c_6,plain,
    ( r1_tarski(k7_relat_1(X0,X1),X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_105,plain,
    ( r1_tarski(k7_relat_1(X0_37,X1_37),X0_37)
    | ~ v1_relat_1(X0_37) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_300,plain,
    ( r1_tarski(k7_relat_1(X0_37,X1_37),X0_37) = iProver_top
    | v1_relat_1(X0_37) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_105])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_106,plain,
    ( ~ r1_tarski(X0_37,X1_37)
    | r1_tarski(k1_relat_1(X0_37),k1_relat_1(X1_37))
    | ~ v1_relat_1(X0_37)
    | ~ v1_relat_1(X1_37) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_299,plain,
    ( r1_tarski(X0_37,X1_37) != iProver_top
    | r1_tarski(k1_relat_1(X0_37),k1_relat_1(X1_37)) = iProver_top
    | v1_relat_1(X0_37) != iProver_top
    | v1_relat_1(X1_37) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_106])).

cnf(c_7,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_104,plain,
    ( ~ r1_tarski(k1_relat_1(X0_37),X1_37)
    | ~ v1_relat_1(X0_37)
    | k7_relat_1(X0_37,X1_37) = X0_37 ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_301,plain,
    ( k7_relat_1(X0_37,X1_37) = X0_37
    | r1_tarski(k1_relat_1(X0_37),X1_37) != iProver_top
    | v1_relat_1(X0_37) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_104])).

cnf(c_731,plain,
    ( k7_relat_1(X0_37,k1_relat_1(X1_37)) = X0_37
    | r1_tarski(X0_37,X1_37) != iProver_top
    | v1_relat_1(X0_37) != iProver_top
    | v1_relat_1(X1_37) != iProver_top ),
    inference(superposition,[status(thm)],[c_299,c_301])).

cnf(c_118,plain,
    ( X0_38 != X1_38
    | k1_setfam_1(X0_38) = k1_setfam_1(X1_38) ),
    theory(equality)).

cnf(c_120,plain,
    ( ~ v1_relat_1(X0_37)
    | v1_relat_1(X1_37)
    | X1_37 != X0_37 ),
    theory(equality)).

cnf(c_385,plain,
    ( ~ v1_relat_1(k1_setfam_1(X0_38))
    | v1_relat_1(k1_setfam_1(X1_38))
    | X1_38 != X0_38 ),
    inference(resolution,[status(thm)],[c_118,c_120])).

cnf(c_1,plain,
    ( k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_110,plain,
    ( k2_enumset1(X0_37,X0_37,X0_37,X1_37) = k2_enumset1(X1_37,X1_37,X1_37,X0_37) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_447,plain,
    ( ~ v1_relat_1(k1_setfam_1(k2_enumset1(X0_37,X0_37,X0_37,X1_37)))
    | v1_relat_1(k1_setfam_1(k2_enumset1(X1_37,X1_37,X1_37,X0_37))) ),
    inference(resolution,[status(thm)],[c_385,c_110])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_109,plain,
    ( ~ v1_relat_1(X0_37)
    | v1_relat_1(k1_setfam_1(k2_enumset1(X0_37,X0_37,X0_37,X1_37))) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_2044,plain,
    ( ~ v1_relat_1(X0_37)
    | v1_relat_1(k1_setfam_1(k2_enumset1(X1_37,X1_37,X1_37,X0_37))) ),
    inference(resolution,[status(thm)],[c_447,c_109])).

cnf(c_115,plain,
    ( X0_37 != X1_37
    | X2_37 != X1_37
    | X2_37 = X0_37 ),
    theory(equality)).

cnf(c_113,plain,
    ( X0_37 = X0_37 ),
    theory(equality)).

cnf(c_623,plain,
    ( X0_37 != X1_37
    | X1_37 = X0_37 ),
    inference(resolution,[status(thm)],[c_115,c_113])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_111,plain,
    ( ~ r1_tarski(X0_37,X1_37)
    | k1_setfam_1(k2_enumset1(X0_37,X0_37,X0_37,X1_37)) = X0_37 ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_879,plain,
    ( ~ r1_tarski(X0_37,X1_37)
    | X0_37 = k1_setfam_1(k2_enumset1(X0_37,X0_37,X0_37,X1_37)) ),
    inference(resolution,[status(thm)],[c_623,c_111])).

cnf(c_1209,plain,
    ( ~ r1_tarski(X0_37,X1_37)
    | v1_relat_1(X0_37)
    | ~ v1_relat_1(k1_setfam_1(k2_enumset1(X0_37,X0_37,X0_37,X1_37))) ),
    inference(resolution,[status(thm)],[c_879,c_120])).

cnf(c_2166,plain,
    ( ~ r1_tarski(X0_37,X1_37)
    | ~ v1_relat_1(X1_37)
    | v1_relat_1(X0_37) ),
    inference(resolution,[status(thm)],[c_2044,c_1209])).

cnf(c_2168,plain,
    ( r1_tarski(X0_37,X1_37) != iProver_top
    | v1_relat_1(X1_37) != iProver_top
    | v1_relat_1(X0_37) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2166])).

cnf(c_2898,plain,
    ( r1_tarski(X0_37,X1_37) != iProver_top
    | k7_relat_1(X0_37,k1_relat_1(X1_37)) = X0_37
    | v1_relat_1(X1_37) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_731,c_2168])).

cnf(c_2899,plain,
    ( k7_relat_1(X0_37,k1_relat_1(X1_37)) = X0_37
    | r1_tarski(X0_37,X1_37) != iProver_top
    | v1_relat_1(X1_37) != iProver_top ),
    inference(renaming,[status(thm)],[c_2898])).

cnf(c_2902,plain,
    ( k7_relat_1(k7_relat_1(X0_37,X1_37),k1_relat_1(X0_37)) = k7_relat_1(X0_37,X1_37)
    | v1_relat_1(X0_37) != iProver_top ),
    inference(superposition,[status(thm)],[c_300,c_2899])).

cnf(c_3213,plain,
    ( k7_relat_1(k7_relat_1(sK1,X0_37),k1_relat_1(sK1)) = k7_relat_1(sK1,X0_37) ),
    inference(superposition,[status(thm)],[c_302,c_2902])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) = k7_relat_1(k7_relat_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_108,plain,
    ( ~ v1_relat_1(X0_37)
    | k7_relat_1(X0_37,k1_setfam_1(k2_enumset1(X1_37,X1_37,X1_37,X2_37))) = k7_relat_1(k7_relat_1(X0_37,X1_37),X2_37) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_297,plain,
    ( k7_relat_1(X0_37,k1_setfam_1(k2_enumset1(X1_37,X1_37,X1_37,X2_37))) = k7_relat_1(k7_relat_1(X0_37,X1_37),X2_37)
    | v1_relat_1(X0_37) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_108])).

cnf(c_605,plain,
    ( k7_relat_1(sK1,k1_setfam_1(k2_enumset1(X0_37,X0_37,X0_37,X1_37))) = k7_relat_1(k7_relat_1(sK1,X0_37),X1_37) ),
    inference(superposition,[status(thm)],[c_302,c_297])).

cnf(c_8,negated_conjecture,
    ( k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k1_setfam_1(k2_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),sK0))) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_103,negated_conjecture,
    ( k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k1_setfam_1(k2_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),sK0))) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_329,plain,
    ( k7_relat_1(sK1,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k1_relat_1(sK1)))) != k7_relat_1(sK1,sK0) ),
    inference(superposition,[status(thm)],[c_110,c_103])).

cnf(c_871,plain,
    ( k7_relat_1(k7_relat_1(sK1,sK0),k1_relat_1(sK1)) != k7_relat_1(sK1,sK0) ),
    inference(superposition,[status(thm)],[c_605,c_329])).

cnf(c_3250,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_3213,c_871])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:03:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 2.98/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.98/1.01  
% 2.98/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.98/1.01  
% 2.98/1.01  ------  iProver source info
% 2.98/1.01  
% 2.98/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.98/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.98/1.01  git: non_committed_changes: false
% 2.98/1.01  git: last_make_outside_of_git: false
% 2.98/1.01  
% 2.98/1.01  ------ 
% 2.98/1.01  ------ Parsing...
% 2.98/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.98/1.01  
% 2.98/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.98/1.01  
% 2.98/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.98/1.01  
% 2.98/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.98/1.01  ------ Proving...
% 2.98/1.01  ------ Problem Properties 
% 2.98/1.01  
% 2.98/1.01  
% 2.98/1.01  clauses                                 10
% 2.98/1.01  conjectures                             2
% 2.98/1.01  EPR                                     1
% 2.98/1.01  Horn                                    10
% 2.98/1.01  unary                                   3
% 2.98/1.01  binary                                  4
% 2.98/1.01  lits                                    22
% 2.98/1.01  lits eq                                 5
% 2.98/1.01  fd_pure                                 0
% 2.98/1.01  fd_pseudo                               0
% 2.98/1.01  fd_cond                                 0
% 2.98/1.01  fd_pseudo_cond                          0
% 2.98/1.01  AC symbols                              0
% 2.98/1.01  
% 2.98/1.01  ------ Input Options Time Limit: Unbounded
% 2.98/1.01  
% 2.98/1.01  
% 2.98/1.01  ------ 
% 2.98/1.01  Current options:
% 2.98/1.01  ------ 
% 2.98/1.01  
% 2.98/1.01  
% 2.98/1.01  
% 2.98/1.01  
% 2.98/1.01  ------ Proving...
% 2.98/1.01  
% 2.98/1.01  
% 2.98/1.01  % SZS status Theorem for theBenchmark.p
% 2.98/1.01  
% 2.98/1.01   Resolution empty clause
% 2.98/1.01  
% 2.98/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.98/1.01  
% 2.98/1.01  fof(f11,conjecture,(
% 2.98/1.01    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)))),
% 2.98/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.98/1.01  
% 2.98/1.01  fof(f12,negated_conjecture,(
% 2.98/1.01    ~! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)))),
% 2.98/1.01    inference(negated_conjecture,[],[f11])).
% 2.98/1.01  
% 2.98/1.01  fof(f21,plain,(
% 2.98/1.01    ? [X0,X1] : (k7_relat_1(X1,X0) != k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) & v1_relat_1(X1))),
% 2.98/1.01    inference(ennf_transformation,[],[f12])).
% 2.98/1.01  
% 2.98/1.01  fof(f22,plain,(
% 2.98/1.01    ? [X0,X1] : (k7_relat_1(X1,X0) != k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) & v1_relat_1(X1)) => (k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0)) & v1_relat_1(sK1))),
% 2.98/1.01    introduced(choice_axiom,[])).
% 2.98/1.01  
% 2.98/1.01  fof(f23,plain,(
% 2.98/1.01    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0)) & v1_relat_1(sK1)),
% 2.98/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f22])).
% 2.98/1.01  
% 2.98/1.01  fof(f35,plain,(
% 2.98/1.01    v1_relat_1(sK1)),
% 2.98/1.01    inference(cnf_transformation,[],[f23])).
% 2.98/1.01  
% 2.98/1.01  fof(f9,axiom,(
% 2.98/1.01    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 2.98/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.98/1.01  
% 2.98/1.01  fof(f18,plain,(
% 2.98/1.01    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 2.98/1.01    inference(ennf_transformation,[],[f9])).
% 2.98/1.01  
% 2.98/1.01  fof(f33,plain,(
% 2.98/1.01    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 2.98/1.01    inference(cnf_transformation,[],[f18])).
% 2.98/1.01  
% 2.98/1.01  fof(f8,axiom,(
% 2.98/1.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 2.98/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.98/1.01  
% 2.98/1.01  fof(f16,plain,(
% 2.98/1.01    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.98/1.01    inference(ennf_transformation,[],[f8])).
% 2.98/1.01  
% 2.98/1.01  fof(f17,plain,(
% 2.98/1.01    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.98/1.01    inference(flattening,[],[f16])).
% 2.98/1.01  
% 2.98/1.01  fof(f31,plain,(
% 2.98/1.01    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.98/1.01    inference(cnf_transformation,[],[f17])).
% 2.98/1.01  
% 2.98/1.01  fof(f10,axiom,(
% 2.98/1.01    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 2.98/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.98/1.01  
% 2.98/1.01  fof(f19,plain,(
% 2.98/1.01    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.98/1.01    inference(ennf_transformation,[],[f10])).
% 2.98/1.01  
% 2.98/1.01  fof(f20,plain,(
% 2.98/1.01    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 2.98/1.01    inference(flattening,[],[f19])).
% 2.98/1.01  
% 2.98/1.01  fof(f34,plain,(
% 2.98/1.01    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 2.98/1.01    inference(cnf_transformation,[],[f20])).
% 2.98/1.01  
% 2.98/1.01  fof(f2,axiom,(
% 2.98/1.01    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 2.98/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.98/1.01  
% 2.98/1.01  fof(f25,plain,(
% 2.98/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 2.98/1.01    inference(cnf_transformation,[],[f2])).
% 2.98/1.01  
% 2.98/1.01  fof(f3,axiom,(
% 2.98/1.01    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.98/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.98/1.01  
% 2.98/1.01  fof(f26,plain,(
% 2.98/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.98/1.01    inference(cnf_transformation,[],[f3])).
% 2.98/1.01  
% 2.98/1.01  fof(f4,axiom,(
% 2.98/1.01    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.98/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.98/1.01  
% 2.98/1.01  fof(f27,plain,(
% 2.98/1.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.98/1.01    inference(cnf_transformation,[],[f4])).
% 2.98/1.01  
% 2.98/1.01  fof(f37,plain,(
% 2.98/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 2.98/1.01    inference(definition_unfolding,[],[f26,f27])).
% 2.98/1.01  
% 2.98/1.01  fof(f40,plain,(
% 2.98/1.01    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0)) )),
% 2.98/1.01    inference(definition_unfolding,[],[f25,f37,f37])).
% 2.98/1.01  
% 2.98/1.01  fof(f6,axiom,(
% 2.98/1.01    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k3_xboole_0(X0,X1)))),
% 2.98/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.98/1.01  
% 2.98/1.01  fof(f14,plain,(
% 2.98/1.01    ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 2.98/1.01    inference(ennf_transformation,[],[f6])).
% 2.98/1.01  
% 2.98/1.01  fof(f29,plain,(
% 2.98/1.01    ( ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 2.98/1.01    inference(cnf_transformation,[],[f14])).
% 2.98/1.01  
% 2.98/1.01  fof(f5,axiom,(
% 2.98/1.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.98/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.98/1.01  
% 2.98/1.01  fof(f28,plain,(
% 2.98/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.98/1.01    inference(cnf_transformation,[],[f5])).
% 2.98/1.01  
% 2.98/1.01  fof(f38,plain,(
% 2.98/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 2.98/1.01    inference(definition_unfolding,[],[f28,f37])).
% 2.98/1.01  
% 2.98/1.01  fof(f41,plain,(
% 2.98/1.01    ( ! [X0,X1] : (v1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) | ~v1_relat_1(X0)) )),
% 2.98/1.01    inference(definition_unfolding,[],[f29,f38])).
% 2.98/1.01  
% 2.98/1.01  fof(f1,axiom,(
% 2.98/1.01    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.98/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.98/1.01  
% 2.98/1.01  fof(f13,plain,(
% 2.98/1.01    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.98/1.01    inference(ennf_transformation,[],[f1])).
% 2.98/1.01  
% 2.98/1.01  fof(f24,plain,(
% 2.98/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 2.98/1.01    inference(cnf_transformation,[],[f13])).
% 2.98/1.01  
% 2.98/1.01  fof(f39,plain,(
% 2.98/1.01    ( ! [X0,X1] : (k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 2.98/1.01    inference(definition_unfolding,[],[f24,f38])).
% 2.98/1.01  
% 2.98/1.01  fof(f7,axiom,(
% 2.98/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1))),
% 2.98/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.98/1.01  
% 2.98/1.01  fof(f15,plain,(
% 2.98/1.01    ! [X0,X1,X2] : (k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2))),
% 2.98/1.01    inference(ennf_transformation,[],[f7])).
% 2.98/1.01  
% 2.98/1.01  fof(f30,plain,(
% 2.98/1.01    ( ! [X2,X0,X1] : (k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 2.98/1.01    inference(cnf_transformation,[],[f15])).
% 2.98/1.01  
% 2.98/1.01  fof(f42,plain,(
% 2.98/1.01    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) | ~v1_relat_1(X2)) )),
% 2.98/1.01    inference(definition_unfolding,[],[f30,f38])).
% 2.98/1.01  
% 2.98/1.01  fof(f36,plain,(
% 2.98/1.01    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0))),
% 2.98/1.01    inference(cnf_transformation,[],[f23])).
% 2.98/1.01  
% 2.98/1.01  fof(f43,plain,(
% 2.98/1.01    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k1_setfam_1(k2_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),sK0)))),
% 2.98/1.01    inference(definition_unfolding,[],[f36,f38])).
% 2.98/1.01  
% 2.98/1.01  cnf(c_9,negated_conjecture,
% 2.98/1.01      ( v1_relat_1(sK1) ),
% 2.98/1.01      inference(cnf_transformation,[],[f35]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_102,negated_conjecture,
% 2.98/1.01      ( v1_relat_1(sK1) ),
% 2.98/1.01      inference(subtyping,[status(esa)],[c_9]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_302,plain,
% 2.98/1.01      ( v1_relat_1(sK1) = iProver_top ),
% 2.98/1.01      inference(predicate_to_equality,[status(thm)],[c_102]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_6,plain,
% 2.98/1.01      ( r1_tarski(k7_relat_1(X0,X1),X0) | ~ v1_relat_1(X0) ),
% 2.98/1.01      inference(cnf_transformation,[],[f33]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_105,plain,
% 2.98/1.01      ( r1_tarski(k7_relat_1(X0_37,X1_37),X0_37) | ~ v1_relat_1(X0_37) ),
% 2.98/1.01      inference(subtyping,[status(esa)],[c_6]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_300,plain,
% 2.98/1.01      ( r1_tarski(k7_relat_1(X0_37,X1_37),X0_37) = iProver_top
% 2.98/1.01      | v1_relat_1(X0_37) != iProver_top ),
% 2.98/1.01      inference(predicate_to_equality,[status(thm)],[c_105]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_5,plain,
% 2.98/1.01      ( ~ r1_tarski(X0,X1)
% 2.98/1.01      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
% 2.98/1.01      | ~ v1_relat_1(X0)
% 2.98/1.01      | ~ v1_relat_1(X1) ),
% 2.98/1.01      inference(cnf_transformation,[],[f31]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_106,plain,
% 2.98/1.01      ( ~ r1_tarski(X0_37,X1_37)
% 2.98/1.01      | r1_tarski(k1_relat_1(X0_37),k1_relat_1(X1_37))
% 2.98/1.01      | ~ v1_relat_1(X0_37)
% 2.98/1.01      | ~ v1_relat_1(X1_37) ),
% 2.98/1.01      inference(subtyping,[status(esa)],[c_5]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_299,plain,
% 2.98/1.01      ( r1_tarski(X0_37,X1_37) != iProver_top
% 2.98/1.01      | r1_tarski(k1_relat_1(X0_37),k1_relat_1(X1_37)) = iProver_top
% 2.98/1.01      | v1_relat_1(X0_37) != iProver_top
% 2.98/1.01      | v1_relat_1(X1_37) != iProver_top ),
% 2.98/1.01      inference(predicate_to_equality,[status(thm)],[c_106]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_7,plain,
% 2.98/1.01      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 2.98/1.01      | ~ v1_relat_1(X0)
% 2.98/1.01      | k7_relat_1(X0,X1) = X0 ),
% 2.98/1.01      inference(cnf_transformation,[],[f34]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_104,plain,
% 2.98/1.01      ( ~ r1_tarski(k1_relat_1(X0_37),X1_37)
% 2.98/1.01      | ~ v1_relat_1(X0_37)
% 2.98/1.01      | k7_relat_1(X0_37,X1_37) = X0_37 ),
% 2.98/1.01      inference(subtyping,[status(esa)],[c_7]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_301,plain,
% 2.98/1.01      ( k7_relat_1(X0_37,X1_37) = X0_37
% 2.98/1.01      | r1_tarski(k1_relat_1(X0_37),X1_37) != iProver_top
% 2.98/1.01      | v1_relat_1(X0_37) != iProver_top ),
% 2.98/1.01      inference(predicate_to_equality,[status(thm)],[c_104]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_731,plain,
% 2.98/1.01      ( k7_relat_1(X0_37,k1_relat_1(X1_37)) = X0_37
% 2.98/1.01      | r1_tarski(X0_37,X1_37) != iProver_top
% 2.98/1.01      | v1_relat_1(X0_37) != iProver_top
% 2.98/1.01      | v1_relat_1(X1_37) != iProver_top ),
% 2.98/1.01      inference(superposition,[status(thm)],[c_299,c_301]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_118,plain,
% 2.98/1.01      ( X0_38 != X1_38 | k1_setfam_1(X0_38) = k1_setfam_1(X1_38) ),
% 2.98/1.01      theory(equality) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_120,plain,
% 2.98/1.01      ( ~ v1_relat_1(X0_37) | v1_relat_1(X1_37) | X1_37 != X0_37 ),
% 2.98/1.01      theory(equality) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_385,plain,
% 2.98/1.01      ( ~ v1_relat_1(k1_setfam_1(X0_38))
% 2.98/1.01      | v1_relat_1(k1_setfam_1(X1_38))
% 2.98/1.01      | X1_38 != X0_38 ),
% 2.98/1.01      inference(resolution,[status(thm)],[c_118,c_120]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_1,plain,
% 2.98/1.01      ( k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
% 2.98/1.01      inference(cnf_transformation,[],[f40]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_110,plain,
% 2.98/1.01      ( k2_enumset1(X0_37,X0_37,X0_37,X1_37) = k2_enumset1(X1_37,X1_37,X1_37,X0_37) ),
% 2.98/1.01      inference(subtyping,[status(esa)],[c_1]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_447,plain,
% 2.98/1.01      ( ~ v1_relat_1(k1_setfam_1(k2_enumset1(X0_37,X0_37,X0_37,X1_37)))
% 2.98/1.01      | v1_relat_1(k1_setfam_1(k2_enumset1(X1_37,X1_37,X1_37,X0_37))) ),
% 2.98/1.01      inference(resolution,[status(thm)],[c_385,c_110]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_2,plain,
% 2.98/1.01      ( ~ v1_relat_1(X0) | v1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ),
% 2.98/1.01      inference(cnf_transformation,[],[f41]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_109,plain,
% 2.98/1.01      ( ~ v1_relat_1(X0_37)
% 2.98/1.01      | v1_relat_1(k1_setfam_1(k2_enumset1(X0_37,X0_37,X0_37,X1_37))) ),
% 2.98/1.01      inference(subtyping,[status(esa)],[c_2]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_2044,plain,
% 2.98/1.01      ( ~ v1_relat_1(X0_37)
% 2.98/1.01      | v1_relat_1(k1_setfam_1(k2_enumset1(X1_37,X1_37,X1_37,X0_37))) ),
% 2.98/1.01      inference(resolution,[status(thm)],[c_447,c_109]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_115,plain,
% 2.98/1.01      ( X0_37 != X1_37 | X2_37 != X1_37 | X2_37 = X0_37 ),
% 2.98/1.01      theory(equality) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_113,plain,( X0_37 = X0_37 ),theory(equality) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_623,plain,
% 2.98/1.01      ( X0_37 != X1_37 | X1_37 = X0_37 ),
% 2.98/1.01      inference(resolution,[status(thm)],[c_115,c_113]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_0,plain,
% 2.98/1.01      ( ~ r1_tarski(X0,X1) | k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X0 ),
% 2.98/1.01      inference(cnf_transformation,[],[f39]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_111,plain,
% 2.98/1.01      ( ~ r1_tarski(X0_37,X1_37)
% 2.98/1.01      | k1_setfam_1(k2_enumset1(X0_37,X0_37,X0_37,X1_37)) = X0_37 ),
% 2.98/1.01      inference(subtyping,[status(esa)],[c_0]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_879,plain,
% 2.98/1.01      ( ~ r1_tarski(X0_37,X1_37)
% 2.98/1.01      | X0_37 = k1_setfam_1(k2_enumset1(X0_37,X0_37,X0_37,X1_37)) ),
% 2.98/1.01      inference(resolution,[status(thm)],[c_623,c_111]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_1209,plain,
% 2.98/1.01      ( ~ r1_tarski(X0_37,X1_37)
% 2.98/1.01      | v1_relat_1(X0_37)
% 2.98/1.01      | ~ v1_relat_1(k1_setfam_1(k2_enumset1(X0_37,X0_37,X0_37,X1_37))) ),
% 2.98/1.01      inference(resolution,[status(thm)],[c_879,c_120]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_2166,plain,
% 2.98/1.01      ( ~ r1_tarski(X0_37,X1_37) | ~ v1_relat_1(X1_37) | v1_relat_1(X0_37) ),
% 2.98/1.01      inference(resolution,[status(thm)],[c_2044,c_1209]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_2168,plain,
% 2.98/1.01      ( r1_tarski(X0_37,X1_37) != iProver_top
% 2.98/1.01      | v1_relat_1(X1_37) != iProver_top
% 2.98/1.01      | v1_relat_1(X0_37) = iProver_top ),
% 2.98/1.01      inference(predicate_to_equality,[status(thm)],[c_2166]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_2898,plain,
% 2.98/1.01      ( r1_tarski(X0_37,X1_37) != iProver_top
% 2.98/1.01      | k7_relat_1(X0_37,k1_relat_1(X1_37)) = X0_37
% 2.98/1.01      | v1_relat_1(X1_37) != iProver_top ),
% 2.98/1.01      inference(global_propositional_subsumption,[status(thm)],[c_731,c_2168]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_2899,plain,
% 2.98/1.01      ( k7_relat_1(X0_37,k1_relat_1(X1_37)) = X0_37
% 2.98/1.01      | r1_tarski(X0_37,X1_37) != iProver_top
% 2.98/1.01      | v1_relat_1(X1_37) != iProver_top ),
% 2.98/1.01      inference(renaming,[status(thm)],[c_2898]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_2902,plain,
% 2.98/1.01      ( k7_relat_1(k7_relat_1(X0_37,X1_37),k1_relat_1(X0_37)) = k7_relat_1(X0_37,X1_37)
% 2.98/1.01      | v1_relat_1(X0_37) != iProver_top ),
% 2.98/1.01      inference(superposition,[status(thm)],[c_300,c_2899]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_3213,plain,
% 2.98/1.01      ( k7_relat_1(k7_relat_1(sK1,X0_37),k1_relat_1(sK1)) = k7_relat_1(sK1,X0_37) ),
% 2.98/1.01      inference(superposition,[status(thm)],[c_302,c_2902]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_3,plain,
% 2.98/1.01      ( ~ v1_relat_1(X0)
% 2.98/1.01      | k7_relat_1(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) = k7_relat_1(k7_relat_1(X0,X1),X2) ),
% 2.98/1.01      inference(cnf_transformation,[],[f42]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_108,plain,
% 2.98/1.01      ( ~ v1_relat_1(X0_37)
% 2.98/1.01      | k7_relat_1(X0_37,k1_setfam_1(k2_enumset1(X1_37,X1_37,X1_37,X2_37))) = k7_relat_1(k7_relat_1(X0_37,X1_37),X2_37) ),
% 2.98/1.01      inference(subtyping,[status(esa)],[c_3]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_297,plain,
% 2.98/1.01      ( k7_relat_1(X0_37,k1_setfam_1(k2_enumset1(X1_37,X1_37,X1_37,X2_37))) = k7_relat_1(k7_relat_1(X0_37,X1_37),X2_37)
% 2.98/1.01      | v1_relat_1(X0_37) != iProver_top ),
% 2.98/1.01      inference(predicate_to_equality,[status(thm)],[c_108]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_605,plain,
% 2.98/1.01      ( k7_relat_1(sK1,k1_setfam_1(k2_enumset1(X0_37,X0_37,X0_37,X1_37))) = k7_relat_1(k7_relat_1(sK1,X0_37),X1_37) ),
% 2.98/1.01      inference(superposition,[status(thm)],[c_302,c_297]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_8,negated_conjecture,
% 2.98/1.01      ( k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k1_setfam_1(k2_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),sK0))) ),
% 2.98/1.01      inference(cnf_transformation,[],[f43]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_103,negated_conjecture,
% 2.98/1.01      ( k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k1_setfam_1(k2_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),sK0))) ),
% 2.98/1.01      inference(subtyping,[status(esa)],[c_8]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_329,plain,
% 2.98/1.01      ( k7_relat_1(sK1,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,k1_relat_1(sK1)))) != k7_relat_1(sK1,sK0) ),
% 2.98/1.01      inference(superposition,[status(thm)],[c_110,c_103]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_871,plain,
% 2.98/1.01      ( k7_relat_1(k7_relat_1(sK1,sK0),k1_relat_1(sK1)) != k7_relat_1(sK1,sK0) ),
% 2.98/1.01      inference(superposition,[status(thm)],[c_605,c_329]) ).
% 2.98/1.01  
% 2.98/1.01  cnf(c_3250,plain,
% 2.98/1.01      ( $false ),
% 2.98/1.01      inference(superposition,[status(thm)],[c_3213,c_871]) ).
% 2.98/1.01  
% 2.98/1.01  
% 2.98/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.98/1.01  
% 2.98/1.01  ------                               Statistics
% 2.98/1.01  
% 2.98/1.01  ------ Selected
% 2.98/1.01  
% 2.98/1.01  total_time:                             0.215
% 2.98/1.01  
%------------------------------------------------------------------------------
