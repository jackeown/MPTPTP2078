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
% DateTime   : Thu Dec  3 11:51:59 EST 2020

% Result     : Theorem 3.40s
% Output     : CNFRefutation 3.40s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 146 expanded)
%              Number of clauses        :   41 (  51 expanded)
%              Number of leaves         :   10 (  31 expanded)
%              Depth                    :   14
%              Number of atoms          :  164 ( 304 expanded)
%              Number of equality atoms :   35 (  64 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k1_setfam_1(k2_tarski(X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f29,f31])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f38,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(definition_unfolding,[],[f26,f31,f31])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f24,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f24])).

fof(f37,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1)) ),
    inference(cnf_transformation,[],[f25])).

fof(f43,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_tarski(sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k2_tarski(k9_relat_1(sK2,sK0),sK1))) ),
    inference(definition_unfolding,[],[f37,f31,f31])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f40,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f28,f31])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f36,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f35,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X2,k1_setfam_1(k2_tarski(X0,X1))),k1_setfam_1(k2_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f32,f31,f31])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_220,plain,
    ( ~ r1_tarski(X0_38,X1_38)
    | ~ r1_tarski(X0_38,X2_38)
    | r1_tarski(X0_38,k1_setfam_1(k2_tarski(X1_38,X2_38))) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_385,plain,
    ( r1_tarski(X0_38,X1_38) != iProver_top
    | r1_tarski(X0_38,X2_38) != iProver_top
    | r1_tarski(X0_38,k1_setfam_1(k2_tarski(X1_38,X2_38))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_220])).

cnf(c_0,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_223,plain,
    ( k1_setfam_1(k2_tarski(X0_38,X1_38)) = k1_setfam_1(k2_tarski(X1_38,X0_38)) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_8,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_tarski(sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k2_tarski(k9_relat_1(sK2,sK0),sK1))) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_218,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_tarski(sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k2_tarski(k9_relat_1(sK2,sK0),sK1))) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_387,plain,
    ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_tarski(sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k2_tarski(k9_relat_1(sK2,sK0),sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_218])).

cnf(c_684,plain,
    ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_tarski(sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k2_tarski(sK1,k9_relat_1(sK2,sK0)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_223,c_387])).

cnf(c_1612,plain,
    ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_tarski(sK0,k10_relat_1(sK2,sK1)))),k9_relat_1(sK2,sK0)) != iProver_top
    | r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_tarski(sK0,k10_relat_1(sK2,sK1)))),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_385,c_684])).

cnf(c_2,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_221,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X0_38,X1_38)),X0_38) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_384,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X0_38,X1_38)),X0_38) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_221])).

cnf(c_689,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X0_38,X1_38)),X1_38) = iProver_top ),
    inference(superposition,[status(thm)],[c_223,c_384])).

cnf(c_7,plain,
    ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_9,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_114,plain,
    ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
    | ~ v1_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_9])).

cnf(c_115,plain,
    ( r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X0)),X0)
    | ~ v1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_114])).

cnf(c_10,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_119,plain,
    ( r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X0)),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_115,c_10])).

cnf(c_217,plain,
    ( r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X0_38)),X0_38) ),
    inference(subtyping,[status(esa)],[c_119])).

cnf(c_388,plain,
    ( r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X0_38)),X0_38) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_217])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_131,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_10])).

cnf(c_132,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) ),
    inference(unflattening,[status(thm)],[c_131])).

cnf(c_216,plain,
    ( ~ r1_tarski(X0_38,X1_38)
    | r1_tarski(k9_relat_1(sK2,X0_38),k9_relat_1(sK2,X1_38)) ),
    inference(subtyping,[status(esa)],[c_132])).

cnf(c_389,plain,
    ( r1_tarski(X0_38,X1_38) != iProver_top
    | r1_tarski(k9_relat_1(sK2,X0_38),k9_relat_1(sK2,X1_38)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_216])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_219,plain,
    ( ~ r1_tarski(X0_38,X1_38)
    | ~ r1_tarski(X1_38,X2_38)
    | r1_tarski(X0_38,X2_38) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_386,plain,
    ( r1_tarski(X0_38,X1_38) != iProver_top
    | r1_tarski(X1_38,X2_38) != iProver_top
    | r1_tarski(X0_38,X2_38) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_219])).

cnf(c_1243,plain,
    ( r1_tarski(X0_38,X1_38) != iProver_top
    | r1_tarski(k9_relat_1(sK2,X1_38),X2_38) != iProver_top
    | r1_tarski(k9_relat_1(sK2,X0_38),X2_38) = iProver_top ),
    inference(superposition,[status(thm)],[c_389,c_386])).

cnf(c_1796,plain,
    ( r1_tarski(X0_38,k10_relat_1(sK2,X1_38)) != iProver_top
    | r1_tarski(k9_relat_1(sK2,X0_38),X1_38) = iProver_top ),
    inference(superposition,[status(thm)],[c_388,c_1243])).

cnf(c_1851,plain,
    ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_tarski(X0_38,k10_relat_1(sK2,X1_38)))),X1_38) = iProver_top ),
    inference(superposition,[status(thm)],[c_689,c_1796])).

cnf(c_5,plain,
    ( r1_tarski(k9_relat_1(X0,k1_setfam_1(k2_tarski(X1,X2))),k1_setfam_1(k2_tarski(k9_relat_1(X0,X1),k9_relat_1(X0,X2))))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_143,plain,
    ( r1_tarski(k9_relat_1(X0,k1_setfam_1(k2_tarski(X1,X2))),k1_setfam_1(k2_tarski(k9_relat_1(X0,X1),k9_relat_1(X0,X2))))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_10])).

cnf(c_144,plain,
    ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_tarski(X0,X1))),k1_setfam_1(k2_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)))) ),
    inference(unflattening,[status(thm)],[c_143])).

cnf(c_215,plain,
    ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_tarski(X0_38,X1_38))),k1_setfam_1(k2_tarski(k9_relat_1(sK2,X0_38),k9_relat_1(sK2,X1_38)))) ),
    inference(subtyping,[status(esa)],[c_144])).

cnf(c_390,plain,
    ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_tarski(X0_38,X1_38))),k1_setfam_1(k2_tarski(k9_relat_1(sK2,X0_38),k9_relat_1(sK2,X1_38)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_215])).

cnf(c_1242,plain,
    ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_tarski(X0_38,X1_38))),X2_38) = iProver_top
    | r1_tarski(k1_setfam_1(k2_tarski(k9_relat_1(sK2,X0_38),k9_relat_1(sK2,X1_38))),X2_38) != iProver_top ),
    inference(superposition,[status(thm)],[c_390,c_386])).

cnf(c_3034,plain,
    ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_tarski(X0_38,X1_38))),k9_relat_1(sK2,X0_38)) = iProver_top ),
    inference(superposition,[status(thm)],[c_384,c_1242])).

cnf(c_5853,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1612,c_1851,c_3034])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:43:56 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.40/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.40/0.98  
% 3.40/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.40/0.98  
% 3.40/0.98  ------  iProver source info
% 3.40/0.98  
% 3.40/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.40/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.40/0.98  git: non_committed_changes: false
% 3.40/0.98  git: last_make_outside_of_git: false
% 3.40/0.98  
% 3.40/0.98  ------ 
% 3.40/0.98  
% 3.40/0.98  ------ Input Options
% 3.40/0.98  
% 3.40/0.98  --out_options                           all
% 3.40/0.98  --tptp_safe_out                         true
% 3.40/0.98  --problem_path                          ""
% 3.40/0.98  --include_path                          ""
% 3.40/0.98  --clausifier                            res/vclausify_rel
% 3.40/0.98  --clausifier_options                    --mode clausify
% 3.40/0.98  --stdin                                 false
% 3.40/0.98  --stats_out                             all
% 3.40/0.98  
% 3.40/0.98  ------ General Options
% 3.40/0.98  
% 3.40/0.98  --fof                                   false
% 3.40/0.98  --time_out_real                         305.
% 3.40/0.98  --time_out_virtual                      -1.
% 3.40/0.98  --symbol_type_check                     false
% 3.40/0.98  --clausify_out                          false
% 3.40/0.98  --sig_cnt_out                           false
% 3.40/0.98  --trig_cnt_out                          false
% 3.40/0.98  --trig_cnt_out_tolerance                1.
% 3.40/0.98  --trig_cnt_out_sk_spl                   false
% 3.40/0.98  --abstr_cl_out                          false
% 3.40/0.98  
% 3.40/0.98  ------ Global Options
% 3.40/0.98  
% 3.40/0.98  --schedule                              default
% 3.40/0.98  --add_important_lit                     false
% 3.40/0.98  --prop_solver_per_cl                    1000
% 3.40/0.98  --min_unsat_core                        false
% 3.40/0.98  --soft_assumptions                      false
% 3.40/0.98  --soft_lemma_size                       3
% 3.40/0.98  --prop_impl_unit_size                   0
% 3.40/0.98  --prop_impl_unit                        []
% 3.40/0.98  --share_sel_clauses                     true
% 3.40/0.98  --reset_solvers                         false
% 3.40/0.98  --bc_imp_inh                            [conj_cone]
% 3.40/0.98  --conj_cone_tolerance                   3.
% 3.40/0.98  --extra_neg_conj                        none
% 3.40/0.98  --large_theory_mode                     true
% 3.40/0.98  --prolific_symb_bound                   200
% 3.40/0.98  --lt_threshold                          2000
% 3.40/0.98  --clause_weak_htbl                      true
% 3.40/0.98  --gc_record_bc_elim                     false
% 3.40/0.98  
% 3.40/0.98  ------ Preprocessing Options
% 3.40/0.98  
% 3.40/0.98  --preprocessing_flag                    true
% 3.40/0.98  --time_out_prep_mult                    0.1
% 3.40/0.98  --splitting_mode                        input
% 3.40/0.98  --splitting_grd                         true
% 3.40/0.98  --splitting_cvd                         false
% 3.40/0.98  --splitting_cvd_svl                     false
% 3.40/0.98  --splitting_nvd                         32
% 3.40/0.98  --sub_typing                            true
% 3.40/0.98  --prep_gs_sim                           true
% 3.40/0.98  --prep_unflatten                        true
% 3.40/0.98  --prep_res_sim                          true
% 3.40/0.98  --prep_upred                            true
% 3.40/0.98  --prep_sem_filter                       exhaustive
% 3.40/0.98  --prep_sem_filter_out                   false
% 3.40/0.98  --pred_elim                             true
% 3.40/0.98  --res_sim_input                         true
% 3.40/0.98  --eq_ax_congr_red                       true
% 3.40/0.98  --pure_diseq_elim                       true
% 3.40/0.98  --brand_transform                       false
% 3.40/0.98  --non_eq_to_eq                          false
% 3.40/0.98  --prep_def_merge                        true
% 3.40/0.98  --prep_def_merge_prop_impl              false
% 3.40/0.98  --prep_def_merge_mbd                    true
% 3.40/0.98  --prep_def_merge_tr_red                 false
% 3.40/0.98  --prep_def_merge_tr_cl                  false
% 3.40/0.98  --smt_preprocessing                     true
% 3.40/0.98  --smt_ac_axioms                         fast
% 3.40/0.98  --preprocessed_out                      false
% 3.40/0.98  --preprocessed_stats                    false
% 3.40/0.98  
% 3.40/0.98  ------ Abstraction refinement Options
% 3.40/0.98  
% 3.40/0.98  --abstr_ref                             []
% 3.40/0.98  --abstr_ref_prep                        false
% 3.40/0.98  --abstr_ref_until_sat                   false
% 3.40/0.98  --abstr_ref_sig_restrict                funpre
% 3.40/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.40/0.98  --abstr_ref_under                       []
% 3.40/0.98  
% 3.40/0.98  ------ SAT Options
% 3.40/0.98  
% 3.40/0.98  --sat_mode                              false
% 3.40/0.98  --sat_fm_restart_options                ""
% 3.40/0.98  --sat_gr_def                            false
% 3.40/0.98  --sat_epr_types                         true
% 3.40/0.98  --sat_non_cyclic_types                  false
% 3.40/0.98  --sat_finite_models                     false
% 3.40/0.98  --sat_fm_lemmas                         false
% 3.40/0.98  --sat_fm_prep                           false
% 3.40/0.98  --sat_fm_uc_incr                        true
% 3.40/0.98  --sat_out_model                         small
% 3.40/0.98  --sat_out_clauses                       false
% 3.40/0.98  
% 3.40/0.98  ------ QBF Options
% 3.40/0.98  
% 3.40/0.98  --qbf_mode                              false
% 3.40/0.98  --qbf_elim_univ                         false
% 3.40/0.98  --qbf_dom_inst                          none
% 3.40/0.98  --qbf_dom_pre_inst                      false
% 3.40/0.98  --qbf_sk_in                             false
% 3.40/0.98  --qbf_pred_elim                         true
% 3.40/0.98  --qbf_split                             512
% 3.40/0.98  
% 3.40/0.98  ------ BMC1 Options
% 3.40/0.98  
% 3.40/0.98  --bmc1_incremental                      false
% 3.40/0.98  --bmc1_axioms                           reachable_all
% 3.40/0.98  --bmc1_min_bound                        0
% 3.40/0.98  --bmc1_max_bound                        -1
% 3.40/0.98  --bmc1_max_bound_default                -1
% 3.40/0.98  --bmc1_symbol_reachability              true
% 3.40/0.98  --bmc1_property_lemmas                  false
% 3.40/0.98  --bmc1_k_induction                      false
% 3.40/0.98  --bmc1_non_equiv_states                 false
% 3.40/0.98  --bmc1_deadlock                         false
% 3.40/0.98  --bmc1_ucm                              false
% 3.40/0.98  --bmc1_add_unsat_core                   none
% 3.40/0.98  --bmc1_unsat_core_children              false
% 3.40/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.40/0.98  --bmc1_out_stat                         full
% 3.40/0.98  --bmc1_ground_init                      false
% 3.40/0.98  --bmc1_pre_inst_next_state              false
% 3.40/0.98  --bmc1_pre_inst_state                   false
% 3.40/0.98  --bmc1_pre_inst_reach_state             false
% 3.40/0.98  --bmc1_out_unsat_core                   false
% 3.40/0.98  --bmc1_aig_witness_out                  false
% 3.40/0.98  --bmc1_verbose                          false
% 3.40/0.98  --bmc1_dump_clauses_tptp                false
% 3.40/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.40/0.98  --bmc1_dump_file                        -
% 3.40/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.40/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.40/0.98  --bmc1_ucm_extend_mode                  1
% 3.40/0.98  --bmc1_ucm_init_mode                    2
% 3.40/0.98  --bmc1_ucm_cone_mode                    none
% 3.40/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.40/0.98  --bmc1_ucm_relax_model                  4
% 3.40/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.40/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.40/0.98  --bmc1_ucm_layered_model                none
% 3.40/0.98  --bmc1_ucm_max_lemma_size               10
% 3.40/0.98  
% 3.40/0.98  ------ AIG Options
% 3.40/0.98  
% 3.40/0.98  --aig_mode                              false
% 3.40/0.98  
% 3.40/0.98  ------ Instantiation Options
% 3.40/0.98  
% 3.40/0.98  --instantiation_flag                    true
% 3.40/0.98  --inst_sos_flag                         false
% 3.40/0.98  --inst_sos_phase                        true
% 3.40/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.40/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.40/0.98  --inst_lit_sel_side                     num_symb
% 3.40/0.98  --inst_solver_per_active                1400
% 3.40/0.98  --inst_solver_calls_frac                1.
% 3.40/0.98  --inst_passive_queue_type               priority_queues
% 3.40/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.40/0.98  --inst_passive_queues_freq              [25;2]
% 3.40/0.98  --inst_dismatching                      true
% 3.40/0.98  --inst_eager_unprocessed_to_passive     true
% 3.40/0.98  --inst_prop_sim_given                   true
% 3.40/0.98  --inst_prop_sim_new                     false
% 3.40/0.98  --inst_subs_new                         false
% 3.40/0.98  --inst_eq_res_simp                      false
% 3.40/0.98  --inst_subs_given                       false
% 3.40/0.98  --inst_orphan_elimination               true
% 3.40/0.98  --inst_learning_loop_flag               true
% 3.40/0.98  --inst_learning_start                   3000
% 3.40/0.98  --inst_learning_factor                  2
% 3.40/0.98  --inst_start_prop_sim_after_learn       3
% 3.40/0.98  --inst_sel_renew                        solver
% 3.40/0.98  --inst_lit_activity_flag                true
% 3.40/0.98  --inst_restr_to_given                   false
% 3.40/0.98  --inst_activity_threshold               500
% 3.40/0.98  --inst_out_proof                        true
% 3.40/0.98  
% 3.40/0.98  ------ Resolution Options
% 3.40/0.98  
% 3.40/0.98  --resolution_flag                       true
% 3.40/0.98  --res_lit_sel                           adaptive
% 3.40/0.98  --res_lit_sel_side                      none
% 3.40/0.98  --res_ordering                          kbo
% 3.40/0.98  --res_to_prop_solver                    active
% 3.40/0.98  --res_prop_simpl_new                    false
% 3.40/0.98  --res_prop_simpl_given                  true
% 3.40/0.98  --res_passive_queue_type                priority_queues
% 3.40/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.40/0.98  --res_passive_queues_freq               [15;5]
% 3.40/0.98  --res_forward_subs                      full
% 3.40/0.98  --res_backward_subs                     full
% 3.40/0.98  --res_forward_subs_resolution           true
% 3.40/0.98  --res_backward_subs_resolution          true
% 3.40/0.98  --res_orphan_elimination                true
% 3.40/0.98  --res_time_limit                        2.
% 3.40/0.98  --res_out_proof                         true
% 3.40/0.98  
% 3.40/0.98  ------ Superposition Options
% 3.40/0.98  
% 3.40/0.98  --superposition_flag                    true
% 3.40/0.98  --sup_passive_queue_type                priority_queues
% 3.40/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.40/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.40/0.98  --demod_completeness_check              fast
% 3.40/0.98  --demod_use_ground                      true
% 3.40/0.98  --sup_to_prop_solver                    passive
% 3.40/0.98  --sup_prop_simpl_new                    true
% 3.40/0.98  --sup_prop_simpl_given                  true
% 3.40/0.98  --sup_fun_splitting                     false
% 3.40/0.98  --sup_smt_interval                      50000
% 3.40/0.98  
% 3.40/0.98  ------ Superposition Simplification Setup
% 3.40/0.98  
% 3.40/0.98  --sup_indices_passive                   []
% 3.40/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.40/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.40/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.40/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.40/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.40/0.98  --sup_full_bw                           [BwDemod]
% 3.40/0.98  --sup_immed_triv                        [TrivRules]
% 3.40/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.40/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.40/0.98  --sup_immed_bw_main                     []
% 3.40/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.40/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.40/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.40/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.40/0.98  
% 3.40/0.98  ------ Combination Options
% 3.40/0.98  
% 3.40/0.98  --comb_res_mult                         3
% 3.40/0.98  --comb_sup_mult                         2
% 3.40/0.98  --comb_inst_mult                        10
% 3.40/0.98  
% 3.40/0.98  ------ Debug Options
% 3.40/0.98  
% 3.40/0.98  --dbg_backtrace                         false
% 3.40/0.98  --dbg_dump_prop_clauses                 false
% 3.40/0.98  --dbg_dump_prop_clauses_file            -
% 3.40/0.98  --dbg_out_stat                          false
% 3.40/0.98  ------ Parsing...
% 3.40/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.40/0.98  
% 3.40/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.40/0.98  
% 3.40/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.40/0.98  
% 3.40/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.40/0.98  ------ Proving...
% 3.40/0.98  ------ Problem Properties 
% 3.40/0.98  
% 3.40/0.98  
% 3.40/0.98  clauses                                 9
% 3.40/0.98  conjectures                             1
% 3.40/0.98  EPR                                     1
% 3.40/0.98  Horn                                    9
% 3.40/0.98  unary                                   5
% 3.40/0.98  binary                                  2
% 3.40/0.98  lits                                    15
% 3.40/0.98  lits eq                                 1
% 3.40/0.98  fd_pure                                 0
% 3.40/0.98  fd_pseudo                               0
% 3.40/0.98  fd_cond                                 0
% 3.40/0.98  fd_pseudo_cond                          0
% 3.40/0.98  AC symbols                              0
% 3.40/0.98  
% 3.40/0.98  ------ Schedule dynamic 5 is on 
% 3.40/0.98  
% 3.40/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.40/0.98  
% 3.40/0.98  
% 3.40/0.98  ------ 
% 3.40/0.98  Current options:
% 3.40/0.98  ------ 
% 3.40/0.98  
% 3.40/0.98  ------ Input Options
% 3.40/0.98  
% 3.40/0.98  --out_options                           all
% 3.40/0.98  --tptp_safe_out                         true
% 3.40/0.98  --problem_path                          ""
% 3.40/0.98  --include_path                          ""
% 3.40/0.98  --clausifier                            res/vclausify_rel
% 3.40/0.98  --clausifier_options                    --mode clausify
% 3.40/0.98  --stdin                                 false
% 3.40/0.98  --stats_out                             all
% 3.40/0.98  
% 3.40/0.98  ------ General Options
% 3.40/0.98  
% 3.40/0.98  --fof                                   false
% 3.40/0.98  --time_out_real                         305.
% 3.40/0.98  --time_out_virtual                      -1.
% 3.40/0.98  --symbol_type_check                     false
% 3.40/0.98  --clausify_out                          false
% 3.40/0.98  --sig_cnt_out                           false
% 3.40/0.98  --trig_cnt_out                          false
% 3.40/0.98  --trig_cnt_out_tolerance                1.
% 3.40/0.98  --trig_cnt_out_sk_spl                   false
% 3.40/0.98  --abstr_cl_out                          false
% 3.40/0.98  
% 3.40/0.98  ------ Global Options
% 3.40/0.98  
% 3.40/0.98  --schedule                              default
% 3.40/0.98  --add_important_lit                     false
% 3.40/0.98  --prop_solver_per_cl                    1000
% 3.40/0.98  --min_unsat_core                        false
% 3.40/0.98  --soft_assumptions                      false
% 3.40/0.98  --soft_lemma_size                       3
% 3.40/0.98  --prop_impl_unit_size                   0
% 3.40/0.98  --prop_impl_unit                        []
% 3.40/0.98  --share_sel_clauses                     true
% 3.40/0.98  --reset_solvers                         false
% 3.40/0.98  --bc_imp_inh                            [conj_cone]
% 3.40/0.98  --conj_cone_tolerance                   3.
% 3.40/0.98  --extra_neg_conj                        none
% 3.40/0.98  --large_theory_mode                     true
% 3.40/0.98  --prolific_symb_bound                   200
% 3.40/0.98  --lt_threshold                          2000
% 3.40/0.98  --clause_weak_htbl                      true
% 3.40/0.98  --gc_record_bc_elim                     false
% 3.40/0.98  
% 3.40/0.98  ------ Preprocessing Options
% 3.40/0.98  
% 3.40/0.98  --preprocessing_flag                    true
% 3.40/0.98  --time_out_prep_mult                    0.1
% 3.40/0.98  --splitting_mode                        input
% 3.40/0.98  --splitting_grd                         true
% 3.40/0.98  --splitting_cvd                         false
% 3.40/0.98  --splitting_cvd_svl                     false
% 3.40/0.98  --splitting_nvd                         32
% 3.40/0.98  --sub_typing                            true
% 3.40/0.98  --prep_gs_sim                           true
% 3.40/0.98  --prep_unflatten                        true
% 3.40/0.98  --prep_res_sim                          true
% 3.40/0.98  --prep_upred                            true
% 3.40/0.98  --prep_sem_filter                       exhaustive
% 3.40/0.98  --prep_sem_filter_out                   false
% 3.40/0.98  --pred_elim                             true
% 3.40/0.98  --res_sim_input                         true
% 3.40/0.98  --eq_ax_congr_red                       true
% 3.40/0.98  --pure_diseq_elim                       true
% 3.40/0.98  --brand_transform                       false
% 3.40/0.98  --non_eq_to_eq                          false
% 3.40/0.98  --prep_def_merge                        true
% 3.40/0.98  --prep_def_merge_prop_impl              false
% 3.40/0.98  --prep_def_merge_mbd                    true
% 3.40/0.98  --prep_def_merge_tr_red                 false
% 3.40/0.98  --prep_def_merge_tr_cl                  false
% 3.40/0.98  --smt_preprocessing                     true
% 3.40/0.98  --smt_ac_axioms                         fast
% 3.40/0.98  --preprocessed_out                      false
% 3.40/0.98  --preprocessed_stats                    false
% 3.40/0.98  
% 3.40/0.98  ------ Abstraction refinement Options
% 3.40/0.98  
% 3.40/0.98  --abstr_ref                             []
% 3.40/0.98  --abstr_ref_prep                        false
% 3.40/0.98  --abstr_ref_until_sat                   false
% 3.40/0.98  --abstr_ref_sig_restrict                funpre
% 3.40/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.40/0.98  --abstr_ref_under                       []
% 3.40/0.98  
% 3.40/0.98  ------ SAT Options
% 3.40/0.98  
% 3.40/0.98  --sat_mode                              false
% 3.40/0.98  --sat_fm_restart_options                ""
% 3.40/0.98  --sat_gr_def                            false
% 3.40/0.98  --sat_epr_types                         true
% 3.40/0.98  --sat_non_cyclic_types                  false
% 3.40/0.98  --sat_finite_models                     false
% 3.40/0.98  --sat_fm_lemmas                         false
% 3.40/0.98  --sat_fm_prep                           false
% 3.40/0.98  --sat_fm_uc_incr                        true
% 3.40/0.98  --sat_out_model                         small
% 3.40/0.98  --sat_out_clauses                       false
% 3.40/0.98  
% 3.40/0.98  ------ QBF Options
% 3.40/0.98  
% 3.40/0.98  --qbf_mode                              false
% 3.40/0.98  --qbf_elim_univ                         false
% 3.40/0.98  --qbf_dom_inst                          none
% 3.40/0.98  --qbf_dom_pre_inst                      false
% 3.40/0.98  --qbf_sk_in                             false
% 3.40/0.98  --qbf_pred_elim                         true
% 3.40/0.98  --qbf_split                             512
% 3.40/0.98  
% 3.40/0.98  ------ BMC1 Options
% 3.40/0.98  
% 3.40/0.98  --bmc1_incremental                      false
% 3.40/0.98  --bmc1_axioms                           reachable_all
% 3.40/0.98  --bmc1_min_bound                        0
% 3.40/0.98  --bmc1_max_bound                        -1
% 3.40/0.98  --bmc1_max_bound_default                -1
% 3.40/0.98  --bmc1_symbol_reachability              true
% 3.40/0.98  --bmc1_property_lemmas                  false
% 3.40/0.98  --bmc1_k_induction                      false
% 3.40/0.98  --bmc1_non_equiv_states                 false
% 3.40/0.98  --bmc1_deadlock                         false
% 3.40/0.98  --bmc1_ucm                              false
% 3.40/0.98  --bmc1_add_unsat_core                   none
% 3.40/0.98  --bmc1_unsat_core_children              false
% 3.40/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.40/0.98  --bmc1_out_stat                         full
% 3.40/0.98  --bmc1_ground_init                      false
% 3.40/0.98  --bmc1_pre_inst_next_state              false
% 3.40/0.98  --bmc1_pre_inst_state                   false
% 3.40/0.98  --bmc1_pre_inst_reach_state             false
% 3.40/0.98  --bmc1_out_unsat_core                   false
% 3.40/0.98  --bmc1_aig_witness_out                  false
% 3.40/0.98  --bmc1_verbose                          false
% 3.40/0.98  --bmc1_dump_clauses_tptp                false
% 3.40/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.40/0.98  --bmc1_dump_file                        -
% 3.40/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.40/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.40/0.98  --bmc1_ucm_extend_mode                  1
% 3.40/0.98  --bmc1_ucm_init_mode                    2
% 3.40/0.98  --bmc1_ucm_cone_mode                    none
% 3.40/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.40/0.98  --bmc1_ucm_relax_model                  4
% 3.40/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.40/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.40/0.98  --bmc1_ucm_layered_model                none
% 3.40/0.98  --bmc1_ucm_max_lemma_size               10
% 3.40/0.98  
% 3.40/0.98  ------ AIG Options
% 3.40/0.98  
% 3.40/0.98  --aig_mode                              false
% 3.40/0.98  
% 3.40/0.98  ------ Instantiation Options
% 3.40/0.98  
% 3.40/0.98  --instantiation_flag                    true
% 3.40/0.98  --inst_sos_flag                         false
% 3.40/0.98  --inst_sos_phase                        true
% 3.40/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.40/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.40/0.98  --inst_lit_sel_side                     none
% 3.40/0.98  --inst_solver_per_active                1400
% 3.40/0.98  --inst_solver_calls_frac                1.
% 3.40/0.98  --inst_passive_queue_type               priority_queues
% 3.40/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.40/0.98  --inst_passive_queues_freq              [25;2]
% 3.40/0.98  --inst_dismatching                      true
% 3.40/0.98  --inst_eager_unprocessed_to_passive     true
% 3.40/0.98  --inst_prop_sim_given                   true
% 3.40/0.98  --inst_prop_sim_new                     false
% 3.40/0.98  --inst_subs_new                         false
% 3.40/0.98  --inst_eq_res_simp                      false
% 3.40/0.98  --inst_subs_given                       false
% 3.40/0.98  --inst_orphan_elimination               true
% 3.40/0.98  --inst_learning_loop_flag               true
% 3.40/0.98  --inst_learning_start                   3000
% 3.40/0.98  --inst_learning_factor                  2
% 3.40/0.98  --inst_start_prop_sim_after_learn       3
% 3.40/0.98  --inst_sel_renew                        solver
% 3.40/0.98  --inst_lit_activity_flag                true
% 3.40/0.98  --inst_restr_to_given                   false
% 3.40/0.98  --inst_activity_threshold               500
% 3.40/0.98  --inst_out_proof                        true
% 3.40/0.98  
% 3.40/0.98  ------ Resolution Options
% 3.40/0.98  
% 3.40/0.98  --resolution_flag                       false
% 3.40/0.98  --res_lit_sel                           adaptive
% 3.40/0.98  --res_lit_sel_side                      none
% 3.40/0.98  --res_ordering                          kbo
% 3.40/0.98  --res_to_prop_solver                    active
% 3.40/0.98  --res_prop_simpl_new                    false
% 3.40/0.98  --res_prop_simpl_given                  true
% 3.40/0.98  --res_passive_queue_type                priority_queues
% 3.40/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.40/0.98  --res_passive_queues_freq               [15;5]
% 3.40/0.98  --res_forward_subs                      full
% 3.40/0.98  --res_backward_subs                     full
% 3.40/0.98  --res_forward_subs_resolution           true
% 3.40/0.98  --res_backward_subs_resolution          true
% 3.40/0.98  --res_orphan_elimination                true
% 3.40/0.98  --res_time_limit                        2.
% 3.40/0.98  --res_out_proof                         true
% 3.40/0.98  
% 3.40/0.98  ------ Superposition Options
% 3.40/0.98  
% 3.40/0.98  --superposition_flag                    true
% 3.40/0.98  --sup_passive_queue_type                priority_queues
% 3.40/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.40/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.40/0.98  --demod_completeness_check              fast
% 3.40/0.98  --demod_use_ground                      true
% 3.40/0.98  --sup_to_prop_solver                    passive
% 3.40/0.98  --sup_prop_simpl_new                    true
% 3.40/0.98  --sup_prop_simpl_given                  true
% 3.40/0.98  --sup_fun_splitting                     false
% 3.40/0.98  --sup_smt_interval                      50000
% 3.40/0.98  
% 3.40/0.98  ------ Superposition Simplification Setup
% 3.40/0.98  
% 3.40/0.98  --sup_indices_passive                   []
% 3.40/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.40/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.40/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.40/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.40/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.40/0.98  --sup_full_bw                           [BwDemod]
% 3.40/0.98  --sup_immed_triv                        [TrivRules]
% 3.40/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.40/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.40/0.98  --sup_immed_bw_main                     []
% 3.40/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.40/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.40/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.40/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.40/0.98  
% 3.40/0.98  ------ Combination Options
% 3.40/0.98  
% 3.40/0.98  --comb_res_mult                         3
% 3.40/0.98  --comb_sup_mult                         2
% 3.40/0.98  --comb_inst_mult                        10
% 3.40/0.98  
% 3.40/0.98  ------ Debug Options
% 3.40/0.98  
% 3.40/0.98  --dbg_backtrace                         false
% 3.40/0.98  --dbg_dump_prop_clauses                 false
% 3.40/0.98  --dbg_dump_prop_clauses_file            -
% 3.40/0.98  --dbg_out_stat                          false
% 3.40/0.98  
% 3.40/0.98  
% 3.40/0.98  
% 3.40/0.98  
% 3.40/0.98  ------ Proving...
% 3.40/0.98  
% 3.40/0.98  
% 3.40/0.98  % SZS status Theorem for theBenchmark.p
% 3.40/0.98  
% 3.40/0.98   Resolution empty clause
% 3.40/0.98  
% 3.40/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.40/0.98  
% 3.40/0.98  fof(f4,axiom,(
% 3.40/0.98    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 3.40/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.40/0.98  
% 3.40/0.98  fof(f13,plain,(
% 3.40/0.98    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 3.40/0.98    inference(ennf_transformation,[],[f4])).
% 3.40/0.98  
% 3.40/0.98  fof(f14,plain,(
% 3.40/0.98    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 3.40/0.98    inference(flattening,[],[f13])).
% 3.40/0.98  
% 3.40/0.98  fof(f29,plain,(
% 3.40/0.98    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 3.40/0.98    inference(cnf_transformation,[],[f14])).
% 3.40/0.98  
% 3.40/0.98  fof(f6,axiom,(
% 3.40/0.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.40/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.40/0.98  
% 3.40/0.98  fof(f31,plain,(
% 3.40/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.40/0.98    inference(cnf_transformation,[],[f6])).
% 3.40/0.98  
% 3.40/0.98  fof(f41,plain,(
% 3.40/0.98    ( ! [X2,X0,X1] : (r1_tarski(X0,k1_setfam_1(k2_tarski(X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 3.40/0.98    inference(definition_unfolding,[],[f29,f31])).
% 3.40/0.98  
% 3.40/0.98  fof(f1,axiom,(
% 3.40/0.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.40/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.40/0.98  
% 3.40/0.98  fof(f26,plain,(
% 3.40/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.40/0.98    inference(cnf_transformation,[],[f1])).
% 3.40/0.98  
% 3.40/0.98  fof(f38,plain,(
% 3.40/0.98    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k1_setfam_1(k2_tarski(X1,X0))) )),
% 3.40/0.98    inference(definition_unfolding,[],[f26,f31,f31])).
% 3.40/0.98  
% 3.40/0.98  fof(f10,conjecture,(
% 3.40/0.98    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)))),
% 3.40/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.40/0.98  
% 3.40/0.98  fof(f11,negated_conjecture,(
% 3.40/0.98    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)))),
% 3.40/0.98    inference(negated_conjecture,[],[f10])).
% 3.40/0.98  
% 3.40/0.98  fof(f22,plain,(
% 3.40/0.98    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 3.40/0.98    inference(ennf_transformation,[],[f11])).
% 3.40/0.98  
% 3.40/0.98  fof(f23,plain,(
% 3.40/0.98    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 3.40/0.98    inference(flattening,[],[f22])).
% 3.40/0.98  
% 3.40/0.98  fof(f24,plain,(
% 3.40/0.98    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 3.40/0.98    introduced(choice_axiom,[])).
% 3.40/0.98  
% 3.40/0.98  fof(f25,plain,(
% 3.40/0.98    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 3.40/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f24])).
% 3.40/0.98  
% 3.40/0.98  fof(f37,plain,(
% 3.40/0.98    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1))),
% 3.40/0.98    inference(cnf_transformation,[],[f25])).
% 3.40/0.98  
% 3.40/0.98  fof(f43,plain,(
% 3.40/0.98    ~r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_tarski(sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k2_tarski(k9_relat_1(sK2,sK0),sK1)))),
% 3.40/0.98    inference(definition_unfolding,[],[f37,f31,f31])).
% 3.40/0.98  
% 3.40/0.98  fof(f3,axiom,(
% 3.40/0.98    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 3.40/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.40/0.98  
% 3.40/0.98  fof(f28,plain,(
% 3.40/0.98    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 3.40/0.98    inference(cnf_transformation,[],[f3])).
% 3.40/0.98  
% 3.40/0.98  fof(f40,plain,(
% 3.40/0.98    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)) )),
% 3.40/0.98    inference(definition_unfolding,[],[f28,f31])).
% 3.40/0.98  
% 3.40/0.98  fof(f9,axiom,(
% 3.40/0.98    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 3.40/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.40/0.98  
% 3.40/0.98  fof(f20,plain,(
% 3.40/0.98    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.40/0.98    inference(ennf_transformation,[],[f9])).
% 3.40/0.98  
% 3.40/0.98  fof(f21,plain,(
% 3.40/0.98    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.40/0.98    inference(flattening,[],[f20])).
% 3.40/0.98  
% 3.40/0.98  fof(f34,plain,(
% 3.40/0.98    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.40/0.98    inference(cnf_transformation,[],[f21])).
% 3.40/0.98  
% 3.40/0.98  fof(f36,plain,(
% 3.40/0.98    v1_funct_1(sK2)),
% 3.40/0.98    inference(cnf_transformation,[],[f25])).
% 3.40/0.98  
% 3.40/0.98  fof(f35,plain,(
% 3.40/0.98    v1_relat_1(sK2)),
% 3.40/0.98    inference(cnf_transformation,[],[f25])).
% 3.40/0.98  
% 3.40/0.98  fof(f8,axiom,(
% 3.40/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 3.40/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.40/0.98  
% 3.40/0.98  fof(f18,plain,(
% 3.40/0.98    ! [X0,X1,X2] : ((r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 3.40/0.98    inference(ennf_transformation,[],[f8])).
% 3.40/0.98  
% 3.40/0.98  fof(f19,plain,(
% 3.40/0.98    ! [X0,X1,X2] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 3.40/0.98    inference(flattening,[],[f18])).
% 3.40/0.98  
% 3.40/0.98  fof(f33,plain,(
% 3.40/0.98    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 3.40/0.98    inference(cnf_transformation,[],[f19])).
% 3.40/0.98  
% 3.40/0.98  fof(f5,axiom,(
% 3.40/0.98    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 3.40/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.40/0.98  
% 3.40/0.98  fof(f15,plain,(
% 3.40/0.98    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 3.40/0.98    inference(ennf_transformation,[],[f5])).
% 3.40/0.98  
% 3.40/0.98  fof(f16,plain,(
% 3.40/0.98    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 3.40/0.98    inference(flattening,[],[f15])).
% 3.40/0.98  
% 3.40/0.98  fof(f30,plain,(
% 3.40/0.98    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 3.40/0.98    inference(cnf_transformation,[],[f16])).
% 3.40/0.98  
% 3.40/0.98  fof(f7,axiom,(
% 3.40/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 3.40/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.40/0.98  
% 3.40/0.98  fof(f17,plain,(
% 3.40/0.98    ! [X0,X1,X2] : (r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) | ~v1_relat_1(X2))),
% 3.40/0.98    inference(ennf_transformation,[],[f7])).
% 3.40/0.98  
% 3.40/0.98  fof(f32,plain,(
% 3.40/0.98    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) | ~v1_relat_1(X2)) )),
% 3.40/0.98    inference(cnf_transformation,[],[f17])).
% 3.40/0.98  
% 3.40/0.98  fof(f42,plain,(
% 3.40/0.98    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X2,k1_setfam_1(k2_tarski(X0,X1))),k1_setfam_1(k2_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))) | ~v1_relat_1(X2)) )),
% 3.40/0.98    inference(definition_unfolding,[],[f32,f31,f31])).
% 3.40/0.98  
% 3.40/0.98  cnf(c_3,plain,
% 3.40/0.98      ( ~ r1_tarski(X0,X1)
% 3.40/0.98      | ~ r1_tarski(X0,X2)
% 3.40/0.98      | r1_tarski(X0,k1_setfam_1(k2_tarski(X1,X2))) ),
% 3.40/0.98      inference(cnf_transformation,[],[f41]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_220,plain,
% 3.40/0.98      ( ~ r1_tarski(X0_38,X1_38)
% 3.40/0.98      | ~ r1_tarski(X0_38,X2_38)
% 3.40/0.98      | r1_tarski(X0_38,k1_setfam_1(k2_tarski(X1_38,X2_38))) ),
% 3.40/0.98      inference(subtyping,[status(esa)],[c_3]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_385,plain,
% 3.40/0.98      ( r1_tarski(X0_38,X1_38) != iProver_top
% 3.40/0.98      | r1_tarski(X0_38,X2_38) != iProver_top
% 3.40/0.98      | r1_tarski(X0_38,k1_setfam_1(k2_tarski(X1_38,X2_38))) = iProver_top ),
% 3.40/0.98      inference(predicate_to_equality,[status(thm)],[c_220]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_0,plain,
% 3.40/0.98      ( k1_setfam_1(k2_tarski(X0,X1)) = k1_setfam_1(k2_tarski(X1,X0)) ),
% 3.40/0.98      inference(cnf_transformation,[],[f38]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_223,plain,
% 3.40/0.98      ( k1_setfam_1(k2_tarski(X0_38,X1_38)) = k1_setfam_1(k2_tarski(X1_38,X0_38)) ),
% 3.40/0.98      inference(subtyping,[status(esa)],[c_0]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_8,negated_conjecture,
% 3.40/0.98      ( ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_tarski(sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k2_tarski(k9_relat_1(sK2,sK0),sK1))) ),
% 3.40/0.98      inference(cnf_transformation,[],[f43]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_218,negated_conjecture,
% 3.40/0.98      ( ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_tarski(sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k2_tarski(k9_relat_1(sK2,sK0),sK1))) ),
% 3.40/0.98      inference(subtyping,[status(esa)],[c_8]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_387,plain,
% 3.40/0.98      ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_tarski(sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k2_tarski(k9_relat_1(sK2,sK0),sK1))) != iProver_top ),
% 3.40/0.98      inference(predicate_to_equality,[status(thm)],[c_218]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_684,plain,
% 3.40/0.98      ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_tarski(sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k2_tarski(sK1,k9_relat_1(sK2,sK0)))) != iProver_top ),
% 3.40/0.98      inference(demodulation,[status(thm)],[c_223,c_387]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_1612,plain,
% 3.40/0.98      ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_tarski(sK0,k10_relat_1(sK2,sK1)))),k9_relat_1(sK2,sK0)) != iProver_top
% 3.40/0.98      | r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_tarski(sK0,k10_relat_1(sK2,sK1)))),sK1) != iProver_top ),
% 3.40/0.98      inference(superposition,[status(thm)],[c_385,c_684]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_2,plain,
% 3.40/0.98      ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
% 3.40/0.98      inference(cnf_transformation,[],[f40]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_221,plain,
% 3.40/0.98      ( r1_tarski(k1_setfam_1(k2_tarski(X0_38,X1_38)),X0_38) ),
% 3.40/0.98      inference(subtyping,[status(esa)],[c_2]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_384,plain,
% 3.40/0.98      ( r1_tarski(k1_setfam_1(k2_tarski(X0_38,X1_38)),X0_38) = iProver_top ),
% 3.40/0.98      inference(predicate_to_equality,[status(thm)],[c_221]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_689,plain,
% 3.40/0.98      ( r1_tarski(k1_setfam_1(k2_tarski(X0_38,X1_38)),X1_38) = iProver_top ),
% 3.40/0.98      inference(superposition,[status(thm)],[c_223,c_384]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_7,plain,
% 3.40/0.98      ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
% 3.40/0.98      | ~ v1_funct_1(X0)
% 3.40/0.98      | ~ v1_relat_1(X0) ),
% 3.40/0.98      inference(cnf_transformation,[],[f34]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_9,negated_conjecture,
% 3.40/0.98      ( v1_funct_1(sK2) ),
% 3.40/0.98      inference(cnf_transformation,[],[f36]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_114,plain,
% 3.40/0.98      ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
% 3.40/0.98      | ~ v1_relat_1(X0)
% 3.40/0.98      | sK2 != X0 ),
% 3.40/0.98      inference(resolution_lifted,[status(thm)],[c_7,c_9]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_115,plain,
% 3.40/0.98      ( r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X0)),X0) | ~ v1_relat_1(sK2) ),
% 3.40/0.98      inference(unflattening,[status(thm)],[c_114]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_10,negated_conjecture,
% 3.40/0.98      ( v1_relat_1(sK2) ),
% 3.40/0.98      inference(cnf_transformation,[],[f35]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_119,plain,
% 3.40/0.98      ( r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X0)),X0) ),
% 3.40/0.98      inference(global_propositional_subsumption,[status(thm)],[c_115,c_10]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_217,plain,
% 3.40/0.98      ( r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X0_38)),X0_38) ),
% 3.40/0.98      inference(subtyping,[status(esa)],[c_119]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_388,plain,
% 3.40/0.98      ( r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X0_38)),X0_38) = iProver_top ),
% 3.40/0.98      inference(predicate_to_equality,[status(thm)],[c_217]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_6,plain,
% 3.40/0.98      ( ~ r1_tarski(X0,X1)
% 3.40/0.98      | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
% 3.40/0.98      | ~ v1_relat_1(X2) ),
% 3.40/0.98      inference(cnf_transformation,[],[f33]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_131,plain,
% 3.40/0.98      ( ~ r1_tarski(X0,X1)
% 3.40/0.98      | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
% 3.40/0.98      | sK2 != X2 ),
% 3.40/0.98      inference(resolution_lifted,[status(thm)],[c_6,c_10]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_132,plain,
% 3.40/0.98      ( ~ r1_tarski(X0,X1) | r1_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) ),
% 3.40/0.98      inference(unflattening,[status(thm)],[c_131]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_216,plain,
% 3.40/0.98      ( ~ r1_tarski(X0_38,X1_38)
% 3.40/0.98      | r1_tarski(k9_relat_1(sK2,X0_38),k9_relat_1(sK2,X1_38)) ),
% 3.40/0.98      inference(subtyping,[status(esa)],[c_132]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_389,plain,
% 3.40/0.98      ( r1_tarski(X0_38,X1_38) != iProver_top
% 3.40/0.98      | r1_tarski(k9_relat_1(sK2,X0_38),k9_relat_1(sK2,X1_38)) = iProver_top ),
% 3.40/0.98      inference(predicate_to_equality,[status(thm)],[c_216]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_4,plain,
% 3.40/0.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 3.40/0.98      inference(cnf_transformation,[],[f30]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_219,plain,
% 3.40/0.98      ( ~ r1_tarski(X0_38,X1_38)
% 3.40/0.98      | ~ r1_tarski(X1_38,X2_38)
% 3.40/0.98      | r1_tarski(X0_38,X2_38) ),
% 3.40/0.98      inference(subtyping,[status(esa)],[c_4]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_386,plain,
% 3.40/0.98      ( r1_tarski(X0_38,X1_38) != iProver_top
% 3.40/0.98      | r1_tarski(X1_38,X2_38) != iProver_top
% 3.40/0.98      | r1_tarski(X0_38,X2_38) = iProver_top ),
% 3.40/0.98      inference(predicate_to_equality,[status(thm)],[c_219]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_1243,plain,
% 3.40/0.98      ( r1_tarski(X0_38,X1_38) != iProver_top
% 3.40/0.98      | r1_tarski(k9_relat_1(sK2,X1_38),X2_38) != iProver_top
% 3.40/0.98      | r1_tarski(k9_relat_1(sK2,X0_38),X2_38) = iProver_top ),
% 3.40/0.98      inference(superposition,[status(thm)],[c_389,c_386]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_1796,plain,
% 3.40/0.98      ( r1_tarski(X0_38,k10_relat_1(sK2,X1_38)) != iProver_top
% 3.40/0.98      | r1_tarski(k9_relat_1(sK2,X0_38),X1_38) = iProver_top ),
% 3.40/0.98      inference(superposition,[status(thm)],[c_388,c_1243]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_1851,plain,
% 3.40/0.98      ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_tarski(X0_38,k10_relat_1(sK2,X1_38)))),X1_38) = iProver_top ),
% 3.40/0.98      inference(superposition,[status(thm)],[c_689,c_1796]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_5,plain,
% 3.40/0.98      ( r1_tarski(k9_relat_1(X0,k1_setfam_1(k2_tarski(X1,X2))),k1_setfam_1(k2_tarski(k9_relat_1(X0,X1),k9_relat_1(X0,X2))))
% 3.40/0.98      | ~ v1_relat_1(X0) ),
% 3.40/0.98      inference(cnf_transformation,[],[f42]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_143,plain,
% 3.40/0.98      ( r1_tarski(k9_relat_1(X0,k1_setfam_1(k2_tarski(X1,X2))),k1_setfam_1(k2_tarski(k9_relat_1(X0,X1),k9_relat_1(X0,X2))))
% 3.40/0.98      | sK2 != X0 ),
% 3.40/0.98      inference(resolution_lifted,[status(thm)],[c_5,c_10]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_144,plain,
% 3.40/0.98      ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_tarski(X0,X1))),k1_setfam_1(k2_tarski(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)))) ),
% 3.40/0.98      inference(unflattening,[status(thm)],[c_143]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_215,plain,
% 3.40/0.98      ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_tarski(X0_38,X1_38))),k1_setfam_1(k2_tarski(k9_relat_1(sK2,X0_38),k9_relat_1(sK2,X1_38)))) ),
% 3.40/0.98      inference(subtyping,[status(esa)],[c_144]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_390,plain,
% 3.40/0.98      ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_tarski(X0_38,X1_38))),k1_setfam_1(k2_tarski(k9_relat_1(sK2,X0_38),k9_relat_1(sK2,X1_38)))) = iProver_top ),
% 3.40/0.98      inference(predicate_to_equality,[status(thm)],[c_215]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_1242,plain,
% 3.40/0.98      ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_tarski(X0_38,X1_38))),X2_38) = iProver_top
% 3.40/0.98      | r1_tarski(k1_setfam_1(k2_tarski(k9_relat_1(sK2,X0_38),k9_relat_1(sK2,X1_38))),X2_38) != iProver_top ),
% 3.40/0.98      inference(superposition,[status(thm)],[c_390,c_386]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_3034,plain,
% 3.40/0.98      ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k2_tarski(X0_38,X1_38))),k9_relat_1(sK2,X0_38)) = iProver_top ),
% 3.40/0.98      inference(superposition,[status(thm)],[c_384,c_1242]) ).
% 3.40/0.98  
% 3.40/0.98  cnf(c_5853,plain,
% 3.40/0.98      ( $false ),
% 3.40/0.98      inference(forward_subsumption_resolution,
% 3.40/0.98                [status(thm)],
% 3.40/0.98                [c_1612,c_1851,c_3034]) ).
% 3.40/0.98  
% 3.40/0.98  
% 3.40/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.40/0.98  
% 3.40/0.98  ------                               Statistics
% 3.40/0.98  
% 3.40/0.98  ------ General
% 3.40/0.98  
% 3.40/0.98  abstr_ref_over_cycles:                  0
% 3.40/0.98  abstr_ref_under_cycles:                 0
% 3.40/0.98  gc_basic_clause_elim:                   0
% 3.40/0.98  forced_gc_time:                         0
% 3.40/0.98  parsing_time:                           0.008
% 3.40/0.98  unif_index_cands_time:                  0.
% 3.40/0.98  unif_index_add_time:                    0.
% 3.40/0.98  orderings_time:                         0.
% 3.40/0.98  out_proof_time:                         0.006
% 3.40/0.98  total_time:                             0.221
% 3.40/0.98  num_of_symbols:                         41
% 3.40/0.98  num_of_terms:                           9779
% 3.40/0.98  
% 3.40/0.98  ------ Preprocessing
% 3.40/0.98  
% 3.40/0.98  num_of_splits:                          0
% 3.40/0.98  num_of_split_atoms:                     0
% 3.40/0.98  num_of_reused_defs:                     0
% 3.40/0.98  num_eq_ax_congr_red:                    2
% 3.40/0.98  num_of_sem_filtered_clauses:            1
% 3.40/0.98  num_of_subtypes:                        3
% 3.40/0.98  monotx_restored_types:                  0
% 3.40/0.98  sat_num_of_epr_types:                   0
% 3.40/0.98  sat_num_of_non_cyclic_types:            0
% 3.40/0.98  sat_guarded_non_collapsed_types:        0
% 3.40/0.98  num_pure_diseq_elim:                    0
% 3.40/0.98  simp_replaced_by:                       0
% 3.40/0.98  res_preprocessed:                       55
% 3.40/0.98  prep_upred:                             0
% 3.40/0.98  prep_unflattend:                        3
% 3.40/0.98  smt_new_axioms:                         0
% 3.40/0.98  pred_elim_cands:                        1
% 3.40/0.98  pred_elim:                              2
% 3.40/0.98  pred_elim_cl:                           2
% 3.40/0.98  pred_elim_cycles:                       4
% 3.40/0.98  merged_defs:                            0
% 3.40/0.98  merged_defs_ncl:                        0
% 3.40/0.98  bin_hyper_res:                          0
% 3.40/0.98  prep_cycles:                            4
% 3.40/0.98  pred_elim_time:                         0.001
% 3.40/0.98  splitting_time:                         0.
% 3.40/0.98  sem_filter_time:                        0.
% 3.40/0.98  monotx_time:                            0.
% 3.40/0.98  subtype_inf_time:                       0.
% 3.40/0.98  
% 3.40/0.98  ------ Problem properties
% 3.40/0.98  
% 3.40/0.98  clauses:                                9
% 3.40/0.98  conjectures:                            1
% 3.40/0.98  epr:                                    1
% 3.40/0.98  horn:                                   9
% 3.40/0.98  ground:                                 1
% 3.40/0.98  unary:                                  5
% 3.40/0.98  binary:                                 2
% 3.40/0.98  lits:                                   15
% 3.40/0.98  lits_eq:                                1
% 3.40/0.99  fd_pure:                                0
% 3.40/0.99  fd_pseudo:                              0
% 3.40/0.99  fd_cond:                                0
% 3.40/0.99  fd_pseudo_cond:                         0
% 3.40/0.99  ac_symbols:                             0
% 3.40/0.99  
% 3.40/0.99  ------ Propositional Solver
% 3.40/0.99  
% 3.40/0.99  prop_solver_calls:                      27
% 3.40/0.99  prop_fast_solver_calls:                 270
% 3.40/0.99  smt_solver_calls:                       0
% 3.40/0.99  smt_fast_solver_calls:                  0
% 3.40/0.99  prop_num_of_clauses:                    2879
% 3.40/0.99  prop_preprocess_simplified:             7749
% 3.40/0.99  prop_fo_subsumed:                       1
% 3.40/0.99  prop_solver_time:                       0.
% 3.40/0.99  smt_solver_time:                        0.
% 3.40/0.99  smt_fast_solver_time:                   0.
% 3.40/0.99  prop_fast_solver_time:                  0.
% 3.40/0.99  prop_unsat_core_time:                   0.
% 3.40/0.99  
% 3.40/0.99  ------ QBF
% 3.40/0.99  
% 3.40/0.99  qbf_q_res:                              0
% 3.40/0.99  qbf_num_tautologies:                    0
% 3.40/0.99  qbf_prep_cycles:                        0
% 3.40/0.99  
% 3.40/0.99  ------ BMC1
% 3.40/0.99  
% 3.40/0.99  bmc1_current_bound:                     -1
% 3.40/0.99  bmc1_last_solved_bound:                 -1
% 3.40/0.99  bmc1_unsat_core_size:                   -1
% 3.40/0.99  bmc1_unsat_core_parents_size:           -1
% 3.40/0.99  bmc1_merge_next_fun:                    0
% 3.40/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.40/0.99  
% 3.40/0.99  ------ Instantiation
% 3.40/0.99  
% 3.40/0.99  inst_num_of_clauses:                    764
% 3.40/0.99  inst_num_in_passive:                    579
% 3.40/0.99  inst_num_in_active:                     156
% 3.40/0.99  inst_num_in_unprocessed:                29
% 3.40/0.99  inst_num_of_loops:                      170
% 3.40/0.99  inst_num_of_learning_restarts:          0
% 3.40/0.99  inst_num_moves_active_passive:          13
% 3.40/0.99  inst_lit_activity:                      0
% 3.40/0.99  inst_lit_activity_moves:                0
% 3.40/0.99  inst_num_tautologies:                   0
% 3.40/0.99  inst_num_prop_implied:                  0
% 3.40/0.99  inst_num_existing_simplified:           0
% 3.40/0.99  inst_num_eq_res_simplified:             0
% 3.40/0.99  inst_num_child_elim:                    0
% 3.40/0.99  inst_num_of_dismatching_blockings:      338
% 3.40/0.99  inst_num_of_non_proper_insts:           569
% 3.40/0.99  inst_num_of_duplicates:                 0
% 3.40/0.99  inst_inst_num_from_inst_to_res:         0
% 3.40/0.99  inst_dismatching_checking_time:         0.
% 3.40/0.99  
% 3.40/0.99  ------ Resolution
% 3.40/0.99  
% 3.40/0.99  res_num_of_clauses:                     0
% 3.40/0.99  res_num_in_passive:                     0
% 3.40/0.99  res_num_in_active:                      0
% 3.40/0.99  res_num_of_loops:                       59
% 3.40/0.99  res_forward_subset_subsumed:            18
% 3.40/0.99  res_backward_subset_subsumed:           0
% 3.40/0.99  res_forward_subsumed:                   0
% 3.40/0.99  res_backward_subsumed:                  0
% 3.40/0.99  res_forward_subsumption_resolution:     0
% 3.40/0.99  res_backward_subsumption_resolution:    0
% 3.40/0.99  res_clause_to_clause_subsumption:       617
% 3.40/0.99  res_orphan_elimination:                 0
% 3.40/0.99  res_tautology_del:                      7
% 3.40/0.99  res_num_eq_res_simplified:              0
% 3.40/0.99  res_num_sel_changes:                    0
% 3.40/0.99  res_moves_from_active_to_pass:          0
% 3.40/0.99  
% 3.40/0.99  ------ Superposition
% 3.40/0.99  
% 3.40/0.99  sup_time_total:                         0.
% 3.40/0.99  sup_time_generating:                    0.
% 3.40/0.99  sup_time_sim_full:                      0.
% 3.40/0.99  sup_time_sim_immed:                     0.
% 3.40/0.99  
% 3.40/0.99  sup_num_of_clauses:                     130
% 3.40/0.99  sup_num_in_active:                      31
% 3.40/0.99  sup_num_in_passive:                     99
% 3.40/0.99  sup_num_of_loops:                       32
% 3.40/0.99  sup_fw_superposition:                   103
% 3.40/0.99  sup_bw_superposition:                   55
% 3.40/0.99  sup_immediate_simplified:               0
% 3.40/0.99  sup_given_eliminated:                   0
% 3.40/0.99  comparisons_done:                       0
% 3.40/0.99  comparisons_avoided:                    0
% 3.40/0.99  
% 3.40/0.99  ------ Simplifications
% 3.40/0.99  
% 3.40/0.99  
% 3.40/0.99  sim_fw_subset_subsumed:                 0
% 3.40/0.99  sim_bw_subset_subsumed:                 0
% 3.40/0.99  sim_fw_subsumed:                        0
% 3.40/0.99  sim_bw_subsumed:                        0
% 3.40/0.99  sim_fw_subsumption_res:                 2
% 3.40/0.99  sim_bw_subsumption_res:                 0
% 3.40/0.99  sim_tautology_del:                      0
% 3.40/0.99  sim_eq_tautology_del:                   0
% 3.40/0.99  sim_eq_res_simp:                        0
% 3.40/0.99  sim_fw_demodulated:                     0
% 3.40/0.99  sim_bw_demodulated:                     1
% 3.40/0.99  sim_light_normalised:                   0
% 3.40/0.99  sim_joinable_taut:                      0
% 3.40/0.99  sim_joinable_simp:                      0
% 3.40/0.99  sim_ac_normalised:                      0
% 3.40/0.99  sim_smt_subsumption:                    0
% 3.40/0.99  
%------------------------------------------------------------------------------
