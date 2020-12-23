%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:51:59 EST 2020

% Result     : Theorem 11.80s
% Output     : CNFRefutation 11.80s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 144 expanded)
%              Number of clauses        :   40 (  51 expanded)
%              Number of leaves         :   11 (  32 expanded)
%              Depth                    :   20
%              Number of atoms          :  163 ( 319 expanded)
%              Number of equality atoms :   31 (  54 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f23,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f23])).

fof(f37,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f42,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k4_xboole_0(k9_relat_1(sK2,sK0),k4_xboole_0(k9_relat_1(sK2,sK0),sK1))) ),
    inference(definition_unfolding,[],[f37,f29,f29])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f26,f29])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f39,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f25,f29,f29])).

fof(f35,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f36,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_7,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k4_xboole_0(k9_relat_1(sK2,sK0),k4_xboole_0(k9_relat_1(sK2,sK0),sK1))) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_80,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k4_xboole_0(k9_relat_1(sK2,sK0),k4_xboole_0(k9_relat_1(sK2,sK0),sK1))) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_86,plain,
    ( ~ r1_tarski(X0_40,X1_40)
    | ~ r1_tarski(X0_40,X2_40)
    | r1_tarski(X0_40,k4_xboole_0(X2_40,k4_xboole_0(X2_40,X1_40))) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1949,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k9_relat_1(sK2,sK0))
    | ~ r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),sK1) ),
    inference(resolution,[status(thm)],[c_80,c_86])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_82,plain,
    ( ~ r1_tarski(X0_40,X1_40)
    | r1_tarski(k9_relat_1(X0_39,X0_40),k9_relat_1(X0_39,X1_40))
    | ~ v1_relat_1(X0_39) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_234,plain,
    ( r1_tarski(X0_40,X1_40) != iProver_top
    | r1_tarski(k9_relat_1(X0_39,X0_40),k9_relat_1(X0_39,X1_40)) = iProver_top
    | v1_relat_1(X0_39) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_82])).

cnf(c_231,plain,
    ( r1_tarski(X0_40,X1_40) != iProver_top
    | r1_tarski(X0_40,X2_40) != iProver_top
    | r1_tarski(X0_40,k4_xboole_0(X2_40,k4_xboole_0(X2_40,X1_40))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_86])).

cnf(c_0,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_87,plain,
    ( k4_xboole_0(X0_40,k4_xboole_0(X0_40,X1_40)) = k4_xboole_0(X1_40,k4_xboole_0(X1_40,X0_40)) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_236,plain,
    ( r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k4_xboole_0(k9_relat_1(sK2,sK0),k4_xboole_0(k9_relat_1(sK2,sK0),sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_80])).

cnf(c_600,plain,
    ( r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k4_xboole_0(sK1,k4_xboole_0(sK1,k9_relat_1(sK2,sK0)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_87,c_236])).

cnf(c_1105,plain,
    ( r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k9_relat_1(sK2,sK0)) != iProver_top
    | r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_231,c_600])).

cnf(c_3027,plain,
    ( r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),sK1) != iProver_top
    | r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1))),sK0) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_234,c_1105])).

cnf(c_9,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_10,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4175,plain,
    ( r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1))),sK0) != iProver_top
    | r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3027,c_10])).

cnf(c_4176,plain,
    ( r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),sK1) != iProver_top
    | r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1))),sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4175])).

cnf(c_3,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_84,plain,
    ( r1_tarski(k4_xboole_0(X0_40,X1_40),X0_40) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_233,plain,
    ( r1_tarski(k4_xboole_0(X0_40,X1_40),X0_40) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_84])).

cnf(c_4181,plain,
    ( r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),sK1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4176,c_233])).

cnf(c_4182,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),sK1) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4181])).

cnf(c_47693,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1949,c_4182])).

cnf(c_6,plain,
    ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_81,plain,
    ( r1_tarski(k9_relat_1(X0_39,k10_relat_1(X0_39,X0_40)),X0_40)
    | ~ v1_funct_1(X0_39)
    | ~ v1_relat_1(X0_39) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_85,plain,
    ( ~ r1_tarski(X0_40,X1_40)
    | ~ r1_tarski(X1_40,X2_40)
    | r1_tarski(X0_40,X2_40) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_632,plain,
    ( r1_tarski(X0_40,X1_40)
    | ~ r1_tarski(X0_40,k9_relat_1(X0_39,k10_relat_1(X0_39,X1_40)))
    | ~ v1_funct_1(X0_39)
    | ~ v1_relat_1(X0_39) ),
    inference(resolution,[status(thm)],[c_81,c_85])).

cnf(c_14549,plain,
    ( ~ r1_tarski(X0_40,k10_relat_1(X0_39,X1_40))
    | r1_tarski(k9_relat_1(X0_39,X0_40),X1_40)
    | ~ v1_funct_1(X0_39)
    | ~ v1_relat_1(X0_39) ),
    inference(resolution,[status(thm)],[c_632,c_82])).

cnf(c_47705,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1))),k10_relat_1(sK2,sK1))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[status(thm)],[c_47693,c_14549])).

cnf(c_8,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_50290,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1))),k10_relat_1(sK2,sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_47705,c_9,c_8])).

cnf(c_93,plain,
    ( ~ r1_tarski(X0_40,X1_40)
    | r1_tarski(X2_40,X3_40)
    | X2_40 != X0_40
    | X3_40 != X1_40 ),
    theory(equality)).

cnf(c_89,plain,
    ( X0_40 = X0_40 ),
    theory(equality)).

cnf(c_1567,plain,
    ( ~ r1_tarski(X0_40,X1_40)
    | r1_tarski(X2_40,X1_40)
    | X2_40 != X0_40 ),
    inference(resolution,[status(thm)],[c_93,c_89])).

cnf(c_1587,plain,
    ( ~ r1_tarski(k4_xboole_0(X0_40,k4_xboole_0(X0_40,X1_40)),X2_40)
    | r1_tarski(k4_xboole_0(X1_40,k4_xboole_0(X1_40,X0_40)),X2_40) ),
    inference(resolution,[status(thm)],[c_1567,c_87])).

cnf(c_3061,plain,
    ( r1_tarski(k4_xboole_0(X0_40,k4_xboole_0(X0_40,X1_40)),X1_40) ),
    inference(resolution,[status(thm)],[c_1587,c_84])).

cnf(c_50295,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_50290,c_3061])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:40:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 11.80/1.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.80/1.98  
% 11.80/1.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.80/1.98  
% 11.80/1.98  ------  iProver source info
% 11.80/1.98  
% 11.80/1.98  git: date: 2020-06-30 10:37:57 +0100
% 11.80/1.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.80/1.98  git: non_committed_changes: false
% 11.80/1.98  git: last_make_outside_of_git: false
% 11.80/1.98  
% 11.80/1.98  ------ 
% 11.80/1.98  ------ Parsing...
% 11.80/1.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.80/1.98  
% 11.80/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 11.80/1.98  
% 11.80/1.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.80/1.98  
% 11.80/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.80/1.98  ------ Proving...
% 11.80/1.98  ------ Problem Properties 
% 11.80/1.98  
% 11.80/1.98  
% 11.80/1.98  clauses                                 10
% 11.80/1.98  conjectures                             3
% 11.80/1.98  EPR                                     3
% 11.80/1.98  Horn                                    10
% 11.80/1.98  unary                                   6
% 11.80/1.98  binary                                  0
% 11.80/1.98  lits                                    18
% 11.80/1.98  lits eq                                 2
% 11.80/1.98  fd_pure                                 0
% 11.80/1.98  fd_pseudo                               0
% 11.80/1.98  fd_cond                                 0
% 11.80/1.98  fd_pseudo_cond                          0
% 11.80/1.98  AC symbols                              0
% 11.80/1.98  
% 11.80/1.98  ------ Input Options Time Limit: Unbounded
% 11.80/1.98  
% 11.80/1.98  
% 11.80/1.98  ------ 
% 11.80/1.98  Current options:
% 11.80/1.98  ------ 
% 11.80/1.98  
% 11.80/1.98  
% 11.80/1.98  
% 11.80/1.98  
% 11.80/1.98  ------ Proving...
% 11.80/1.98  
% 11.80/1.98  
% 11.80/1.98  % SZS status Theorem for theBenchmark.p
% 11.80/1.98  
% 11.80/1.98   Resolution empty clause
% 11.80/1.98  
% 11.80/1.98  % SZS output start CNFRefutation for theBenchmark.p
% 11.80/1.98  
% 11.80/1.98  fof(f11,conjecture,(
% 11.80/1.98    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)))),
% 11.80/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.80/1.98  
% 11.80/1.98  fof(f12,negated_conjecture,(
% 11.80/1.98    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)))),
% 11.80/1.98    inference(negated_conjecture,[],[f11])).
% 11.80/1.98  
% 11.80/1.98  fof(f21,plain,(
% 11.80/1.98    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 11.80/1.98    inference(ennf_transformation,[],[f12])).
% 11.80/1.98  
% 11.80/1.98  fof(f22,plain,(
% 11.80/1.98    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 11.80/1.98    inference(flattening,[],[f21])).
% 11.80/1.98  
% 11.80/1.98  fof(f23,plain,(
% 11.80/1.98    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 11.80/1.98    introduced(choice_axiom,[])).
% 11.80/1.98  
% 11.80/1.98  fof(f24,plain,(
% 11.80/1.98    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 11.80/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f23])).
% 11.80/1.98  
% 11.80/1.98  fof(f37,plain,(
% 11.80/1.98    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1))),
% 11.80/1.98    inference(cnf_transformation,[],[f24])).
% 11.80/1.98  
% 11.80/1.98  fof(f5,axiom,(
% 11.80/1.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 11.80/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.80/1.98  
% 11.80/1.98  fof(f29,plain,(
% 11.80/1.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 11.80/1.98    inference(cnf_transformation,[],[f5])).
% 11.80/1.98  
% 11.80/1.98  fof(f42,plain,(
% 11.80/1.98    ~r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k4_xboole_0(k9_relat_1(sK2,sK0),k4_xboole_0(k9_relat_1(sK2,sK0),sK1)))),
% 11.80/1.98    inference(definition_unfolding,[],[f37,f29,f29])).
% 11.80/1.98  
% 11.80/1.98  fof(f2,axiom,(
% 11.80/1.98    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 11.80/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.80/1.98  
% 11.80/1.98  fof(f13,plain,(
% 11.80/1.98    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 11.80/1.98    inference(ennf_transformation,[],[f2])).
% 11.80/1.98  
% 11.80/1.98  fof(f14,plain,(
% 11.80/1.98    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 11.80/1.98    inference(flattening,[],[f13])).
% 11.80/1.98  
% 11.80/1.98  fof(f26,plain,(
% 11.80/1.98    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 11.80/1.98    inference(cnf_transformation,[],[f14])).
% 11.80/1.98  
% 11.80/1.98  fof(f40,plain,(
% 11.80/1.98    ( ! [X2,X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 11.80/1.98    inference(definition_unfolding,[],[f26,f29])).
% 11.80/1.98  
% 11.80/1.98  fof(f9,axiom,(
% 11.80/1.98    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 11.80/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.80/1.98  
% 11.80/1.98  fof(f17,plain,(
% 11.80/1.98    ! [X0,X1,X2] : ((r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 11.80/1.98    inference(ennf_transformation,[],[f9])).
% 11.80/1.98  
% 11.80/1.98  fof(f18,plain,(
% 11.80/1.98    ! [X0,X1,X2] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 11.80/1.98    inference(flattening,[],[f17])).
% 11.80/1.98  
% 11.80/1.98  fof(f33,plain,(
% 11.80/1.98    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 11.80/1.98    inference(cnf_transformation,[],[f18])).
% 11.80/1.98  
% 11.80/1.98  fof(f1,axiom,(
% 11.80/1.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 11.80/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.80/1.98  
% 11.80/1.98  fof(f25,plain,(
% 11.80/1.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 11.80/1.98    inference(cnf_transformation,[],[f1])).
% 11.80/1.98  
% 11.80/1.98  fof(f39,plain,(
% 11.80/1.98    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 11.80/1.98    inference(definition_unfolding,[],[f25,f29,f29])).
% 11.80/1.98  
% 11.80/1.98  fof(f35,plain,(
% 11.80/1.98    v1_relat_1(sK2)),
% 11.80/1.98    inference(cnf_transformation,[],[f24])).
% 11.80/1.98  
% 11.80/1.98  fof(f4,axiom,(
% 11.80/1.98    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 11.80/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.80/1.98  
% 11.80/1.98  fof(f28,plain,(
% 11.80/1.98    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 11.80/1.98    inference(cnf_transformation,[],[f4])).
% 11.80/1.98  
% 11.80/1.98  fof(f10,axiom,(
% 11.80/1.98    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 11.80/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.80/1.98  
% 11.80/1.98  fof(f19,plain,(
% 11.80/1.98    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 11.80/1.98    inference(ennf_transformation,[],[f10])).
% 11.80/1.98  
% 11.80/1.98  fof(f20,plain,(
% 11.80/1.98    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 11.80/1.98    inference(flattening,[],[f19])).
% 11.80/1.98  
% 11.80/1.98  fof(f34,plain,(
% 11.80/1.98    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 11.80/1.98    inference(cnf_transformation,[],[f20])).
% 11.80/1.98  
% 11.80/1.98  fof(f3,axiom,(
% 11.80/1.98    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 11.80/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.80/1.98  
% 11.80/1.98  fof(f15,plain,(
% 11.80/1.98    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 11.80/1.98    inference(ennf_transformation,[],[f3])).
% 11.80/1.98  
% 11.80/1.98  fof(f16,plain,(
% 11.80/1.98    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 11.80/1.98    inference(flattening,[],[f15])).
% 11.80/1.98  
% 11.80/1.98  fof(f27,plain,(
% 11.80/1.98    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 11.80/1.98    inference(cnf_transformation,[],[f16])).
% 11.80/1.98  
% 11.80/1.98  fof(f36,plain,(
% 11.80/1.98    v1_funct_1(sK2)),
% 11.80/1.98    inference(cnf_transformation,[],[f24])).
% 11.80/1.98  
% 11.80/1.98  cnf(c_7,negated_conjecture,
% 11.80/1.98      ( ~ r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k4_xboole_0(k9_relat_1(sK2,sK0),k4_xboole_0(k9_relat_1(sK2,sK0),sK1))) ),
% 11.80/1.98      inference(cnf_transformation,[],[f42]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_80,negated_conjecture,
% 11.80/1.98      ( ~ r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k4_xboole_0(k9_relat_1(sK2,sK0),k4_xboole_0(k9_relat_1(sK2,sK0),sK1))) ),
% 11.80/1.98      inference(subtyping,[status(esa)],[c_7]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_1,plain,
% 11.80/1.98      ( ~ r1_tarski(X0,X1)
% 11.80/1.98      | ~ r1_tarski(X0,X2)
% 11.80/1.98      | r1_tarski(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
% 11.80/1.98      inference(cnf_transformation,[],[f40]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_86,plain,
% 11.80/1.98      ( ~ r1_tarski(X0_40,X1_40)
% 11.80/1.98      | ~ r1_tarski(X0_40,X2_40)
% 11.80/1.98      | r1_tarski(X0_40,k4_xboole_0(X2_40,k4_xboole_0(X2_40,X1_40))) ),
% 11.80/1.98      inference(subtyping,[status(esa)],[c_1]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_1949,plain,
% 11.80/1.98      ( ~ r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k9_relat_1(sK2,sK0))
% 11.80/1.98      | ~ r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),sK1) ),
% 11.80/1.98      inference(resolution,[status(thm)],[c_80,c_86]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_5,plain,
% 11.80/1.98      ( ~ r1_tarski(X0,X1)
% 11.80/1.98      | r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
% 11.80/1.98      | ~ v1_relat_1(X2) ),
% 11.80/1.98      inference(cnf_transformation,[],[f33]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_82,plain,
% 11.80/1.98      ( ~ r1_tarski(X0_40,X1_40)
% 11.80/1.98      | r1_tarski(k9_relat_1(X0_39,X0_40),k9_relat_1(X0_39,X1_40))
% 11.80/1.98      | ~ v1_relat_1(X0_39) ),
% 11.80/1.98      inference(subtyping,[status(esa)],[c_5]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_234,plain,
% 11.80/1.98      ( r1_tarski(X0_40,X1_40) != iProver_top
% 11.80/1.98      | r1_tarski(k9_relat_1(X0_39,X0_40),k9_relat_1(X0_39,X1_40)) = iProver_top
% 11.80/1.98      | v1_relat_1(X0_39) != iProver_top ),
% 11.80/1.98      inference(predicate_to_equality,[status(thm)],[c_82]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_231,plain,
% 11.80/1.98      ( r1_tarski(X0_40,X1_40) != iProver_top
% 11.80/1.98      | r1_tarski(X0_40,X2_40) != iProver_top
% 11.80/1.98      | r1_tarski(X0_40,k4_xboole_0(X2_40,k4_xboole_0(X2_40,X1_40))) = iProver_top ),
% 11.80/1.98      inference(predicate_to_equality,[status(thm)],[c_86]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_0,plain,
% 11.80/1.98      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 11.80/1.98      inference(cnf_transformation,[],[f39]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_87,plain,
% 11.80/1.98      ( k4_xboole_0(X0_40,k4_xboole_0(X0_40,X1_40)) = k4_xboole_0(X1_40,k4_xboole_0(X1_40,X0_40)) ),
% 11.80/1.98      inference(subtyping,[status(esa)],[c_0]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_236,plain,
% 11.80/1.98      ( r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k4_xboole_0(k9_relat_1(sK2,sK0),k4_xboole_0(k9_relat_1(sK2,sK0),sK1))) != iProver_top ),
% 11.80/1.98      inference(predicate_to_equality,[status(thm)],[c_80]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_600,plain,
% 11.80/1.98      ( r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k4_xboole_0(sK1,k4_xboole_0(sK1,k9_relat_1(sK2,sK0)))) != iProver_top ),
% 11.80/1.98      inference(demodulation,[status(thm)],[c_87,c_236]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_1105,plain,
% 11.80/1.98      ( r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k9_relat_1(sK2,sK0)) != iProver_top
% 11.80/1.98      | r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),sK1) != iProver_top ),
% 11.80/1.98      inference(superposition,[status(thm)],[c_231,c_600]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_3027,plain,
% 11.80/1.98      ( r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),sK1) != iProver_top
% 11.80/1.98      | r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1))),sK0) != iProver_top
% 11.80/1.98      | v1_relat_1(sK2) != iProver_top ),
% 11.80/1.98      inference(superposition,[status(thm)],[c_234,c_1105]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_9,negated_conjecture,
% 11.80/1.98      ( v1_relat_1(sK2) ),
% 11.80/1.98      inference(cnf_transformation,[],[f35]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_10,plain,
% 11.80/1.98      ( v1_relat_1(sK2) = iProver_top ),
% 11.80/1.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_4175,plain,
% 11.80/1.98      ( r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1))),sK0) != iProver_top
% 11.80/1.98      | r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),sK1) != iProver_top ),
% 11.80/1.98      inference(global_propositional_subsumption,[status(thm)],[c_3027,c_10]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_4176,plain,
% 11.80/1.98      ( r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),sK1) != iProver_top
% 11.80/1.98      | r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1))),sK0) != iProver_top ),
% 11.80/1.98      inference(renaming,[status(thm)],[c_4175]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_3,plain,
% 11.80/1.98      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 11.80/1.98      inference(cnf_transformation,[],[f28]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_84,plain,
% 11.80/1.98      ( r1_tarski(k4_xboole_0(X0_40,X1_40),X0_40) ),
% 11.80/1.98      inference(subtyping,[status(esa)],[c_3]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_233,plain,
% 11.80/1.98      ( r1_tarski(k4_xboole_0(X0_40,X1_40),X0_40) = iProver_top ),
% 11.80/1.98      inference(predicate_to_equality,[status(thm)],[c_84]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_4181,plain,
% 11.80/1.98      ( r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),sK1) != iProver_top ),
% 11.80/1.98      inference(forward_subsumption_resolution,[status(thm)],[c_4176,c_233]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_4182,plain,
% 11.80/1.98      ( ~ r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),sK1) ),
% 11.80/1.98      inference(predicate_to_equality_rev,[status(thm)],[c_4181]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_47693,plain,
% 11.80/1.98      ( ~ r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),sK1) ),
% 11.80/1.98      inference(global_propositional_subsumption,[status(thm)],[c_1949,c_4182]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_6,plain,
% 11.80/1.98      ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
% 11.80/1.98      | ~ v1_funct_1(X0)
% 11.80/1.98      | ~ v1_relat_1(X0) ),
% 11.80/1.98      inference(cnf_transformation,[],[f34]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_81,plain,
% 11.80/1.98      ( r1_tarski(k9_relat_1(X0_39,k10_relat_1(X0_39,X0_40)),X0_40)
% 11.80/1.98      | ~ v1_funct_1(X0_39)
% 11.80/1.98      | ~ v1_relat_1(X0_39) ),
% 11.80/1.98      inference(subtyping,[status(esa)],[c_6]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_2,plain,
% 11.80/1.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 11.80/1.98      inference(cnf_transformation,[],[f27]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_85,plain,
% 11.80/1.98      ( ~ r1_tarski(X0_40,X1_40)
% 11.80/1.98      | ~ r1_tarski(X1_40,X2_40)
% 11.80/1.98      | r1_tarski(X0_40,X2_40) ),
% 11.80/1.98      inference(subtyping,[status(esa)],[c_2]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_632,plain,
% 11.80/1.98      ( r1_tarski(X0_40,X1_40)
% 11.80/1.98      | ~ r1_tarski(X0_40,k9_relat_1(X0_39,k10_relat_1(X0_39,X1_40)))
% 11.80/1.98      | ~ v1_funct_1(X0_39)
% 11.80/1.98      | ~ v1_relat_1(X0_39) ),
% 11.80/1.98      inference(resolution,[status(thm)],[c_81,c_85]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_14549,plain,
% 11.80/1.98      ( ~ r1_tarski(X0_40,k10_relat_1(X0_39,X1_40))
% 11.80/1.98      | r1_tarski(k9_relat_1(X0_39,X0_40),X1_40)
% 11.80/1.98      | ~ v1_funct_1(X0_39)
% 11.80/1.98      | ~ v1_relat_1(X0_39) ),
% 11.80/1.98      inference(resolution,[status(thm)],[c_632,c_82]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_47705,plain,
% 11.80/1.98      ( ~ r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1))),k10_relat_1(sK2,sK1))
% 11.80/1.98      | ~ v1_funct_1(sK2)
% 11.80/1.98      | ~ v1_relat_1(sK2) ),
% 11.80/1.98      inference(resolution,[status(thm)],[c_47693,c_14549]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_8,negated_conjecture,
% 11.80/1.98      ( v1_funct_1(sK2) ),
% 11.80/1.98      inference(cnf_transformation,[],[f36]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_50290,plain,
% 11.80/1.98      ( ~ r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1))),k10_relat_1(sK2,sK1)) ),
% 11.80/1.98      inference(global_propositional_subsumption,
% 11.80/1.98                [status(thm)],
% 11.80/1.98                [c_47705,c_9,c_8]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_93,plain,
% 11.80/1.98      ( ~ r1_tarski(X0_40,X1_40)
% 11.80/1.98      | r1_tarski(X2_40,X3_40)
% 11.80/1.98      | X2_40 != X0_40
% 11.80/1.98      | X3_40 != X1_40 ),
% 11.80/1.98      theory(equality) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_89,plain,( X0_40 = X0_40 ),theory(equality) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_1567,plain,
% 11.80/1.98      ( ~ r1_tarski(X0_40,X1_40) | r1_tarski(X2_40,X1_40) | X2_40 != X0_40 ),
% 11.80/1.98      inference(resolution,[status(thm)],[c_93,c_89]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_1587,plain,
% 11.80/1.98      ( ~ r1_tarski(k4_xboole_0(X0_40,k4_xboole_0(X0_40,X1_40)),X2_40)
% 11.80/1.98      | r1_tarski(k4_xboole_0(X1_40,k4_xboole_0(X1_40,X0_40)),X2_40) ),
% 11.80/1.98      inference(resolution,[status(thm)],[c_1567,c_87]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_3061,plain,
% 11.80/1.98      ( r1_tarski(k4_xboole_0(X0_40,k4_xboole_0(X0_40,X1_40)),X1_40) ),
% 11.80/1.98      inference(resolution,[status(thm)],[c_1587,c_84]) ).
% 11.80/1.98  
% 11.80/1.98  cnf(c_50295,plain,
% 11.80/1.98      ( $false ),
% 11.80/1.98      inference(forward_subsumption_resolution,[status(thm)],[c_50290,c_3061]) ).
% 11.80/1.98  
% 11.80/1.98  
% 11.80/1.98  % SZS output end CNFRefutation for theBenchmark.p
% 11.80/1.98  
% 11.80/1.98  ------                               Statistics
% 11.80/1.98  
% 11.80/1.98  ------ Selected
% 11.80/1.98  
% 11.80/1.98  total_time:                             1.48
% 11.80/1.98  
%------------------------------------------------------------------------------
