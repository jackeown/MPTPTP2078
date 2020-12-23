%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:52:00 EST 2020

% Result     : Theorem 3.42s
% Output     : CNFRefutation 3.42s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 126 expanded)
%              Number of clauses        :   39 (  46 expanded)
%              Number of leaves         :   10 (  29 expanded)
%              Depth                    :   12
%              Number of atoms          :  162 ( 277 expanded)
%              Number of equality atoms :   41 (  63 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ) ),
    inference(definition_unfolding,[],[f20,f22])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))) = k9_relat_1(X1,k10_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f24,f22])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f17,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f17])).

fof(f26,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f25,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f28,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f19,f22,f22])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k9_relat_1(X2,X0),k4_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f23,f22,f22])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f10])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f21,f22])).

fof(f27,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f33,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k4_xboole_0(k9_relat_1(sK2,sK0),k4_xboole_0(k9_relat_1(sK2,sK0),sK1))) ),
    inference(definition_unfolding,[],[f27,f22,f22])).

cnf(c_1,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_144,plain,
    ( r1_tarski(X0_38,X1_38)
    | ~ r1_tarski(X0_38,k4_xboole_0(X1_38,k4_xboole_0(X1_38,X2_38))) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_258,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k4_xboole_0(sK1,k4_xboole_0(sK1,X0_38)))
    | r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),sK1) ),
    inference(instantiation,[status(thm)],[c_144])).

cnf(c_5215,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k4_xboole_0(sK1,k4_xboole_0(sK1,k9_relat_1(sK2,k1_relat_1(sK2)))))
    | r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),sK1) ),
    inference(instantiation,[status(thm)],[c_258])).

cnf(c_150,plain,
    ( ~ r1_tarski(X0_38,X1_38)
    | r1_tarski(X2_38,X3_38)
    | X2_38 != X0_38
    | X3_38 != X1_38 ),
    theory(equality)).

cnf(c_302,plain,
    ( ~ r1_tarski(X0_38,X1_38)
    | r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k4_xboole_0(sK1,k4_xboole_0(sK1,X2_38)))
    | k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))) != X0_38
    | k4_xboole_0(sK1,k4_xboole_0(sK1,X2_38)) != X1_38 ),
    inference(instantiation,[status(thm)],[c_150])).

cnf(c_394,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),X0_38)
    | r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k4_xboole_0(sK1,k4_xboole_0(sK1,X1_38)))
    | k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))) != k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1))))
    | k4_xboole_0(sK1,k4_xboole_0(sK1,X1_38)) != X0_38 ),
    inference(instantiation,[status(thm)],[c_302])).

cnf(c_1631,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k9_relat_1(sK2,X0_38))
    | r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k4_xboole_0(sK1,k4_xboole_0(sK1,X1_38)))
    | k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))) != k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1))))
    | k4_xboole_0(sK1,k4_xboole_0(sK1,X1_38)) != k9_relat_1(sK2,X0_38) ),
    inference(instantiation,[status(thm)],[c_394])).

cnf(c_4031,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k9_relat_1(sK2,k10_relat_1(sK2,sK1)))
    | r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k4_xboole_0(sK1,k4_xboole_0(sK1,k9_relat_1(sK2,k1_relat_1(sK2)))))
    | k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))) != k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1))))
    | k4_xboole_0(sK1,k4_xboole_0(sK1,k9_relat_1(sK2,k1_relat_1(sK2)))) != k9_relat_1(sK2,k10_relat_1(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_1631])).

cnf(c_429,plain,
    ( r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),X0_38)
    | ~ r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k4_xboole_0(X0_38,k4_xboole_0(X0_38,X1_38))) ),
    inference(instantiation,[status(thm)],[c_144])).

cnf(c_3467,plain,
    ( r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k9_relat_1(sK2,k10_relat_1(sK2,sK1)))
    | ~ r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k4_xboole_0(k9_relat_1(sK2,k10_relat_1(sK2,sK1)),k4_xboole_0(k9_relat_1(sK2,k10_relat_1(sK2,sK1)),k9_relat_1(sK2,sK0)))) ),
    inference(instantiation,[status(thm)],[c_429])).

cnf(c_4,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k4_xboole_0(X1,k4_xboole_0(X1,k9_relat_1(X0,k1_relat_1(X0)))) = k9_relat_1(X0,k10_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_6,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_84,plain,
    ( ~ v1_relat_1(X0)
    | k4_xboole_0(X1,k4_xboole_0(X1,k9_relat_1(X0,k1_relat_1(X0)))) = k9_relat_1(X0,k10_relat_1(X0,X1))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_6])).

cnf(c_85,plain,
    ( ~ v1_relat_1(sK2)
    | k4_xboole_0(X0,k4_xboole_0(X0,k9_relat_1(sK2,k1_relat_1(sK2)))) = k9_relat_1(sK2,k10_relat_1(sK2,X0)) ),
    inference(unflattening,[status(thm)],[c_84])).

cnf(c_7,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_89,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k9_relat_1(sK2,k1_relat_1(sK2)))) = k9_relat_1(sK2,k10_relat_1(sK2,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_85,c_7])).

cnf(c_141,plain,
    ( k4_xboole_0(X0_38,k4_xboole_0(X0_38,k9_relat_1(sK2,k1_relat_1(sK2)))) = k9_relat_1(sK2,k10_relat_1(sK2,X0_38)) ),
    inference(subtyping,[status(esa)],[c_89])).

cnf(c_2362,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k9_relat_1(sK2,k1_relat_1(sK2)))) = k9_relat_1(sK2,k10_relat_1(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_141])).

cnf(c_0,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_145,plain,
    ( k4_xboole_0(X0_38,k4_xboole_0(X0_38,X1_38)) = k4_xboole_0(X1_38,k4_xboole_0(X1_38,X0_38)) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1486,plain,
    ( k4_xboole_0(k9_relat_1(sK2,k10_relat_1(sK2,sK1)),k4_xboole_0(k9_relat_1(sK2,k10_relat_1(sK2,sK1)),k9_relat_1(sK2,sK0))) = k4_xboole_0(k9_relat_1(sK2,sK0),k4_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,k10_relat_1(sK2,sK1)))) ),
    inference(instantiation,[status(thm)],[c_145])).

cnf(c_439,plain,
    ( ~ r1_tarski(X0_38,X1_38)
    | r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),X2_38)
    | X2_38 != X1_38
    | k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))) != X0_38 ),
    inference(instantiation,[status(thm)],[c_150])).

cnf(c_538,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),X0_38)
    | r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),X1_38)
    | X1_38 != X0_38
    | k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))) != k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))) ),
    inference(instantiation,[status(thm)],[c_439])).

cnf(c_965,plain,
    ( r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),X0_38)
    | ~ r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k4_xboole_0(k9_relat_1(sK2,sK0),k4_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,k10_relat_1(sK2,sK1)))))
    | X0_38 != k4_xboole_0(k9_relat_1(sK2,sK0),k4_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,k10_relat_1(sK2,sK1))))
    | k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))) != k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))) ),
    inference(instantiation,[status(thm)],[c_538])).

cnf(c_1118,plain,
    ( r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k4_xboole_0(k9_relat_1(sK2,k10_relat_1(sK2,sK1)),k4_xboole_0(k9_relat_1(sK2,k10_relat_1(sK2,sK1)),k9_relat_1(sK2,sK0))))
    | ~ r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k4_xboole_0(k9_relat_1(sK2,sK0),k4_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,k10_relat_1(sK2,sK1)))))
    | k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))) != k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1))))
    | k4_xboole_0(k9_relat_1(sK2,k10_relat_1(sK2,sK1)),k4_xboole_0(k9_relat_1(sK2,k10_relat_1(sK2,sK1)),k9_relat_1(sK2,sK0))) != k4_xboole_0(k9_relat_1(sK2,sK0),k4_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,k10_relat_1(sK2,sK1)))) ),
    inference(instantiation,[status(thm)],[c_965])).

cnf(c_497,plain,
    ( r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k9_relat_1(sK2,sK0))
    | ~ r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k4_xboole_0(k9_relat_1(sK2,sK0),k4_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,k10_relat_1(sK2,sK1))))) ),
    inference(instantiation,[status(thm)],[c_429])).

cnf(c_3,plain,
    ( r1_tarski(k9_relat_1(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))),k4_xboole_0(k9_relat_1(X0,X1),k4_xboole_0(k9_relat_1(X0,X1),k9_relat_1(X0,X2))))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_96,plain,
    ( r1_tarski(k9_relat_1(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))),k4_xboole_0(k9_relat_1(X0,X1),k4_xboole_0(k9_relat_1(X0,X1),k9_relat_1(X0,X2))))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_7])).

cnf(c_97,plain,
    ( r1_tarski(k9_relat_1(sK2,k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k9_relat_1(sK2,X0),k4_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)))) ),
    inference(unflattening,[status(thm)],[c_96])).

cnf(c_140,plain,
    ( r1_tarski(k9_relat_1(sK2,k4_xboole_0(X0_38,k4_xboole_0(X0_38,X1_38))),k4_xboole_0(k9_relat_1(sK2,X0_38),k4_xboole_0(k9_relat_1(sK2,X0_38),k9_relat_1(sK2,X1_38)))) ),
    inference(subtyping,[status(esa)],[c_97])).

cnf(c_424,plain,
    ( r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k4_xboole_0(k9_relat_1(sK2,sK0),k4_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,k10_relat_1(sK2,sK1))))) ),
    inference(instantiation,[status(thm)],[c_140])).

cnf(c_147,plain,
    ( X0_38 = X0_38 ),
    theory(equality)).

cnf(c_321,plain,
    ( k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))) = k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))) ),
    inference(instantiation,[status(thm)],[c_147])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_143,plain,
    ( ~ r1_tarski(X0_38,X1_38)
    | ~ r1_tarski(X0_38,X2_38)
    | r1_tarski(X0_38,k4_xboole_0(X2_38,k4_xboole_0(X2_38,X1_38))) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_250,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k9_relat_1(sK2,sK0))
    | r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k4_xboole_0(k9_relat_1(sK2,sK0),k4_xboole_0(k9_relat_1(sK2,sK0),sK1)))
    | ~ r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),sK1) ),
    inference(instantiation,[status(thm)],[c_143])).

cnf(c_5,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k4_xboole_0(k9_relat_1(sK2,sK0),k4_xboole_0(k9_relat_1(sK2,sK0),sK1))) ),
    inference(cnf_transformation,[],[f33])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5215,c_4031,c_3467,c_2362,c_1486,c_1118,c_497,c_424,c_321,c_250,c_5])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:01:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 3.42/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.42/1.01  
% 3.42/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.42/1.01  
% 3.42/1.01  ------  iProver source info
% 3.42/1.01  
% 3.42/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.42/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.42/1.01  git: non_committed_changes: false
% 3.42/1.01  git: last_make_outside_of_git: false
% 3.42/1.01  
% 3.42/1.01  ------ 
% 3.42/1.01  
% 3.42/1.01  ------ Input Options
% 3.42/1.01  
% 3.42/1.01  --out_options                           all
% 3.42/1.01  --tptp_safe_out                         true
% 3.42/1.01  --problem_path                          ""
% 3.42/1.01  --include_path                          ""
% 3.42/1.01  --clausifier                            res/vclausify_rel
% 3.42/1.01  --clausifier_options                    ""
% 3.42/1.01  --stdin                                 false
% 3.42/1.01  --stats_out                             all
% 3.42/1.01  
% 3.42/1.01  ------ General Options
% 3.42/1.01  
% 3.42/1.01  --fof                                   false
% 3.42/1.01  --time_out_real                         305.
% 3.42/1.01  --time_out_virtual                      -1.
% 3.42/1.01  --symbol_type_check                     false
% 3.42/1.01  --clausify_out                          false
% 3.42/1.01  --sig_cnt_out                           false
% 3.42/1.01  --trig_cnt_out                          false
% 3.42/1.01  --trig_cnt_out_tolerance                1.
% 3.42/1.01  --trig_cnt_out_sk_spl                   false
% 3.42/1.01  --abstr_cl_out                          false
% 3.42/1.01  
% 3.42/1.01  ------ Global Options
% 3.42/1.01  
% 3.42/1.01  --schedule                              default
% 3.42/1.01  --add_important_lit                     false
% 3.42/1.01  --prop_solver_per_cl                    1000
% 3.42/1.01  --min_unsat_core                        false
% 3.42/1.01  --soft_assumptions                      false
% 3.42/1.01  --soft_lemma_size                       3
% 3.42/1.01  --prop_impl_unit_size                   0
% 3.42/1.01  --prop_impl_unit                        []
% 3.42/1.01  --share_sel_clauses                     true
% 3.42/1.01  --reset_solvers                         false
% 3.42/1.01  --bc_imp_inh                            [conj_cone]
% 3.42/1.01  --conj_cone_tolerance                   3.
% 3.42/1.01  --extra_neg_conj                        none
% 3.42/1.01  --large_theory_mode                     true
% 3.42/1.01  --prolific_symb_bound                   200
% 3.42/1.01  --lt_threshold                          2000
% 3.42/1.01  --clause_weak_htbl                      true
% 3.42/1.01  --gc_record_bc_elim                     false
% 3.42/1.01  
% 3.42/1.01  ------ Preprocessing Options
% 3.42/1.01  
% 3.42/1.01  --preprocessing_flag                    true
% 3.42/1.01  --time_out_prep_mult                    0.1
% 3.42/1.01  --splitting_mode                        input
% 3.42/1.01  --splitting_grd                         true
% 3.42/1.01  --splitting_cvd                         false
% 3.42/1.01  --splitting_cvd_svl                     false
% 3.42/1.01  --splitting_nvd                         32
% 3.42/1.01  --sub_typing                            true
% 3.42/1.01  --prep_gs_sim                           true
% 3.42/1.01  --prep_unflatten                        true
% 3.42/1.01  --prep_res_sim                          true
% 3.42/1.01  --prep_upred                            true
% 3.42/1.01  --prep_sem_filter                       exhaustive
% 3.42/1.01  --prep_sem_filter_out                   false
% 3.42/1.01  --pred_elim                             true
% 3.42/1.01  --res_sim_input                         true
% 3.42/1.01  --eq_ax_congr_red                       true
% 3.42/1.01  --pure_diseq_elim                       true
% 3.42/1.01  --brand_transform                       false
% 3.42/1.01  --non_eq_to_eq                          false
% 3.42/1.01  --prep_def_merge                        true
% 3.42/1.01  --prep_def_merge_prop_impl              false
% 3.42/1.01  --prep_def_merge_mbd                    true
% 3.42/1.01  --prep_def_merge_tr_red                 false
% 3.42/1.01  --prep_def_merge_tr_cl                  false
% 3.42/1.01  --smt_preprocessing                     true
% 3.42/1.01  --smt_ac_axioms                         fast
% 3.42/1.01  --preprocessed_out                      false
% 3.42/1.01  --preprocessed_stats                    false
% 3.42/1.01  
% 3.42/1.01  ------ Abstraction refinement Options
% 3.42/1.01  
% 3.42/1.01  --abstr_ref                             []
% 3.42/1.01  --abstr_ref_prep                        false
% 3.42/1.01  --abstr_ref_until_sat                   false
% 3.42/1.01  --abstr_ref_sig_restrict                funpre
% 3.42/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.42/1.01  --abstr_ref_under                       []
% 3.42/1.01  
% 3.42/1.01  ------ SAT Options
% 3.42/1.01  
% 3.42/1.01  --sat_mode                              false
% 3.42/1.01  --sat_fm_restart_options                ""
% 3.42/1.01  --sat_gr_def                            false
% 3.42/1.01  --sat_epr_types                         true
% 3.42/1.01  --sat_non_cyclic_types                  false
% 3.42/1.01  --sat_finite_models                     false
% 3.42/1.01  --sat_fm_lemmas                         false
% 3.42/1.01  --sat_fm_prep                           false
% 3.42/1.01  --sat_fm_uc_incr                        true
% 3.42/1.01  --sat_out_model                         small
% 3.42/1.01  --sat_out_clauses                       false
% 3.42/1.01  
% 3.42/1.01  ------ QBF Options
% 3.42/1.01  
% 3.42/1.01  --qbf_mode                              false
% 3.42/1.01  --qbf_elim_univ                         false
% 3.42/1.01  --qbf_dom_inst                          none
% 3.42/1.01  --qbf_dom_pre_inst                      false
% 3.42/1.01  --qbf_sk_in                             false
% 3.42/1.01  --qbf_pred_elim                         true
% 3.42/1.01  --qbf_split                             512
% 3.42/1.01  
% 3.42/1.01  ------ BMC1 Options
% 3.42/1.01  
% 3.42/1.01  --bmc1_incremental                      false
% 3.42/1.01  --bmc1_axioms                           reachable_all
% 3.42/1.01  --bmc1_min_bound                        0
% 3.42/1.01  --bmc1_max_bound                        -1
% 3.42/1.01  --bmc1_max_bound_default                -1
% 3.42/1.01  --bmc1_symbol_reachability              true
% 3.42/1.01  --bmc1_property_lemmas                  false
% 3.42/1.01  --bmc1_k_induction                      false
% 3.42/1.01  --bmc1_non_equiv_states                 false
% 3.42/1.01  --bmc1_deadlock                         false
% 3.42/1.01  --bmc1_ucm                              false
% 3.42/1.01  --bmc1_add_unsat_core                   none
% 3.42/1.01  --bmc1_unsat_core_children              false
% 3.42/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.42/1.01  --bmc1_out_stat                         full
% 3.42/1.01  --bmc1_ground_init                      false
% 3.42/1.01  --bmc1_pre_inst_next_state              false
% 3.42/1.01  --bmc1_pre_inst_state                   false
% 3.42/1.01  --bmc1_pre_inst_reach_state             false
% 3.42/1.01  --bmc1_out_unsat_core                   false
% 3.42/1.01  --bmc1_aig_witness_out                  false
% 3.42/1.01  --bmc1_verbose                          false
% 3.42/1.01  --bmc1_dump_clauses_tptp                false
% 3.42/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.42/1.01  --bmc1_dump_file                        -
% 3.42/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.42/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.42/1.01  --bmc1_ucm_extend_mode                  1
% 3.42/1.01  --bmc1_ucm_init_mode                    2
% 3.42/1.01  --bmc1_ucm_cone_mode                    none
% 3.42/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.42/1.01  --bmc1_ucm_relax_model                  4
% 3.42/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.42/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.42/1.01  --bmc1_ucm_layered_model                none
% 3.42/1.01  --bmc1_ucm_max_lemma_size               10
% 3.42/1.01  
% 3.42/1.01  ------ AIG Options
% 3.42/1.01  
% 3.42/1.01  --aig_mode                              false
% 3.42/1.01  
% 3.42/1.01  ------ Instantiation Options
% 3.42/1.01  
% 3.42/1.01  --instantiation_flag                    true
% 3.42/1.01  --inst_sos_flag                         true
% 3.42/1.01  --inst_sos_phase                        true
% 3.42/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.42/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.42/1.01  --inst_lit_sel_side                     num_symb
% 3.42/1.01  --inst_solver_per_active                1400
% 3.42/1.01  --inst_solver_calls_frac                1.
% 3.42/1.01  --inst_passive_queue_type               priority_queues
% 3.42/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.42/1.01  --inst_passive_queues_freq              [25;2]
% 3.42/1.01  --inst_dismatching                      true
% 3.42/1.01  --inst_eager_unprocessed_to_passive     true
% 3.42/1.01  --inst_prop_sim_given                   true
% 3.42/1.01  --inst_prop_sim_new                     false
% 3.42/1.01  --inst_subs_new                         false
% 3.42/1.01  --inst_eq_res_simp                      false
% 3.42/1.01  --inst_subs_given                       false
% 3.42/1.01  --inst_orphan_elimination               true
% 3.42/1.01  --inst_learning_loop_flag               true
% 3.42/1.01  --inst_learning_start                   3000
% 3.42/1.01  --inst_learning_factor                  2
% 3.42/1.01  --inst_start_prop_sim_after_learn       3
% 3.42/1.01  --inst_sel_renew                        solver
% 3.42/1.01  --inst_lit_activity_flag                true
% 3.42/1.01  --inst_restr_to_given                   false
% 3.42/1.01  --inst_activity_threshold               500
% 3.42/1.01  --inst_out_proof                        true
% 3.42/1.01  
% 3.42/1.01  ------ Resolution Options
% 3.42/1.01  
% 3.42/1.01  --resolution_flag                       true
% 3.42/1.01  --res_lit_sel                           adaptive
% 3.42/1.01  --res_lit_sel_side                      none
% 3.42/1.01  --res_ordering                          kbo
% 3.42/1.01  --res_to_prop_solver                    active
% 3.42/1.01  --res_prop_simpl_new                    false
% 3.42/1.01  --res_prop_simpl_given                  true
% 3.42/1.01  --res_passive_queue_type                priority_queues
% 3.42/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.42/1.01  --res_passive_queues_freq               [15;5]
% 3.42/1.01  --res_forward_subs                      full
% 3.42/1.01  --res_backward_subs                     full
% 3.42/1.01  --res_forward_subs_resolution           true
% 3.42/1.01  --res_backward_subs_resolution          true
% 3.42/1.01  --res_orphan_elimination                true
% 3.42/1.01  --res_time_limit                        2.
% 3.42/1.01  --res_out_proof                         true
% 3.42/1.01  
% 3.42/1.01  ------ Superposition Options
% 3.42/1.01  
% 3.42/1.01  --superposition_flag                    true
% 3.42/1.01  --sup_passive_queue_type                priority_queues
% 3.42/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.42/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.42/1.01  --demod_completeness_check              fast
% 3.42/1.01  --demod_use_ground                      true
% 3.42/1.01  --sup_to_prop_solver                    passive
% 3.42/1.01  --sup_prop_simpl_new                    true
% 3.42/1.01  --sup_prop_simpl_given                  true
% 3.42/1.01  --sup_fun_splitting                     true
% 3.42/1.01  --sup_smt_interval                      50000
% 3.42/1.01  
% 3.42/1.01  ------ Superposition Simplification Setup
% 3.42/1.01  
% 3.42/1.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.42/1.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.42/1.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.42/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.42/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.42/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.42/1.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.42/1.01  --sup_immed_triv                        [TrivRules]
% 3.42/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.42/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.42/1.01  --sup_immed_bw_main                     []
% 3.42/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.42/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.42/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.42/1.01  --sup_input_bw                          []
% 3.42/1.01  
% 3.42/1.01  ------ Combination Options
% 3.42/1.01  
% 3.42/1.01  --comb_res_mult                         3
% 3.42/1.01  --comb_sup_mult                         2
% 3.42/1.01  --comb_inst_mult                        10
% 3.42/1.01  
% 3.42/1.01  ------ Debug Options
% 3.42/1.01  
% 3.42/1.01  --dbg_backtrace                         false
% 3.42/1.01  --dbg_dump_prop_clauses                 false
% 3.42/1.01  --dbg_dump_prop_clauses_file            -
% 3.42/1.01  --dbg_out_stat                          false
% 3.42/1.01  ------ Parsing...
% 3.42/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.42/1.01  
% 3.42/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.42/1.01  
% 3.42/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.42/1.01  
% 3.42/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.42/1.01  ------ Proving...
% 3.42/1.01  ------ Problem Properties 
% 3.42/1.01  
% 3.42/1.01  
% 3.42/1.01  clauses                                 6
% 3.42/1.01  conjectures                             1
% 3.42/1.01  EPR                                     0
% 3.42/1.01  Horn                                    6
% 3.42/1.01  unary                                   4
% 3.42/1.01  binary                                  1
% 3.42/1.01  lits                                    9
% 3.42/1.01  lits eq                                 2
% 3.42/1.01  fd_pure                                 0
% 3.42/1.01  fd_pseudo                               0
% 3.42/1.01  fd_cond                                 0
% 3.42/1.01  fd_pseudo_cond                          0
% 3.42/1.01  AC symbols                              0
% 3.42/1.01  
% 3.42/1.01  ------ Schedule dynamic 5 is on 
% 3.42/1.01  
% 3.42/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.42/1.01  
% 3.42/1.01  
% 3.42/1.01  ------ 
% 3.42/1.01  Current options:
% 3.42/1.01  ------ 
% 3.42/1.01  
% 3.42/1.01  ------ Input Options
% 3.42/1.01  
% 3.42/1.01  --out_options                           all
% 3.42/1.01  --tptp_safe_out                         true
% 3.42/1.01  --problem_path                          ""
% 3.42/1.01  --include_path                          ""
% 3.42/1.01  --clausifier                            res/vclausify_rel
% 3.42/1.01  --clausifier_options                    ""
% 3.42/1.01  --stdin                                 false
% 3.42/1.01  --stats_out                             all
% 3.42/1.01  
% 3.42/1.01  ------ General Options
% 3.42/1.01  
% 3.42/1.01  --fof                                   false
% 3.42/1.01  --time_out_real                         305.
% 3.42/1.01  --time_out_virtual                      -1.
% 3.42/1.01  --symbol_type_check                     false
% 3.42/1.01  --clausify_out                          false
% 3.42/1.01  --sig_cnt_out                           false
% 3.42/1.01  --trig_cnt_out                          false
% 3.42/1.01  --trig_cnt_out_tolerance                1.
% 3.42/1.01  --trig_cnt_out_sk_spl                   false
% 3.42/1.01  --abstr_cl_out                          false
% 3.42/1.01  
% 3.42/1.01  ------ Global Options
% 3.42/1.01  
% 3.42/1.01  --schedule                              default
% 3.42/1.01  --add_important_lit                     false
% 3.42/1.01  --prop_solver_per_cl                    1000
% 3.42/1.01  --min_unsat_core                        false
% 3.42/1.01  --soft_assumptions                      false
% 3.42/1.01  --soft_lemma_size                       3
% 3.42/1.01  --prop_impl_unit_size                   0
% 3.42/1.01  --prop_impl_unit                        []
% 3.42/1.01  --share_sel_clauses                     true
% 3.42/1.01  --reset_solvers                         false
% 3.42/1.01  --bc_imp_inh                            [conj_cone]
% 3.42/1.01  --conj_cone_tolerance                   3.
% 3.42/1.01  --extra_neg_conj                        none
% 3.42/1.01  --large_theory_mode                     true
% 3.42/1.01  --prolific_symb_bound                   200
% 3.42/1.01  --lt_threshold                          2000
% 3.42/1.01  --clause_weak_htbl                      true
% 3.42/1.01  --gc_record_bc_elim                     false
% 3.42/1.01  
% 3.42/1.01  ------ Preprocessing Options
% 3.42/1.01  
% 3.42/1.01  --preprocessing_flag                    true
% 3.42/1.01  --time_out_prep_mult                    0.1
% 3.42/1.01  --splitting_mode                        input
% 3.42/1.01  --splitting_grd                         true
% 3.42/1.01  --splitting_cvd                         false
% 3.42/1.01  --splitting_cvd_svl                     false
% 3.42/1.01  --splitting_nvd                         32
% 3.42/1.01  --sub_typing                            true
% 3.42/1.01  --prep_gs_sim                           true
% 3.42/1.01  --prep_unflatten                        true
% 3.42/1.01  --prep_res_sim                          true
% 3.42/1.01  --prep_upred                            true
% 3.42/1.01  --prep_sem_filter                       exhaustive
% 3.42/1.01  --prep_sem_filter_out                   false
% 3.42/1.01  --pred_elim                             true
% 3.42/1.01  --res_sim_input                         true
% 3.42/1.01  --eq_ax_congr_red                       true
% 3.42/1.01  --pure_diseq_elim                       true
% 3.42/1.01  --brand_transform                       false
% 3.42/1.01  --non_eq_to_eq                          false
% 3.42/1.01  --prep_def_merge                        true
% 3.42/1.01  --prep_def_merge_prop_impl              false
% 3.42/1.01  --prep_def_merge_mbd                    true
% 3.42/1.01  --prep_def_merge_tr_red                 false
% 3.42/1.01  --prep_def_merge_tr_cl                  false
% 3.42/1.01  --smt_preprocessing                     true
% 3.42/1.01  --smt_ac_axioms                         fast
% 3.42/1.01  --preprocessed_out                      false
% 3.42/1.01  --preprocessed_stats                    false
% 3.42/1.01  
% 3.42/1.01  ------ Abstraction refinement Options
% 3.42/1.01  
% 3.42/1.01  --abstr_ref                             []
% 3.42/1.01  --abstr_ref_prep                        false
% 3.42/1.01  --abstr_ref_until_sat                   false
% 3.42/1.01  --abstr_ref_sig_restrict                funpre
% 3.42/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.42/1.01  --abstr_ref_under                       []
% 3.42/1.01  
% 3.42/1.01  ------ SAT Options
% 3.42/1.01  
% 3.42/1.01  --sat_mode                              false
% 3.42/1.01  --sat_fm_restart_options                ""
% 3.42/1.01  --sat_gr_def                            false
% 3.42/1.01  --sat_epr_types                         true
% 3.42/1.01  --sat_non_cyclic_types                  false
% 3.42/1.01  --sat_finite_models                     false
% 3.42/1.01  --sat_fm_lemmas                         false
% 3.42/1.01  --sat_fm_prep                           false
% 3.42/1.01  --sat_fm_uc_incr                        true
% 3.42/1.01  --sat_out_model                         small
% 3.42/1.01  --sat_out_clauses                       false
% 3.42/1.01  
% 3.42/1.01  ------ QBF Options
% 3.42/1.01  
% 3.42/1.01  --qbf_mode                              false
% 3.42/1.01  --qbf_elim_univ                         false
% 3.42/1.01  --qbf_dom_inst                          none
% 3.42/1.01  --qbf_dom_pre_inst                      false
% 3.42/1.01  --qbf_sk_in                             false
% 3.42/1.01  --qbf_pred_elim                         true
% 3.42/1.01  --qbf_split                             512
% 3.42/1.01  
% 3.42/1.01  ------ BMC1 Options
% 3.42/1.01  
% 3.42/1.01  --bmc1_incremental                      false
% 3.42/1.01  --bmc1_axioms                           reachable_all
% 3.42/1.01  --bmc1_min_bound                        0
% 3.42/1.01  --bmc1_max_bound                        -1
% 3.42/1.01  --bmc1_max_bound_default                -1
% 3.42/1.01  --bmc1_symbol_reachability              true
% 3.42/1.01  --bmc1_property_lemmas                  false
% 3.42/1.01  --bmc1_k_induction                      false
% 3.42/1.01  --bmc1_non_equiv_states                 false
% 3.42/1.01  --bmc1_deadlock                         false
% 3.42/1.01  --bmc1_ucm                              false
% 3.42/1.01  --bmc1_add_unsat_core                   none
% 3.42/1.01  --bmc1_unsat_core_children              false
% 3.42/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.42/1.01  --bmc1_out_stat                         full
% 3.42/1.01  --bmc1_ground_init                      false
% 3.42/1.01  --bmc1_pre_inst_next_state              false
% 3.42/1.01  --bmc1_pre_inst_state                   false
% 3.42/1.01  --bmc1_pre_inst_reach_state             false
% 3.42/1.01  --bmc1_out_unsat_core                   false
% 3.42/1.01  --bmc1_aig_witness_out                  false
% 3.42/1.01  --bmc1_verbose                          false
% 3.42/1.01  --bmc1_dump_clauses_tptp                false
% 3.42/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.42/1.01  --bmc1_dump_file                        -
% 3.42/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.42/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.42/1.01  --bmc1_ucm_extend_mode                  1
% 3.42/1.01  --bmc1_ucm_init_mode                    2
% 3.42/1.01  --bmc1_ucm_cone_mode                    none
% 3.42/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.42/1.01  --bmc1_ucm_relax_model                  4
% 3.42/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.42/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.42/1.01  --bmc1_ucm_layered_model                none
% 3.42/1.01  --bmc1_ucm_max_lemma_size               10
% 3.42/1.01  
% 3.42/1.01  ------ AIG Options
% 3.42/1.01  
% 3.42/1.01  --aig_mode                              false
% 3.42/1.01  
% 3.42/1.01  ------ Instantiation Options
% 3.42/1.01  
% 3.42/1.01  --instantiation_flag                    true
% 3.42/1.01  --inst_sos_flag                         true
% 3.42/1.01  --inst_sos_phase                        true
% 3.42/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.42/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.42/1.01  --inst_lit_sel_side                     none
% 3.42/1.01  --inst_solver_per_active                1400
% 3.42/1.01  --inst_solver_calls_frac                1.
% 3.42/1.01  --inst_passive_queue_type               priority_queues
% 3.42/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.42/1.01  --inst_passive_queues_freq              [25;2]
% 3.42/1.01  --inst_dismatching                      true
% 3.42/1.01  --inst_eager_unprocessed_to_passive     true
% 3.42/1.01  --inst_prop_sim_given                   true
% 3.42/1.01  --inst_prop_sim_new                     false
% 3.42/1.01  --inst_subs_new                         false
% 3.42/1.01  --inst_eq_res_simp                      false
% 3.42/1.01  --inst_subs_given                       false
% 3.42/1.01  --inst_orphan_elimination               true
% 3.42/1.01  --inst_learning_loop_flag               true
% 3.42/1.01  --inst_learning_start                   3000
% 3.42/1.01  --inst_learning_factor                  2
% 3.42/1.01  --inst_start_prop_sim_after_learn       3
% 3.42/1.01  --inst_sel_renew                        solver
% 3.42/1.01  --inst_lit_activity_flag                true
% 3.42/1.01  --inst_restr_to_given                   false
% 3.42/1.01  --inst_activity_threshold               500
% 3.42/1.01  --inst_out_proof                        true
% 3.42/1.01  
% 3.42/1.01  ------ Resolution Options
% 3.42/1.01  
% 3.42/1.01  --resolution_flag                       false
% 3.42/1.01  --res_lit_sel                           adaptive
% 3.42/1.01  --res_lit_sel_side                      none
% 3.42/1.01  --res_ordering                          kbo
% 3.42/1.01  --res_to_prop_solver                    active
% 3.42/1.01  --res_prop_simpl_new                    false
% 3.42/1.01  --res_prop_simpl_given                  true
% 3.42/1.01  --res_passive_queue_type                priority_queues
% 3.42/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.42/1.01  --res_passive_queues_freq               [15;5]
% 3.42/1.01  --res_forward_subs                      full
% 3.42/1.01  --res_backward_subs                     full
% 3.42/1.01  --res_forward_subs_resolution           true
% 3.42/1.01  --res_backward_subs_resolution          true
% 3.42/1.01  --res_orphan_elimination                true
% 3.42/1.01  --res_time_limit                        2.
% 3.42/1.01  --res_out_proof                         true
% 3.42/1.01  
% 3.42/1.01  ------ Superposition Options
% 3.42/1.01  
% 3.42/1.01  --superposition_flag                    true
% 3.42/1.01  --sup_passive_queue_type                priority_queues
% 3.42/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.42/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.42/1.01  --demod_completeness_check              fast
% 3.42/1.01  --demod_use_ground                      true
% 3.42/1.01  --sup_to_prop_solver                    passive
% 3.42/1.01  --sup_prop_simpl_new                    true
% 3.42/1.01  --sup_prop_simpl_given                  true
% 3.42/1.01  --sup_fun_splitting                     true
% 3.42/1.01  --sup_smt_interval                      50000
% 3.42/1.01  
% 3.42/1.01  ------ Superposition Simplification Setup
% 3.42/1.01  
% 3.42/1.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.42/1.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.42/1.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.42/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.42/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.42/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.42/1.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.42/1.01  --sup_immed_triv                        [TrivRules]
% 3.42/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.42/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.42/1.01  --sup_immed_bw_main                     []
% 3.42/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.42/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.42/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.42/1.01  --sup_input_bw                          []
% 3.42/1.01  
% 3.42/1.01  ------ Combination Options
% 3.42/1.01  
% 3.42/1.01  --comb_res_mult                         3
% 3.42/1.01  --comb_sup_mult                         2
% 3.42/1.01  --comb_inst_mult                        10
% 3.42/1.01  
% 3.42/1.01  ------ Debug Options
% 3.42/1.01  
% 3.42/1.01  --dbg_backtrace                         false
% 3.42/1.01  --dbg_dump_prop_clauses                 false
% 3.42/1.01  --dbg_dump_prop_clauses_file            -
% 3.42/1.01  --dbg_out_stat                          false
% 3.42/1.01  
% 3.42/1.01  
% 3.42/1.01  
% 3.42/1.01  
% 3.42/1.01  ------ Proving...
% 3.42/1.01  
% 3.42/1.01  
% 3.42/1.01  % SZS status Theorem for theBenchmark.p
% 3.42/1.01  
% 3.42/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.42/1.01  
% 3.42/1.01  fof(f2,axiom,(
% 3.42/1.01    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) => r1_tarski(X0,X1))),
% 3.42/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.42/1.01  
% 3.42/1.01  fof(f9,plain,(
% 3.42/1.01    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 3.42/1.01    inference(ennf_transformation,[],[f2])).
% 3.42/1.01  
% 3.42/1.01  fof(f20,plain,(
% 3.42/1.01    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2))) )),
% 3.42/1.01    inference(cnf_transformation,[],[f9])).
% 3.42/1.01  
% 3.42/1.01  fof(f4,axiom,(
% 3.42/1.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.42/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.42/1.01  
% 3.42/1.01  fof(f22,plain,(
% 3.42/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.42/1.01    inference(cnf_transformation,[],[f4])).
% 3.42/1.01  
% 3.42/1.01  fof(f29,plain,(
% 3.42/1.01    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) )),
% 3.42/1.01    inference(definition_unfolding,[],[f20,f22])).
% 3.42/1.01  
% 3.42/1.01  fof(f6,axiom,(
% 3.42/1.01    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)))),
% 3.42/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.42/1.01  
% 3.42/1.01  fof(f13,plain,(
% 3.42/1.01    ! [X0,X1] : (k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.42/1.01    inference(ennf_transformation,[],[f6])).
% 3.42/1.01  
% 3.42/1.01  fof(f14,plain,(
% 3.42/1.01    ! [X0,X1] : (k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.42/1.01    inference(flattening,[],[f13])).
% 3.42/1.01  
% 3.42/1.01  fof(f24,plain,(
% 3.42/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.42/1.01    inference(cnf_transformation,[],[f14])).
% 3.42/1.01  
% 3.42/1.01  fof(f32,plain,(
% 3.42/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))) = k9_relat_1(X1,k10_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.42/1.01    inference(definition_unfolding,[],[f24,f22])).
% 3.42/1.01  
% 3.42/1.01  fof(f7,conjecture,(
% 3.42/1.01    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)))),
% 3.42/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.42/1.01  
% 3.42/1.01  fof(f8,negated_conjecture,(
% 3.42/1.01    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)))),
% 3.42/1.01    inference(negated_conjecture,[],[f7])).
% 3.42/1.01  
% 3.42/1.01  fof(f15,plain,(
% 3.42/1.01    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 3.42/1.01    inference(ennf_transformation,[],[f8])).
% 3.42/1.01  
% 3.42/1.01  fof(f16,plain,(
% 3.42/1.01    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 3.42/1.01    inference(flattening,[],[f15])).
% 3.42/1.01  
% 3.42/1.01  fof(f17,plain,(
% 3.42/1.01    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 3.42/1.01    introduced(choice_axiom,[])).
% 3.42/1.01  
% 3.42/1.01  fof(f18,plain,(
% 3.42/1.01    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 3.42/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f17])).
% 3.42/1.01  
% 3.42/1.01  fof(f26,plain,(
% 3.42/1.01    v1_funct_1(sK2)),
% 3.42/1.01    inference(cnf_transformation,[],[f18])).
% 3.42/1.01  
% 3.42/1.01  fof(f25,plain,(
% 3.42/1.01    v1_relat_1(sK2)),
% 3.42/1.01    inference(cnf_transformation,[],[f18])).
% 3.42/1.01  
% 3.42/1.01  fof(f1,axiom,(
% 3.42/1.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.42/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.42/1.01  
% 3.42/1.01  fof(f19,plain,(
% 3.42/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.42/1.01    inference(cnf_transformation,[],[f1])).
% 3.42/1.01  
% 3.42/1.01  fof(f28,plain,(
% 3.42/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 3.42/1.01    inference(definition_unfolding,[],[f19,f22,f22])).
% 3.42/1.01  
% 3.42/1.01  fof(f5,axiom,(
% 3.42/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 3.42/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.42/1.01  
% 3.42/1.01  fof(f12,plain,(
% 3.42/1.01    ! [X0,X1,X2] : (r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) | ~v1_relat_1(X2))),
% 3.42/1.01    inference(ennf_transformation,[],[f5])).
% 3.42/1.01  
% 3.42/1.01  fof(f23,plain,(
% 3.42/1.01    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) | ~v1_relat_1(X2)) )),
% 3.42/1.01    inference(cnf_transformation,[],[f12])).
% 3.42/1.01  
% 3.42/1.01  fof(f31,plain,(
% 3.42/1.01    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k9_relat_1(X2,X0),k4_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))) | ~v1_relat_1(X2)) )),
% 3.42/1.01    inference(definition_unfolding,[],[f23,f22,f22])).
% 3.42/1.01  
% 3.42/1.01  fof(f3,axiom,(
% 3.42/1.01    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 3.42/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.42/1.01  
% 3.42/1.01  fof(f10,plain,(
% 3.42/1.01    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 3.42/1.01    inference(ennf_transformation,[],[f3])).
% 3.42/1.01  
% 3.42/1.01  fof(f11,plain,(
% 3.42/1.01    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 3.42/1.01    inference(flattening,[],[f10])).
% 3.42/1.01  
% 3.42/1.01  fof(f21,plain,(
% 3.42/1.01    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 3.42/1.01    inference(cnf_transformation,[],[f11])).
% 3.42/1.01  
% 3.42/1.01  fof(f30,plain,(
% 3.42/1.01    ( ! [X2,X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 3.42/1.01    inference(definition_unfolding,[],[f21,f22])).
% 3.42/1.01  
% 3.42/1.01  fof(f27,plain,(
% 3.42/1.01    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1))),
% 3.42/1.01    inference(cnf_transformation,[],[f18])).
% 3.42/1.01  
% 3.42/1.01  fof(f33,plain,(
% 3.42/1.01    ~r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k4_xboole_0(k9_relat_1(sK2,sK0),k4_xboole_0(k9_relat_1(sK2,sK0),sK1)))),
% 3.42/1.01    inference(definition_unfolding,[],[f27,f22,f22])).
% 3.42/1.01  
% 3.42/1.01  cnf(c_1,plain,
% 3.42/1.01      ( r1_tarski(X0,X1)
% 3.42/1.01      | ~ r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
% 3.42/1.01      inference(cnf_transformation,[],[f29]) ).
% 3.42/1.01  
% 3.42/1.01  cnf(c_144,plain,
% 3.42/1.01      ( r1_tarski(X0_38,X1_38)
% 3.42/1.01      | ~ r1_tarski(X0_38,k4_xboole_0(X1_38,k4_xboole_0(X1_38,X2_38))) ),
% 3.42/1.01      inference(subtyping,[status(esa)],[c_1]) ).
% 3.42/1.01  
% 3.42/1.01  cnf(c_258,plain,
% 3.42/1.01      ( ~ r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k4_xboole_0(sK1,k4_xboole_0(sK1,X0_38)))
% 3.42/1.01      | r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),sK1) ),
% 3.42/1.01      inference(instantiation,[status(thm)],[c_144]) ).
% 3.42/1.01  
% 3.42/1.01  cnf(c_5215,plain,
% 3.42/1.01      ( ~ r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k4_xboole_0(sK1,k4_xboole_0(sK1,k9_relat_1(sK2,k1_relat_1(sK2)))))
% 3.42/1.01      | r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),sK1) ),
% 3.42/1.01      inference(instantiation,[status(thm)],[c_258]) ).
% 3.42/1.01  
% 3.42/1.01  cnf(c_150,plain,
% 3.42/1.01      ( ~ r1_tarski(X0_38,X1_38)
% 3.42/1.01      | r1_tarski(X2_38,X3_38)
% 3.42/1.01      | X2_38 != X0_38
% 3.42/1.01      | X3_38 != X1_38 ),
% 3.42/1.01      theory(equality) ).
% 3.42/1.01  
% 3.42/1.01  cnf(c_302,plain,
% 3.42/1.01      ( ~ r1_tarski(X0_38,X1_38)
% 3.42/1.01      | r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k4_xboole_0(sK1,k4_xboole_0(sK1,X2_38)))
% 3.42/1.01      | k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))) != X0_38
% 3.42/1.01      | k4_xboole_0(sK1,k4_xboole_0(sK1,X2_38)) != X1_38 ),
% 3.42/1.01      inference(instantiation,[status(thm)],[c_150]) ).
% 3.42/1.01  
% 3.42/1.01  cnf(c_394,plain,
% 3.42/1.01      ( ~ r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),X0_38)
% 3.42/1.01      | r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k4_xboole_0(sK1,k4_xboole_0(sK1,X1_38)))
% 3.42/1.01      | k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))) != k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1))))
% 3.42/1.01      | k4_xboole_0(sK1,k4_xboole_0(sK1,X1_38)) != X0_38 ),
% 3.42/1.01      inference(instantiation,[status(thm)],[c_302]) ).
% 3.42/1.01  
% 3.42/1.01  cnf(c_1631,plain,
% 3.42/1.01      ( ~ r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k9_relat_1(sK2,X0_38))
% 3.42/1.01      | r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k4_xboole_0(sK1,k4_xboole_0(sK1,X1_38)))
% 3.42/1.01      | k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))) != k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1))))
% 3.42/1.01      | k4_xboole_0(sK1,k4_xboole_0(sK1,X1_38)) != k9_relat_1(sK2,X0_38) ),
% 3.42/1.01      inference(instantiation,[status(thm)],[c_394]) ).
% 3.42/1.01  
% 3.42/1.01  cnf(c_4031,plain,
% 3.42/1.01      ( ~ r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k9_relat_1(sK2,k10_relat_1(sK2,sK1)))
% 3.42/1.01      | r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k4_xboole_0(sK1,k4_xboole_0(sK1,k9_relat_1(sK2,k1_relat_1(sK2)))))
% 3.42/1.01      | k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))) != k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1))))
% 3.42/1.01      | k4_xboole_0(sK1,k4_xboole_0(sK1,k9_relat_1(sK2,k1_relat_1(sK2)))) != k9_relat_1(sK2,k10_relat_1(sK2,sK1)) ),
% 3.42/1.01      inference(instantiation,[status(thm)],[c_1631]) ).
% 3.42/1.01  
% 3.42/1.01  cnf(c_429,plain,
% 3.42/1.01      ( r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),X0_38)
% 3.42/1.01      | ~ r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k4_xboole_0(X0_38,k4_xboole_0(X0_38,X1_38))) ),
% 3.42/1.01      inference(instantiation,[status(thm)],[c_144]) ).
% 3.42/1.01  
% 3.42/1.01  cnf(c_3467,plain,
% 3.42/1.01      ( r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k9_relat_1(sK2,k10_relat_1(sK2,sK1)))
% 3.42/1.01      | ~ r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k4_xboole_0(k9_relat_1(sK2,k10_relat_1(sK2,sK1)),k4_xboole_0(k9_relat_1(sK2,k10_relat_1(sK2,sK1)),k9_relat_1(sK2,sK0)))) ),
% 3.42/1.01      inference(instantiation,[status(thm)],[c_429]) ).
% 3.42/1.01  
% 3.42/1.01  cnf(c_4,plain,
% 3.42/1.01      ( ~ v1_funct_1(X0)
% 3.42/1.01      | ~ v1_relat_1(X0)
% 3.42/1.01      | k4_xboole_0(X1,k4_xboole_0(X1,k9_relat_1(X0,k1_relat_1(X0)))) = k9_relat_1(X0,k10_relat_1(X0,X1)) ),
% 3.42/1.01      inference(cnf_transformation,[],[f32]) ).
% 3.42/1.01  
% 3.42/1.01  cnf(c_6,negated_conjecture,
% 3.42/1.01      ( v1_funct_1(sK2) ),
% 3.42/1.01      inference(cnf_transformation,[],[f26]) ).
% 3.42/1.01  
% 3.42/1.01  cnf(c_84,plain,
% 3.42/1.01      ( ~ v1_relat_1(X0)
% 3.42/1.01      | k4_xboole_0(X1,k4_xboole_0(X1,k9_relat_1(X0,k1_relat_1(X0)))) = k9_relat_1(X0,k10_relat_1(X0,X1))
% 3.42/1.01      | sK2 != X0 ),
% 3.42/1.01      inference(resolution_lifted,[status(thm)],[c_4,c_6]) ).
% 3.42/1.01  
% 3.42/1.01  cnf(c_85,plain,
% 3.42/1.01      ( ~ v1_relat_1(sK2)
% 3.42/1.01      | k4_xboole_0(X0,k4_xboole_0(X0,k9_relat_1(sK2,k1_relat_1(sK2)))) = k9_relat_1(sK2,k10_relat_1(sK2,X0)) ),
% 3.42/1.01      inference(unflattening,[status(thm)],[c_84]) ).
% 3.42/1.01  
% 3.42/1.01  cnf(c_7,negated_conjecture,
% 3.42/1.01      ( v1_relat_1(sK2) ),
% 3.42/1.01      inference(cnf_transformation,[],[f25]) ).
% 3.42/1.01  
% 3.42/1.01  cnf(c_89,plain,
% 3.42/1.01      ( k4_xboole_0(X0,k4_xboole_0(X0,k9_relat_1(sK2,k1_relat_1(sK2)))) = k9_relat_1(sK2,k10_relat_1(sK2,X0)) ),
% 3.42/1.01      inference(global_propositional_subsumption,
% 3.42/1.01                [status(thm)],
% 3.42/1.01                [c_85,c_7]) ).
% 3.42/1.01  
% 3.42/1.01  cnf(c_141,plain,
% 3.42/1.01      ( k4_xboole_0(X0_38,k4_xboole_0(X0_38,k9_relat_1(sK2,k1_relat_1(sK2)))) = k9_relat_1(sK2,k10_relat_1(sK2,X0_38)) ),
% 3.42/1.01      inference(subtyping,[status(esa)],[c_89]) ).
% 3.42/1.01  
% 3.42/1.01  cnf(c_2362,plain,
% 3.42/1.01      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k9_relat_1(sK2,k1_relat_1(sK2)))) = k9_relat_1(sK2,k10_relat_1(sK2,sK1)) ),
% 3.42/1.01      inference(instantiation,[status(thm)],[c_141]) ).
% 3.42/1.01  
% 3.42/1.01  cnf(c_0,plain,
% 3.42/1.01      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 3.42/1.01      inference(cnf_transformation,[],[f28]) ).
% 3.42/1.01  
% 3.42/1.01  cnf(c_145,plain,
% 3.42/1.01      ( k4_xboole_0(X0_38,k4_xboole_0(X0_38,X1_38)) = k4_xboole_0(X1_38,k4_xboole_0(X1_38,X0_38)) ),
% 3.42/1.01      inference(subtyping,[status(esa)],[c_0]) ).
% 3.42/1.01  
% 3.42/1.01  cnf(c_1486,plain,
% 3.42/1.01      ( k4_xboole_0(k9_relat_1(sK2,k10_relat_1(sK2,sK1)),k4_xboole_0(k9_relat_1(sK2,k10_relat_1(sK2,sK1)),k9_relat_1(sK2,sK0))) = k4_xboole_0(k9_relat_1(sK2,sK0),k4_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,k10_relat_1(sK2,sK1)))) ),
% 3.42/1.01      inference(instantiation,[status(thm)],[c_145]) ).
% 3.42/1.01  
% 3.42/1.01  cnf(c_439,plain,
% 3.42/1.01      ( ~ r1_tarski(X0_38,X1_38)
% 3.42/1.01      | r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),X2_38)
% 3.42/1.01      | X2_38 != X1_38
% 3.42/1.01      | k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))) != X0_38 ),
% 3.42/1.01      inference(instantiation,[status(thm)],[c_150]) ).
% 3.42/1.01  
% 3.42/1.01  cnf(c_538,plain,
% 3.42/1.01      ( ~ r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),X0_38)
% 3.42/1.01      | r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),X1_38)
% 3.42/1.01      | X1_38 != X0_38
% 3.42/1.01      | k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))) != k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))) ),
% 3.42/1.01      inference(instantiation,[status(thm)],[c_439]) ).
% 3.42/1.01  
% 3.42/1.01  cnf(c_965,plain,
% 3.42/1.01      ( r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),X0_38)
% 3.42/1.01      | ~ r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k4_xboole_0(k9_relat_1(sK2,sK0),k4_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,k10_relat_1(sK2,sK1)))))
% 3.42/1.01      | X0_38 != k4_xboole_0(k9_relat_1(sK2,sK0),k4_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,k10_relat_1(sK2,sK1))))
% 3.42/1.01      | k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))) != k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))) ),
% 3.42/1.01      inference(instantiation,[status(thm)],[c_538]) ).
% 3.42/1.01  
% 3.42/1.01  cnf(c_1118,plain,
% 3.42/1.01      ( r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k4_xboole_0(k9_relat_1(sK2,k10_relat_1(sK2,sK1)),k4_xboole_0(k9_relat_1(sK2,k10_relat_1(sK2,sK1)),k9_relat_1(sK2,sK0))))
% 3.42/1.01      | ~ r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k4_xboole_0(k9_relat_1(sK2,sK0),k4_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,k10_relat_1(sK2,sK1)))))
% 3.42/1.01      | k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))) != k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1))))
% 3.42/1.01      | k4_xboole_0(k9_relat_1(sK2,k10_relat_1(sK2,sK1)),k4_xboole_0(k9_relat_1(sK2,k10_relat_1(sK2,sK1)),k9_relat_1(sK2,sK0))) != k4_xboole_0(k9_relat_1(sK2,sK0),k4_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,k10_relat_1(sK2,sK1)))) ),
% 3.42/1.01      inference(instantiation,[status(thm)],[c_965]) ).
% 3.42/1.01  
% 3.42/1.01  cnf(c_497,plain,
% 3.42/1.01      ( r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k9_relat_1(sK2,sK0))
% 3.42/1.01      | ~ r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k4_xboole_0(k9_relat_1(sK2,sK0),k4_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,k10_relat_1(sK2,sK1))))) ),
% 3.42/1.01      inference(instantiation,[status(thm)],[c_429]) ).
% 3.42/1.01  
% 3.42/1.01  cnf(c_3,plain,
% 3.42/1.01      ( r1_tarski(k9_relat_1(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))),k4_xboole_0(k9_relat_1(X0,X1),k4_xboole_0(k9_relat_1(X0,X1),k9_relat_1(X0,X2))))
% 3.42/1.01      | ~ v1_relat_1(X0) ),
% 3.42/1.01      inference(cnf_transformation,[],[f31]) ).
% 3.42/1.01  
% 3.42/1.01  cnf(c_96,plain,
% 3.42/1.01      ( r1_tarski(k9_relat_1(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))),k4_xboole_0(k9_relat_1(X0,X1),k4_xboole_0(k9_relat_1(X0,X1),k9_relat_1(X0,X2))))
% 3.42/1.01      | sK2 != X0 ),
% 3.42/1.01      inference(resolution_lifted,[status(thm)],[c_3,c_7]) ).
% 3.42/1.01  
% 3.42/1.01  cnf(c_97,plain,
% 3.42/1.01      ( r1_tarski(k9_relat_1(sK2,k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k9_relat_1(sK2,X0),k4_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)))) ),
% 3.42/1.01      inference(unflattening,[status(thm)],[c_96]) ).
% 3.42/1.01  
% 3.42/1.01  cnf(c_140,plain,
% 3.42/1.01      ( r1_tarski(k9_relat_1(sK2,k4_xboole_0(X0_38,k4_xboole_0(X0_38,X1_38))),k4_xboole_0(k9_relat_1(sK2,X0_38),k4_xboole_0(k9_relat_1(sK2,X0_38),k9_relat_1(sK2,X1_38)))) ),
% 3.42/1.01      inference(subtyping,[status(esa)],[c_97]) ).
% 3.42/1.01  
% 3.42/1.01  cnf(c_424,plain,
% 3.42/1.01      ( r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k4_xboole_0(k9_relat_1(sK2,sK0),k4_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,k10_relat_1(sK2,sK1))))) ),
% 3.42/1.01      inference(instantiation,[status(thm)],[c_140]) ).
% 3.42/1.01  
% 3.42/1.01  cnf(c_147,plain,( X0_38 = X0_38 ),theory(equality) ).
% 3.42/1.01  
% 3.42/1.01  cnf(c_321,plain,
% 3.42/1.01      ( k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))) = k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))) ),
% 3.42/1.01      inference(instantiation,[status(thm)],[c_147]) ).
% 3.42/1.01  
% 3.42/1.01  cnf(c_2,plain,
% 3.42/1.01      ( ~ r1_tarski(X0,X1)
% 3.42/1.01      | ~ r1_tarski(X0,X2)
% 3.42/1.01      | r1_tarski(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
% 3.42/1.01      inference(cnf_transformation,[],[f30]) ).
% 3.42/1.01  
% 3.42/1.01  cnf(c_143,plain,
% 3.42/1.01      ( ~ r1_tarski(X0_38,X1_38)
% 3.42/1.01      | ~ r1_tarski(X0_38,X2_38)
% 3.42/1.01      | r1_tarski(X0_38,k4_xboole_0(X2_38,k4_xboole_0(X2_38,X1_38))) ),
% 3.42/1.01      inference(subtyping,[status(esa)],[c_2]) ).
% 3.42/1.01  
% 3.42/1.01  cnf(c_250,plain,
% 3.42/1.01      ( ~ r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k9_relat_1(sK2,sK0))
% 3.42/1.01      | r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k4_xboole_0(k9_relat_1(sK2,sK0),k4_xboole_0(k9_relat_1(sK2,sK0),sK1)))
% 3.42/1.01      | ~ r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),sK1) ),
% 3.42/1.01      inference(instantiation,[status(thm)],[c_143]) ).
% 3.42/1.01  
% 3.42/1.01  cnf(c_5,negated_conjecture,
% 3.42/1.01      ( ~ r1_tarski(k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,k10_relat_1(sK2,sK1)))),k4_xboole_0(k9_relat_1(sK2,sK0),k4_xboole_0(k9_relat_1(sK2,sK0),sK1))) ),
% 3.42/1.01      inference(cnf_transformation,[],[f33]) ).
% 3.42/1.01  
% 3.42/1.01  cnf(contradiction,plain,
% 3.42/1.01      ( $false ),
% 3.42/1.01      inference(minisat,
% 3.42/1.01                [status(thm)],
% 3.42/1.01                [c_5215,c_4031,c_3467,c_2362,c_1486,c_1118,c_497,c_424,
% 3.42/1.01                 c_321,c_250,c_5]) ).
% 3.42/1.01  
% 3.42/1.01  
% 3.42/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.42/1.01  
% 3.42/1.01  ------                               Statistics
% 3.42/1.01  
% 3.42/1.01  ------ General
% 3.42/1.01  
% 3.42/1.01  abstr_ref_over_cycles:                  0
% 3.42/1.01  abstr_ref_under_cycles:                 0
% 3.42/1.01  gc_basic_clause_elim:                   0
% 3.42/1.01  forced_gc_time:                         0
% 3.42/1.01  parsing_time:                           0.008
% 3.42/1.01  unif_index_cands_time:                  0.
% 3.42/1.01  unif_index_add_time:                    0.
% 3.42/1.01  orderings_time:                         0.
% 3.42/1.01  out_proof_time:                         0.023
% 3.42/1.01  total_time:                             0.37
% 3.42/1.01  num_of_symbols:                         43
% 3.42/1.01  num_of_terms:                           6723
% 3.42/1.01  
% 3.42/1.01  ------ Preprocessing
% 3.42/1.01  
% 3.42/1.01  num_of_splits:                          0
% 3.42/1.01  num_of_split_atoms:                     0
% 3.42/1.01  num_of_reused_defs:                     0
% 3.42/1.01  num_eq_ax_congr_red:                    4
% 3.42/1.01  num_of_sem_filtered_clauses:            1
% 3.42/1.01  num_of_subtypes:                        2
% 3.42/1.01  monotx_restored_types:                  0
% 3.42/1.01  sat_num_of_epr_types:                   0
% 3.42/1.01  sat_num_of_non_cyclic_types:            0
% 3.42/1.01  sat_guarded_non_collapsed_types:        0
% 3.42/1.01  num_pure_diseq_elim:                    0
% 3.42/1.01  simp_replaced_by:                       0
% 3.42/1.01  res_preprocessed:                       39
% 3.42/1.01  prep_upred:                             0
% 3.42/1.01  prep_unflattend:                        2
% 3.42/1.01  smt_new_axioms:                         0
% 3.42/1.01  pred_elim_cands:                        1
% 3.42/1.01  pred_elim:                              2
% 3.42/1.01  pred_elim_cl:                           2
% 3.42/1.01  pred_elim_cycles:                       4
% 3.42/1.01  merged_defs:                            0
% 3.42/1.01  merged_defs_ncl:                        0
% 3.42/1.01  bin_hyper_res:                          0
% 3.42/1.01  prep_cycles:                            4
% 3.42/1.01  pred_elim_time:                         0.001
% 3.42/1.01  splitting_time:                         0.
% 3.42/1.01  sem_filter_time:                        0.
% 3.42/1.01  monotx_time:                            0.
% 3.42/1.01  subtype_inf_time:                       0.
% 3.42/1.01  
% 3.42/1.01  ------ Problem properties
% 3.42/1.01  
% 3.42/1.01  clauses:                                6
% 3.42/1.01  conjectures:                            1
% 3.42/1.01  epr:                                    0
% 3.42/1.01  horn:                                   6
% 3.42/1.01  ground:                                 1
% 3.42/1.01  unary:                                  4
% 3.42/1.01  binary:                                 1
% 3.42/1.01  lits:                                   9
% 3.42/1.01  lits_eq:                                2
% 3.42/1.01  fd_pure:                                0
% 3.42/1.01  fd_pseudo:                              0
% 3.42/1.01  fd_cond:                                0
% 3.42/1.01  fd_pseudo_cond:                         0
% 3.42/1.01  ac_symbols:                             0
% 3.42/1.01  
% 3.42/1.01  ------ Propositional Solver
% 3.42/1.01  
% 3.42/1.01  prop_solver_calls:                      34
% 3.42/1.01  prop_fast_solver_calls:                 240
% 3.42/1.01  smt_solver_calls:                       0
% 3.42/1.01  smt_fast_solver_calls:                  0
% 3.42/1.01  prop_num_of_clauses:                    2603
% 3.42/1.01  prop_preprocess_simplified:             4690
% 3.42/1.01  prop_fo_subsumed:                       1
% 3.42/1.01  prop_solver_time:                       0.
% 3.42/1.01  smt_solver_time:                        0.
% 3.42/1.01  smt_fast_solver_time:                   0.
% 3.42/1.01  prop_fast_solver_time:                  0.
% 3.42/1.01  prop_unsat_core_time:                   0.
% 3.42/1.01  
% 3.42/1.01  ------ QBF
% 3.42/1.01  
% 3.42/1.01  qbf_q_res:                              0
% 3.42/1.01  qbf_num_tautologies:                    0
% 3.42/1.01  qbf_prep_cycles:                        0
% 3.42/1.01  
% 3.42/1.01  ------ BMC1
% 3.42/1.01  
% 3.42/1.01  bmc1_current_bound:                     -1
% 3.42/1.01  bmc1_last_solved_bound:                 -1
% 3.42/1.01  bmc1_unsat_core_size:                   -1
% 3.42/1.01  bmc1_unsat_core_parents_size:           -1
% 3.42/1.01  bmc1_merge_next_fun:                    0
% 3.42/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.42/1.01  
% 3.42/1.01  ------ Instantiation
% 3.42/1.01  
% 3.42/1.01  inst_num_of_clauses:                    725
% 3.42/1.01  inst_num_in_passive:                    385
% 3.42/1.01  inst_num_in_active:                     328
% 3.42/1.01  inst_num_in_unprocessed:                11
% 3.42/1.01  inst_num_of_loops:                      350
% 3.42/1.01  inst_num_of_learning_restarts:          0
% 3.42/1.01  inst_num_moves_active_passive:          16
% 3.42/1.01  inst_lit_activity:                      0
% 3.42/1.01  inst_lit_activity_moves:                0
% 3.42/1.01  inst_num_tautologies:                   0
% 3.42/1.01  inst_num_prop_implied:                  0
% 3.42/1.01  inst_num_existing_simplified:           0
% 3.42/1.01  inst_num_eq_res_simplified:             0
% 3.42/1.01  inst_num_child_elim:                    0
% 3.42/1.01  inst_num_of_dismatching_blockings:      411
% 3.42/1.01  inst_num_of_non_proper_insts:           836
% 3.42/1.01  inst_num_of_duplicates:                 0
% 3.42/1.01  inst_inst_num_from_inst_to_res:         0
% 3.42/1.01  inst_dismatching_checking_time:         0.
% 3.42/1.01  
% 3.42/1.01  ------ Resolution
% 3.42/1.01  
% 3.42/1.01  res_num_of_clauses:                     0
% 3.42/1.01  res_num_in_passive:                     0
% 3.42/1.01  res_num_in_active:                      0
% 3.42/1.01  res_num_of_loops:                       43
% 3.42/1.01  res_forward_subset_subsumed:            102
% 3.42/1.01  res_backward_subset_subsumed:           0
% 3.42/1.01  res_forward_subsumed:                   0
% 3.42/1.01  res_backward_subsumed:                  0
% 3.42/1.01  res_forward_subsumption_resolution:     0
% 3.42/1.01  res_backward_subsumption_resolution:    0
% 3.42/1.01  res_clause_to_clause_subsumption:       1214
% 3.42/1.01  res_orphan_elimination:                 0
% 3.42/1.01  res_tautology_del:                      48
% 3.42/1.01  res_num_eq_res_simplified:              0
% 3.42/1.01  res_num_sel_changes:                    0
% 3.42/1.01  res_moves_from_active_to_pass:          0
% 3.42/1.01  
% 3.42/1.01  ------ Superposition
% 3.42/1.01  
% 3.42/1.01  sup_time_total:                         0.
% 3.42/1.01  sup_time_generating:                    0.
% 3.42/1.01  sup_time_sim_full:                      0.
% 3.42/1.01  sup_time_sim_immed:                     0.
% 3.42/1.01  
% 3.42/1.01  sup_num_of_clauses:                     168
% 3.42/1.01  sup_num_in_active:                      67
% 3.42/1.01  sup_num_in_passive:                     101
% 3.42/1.01  sup_num_of_loops:                       68
% 3.42/1.01  sup_fw_superposition:                   412
% 3.42/1.01  sup_bw_superposition:                   75
% 3.42/1.01  sup_immediate_simplified:               103
% 3.42/1.01  sup_given_eliminated:                   0
% 3.42/1.01  comparisons_done:                       0
% 3.42/1.01  comparisons_avoided:                    0
% 3.42/1.01  
% 3.42/1.01  ------ Simplifications
% 3.42/1.01  
% 3.42/1.01  
% 3.42/1.01  sim_fw_subset_subsumed:                 0
% 3.42/1.01  sim_bw_subset_subsumed:                 0
% 3.42/1.01  sim_fw_subsumed:                        74
% 3.42/1.01  sim_bw_subsumed:                        0
% 3.42/1.01  sim_fw_subsumption_res:                 0
% 3.42/1.01  sim_bw_subsumption_res:                 0
% 3.42/1.01  sim_tautology_del:                      14
% 3.42/1.01  sim_eq_tautology_del:                   1
% 3.42/1.01  sim_eq_res_simp:                        0
% 3.42/1.01  sim_fw_demodulated:                     100
% 3.42/1.01  sim_bw_demodulated:                     1
% 3.42/1.01  sim_light_normalised:                   41
% 3.42/1.01  sim_joinable_taut:                      0
% 3.42/1.01  sim_joinable_simp:                      0
% 3.42/1.01  sim_ac_normalised:                      0
% 3.42/1.01  sim_smt_subsumption:                    0
% 3.42/1.01  
%------------------------------------------------------------------------------
