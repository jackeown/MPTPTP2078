%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:51:45 EST 2020

% Result     : Timeout 59.02s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :   82 ( 266 expanded)
%              Number of clauses        :   45 (  92 expanded)
%              Number of leaves         :   11 (  56 expanded)
%              Depth                    :   18
%              Number of atoms          :  136 ( 540 expanded)
%              Number of equality atoms :   70 ( 169 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f19,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(X0,k1_relat_1(X1))
         => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f36,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f37,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f36])).

fof(f40,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
        & r1_tarski(X0,k1_relat_1(X1))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
      & r1_tarski(sK0,k1_relat_1(sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    & r1_tarski(sK0,k1_relat_1(sK1))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f37,f40])).

fof(f63,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f41])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_tarski(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f50,f53])).

fof(f62,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f57,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k1_setfam_1(k2_tarski(X0,k10_relat_1(X2,X1))) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f61,f53])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f66,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f49,f53])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f65,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(definition_unfolding,[],[f42,f53,f53])).

fof(f64,plain,(
    ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_723,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k7_relat_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_20,negated_conjecture,
    ( r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_714,plain,
    ( r1_tarski(sK0,k1_relat_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | k1_setfam_1(k2_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_726,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1510,plain,
    ( k1_setfam_1(k2_tarski(sK0,k1_relat_1(sK1))) = sK0 ),
    inference(superposition,[status(thm)],[c_714,c_726])).

cnf(c_21,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_713,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_14,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_720,plain,
    ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1363,plain,
    ( k10_relat_1(sK1,k2_relat_1(sK1)) = k1_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_713,c_720])).

cnf(c_18,plain,
    ( ~ v1_relat_1(X0)
    | k1_setfam_1(k2_tarski(X1,k10_relat_1(X0,X2))) = k10_relat_1(k7_relat_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_716,plain,
    ( k1_setfam_1(k2_tarski(X0,k10_relat_1(X1,X2))) = k10_relat_1(k7_relat_1(X1,X0),X2)
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1284,plain,
    ( k1_setfam_1(k2_tarski(X0,k10_relat_1(sK1,X1))) = k10_relat_1(k7_relat_1(sK1,X0),X1) ),
    inference(superposition,[status(thm)],[c_713,c_716])).

cnf(c_1785,plain,
    ( k10_relat_1(k7_relat_1(sK1,X0),k2_relat_1(sK1)) = k1_setfam_1(k2_tarski(X0,k1_relat_1(sK1))) ),
    inference(superposition,[status(thm)],[c_1363,c_1284])).

cnf(c_15,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k10_relat_1(X0,k2_relat_1(X0)))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_719,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k10_relat_1(X0,k2_relat_1(X0))) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3651,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X0,k1_relat_1(sK1))),k10_relat_1(k7_relat_1(sK1,X0),k2_relat_1(k7_relat_1(sK1,X0)))) = iProver_top
    | v1_relat_1(k7_relat_1(sK1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1785,c_719])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_722,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2383,plain,
    ( k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0) ),
    inference(superposition,[status(thm)],[c_713,c_722])).

cnf(c_3661,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X0,k1_relat_1(sK1))),k10_relat_1(k7_relat_1(sK1,X0),k9_relat_1(sK1,X0))) = iProver_top
    | v1_relat_1(k7_relat_1(sK1,X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3651,c_2383])).

cnf(c_4658,plain,
    ( r1_tarski(sK0,k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))) = iProver_top
    | v1_relat_1(k7_relat_1(sK1,sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1510,c_3661])).

cnf(c_4780,plain,
    ( k1_setfam_1(k2_tarski(sK0,k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)))) = sK0
    | v1_relat_1(k7_relat_1(sK1,sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4658,c_726])).

cnf(c_1362,plain,
    ( k10_relat_1(k7_relat_1(X0,X1),k2_relat_1(k7_relat_1(X0,X1))) = k1_relat_1(k7_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_723,c_720])).

cnf(c_7616,plain,
    ( k10_relat_1(k7_relat_1(sK1,X0),k2_relat_1(k7_relat_1(sK1,X0))) = k1_relat_1(k7_relat_1(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_713,c_1362])).

cnf(c_7617,plain,
    ( k10_relat_1(k7_relat_1(sK1,X0),k9_relat_1(sK1,X0)) = k1_relat_1(k7_relat_1(sK1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_7616,c_2383])).

cnf(c_7,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_727,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1788,plain,
    ( r1_tarski(k10_relat_1(k7_relat_1(sK1,X0),X1),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1284,c_727])).

cnf(c_1799,plain,
    ( k1_setfam_1(k2_tarski(k10_relat_1(k7_relat_1(sK1,X0),X1),X0)) = k10_relat_1(k7_relat_1(sK1,X0),X1) ),
    inference(superposition,[status(thm)],[c_1788,c_726])).

cnf(c_0,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_9096,plain,
    ( k1_setfam_1(k2_tarski(X0,k10_relat_1(k7_relat_1(sK1,X0),X1))) = k10_relat_1(k7_relat_1(sK1,X0),X1) ),
    inference(superposition,[status(thm)],[c_1799,c_0])).

cnf(c_229580,plain,
    ( k1_relat_1(k7_relat_1(sK1,sK0)) = sK0
    | v1_relat_1(k7_relat_1(sK1,sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4780,c_7617,c_9096])).

cnf(c_229582,plain,
    ( k1_relat_1(k7_relat_1(sK1,sK0)) = sK0
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_723,c_229580])).

cnf(c_22,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_230492,plain,
    ( k1_relat_1(k7_relat_1(sK1,sK0)) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_229582,c_22])).

cnf(c_1170,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_727])).

cnf(c_1786,plain,
    ( r1_tarski(k10_relat_1(k7_relat_1(sK1,X0),X1),k10_relat_1(sK1,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1284,c_1170])).

cnf(c_7959,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k10_relat_1(sK1,k9_relat_1(sK1,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_7617,c_1786])).

cnf(c_230566,plain,
    ( r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_230492,c_7959])).

cnf(c_19,negated_conjecture,
    ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_24,plain,
    ( r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_230566,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n002.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 11:23:22 EST 2020
% 0.19/0.33  % CPUTime    : 
% 0.19/0.34  % Running in FOF mode
% 59.02/7.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 59.02/7.99  
% 59.02/7.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 59.02/7.99  
% 59.02/7.99  ------  iProver source info
% 59.02/7.99  
% 59.02/7.99  git: date: 2020-06-30 10:37:57 +0100
% 59.02/7.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 59.02/7.99  git: non_committed_changes: false
% 59.02/7.99  git: last_make_outside_of_git: false
% 59.02/7.99  
% 59.02/7.99  ------ 
% 59.02/7.99  
% 59.02/7.99  ------ Input Options
% 59.02/7.99  
% 59.02/7.99  --out_options                           all
% 59.02/7.99  --tptp_safe_out                         true
% 59.02/7.99  --problem_path                          ""
% 59.02/7.99  --include_path                          ""
% 59.02/7.99  --clausifier                            res/vclausify_rel
% 59.02/7.99  --clausifier_options                    ""
% 59.02/7.99  --stdin                                 false
% 59.02/7.99  --stats_out                             all
% 59.02/7.99  
% 59.02/7.99  ------ General Options
% 59.02/7.99  
% 59.02/7.99  --fof                                   false
% 59.02/7.99  --time_out_real                         305.
% 59.02/7.99  --time_out_virtual                      -1.
% 59.02/7.99  --symbol_type_check                     false
% 59.02/7.99  --clausify_out                          false
% 59.02/7.99  --sig_cnt_out                           false
% 59.02/7.99  --trig_cnt_out                          false
% 59.02/7.99  --trig_cnt_out_tolerance                1.
% 59.02/7.99  --trig_cnt_out_sk_spl                   false
% 59.02/7.99  --abstr_cl_out                          false
% 59.02/7.99  
% 59.02/7.99  ------ Global Options
% 59.02/7.99  
% 59.02/7.99  --schedule                              default
% 59.02/7.99  --add_important_lit                     false
% 59.02/7.99  --prop_solver_per_cl                    1000
% 59.02/7.99  --min_unsat_core                        false
% 59.02/7.99  --soft_assumptions                      false
% 59.02/7.99  --soft_lemma_size                       3
% 59.02/7.99  --prop_impl_unit_size                   0
% 59.02/7.99  --prop_impl_unit                        []
% 59.02/7.99  --share_sel_clauses                     true
% 59.02/7.99  --reset_solvers                         false
% 59.02/7.99  --bc_imp_inh                            [conj_cone]
% 59.02/7.99  --conj_cone_tolerance                   3.
% 59.02/7.99  --extra_neg_conj                        none
% 59.02/7.99  --large_theory_mode                     true
% 59.02/7.99  --prolific_symb_bound                   200
% 59.02/7.99  --lt_threshold                          2000
% 59.02/7.99  --clause_weak_htbl                      true
% 59.02/7.99  --gc_record_bc_elim                     false
% 59.02/7.99  
% 59.02/7.99  ------ Preprocessing Options
% 59.02/7.99  
% 59.02/7.99  --preprocessing_flag                    true
% 59.02/7.99  --time_out_prep_mult                    0.1
% 59.02/7.99  --splitting_mode                        input
% 59.02/7.99  --splitting_grd                         true
% 59.02/7.99  --splitting_cvd                         false
% 59.02/7.99  --splitting_cvd_svl                     false
% 59.02/7.99  --splitting_nvd                         32
% 59.02/7.99  --sub_typing                            true
% 59.02/7.99  --prep_gs_sim                           true
% 59.02/7.99  --prep_unflatten                        true
% 59.02/7.99  --prep_res_sim                          true
% 59.02/7.99  --prep_upred                            true
% 59.02/7.99  --prep_sem_filter                       exhaustive
% 59.02/7.99  --prep_sem_filter_out                   false
% 59.02/7.99  --pred_elim                             true
% 59.02/7.99  --res_sim_input                         true
% 59.02/7.99  --eq_ax_congr_red                       true
% 59.02/7.99  --pure_diseq_elim                       true
% 59.02/7.99  --brand_transform                       false
% 59.02/7.99  --non_eq_to_eq                          false
% 59.02/7.99  --prep_def_merge                        true
% 59.02/7.99  --prep_def_merge_prop_impl              false
% 59.02/7.99  --prep_def_merge_mbd                    true
% 59.02/7.99  --prep_def_merge_tr_red                 false
% 59.02/7.99  --prep_def_merge_tr_cl                  false
% 59.02/7.99  --smt_preprocessing                     true
% 59.02/7.99  --smt_ac_axioms                         fast
% 59.02/7.99  --preprocessed_out                      false
% 59.02/7.99  --preprocessed_stats                    false
% 59.02/7.99  
% 59.02/7.99  ------ Abstraction refinement Options
% 59.02/7.99  
% 59.02/7.99  --abstr_ref                             []
% 59.02/7.99  --abstr_ref_prep                        false
% 59.02/7.99  --abstr_ref_until_sat                   false
% 59.02/7.99  --abstr_ref_sig_restrict                funpre
% 59.02/7.99  --abstr_ref_af_restrict_to_split_sk     false
% 59.02/7.99  --abstr_ref_under                       []
% 59.02/7.99  
% 59.02/7.99  ------ SAT Options
% 59.02/7.99  
% 59.02/7.99  --sat_mode                              false
% 59.02/7.99  --sat_fm_restart_options                ""
% 59.02/7.99  --sat_gr_def                            false
% 59.02/7.99  --sat_epr_types                         true
% 59.02/7.99  --sat_non_cyclic_types                  false
% 59.02/7.99  --sat_finite_models                     false
% 59.02/7.99  --sat_fm_lemmas                         false
% 59.02/7.99  --sat_fm_prep                           false
% 59.02/7.99  --sat_fm_uc_incr                        true
% 59.02/7.99  --sat_out_model                         small
% 59.02/7.99  --sat_out_clauses                       false
% 59.02/7.99  
% 59.02/7.99  ------ QBF Options
% 59.02/7.99  
% 59.02/7.99  --qbf_mode                              false
% 59.02/7.99  --qbf_elim_univ                         false
% 59.02/7.99  --qbf_dom_inst                          none
% 59.02/7.99  --qbf_dom_pre_inst                      false
% 59.02/7.99  --qbf_sk_in                             false
% 59.02/7.99  --qbf_pred_elim                         true
% 59.02/7.99  --qbf_split                             512
% 59.02/7.99  
% 59.02/7.99  ------ BMC1 Options
% 59.02/7.99  
% 59.02/7.99  --bmc1_incremental                      false
% 59.02/7.99  --bmc1_axioms                           reachable_all
% 59.02/7.99  --bmc1_min_bound                        0
% 59.02/7.99  --bmc1_max_bound                        -1
% 59.02/7.99  --bmc1_max_bound_default                -1
% 59.02/7.99  --bmc1_symbol_reachability              true
% 59.02/7.99  --bmc1_property_lemmas                  false
% 59.02/7.99  --bmc1_k_induction                      false
% 59.02/7.99  --bmc1_non_equiv_states                 false
% 59.02/7.99  --bmc1_deadlock                         false
% 59.02/7.99  --bmc1_ucm                              false
% 59.02/7.99  --bmc1_add_unsat_core                   none
% 59.02/7.99  --bmc1_unsat_core_children              false
% 59.02/7.99  --bmc1_unsat_core_extrapolate_axioms    false
% 59.02/7.99  --bmc1_out_stat                         full
% 59.02/7.99  --bmc1_ground_init                      false
% 59.02/7.99  --bmc1_pre_inst_next_state              false
% 59.02/7.99  --bmc1_pre_inst_state                   false
% 59.02/7.99  --bmc1_pre_inst_reach_state             false
% 59.02/7.99  --bmc1_out_unsat_core                   false
% 59.02/7.99  --bmc1_aig_witness_out                  false
% 59.02/7.99  --bmc1_verbose                          false
% 59.02/7.99  --bmc1_dump_clauses_tptp                false
% 59.02/7.99  --bmc1_dump_unsat_core_tptp             false
% 59.02/7.99  --bmc1_dump_file                        -
% 59.02/7.99  --bmc1_ucm_expand_uc_limit              128
% 59.02/7.99  --bmc1_ucm_n_expand_iterations          6
% 59.02/7.99  --bmc1_ucm_extend_mode                  1
% 59.02/7.99  --bmc1_ucm_init_mode                    2
% 59.02/7.99  --bmc1_ucm_cone_mode                    none
% 59.02/7.99  --bmc1_ucm_reduced_relation_type        0
% 59.02/7.99  --bmc1_ucm_relax_model                  4
% 59.02/7.99  --bmc1_ucm_full_tr_after_sat            true
% 59.02/7.99  --bmc1_ucm_expand_neg_assumptions       false
% 59.02/7.99  --bmc1_ucm_layered_model                none
% 59.02/7.99  --bmc1_ucm_max_lemma_size               10
% 59.02/7.99  
% 59.02/7.99  ------ AIG Options
% 59.02/7.99  
% 59.02/7.99  --aig_mode                              false
% 59.02/7.99  
% 59.02/7.99  ------ Instantiation Options
% 59.02/7.99  
% 59.02/7.99  --instantiation_flag                    true
% 59.02/7.99  --inst_sos_flag                         true
% 59.02/7.99  --inst_sos_phase                        true
% 59.02/7.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 59.02/7.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 59.02/7.99  --inst_lit_sel_side                     num_symb
% 59.02/7.99  --inst_solver_per_active                1400
% 59.02/7.99  --inst_solver_calls_frac                1.
% 59.02/7.99  --inst_passive_queue_type               priority_queues
% 59.02/7.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 59.02/7.99  --inst_passive_queues_freq              [25;2]
% 59.02/7.99  --inst_dismatching                      true
% 59.02/7.99  --inst_eager_unprocessed_to_passive     true
% 59.02/7.99  --inst_prop_sim_given                   true
% 59.02/7.99  --inst_prop_sim_new                     false
% 59.02/7.99  --inst_subs_new                         false
% 59.02/7.99  --inst_eq_res_simp                      false
% 59.02/7.99  --inst_subs_given                       false
% 59.02/7.99  --inst_orphan_elimination               true
% 59.02/7.99  --inst_learning_loop_flag               true
% 59.02/7.99  --inst_learning_start                   3000
% 59.02/7.99  --inst_learning_factor                  2
% 59.02/7.99  --inst_start_prop_sim_after_learn       3
% 59.02/7.99  --inst_sel_renew                        solver
% 59.02/7.99  --inst_lit_activity_flag                true
% 59.02/7.99  --inst_restr_to_given                   false
% 59.02/7.99  --inst_activity_threshold               500
% 59.02/7.99  --inst_out_proof                        true
% 59.02/7.99  
% 59.02/7.99  ------ Resolution Options
% 59.02/7.99  
% 59.02/7.99  --resolution_flag                       true
% 59.02/7.99  --res_lit_sel                           adaptive
% 59.02/7.99  --res_lit_sel_side                      none
% 59.02/7.99  --res_ordering                          kbo
% 59.02/7.99  --res_to_prop_solver                    active
% 59.02/7.99  --res_prop_simpl_new                    false
% 59.02/7.99  --res_prop_simpl_given                  true
% 59.02/7.99  --res_passive_queue_type                priority_queues
% 59.02/7.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 59.02/7.99  --res_passive_queues_freq               [15;5]
% 59.02/7.99  --res_forward_subs                      full
% 59.02/7.99  --res_backward_subs                     full
% 59.02/7.99  --res_forward_subs_resolution           true
% 59.02/7.99  --res_backward_subs_resolution          true
% 59.02/7.99  --res_orphan_elimination                true
% 59.02/7.99  --res_time_limit                        2.
% 59.02/7.99  --res_out_proof                         true
% 59.02/7.99  
% 59.02/7.99  ------ Superposition Options
% 59.02/7.99  
% 59.02/7.99  --superposition_flag                    true
% 59.02/7.99  --sup_passive_queue_type                priority_queues
% 59.02/7.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 59.02/7.99  --sup_passive_queues_freq               [8;1;4]
% 59.02/7.99  --demod_completeness_check              fast
% 59.02/7.99  --demod_use_ground                      true
% 59.02/7.99  --sup_to_prop_solver                    passive
% 59.02/7.99  --sup_prop_simpl_new                    true
% 59.02/7.99  --sup_prop_simpl_given                  true
% 59.02/7.99  --sup_fun_splitting                     true
% 59.02/7.99  --sup_smt_interval                      50000
% 59.02/7.99  
% 59.02/7.99  ------ Superposition Simplification Setup
% 59.02/7.99  
% 59.02/7.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 59.02/7.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 59.02/7.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 59.02/7.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 59.02/7.99  --sup_full_triv                         [TrivRules;PropSubs]
% 59.02/7.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 59.02/7.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 59.02/7.99  --sup_immed_triv                        [TrivRules]
% 59.02/7.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 59.02/7.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 59.02/7.99  --sup_immed_bw_main                     []
% 59.02/7.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 59.02/7.99  --sup_input_triv                        [Unflattening;TrivRules]
% 59.02/7.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 59.02/7.99  --sup_input_bw                          []
% 59.02/7.99  
% 59.02/7.99  ------ Combination Options
% 59.02/7.99  
% 59.02/7.99  --comb_res_mult                         3
% 59.02/7.99  --comb_sup_mult                         2
% 59.02/7.99  --comb_inst_mult                        10
% 59.02/7.99  
% 59.02/7.99  ------ Debug Options
% 59.02/7.99  
% 59.02/7.99  --dbg_backtrace                         false
% 59.02/7.99  --dbg_dump_prop_clauses                 false
% 59.02/7.99  --dbg_dump_prop_clauses_file            -
% 59.02/7.99  --dbg_out_stat                          false
% 59.02/7.99  ------ Parsing...
% 59.02/7.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 59.02/7.99  
% 59.02/7.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 59.02/7.99  
% 59.02/7.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 59.02/7.99  
% 59.02/7.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 59.02/7.99  ------ Proving...
% 59.02/7.99  ------ Problem Properties 
% 59.02/7.99  
% 59.02/7.99  
% 59.02/7.99  clauses                                 21
% 59.02/7.99  conjectures                             3
% 59.02/7.99  EPR                                     3
% 59.02/7.99  Horn                                    21
% 59.02/7.99  unary                                   7
% 59.02/7.99  binary                                  11
% 59.02/7.99  lits                                    38
% 59.02/7.99  lits eq                                 7
% 59.02/7.99  fd_pure                                 0
% 59.02/7.99  fd_pseudo                               0
% 59.02/7.99  fd_cond                                 0
% 59.02/7.99  fd_pseudo_cond                          1
% 59.02/7.99  AC symbols                              0
% 59.02/7.99  
% 59.02/7.99  ------ Schedule dynamic 5 is on 
% 59.02/7.99  
% 59.02/7.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 59.02/7.99  
% 59.02/7.99  
% 59.02/7.99  ------ 
% 59.02/7.99  Current options:
% 59.02/7.99  ------ 
% 59.02/7.99  
% 59.02/7.99  ------ Input Options
% 59.02/7.99  
% 59.02/7.99  --out_options                           all
% 59.02/7.99  --tptp_safe_out                         true
% 59.02/7.99  --problem_path                          ""
% 59.02/7.99  --include_path                          ""
% 59.02/7.99  --clausifier                            res/vclausify_rel
% 59.02/7.99  --clausifier_options                    ""
% 59.02/7.99  --stdin                                 false
% 59.02/7.99  --stats_out                             all
% 59.02/7.99  
% 59.02/7.99  ------ General Options
% 59.02/7.99  
% 59.02/7.99  --fof                                   false
% 59.02/7.99  --time_out_real                         305.
% 59.02/7.99  --time_out_virtual                      -1.
% 59.02/7.99  --symbol_type_check                     false
% 59.02/7.99  --clausify_out                          false
% 59.02/7.99  --sig_cnt_out                           false
% 59.02/7.99  --trig_cnt_out                          false
% 59.02/7.99  --trig_cnt_out_tolerance                1.
% 59.02/7.99  --trig_cnt_out_sk_spl                   false
% 59.02/7.99  --abstr_cl_out                          false
% 59.02/7.99  
% 59.02/7.99  ------ Global Options
% 59.02/7.99  
% 59.02/7.99  --schedule                              default
% 59.02/7.99  --add_important_lit                     false
% 59.02/7.99  --prop_solver_per_cl                    1000
% 59.02/7.99  --min_unsat_core                        false
% 59.02/7.99  --soft_assumptions                      false
% 59.02/7.99  --soft_lemma_size                       3
% 59.02/7.99  --prop_impl_unit_size                   0
% 59.02/7.99  --prop_impl_unit                        []
% 59.02/7.99  --share_sel_clauses                     true
% 59.02/7.99  --reset_solvers                         false
% 59.02/7.99  --bc_imp_inh                            [conj_cone]
% 59.02/7.99  --conj_cone_tolerance                   3.
% 59.02/7.99  --extra_neg_conj                        none
% 59.02/7.99  --large_theory_mode                     true
% 59.02/7.99  --prolific_symb_bound                   200
% 59.02/7.99  --lt_threshold                          2000
% 59.02/7.99  --clause_weak_htbl                      true
% 59.02/7.99  --gc_record_bc_elim                     false
% 59.02/7.99  
% 59.02/7.99  ------ Preprocessing Options
% 59.02/7.99  
% 59.02/7.99  --preprocessing_flag                    true
% 59.02/7.99  --time_out_prep_mult                    0.1
% 59.02/7.99  --splitting_mode                        input
% 59.02/7.99  --splitting_grd                         true
% 59.02/7.99  --splitting_cvd                         false
% 59.02/7.99  --splitting_cvd_svl                     false
% 59.02/7.99  --splitting_nvd                         32
% 59.02/7.99  --sub_typing                            true
% 59.02/7.99  --prep_gs_sim                           true
% 59.02/7.99  --prep_unflatten                        true
% 59.02/7.99  --prep_res_sim                          true
% 59.02/7.99  --prep_upred                            true
% 59.02/7.99  --prep_sem_filter                       exhaustive
% 59.02/7.99  --prep_sem_filter_out                   false
% 59.02/7.99  --pred_elim                             true
% 59.02/7.99  --res_sim_input                         true
% 59.02/7.99  --eq_ax_congr_red                       true
% 59.02/7.99  --pure_diseq_elim                       true
% 59.02/7.99  --brand_transform                       false
% 59.02/7.99  --non_eq_to_eq                          false
% 59.02/7.99  --prep_def_merge                        true
% 59.02/7.99  --prep_def_merge_prop_impl              false
% 59.02/7.99  --prep_def_merge_mbd                    true
% 59.02/7.99  --prep_def_merge_tr_red                 false
% 59.02/7.99  --prep_def_merge_tr_cl                  false
% 59.02/7.99  --smt_preprocessing                     true
% 59.02/7.99  --smt_ac_axioms                         fast
% 59.02/7.99  --preprocessed_out                      false
% 59.02/7.99  --preprocessed_stats                    false
% 59.02/7.99  
% 59.02/7.99  ------ Abstraction refinement Options
% 59.02/7.99  
% 59.02/7.99  --abstr_ref                             []
% 59.02/7.99  --abstr_ref_prep                        false
% 59.02/7.99  --abstr_ref_until_sat                   false
% 59.02/7.99  --abstr_ref_sig_restrict                funpre
% 59.02/7.99  --abstr_ref_af_restrict_to_split_sk     false
% 59.02/7.99  --abstr_ref_under                       []
% 59.02/7.99  
% 59.02/7.99  ------ SAT Options
% 59.02/7.99  
% 59.02/7.99  --sat_mode                              false
% 59.02/7.99  --sat_fm_restart_options                ""
% 59.02/7.99  --sat_gr_def                            false
% 59.02/7.99  --sat_epr_types                         true
% 59.02/7.99  --sat_non_cyclic_types                  false
% 59.02/7.99  --sat_finite_models                     false
% 59.02/7.99  --sat_fm_lemmas                         false
% 59.02/7.99  --sat_fm_prep                           false
% 59.02/7.99  --sat_fm_uc_incr                        true
% 59.02/7.99  --sat_out_model                         small
% 59.02/7.99  --sat_out_clauses                       false
% 59.02/7.99  
% 59.02/7.99  ------ QBF Options
% 59.02/7.99  
% 59.02/7.99  --qbf_mode                              false
% 59.02/7.99  --qbf_elim_univ                         false
% 59.02/7.99  --qbf_dom_inst                          none
% 59.02/7.99  --qbf_dom_pre_inst                      false
% 59.02/7.99  --qbf_sk_in                             false
% 59.02/7.99  --qbf_pred_elim                         true
% 59.02/7.99  --qbf_split                             512
% 59.02/7.99  
% 59.02/7.99  ------ BMC1 Options
% 59.02/7.99  
% 59.02/7.99  --bmc1_incremental                      false
% 59.02/7.99  --bmc1_axioms                           reachable_all
% 59.02/7.99  --bmc1_min_bound                        0
% 59.02/7.99  --bmc1_max_bound                        -1
% 59.02/7.99  --bmc1_max_bound_default                -1
% 59.02/7.99  --bmc1_symbol_reachability              true
% 59.02/7.99  --bmc1_property_lemmas                  false
% 59.02/7.99  --bmc1_k_induction                      false
% 59.02/7.99  --bmc1_non_equiv_states                 false
% 59.02/7.99  --bmc1_deadlock                         false
% 59.02/7.99  --bmc1_ucm                              false
% 59.02/7.99  --bmc1_add_unsat_core                   none
% 59.02/7.99  --bmc1_unsat_core_children              false
% 59.02/7.99  --bmc1_unsat_core_extrapolate_axioms    false
% 59.02/7.99  --bmc1_out_stat                         full
% 59.02/7.99  --bmc1_ground_init                      false
% 59.02/7.99  --bmc1_pre_inst_next_state              false
% 59.02/7.99  --bmc1_pre_inst_state                   false
% 59.02/7.99  --bmc1_pre_inst_reach_state             false
% 59.02/7.99  --bmc1_out_unsat_core                   false
% 59.02/7.99  --bmc1_aig_witness_out                  false
% 59.02/7.99  --bmc1_verbose                          false
% 59.02/7.99  --bmc1_dump_clauses_tptp                false
% 59.02/7.99  --bmc1_dump_unsat_core_tptp             false
% 59.02/7.99  --bmc1_dump_file                        -
% 59.02/7.99  --bmc1_ucm_expand_uc_limit              128
% 59.02/7.99  --bmc1_ucm_n_expand_iterations          6
% 59.02/7.99  --bmc1_ucm_extend_mode                  1
% 59.02/7.99  --bmc1_ucm_init_mode                    2
% 59.02/7.99  --bmc1_ucm_cone_mode                    none
% 59.02/7.99  --bmc1_ucm_reduced_relation_type        0
% 59.02/7.99  --bmc1_ucm_relax_model                  4
% 59.02/7.99  --bmc1_ucm_full_tr_after_sat            true
% 59.02/7.99  --bmc1_ucm_expand_neg_assumptions       false
% 59.02/7.99  --bmc1_ucm_layered_model                none
% 59.02/7.99  --bmc1_ucm_max_lemma_size               10
% 59.02/7.99  
% 59.02/7.99  ------ AIG Options
% 59.02/7.99  
% 59.02/7.99  --aig_mode                              false
% 59.02/7.99  
% 59.02/7.99  ------ Instantiation Options
% 59.02/7.99  
% 59.02/7.99  --instantiation_flag                    true
% 59.02/7.99  --inst_sos_flag                         true
% 59.02/7.99  --inst_sos_phase                        true
% 59.02/7.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 59.02/7.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 59.02/7.99  --inst_lit_sel_side                     none
% 59.02/7.99  --inst_solver_per_active                1400
% 59.02/7.99  --inst_solver_calls_frac                1.
% 59.02/7.99  --inst_passive_queue_type               priority_queues
% 59.02/7.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 59.02/7.99  --inst_passive_queues_freq              [25;2]
% 59.02/7.99  --inst_dismatching                      true
% 59.02/7.99  --inst_eager_unprocessed_to_passive     true
% 59.02/7.99  --inst_prop_sim_given                   true
% 59.02/7.99  --inst_prop_sim_new                     false
% 59.02/7.99  --inst_subs_new                         false
% 59.02/7.99  --inst_eq_res_simp                      false
% 59.02/7.99  --inst_subs_given                       false
% 59.02/7.99  --inst_orphan_elimination               true
% 59.02/7.99  --inst_learning_loop_flag               true
% 59.02/7.99  --inst_learning_start                   3000
% 59.02/7.99  --inst_learning_factor                  2
% 59.02/7.99  --inst_start_prop_sim_after_learn       3
% 59.02/7.99  --inst_sel_renew                        solver
% 59.02/7.99  --inst_lit_activity_flag                true
% 59.02/7.99  --inst_restr_to_given                   false
% 59.02/7.99  --inst_activity_threshold               500
% 59.02/7.99  --inst_out_proof                        true
% 59.02/7.99  
% 59.02/7.99  ------ Resolution Options
% 59.02/7.99  
% 59.02/7.99  --resolution_flag                       false
% 59.02/7.99  --res_lit_sel                           adaptive
% 59.02/7.99  --res_lit_sel_side                      none
% 59.02/7.99  --res_ordering                          kbo
% 59.02/7.99  --res_to_prop_solver                    active
% 59.02/7.99  --res_prop_simpl_new                    false
% 59.02/7.99  --res_prop_simpl_given                  true
% 59.02/7.99  --res_passive_queue_type                priority_queues
% 59.02/7.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 59.02/7.99  --res_passive_queues_freq               [15;5]
% 59.02/7.99  --res_forward_subs                      full
% 59.02/7.99  --res_backward_subs                     full
% 59.02/7.99  --res_forward_subs_resolution           true
% 59.02/7.99  --res_backward_subs_resolution          true
% 59.02/7.99  --res_orphan_elimination                true
% 59.02/7.99  --res_time_limit                        2.
% 59.02/7.99  --res_out_proof                         true
% 59.02/7.99  
% 59.02/7.99  ------ Superposition Options
% 59.02/7.99  
% 59.02/7.99  --superposition_flag                    true
% 59.02/7.99  --sup_passive_queue_type                priority_queues
% 59.02/7.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 59.02/7.99  --sup_passive_queues_freq               [8;1;4]
% 59.02/7.99  --demod_completeness_check              fast
% 59.02/7.99  --demod_use_ground                      true
% 59.02/7.99  --sup_to_prop_solver                    passive
% 59.02/7.99  --sup_prop_simpl_new                    true
% 59.02/7.99  --sup_prop_simpl_given                  true
% 59.02/7.99  --sup_fun_splitting                     true
% 59.02/7.99  --sup_smt_interval                      50000
% 59.02/7.99  
% 59.02/7.99  ------ Superposition Simplification Setup
% 59.02/7.99  
% 59.02/7.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 59.02/7.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 59.02/7.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 59.02/7.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 59.02/7.99  --sup_full_triv                         [TrivRules;PropSubs]
% 59.02/7.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 59.02/7.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 59.02/7.99  --sup_immed_triv                        [TrivRules]
% 59.02/7.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 59.02/7.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 59.02/7.99  --sup_immed_bw_main                     []
% 59.02/7.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 59.02/7.99  --sup_input_triv                        [Unflattening;TrivRules]
% 59.02/7.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 59.02/7.99  --sup_input_bw                          []
% 59.02/7.99  
% 59.02/7.99  ------ Combination Options
% 59.02/7.99  
% 59.02/7.99  --comb_res_mult                         3
% 59.02/7.99  --comb_sup_mult                         2
% 59.02/7.99  --comb_inst_mult                        10
% 59.02/7.99  
% 59.02/7.99  ------ Debug Options
% 59.02/7.99  
% 59.02/7.99  --dbg_backtrace                         false
% 59.02/7.99  --dbg_dump_prop_clauses                 false
% 59.02/7.99  --dbg_dump_prop_clauses_file            -
% 59.02/7.99  --dbg_out_stat                          false
% 59.02/7.99  
% 59.02/7.99  
% 59.02/7.99  
% 59.02/7.99  
% 59.02/7.99  ------ Proving...
% 59.02/7.99  
% 59.02/7.99  
% 59.02/7.99  % SZS status Theorem for theBenchmark.p
% 59.02/7.99  
% 59.02/7.99  % SZS output start CNFRefutation for theBenchmark.p
% 59.02/7.99  
% 59.02/7.99  fof(f11,axiom,(
% 59.02/7.99    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 59.02/7.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.02/7.99  
% 59.02/7.99  fof(f27,plain,(
% 59.02/7.99    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 59.02/7.99    inference(ennf_transformation,[],[f11])).
% 59.02/7.99  
% 59.02/7.99  fof(f54,plain,(
% 59.02/7.99    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 59.02/7.99    inference(cnf_transformation,[],[f27])).
% 59.02/7.99  
% 59.02/7.99  fof(f19,conjecture,(
% 59.02/7.99    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 59.02/7.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.02/7.99  
% 59.02/7.99  fof(f20,negated_conjecture,(
% 59.02/7.99    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 59.02/7.99    inference(negated_conjecture,[],[f19])).
% 59.02/7.99  
% 59.02/7.99  fof(f36,plain,(
% 59.02/7.99    ? [X0,X1] : ((~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 59.02/7.99    inference(ennf_transformation,[],[f20])).
% 59.02/7.99  
% 59.02/7.99  fof(f37,plain,(
% 59.02/7.99    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1))),
% 59.02/7.99    inference(flattening,[],[f36])).
% 59.02/7.99  
% 59.02/7.99  fof(f40,plain,(
% 59.02/7.99    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1)) => (~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1))),
% 59.02/7.99    introduced(choice_axiom,[])).
% 59.02/7.99  
% 59.02/7.99  fof(f41,plain,(
% 59.02/7.99    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1)),
% 59.02/7.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f37,f40])).
% 59.02/7.99  
% 59.02/7.99  fof(f63,plain,(
% 59.02/7.99    r1_tarski(sK0,k1_relat_1(sK1))),
% 59.02/7.99    inference(cnf_transformation,[],[f41])).
% 59.02/7.99  
% 59.02/7.99  fof(f7,axiom,(
% 59.02/7.99    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 59.02/7.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.02/7.99  
% 59.02/7.99  fof(f24,plain,(
% 59.02/7.99    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 59.02/7.99    inference(ennf_transformation,[],[f7])).
% 59.02/7.99  
% 59.02/7.99  fof(f50,plain,(
% 59.02/7.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 59.02/7.99    inference(cnf_transformation,[],[f24])).
% 59.02/7.99  
% 59.02/7.99  fof(f10,axiom,(
% 59.02/7.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 59.02/7.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.02/7.99  
% 59.02/7.99  fof(f53,plain,(
% 59.02/7.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 59.02/7.99    inference(cnf_transformation,[],[f10])).
% 59.02/7.99  
% 59.02/7.99  fof(f67,plain,(
% 59.02/7.99    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 59.02/7.99    inference(definition_unfolding,[],[f50,f53])).
% 59.02/7.99  
% 59.02/7.99  fof(f62,plain,(
% 59.02/7.99    v1_relat_1(sK1)),
% 59.02/7.99    inference(cnf_transformation,[],[f41])).
% 59.02/7.99  
% 59.02/7.99  fof(f14,axiom,(
% 59.02/7.99    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 59.02/7.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.02/7.99  
% 59.02/7.99  fof(f30,plain,(
% 59.02/7.99    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 59.02/7.99    inference(ennf_transformation,[],[f14])).
% 59.02/7.99  
% 59.02/7.99  fof(f57,plain,(
% 59.02/7.99    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 59.02/7.99    inference(cnf_transformation,[],[f30])).
% 59.02/7.99  
% 59.02/7.99  fof(f18,axiom,(
% 59.02/7.99    ! [X0,X1,X2] : (v1_relat_1(X2) => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1))),
% 59.02/7.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.02/7.99  
% 59.02/7.99  fof(f35,plain,(
% 59.02/7.99    ! [X0,X1,X2] : (k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2))),
% 59.02/7.99    inference(ennf_transformation,[],[f18])).
% 59.02/7.99  
% 59.02/7.99  fof(f61,plain,(
% 59.02/7.99    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 59.02/7.99    inference(cnf_transformation,[],[f35])).
% 59.02/7.99  
% 59.02/7.99  fof(f68,plain,(
% 59.02/7.99    ( ! [X2,X0,X1] : (k1_setfam_1(k2_tarski(X0,k10_relat_1(X2,X1))) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 59.02/7.99    inference(definition_unfolding,[],[f61,f53])).
% 59.02/7.99  
% 59.02/7.99  fof(f15,axiom,(
% 59.02/7.99    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))))),
% 59.02/7.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.02/7.99  
% 59.02/7.99  fof(f31,plain,(
% 59.02/7.99    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))) | ~v1_relat_1(X1))),
% 59.02/7.99    inference(ennf_transformation,[],[f15])).
% 59.02/7.99  
% 59.02/7.99  fof(f58,plain,(
% 59.02/7.99    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))) | ~v1_relat_1(X1)) )),
% 59.02/7.99    inference(cnf_transformation,[],[f31])).
% 59.02/7.99  
% 59.02/7.99  fof(f12,axiom,(
% 59.02/7.99    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 59.02/7.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.02/7.99  
% 59.02/7.99  fof(f28,plain,(
% 59.02/7.99    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 59.02/7.99    inference(ennf_transformation,[],[f12])).
% 59.02/7.99  
% 59.02/7.99  fof(f55,plain,(
% 59.02/7.99    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 59.02/7.99    inference(cnf_transformation,[],[f28])).
% 59.02/7.99  
% 59.02/7.99  fof(f6,axiom,(
% 59.02/7.99    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 59.02/7.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.02/7.99  
% 59.02/7.99  fof(f49,plain,(
% 59.02/7.99    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 59.02/7.99    inference(cnf_transformation,[],[f6])).
% 59.02/7.99  
% 59.02/7.99  fof(f66,plain,(
% 59.02/7.99    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)) )),
% 59.02/7.99    inference(definition_unfolding,[],[f49,f53])).
% 59.02/7.99  
% 59.02/7.99  fof(f1,axiom,(
% 59.02/7.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 59.02/7.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.02/7.99  
% 59.02/7.99  fof(f42,plain,(
% 59.02/7.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 59.02/7.99    inference(cnf_transformation,[],[f1])).
% 59.02/7.99  
% 59.02/7.99  fof(f65,plain,(
% 59.02/7.99    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k1_setfam_1(k2_tarski(X1,X0))) )),
% 59.02/7.99    inference(definition_unfolding,[],[f42,f53,f53])).
% 59.02/7.99  
% 59.02/7.99  fof(f64,plain,(
% 59.02/7.99    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 59.02/7.99    inference(cnf_transformation,[],[f41])).
% 59.02/7.99  
% 59.02/7.99  cnf(c_11,plain,
% 59.02/7.99      ( ~ v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1)) ),
% 59.02/7.99      inference(cnf_transformation,[],[f54]) ).
% 59.02/7.99  
% 59.02/7.99  cnf(c_723,plain,
% 59.02/7.99      ( v1_relat_1(X0) != iProver_top
% 59.02/7.99      | v1_relat_1(k7_relat_1(X0,X1)) = iProver_top ),
% 59.02/7.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 59.02/7.99  
% 59.02/7.99  cnf(c_20,negated_conjecture,
% 59.02/7.99      ( r1_tarski(sK0,k1_relat_1(sK1)) ),
% 59.02/7.99      inference(cnf_transformation,[],[f63]) ).
% 59.02/7.99  
% 59.02/7.99  cnf(c_714,plain,
% 59.02/7.99      ( r1_tarski(sK0,k1_relat_1(sK1)) = iProver_top ),
% 59.02/7.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 59.02/7.99  
% 59.02/7.99  cnf(c_8,plain,
% 59.02/7.99      ( ~ r1_tarski(X0,X1) | k1_setfam_1(k2_tarski(X0,X1)) = X0 ),
% 59.02/7.99      inference(cnf_transformation,[],[f67]) ).
% 59.02/7.99  
% 59.02/7.99  cnf(c_726,plain,
% 59.02/7.99      ( k1_setfam_1(k2_tarski(X0,X1)) = X0
% 59.02/7.99      | r1_tarski(X0,X1) != iProver_top ),
% 59.02/7.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 59.02/7.99  
% 59.02/7.99  cnf(c_1510,plain,
% 59.02/7.99      ( k1_setfam_1(k2_tarski(sK0,k1_relat_1(sK1))) = sK0 ),
% 59.02/7.99      inference(superposition,[status(thm)],[c_714,c_726]) ).
% 59.02/7.99  
% 59.02/7.99  cnf(c_21,negated_conjecture,
% 59.02/7.99      ( v1_relat_1(sK1) ),
% 59.02/7.99      inference(cnf_transformation,[],[f62]) ).
% 59.02/7.99  
% 59.02/7.99  cnf(c_713,plain,
% 59.02/7.99      ( v1_relat_1(sK1) = iProver_top ),
% 59.02/7.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 59.02/7.99  
% 59.02/7.99  cnf(c_14,plain,
% 59.02/7.99      ( ~ v1_relat_1(X0)
% 59.02/7.99      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
% 59.02/7.99      inference(cnf_transformation,[],[f57]) ).
% 59.02/7.99  
% 59.02/7.99  cnf(c_720,plain,
% 59.02/7.99      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
% 59.02/7.99      | v1_relat_1(X0) != iProver_top ),
% 59.02/7.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 59.02/7.99  
% 59.02/7.99  cnf(c_1363,plain,
% 59.02/7.99      ( k10_relat_1(sK1,k2_relat_1(sK1)) = k1_relat_1(sK1) ),
% 59.02/7.99      inference(superposition,[status(thm)],[c_713,c_720]) ).
% 59.02/7.99  
% 59.02/7.99  cnf(c_18,plain,
% 59.02/7.99      ( ~ v1_relat_1(X0)
% 59.02/7.99      | k1_setfam_1(k2_tarski(X1,k10_relat_1(X0,X2))) = k10_relat_1(k7_relat_1(X0,X1),X2) ),
% 59.02/7.99      inference(cnf_transformation,[],[f68]) ).
% 59.02/7.99  
% 59.02/7.99  cnf(c_716,plain,
% 59.02/7.99      ( k1_setfam_1(k2_tarski(X0,k10_relat_1(X1,X2))) = k10_relat_1(k7_relat_1(X1,X0),X2)
% 59.02/7.99      | v1_relat_1(X1) != iProver_top ),
% 59.02/7.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 59.02/7.99  
% 59.02/7.99  cnf(c_1284,plain,
% 59.02/7.99      ( k1_setfam_1(k2_tarski(X0,k10_relat_1(sK1,X1))) = k10_relat_1(k7_relat_1(sK1,X0),X1) ),
% 59.02/7.99      inference(superposition,[status(thm)],[c_713,c_716]) ).
% 59.02/7.99  
% 59.02/7.99  cnf(c_1785,plain,
% 59.02/7.99      ( k10_relat_1(k7_relat_1(sK1,X0),k2_relat_1(sK1)) = k1_setfam_1(k2_tarski(X0,k1_relat_1(sK1))) ),
% 59.02/7.99      inference(superposition,[status(thm)],[c_1363,c_1284]) ).
% 59.02/7.99  
% 59.02/7.99  cnf(c_15,plain,
% 59.02/7.99      ( r1_tarski(k10_relat_1(X0,X1),k10_relat_1(X0,k2_relat_1(X0)))
% 59.02/7.99      | ~ v1_relat_1(X0) ),
% 59.02/7.99      inference(cnf_transformation,[],[f58]) ).
% 59.02/7.99  
% 59.02/7.99  cnf(c_719,plain,
% 59.02/7.99      ( r1_tarski(k10_relat_1(X0,X1),k10_relat_1(X0,k2_relat_1(X0))) = iProver_top
% 59.02/7.99      | v1_relat_1(X0) != iProver_top ),
% 59.02/7.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 59.02/7.99  
% 59.02/7.99  cnf(c_3651,plain,
% 59.02/7.99      ( r1_tarski(k1_setfam_1(k2_tarski(X0,k1_relat_1(sK1))),k10_relat_1(k7_relat_1(sK1,X0),k2_relat_1(k7_relat_1(sK1,X0)))) = iProver_top
% 59.02/7.99      | v1_relat_1(k7_relat_1(sK1,X0)) != iProver_top ),
% 59.02/7.99      inference(superposition,[status(thm)],[c_1785,c_719]) ).
% 59.02/7.99  
% 59.02/7.99  cnf(c_12,plain,
% 59.02/7.99      ( ~ v1_relat_1(X0)
% 59.02/7.99      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 59.02/7.99      inference(cnf_transformation,[],[f55]) ).
% 59.02/7.99  
% 59.02/7.99  cnf(c_722,plain,
% 59.02/7.99      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 59.02/7.99      | v1_relat_1(X0) != iProver_top ),
% 59.02/7.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 59.02/7.99  
% 59.02/7.99  cnf(c_2383,plain,
% 59.02/7.99      ( k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0) ),
% 59.02/7.99      inference(superposition,[status(thm)],[c_713,c_722]) ).
% 59.02/7.99  
% 59.02/7.99  cnf(c_3661,plain,
% 59.02/7.99      ( r1_tarski(k1_setfam_1(k2_tarski(X0,k1_relat_1(sK1))),k10_relat_1(k7_relat_1(sK1,X0),k9_relat_1(sK1,X0))) = iProver_top
% 59.02/7.99      | v1_relat_1(k7_relat_1(sK1,X0)) != iProver_top ),
% 59.02/7.99      inference(light_normalisation,[status(thm)],[c_3651,c_2383]) ).
% 59.02/7.99  
% 59.02/7.99  cnf(c_4658,plain,
% 59.02/7.99      ( r1_tarski(sK0,k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0))) = iProver_top
% 59.02/7.99      | v1_relat_1(k7_relat_1(sK1,sK0)) != iProver_top ),
% 59.02/7.99      inference(superposition,[status(thm)],[c_1510,c_3661]) ).
% 59.02/7.99  
% 59.02/7.99  cnf(c_4780,plain,
% 59.02/7.99      ( k1_setfam_1(k2_tarski(sK0,k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)))) = sK0
% 59.02/7.99      | v1_relat_1(k7_relat_1(sK1,sK0)) != iProver_top ),
% 59.02/7.99      inference(superposition,[status(thm)],[c_4658,c_726]) ).
% 59.02/7.99  
% 59.02/7.99  cnf(c_1362,plain,
% 59.02/7.99      ( k10_relat_1(k7_relat_1(X0,X1),k2_relat_1(k7_relat_1(X0,X1))) = k1_relat_1(k7_relat_1(X0,X1))
% 59.02/7.99      | v1_relat_1(X0) != iProver_top ),
% 59.02/7.99      inference(superposition,[status(thm)],[c_723,c_720]) ).
% 59.02/7.99  
% 59.02/7.99  cnf(c_7616,plain,
% 59.02/7.99      ( k10_relat_1(k7_relat_1(sK1,X0),k2_relat_1(k7_relat_1(sK1,X0))) = k1_relat_1(k7_relat_1(sK1,X0)) ),
% 59.02/7.99      inference(superposition,[status(thm)],[c_713,c_1362]) ).
% 59.02/7.99  
% 59.02/7.99  cnf(c_7617,plain,
% 59.02/7.99      ( k10_relat_1(k7_relat_1(sK1,X0),k9_relat_1(sK1,X0)) = k1_relat_1(k7_relat_1(sK1,X0)) ),
% 59.02/7.99      inference(light_normalisation,[status(thm)],[c_7616,c_2383]) ).
% 59.02/7.99  
% 59.02/7.99  cnf(c_7,plain,
% 59.02/7.99      ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
% 59.02/7.99      inference(cnf_transformation,[],[f66]) ).
% 59.02/7.99  
% 59.02/7.99  cnf(c_727,plain,
% 59.02/7.99      ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) = iProver_top ),
% 59.02/7.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 59.02/7.99  
% 59.02/7.99  cnf(c_1788,plain,
% 59.02/7.99      ( r1_tarski(k10_relat_1(k7_relat_1(sK1,X0),X1),X0) = iProver_top ),
% 59.02/7.99      inference(superposition,[status(thm)],[c_1284,c_727]) ).
% 59.02/7.99  
% 59.02/7.99  cnf(c_1799,plain,
% 59.02/7.99      ( k1_setfam_1(k2_tarski(k10_relat_1(k7_relat_1(sK1,X0),X1),X0)) = k10_relat_1(k7_relat_1(sK1,X0),X1) ),
% 59.02/7.99      inference(superposition,[status(thm)],[c_1788,c_726]) ).
% 59.02/7.99  
% 59.02/7.99  cnf(c_0,plain,
% 59.02/7.99      ( k1_setfam_1(k2_tarski(X0,X1)) = k1_setfam_1(k2_tarski(X1,X0)) ),
% 59.02/7.99      inference(cnf_transformation,[],[f65]) ).
% 59.02/7.99  
% 59.02/7.99  cnf(c_9096,plain,
% 59.02/7.99      ( k1_setfam_1(k2_tarski(X0,k10_relat_1(k7_relat_1(sK1,X0),X1))) = k10_relat_1(k7_relat_1(sK1,X0),X1) ),
% 59.02/7.99      inference(superposition,[status(thm)],[c_1799,c_0]) ).
% 59.02/7.99  
% 59.02/7.99  cnf(c_229580,plain,
% 59.02/7.99      ( k1_relat_1(k7_relat_1(sK1,sK0)) = sK0
% 59.02/7.99      | v1_relat_1(k7_relat_1(sK1,sK0)) != iProver_top ),
% 59.02/7.99      inference(demodulation,[status(thm)],[c_4780,c_7617,c_9096]) ).
% 59.02/7.99  
% 59.02/7.99  cnf(c_229582,plain,
% 59.02/7.99      ( k1_relat_1(k7_relat_1(sK1,sK0)) = sK0
% 59.02/7.99      | v1_relat_1(sK1) != iProver_top ),
% 59.02/7.99      inference(superposition,[status(thm)],[c_723,c_229580]) ).
% 59.02/7.99  
% 59.02/7.99  cnf(c_22,plain,
% 59.02/7.99      ( v1_relat_1(sK1) = iProver_top ),
% 59.02/7.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 59.02/7.99  
% 59.02/7.99  cnf(c_230492,plain,
% 59.02/7.99      ( k1_relat_1(k7_relat_1(sK1,sK0)) = sK0 ),
% 59.02/7.99      inference(global_propositional_subsumption,
% 59.02/7.99                [status(thm)],
% 59.02/7.99                [c_229582,c_22]) ).
% 59.02/7.99  
% 59.02/7.99  cnf(c_1170,plain,
% 59.02/7.99      ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X1) = iProver_top ),
% 59.02/7.99      inference(superposition,[status(thm)],[c_0,c_727]) ).
% 59.02/7.99  
% 59.02/7.99  cnf(c_1786,plain,
% 59.02/7.99      ( r1_tarski(k10_relat_1(k7_relat_1(sK1,X0),X1),k10_relat_1(sK1,X1)) = iProver_top ),
% 59.02/7.99      inference(superposition,[status(thm)],[c_1284,c_1170]) ).
% 59.02/7.99  
% 59.02/7.99  cnf(c_7959,plain,
% 59.02/7.99      ( r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k10_relat_1(sK1,k9_relat_1(sK1,X0))) = iProver_top ),
% 59.02/7.99      inference(superposition,[status(thm)],[c_7617,c_1786]) ).
% 59.02/7.99  
% 59.02/7.99  cnf(c_230566,plain,
% 59.02/7.99      ( r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) = iProver_top ),
% 59.02/7.99      inference(superposition,[status(thm)],[c_230492,c_7959]) ).
% 59.02/7.99  
% 59.02/7.99  cnf(c_19,negated_conjecture,
% 59.02/7.99      ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
% 59.02/7.99      inference(cnf_transformation,[],[f64]) ).
% 59.02/7.99  
% 59.02/7.99  cnf(c_24,plain,
% 59.02/7.99      ( r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) != iProver_top ),
% 59.02/7.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 59.02/7.99  
% 59.02/7.99  cnf(contradiction,plain,
% 59.02/7.99      ( $false ),
% 59.02/7.99      inference(minisat,[status(thm)],[c_230566,c_24]) ).
% 59.02/7.99  
% 59.02/7.99  
% 59.02/7.99  % SZS output end CNFRefutation for theBenchmark.p
% 59.02/7.99  
% 59.02/7.99  ------                               Statistics
% 59.02/7.99  
% 59.02/7.99  ------ General
% 59.02/7.99  
% 59.02/7.99  abstr_ref_over_cycles:                  0
% 59.02/7.99  abstr_ref_under_cycles:                 0
% 59.02/7.99  gc_basic_clause_elim:                   0
% 59.02/7.99  forced_gc_time:                         0
% 59.02/7.99  parsing_time:                           0.006
% 59.02/7.99  unif_index_cands_time:                  0.
% 59.02/7.99  unif_index_add_time:                    0.
% 59.02/7.99  orderings_time:                         0.
% 59.02/7.99  out_proof_time:                         0.033
% 59.02/7.99  total_time:                             7.185
% 59.02/7.99  num_of_symbols:                         43
% 59.02/7.99  num_of_terms:                           319617
% 59.02/7.99  
% 59.02/7.99  ------ Preprocessing
% 59.02/7.99  
% 59.02/7.99  num_of_splits:                          0
% 59.02/7.99  num_of_split_atoms:                     0
% 59.02/7.99  num_of_reused_defs:                     0
% 59.02/7.99  num_eq_ax_congr_red:                    15
% 59.02/7.99  num_of_sem_filtered_clauses:            1
% 59.02/7.99  num_of_subtypes:                        0
% 59.02/7.99  monotx_restored_types:                  0
% 59.02/7.99  sat_num_of_epr_types:                   0
% 59.02/7.99  sat_num_of_non_cyclic_types:            0
% 59.02/7.99  sat_guarded_non_collapsed_types:        0
% 59.02/7.99  num_pure_diseq_elim:                    0
% 59.02/7.99  simp_replaced_by:                       0
% 59.02/7.99  res_preprocessed:                       105
% 59.02/7.99  prep_upred:                             0
% 59.02/7.99  prep_unflattend:                        0
% 59.02/7.99  smt_new_axioms:                         0
% 59.02/7.99  pred_elim_cands:                        2
% 59.02/7.99  pred_elim:                              0
% 59.02/7.99  pred_elim_cl:                           0
% 59.02/7.99  pred_elim_cycles:                       2
% 59.02/7.99  merged_defs:                            0
% 59.02/7.99  merged_defs_ncl:                        0
% 59.02/7.99  bin_hyper_res:                          0
% 59.02/7.99  prep_cycles:                            4
% 59.02/7.99  pred_elim_time:                         0.
% 59.02/7.99  splitting_time:                         0.
% 59.02/7.99  sem_filter_time:                        0.
% 59.02/7.99  monotx_time:                            0.
% 59.02/7.99  subtype_inf_time:                       0.
% 59.02/7.99  
% 59.02/7.99  ------ Problem properties
% 59.02/7.99  
% 59.02/7.99  clauses:                                21
% 59.02/7.99  conjectures:                            3
% 59.02/7.99  epr:                                    3
% 59.02/7.99  horn:                                   21
% 59.02/7.99  ground:                                 3
% 59.02/7.99  unary:                                  7
% 59.02/7.99  binary:                                 11
% 59.02/7.99  lits:                                   38
% 59.02/7.99  lits_eq:                                7
% 59.02/7.99  fd_pure:                                0
% 59.02/7.99  fd_pseudo:                              0
% 59.02/7.99  fd_cond:                                0
% 59.02/7.99  fd_pseudo_cond:                         1
% 59.02/7.99  ac_symbols:                             0
% 59.02/7.99  
% 59.02/7.99  ------ Propositional Solver
% 59.02/7.99  
% 59.02/7.99  prop_solver_calls:                      88
% 59.02/7.99  prop_fast_solver_calls:                 1428
% 59.02/7.99  smt_solver_calls:                       0
% 59.02/7.99  smt_fast_solver_calls:                  0
% 59.02/7.99  prop_num_of_clauses:                    86563
% 59.02/7.99  prop_preprocess_simplified:             126315
% 59.02/7.99  prop_fo_subsumed:                       5
% 59.02/7.99  prop_solver_time:                       0.
% 59.02/7.99  smt_solver_time:                        0.
% 59.02/7.99  smt_fast_solver_time:                   0.
% 59.02/7.99  prop_fast_solver_time:                  0.
% 59.02/7.99  prop_unsat_core_time:                   0.012
% 59.02/7.99  
% 59.02/7.99  ------ QBF
% 59.02/7.99  
% 59.02/7.99  qbf_q_res:                              0
% 59.02/7.99  qbf_num_tautologies:                    0
% 59.02/7.99  qbf_prep_cycles:                        0
% 59.02/7.99  
% 59.02/7.99  ------ BMC1
% 59.02/7.99  
% 59.02/7.99  bmc1_current_bound:                     -1
% 59.02/7.99  bmc1_last_solved_bound:                 -1
% 59.02/7.99  bmc1_unsat_core_size:                   -1
% 59.02/7.99  bmc1_unsat_core_parents_size:           -1
% 59.02/7.99  bmc1_merge_next_fun:                    0
% 59.02/7.99  bmc1_unsat_core_clauses_time:           0.
% 59.02/7.99  
% 59.02/7.99  ------ Instantiation
% 59.02/7.99  
% 59.02/7.99  inst_num_of_clauses:                    1790
% 59.02/7.99  inst_num_in_passive:                    1229
% 59.02/7.99  inst_num_in_active:                     2845
% 59.02/7.99  inst_num_in_unprocessed:                31
% 59.02/7.99  inst_num_of_loops:                      3569
% 59.02/7.99  inst_num_of_learning_restarts:          1
% 59.02/7.99  inst_num_moves_active_passive:          711
% 59.02/7.99  inst_lit_activity:                      0
% 59.02/7.99  inst_lit_activity_moves:                5
% 59.02/7.99  inst_num_tautologies:                   0
% 59.02/7.99  inst_num_prop_implied:                  0
% 59.02/7.99  inst_num_existing_simplified:           0
% 59.02/7.99  inst_num_eq_res_simplified:             0
% 59.02/7.99  inst_num_child_elim:                    0
% 59.02/7.99  inst_num_of_dismatching_blockings:      28446
% 59.02/7.99  inst_num_of_non_proper_insts:           19700
% 59.02/7.99  inst_num_of_duplicates:                 0
% 59.02/7.99  inst_inst_num_from_inst_to_res:         0
% 59.02/7.99  inst_dismatching_checking_time:         0.
% 59.02/7.99  
% 59.02/7.99  ------ Resolution
% 59.02/7.99  
% 59.02/7.99  res_num_of_clauses:                     31
% 59.02/7.99  res_num_in_passive:                     31
% 59.02/7.99  res_num_in_active:                      0
% 59.02/7.99  res_num_of_loops:                       109
% 59.02/7.99  res_forward_subset_subsumed:            2817
% 59.02/7.99  res_backward_subset_subsumed:           72
% 59.02/7.99  res_forward_subsumed:                   0
% 59.02/7.99  res_backward_subsumed:                  0
% 59.02/7.99  res_forward_subsumption_resolution:     0
% 59.02/7.99  res_backward_subsumption_resolution:    0
% 59.02/7.99  res_clause_to_clause_subsumption:       135232
% 59.02/7.99  res_orphan_elimination:                 0
% 59.02/7.99  res_tautology_del:                      607
% 59.02/7.99  res_num_eq_res_simplified:              0
% 59.02/7.99  res_num_sel_changes:                    0
% 59.02/7.99  res_moves_from_active_to_pass:          0
% 59.02/7.99  
% 59.02/7.99  ------ Superposition
% 59.02/7.99  
% 59.02/7.99  sup_time_total:                         0.
% 59.02/7.99  sup_time_generating:                    0.
% 59.02/7.99  sup_time_sim_full:                      0.
% 59.02/7.99  sup_time_sim_immed:                     0.
% 59.02/7.99  
% 59.02/7.99  sup_num_of_clauses:                     11866
% 59.02/7.99  sup_num_in_active:                      648
% 59.02/7.99  sup_num_in_passive:                     11218
% 59.02/7.99  sup_num_of_loops:                       712
% 59.02/7.99  sup_fw_superposition:                   23474
% 59.02/7.99  sup_bw_superposition:                   20161
% 59.02/7.99  sup_immediate_simplified:               20870
% 59.02/7.99  sup_given_eliminated:                   16
% 59.02/7.99  comparisons_done:                       0
% 59.02/7.99  comparisons_avoided:                    0
% 59.02/7.99  
% 59.02/7.99  ------ Simplifications
% 59.02/7.99  
% 59.02/7.99  
% 59.02/7.99  sim_fw_subset_subsumed:                 177
% 59.02/7.99  sim_bw_subset_subsumed:                 17
% 59.02/7.99  sim_fw_subsumed:                        4303
% 59.02/7.99  sim_bw_subsumed:                        166
% 59.02/7.99  sim_fw_subsumption_res:                 0
% 59.02/7.99  sim_bw_subsumption_res:                 0
% 59.02/7.99  sim_tautology_del:                      308
% 59.02/7.99  sim_eq_tautology_del:                   4051
% 59.02/7.99  sim_eq_res_simp:                        0
% 59.02/7.99  sim_fw_demodulated:                     13504
% 59.02/7.99  sim_bw_demodulated:                     299
% 59.02/7.99  sim_light_normalised:                   7722
% 59.02/7.99  sim_joinable_taut:                      0
% 59.02/7.99  sim_joinable_simp:                      0
% 59.02/7.99  sim_ac_normalised:                      0
% 59.02/7.99  sim_smt_subsumption:                    0
% 59.02/7.99  
%------------------------------------------------------------------------------
