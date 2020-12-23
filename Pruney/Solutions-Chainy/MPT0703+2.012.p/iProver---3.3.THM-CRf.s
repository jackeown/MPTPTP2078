%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:52:16 EST 2020

% Result     : Theorem 1.01s
% Output     : CNFRefutation 1.01s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 124 expanded)
%              Number of clauses        :   41 (  44 expanded)
%              Number of leaves         :   10 (  28 expanded)
%              Depth                    :   14
%              Number of atoms          :  160 ( 387 expanded)
%              Number of equality atoms :   71 (  84 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_tarski(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f20,f21])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(X0,k2_relat_1(X2))
          & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( r1_tarski(X0,k2_relat_1(X2))
            & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
         => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k2_relat_1(X2))
      & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k2_relat_1(X2))
      & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f16,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,X1)
        & r1_tarski(X0,k2_relat_1(X2))
        & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(sK0,sK1)
      & r1_tarski(sK0,k2_relat_1(sK2))
      & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ~ r1_tarski(sK0,sK1)
    & r1_tarski(sK0,k2_relat_1(sK2))
    & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f16])).

fof(f26,plain,(
    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k3_xboole_0(k9_relat_1(X2,X0),X1) = k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(k9_relat_1(X2,X0),X1) = k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(k9_relat_1(X2,X0),X1) = k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f12])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(k9_relat_1(X2,X0),X1) = k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k1_setfam_1(k2_tarski(k9_relat_1(X2,X0),X1)) = k9_relat_1(X2,k1_setfam_1(k2_tarski(X0,k10_relat_1(X2,X1))))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f23,f21,f21])).

fof(f25,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f24,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f27,plain,(
    r1_tarski(sK0,k2_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f17])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f10])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f29,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(definition_unfolding,[],[f18,f21,f21])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f30,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f19,f21])).

fof(f28,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | k1_setfam_1(k2_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_7,negated_conjecture,
    ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_159,plain,
    ( k10_relat_1(sK2,sK1) != X0
    | k10_relat_1(sK2,sK0) != X1
    | k1_setfam_1(k2_tarski(X1,X0)) = X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_7])).

cnf(c_160,plain,
    ( k1_setfam_1(k2_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))) = k10_relat_1(sK2,sK0) ),
    inference(unflattening,[status(thm)],[c_159])).

cnf(c_207,plain,
    ( k1_setfam_1(k2_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))) = k10_relat_1(sK2,sK0) ),
    inference(subtyping,[status(esa)],[c_160])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k9_relat_1(X0,k1_setfam_1(k2_tarski(X1,k10_relat_1(X0,X2)))) = k1_setfam_1(k2_tarski(k9_relat_1(X0,X1),X2)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_8,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_121,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_setfam_1(k2_tarski(X1,k10_relat_1(X0,X2)))) = k1_setfam_1(k2_tarski(k9_relat_1(X0,X1),X2))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_8])).

cnf(c_122,plain,
    ( ~ v1_relat_1(sK2)
    | k9_relat_1(sK2,k1_setfam_1(k2_tarski(X0,k10_relat_1(sK2,X1)))) = k1_setfam_1(k2_tarski(k9_relat_1(sK2,X0),X1)) ),
    inference(unflattening,[status(thm)],[c_121])).

cnf(c_9,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_126,plain,
    ( k9_relat_1(sK2,k1_setfam_1(k2_tarski(X0,k10_relat_1(sK2,X1)))) = k1_setfam_1(k2_tarski(k9_relat_1(sK2,X0),X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_122,c_9])).

cnf(c_212,plain,
    ( k9_relat_1(sK2,k1_setfam_1(k2_tarski(X0_39,k10_relat_1(sK2,X1_39)))) = k1_setfam_1(k2_tarski(k9_relat_1(sK2,X0_39),X1_39)) ),
    inference(subtyping,[status(esa)],[c_126])).

cnf(c_306,plain,
    ( k1_setfam_1(k2_tarski(k9_relat_1(sK2,k10_relat_1(sK2,sK0)),sK1)) = k9_relat_1(sK2,k10_relat_1(sK2,sK0)) ),
    inference(superposition,[status(thm)],[c_207,c_212])).

cnf(c_6,negated_conjecture,
    ( r1_tarski(sK0,k2_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f22])).

cnf(c_103,plain,
    ( ~ r1_tarski(X0,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_8])).

cnf(c_104,plain,
    ( ~ r1_tarski(X0,k2_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_103])).

cnf(c_108,plain,
    ( ~ r1_tarski(X0,k2_relat_1(sK2))
    | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_104,c_9])).

cnf(c_178,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0
    | k2_relat_1(sK2) != k2_relat_1(sK2)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_108])).

cnf(c_179,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,sK0)) = sK0 ),
    inference(unflattening,[status(thm)],[c_178])).

cnf(c_204,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,sK0)) = sK0 ),
    inference(subtyping,[status(esa)],[c_179])).

cnf(c_307,plain,
    ( k1_setfam_1(k2_tarski(sK0,sK1)) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_306,c_204])).

cnf(c_216,plain,
    ( X0_39 != X1_39
    | X2_39 != X1_39
    | X2_39 = X0_39 ),
    theory(equality)).

cnf(c_301,plain,
    ( k1_setfam_1(k2_tarski(X0_39,sK1)) != X1_39
    | sK0 != X1_39
    | sK0 = k1_setfam_1(k2_tarski(X0_39,sK1)) ),
    inference(instantiation,[status(thm)],[c_216])).

cnf(c_302,plain,
    ( k1_setfam_1(k2_tarski(sK0,sK1)) != sK0
    | sK0 = k1_setfam_1(k2_tarski(sK0,sK1))
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_301])).

cnf(c_0,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_213,plain,
    ( k1_setfam_1(k2_tarski(X0_39,X1_39)) = k1_setfam_1(k2_tarski(X1_39,X0_39)) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_278,plain,
    ( k1_setfam_1(k2_tarski(sK1,X0_39)) = k1_setfam_1(k2_tarski(X0_39,sK1)) ),
    inference(instantiation,[status(thm)],[c_213])).

cnf(c_280,plain,
    ( k1_setfam_1(k2_tarski(sK1,sK0)) = k1_setfam_1(k2_tarski(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_278])).

cnf(c_268,plain,
    ( k1_setfam_1(k2_tarski(sK1,X0_39)) != X1_39
    | k1_setfam_1(k2_tarski(sK1,X0_39)) = sK0
    | sK0 != X1_39 ),
    inference(instantiation,[status(thm)],[c_216])).

cnf(c_277,plain,
    ( k1_setfam_1(k2_tarski(sK1,X0_39)) != k1_setfam_1(k2_tarski(X0_39,sK1))
    | k1_setfam_1(k2_tarski(sK1,X0_39)) = sK0
    | sK0 != k1_setfam_1(k2_tarski(X0_39,sK1)) ),
    inference(instantiation,[status(thm)],[c_268])).

cnf(c_279,plain,
    ( k1_setfam_1(k2_tarski(sK1,sK0)) != k1_setfam_1(k2_tarski(sK0,sK1))
    | k1_setfam_1(k2_tarski(sK1,sK0)) = sK0
    | sK0 != k1_setfam_1(k2_tarski(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_277])).

cnf(c_1,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_5,negated_conjecture,
    ( ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_142,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) != sK0
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_5])).

cnf(c_143,plain,
    ( k1_setfam_1(k2_tarski(sK1,X0)) != sK0 ),
    inference(unflattening,[status(thm)],[c_142])).

cnf(c_210,plain,
    ( k1_setfam_1(k2_tarski(sK1,X0_39)) != sK0 ),
    inference(subtyping,[status(esa)],[c_143])).

cnf(c_230,plain,
    ( k1_setfam_1(k2_tarski(sK1,sK0)) != sK0 ),
    inference(instantiation,[status(thm)],[c_210])).

cnf(c_214,plain,
    ( X0_39 = X0_39 ),
    theory(equality)).

cnf(c_225,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_214])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_307,c_302,c_280,c_279,c_230,c_225])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.08  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.08  % Command    : iproveropt_run.sh %d %s
% 0.07/0.27  % Computer   : n012.cluster.edu
% 0.07/0.27  % Model      : x86_64 x86_64
% 0.07/0.27  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.07/0.27  % Memory     : 8042.1875MB
% 0.07/0.27  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.07/0.27  % CPULimit   : 60
% 0.07/0.27  % WCLimit    : 600
% 0.07/0.27  % DateTime   : Tue Dec  1 12:06:22 EST 2020
% 0.07/0.27  % CPUTime    : 
% 0.07/0.28  % Running in FOF mode
% 1.01/0.85  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.01/0.85  
% 1.01/0.85  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.01/0.85  
% 1.01/0.85  ------  iProver source info
% 1.01/0.85  
% 1.01/0.85  git: date: 2020-06-30 10:37:57 +0100
% 1.01/0.85  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.01/0.85  git: non_committed_changes: false
% 1.01/0.85  git: last_make_outside_of_git: false
% 1.01/0.85  
% 1.01/0.85  ------ 
% 1.01/0.85  
% 1.01/0.85  ------ Input Options
% 1.01/0.85  
% 1.01/0.85  --out_options                           all
% 1.01/0.85  --tptp_safe_out                         true
% 1.01/0.85  --problem_path                          ""
% 1.01/0.85  --include_path                          ""
% 1.01/0.85  --clausifier                            res/vclausify_rel
% 1.01/0.85  --clausifier_options                    --mode clausify
% 1.01/0.85  --stdin                                 false
% 1.01/0.85  --stats_out                             all
% 1.01/0.85  
% 1.01/0.85  ------ General Options
% 1.01/0.85  
% 1.01/0.85  --fof                                   false
% 1.01/0.85  --time_out_real                         305.
% 1.01/0.85  --time_out_virtual                      -1.
% 1.01/0.85  --symbol_type_check                     false
% 1.01/0.85  --clausify_out                          false
% 1.01/0.85  --sig_cnt_out                           false
% 1.01/0.85  --trig_cnt_out                          false
% 1.01/0.85  --trig_cnt_out_tolerance                1.
% 1.01/0.85  --trig_cnt_out_sk_spl                   false
% 1.01/0.85  --abstr_cl_out                          false
% 1.01/0.85  
% 1.01/0.85  ------ Global Options
% 1.01/0.85  
% 1.01/0.85  --schedule                              default
% 1.01/0.85  --add_important_lit                     false
% 1.01/0.85  --prop_solver_per_cl                    1000
% 1.01/0.85  --min_unsat_core                        false
% 1.01/0.85  --soft_assumptions                      false
% 1.01/0.85  --soft_lemma_size                       3
% 1.01/0.85  --prop_impl_unit_size                   0
% 1.01/0.85  --prop_impl_unit                        []
% 1.01/0.85  --share_sel_clauses                     true
% 1.01/0.85  --reset_solvers                         false
% 1.01/0.85  --bc_imp_inh                            [conj_cone]
% 1.01/0.85  --conj_cone_tolerance                   3.
% 1.01/0.85  --extra_neg_conj                        none
% 1.01/0.85  --large_theory_mode                     true
% 1.01/0.85  --prolific_symb_bound                   200
% 1.01/0.85  --lt_threshold                          2000
% 1.01/0.85  --clause_weak_htbl                      true
% 1.01/0.85  --gc_record_bc_elim                     false
% 1.01/0.85  
% 1.01/0.85  ------ Preprocessing Options
% 1.01/0.85  
% 1.01/0.85  --preprocessing_flag                    true
% 1.01/0.85  --time_out_prep_mult                    0.1
% 1.01/0.85  --splitting_mode                        input
% 1.01/0.85  --splitting_grd                         true
% 1.01/0.85  --splitting_cvd                         false
% 1.01/0.85  --splitting_cvd_svl                     false
% 1.01/0.85  --splitting_nvd                         32
% 1.01/0.85  --sub_typing                            true
% 1.01/0.85  --prep_gs_sim                           true
% 1.01/0.85  --prep_unflatten                        true
% 1.01/0.85  --prep_res_sim                          true
% 1.01/0.85  --prep_upred                            true
% 1.01/0.85  --prep_sem_filter                       exhaustive
% 1.01/0.85  --prep_sem_filter_out                   false
% 1.01/0.85  --pred_elim                             true
% 1.01/0.85  --res_sim_input                         true
% 1.01/0.85  --eq_ax_congr_red                       true
% 1.01/0.85  --pure_diseq_elim                       true
% 1.01/0.85  --brand_transform                       false
% 1.01/0.85  --non_eq_to_eq                          false
% 1.01/0.85  --prep_def_merge                        true
% 1.01/0.85  --prep_def_merge_prop_impl              false
% 1.01/0.85  --prep_def_merge_mbd                    true
% 1.01/0.85  --prep_def_merge_tr_red                 false
% 1.01/0.85  --prep_def_merge_tr_cl                  false
% 1.01/0.85  --smt_preprocessing                     true
% 1.01/0.85  --smt_ac_axioms                         fast
% 1.01/0.85  --preprocessed_out                      false
% 1.01/0.85  --preprocessed_stats                    false
% 1.01/0.85  
% 1.01/0.85  ------ Abstraction refinement Options
% 1.01/0.85  
% 1.01/0.85  --abstr_ref                             []
% 1.01/0.85  --abstr_ref_prep                        false
% 1.01/0.85  --abstr_ref_until_sat                   false
% 1.01/0.85  --abstr_ref_sig_restrict                funpre
% 1.01/0.85  --abstr_ref_af_restrict_to_split_sk     false
% 1.01/0.85  --abstr_ref_under                       []
% 1.01/0.85  
% 1.01/0.85  ------ SAT Options
% 1.01/0.85  
% 1.01/0.85  --sat_mode                              false
% 1.01/0.85  --sat_fm_restart_options                ""
% 1.01/0.85  --sat_gr_def                            false
% 1.01/0.85  --sat_epr_types                         true
% 1.01/0.85  --sat_non_cyclic_types                  false
% 1.01/0.85  --sat_finite_models                     false
% 1.01/0.85  --sat_fm_lemmas                         false
% 1.01/0.85  --sat_fm_prep                           false
% 1.01/0.85  --sat_fm_uc_incr                        true
% 1.01/0.85  --sat_out_model                         small
% 1.01/0.85  --sat_out_clauses                       false
% 1.01/0.85  
% 1.01/0.85  ------ QBF Options
% 1.01/0.85  
% 1.01/0.85  --qbf_mode                              false
% 1.01/0.85  --qbf_elim_univ                         false
% 1.01/0.85  --qbf_dom_inst                          none
% 1.01/0.85  --qbf_dom_pre_inst                      false
% 1.01/0.85  --qbf_sk_in                             false
% 1.01/0.85  --qbf_pred_elim                         true
% 1.01/0.85  --qbf_split                             512
% 1.01/0.85  
% 1.01/0.85  ------ BMC1 Options
% 1.01/0.85  
% 1.01/0.85  --bmc1_incremental                      false
% 1.01/0.85  --bmc1_axioms                           reachable_all
% 1.01/0.85  --bmc1_min_bound                        0
% 1.01/0.85  --bmc1_max_bound                        -1
% 1.01/0.85  --bmc1_max_bound_default                -1
% 1.01/0.85  --bmc1_symbol_reachability              true
% 1.01/0.85  --bmc1_property_lemmas                  false
% 1.01/0.85  --bmc1_k_induction                      false
% 1.01/0.85  --bmc1_non_equiv_states                 false
% 1.01/0.85  --bmc1_deadlock                         false
% 1.01/0.85  --bmc1_ucm                              false
% 1.01/0.85  --bmc1_add_unsat_core                   none
% 1.01/0.85  --bmc1_unsat_core_children              false
% 1.01/0.85  --bmc1_unsat_core_extrapolate_axioms    false
% 1.01/0.85  --bmc1_out_stat                         full
% 1.01/0.85  --bmc1_ground_init                      false
% 1.01/0.85  --bmc1_pre_inst_next_state              false
% 1.01/0.85  --bmc1_pre_inst_state                   false
% 1.01/0.85  --bmc1_pre_inst_reach_state             false
% 1.01/0.85  --bmc1_out_unsat_core                   false
% 1.01/0.85  --bmc1_aig_witness_out                  false
% 1.01/0.85  --bmc1_verbose                          false
% 1.01/0.85  --bmc1_dump_clauses_tptp                false
% 1.01/0.85  --bmc1_dump_unsat_core_tptp             false
% 1.01/0.85  --bmc1_dump_file                        -
% 1.01/0.85  --bmc1_ucm_expand_uc_limit              128
% 1.01/0.85  --bmc1_ucm_n_expand_iterations          6
% 1.01/0.85  --bmc1_ucm_extend_mode                  1
% 1.01/0.85  --bmc1_ucm_init_mode                    2
% 1.01/0.85  --bmc1_ucm_cone_mode                    none
% 1.01/0.85  --bmc1_ucm_reduced_relation_type        0
% 1.01/0.85  --bmc1_ucm_relax_model                  4
% 1.01/0.85  --bmc1_ucm_full_tr_after_sat            true
% 1.01/0.85  --bmc1_ucm_expand_neg_assumptions       false
% 1.01/0.85  --bmc1_ucm_layered_model                none
% 1.01/0.85  --bmc1_ucm_max_lemma_size               10
% 1.01/0.85  
% 1.01/0.85  ------ AIG Options
% 1.01/0.85  
% 1.01/0.85  --aig_mode                              false
% 1.01/0.85  
% 1.01/0.85  ------ Instantiation Options
% 1.01/0.85  
% 1.01/0.85  --instantiation_flag                    true
% 1.01/0.85  --inst_sos_flag                         false
% 1.01/0.85  --inst_sos_phase                        true
% 1.01/0.85  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.01/0.85  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.01/0.85  --inst_lit_sel_side                     num_symb
% 1.01/0.85  --inst_solver_per_active                1400
% 1.01/0.85  --inst_solver_calls_frac                1.
% 1.01/0.85  --inst_passive_queue_type               priority_queues
% 1.01/0.85  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.01/0.85  --inst_passive_queues_freq              [25;2]
% 1.01/0.85  --inst_dismatching                      true
% 1.01/0.85  --inst_eager_unprocessed_to_passive     true
% 1.01/0.85  --inst_prop_sim_given                   true
% 1.01/0.85  --inst_prop_sim_new                     false
% 1.01/0.85  --inst_subs_new                         false
% 1.01/0.85  --inst_eq_res_simp                      false
% 1.01/0.85  --inst_subs_given                       false
% 1.01/0.85  --inst_orphan_elimination               true
% 1.01/0.85  --inst_learning_loop_flag               true
% 1.01/0.85  --inst_learning_start                   3000
% 1.01/0.85  --inst_learning_factor                  2
% 1.01/0.85  --inst_start_prop_sim_after_learn       3
% 1.01/0.85  --inst_sel_renew                        solver
% 1.01/0.85  --inst_lit_activity_flag                true
% 1.01/0.85  --inst_restr_to_given                   false
% 1.01/0.85  --inst_activity_threshold               500
% 1.01/0.85  --inst_out_proof                        true
% 1.01/0.85  
% 1.01/0.85  ------ Resolution Options
% 1.01/0.85  
% 1.01/0.85  --resolution_flag                       true
% 1.01/0.85  --res_lit_sel                           adaptive
% 1.01/0.85  --res_lit_sel_side                      none
% 1.01/0.85  --res_ordering                          kbo
% 1.01/0.85  --res_to_prop_solver                    active
% 1.01/0.85  --res_prop_simpl_new                    false
% 1.01/0.85  --res_prop_simpl_given                  true
% 1.01/0.85  --res_passive_queue_type                priority_queues
% 1.01/0.85  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.01/0.85  --res_passive_queues_freq               [15;5]
% 1.01/0.85  --res_forward_subs                      full
% 1.01/0.85  --res_backward_subs                     full
% 1.01/0.85  --res_forward_subs_resolution           true
% 1.01/0.85  --res_backward_subs_resolution          true
% 1.01/0.85  --res_orphan_elimination                true
% 1.01/0.85  --res_time_limit                        2.
% 1.01/0.85  --res_out_proof                         true
% 1.01/0.85  
% 1.01/0.85  ------ Superposition Options
% 1.01/0.85  
% 1.01/0.85  --superposition_flag                    true
% 1.01/0.85  --sup_passive_queue_type                priority_queues
% 1.01/0.85  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.01/0.85  --sup_passive_queues_freq               [8;1;4]
% 1.01/0.85  --demod_completeness_check              fast
% 1.01/0.85  --demod_use_ground                      true
% 1.01/0.85  --sup_to_prop_solver                    passive
% 1.01/0.85  --sup_prop_simpl_new                    true
% 1.01/0.85  --sup_prop_simpl_given                  true
% 1.01/0.85  --sup_fun_splitting                     false
% 1.01/0.85  --sup_smt_interval                      50000
% 1.01/0.85  
% 1.01/0.85  ------ Superposition Simplification Setup
% 1.01/0.85  
% 1.01/0.85  --sup_indices_passive                   []
% 1.01/0.85  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.01/0.85  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.01/0.85  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.01/0.85  --sup_full_triv                         [TrivRules;PropSubs]
% 1.01/0.85  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.01/0.85  --sup_full_bw                           [BwDemod]
% 1.01/0.85  --sup_immed_triv                        [TrivRules]
% 1.01/0.85  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.01/0.85  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.01/0.85  --sup_immed_bw_main                     []
% 1.01/0.85  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.01/0.85  --sup_input_triv                        [Unflattening;TrivRules]
% 1.01/0.85  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.01/0.85  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.01/0.85  
% 1.01/0.85  ------ Combination Options
% 1.01/0.85  
% 1.01/0.85  --comb_res_mult                         3
% 1.01/0.85  --comb_sup_mult                         2
% 1.01/0.85  --comb_inst_mult                        10
% 1.01/0.85  
% 1.01/0.85  ------ Debug Options
% 1.01/0.85  
% 1.01/0.85  --dbg_backtrace                         false
% 1.01/0.85  --dbg_dump_prop_clauses                 false
% 1.01/0.85  --dbg_dump_prop_clauses_file            -
% 1.01/0.85  --dbg_out_stat                          false
% 1.01/0.85  ------ Parsing...
% 1.01/0.85  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.01/0.85  
% 1.01/0.85  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e 
% 1.01/0.85  
% 1.01/0.85  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.01/0.85  
% 1.01/0.85  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 1.01/0.85  ------ Proving...
% 1.01/0.85  ------ Problem Properties 
% 1.01/0.85  
% 1.01/0.85  
% 1.01/0.85  clauses                                 11
% 1.01/0.85  conjectures                             0
% 1.01/0.85  EPR                                     0
% 1.01/0.85  Horn                                    11
% 1.01/0.85  unary                                   8
% 1.01/0.85  binary                                  3
% 1.01/0.85  lits                                    14
% 1.01/0.85  lits eq                                 14
% 1.01/0.85  fd_pure                                 0
% 1.01/0.85  fd_pseudo                               0
% 1.01/0.85  fd_cond                                 0
% 1.01/0.85  fd_pseudo_cond                          0
% 1.01/0.85  AC symbols                              0
% 1.01/0.85  
% 1.01/0.85  ------ Schedule dynamic 5 is on 
% 1.01/0.85  
% 1.01/0.85  ------ no conjectures: strip conj schedule 
% 1.01/0.85  
% 1.01/0.85  ------ pure equality problem: resolution off 
% 1.01/0.85  
% 1.01/0.85  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" stripped conjectures Time Limit: 10.
% 1.01/0.85  
% 1.01/0.85  
% 1.01/0.85  ------ 
% 1.01/0.85  Current options:
% 1.01/0.85  ------ 
% 1.01/0.85  
% 1.01/0.85  ------ Input Options
% 1.01/0.85  
% 1.01/0.85  --out_options                           all
% 1.01/0.85  --tptp_safe_out                         true
% 1.01/0.85  --problem_path                          ""
% 1.01/0.85  --include_path                          ""
% 1.01/0.85  --clausifier                            res/vclausify_rel
% 1.01/0.85  --clausifier_options                    --mode clausify
% 1.01/0.85  --stdin                                 false
% 1.01/0.85  --stats_out                             all
% 1.01/0.85  
% 1.01/0.85  ------ General Options
% 1.01/0.85  
% 1.01/0.85  --fof                                   false
% 1.01/0.85  --time_out_real                         305.
% 1.01/0.85  --time_out_virtual                      -1.
% 1.01/0.85  --symbol_type_check                     false
% 1.01/0.85  --clausify_out                          false
% 1.01/0.85  --sig_cnt_out                           false
% 1.01/0.85  --trig_cnt_out                          false
% 1.01/0.85  --trig_cnt_out_tolerance                1.
% 1.01/0.85  --trig_cnt_out_sk_spl                   false
% 1.01/0.85  --abstr_cl_out                          false
% 1.01/0.85  
% 1.01/0.85  ------ Global Options
% 1.01/0.85  
% 1.01/0.85  --schedule                              default
% 1.01/0.85  --add_important_lit                     false
% 1.01/0.85  --prop_solver_per_cl                    1000
% 1.01/0.85  --min_unsat_core                        false
% 1.01/0.85  --soft_assumptions                      false
% 1.01/0.85  --soft_lemma_size                       3
% 1.01/0.85  --prop_impl_unit_size                   0
% 1.01/0.85  --prop_impl_unit                        []
% 1.01/0.85  --share_sel_clauses                     true
% 1.01/0.85  --reset_solvers                         false
% 1.01/0.85  --bc_imp_inh                            [conj_cone]
% 1.01/0.85  --conj_cone_tolerance                   3.
% 1.01/0.85  --extra_neg_conj                        none
% 1.01/0.85  --large_theory_mode                     true
% 1.01/0.85  --prolific_symb_bound                   200
% 1.01/0.85  --lt_threshold                          2000
% 1.01/0.85  --clause_weak_htbl                      true
% 1.01/0.85  --gc_record_bc_elim                     false
% 1.01/0.85  
% 1.01/0.85  ------ Preprocessing Options
% 1.01/0.85  
% 1.01/0.85  --preprocessing_flag                    true
% 1.01/0.85  --time_out_prep_mult                    0.1
% 1.01/0.85  --splitting_mode                        input
% 1.01/0.85  --splitting_grd                         true
% 1.01/0.85  --splitting_cvd                         false
% 1.01/0.85  --splitting_cvd_svl                     false
% 1.01/0.85  --splitting_nvd                         32
% 1.01/0.85  --sub_typing                            true
% 1.01/0.85  --prep_gs_sim                           true
% 1.01/0.85  --prep_unflatten                        true
% 1.01/0.85  --prep_res_sim                          true
% 1.01/0.85  --prep_upred                            true
% 1.01/0.85  --prep_sem_filter                       exhaustive
% 1.01/0.85  --prep_sem_filter_out                   false
% 1.01/0.85  --pred_elim                             true
% 1.01/0.85  --res_sim_input                         true
% 1.01/0.85  --eq_ax_congr_red                       true
% 1.01/0.85  --pure_diseq_elim                       true
% 1.01/0.85  --brand_transform                       false
% 1.01/0.85  --non_eq_to_eq                          false
% 1.01/0.85  --prep_def_merge                        true
% 1.01/0.85  --prep_def_merge_prop_impl              false
% 1.01/0.85  --prep_def_merge_mbd                    true
% 1.01/0.85  --prep_def_merge_tr_red                 false
% 1.01/0.85  --prep_def_merge_tr_cl                  false
% 1.01/0.85  --smt_preprocessing                     true
% 1.01/0.85  --smt_ac_axioms                         fast
% 1.01/0.85  --preprocessed_out                      false
% 1.01/0.85  --preprocessed_stats                    false
% 1.01/0.85  
% 1.01/0.85  ------ Abstraction refinement Options
% 1.01/0.85  
% 1.01/0.85  --abstr_ref                             []
% 1.01/0.85  --abstr_ref_prep                        false
% 1.01/0.85  --abstr_ref_until_sat                   false
% 1.01/0.85  --abstr_ref_sig_restrict                funpre
% 1.01/0.85  --abstr_ref_af_restrict_to_split_sk     false
% 1.01/0.85  --abstr_ref_under                       []
% 1.01/0.85  
% 1.01/0.85  ------ SAT Options
% 1.01/0.85  
% 1.01/0.85  --sat_mode                              false
% 1.01/0.85  --sat_fm_restart_options                ""
% 1.01/0.85  --sat_gr_def                            false
% 1.01/0.85  --sat_epr_types                         true
% 1.01/0.85  --sat_non_cyclic_types                  false
% 1.01/0.85  --sat_finite_models                     false
% 1.01/0.85  --sat_fm_lemmas                         false
% 1.01/0.85  --sat_fm_prep                           false
% 1.01/0.85  --sat_fm_uc_incr                        true
% 1.01/0.85  --sat_out_model                         small
% 1.01/0.85  --sat_out_clauses                       false
% 1.01/0.85  
% 1.01/0.85  ------ QBF Options
% 1.01/0.85  
% 1.01/0.85  --qbf_mode                              false
% 1.01/0.85  --qbf_elim_univ                         false
% 1.01/0.85  --qbf_dom_inst                          none
% 1.01/0.85  --qbf_dom_pre_inst                      false
% 1.01/0.85  --qbf_sk_in                             false
% 1.01/0.85  --qbf_pred_elim                         true
% 1.01/0.85  --qbf_split                             512
% 1.01/0.85  
% 1.01/0.85  ------ BMC1 Options
% 1.01/0.85  
% 1.01/0.85  --bmc1_incremental                      false
% 1.01/0.85  --bmc1_axioms                           reachable_all
% 1.01/0.85  --bmc1_min_bound                        0
% 1.01/0.85  --bmc1_max_bound                        -1
% 1.01/0.85  --bmc1_max_bound_default                -1
% 1.01/0.85  --bmc1_symbol_reachability              true
% 1.01/0.85  --bmc1_property_lemmas                  false
% 1.01/0.85  --bmc1_k_induction                      false
% 1.01/0.85  --bmc1_non_equiv_states                 false
% 1.01/0.85  --bmc1_deadlock                         false
% 1.01/0.85  --bmc1_ucm                              false
% 1.01/0.85  --bmc1_add_unsat_core                   none
% 1.01/0.85  --bmc1_unsat_core_children              false
% 1.01/0.85  --bmc1_unsat_core_extrapolate_axioms    false
% 1.01/0.85  --bmc1_out_stat                         full
% 1.01/0.85  --bmc1_ground_init                      false
% 1.01/0.85  --bmc1_pre_inst_next_state              false
% 1.01/0.85  --bmc1_pre_inst_state                   false
% 1.01/0.85  --bmc1_pre_inst_reach_state             false
% 1.01/0.85  --bmc1_out_unsat_core                   false
% 1.01/0.85  --bmc1_aig_witness_out                  false
% 1.01/0.85  --bmc1_verbose                          false
% 1.01/0.85  --bmc1_dump_clauses_tptp                false
% 1.01/0.85  --bmc1_dump_unsat_core_tptp             false
% 1.01/0.85  --bmc1_dump_file                        -
% 1.01/0.85  --bmc1_ucm_expand_uc_limit              128
% 1.01/0.85  --bmc1_ucm_n_expand_iterations          6
% 1.01/0.85  --bmc1_ucm_extend_mode                  1
% 1.01/0.85  --bmc1_ucm_init_mode                    2
% 1.01/0.85  --bmc1_ucm_cone_mode                    none
% 1.01/0.85  --bmc1_ucm_reduced_relation_type        0
% 1.01/0.85  --bmc1_ucm_relax_model                  4
% 1.01/0.85  --bmc1_ucm_full_tr_after_sat            true
% 1.01/0.85  --bmc1_ucm_expand_neg_assumptions       false
% 1.01/0.85  --bmc1_ucm_layered_model                none
% 1.01/0.85  --bmc1_ucm_max_lemma_size               10
% 1.01/0.85  
% 1.01/0.85  ------ AIG Options
% 1.01/0.85  
% 1.01/0.85  --aig_mode                              false
% 1.01/0.85  
% 1.01/0.85  ------ Instantiation Options
% 1.01/0.85  
% 1.01/0.85  --instantiation_flag                    true
% 1.01/0.85  --inst_sos_flag                         false
% 1.01/0.85  --inst_sos_phase                        true
% 1.01/0.85  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.01/0.85  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.01/0.85  --inst_lit_sel_side                     none
% 1.01/0.85  --inst_solver_per_active                1400
% 1.01/0.85  --inst_solver_calls_frac                1.
% 1.01/0.85  --inst_passive_queue_type               priority_queues
% 1.01/0.85  --inst_passive_queues                   [[-num_var];[+age;-num_symb]]
% 1.01/0.85  --inst_passive_queues_freq              [25;2]
% 1.01/0.85  --inst_dismatching                      true
% 1.01/0.85  --inst_eager_unprocessed_to_passive     true
% 1.01/0.85  --inst_prop_sim_given                   true
% 1.01/0.85  --inst_prop_sim_new                     false
% 1.01/0.85  --inst_subs_new                         false
% 1.01/0.85  --inst_eq_res_simp                      false
% 1.01/0.85  --inst_subs_given                       false
% 1.01/0.85  --inst_orphan_elimination               true
% 1.01/0.85  --inst_learning_loop_flag               true
% 1.01/0.85  --inst_learning_start                   3000
% 1.01/0.85  --inst_learning_factor                  2
% 1.01/0.85  --inst_start_prop_sim_after_learn       3
% 1.01/0.85  --inst_sel_renew                        solver
% 1.01/0.85  --inst_lit_activity_flag                true
% 1.01/0.85  --inst_restr_to_given                   false
% 1.01/0.85  --inst_activity_threshold               500
% 1.01/0.85  --inst_out_proof                        true
% 1.01/0.85  
% 1.01/0.85  ------ Resolution Options
% 1.01/0.85  
% 1.01/0.85  --resolution_flag                       false
% 1.01/0.85  --res_lit_sel                           adaptive
% 1.01/0.85  --res_lit_sel_side                      none
% 1.01/0.85  --res_ordering                          kbo
% 1.01/0.85  --res_to_prop_solver                    active
% 1.01/0.85  --res_prop_simpl_new                    false
% 1.01/0.85  --res_prop_simpl_given                  true
% 1.01/0.85  --res_passive_queue_type                priority_queues
% 1.01/0.85  --res_passive_queues                    [[-num_symb];[+age;-num_symb]]
% 1.01/0.85  --res_passive_queues_freq               [15;5]
% 1.01/0.85  --res_forward_subs                      full
% 1.01/0.85  --res_backward_subs                     full
% 1.01/0.85  --res_forward_subs_resolution           true
% 1.01/0.85  --res_backward_subs_resolution          true
% 1.01/0.85  --res_orphan_elimination                true
% 1.01/0.85  --res_time_limit                        2.
% 1.01/0.85  --res_out_proof                         true
% 1.01/0.85  
% 1.01/0.85  ------ Superposition Options
% 1.01/0.85  
% 1.01/0.85  --superposition_flag                    true
% 1.01/0.85  --sup_passive_queue_type                priority_queues
% 1.01/0.85  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.01/0.85  --sup_passive_queues_freq               [8;1;4]
% 1.01/0.85  --demod_completeness_check              fast
% 1.01/0.85  --demod_use_ground                      true
% 1.01/0.85  --sup_to_prop_solver                    passive
% 1.01/0.85  --sup_prop_simpl_new                    true
% 1.01/0.85  --sup_prop_simpl_given                  true
% 1.01/0.85  --sup_fun_splitting                     false
% 1.01/0.85  --sup_smt_interval                      50000
% 1.01/0.85  
% 1.01/0.85  ------ Superposition Simplification Setup
% 1.01/0.85  
% 1.01/0.85  --sup_indices_passive                   []
% 1.01/0.85  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.01/0.85  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.01/0.85  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.01/0.85  --sup_full_triv                         [TrivRules;PropSubs]
% 1.01/0.85  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.01/0.85  --sup_full_bw                           [BwDemod]
% 1.01/0.85  --sup_immed_triv                        [TrivRules]
% 1.01/0.85  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.01/0.85  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.01/0.85  --sup_immed_bw_main                     []
% 1.01/0.85  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.01/0.85  --sup_input_triv                        [Unflattening;TrivRules]
% 1.01/0.85  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.01/0.85  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.01/0.85  
% 1.01/0.85  ------ Combination Options
% 1.01/0.85  
% 1.01/0.85  --comb_res_mult                         3
% 1.01/0.85  --comb_sup_mult                         2
% 1.01/0.85  --comb_inst_mult                        10
% 1.01/0.85  
% 1.01/0.85  ------ Debug Options
% 1.01/0.85  
% 1.01/0.85  --dbg_backtrace                         false
% 1.01/0.85  --dbg_dump_prop_clauses                 false
% 1.01/0.85  --dbg_dump_prop_clauses_file            -
% 1.01/0.85  --dbg_out_stat                          false
% 1.01/0.85  
% 1.01/0.85  
% 1.01/0.85  
% 1.01/0.85  
% 1.01/0.85  ------ Proving...
% 1.01/0.85  
% 1.01/0.85  
% 1.01/0.85  % SZS status Theorem for theBenchmark.p
% 1.01/0.85  
% 1.01/0.85  % SZS output start CNFRefutation for theBenchmark.p
% 1.01/0.85  
% 1.01/0.85  fof(f3,axiom,(
% 1.01/0.85    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.01/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.01/0.85  
% 1.01/0.85  fof(f9,plain,(
% 1.01/0.85    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.01/0.85    inference(ennf_transformation,[],[f3])).
% 1.01/0.85  
% 1.01/0.85  fof(f20,plain,(
% 1.01/0.85    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.01/0.85    inference(cnf_transformation,[],[f9])).
% 1.01/0.85  
% 1.01/0.85  fof(f4,axiom,(
% 1.01/0.85    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.01/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.01/0.85  
% 1.01/0.85  fof(f21,plain,(
% 1.01/0.85    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.01/0.85    inference(cnf_transformation,[],[f4])).
% 1.01/0.85  
% 1.01/0.85  fof(f31,plain,(
% 1.01/0.85    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 1.01/0.85    inference(definition_unfolding,[],[f20,f21])).
% 1.01/0.85  
% 1.01/0.85  fof(f7,conjecture,(
% 1.01/0.85    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 1.01/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.01/0.85  
% 1.01/0.85  fof(f8,negated_conjecture,(
% 1.01/0.85    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 1.01/0.85    inference(negated_conjecture,[],[f7])).
% 1.01/0.85  
% 1.01/0.85  fof(f14,plain,(
% 1.01/0.85    ? [X0,X1,X2] : ((~r1_tarski(X0,X1) & (r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 1.01/0.85    inference(ennf_transformation,[],[f8])).
% 1.01/0.85  
% 1.01/0.85  fof(f15,plain,(
% 1.01/0.85    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 1.01/0.85    inference(flattening,[],[f14])).
% 1.01/0.85  
% 1.01/0.85  fof(f16,plain,(
% 1.01/0.85    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(sK0,sK1) & r1_tarski(sK0,k2_relat_1(sK2)) & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 1.01/0.85    introduced(choice_axiom,[])).
% 1.01/0.85  
% 1.01/0.85  fof(f17,plain,(
% 1.01/0.85    ~r1_tarski(sK0,sK1) & r1_tarski(sK0,k2_relat_1(sK2)) & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 1.01/0.85    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f16])).
% 1.01/0.85  
% 1.01/0.85  fof(f26,plain,(
% 1.01/0.85    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 1.01/0.85    inference(cnf_transformation,[],[f17])).
% 1.01/0.85  
% 1.01/0.85  fof(f6,axiom,(
% 1.01/0.85    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k3_xboole_0(k9_relat_1(X2,X0),X1) = k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))))),
% 1.01/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.01/0.85  
% 1.01/0.85  fof(f12,plain,(
% 1.01/0.85    ! [X0,X1,X2] : (k3_xboole_0(k9_relat_1(X2,X0),X1) = k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.01/0.85    inference(ennf_transformation,[],[f6])).
% 1.01/0.85  
% 1.01/0.85  fof(f13,plain,(
% 1.01/0.85    ! [X0,X1,X2] : (k3_xboole_0(k9_relat_1(X2,X0),X1) = k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.01/0.85    inference(flattening,[],[f12])).
% 1.01/0.85  
% 1.01/0.85  fof(f23,plain,(
% 1.01/0.85    ( ! [X2,X0,X1] : (k3_xboole_0(k9_relat_1(X2,X0),X1) = k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.01/0.85    inference(cnf_transformation,[],[f13])).
% 1.01/0.85  
% 1.01/0.85  fof(f32,plain,(
% 1.01/0.85    ( ! [X2,X0,X1] : (k1_setfam_1(k2_tarski(k9_relat_1(X2,X0),X1)) = k9_relat_1(X2,k1_setfam_1(k2_tarski(X0,k10_relat_1(X2,X1)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.01/0.85    inference(definition_unfolding,[],[f23,f21,f21])).
% 1.01/0.85  
% 1.01/0.85  fof(f25,plain,(
% 1.01/0.85    v1_funct_1(sK2)),
% 1.01/0.85    inference(cnf_transformation,[],[f17])).
% 1.01/0.85  
% 1.01/0.85  fof(f24,plain,(
% 1.01/0.85    v1_relat_1(sK2)),
% 1.01/0.85    inference(cnf_transformation,[],[f17])).
% 1.01/0.85  
% 1.01/0.85  fof(f27,plain,(
% 1.01/0.85    r1_tarski(sK0,k2_relat_1(sK2))),
% 1.01/0.85    inference(cnf_transformation,[],[f17])).
% 1.01/0.85  
% 1.01/0.85  fof(f5,axiom,(
% 1.01/0.85    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 1.01/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.01/0.85  
% 1.01/0.85  fof(f10,plain,(
% 1.01/0.85    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.01/0.85    inference(ennf_transformation,[],[f5])).
% 1.01/0.85  
% 1.01/0.85  fof(f11,plain,(
% 1.01/0.85    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.01/0.85    inference(flattening,[],[f10])).
% 1.01/0.85  
% 1.01/0.85  fof(f22,plain,(
% 1.01/0.85    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.01/0.85    inference(cnf_transformation,[],[f11])).
% 1.01/0.85  
% 1.01/0.85  fof(f1,axiom,(
% 1.01/0.85    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.01/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.01/0.85  
% 1.01/0.85  fof(f18,plain,(
% 1.01/0.85    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.01/0.85    inference(cnf_transformation,[],[f1])).
% 1.01/0.85  
% 1.01/0.85  fof(f29,plain,(
% 1.01/0.85    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k1_setfam_1(k2_tarski(X1,X0))) )),
% 1.01/0.85    inference(definition_unfolding,[],[f18,f21,f21])).
% 1.01/0.85  
% 1.01/0.85  fof(f2,axiom,(
% 1.01/0.85    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.01/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.01/0.85  
% 1.01/0.85  fof(f19,plain,(
% 1.01/0.85    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.01/0.85    inference(cnf_transformation,[],[f2])).
% 1.01/0.85  
% 1.01/0.85  fof(f30,plain,(
% 1.01/0.85    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)) )),
% 1.01/0.85    inference(definition_unfolding,[],[f19,f21])).
% 1.01/0.85  
% 1.01/0.85  fof(f28,plain,(
% 1.01/0.85    ~r1_tarski(sK0,sK1)),
% 1.01/0.85    inference(cnf_transformation,[],[f17])).
% 1.01/0.85  
% 1.01/0.85  cnf(c_2,plain,
% 1.01/0.85      ( ~ r1_tarski(X0,X1) | k1_setfam_1(k2_tarski(X0,X1)) = X0 ),
% 1.01/0.85      inference(cnf_transformation,[],[f31]) ).
% 1.01/0.85  
% 1.01/0.85  cnf(c_7,negated_conjecture,
% 1.01/0.85      ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
% 1.01/0.85      inference(cnf_transformation,[],[f26]) ).
% 1.01/0.85  
% 1.01/0.85  cnf(c_159,plain,
% 1.01/0.85      ( k10_relat_1(sK2,sK1) != X0
% 1.01/0.85      | k10_relat_1(sK2,sK0) != X1
% 1.01/0.85      | k1_setfam_1(k2_tarski(X1,X0)) = X1 ),
% 1.01/0.85      inference(resolution_lifted,[status(thm)],[c_2,c_7]) ).
% 1.01/0.85  
% 1.01/0.85  cnf(c_160,plain,
% 1.01/0.85      ( k1_setfam_1(k2_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))) = k10_relat_1(sK2,sK0) ),
% 1.01/0.85      inference(unflattening,[status(thm)],[c_159]) ).
% 1.01/0.85  
% 1.01/0.85  cnf(c_207,plain,
% 1.01/0.85      ( k1_setfam_1(k2_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))) = k10_relat_1(sK2,sK0) ),
% 1.01/0.85      inference(subtyping,[status(esa)],[c_160]) ).
% 1.01/0.85  
% 1.01/0.85  cnf(c_4,plain,
% 1.01/0.85      ( ~ v1_relat_1(X0)
% 1.01/0.85      | ~ v1_funct_1(X0)
% 1.01/0.85      | k9_relat_1(X0,k1_setfam_1(k2_tarski(X1,k10_relat_1(X0,X2)))) = k1_setfam_1(k2_tarski(k9_relat_1(X0,X1),X2)) ),
% 1.01/0.85      inference(cnf_transformation,[],[f32]) ).
% 1.01/0.85  
% 1.01/0.85  cnf(c_8,negated_conjecture,
% 1.01/0.85      ( v1_funct_1(sK2) ),
% 1.01/0.85      inference(cnf_transformation,[],[f25]) ).
% 1.01/0.85  
% 1.01/0.85  cnf(c_121,plain,
% 1.01/0.85      ( ~ v1_relat_1(X0)
% 1.01/0.85      | k9_relat_1(X0,k1_setfam_1(k2_tarski(X1,k10_relat_1(X0,X2)))) = k1_setfam_1(k2_tarski(k9_relat_1(X0,X1),X2))
% 1.01/0.85      | sK2 != X0 ),
% 1.01/0.85      inference(resolution_lifted,[status(thm)],[c_4,c_8]) ).
% 1.01/0.85  
% 1.01/0.85  cnf(c_122,plain,
% 1.01/0.85      ( ~ v1_relat_1(sK2)
% 1.01/0.85      | k9_relat_1(sK2,k1_setfam_1(k2_tarski(X0,k10_relat_1(sK2,X1)))) = k1_setfam_1(k2_tarski(k9_relat_1(sK2,X0),X1)) ),
% 1.01/0.85      inference(unflattening,[status(thm)],[c_121]) ).
% 1.01/0.85  
% 1.01/0.85  cnf(c_9,negated_conjecture,
% 1.01/0.85      ( v1_relat_1(sK2) ),
% 1.01/0.85      inference(cnf_transformation,[],[f24]) ).
% 1.01/0.85  
% 1.01/0.85  cnf(c_126,plain,
% 1.01/0.85      ( k9_relat_1(sK2,k1_setfam_1(k2_tarski(X0,k10_relat_1(sK2,X1)))) = k1_setfam_1(k2_tarski(k9_relat_1(sK2,X0),X1)) ),
% 1.01/0.85      inference(global_propositional_subsumption,
% 1.01/0.85                [status(thm)],
% 1.01/0.85                [c_122,c_9]) ).
% 1.01/0.85  
% 1.01/0.85  cnf(c_212,plain,
% 1.01/0.85      ( k9_relat_1(sK2,k1_setfam_1(k2_tarski(X0_39,k10_relat_1(sK2,X1_39)))) = k1_setfam_1(k2_tarski(k9_relat_1(sK2,X0_39),X1_39)) ),
% 1.01/0.85      inference(subtyping,[status(esa)],[c_126]) ).
% 1.01/0.85  
% 1.01/0.85  cnf(c_306,plain,
% 1.01/0.85      ( k1_setfam_1(k2_tarski(k9_relat_1(sK2,k10_relat_1(sK2,sK0)),sK1)) = k9_relat_1(sK2,k10_relat_1(sK2,sK0)) ),
% 1.01/0.85      inference(superposition,[status(thm)],[c_207,c_212]) ).
% 1.01/0.85  
% 1.01/0.85  cnf(c_6,negated_conjecture,
% 1.01/0.85      ( r1_tarski(sK0,k2_relat_1(sK2)) ),
% 1.01/0.85      inference(cnf_transformation,[],[f27]) ).
% 1.01/0.85  
% 1.01/0.85  cnf(c_3,plain,
% 1.01/0.85      ( ~ r1_tarski(X0,k2_relat_1(X1))
% 1.01/0.85      | ~ v1_relat_1(X1)
% 1.01/0.85      | ~ v1_funct_1(X1)
% 1.01/0.85      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ),
% 1.01/0.85      inference(cnf_transformation,[],[f22]) ).
% 1.01/0.85  
% 1.01/0.85  cnf(c_103,plain,
% 1.01/0.85      ( ~ r1_tarski(X0,k2_relat_1(X1))
% 1.01/0.85      | ~ v1_relat_1(X1)
% 1.01/0.85      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
% 1.01/0.85      | sK2 != X1 ),
% 1.01/0.85      inference(resolution_lifted,[status(thm)],[c_3,c_8]) ).
% 1.01/0.85  
% 1.01/0.85  cnf(c_104,plain,
% 1.01/0.85      ( ~ r1_tarski(X0,k2_relat_1(sK2))
% 1.01/0.85      | ~ v1_relat_1(sK2)
% 1.01/0.85      | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0 ),
% 1.01/0.85      inference(unflattening,[status(thm)],[c_103]) ).
% 1.01/0.85  
% 1.01/0.85  cnf(c_108,plain,
% 1.01/0.85      ( ~ r1_tarski(X0,k2_relat_1(sK2))
% 1.01/0.85      | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0 ),
% 1.01/0.85      inference(global_propositional_subsumption,
% 1.01/0.85                [status(thm)],
% 1.01/0.85                [c_104,c_9]) ).
% 1.01/0.85  
% 1.01/0.85  cnf(c_178,plain,
% 1.01/0.85      ( k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0
% 1.01/0.85      | k2_relat_1(sK2) != k2_relat_1(sK2)
% 1.01/0.85      | sK0 != X0 ),
% 1.01/0.85      inference(resolution_lifted,[status(thm)],[c_6,c_108]) ).
% 1.01/0.85  
% 1.01/0.85  cnf(c_179,plain,
% 1.01/0.85      ( k9_relat_1(sK2,k10_relat_1(sK2,sK0)) = sK0 ),
% 1.01/0.85      inference(unflattening,[status(thm)],[c_178]) ).
% 1.01/0.85  
% 1.01/0.85  cnf(c_204,plain,
% 1.01/0.85      ( k9_relat_1(sK2,k10_relat_1(sK2,sK0)) = sK0 ),
% 1.01/0.85      inference(subtyping,[status(esa)],[c_179]) ).
% 1.01/0.85  
% 1.01/0.85  cnf(c_307,plain,
% 1.01/0.85      ( k1_setfam_1(k2_tarski(sK0,sK1)) = sK0 ),
% 1.01/0.85      inference(light_normalisation,[status(thm)],[c_306,c_204]) ).
% 1.01/0.85  
% 1.01/0.85  cnf(c_216,plain,
% 1.01/0.85      ( X0_39 != X1_39 | X2_39 != X1_39 | X2_39 = X0_39 ),
% 1.01/0.85      theory(equality) ).
% 1.01/0.85  
% 1.01/0.85  cnf(c_301,plain,
% 1.01/0.85      ( k1_setfam_1(k2_tarski(X0_39,sK1)) != X1_39
% 1.01/0.85      | sK0 != X1_39
% 1.01/0.85      | sK0 = k1_setfam_1(k2_tarski(X0_39,sK1)) ),
% 1.01/0.85      inference(instantiation,[status(thm)],[c_216]) ).
% 1.01/0.85  
% 1.01/0.85  cnf(c_302,plain,
% 1.01/0.85      ( k1_setfam_1(k2_tarski(sK0,sK1)) != sK0
% 1.01/0.85      | sK0 = k1_setfam_1(k2_tarski(sK0,sK1))
% 1.01/0.85      | sK0 != sK0 ),
% 1.01/0.85      inference(instantiation,[status(thm)],[c_301]) ).
% 1.01/0.85  
% 1.01/0.85  cnf(c_0,plain,
% 1.01/0.85      ( k1_setfam_1(k2_tarski(X0,X1)) = k1_setfam_1(k2_tarski(X1,X0)) ),
% 1.01/0.85      inference(cnf_transformation,[],[f29]) ).
% 1.01/0.85  
% 1.01/0.85  cnf(c_213,plain,
% 1.01/0.85      ( k1_setfam_1(k2_tarski(X0_39,X1_39)) = k1_setfam_1(k2_tarski(X1_39,X0_39)) ),
% 1.01/0.85      inference(subtyping,[status(esa)],[c_0]) ).
% 1.01/0.85  
% 1.01/0.85  cnf(c_278,plain,
% 1.01/0.85      ( k1_setfam_1(k2_tarski(sK1,X0_39)) = k1_setfam_1(k2_tarski(X0_39,sK1)) ),
% 1.01/0.85      inference(instantiation,[status(thm)],[c_213]) ).
% 1.01/0.85  
% 1.01/0.85  cnf(c_280,plain,
% 1.01/0.85      ( k1_setfam_1(k2_tarski(sK1,sK0)) = k1_setfam_1(k2_tarski(sK0,sK1)) ),
% 1.01/0.85      inference(instantiation,[status(thm)],[c_278]) ).
% 1.01/0.85  
% 1.01/0.85  cnf(c_268,plain,
% 1.01/0.85      ( k1_setfam_1(k2_tarski(sK1,X0_39)) != X1_39
% 1.01/0.85      | k1_setfam_1(k2_tarski(sK1,X0_39)) = sK0
% 1.01/0.85      | sK0 != X1_39 ),
% 1.01/0.85      inference(instantiation,[status(thm)],[c_216]) ).
% 1.01/0.85  
% 1.01/0.85  cnf(c_277,plain,
% 1.01/0.85      ( k1_setfam_1(k2_tarski(sK1,X0_39)) != k1_setfam_1(k2_tarski(X0_39,sK1))
% 1.01/0.85      | k1_setfam_1(k2_tarski(sK1,X0_39)) = sK0
% 1.01/0.85      | sK0 != k1_setfam_1(k2_tarski(X0_39,sK1)) ),
% 1.01/0.85      inference(instantiation,[status(thm)],[c_268]) ).
% 1.01/0.85  
% 1.01/0.85  cnf(c_279,plain,
% 1.01/0.85      ( k1_setfam_1(k2_tarski(sK1,sK0)) != k1_setfam_1(k2_tarski(sK0,sK1))
% 1.01/0.85      | k1_setfam_1(k2_tarski(sK1,sK0)) = sK0
% 1.01/0.85      | sK0 != k1_setfam_1(k2_tarski(sK0,sK1)) ),
% 1.01/0.85      inference(instantiation,[status(thm)],[c_277]) ).
% 1.01/0.85  
% 1.01/0.85  cnf(c_1,plain,
% 1.01/0.85      ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
% 1.01/0.85      inference(cnf_transformation,[],[f30]) ).
% 1.01/0.85  
% 1.01/0.85  cnf(c_5,negated_conjecture,
% 1.01/0.85      ( ~ r1_tarski(sK0,sK1) ),
% 1.01/0.85      inference(cnf_transformation,[],[f28]) ).
% 1.01/0.85  
% 1.01/0.85  cnf(c_142,plain,
% 1.01/0.85      ( k1_setfam_1(k2_tarski(X0,X1)) != sK0 | sK1 != X0 ),
% 1.01/0.85      inference(resolution_lifted,[status(thm)],[c_1,c_5]) ).
% 1.01/0.85  
% 1.01/0.85  cnf(c_143,plain,
% 1.01/0.85      ( k1_setfam_1(k2_tarski(sK1,X0)) != sK0 ),
% 1.01/0.85      inference(unflattening,[status(thm)],[c_142]) ).
% 1.01/0.85  
% 1.01/0.85  cnf(c_210,plain,
% 1.01/0.85      ( k1_setfam_1(k2_tarski(sK1,X0_39)) != sK0 ),
% 1.01/0.85      inference(subtyping,[status(esa)],[c_143]) ).
% 1.01/0.85  
% 1.01/0.85  cnf(c_230,plain,
% 1.01/0.85      ( k1_setfam_1(k2_tarski(sK1,sK0)) != sK0 ),
% 1.01/0.85      inference(instantiation,[status(thm)],[c_210]) ).
% 1.01/0.85  
% 1.01/0.85  cnf(c_214,plain,( X0_39 = X0_39 ),theory(equality) ).
% 1.01/0.85  
% 1.01/0.85  cnf(c_225,plain,
% 1.01/0.85      ( sK0 = sK0 ),
% 1.01/0.85      inference(instantiation,[status(thm)],[c_214]) ).
% 1.01/0.85  
% 1.01/0.85  cnf(contradiction,plain,
% 1.01/0.85      ( $false ),
% 1.01/0.85      inference(minisat,
% 1.01/0.85                [status(thm)],
% 1.01/0.85                [c_307,c_302,c_280,c_279,c_230,c_225]) ).
% 1.01/0.85  
% 1.01/0.85  
% 1.01/0.85  % SZS output end CNFRefutation for theBenchmark.p
% 1.01/0.85  
% 1.01/0.85  ------                               Statistics
% 1.01/0.85  
% 1.01/0.85  ------ General
% 1.01/0.85  
% 1.01/0.85  abstr_ref_over_cycles:                  0
% 1.01/0.85  abstr_ref_under_cycles:                 0
% 1.01/0.85  gc_basic_clause_elim:                   0
% 1.01/0.85  forced_gc_time:                         0
% 1.01/0.85  parsing_time:                           0.007
% 1.01/0.85  unif_index_cands_time:                  0.
% 1.01/0.85  unif_index_add_time:                    0.
% 1.01/0.85  orderings_time:                         0.
% 1.01/0.85  out_proof_time:                         0.007
% 1.01/0.85  total_time:                             0.041
% 1.01/0.85  num_of_symbols:                         42
% 1.01/0.85  num_of_terms:                           624
% 1.01/0.85  
% 1.01/0.85  ------ Preprocessing
% 1.01/0.85  
% 1.01/0.85  num_of_splits:                          0
% 1.01/0.85  num_of_split_atoms:                     0
% 1.01/0.85  num_of_reused_defs:                     0
% 1.01/0.85  num_eq_ax_congr_red:                    4
% 1.01/0.85  num_of_sem_filtered_clauses:            0
% 1.01/0.85  num_of_subtypes:                        3
% 1.01/0.85  monotx_restored_types:                  0
% 1.01/0.85  sat_num_of_epr_types:                   0
% 1.01/0.85  sat_num_of_non_cyclic_types:            0
% 1.01/0.85  sat_guarded_non_collapsed_types:        0
% 1.01/0.85  num_pure_diseq_elim:                    0
% 1.01/0.85  simp_replaced_by:                       0
% 1.01/0.85  res_preprocessed:                       28
% 1.01/0.85  prep_upred:                             0
% 1.01/0.85  prep_unflattend:                        13
% 1.01/0.85  smt_new_axioms:                         0
% 1.01/0.85  pred_elim_cands:                        3
% 1.01/0.85  pred_elim:                              3
% 1.01/0.85  pred_elim_cl:                           -1
% 1.01/0.85  pred_elim_cycles:                       4
% 1.01/0.85  merged_defs:                            0
% 1.01/0.85  merged_defs_ncl:                        0
% 1.01/0.85  bin_hyper_res:                          0
% 1.01/0.85  prep_cycles:                            2
% 1.01/0.85  pred_elim_time:                         0.001
% 1.01/0.85  splitting_time:                         0.
% 1.01/0.85  sem_filter_time:                        0.
% 1.01/0.85  monotx_time:                            0.
% 1.01/0.85  subtype_inf_time:                       0.
% 1.01/0.85  
% 1.01/0.85  ------ Problem properties
% 1.01/0.85  
% 1.01/0.85  clauses:                                11
% 1.01/0.85  conjectures:                            0
% 1.01/0.85  epr:                                    0
% 1.01/0.85  horn:                                   11
% 1.01/0.85  ground:                                 6
% 1.01/0.85  unary:                                  8
% 1.01/0.85  binary:                                 3
% 1.01/0.85  lits:                                   14
% 1.01/0.85  lits_eq:                                14
% 1.01/0.85  fd_pure:                                0
% 1.01/0.85  fd_pseudo:                              0
% 1.01/0.85  fd_cond:                                0
% 1.01/0.85  fd_pseudo_cond:                         0
% 1.01/0.85  ac_symbols:                             0
% 1.01/0.85  
% 1.01/0.85  ------ Propositional Solver
% 1.01/0.85  
% 1.01/0.85  prop_solver_calls:                      16
% 1.01/0.85  prop_fast_solver_calls:                 113
% 1.01/0.85  smt_solver_calls:                       0
% 1.01/0.85  smt_fast_solver_calls:                  0
% 1.01/0.85  prop_num_of_clauses:                    114
% 1.01/0.85  prop_preprocess_simplified:             582
% 1.01/0.85  prop_fo_subsumed:                       2
% 1.01/0.85  prop_solver_time:                       0.
% 1.01/0.85  smt_solver_time:                        0.
% 1.01/0.85  smt_fast_solver_time:                   0.
% 1.01/0.85  prop_fast_solver_time:                  0.
% 1.01/0.85  prop_unsat_core_time:                   0.
% 1.01/0.85  
% 1.01/0.85  ------ QBF
% 1.01/0.85  
% 1.01/0.85  qbf_q_res:                              0
% 1.01/0.85  qbf_num_tautologies:                    0
% 1.01/0.85  qbf_prep_cycles:                        0
% 1.01/0.85  
% 1.01/0.85  ------ BMC1
% 1.01/0.85  
% 1.01/0.85  bmc1_current_bound:                     -1
% 1.01/0.85  bmc1_last_solved_bound:                 -1
% 1.01/0.85  bmc1_unsat_core_size:                   -1
% 1.01/0.85  bmc1_unsat_core_parents_size:           -1
% 1.01/0.85  bmc1_merge_next_fun:                    0
% 1.01/0.85  bmc1_unsat_core_clauses_time:           0.
% 1.01/0.85  
% 1.01/0.85  ------ Instantiation
% 1.01/0.85  
% 1.01/0.85  inst_num_of_clauses:                    36
% 1.01/0.85  inst_num_in_passive:                    3
% 1.01/0.85  inst_num_in_active:                     28
% 1.01/0.85  inst_num_in_unprocessed:                5
% 1.01/0.85  inst_num_of_loops:                      30
% 1.01/0.85  inst_num_of_learning_restarts:          0
% 1.01/0.85  inst_num_moves_active_passive:          0
% 1.01/0.85  inst_lit_activity:                      0
% 1.01/0.85  inst_lit_activity_moves:                0
% 1.01/0.85  inst_num_tautologies:                   0
% 1.01/0.85  inst_num_prop_implied:                  0
% 1.01/0.85  inst_num_existing_simplified:           0
% 1.01/0.85  inst_num_eq_res_simplified:             0
% 1.01/0.85  inst_num_child_elim:                    0
% 1.01/0.85  inst_num_of_dismatching_blockings:      0
% 1.01/0.85  inst_num_of_non_proper_insts:           14
% 1.01/0.85  inst_num_of_duplicates:                 0
% 1.01/0.85  inst_inst_num_from_inst_to_res:         0
% 1.01/0.85  inst_dismatching_checking_time:         0.
% 1.01/0.85  
% 1.01/0.85  ------ Resolution
% 1.01/0.85  
% 1.01/0.85  res_num_of_clauses:                     0
% 1.01/0.85  res_num_in_passive:                     0
% 1.01/0.85  res_num_in_active:                      0
% 1.01/0.85  res_num_of_loops:                       30
% 1.01/0.85  res_forward_subset_subsumed:            1
% 1.01/0.85  res_backward_subset_subsumed:           0
% 1.01/0.85  res_forward_subsumed:                   0
% 1.01/0.85  res_backward_subsumed:                  0
% 1.01/0.85  res_forward_subsumption_resolution:     0
% 1.01/0.85  res_backward_subsumption_resolution:    0
% 1.01/0.85  res_clause_to_clause_subsumption:       13
% 1.01/0.85  res_orphan_elimination:                 0
% 1.01/0.85  res_tautology_del:                      2
% 1.01/0.85  res_num_eq_res_simplified:              1
% 1.01/0.85  res_num_sel_changes:                    0
% 1.01/0.85  res_moves_from_active_to_pass:          0
% 1.01/0.85  
% 1.01/0.85  ------ Superposition
% 1.01/0.85  
% 1.01/0.85  sup_time_total:                         0.
% 1.01/0.85  sup_time_generating:                    0.
% 1.01/0.85  sup_time_sim_full:                      0.
% 1.01/0.85  sup_time_sim_immed:                     0.
% 1.01/0.85  
% 1.01/0.85  sup_num_of_clauses:                     12
% 1.01/0.85  sup_num_in_active:                      6
% 1.01/0.85  sup_num_in_passive:                     6
% 1.01/0.85  sup_num_of_loops:                       5
% 1.01/0.85  sup_fw_superposition:                   1
% 1.01/0.85  sup_bw_superposition:                   0
% 1.01/0.85  sup_immediate_simplified:               1
% 1.01/0.85  sup_given_eliminated:                   0
% 1.01/0.85  comparisons_done:                       0
% 1.01/0.85  comparisons_avoided:                    0
% 1.01/0.85  
% 1.01/0.85  ------ Simplifications
% 1.01/0.85  
% 1.01/0.85  
% 1.01/0.85  sim_fw_subset_subsumed:                 0
% 1.01/0.85  sim_bw_subset_subsumed:                 0
% 1.01/0.85  sim_fw_subsumed:                        0
% 1.01/0.85  sim_bw_subsumed:                        0
% 1.01/0.85  sim_fw_subsumption_res:                 0
% 1.01/0.85  sim_bw_subsumption_res:                 0
% 1.01/0.85  sim_tautology_del:                      0
% 1.01/0.85  sim_eq_tautology_del:                   0
% 1.01/0.85  sim_eq_res_simp:                        1
% 1.01/0.85  sim_fw_demodulated:                     0
% 1.01/0.85  sim_bw_demodulated:                     0
% 1.01/0.85  sim_light_normalised:                   1
% 1.01/0.85  sim_joinable_taut:                      0
% 1.01/0.85  sim_joinable_simp:                      0
% 1.01/0.85  sim_ac_normalised:                      0
% 1.01/0.85  sim_smt_subsumption:                    0
% 1.01/0.85  
%------------------------------------------------------------------------------
