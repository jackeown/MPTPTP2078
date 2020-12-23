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
% DateTime   : Thu Dec  3 11:36:41 EST 2020

% Result     : Theorem 3.83s
% Output     : CNFRefutation 3.83s
% Verified   : 
% Statistics : Number of formulae       :   59 (  93 expanded)
%              Number of clauses        :   31 (  43 expanded)
%              Number of leaves         :   13 (  23 expanded)
%              Depth                    :   15
%              Number of atoms          :  101 ( 155 expanded)
%              Number of equality atoms :   20 (  39 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f36,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X0,X1)) ),
    inference(definition_unfolding,[],[f29,f24])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f13,conjecture,(
    ! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1))) ),
    inference(negated_conjecture,[],[f13])).

fof(f19,plain,(
    ? [X0,X1] : ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1))) ),
    inference(ennf_transformation,[],[f14])).

fof(f20,plain,
    ( ? [X0,X1] : ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1)))
   => ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f20])).

fof(f34,plain,(
    ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    inference(cnf_transformation,[],[f21])).

fof(f7,axiom,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f38,plain,(
    ~ r1_tarski(k5_xboole_0(k5_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)))),k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f34,f28,f24,f24])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k5_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k5_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k5_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_88,plain,
    ( ~ r1_tarski(X0_36,X1_36)
    | r1_tarski(X2_36,X3_36)
    | X2_36 != X0_36
    | X3_36 != X1_36 ),
    theory(equality)).

cnf(c_1,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_78,plain,
    ( k5_xboole_0(X0_36,X1_36) = k5_xboole_0(X1_36,X0_36) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1148,plain,
    ( ~ r1_tarski(X0_36,k5_xboole_0(X1_36,X2_36))
    | r1_tarski(X3_36,k5_xboole_0(X2_36,X1_36))
    | X3_36 != X0_36 ),
    inference(resolution,[status(thm)],[c_88,c_78])).

cnf(c_5,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_74,plain,
    ( r1_tarski(k5_xboole_0(X0_36,k3_xboole_0(X0_36,X1_36)),k5_xboole_0(X0_36,X1_36)) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_12441,plain,
    ( r1_tarski(X0_36,k5_xboole_0(X1_36,X2_36))
    | X0_36 != k5_xboole_0(X2_36,k3_xboole_0(X2_36,X1_36)) ),
    inference(resolution,[status(thm)],[c_1148,c_74])).

cnf(c_13240,plain,
    ( r1_tarski(k5_xboole_0(k3_xboole_0(X0_36,X1_36),X0_36),k5_xboole_0(X1_36,X0_36)) ),
    inference(resolution,[status(thm)],[c_12441,c_78])).

cnf(c_83,plain,
    ( X0_36 = X0_36 ),
    theory(equality)).

cnf(c_1152,plain,
    ( ~ r1_tarski(X0_36,X1_36)
    | r1_tarski(X2_36,X1_36)
    | X2_36 != X0_36 ),
    inference(resolution,[status(thm)],[c_88,c_83])).

cnf(c_90,plain,
    ( X0_36 != X1_36
    | k1_zfmisc_1(X0_36) = k1_zfmisc_1(X1_36) ),
    theory(equality)).

cnf(c_1524,plain,
    ( ~ r1_tarski(k1_zfmisc_1(X0_36),X1_36)
    | r1_tarski(k1_zfmisc_1(X2_36),X1_36)
    | X2_36 != X0_36 ),
    inference(resolution,[status(thm)],[c_1152,c_90])).

cnf(c_5064,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k5_xboole_0(X0_36,X1_36)),X2_36)
    | r1_tarski(k1_zfmisc_1(k5_xboole_0(X1_36,X0_36)),X2_36) ),
    inference(resolution,[status(thm)],[c_1524,c_78])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_72,plain,
    ( ~ r1_tarski(X0_36,X1_36)
    | r1_tarski(k1_zfmisc_1(X0_36),k1_zfmisc_1(X1_36)) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_5105,plain,
    ( ~ r1_tarski(k5_xboole_0(X0_36,X1_36),X2_36)
    | r1_tarski(k1_zfmisc_1(k5_xboole_0(X1_36,X0_36)),k1_zfmisc_1(X2_36)) ),
    inference(resolution,[status(thm)],[c_5064,c_72])).

cnf(c_8,negated_conjecture,
    ( ~ r1_tarski(k5_xboole_0(k5_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)))),k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_71,negated_conjecture,
    ( ~ r1_tarski(k5_xboole_0(k5_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)))),k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_4,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_81,negated_conjecture,
    ( ~ r1_tarski(k5_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k5_xboole_0(k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)))))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    inference(theory_normalisation,[status(thm)],[c_71,c_4,c_1])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(k5_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_76,plain,
    ( ~ r1_tarski(X0_36,X1_36)
    | ~ r1_tarski(X2_36,X1_36)
    | r1_tarski(k5_xboole_0(X0_36,X2_36),X1_36) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_523,plain,
    ( ~ r1_tarski(k5_xboole_0(k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))
    | ~ r1_tarski(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    inference(resolution,[status(thm)],[c_81,c_76])).

cnf(c_531,plain,
    ( ~ r1_tarski(k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))
    | ~ r1_tarski(k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))
    | ~ r1_tarski(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    inference(resolution,[status(thm)],[c_523,c_76])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k3_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_77,plain,
    ( ~ r1_tarski(X0_36,X1_36)
    | r1_tarski(k3_xboole_0(X0_36,X2_36),X1_36) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_671,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))
    | ~ r1_tarski(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_531,c_77])).

cnf(c_5691,plain,
    ( ~ r1_tarski(k5_xboole_0(k3_xboole_0(sK1,sK0),sK1),k5_xboole_0(sK0,sK1))
    | ~ r1_tarski(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    inference(resolution,[status(thm)],[c_5105,c_671])).

cnf(c_5701,plain,
    ( ~ r1_tarski(k5_xboole_0(k3_xboole_0(sK1,sK0),sK1),k5_xboole_0(sK0,sK1))
    | ~ r1_tarski(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k5_xboole_0(sK0,sK1)) ),
    inference(resolution,[status(thm)],[c_5691,c_72])).

cnf(c_5708,plain,
    ( ~ r1_tarski(k5_xboole_0(k3_xboole_0(sK1,sK0),sK1),k5_xboole_0(sK0,sK1)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5701,c_74])).

cnf(c_14119,plain,
    ( $false ),
    inference(backward_subsumption_resolution,[status(thm)],[c_13240,c_5708])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:15:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.83/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.83/1.00  
% 3.83/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.83/1.00  
% 3.83/1.00  ------  iProver source info
% 3.83/1.00  
% 3.83/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.83/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.83/1.00  git: non_committed_changes: false
% 3.83/1.00  git: last_make_outside_of_git: false
% 3.83/1.00  
% 3.83/1.00  ------ 
% 3.83/1.00  ------ Parsing...
% 3.83/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.83/1.00  
% 3.83/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.83/1.00  
% 3.83/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.83/1.00  
% 3.83/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.83/1.00  ------ Proving...
% 3.83/1.00  ------ Problem Properties 
% 3.83/1.00  
% 3.83/1.00  
% 3.83/1.00  clauses                                 9
% 3.83/1.00  conjectures                             1
% 3.83/1.00  EPR                                     0
% 3.83/1.00  Horn                                    9
% 3.83/1.00  unary                                   6
% 3.83/1.00  binary                                  2
% 3.83/1.00  lits                                    13
% 3.83/1.00  lits eq                                 4
% 3.83/1.00  fd_pure                                 0
% 3.83/1.00  fd_pseudo                               0
% 3.83/1.00  fd_cond                                 0
% 3.83/1.00  fd_pseudo_cond                          0
% 3.83/1.00  AC symbols                              1
% 3.83/1.00  
% 3.83/1.00  ------ Input Options Time Limit: Unbounded
% 3.83/1.00  
% 3.83/1.00  
% 3.83/1.00  ------ 
% 3.83/1.00  Current options:
% 3.83/1.00  ------ 
% 3.83/1.00  
% 3.83/1.00  
% 3.83/1.00  
% 3.83/1.00  
% 3.83/1.00  ------ Proving...
% 3.83/1.00  
% 3.83/1.00  
% 3.83/1.00  % SZS status Theorem for theBenchmark.p
% 3.83/1.00  
% 3.83/1.00   Resolution empty clause
% 3.83/1.00  
% 3.83/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.83/1.00  
% 3.83/1.00  fof(f2,axiom,(
% 3.83/1.00    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 3.83/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.83/1.00  
% 3.83/1.00  fof(f23,plain,(
% 3.83/1.00    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 3.83/1.00    inference(cnf_transformation,[],[f2])).
% 3.83/1.00  
% 3.83/1.00  fof(f8,axiom,(
% 3.83/1.00    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 3.83/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.83/1.00  
% 3.83/1.00  fof(f29,plain,(
% 3.83/1.00    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 3.83/1.00    inference(cnf_transformation,[],[f8])).
% 3.83/1.00  
% 3.83/1.00  fof(f3,axiom,(
% 3.83/1.00    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 3.83/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.83/1.00  
% 3.83/1.00  fof(f24,plain,(
% 3.83/1.00    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 3.83/1.00    inference(cnf_transformation,[],[f3])).
% 3.83/1.00  
% 3.83/1.00  fof(f36,plain,(
% 3.83/1.00    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X0,X1))) )),
% 3.83/1.00    inference(definition_unfolding,[],[f29,f24])).
% 3.83/1.00  
% 3.83/1.00  fof(f12,axiom,(
% 3.83/1.00    ! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)))),
% 3.83/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.83/1.00  
% 3.83/1.00  fof(f18,plain,(
% 3.83/1.00    ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 3.83/1.00    inference(ennf_transformation,[],[f12])).
% 3.83/1.00  
% 3.83/1.00  fof(f33,plain,(
% 3.83/1.00    ( ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.83/1.00    inference(cnf_transformation,[],[f18])).
% 3.83/1.00  
% 3.83/1.00  fof(f13,conjecture,(
% 3.83/1.00    ! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1)))),
% 3.83/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.83/1.00  
% 3.83/1.00  fof(f14,negated_conjecture,(
% 3.83/1.00    ~! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1)))),
% 3.83/1.00    inference(negated_conjecture,[],[f13])).
% 3.83/1.00  
% 3.83/1.00  fof(f19,plain,(
% 3.83/1.00    ? [X0,X1] : ~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1)))),
% 3.83/1.00    inference(ennf_transformation,[],[f14])).
% 3.83/1.00  
% 3.83/1.00  fof(f20,plain,(
% 3.83/1.00    ? [X0,X1] : ~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1))) => ~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),
% 3.83/1.00    introduced(choice_axiom,[])).
% 3.83/1.00  
% 3.83/1.00  fof(f21,plain,(
% 3.83/1.00    ~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),
% 3.83/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f20])).
% 3.83/1.00  
% 3.83/1.00  fof(f34,plain,(
% 3.83/1.00    ~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),
% 3.83/1.00    inference(cnf_transformation,[],[f21])).
% 3.83/1.00  
% 3.83/1.00  fof(f7,axiom,(
% 3.83/1.00    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)),
% 3.83/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.83/1.00  
% 3.83/1.00  fof(f28,plain,(
% 3.83/1.00    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 3.83/1.00    inference(cnf_transformation,[],[f7])).
% 3.83/1.00  
% 3.83/1.00  fof(f38,plain,(
% 3.83/1.00    ~r1_tarski(k5_xboole_0(k5_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)))),k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),
% 3.83/1.00    inference(definition_unfolding,[],[f34,f28,f24,f24])).
% 3.83/1.00  
% 3.83/1.00  fof(f6,axiom,(
% 3.83/1.00    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 3.83/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.83/1.00  
% 3.83/1.00  fof(f27,plain,(
% 3.83/1.00    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 3.83/1.00    inference(cnf_transformation,[],[f6])).
% 3.83/1.00  
% 3.83/1.00  fof(f5,axiom,(
% 3.83/1.00    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k5_xboole_0(X0,X2),X1))),
% 3.83/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.83/1.00  
% 3.83/1.00  fof(f16,plain,(
% 3.83/1.00    ! [X0,X1,X2] : (r1_tarski(k5_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 3.83/1.00    inference(ennf_transformation,[],[f5])).
% 3.83/1.00  
% 3.83/1.00  fof(f17,plain,(
% 3.83/1.00    ! [X0,X1,X2] : (r1_tarski(k5_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 3.83/1.00    inference(flattening,[],[f16])).
% 3.83/1.00  
% 3.83/1.00  fof(f26,plain,(
% 3.83/1.00    ( ! [X2,X0,X1] : (r1_tarski(k5_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 3.83/1.00    inference(cnf_transformation,[],[f17])).
% 3.83/1.00  
% 3.83/1.00  fof(f4,axiom,(
% 3.83/1.00    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k3_xboole_0(X0,X2),X1))),
% 3.83/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.83/1.00  
% 3.83/1.00  fof(f15,plain,(
% 3.83/1.00    ! [X0,X1,X2] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 3.83/1.00    inference(ennf_transformation,[],[f4])).
% 3.83/1.00  
% 3.83/1.00  fof(f25,plain,(
% 3.83/1.00    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 3.83/1.00    inference(cnf_transformation,[],[f15])).
% 3.83/1.00  
% 3.83/1.00  cnf(c_88,plain,
% 3.83/1.00      ( ~ r1_tarski(X0_36,X1_36)
% 3.83/1.00      | r1_tarski(X2_36,X3_36)
% 3.83/1.00      | X2_36 != X0_36
% 3.83/1.00      | X3_36 != X1_36 ),
% 3.83/1.00      theory(equality) ).
% 3.83/1.00  
% 3.83/1.00  cnf(c_1,plain,
% 3.83/1.00      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 3.83/1.00      inference(cnf_transformation,[],[f23]) ).
% 3.83/1.00  
% 3.83/1.00  cnf(c_78,plain,
% 3.83/1.00      ( k5_xboole_0(X0_36,X1_36) = k5_xboole_0(X1_36,X0_36) ),
% 3.83/1.00      inference(subtyping,[status(esa)],[c_1]) ).
% 3.83/1.00  
% 3.83/1.00  cnf(c_1148,plain,
% 3.83/1.00      ( ~ r1_tarski(X0_36,k5_xboole_0(X1_36,X2_36))
% 3.83/1.00      | r1_tarski(X3_36,k5_xboole_0(X2_36,X1_36))
% 3.83/1.00      | X3_36 != X0_36 ),
% 3.83/1.00      inference(resolution,[status(thm)],[c_88,c_78]) ).
% 3.83/1.00  
% 3.83/1.00  cnf(c_5,plain,
% 3.83/1.00      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X0,X1)) ),
% 3.83/1.00      inference(cnf_transformation,[],[f36]) ).
% 3.83/1.00  
% 3.83/1.00  cnf(c_74,plain,
% 3.83/1.00      ( r1_tarski(k5_xboole_0(X0_36,k3_xboole_0(X0_36,X1_36)),k5_xboole_0(X0_36,X1_36)) ),
% 3.83/1.00      inference(subtyping,[status(esa)],[c_5]) ).
% 3.83/1.00  
% 3.83/1.00  cnf(c_12441,plain,
% 3.83/1.00      ( r1_tarski(X0_36,k5_xboole_0(X1_36,X2_36))
% 3.83/1.00      | X0_36 != k5_xboole_0(X2_36,k3_xboole_0(X2_36,X1_36)) ),
% 3.83/1.00      inference(resolution,[status(thm)],[c_1148,c_74]) ).
% 3.83/1.00  
% 3.83/1.00  cnf(c_13240,plain,
% 3.83/1.00      ( r1_tarski(k5_xboole_0(k3_xboole_0(X0_36,X1_36),X0_36),k5_xboole_0(X1_36,X0_36)) ),
% 3.83/1.00      inference(resolution,[status(thm)],[c_12441,c_78]) ).
% 3.83/1.00  
% 3.83/1.00  cnf(c_83,plain,( X0_36 = X0_36 ),theory(equality) ).
% 3.83/1.00  
% 3.83/1.00  cnf(c_1152,plain,
% 3.83/1.00      ( ~ r1_tarski(X0_36,X1_36) | r1_tarski(X2_36,X1_36) | X2_36 != X0_36 ),
% 3.83/1.00      inference(resolution,[status(thm)],[c_88,c_83]) ).
% 3.83/1.00  
% 3.83/1.00  cnf(c_90,plain,
% 3.83/1.00      ( X0_36 != X1_36 | k1_zfmisc_1(X0_36) = k1_zfmisc_1(X1_36) ),
% 3.83/1.00      theory(equality) ).
% 3.83/1.00  
% 3.83/1.00  cnf(c_1524,plain,
% 3.83/1.00      ( ~ r1_tarski(k1_zfmisc_1(X0_36),X1_36)
% 3.83/1.00      | r1_tarski(k1_zfmisc_1(X2_36),X1_36)
% 3.83/1.00      | X2_36 != X0_36 ),
% 3.83/1.00      inference(resolution,[status(thm)],[c_1152,c_90]) ).
% 3.83/1.00  
% 3.83/1.00  cnf(c_5064,plain,
% 3.83/1.00      ( ~ r1_tarski(k1_zfmisc_1(k5_xboole_0(X0_36,X1_36)),X2_36)
% 3.83/1.00      | r1_tarski(k1_zfmisc_1(k5_xboole_0(X1_36,X0_36)),X2_36) ),
% 3.83/1.00      inference(resolution,[status(thm)],[c_1524,c_78]) ).
% 3.83/1.00  
% 3.83/1.00  cnf(c_7,plain,
% 3.83/1.00      ( ~ r1_tarski(X0,X1) | r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ),
% 3.83/1.00      inference(cnf_transformation,[],[f33]) ).
% 3.83/1.00  
% 3.83/1.00  cnf(c_72,plain,
% 3.83/1.00      ( ~ r1_tarski(X0_36,X1_36)
% 3.83/1.00      | r1_tarski(k1_zfmisc_1(X0_36),k1_zfmisc_1(X1_36)) ),
% 3.83/1.00      inference(subtyping,[status(esa)],[c_7]) ).
% 3.83/1.00  
% 3.83/1.00  cnf(c_5105,plain,
% 3.83/1.00      ( ~ r1_tarski(k5_xboole_0(X0_36,X1_36),X2_36)
% 3.83/1.00      | r1_tarski(k1_zfmisc_1(k5_xboole_0(X1_36,X0_36)),k1_zfmisc_1(X2_36)) ),
% 3.83/1.00      inference(resolution,[status(thm)],[c_5064,c_72]) ).
% 3.83/1.00  
% 3.83/1.00  cnf(c_8,negated_conjecture,
% 3.83/1.00      ( ~ r1_tarski(k5_xboole_0(k5_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)))),k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
% 3.83/1.00      inference(cnf_transformation,[],[f38]) ).
% 3.83/1.00  
% 3.83/1.00  cnf(c_71,negated_conjecture,
% 3.83/1.00      ( ~ r1_tarski(k5_xboole_0(k5_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)))),k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
% 3.83/1.00      inference(subtyping,[status(esa)],[c_8]) ).
% 3.83/1.00  
% 3.83/1.00  cnf(c_4,plain,
% 3.83/1.00      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 3.83/1.00      inference(cnf_transformation,[],[f27]) ).
% 3.83/1.00  
% 3.83/1.00  cnf(c_81,negated_conjecture,
% 3.83/1.00      ( ~ r1_tarski(k5_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k5_xboole_0(k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)))))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
% 3.83/1.00      inference(theory_normalisation,[status(thm)],[c_71,c_4,c_1]) ).
% 3.83/1.00  
% 3.83/1.00  cnf(c_3,plain,
% 3.83/1.00      ( ~ r1_tarski(X0,X1)
% 3.83/1.00      | ~ r1_tarski(X2,X1)
% 3.83/1.00      | r1_tarski(k5_xboole_0(X0,X2),X1) ),
% 3.83/1.00      inference(cnf_transformation,[],[f26]) ).
% 3.83/1.00  
% 3.83/1.00  cnf(c_76,plain,
% 3.83/1.00      ( ~ r1_tarski(X0_36,X1_36)
% 3.83/1.00      | ~ r1_tarski(X2_36,X1_36)
% 3.83/1.00      | r1_tarski(k5_xboole_0(X0_36,X2_36),X1_36) ),
% 3.83/1.00      inference(subtyping,[status(esa)],[c_3]) ).
% 3.83/1.00  
% 3.83/1.00  cnf(c_523,plain,
% 3.83/1.00      ( ~ r1_tarski(k5_xboole_0(k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))
% 3.83/1.00      | ~ r1_tarski(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
% 3.83/1.00      inference(resolution,[status(thm)],[c_81,c_76]) ).
% 3.83/1.00  
% 3.83/1.00  cnf(c_531,plain,
% 3.83/1.00      ( ~ r1_tarski(k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))
% 3.83/1.00      | ~ r1_tarski(k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))
% 3.83/1.00      | ~ r1_tarski(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
% 3.83/1.00      inference(resolution,[status(thm)],[c_523,c_76]) ).
% 3.83/1.00  
% 3.83/1.00  cnf(c_2,plain,
% 3.83/1.00      ( ~ r1_tarski(X0,X1) | r1_tarski(k3_xboole_0(X0,X2),X1) ),
% 3.83/1.00      inference(cnf_transformation,[],[f25]) ).
% 3.83/1.00  
% 3.83/1.00  cnf(c_77,plain,
% 3.83/1.00      ( ~ r1_tarski(X0_36,X1_36) | r1_tarski(k3_xboole_0(X0_36,X2_36),X1_36) ),
% 3.83/1.00      inference(subtyping,[status(esa)],[c_2]) ).
% 3.83/1.00  
% 3.83/1.00  cnf(c_671,plain,
% 3.83/1.00      ( ~ r1_tarski(k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))
% 3.83/1.00      | ~ r1_tarski(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
% 3.83/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_531,c_77]) ).
% 3.83/1.00  
% 3.83/1.00  cnf(c_5691,plain,
% 3.83/1.00      ( ~ r1_tarski(k5_xboole_0(k3_xboole_0(sK1,sK0),sK1),k5_xboole_0(sK0,sK1))
% 3.83/1.00      | ~ r1_tarski(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
% 3.83/1.00      inference(resolution,[status(thm)],[c_5105,c_671]) ).
% 3.83/1.00  
% 3.83/1.00  cnf(c_5701,plain,
% 3.83/1.00      ( ~ r1_tarski(k5_xboole_0(k3_xboole_0(sK1,sK0),sK1),k5_xboole_0(sK0,sK1))
% 3.83/1.00      | ~ r1_tarski(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k5_xboole_0(sK0,sK1)) ),
% 3.83/1.00      inference(resolution,[status(thm)],[c_5691,c_72]) ).
% 3.83/1.00  
% 3.83/1.00  cnf(c_5708,plain,
% 3.83/1.00      ( ~ r1_tarski(k5_xboole_0(k3_xboole_0(sK1,sK0),sK1),k5_xboole_0(sK0,sK1)) ),
% 3.83/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_5701,c_74]) ).
% 3.83/1.00  
% 3.83/1.00  cnf(c_14119,plain,
% 3.83/1.00      ( $false ),
% 3.83/1.00      inference(backward_subsumption_resolution,[status(thm)],[c_13240,c_5708]) ).
% 3.83/1.00  
% 3.83/1.00  
% 3.83/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.83/1.00  
% 3.83/1.00  ------                               Statistics
% 3.83/1.00  
% 3.83/1.00  ------ Selected
% 3.83/1.00  
% 3.83/1.00  total_time:                             0.445
% 3.83/1.00  
%------------------------------------------------------------------------------
