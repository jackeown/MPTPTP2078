%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:26:10 EST 2020

% Result     : Theorem 11.56s
% Output     : CNFRefutation 11.56s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 328 expanded)
%              Number of clauses        :   45 ( 149 expanded)
%              Number of leaves         :   11 (  74 expanded)
%              Depth                    :   19
%              Number of atoms          :  159 ( 760 expanded)
%              Number of equality atoms :   16 (  73 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X3)
        & r1_xboole_0(X1,X3)
        & r1_xboole_0(X0,X3) )
     => r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X3)
          & r1_xboole_0(X1,X3)
          & r1_xboole_0(X0,X3) )
       => r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3)
      & r1_xboole_0(X2,X3)
      & r1_xboole_0(X1,X3)
      & r1_xboole_0(X0,X3) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3)
      & r1_xboole_0(X2,X3)
      & r1_xboole_0(X1,X3)
      & r1_xboole_0(X0,X3) ) ),
    inference(flattening,[],[f15])).

fof(f17,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3)
        & r1_xboole_0(X2,X3)
        & r1_xboole_0(X1,X3)
        & r1_xboole_0(X0,X3) )
   => ( ~ r1_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3)
      & r1_xboole_0(sK2,sK3)
      & r1_xboole_0(sK1,sK3)
      & r1_xboole_0(sK0,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ~ r1_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3)
    & r1_xboole_0(sK2,sK3)
    & r1_xboole_0(sK1,sK3)
    & r1_xboole_0(sK0,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f17])).

fof(f29,plain,(
    ~ r1_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( r1_xboole_0(k3_xboole_0(X0,X1),X1)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k3_xboole_0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k3_xboole_0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f28,plain,(
    r1_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f27,plain,(
    r1_xboole_0(sK1,sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f26,plain,(
    r1_xboole_0(sK0,sK3) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_7,negated_conjecture,
    ( ~ r1_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_179,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_175,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1470,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_179,c_175])).

cnf(c_6,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_1486,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(k3_xboole_0(X0,X2),X3)
    | r1_xboole_0(k3_xboole_0(X0,k2_xboole_0(X1,X2)),X3) ),
    inference(resolution,[status(thm)],[c_1470,c_6])).

cnf(c_5,plain,
    ( r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(k3_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_8511,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X0,k2_xboole_0(X1,X2))
    | ~ r1_xboole_0(k3_xboole_0(X0,X2),k2_xboole_0(X1,X2)) ),
    inference(resolution,[status(thm)],[c_1486,c_5])).

cnf(c_1,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_1484,plain,
    ( ~ r1_xboole_0(k3_xboole_0(X0,X1),X2)
    | r1_xboole_0(k3_xboole_0(X1,X0),X2) ),
    inference(resolution,[status(thm)],[c_1470,c_1])).

cnf(c_3,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_xboole_0(X1,X2)
    | r1_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_101,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X1)
    | X0 != X3
    | k3_xboole_0(X3,X4) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_4])).

cnf(c_102,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(k3_xboole_0(X0,X2),X1) ),
    inference(unflattening,[status(thm)],[c_101])).

cnf(c_1625,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(k3_xboole_0(X2,X0),X1) ),
    inference(resolution,[status(thm)],[c_1484,c_102])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_692,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,k3_xboole_0(X0,X2)) ),
    inference(resolution,[status(thm)],[c_102,c_2])).

cnf(c_844,plain,
    ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
    | ~ r1_xboole_0(X1,k3_xboole_0(X0,k3_xboole_0(X1,X2))) ),
    inference(resolution,[status(thm)],[c_692,c_5])).

cnf(c_858,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(resolution,[status(thm)],[c_844,c_692])).

cnf(c_868,plain,
    ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
    | ~ r1_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,X2)),X1) ),
    inference(resolution,[status(thm)],[c_858,c_5])).

cnf(c_1649,plain,
    ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
    | ~ r1_xboole_0(k3_xboole_0(X1,X2),X1) ),
    inference(resolution,[status(thm)],[c_1625,c_868])).

cnf(c_866,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(k3_xboole_0(X1,X2),X0) ),
    inference(resolution,[status(thm)],[c_858,c_2])).

cnf(c_1635,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(k3_xboole_0(X2,X1),X0) ),
    inference(resolution,[status(thm)],[c_1484,c_866])).

cnf(c_2064,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,k3_xboole_0(X0,X1)) ),
    inference(resolution,[status(thm)],[c_1649,c_1635])).

cnf(c_2548,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(resolution,[status(thm)],[c_2064,c_2])).

cnf(c_46232,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(X0,X2)
    | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(resolution,[status(thm)],[c_8511,c_2548])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_1482,plain,
    ( ~ r1_xboole_0(k2_xboole_0(X0,X1),X2)
    | r1_xboole_0(k2_xboole_0(X1,X0),X2) ),
    inference(resolution,[status(thm)],[c_1470,c_0])).

cnf(c_1499,plain,
    ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
    | r1_xboole_0(k2_xboole_0(X2,X1),k3_xboole_0(X0,X3)) ),
    inference(resolution,[status(thm)],[c_1482,c_692])).

cnf(c_4935,plain,
    ( r1_xboole_0(X0,k3_xboole_0(k2_xboole_0(X1,X2),X3))
    | ~ r1_xboole_0(X0,k2_xboole_0(X2,X1)) ),
    inference(resolution,[status(thm)],[c_1499,c_844])).

cnf(c_15283,plain,
    ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
    | r1_xboole_0(k3_xboole_0(k2_xboole_0(X2,X1),X3),X0) ),
    inference(resolution,[status(thm)],[c_4935,c_2])).

cnf(c_44787,plain,
    ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
    | r1_xboole_0(k2_xboole_0(X2,X1),X0) ),
    inference(resolution,[status(thm)],[c_15283,c_5])).

cnf(c_57278,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(X0,X2)
    | r1_xboole_0(k2_xboole_0(X2,X1),X0) ),
    inference(resolution,[status(thm)],[c_46232,c_44787])).

cnf(c_60149,plain,
    ( ~ r1_xboole_0(sK3,k2_xboole_0(sK0,sK1))
    | ~ r1_xboole_0(sK3,sK2) ),
    inference(resolution,[status(thm)],[c_7,c_57278])).

cnf(c_8,negated_conjecture,
    ( r1_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_390,plain,
    ( r1_xboole_0(sK3,sK2)
    | ~ r1_xboole_0(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_60152,plain,
    ( ~ r1_xboole_0(sK3,k2_xboole_0(sK0,sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_60149,c_8,c_390])).

cnf(c_2060,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,k3_xboole_0(X1,X0)) ),
    inference(resolution,[status(thm)],[c_1649,c_1625])).

cnf(c_2521,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(k3_xboole_0(X1,X0),X2) ),
    inference(resolution,[status(thm)],[c_2060,c_2])).

cnf(c_46238,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(X2,X0)
    | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(resolution,[status(thm)],[c_8511,c_2521])).

cnf(c_60165,plain,
    ( ~ r1_xboole_0(sK3,sK0)
    | ~ r1_xboole_0(sK1,sK3) ),
    inference(resolution,[status(thm)],[c_60152,c_46238])).

cnf(c_396,plain,
    ( r1_xboole_0(sK3,sK0)
    | ~ r1_xboole_0(sK0,sK3) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_9,negated_conjecture,
    ( r1_xboole_0(sK1,sK3) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_10,negated_conjecture,
    ( r1_xboole_0(sK0,sK3) ),
    inference(cnf_transformation,[],[f26])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_60165,c_396,c_9,c_10])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:13:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 11.56/1.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.56/1.98  
% 11.56/1.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.56/1.98  
% 11.56/1.98  ------  iProver source info
% 11.56/1.98  
% 11.56/1.98  git: date: 2020-06-30 10:37:57 +0100
% 11.56/1.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.56/1.98  git: non_committed_changes: false
% 11.56/1.98  git: last_make_outside_of_git: false
% 11.56/1.98  
% 11.56/1.98  ------ 
% 11.56/1.98  ------ Parsing...
% 11.56/1.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.56/1.98  
% 11.56/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 11.56/1.98  
% 11.56/1.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.56/1.98  
% 11.56/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.56/1.98  ------ Proving...
% 11.56/1.98  ------ Problem Properties 
% 11.56/1.98  
% 11.56/1.98  
% 11.56/1.98  clauses                                 10
% 11.56/1.98  conjectures                             4
% 11.56/1.98  EPR                                     4
% 11.56/1.98  Horn                                    10
% 11.56/1.98  unary                                   6
% 11.56/1.98  binary                                  4
% 11.56/1.98  lits                                    14
% 11.56/1.98  lits eq                                 3
% 11.56/1.98  fd_pure                                 0
% 11.56/1.98  fd_pseudo                               0
% 11.56/1.98  fd_cond                                 0
% 11.56/1.98  fd_pseudo_cond                          0
% 11.56/1.98  AC symbols                              0
% 11.56/1.98  
% 11.56/1.98  ------ Input Options Time Limit: Unbounded
% 11.56/1.98  
% 11.56/1.98  
% 11.56/1.98  ------ 
% 11.56/1.98  Current options:
% 11.56/1.98  ------ 
% 11.56/1.98  
% 11.56/1.98  
% 11.56/1.98  
% 11.56/1.98  
% 11.56/1.98  ------ Proving...
% 11.56/1.98  
% 11.56/1.98  
% 11.56/1.98  % SZS status Theorem for theBenchmark.p
% 11.56/1.98  
% 11.56/1.98  % SZS output start CNFRefutation for theBenchmark.p
% 11.56/1.98  
% 11.56/1.98  fof(f8,conjecture,(
% 11.56/1.98    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X3) & r1_xboole_0(X1,X3) & r1_xboole_0(X0,X3)) => r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3))),
% 11.56/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.56/1.98  
% 11.56/1.98  fof(f9,negated_conjecture,(
% 11.56/1.98    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X3) & r1_xboole_0(X1,X3) & r1_xboole_0(X0,X3)) => r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3))),
% 11.56/1.98    inference(negated_conjecture,[],[f8])).
% 11.56/1.98  
% 11.56/1.98  fof(f15,plain,(
% 11.56/1.98    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) & (r1_xboole_0(X2,X3) & r1_xboole_0(X1,X3) & r1_xboole_0(X0,X3)))),
% 11.56/1.98    inference(ennf_transformation,[],[f9])).
% 11.56/1.98  
% 11.56/1.98  fof(f16,plain,(
% 11.56/1.98    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) & r1_xboole_0(X2,X3) & r1_xboole_0(X1,X3) & r1_xboole_0(X0,X3))),
% 11.56/1.98    inference(flattening,[],[f15])).
% 11.56/1.98  
% 11.56/1.98  fof(f17,plain,(
% 11.56/1.98    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) & r1_xboole_0(X2,X3) & r1_xboole_0(X1,X3) & r1_xboole_0(X0,X3)) => (~r1_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3) & r1_xboole_0(sK2,sK3) & r1_xboole_0(sK1,sK3) & r1_xboole_0(sK0,sK3))),
% 11.56/1.98    introduced(choice_axiom,[])).
% 11.56/1.98  
% 11.56/1.98  fof(f18,plain,(
% 11.56/1.98    ~r1_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3) & r1_xboole_0(sK2,sK3) & r1_xboole_0(sK1,sK3) & r1_xboole_0(sK0,sK3)),
% 11.56/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f17])).
% 11.56/1.98  
% 11.56/1.98  fof(f29,plain,(
% 11.56/1.98    ~r1_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3)),
% 11.56/1.98    inference(cnf_transformation,[],[f18])).
% 11.56/1.98  
% 11.56/1.98  fof(f7,axiom,(
% 11.56/1.98    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2)))),
% 11.56/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.56/1.98  
% 11.56/1.98  fof(f14,plain,(
% 11.56/1.98    ! [X0,X1,X2] : (k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X1))),
% 11.56/1.98    inference(ennf_transformation,[],[f7])).
% 11.56/1.98  
% 11.56/1.98  fof(f25,plain,(
% 11.56/1.98    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X1)) )),
% 11.56/1.98    inference(cnf_transformation,[],[f14])).
% 11.56/1.98  
% 11.56/1.98  fof(f6,axiom,(
% 11.56/1.98    ! [X0,X1] : ~(r1_xboole_0(k3_xboole_0(X0,X1),X1) & ~r1_xboole_0(X0,X1))),
% 11.56/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.56/1.98  
% 11.56/1.98  fof(f13,plain,(
% 11.56/1.98    ! [X0,X1] : (~r1_xboole_0(k3_xboole_0(X0,X1),X1) | r1_xboole_0(X0,X1))),
% 11.56/1.98    inference(ennf_transformation,[],[f6])).
% 11.56/1.98  
% 11.56/1.98  fof(f24,plain,(
% 11.56/1.98    ( ! [X0,X1] : (~r1_xboole_0(k3_xboole_0(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 11.56/1.98    inference(cnf_transformation,[],[f13])).
% 11.56/1.98  
% 11.56/1.98  fof(f2,axiom,(
% 11.56/1.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 11.56/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.56/1.98  
% 11.56/1.98  fof(f20,plain,(
% 11.56/1.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 11.56/1.98    inference(cnf_transformation,[],[f2])).
% 11.56/1.98  
% 11.56/1.98  fof(f4,axiom,(
% 11.56/1.98    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 11.56/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.56/1.98  
% 11.56/1.98  fof(f22,plain,(
% 11.56/1.98    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 11.56/1.98    inference(cnf_transformation,[],[f4])).
% 11.56/1.98  
% 11.56/1.98  fof(f5,axiom,(
% 11.56/1.98    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 11.56/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.56/1.98  
% 11.56/1.98  fof(f11,plain,(
% 11.56/1.98    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 11.56/1.98    inference(ennf_transformation,[],[f5])).
% 11.56/1.98  
% 11.56/1.98  fof(f12,plain,(
% 11.56/1.98    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 11.56/1.98    inference(flattening,[],[f11])).
% 11.56/1.98  
% 11.56/1.98  fof(f23,plain,(
% 11.56/1.98    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)) )),
% 11.56/1.98    inference(cnf_transformation,[],[f12])).
% 11.56/1.98  
% 11.56/1.98  fof(f3,axiom,(
% 11.56/1.98    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 11.56/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.56/1.98  
% 11.56/1.98  fof(f10,plain,(
% 11.56/1.98    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 11.56/1.98    inference(ennf_transformation,[],[f3])).
% 11.56/1.98  
% 11.56/1.98  fof(f21,plain,(
% 11.56/1.98    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 11.56/1.98    inference(cnf_transformation,[],[f10])).
% 11.56/1.98  
% 11.56/1.98  fof(f1,axiom,(
% 11.56/1.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 11.56/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.56/1.98  
% 11.56/1.98  fof(f19,plain,(
% 11.56/1.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 11.56/1.98    inference(cnf_transformation,[],[f1])).
% 11.56/1.98  
% 11.56/1.98  fof(f28,plain,(
% 11.56/1.98    r1_xboole_0(sK2,sK3)),
% 11.56/1.98    inference(cnf_transformation,[],[f18])).
% 11.56/1.98  
% 11.56/1.98  fof(f27,plain,(
% 11.56/1.98    r1_xboole_0(sK1,sK3)),
% 11.56/1.98    inference(cnf_transformation,[],[f18])).
% 11.56/1.98  
% 11.56/1.98  fof(f26,plain,(
% 11.56/1.98    r1_xboole_0(sK0,sK3)),
% 11.56/1.98    inference(cnf_transformation,[],[f18])).
% 11.56/1.98  
% 11.56/1.98  cnf(c_7,negated_conjecture,
% 11.56/1.98      ( ~ r1_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3) ),
% 11.56/1.98      inference(cnf_transformation,[],[f29]) ).
% 11.56/1.98  
% 11.56/1.98  cnf(c_179,plain,
% 11.56/1.98      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X3) | X2 != X0 | X3 != X1 ),
% 11.56/1.98      theory(equality) ).
% 11.56/1.98  
% 11.56/1.98  cnf(c_175,plain,( X0 = X0 ),theory(equality) ).
% 11.56/1.98  
% 11.56/1.98  cnf(c_1470,plain,
% 11.56/1.98      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X1) | X2 != X0 ),
% 11.56/1.98      inference(resolution,[status(thm)],[c_179,c_175]) ).
% 11.56/1.98  
% 11.56/1.98  cnf(c_6,plain,
% 11.56/1.98      ( ~ r1_xboole_0(X0,X1)
% 11.56/1.98      | k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) ),
% 11.56/1.98      inference(cnf_transformation,[],[f25]) ).
% 11.56/1.98  
% 11.56/1.98  cnf(c_1486,plain,
% 11.56/1.98      ( ~ r1_xboole_0(X0,X1)
% 11.56/1.98      | ~ r1_xboole_0(k3_xboole_0(X0,X2),X3)
% 11.56/1.98      | r1_xboole_0(k3_xboole_0(X0,k2_xboole_0(X1,X2)),X3) ),
% 11.56/1.98      inference(resolution,[status(thm)],[c_1470,c_6]) ).
% 11.56/1.98  
% 11.56/1.98  cnf(c_5,plain,
% 11.56/1.98      ( r1_xboole_0(X0,X1) | ~ r1_xboole_0(k3_xboole_0(X0,X1),X1) ),
% 11.56/1.98      inference(cnf_transformation,[],[f24]) ).
% 11.56/1.98  
% 11.56/1.98  cnf(c_8511,plain,
% 11.56/1.98      ( ~ r1_xboole_0(X0,X1)
% 11.56/1.98      | r1_xboole_0(X0,k2_xboole_0(X1,X2))
% 11.56/1.98      | ~ r1_xboole_0(k3_xboole_0(X0,X2),k2_xboole_0(X1,X2)) ),
% 11.56/1.98      inference(resolution,[status(thm)],[c_1486,c_5]) ).
% 11.56/1.98  
% 11.56/1.98  cnf(c_1,plain,
% 11.56/1.98      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 11.56/1.98      inference(cnf_transformation,[],[f20]) ).
% 11.56/1.98  
% 11.56/1.98  cnf(c_1484,plain,
% 11.56/1.98      ( ~ r1_xboole_0(k3_xboole_0(X0,X1),X2)
% 11.56/1.98      | r1_xboole_0(k3_xboole_0(X1,X0),X2) ),
% 11.56/1.98      inference(resolution,[status(thm)],[c_1470,c_1]) ).
% 11.56/1.98  
% 11.56/1.98  cnf(c_3,plain,
% 11.56/1.98      ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
% 11.56/1.98      inference(cnf_transformation,[],[f22]) ).
% 11.56/1.98  
% 11.56/1.98  cnf(c_4,plain,
% 11.56/1.98      ( ~ r1_tarski(X0,X1) | ~ r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2) ),
% 11.56/1.98      inference(cnf_transformation,[],[f23]) ).
% 11.56/1.98  
% 11.56/1.98  cnf(c_101,plain,
% 11.56/1.98      ( ~ r1_xboole_0(X0,X1)
% 11.56/1.98      | r1_xboole_0(X2,X1)
% 11.56/1.98      | X0 != X3
% 11.56/1.98      | k3_xboole_0(X3,X4) != X2 ),
% 11.56/1.98      inference(resolution_lifted,[status(thm)],[c_3,c_4]) ).
% 11.56/1.98  
% 11.56/1.98  cnf(c_102,plain,
% 11.56/1.98      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(k3_xboole_0(X0,X2),X1) ),
% 11.56/1.98      inference(unflattening,[status(thm)],[c_101]) ).
% 11.56/1.98  
% 11.56/1.98  cnf(c_1625,plain,
% 11.56/1.98      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(k3_xboole_0(X2,X0),X1) ),
% 11.56/1.98      inference(resolution,[status(thm)],[c_1484,c_102]) ).
% 11.56/1.98  
% 11.56/1.98  cnf(c_2,plain,
% 11.56/1.98      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 11.56/1.98      inference(cnf_transformation,[],[f21]) ).
% 11.56/1.98  
% 11.56/1.98  cnf(c_692,plain,
% 11.56/1.98      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,k3_xboole_0(X0,X2)) ),
% 11.56/1.98      inference(resolution,[status(thm)],[c_102,c_2]) ).
% 11.56/1.98  
% 11.56/1.98  cnf(c_844,plain,
% 11.56/1.98      ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
% 11.56/1.98      | ~ r1_xboole_0(X1,k3_xboole_0(X0,k3_xboole_0(X1,X2))) ),
% 11.56/1.98      inference(resolution,[status(thm)],[c_692,c_5]) ).
% 11.56/1.98  
% 11.56/1.98  cnf(c_858,plain,
% 11.56/1.98      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X0,k3_xboole_0(X1,X2)) ),
% 11.56/1.98      inference(resolution,[status(thm)],[c_844,c_692]) ).
% 11.56/1.98  
% 11.56/1.98  cnf(c_868,plain,
% 11.56/1.98      ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
% 11.56/1.98      | ~ r1_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,X2)),X1) ),
% 11.56/1.98      inference(resolution,[status(thm)],[c_858,c_5]) ).
% 11.56/1.98  
% 11.56/1.98  cnf(c_1649,plain,
% 11.56/1.98      ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
% 11.56/1.98      | ~ r1_xboole_0(k3_xboole_0(X1,X2),X1) ),
% 11.56/1.98      inference(resolution,[status(thm)],[c_1625,c_868]) ).
% 11.56/1.98  
% 11.56/1.98  cnf(c_866,plain,
% 11.56/1.98      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(k3_xboole_0(X1,X2),X0) ),
% 11.56/1.98      inference(resolution,[status(thm)],[c_858,c_2]) ).
% 11.56/1.98  
% 11.56/1.98  cnf(c_1635,plain,
% 11.56/1.98      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(k3_xboole_0(X2,X1),X0) ),
% 11.56/1.98      inference(resolution,[status(thm)],[c_1484,c_866]) ).
% 11.56/1.98  
% 11.56/1.98  cnf(c_2064,plain,
% 11.56/1.98      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,k3_xboole_0(X0,X1)) ),
% 11.56/1.98      inference(resolution,[status(thm)],[c_1649,c_1635]) ).
% 11.56/1.98  
% 11.56/1.98  cnf(c_2548,plain,
% 11.56/1.98      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(k3_xboole_0(X0,X1),X2) ),
% 11.56/1.98      inference(resolution,[status(thm)],[c_2064,c_2]) ).
% 11.56/1.98  
% 11.56/1.98  cnf(c_46232,plain,
% 11.56/1.98      ( ~ r1_xboole_0(X0,X1)
% 11.56/1.98      | ~ r1_xboole_0(X0,X2)
% 11.56/1.98      | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 11.56/1.98      inference(resolution,[status(thm)],[c_8511,c_2548]) ).
% 11.56/1.98  
% 11.56/1.98  cnf(c_0,plain,
% 11.56/1.98      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 11.56/1.98      inference(cnf_transformation,[],[f19]) ).
% 11.56/1.98  
% 11.56/1.98  cnf(c_1482,plain,
% 11.56/1.98      ( ~ r1_xboole_0(k2_xboole_0(X0,X1),X2)
% 11.56/1.98      | r1_xboole_0(k2_xboole_0(X1,X0),X2) ),
% 11.56/1.98      inference(resolution,[status(thm)],[c_1470,c_0]) ).
% 11.56/1.98  
% 11.56/1.98  cnf(c_1499,plain,
% 11.56/1.98      ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
% 11.56/1.98      | r1_xboole_0(k2_xboole_0(X2,X1),k3_xboole_0(X0,X3)) ),
% 11.56/1.98      inference(resolution,[status(thm)],[c_1482,c_692]) ).
% 11.56/1.98  
% 11.56/1.98  cnf(c_4935,plain,
% 11.56/1.98      ( r1_xboole_0(X0,k3_xboole_0(k2_xboole_0(X1,X2),X3))
% 11.56/1.98      | ~ r1_xboole_0(X0,k2_xboole_0(X2,X1)) ),
% 11.56/1.98      inference(resolution,[status(thm)],[c_1499,c_844]) ).
% 11.56/1.98  
% 11.56/1.98  cnf(c_15283,plain,
% 11.56/1.98      ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
% 11.56/1.98      | r1_xboole_0(k3_xboole_0(k2_xboole_0(X2,X1),X3),X0) ),
% 11.56/1.98      inference(resolution,[status(thm)],[c_4935,c_2]) ).
% 11.56/1.98  
% 11.56/1.98  cnf(c_44787,plain,
% 11.56/1.98      ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
% 11.56/1.98      | r1_xboole_0(k2_xboole_0(X2,X1),X0) ),
% 11.56/1.98      inference(resolution,[status(thm)],[c_15283,c_5]) ).
% 11.56/1.98  
% 11.56/1.98  cnf(c_57278,plain,
% 11.56/1.98      ( ~ r1_xboole_0(X0,X1)
% 11.56/1.98      | ~ r1_xboole_0(X0,X2)
% 11.56/1.98      | r1_xboole_0(k2_xboole_0(X2,X1),X0) ),
% 11.56/1.98      inference(resolution,[status(thm)],[c_46232,c_44787]) ).
% 11.56/1.98  
% 11.56/1.98  cnf(c_60149,plain,
% 11.56/1.98      ( ~ r1_xboole_0(sK3,k2_xboole_0(sK0,sK1))
% 11.56/1.98      | ~ r1_xboole_0(sK3,sK2) ),
% 11.56/1.98      inference(resolution,[status(thm)],[c_7,c_57278]) ).
% 11.56/1.98  
% 11.56/1.98  cnf(c_8,negated_conjecture,
% 11.56/1.98      ( r1_xboole_0(sK2,sK3) ),
% 11.56/1.98      inference(cnf_transformation,[],[f28]) ).
% 11.56/1.98  
% 11.56/1.98  cnf(c_390,plain,
% 11.56/1.98      ( r1_xboole_0(sK3,sK2) | ~ r1_xboole_0(sK2,sK3) ),
% 11.56/1.98      inference(instantiation,[status(thm)],[c_2]) ).
% 11.56/1.98  
% 11.56/1.98  cnf(c_60152,plain,
% 11.56/1.98      ( ~ r1_xboole_0(sK3,k2_xboole_0(sK0,sK1)) ),
% 11.56/1.98      inference(global_propositional_subsumption,
% 11.56/1.98                [status(thm)],
% 11.56/1.98                [c_60149,c_8,c_390]) ).
% 11.56/1.98  
% 11.56/1.98  cnf(c_2060,plain,
% 11.56/1.98      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,k3_xboole_0(X1,X0)) ),
% 11.56/1.98      inference(resolution,[status(thm)],[c_1649,c_1625]) ).
% 11.56/1.98  
% 11.56/1.98  cnf(c_2521,plain,
% 11.56/1.98      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(k3_xboole_0(X1,X0),X2) ),
% 11.56/1.98      inference(resolution,[status(thm)],[c_2060,c_2]) ).
% 11.56/1.98  
% 11.56/1.98  cnf(c_46238,plain,
% 11.56/1.98      ( ~ r1_xboole_0(X0,X1)
% 11.56/1.98      | ~ r1_xboole_0(X2,X0)
% 11.56/1.98      | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 11.56/1.98      inference(resolution,[status(thm)],[c_8511,c_2521]) ).
% 11.56/1.98  
% 11.56/1.98  cnf(c_60165,plain,
% 11.56/1.98      ( ~ r1_xboole_0(sK3,sK0) | ~ r1_xboole_0(sK1,sK3) ),
% 11.56/1.98      inference(resolution,[status(thm)],[c_60152,c_46238]) ).
% 11.56/1.98  
% 11.56/1.98  cnf(c_396,plain,
% 11.56/1.98      ( r1_xboole_0(sK3,sK0) | ~ r1_xboole_0(sK0,sK3) ),
% 11.56/1.98      inference(instantiation,[status(thm)],[c_2]) ).
% 11.56/1.98  
% 11.56/1.98  cnf(c_9,negated_conjecture,
% 11.56/1.98      ( r1_xboole_0(sK1,sK3) ),
% 11.56/1.98      inference(cnf_transformation,[],[f27]) ).
% 11.56/1.98  
% 11.56/1.98  cnf(c_10,negated_conjecture,
% 11.56/1.98      ( r1_xboole_0(sK0,sK3) ),
% 11.56/1.98      inference(cnf_transformation,[],[f26]) ).
% 11.56/1.98  
% 11.56/1.98  cnf(contradiction,plain,
% 11.56/1.98      ( $false ),
% 11.56/1.98      inference(minisat,[status(thm)],[c_60165,c_396,c_9,c_10]) ).
% 11.56/1.98  
% 11.56/1.98  
% 11.56/1.98  % SZS output end CNFRefutation for theBenchmark.p
% 11.56/1.98  
% 11.56/1.98  ------                               Statistics
% 11.56/1.98  
% 11.56/1.98  ------ Selected
% 11.56/1.98  
% 11.56/1.98  total_time:                             1.342
% 11.56/1.98  
%------------------------------------------------------------------------------
