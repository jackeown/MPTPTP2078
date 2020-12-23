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
% DateTime   : Thu Dec  3 11:43:06 EST 2020

% Result     : Theorem 7.68s
% Output     : CNFRefutation 7.68s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 106 expanded)
%              Number of clauses        :   39 (  44 expanded)
%              Number of leaves         :   13 (  30 expanded)
%              Depth                    :   11
%              Number of atoms          :  143 ( 257 expanded)
%              Number of equality atoms :   56 (  68 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k6_subset_1(X1,X0)) ),
    inference(definition_unfolding,[],[f24,f27])).

fof(f10,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1)))
          & v1_relat_1(X1) )
     => ( ~ r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(X0,sK1)))
        & v1_relat_1(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1)))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(sK0,X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ~ r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(sK0,sK1)))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f21,f20])).

fof(f33,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f34,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) = k2_relat_1(k2_xboole_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) = k2_relat_1(k2_xboole_0(X0,X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) = k2_relat_1(k2_xboole_0(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k4_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f28,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k4_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k6_subset_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f28,f27])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k6_subset_1(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(definition_unfolding,[],[f25,f27])).

fof(f35,plain,(
    ~ r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_123,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_677,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(X2),k2_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,sK1))))
    | k2_relat_1(X2) != X0
    | k2_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,sK1))) != X1 ),
    inference(instantiation,[status(thm)],[c_123])).

cnf(c_1033,plain,
    ( ~ r1_tarski(X0,k2_relat_1(X1))
    | r1_tarski(k2_relat_1(X2),k2_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,sK1))))
    | k2_relat_1(X2) != X0
    | k2_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,sK1))) != k2_relat_1(X1) ),
    inference(instantiation,[status(thm)],[c_677])).

cnf(c_7710,plain,
    ( ~ r1_tarski(X0,k2_relat_1(k2_xboole_0(sK1,sK0)))
    | r1_tarski(k2_relat_1(X1),k2_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,sK1))))
    | k2_relat_1(X1) != X0
    | k2_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,sK1))) != k2_relat_1(k2_xboole_0(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_1033])).

cnf(c_17780,plain,
    ( r1_tarski(k2_relat_1(X0),k2_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,sK1))))
    | ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(k2_xboole_0(sK1,sK0)))
    | k2_relat_1(X0) != k2_relat_1(sK0)
    | k2_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,sK1))) != k2_relat_1(k2_xboole_0(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_7710])).

cnf(c_17783,plain,
    ( r1_tarski(k2_relat_1(sK0),k2_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,sK1))))
    | ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(k2_xboole_0(sK1,sK0)))
    | k2_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,sK1))) != k2_relat_1(k2_xboole_0(sK1,sK0))
    | k2_relat_1(sK0) != k2_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_17780])).

cnf(c_1,plain,
    ( k2_xboole_0(X0,k6_subset_1(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_3901,plain,
    ( k2_xboole_0(sK1,k6_subset_1(sK0,sK1)) = k2_xboole_0(sK1,sK0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_125,plain,
    ( X0 != X1
    | k2_relat_1(X0) = k2_relat_1(X1) ),
    theory(equality)).

cnf(c_1736,plain,
    ( k2_xboole_0(sK1,k6_subset_1(sK0,sK1)) != X0
    | k2_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,sK1))) = k2_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_125])).

cnf(c_3683,plain,
    ( k2_xboole_0(sK1,k6_subset_1(sK0,sK1)) != k2_xboole_0(sK1,sK0)
    | k2_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,sK1))) = k2_relat_1(k2_xboole_0(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_1736])).

cnf(c_11,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_293,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_10,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_294,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) = k2_relat_1(k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_296,plain,
    ( k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) = k2_relat_1(k2_xboole_0(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_645,plain,
    ( k2_xboole_0(k2_relat_1(sK1),k2_relat_1(X0)) = k2_relat_1(k2_xboole_0(sK1,X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_294,c_296])).

cnf(c_771,plain,
    ( k2_xboole_0(k2_relat_1(sK1),k2_relat_1(sK0)) = k2_relat_1(k2_xboole_0(sK1,sK0)) ),
    inference(superposition,[status(thm)],[c_293,c_645])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_3,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_301,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_509,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_301])).

cnf(c_864,plain,
    ( r1_tarski(k2_relat_1(sK0),k2_relat_1(k2_xboole_0(sK1,sK0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_771,c_509])).

cnf(c_872,plain,
    ( r1_tarski(k2_relat_1(sK0),k2_relat_1(k2_xboole_0(sK1,sK0))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_864])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k6_subset_1(X0,X1)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_545,plain,
    ( v1_relat_1(k6_subset_1(sK0,sK1))
    | ~ v1_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_527,plain,
    ( ~ v1_relat_1(k6_subset_1(sK0,sK1))
    | ~ v1_relat_1(sK1)
    | k2_xboole_0(k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1))) = k2_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,sK1))) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_324,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(sK0),k2_xboole_0(k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1))))
    | k2_xboole_0(k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1))) != X1
    | k2_relat_1(sK0) != X0 ),
    inference(instantiation,[status(thm)],[c_123])).

cnf(c_352,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | r1_tarski(k2_relat_1(sK0),k2_xboole_0(k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1))))
    | k2_xboole_0(k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1))) != X1
    | k2_relat_1(sK0) != k2_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_324])).

cnf(c_432,plain,
    ( ~ r1_tarski(k2_relat_1(X0),k2_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,sK1))))
    | r1_tarski(k2_relat_1(sK0),k2_xboole_0(k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1))))
    | k2_xboole_0(k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1))) != k2_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,sK1)))
    | k2_relat_1(sK0) != k2_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_352])).

cnf(c_434,plain,
    ( r1_tarski(k2_relat_1(sK0),k2_xboole_0(k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1))))
    | ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,sK1))))
    | k2_xboole_0(k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1))) != k2_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,sK1)))
    | k2_relat_1(sK0) != k2_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_432])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
    | r1_tarski(k6_subset_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_316,plain,
    ( r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(sK0,sK1)))
    | ~ r1_tarski(k2_relat_1(sK0),k2_xboole_0(k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1)))) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_119,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_131,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_119])).

cnf(c_129,plain,
    ( k2_relat_1(sK0) = k2_relat_1(sK0)
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_125])).

cnf(c_9,negated_conjecture,
    ( ~ r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f35])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_17783,c_3901,c_3683,c_872,c_545,c_527,c_434,c_316,c_131,c_129,c_9,c_10,c_11])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:53:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.68/1.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.68/1.48  
% 7.68/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.68/1.48  
% 7.68/1.48  ------  iProver source info
% 7.68/1.48  
% 7.68/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.68/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.68/1.48  git: non_committed_changes: false
% 7.68/1.48  git: last_make_outside_of_git: false
% 7.68/1.48  
% 7.68/1.48  ------ 
% 7.68/1.48  
% 7.68/1.48  ------ Input Options
% 7.68/1.48  
% 7.68/1.48  --out_options                           all
% 7.68/1.48  --tptp_safe_out                         true
% 7.68/1.48  --problem_path                          ""
% 7.68/1.48  --include_path                          ""
% 7.68/1.48  --clausifier                            res/vclausify_rel
% 7.68/1.48  --clausifier_options                    ""
% 7.68/1.48  --stdin                                 false
% 7.68/1.48  --stats_out                             all
% 7.68/1.48  
% 7.68/1.48  ------ General Options
% 7.68/1.48  
% 7.68/1.48  --fof                                   false
% 7.68/1.48  --time_out_real                         305.
% 7.68/1.48  --time_out_virtual                      -1.
% 7.68/1.48  --symbol_type_check                     false
% 7.68/1.48  --clausify_out                          false
% 7.68/1.48  --sig_cnt_out                           false
% 7.68/1.48  --trig_cnt_out                          false
% 7.68/1.48  --trig_cnt_out_tolerance                1.
% 7.68/1.48  --trig_cnt_out_sk_spl                   false
% 7.68/1.48  --abstr_cl_out                          false
% 7.68/1.48  
% 7.68/1.48  ------ Global Options
% 7.68/1.48  
% 7.68/1.48  --schedule                              default
% 7.68/1.48  --add_important_lit                     false
% 7.68/1.48  --prop_solver_per_cl                    1000
% 7.68/1.48  --min_unsat_core                        false
% 7.68/1.48  --soft_assumptions                      false
% 7.68/1.48  --soft_lemma_size                       3
% 7.68/1.48  --prop_impl_unit_size                   0
% 7.68/1.48  --prop_impl_unit                        []
% 7.68/1.48  --share_sel_clauses                     true
% 7.68/1.48  --reset_solvers                         false
% 7.68/1.48  --bc_imp_inh                            [conj_cone]
% 7.68/1.48  --conj_cone_tolerance                   3.
% 7.68/1.48  --extra_neg_conj                        none
% 7.68/1.48  --large_theory_mode                     true
% 7.68/1.48  --prolific_symb_bound                   200
% 7.68/1.48  --lt_threshold                          2000
% 7.68/1.48  --clause_weak_htbl                      true
% 7.68/1.48  --gc_record_bc_elim                     false
% 7.68/1.48  
% 7.68/1.48  ------ Preprocessing Options
% 7.68/1.48  
% 7.68/1.48  --preprocessing_flag                    true
% 7.68/1.48  --time_out_prep_mult                    0.1
% 7.68/1.48  --splitting_mode                        input
% 7.68/1.48  --splitting_grd                         true
% 7.68/1.48  --splitting_cvd                         false
% 7.68/1.48  --splitting_cvd_svl                     false
% 7.68/1.48  --splitting_nvd                         32
% 7.68/1.48  --sub_typing                            true
% 7.68/1.48  --prep_gs_sim                           true
% 7.68/1.48  --prep_unflatten                        true
% 7.68/1.48  --prep_res_sim                          true
% 7.68/1.48  --prep_upred                            true
% 7.68/1.48  --prep_sem_filter                       exhaustive
% 7.68/1.48  --prep_sem_filter_out                   false
% 7.68/1.48  --pred_elim                             true
% 7.68/1.48  --res_sim_input                         true
% 7.68/1.48  --eq_ax_congr_red                       true
% 7.68/1.48  --pure_diseq_elim                       true
% 7.68/1.48  --brand_transform                       false
% 7.68/1.48  --non_eq_to_eq                          false
% 7.68/1.48  --prep_def_merge                        true
% 7.68/1.48  --prep_def_merge_prop_impl              false
% 7.68/1.48  --prep_def_merge_mbd                    true
% 7.68/1.48  --prep_def_merge_tr_red                 false
% 7.68/1.48  --prep_def_merge_tr_cl                  false
% 7.68/1.48  --smt_preprocessing                     true
% 7.68/1.48  --smt_ac_axioms                         fast
% 7.68/1.48  --preprocessed_out                      false
% 7.68/1.48  --preprocessed_stats                    false
% 7.68/1.48  
% 7.68/1.48  ------ Abstraction refinement Options
% 7.68/1.48  
% 7.68/1.48  --abstr_ref                             []
% 7.68/1.48  --abstr_ref_prep                        false
% 7.68/1.48  --abstr_ref_until_sat                   false
% 7.68/1.48  --abstr_ref_sig_restrict                funpre
% 7.68/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.68/1.48  --abstr_ref_under                       []
% 7.68/1.48  
% 7.68/1.48  ------ SAT Options
% 7.68/1.48  
% 7.68/1.48  --sat_mode                              false
% 7.68/1.48  --sat_fm_restart_options                ""
% 7.68/1.48  --sat_gr_def                            false
% 7.68/1.48  --sat_epr_types                         true
% 7.68/1.48  --sat_non_cyclic_types                  false
% 7.68/1.48  --sat_finite_models                     false
% 7.68/1.48  --sat_fm_lemmas                         false
% 7.68/1.48  --sat_fm_prep                           false
% 7.68/1.48  --sat_fm_uc_incr                        true
% 7.68/1.48  --sat_out_model                         small
% 7.68/1.48  --sat_out_clauses                       false
% 7.68/1.48  
% 7.68/1.48  ------ QBF Options
% 7.68/1.48  
% 7.68/1.48  --qbf_mode                              false
% 7.68/1.48  --qbf_elim_univ                         false
% 7.68/1.48  --qbf_dom_inst                          none
% 7.68/1.48  --qbf_dom_pre_inst                      false
% 7.68/1.48  --qbf_sk_in                             false
% 7.68/1.48  --qbf_pred_elim                         true
% 7.68/1.48  --qbf_split                             512
% 7.68/1.48  
% 7.68/1.48  ------ BMC1 Options
% 7.68/1.48  
% 7.68/1.48  --bmc1_incremental                      false
% 7.68/1.48  --bmc1_axioms                           reachable_all
% 7.68/1.48  --bmc1_min_bound                        0
% 7.68/1.48  --bmc1_max_bound                        -1
% 7.68/1.48  --bmc1_max_bound_default                -1
% 7.68/1.48  --bmc1_symbol_reachability              true
% 7.68/1.48  --bmc1_property_lemmas                  false
% 7.68/1.48  --bmc1_k_induction                      false
% 7.68/1.48  --bmc1_non_equiv_states                 false
% 7.68/1.48  --bmc1_deadlock                         false
% 7.68/1.48  --bmc1_ucm                              false
% 7.68/1.48  --bmc1_add_unsat_core                   none
% 7.68/1.48  --bmc1_unsat_core_children              false
% 7.68/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.68/1.48  --bmc1_out_stat                         full
% 7.68/1.48  --bmc1_ground_init                      false
% 7.68/1.48  --bmc1_pre_inst_next_state              false
% 7.68/1.48  --bmc1_pre_inst_state                   false
% 7.68/1.48  --bmc1_pre_inst_reach_state             false
% 7.68/1.48  --bmc1_out_unsat_core                   false
% 7.68/1.48  --bmc1_aig_witness_out                  false
% 7.68/1.48  --bmc1_verbose                          false
% 7.68/1.48  --bmc1_dump_clauses_tptp                false
% 7.68/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.68/1.48  --bmc1_dump_file                        -
% 7.68/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.68/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.68/1.48  --bmc1_ucm_extend_mode                  1
% 7.68/1.48  --bmc1_ucm_init_mode                    2
% 7.68/1.48  --bmc1_ucm_cone_mode                    none
% 7.68/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.68/1.48  --bmc1_ucm_relax_model                  4
% 7.68/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.68/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.68/1.48  --bmc1_ucm_layered_model                none
% 7.68/1.48  --bmc1_ucm_max_lemma_size               10
% 7.68/1.48  
% 7.68/1.48  ------ AIG Options
% 7.68/1.48  
% 7.68/1.48  --aig_mode                              false
% 7.68/1.48  
% 7.68/1.48  ------ Instantiation Options
% 7.68/1.48  
% 7.68/1.48  --instantiation_flag                    true
% 7.68/1.48  --inst_sos_flag                         true
% 7.68/1.48  --inst_sos_phase                        true
% 7.68/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.68/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.68/1.48  --inst_lit_sel_side                     num_symb
% 7.68/1.48  --inst_solver_per_active                1400
% 7.68/1.48  --inst_solver_calls_frac                1.
% 7.68/1.48  --inst_passive_queue_type               priority_queues
% 7.68/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.68/1.48  --inst_passive_queues_freq              [25;2]
% 7.68/1.48  --inst_dismatching                      true
% 7.68/1.48  --inst_eager_unprocessed_to_passive     true
% 7.68/1.48  --inst_prop_sim_given                   true
% 7.68/1.48  --inst_prop_sim_new                     false
% 7.68/1.48  --inst_subs_new                         false
% 7.68/1.48  --inst_eq_res_simp                      false
% 7.68/1.48  --inst_subs_given                       false
% 7.68/1.48  --inst_orphan_elimination               true
% 7.68/1.48  --inst_learning_loop_flag               true
% 7.68/1.48  --inst_learning_start                   3000
% 7.68/1.48  --inst_learning_factor                  2
% 7.68/1.48  --inst_start_prop_sim_after_learn       3
% 7.68/1.48  --inst_sel_renew                        solver
% 7.68/1.48  --inst_lit_activity_flag                true
% 7.68/1.48  --inst_restr_to_given                   false
% 7.68/1.48  --inst_activity_threshold               500
% 7.68/1.48  --inst_out_proof                        true
% 7.68/1.48  
% 7.68/1.48  ------ Resolution Options
% 7.68/1.48  
% 7.68/1.48  --resolution_flag                       true
% 7.68/1.48  --res_lit_sel                           adaptive
% 7.68/1.48  --res_lit_sel_side                      none
% 7.68/1.48  --res_ordering                          kbo
% 7.68/1.48  --res_to_prop_solver                    active
% 7.68/1.48  --res_prop_simpl_new                    false
% 7.68/1.48  --res_prop_simpl_given                  true
% 7.68/1.48  --res_passive_queue_type                priority_queues
% 7.68/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.68/1.48  --res_passive_queues_freq               [15;5]
% 7.68/1.48  --res_forward_subs                      full
% 7.68/1.48  --res_backward_subs                     full
% 7.68/1.48  --res_forward_subs_resolution           true
% 7.68/1.48  --res_backward_subs_resolution          true
% 7.68/1.48  --res_orphan_elimination                true
% 7.68/1.48  --res_time_limit                        2.
% 7.68/1.48  --res_out_proof                         true
% 7.68/1.48  
% 7.68/1.48  ------ Superposition Options
% 7.68/1.48  
% 7.68/1.48  --superposition_flag                    true
% 7.68/1.48  --sup_passive_queue_type                priority_queues
% 7.68/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.68/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.68/1.48  --demod_completeness_check              fast
% 7.68/1.48  --demod_use_ground                      true
% 7.68/1.48  --sup_to_prop_solver                    passive
% 7.68/1.48  --sup_prop_simpl_new                    true
% 7.68/1.48  --sup_prop_simpl_given                  true
% 7.68/1.48  --sup_fun_splitting                     true
% 7.68/1.48  --sup_smt_interval                      50000
% 7.68/1.48  
% 7.68/1.48  ------ Superposition Simplification Setup
% 7.68/1.48  
% 7.68/1.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.68/1.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.68/1.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.68/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.68/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.68/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.68/1.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.68/1.48  --sup_immed_triv                        [TrivRules]
% 7.68/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.68/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.68/1.48  --sup_immed_bw_main                     []
% 7.68/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.68/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.68/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.68/1.48  --sup_input_bw                          []
% 7.68/1.48  
% 7.68/1.48  ------ Combination Options
% 7.68/1.48  
% 7.68/1.48  --comb_res_mult                         3
% 7.68/1.48  --comb_sup_mult                         2
% 7.68/1.48  --comb_inst_mult                        10
% 7.68/1.48  
% 7.68/1.48  ------ Debug Options
% 7.68/1.48  
% 7.68/1.48  --dbg_backtrace                         false
% 7.68/1.48  --dbg_dump_prop_clauses                 false
% 7.68/1.48  --dbg_dump_prop_clauses_file            -
% 7.68/1.48  --dbg_out_stat                          false
% 7.68/1.48  ------ Parsing...
% 7.68/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.68/1.48  
% 7.68/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.68/1.48  
% 7.68/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.68/1.48  
% 7.68/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.68/1.48  ------ Proving...
% 7.68/1.48  ------ Problem Properties 
% 7.68/1.48  
% 7.68/1.48  
% 7.68/1.48  clauses                                 12
% 7.68/1.48  conjectures                             3
% 7.68/1.48  EPR                                     2
% 7.68/1.48  Horn                                    12
% 7.68/1.48  unary                                   6
% 7.68/1.48  binary                                  2
% 7.68/1.48  lits                                    24
% 7.68/1.48  lits eq                                 3
% 7.68/1.48  fd_pure                                 0
% 7.68/1.48  fd_pseudo                               0
% 7.68/1.48  fd_cond                                 0
% 7.68/1.48  fd_pseudo_cond                          0
% 7.68/1.48  AC symbols                              0
% 7.68/1.48  
% 7.68/1.48  ------ Schedule dynamic 5 is on 
% 7.68/1.48  
% 7.68/1.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.68/1.48  
% 7.68/1.48  
% 7.68/1.48  ------ 
% 7.68/1.48  Current options:
% 7.68/1.48  ------ 
% 7.68/1.48  
% 7.68/1.48  ------ Input Options
% 7.68/1.48  
% 7.68/1.48  --out_options                           all
% 7.68/1.48  --tptp_safe_out                         true
% 7.68/1.48  --problem_path                          ""
% 7.68/1.48  --include_path                          ""
% 7.68/1.48  --clausifier                            res/vclausify_rel
% 7.68/1.48  --clausifier_options                    ""
% 7.68/1.48  --stdin                                 false
% 7.68/1.48  --stats_out                             all
% 7.68/1.48  
% 7.68/1.48  ------ General Options
% 7.68/1.48  
% 7.68/1.48  --fof                                   false
% 7.68/1.48  --time_out_real                         305.
% 7.68/1.48  --time_out_virtual                      -1.
% 7.68/1.48  --symbol_type_check                     false
% 7.68/1.48  --clausify_out                          false
% 7.68/1.48  --sig_cnt_out                           false
% 7.68/1.48  --trig_cnt_out                          false
% 7.68/1.48  --trig_cnt_out_tolerance                1.
% 7.68/1.48  --trig_cnt_out_sk_spl                   false
% 7.68/1.48  --abstr_cl_out                          false
% 7.68/1.48  
% 7.68/1.48  ------ Global Options
% 7.68/1.48  
% 7.68/1.48  --schedule                              default
% 7.68/1.48  --add_important_lit                     false
% 7.68/1.48  --prop_solver_per_cl                    1000
% 7.68/1.48  --min_unsat_core                        false
% 7.68/1.48  --soft_assumptions                      false
% 7.68/1.48  --soft_lemma_size                       3
% 7.68/1.48  --prop_impl_unit_size                   0
% 7.68/1.48  --prop_impl_unit                        []
% 7.68/1.48  --share_sel_clauses                     true
% 7.68/1.48  --reset_solvers                         false
% 7.68/1.48  --bc_imp_inh                            [conj_cone]
% 7.68/1.48  --conj_cone_tolerance                   3.
% 7.68/1.48  --extra_neg_conj                        none
% 7.68/1.48  --large_theory_mode                     true
% 7.68/1.48  --prolific_symb_bound                   200
% 7.68/1.48  --lt_threshold                          2000
% 7.68/1.48  --clause_weak_htbl                      true
% 7.68/1.48  --gc_record_bc_elim                     false
% 7.68/1.48  
% 7.68/1.48  ------ Preprocessing Options
% 7.68/1.48  
% 7.68/1.48  --preprocessing_flag                    true
% 7.68/1.48  --time_out_prep_mult                    0.1
% 7.68/1.48  --splitting_mode                        input
% 7.68/1.48  --splitting_grd                         true
% 7.68/1.48  --splitting_cvd                         false
% 7.68/1.48  --splitting_cvd_svl                     false
% 7.68/1.48  --splitting_nvd                         32
% 7.68/1.48  --sub_typing                            true
% 7.68/1.48  --prep_gs_sim                           true
% 7.68/1.48  --prep_unflatten                        true
% 7.68/1.48  --prep_res_sim                          true
% 7.68/1.48  --prep_upred                            true
% 7.68/1.48  --prep_sem_filter                       exhaustive
% 7.68/1.48  --prep_sem_filter_out                   false
% 7.68/1.48  --pred_elim                             true
% 7.68/1.48  --res_sim_input                         true
% 7.68/1.48  --eq_ax_congr_red                       true
% 7.68/1.48  --pure_diseq_elim                       true
% 7.68/1.48  --brand_transform                       false
% 7.68/1.48  --non_eq_to_eq                          false
% 7.68/1.48  --prep_def_merge                        true
% 7.68/1.48  --prep_def_merge_prop_impl              false
% 7.68/1.48  --prep_def_merge_mbd                    true
% 7.68/1.48  --prep_def_merge_tr_red                 false
% 7.68/1.48  --prep_def_merge_tr_cl                  false
% 7.68/1.48  --smt_preprocessing                     true
% 7.68/1.48  --smt_ac_axioms                         fast
% 7.68/1.48  --preprocessed_out                      false
% 7.68/1.48  --preprocessed_stats                    false
% 7.68/1.48  
% 7.68/1.48  ------ Abstraction refinement Options
% 7.68/1.48  
% 7.68/1.48  --abstr_ref                             []
% 7.68/1.48  --abstr_ref_prep                        false
% 7.68/1.48  --abstr_ref_until_sat                   false
% 7.68/1.48  --abstr_ref_sig_restrict                funpre
% 7.68/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.68/1.48  --abstr_ref_under                       []
% 7.68/1.48  
% 7.68/1.48  ------ SAT Options
% 7.68/1.48  
% 7.68/1.48  --sat_mode                              false
% 7.68/1.48  --sat_fm_restart_options                ""
% 7.68/1.48  --sat_gr_def                            false
% 7.68/1.48  --sat_epr_types                         true
% 7.68/1.48  --sat_non_cyclic_types                  false
% 7.68/1.48  --sat_finite_models                     false
% 7.68/1.48  --sat_fm_lemmas                         false
% 7.68/1.48  --sat_fm_prep                           false
% 7.68/1.48  --sat_fm_uc_incr                        true
% 7.68/1.48  --sat_out_model                         small
% 7.68/1.48  --sat_out_clauses                       false
% 7.68/1.48  
% 7.68/1.48  ------ QBF Options
% 7.68/1.48  
% 7.68/1.48  --qbf_mode                              false
% 7.68/1.48  --qbf_elim_univ                         false
% 7.68/1.48  --qbf_dom_inst                          none
% 7.68/1.48  --qbf_dom_pre_inst                      false
% 7.68/1.48  --qbf_sk_in                             false
% 7.68/1.48  --qbf_pred_elim                         true
% 7.68/1.48  --qbf_split                             512
% 7.68/1.48  
% 7.68/1.48  ------ BMC1 Options
% 7.68/1.48  
% 7.68/1.48  --bmc1_incremental                      false
% 7.68/1.48  --bmc1_axioms                           reachable_all
% 7.68/1.48  --bmc1_min_bound                        0
% 7.68/1.48  --bmc1_max_bound                        -1
% 7.68/1.48  --bmc1_max_bound_default                -1
% 7.68/1.48  --bmc1_symbol_reachability              true
% 7.68/1.48  --bmc1_property_lemmas                  false
% 7.68/1.48  --bmc1_k_induction                      false
% 7.68/1.48  --bmc1_non_equiv_states                 false
% 7.68/1.48  --bmc1_deadlock                         false
% 7.68/1.49  --bmc1_ucm                              false
% 7.68/1.49  --bmc1_add_unsat_core                   none
% 7.68/1.49  --bmc1_unsat_core_children              false
% 7.68/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.68/1.49  --bmc1_out_stat                         full
% 7.68/1.49  --bmc1_ground_init                      false
% 7.68/1.49  --bmc1_pre_inst_next_state              false
% 7.68/1.49  --bmc1_pre_inst_state                   false
% 7.68/1.49  --bmc1_pre_inst_reach_state             false
% 7.68/1.49  --bmc1_out_unsat_core                   false
% 7.68/1.49  --bmc1_aig_witness_out                  false
% 7.68/1.49  --bmc1_verbose                          false
% 7.68/1.49  --bmc1_dump_clauses_tptp                false
% 7.68/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.68/1.49  --bmc1_dump_file                        -
% 7.68/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.68/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.68/1.49  --bmc1_ucm_extend_mode                  1
% 7.68/1.49  --bmc1_ucm_init_mode                    2
% 7.68/1.49  --bmc1_ucm_cone_mode                    none
% 7.68/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.68/1.49  --bmc1_ucm_relax_model                  4
% 7.68/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.68/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.68/1.49  --bmc1_ucm_layered_model                none
% 7.68/1.49  --bmc1_ucm_max_lemma_size               10
% 7.68/1.49  
% 7.68/1.49  ------ AIG Options
% 7.68/1.49  
% 7.68/1.49  --aig_mode                              false
% 7.68/1.49  
% 7.68/1.49  ------ Instantiation Options
% 7.68/1.49  
% 7.68/1.49  --instantiation_flag                    true
% 7.68/1.49  --inst_sos_flag                         true
% 7.68/1.49  --inst_sos_phase                        true
% 7.68/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.68/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.68/1.49  --inst_lit_sel_side                     none
% 7.68/1.49  --inst_solver_per_active                1400
% 7.68/1.49  --inst_solver_calls_frac                1.
% 7.68/1.49  --inst_passive_queue_type               priority_queues
% 7.68/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.68/1.49  --inst_passive_queues_freq              [25;2]
% 7.68/1.49  --inst_dismatching                      true
% 7.68/1.49  --inst_eager_unprocessed_to_passive     true
% 7.68/1.49  --inst_prop_sim_given                   true
% 7.68/1.49  --inst_prop_sim_new                     false
% 7.68/1.49  --inst_subs_new                         false
% 7.68/1.49  --inst_eq_res_simp                      false
% 7.68/1.49  --inst_subs_given                       false
% 7.68/1.49  --inst_orphan_elimination               true
% 7.68/1.49  --inst_learning_loop_flag               true
% 7.68/1.49  --inst_learning_start                   3000
% 7.68/1.49  --inst_learning_factor                  2
% 7.68/1.49  --inst_start_prop_sim_after_learn       3
% 7.68/1.49  --inst_sel_renew                        solver
% 7.68/1.49  --inst_lit_activity_flag                true
% 7.68/1.49  --inst_restr_to_given                   false
% 7.68/1.49  --inst_activity_threshold               500
% 7.68/1.49  --inst_out_proof                        true
% 7.68/1.49  
% 7.68/1.49  ------ Resolution Options
% 7.68/1.49  
% 7.68/1.49  --resolution_flag                       false
% 7.68/1.49  --res_lit_sel                           adaptive
% 7.68/1.49  --res_lit_sel_side                      none
% 7.68/1.49  --res_ordering                          kbo
% 7.68/1.49  --res_to_prop_solver                    active
% 7.68/1.49  --res_prop_simpl_new                    false
% 7.68/1.49  --res_prop_simpl_given                  true
% 7.68/1.49  --res_passive_queue_type                priority_queues
% 7.68/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.68/1.49  --res_passive_queues_freq               [15;5]
% 7.68/1.49  --res_forward_subs                      full
% 7.68/1.49  --res_backward_subs                     full
% 7.68/1.49  --res_forward_subs_resolution           true
% 7.68/1.49  --res_backward_subs_resolution          true
% 7.68/1.49  --res_orphan_elimination                true
% 7.68/1.49  --res_time_limit                        2.
% 7.68/1.49  --res_out_proof                         true
% 7.68/1.49  
% 7.68/1.49  ------ Superposition Options
% 7.68/1.49  
% 7.68/1.49  --superposition_flag                    true
% 7.68/1.49  --sup_passive_queue_type                priority_queues
% 7.68/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.68/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.68/1.49  --demod_completeness_check              fast
% 7.68/1.49  --demod_use_ground                      true
% 7.68/1.49  --sup_to_prop_solver                    passive
% 7.68/1.49  --sup_prop_simpl_new                    true
% 7.68/1.49  --sup_prop_simpl_given                  true
% 7.68/1.49  --sup_fun_splitting                     true
% 7.68/1.49  --sup_smt_interval                      50000
% 7.68/1.49  
% 7.68/1.49  ------ Superposition Simplification Setup
% 7.68/1.49  
% 7.68/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.68/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.68/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.68/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.68/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.68/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.68/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.68/1.49  --sup_immed_triv                        [TrivRules]
% 7.68/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.68/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.68/1.49  --sup_immed_bw_main                     []
% 7.68/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.68/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.68/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.68/1.49  --sup_input_bw                          []
% 7.68/1.49  
% 7.68/1.49  ------ Combination Options
% 7.68/1.49  
% 7.68/1.49  --comb_res_mult                         3
% 7.68/1.49  --comb_sup_mult                         2
% 7.68/1.49  --comb_inst_mult                        10
% 7.68/1.49  
% 7.68/1.49  ------ Debug Options
% 7.68/1.49  
% 7.68/1.49  --dbg_backtrace                         false
% 7.68/1.49  --dbg_dump_prop_clauses                 false
% 7.68/1.49  --dbg_dump_prop_clauses_file            -
% 7.68/1.49  --dbg_out_stat                          false
% 7.68/1.49  
% 7.68/1.49  
% 7.68/1.49  
% 7.68/1.49  
% 7.68/1.49  ------ Proving...
% 7.68/1.49  
% 7.68/1.49  
% 7.68/1.49  % SZS status Theorem for theBenchmark.p
% 7.68/1.49  
% 7.68/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.68/1.49  
% 7.68/1.49  fof(f2,axiom,(
% 7.68/1.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 7.68/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.68/1.49  
% 7.68/1.49  fof(f24,plain,(
% 7.68/1.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 7.68/1.49    inference(cnf_transformation,[],[f2])).
% 7.68/1.49  
% 7.68/1.49  fof(f5,axiom,(
% 7.68/1.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 7.68/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.68/1.49  
% 7.68/1.49  fof(f27,plain,(
% 7.68/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 7.68/1.49    inference(cnf_transformation,[],[f5])).
% 7.68/1.49  
% 7.68/1.49  fof(f36,plain,(
% 7.68/1.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k6_subset_1(X1,X0))) )),
% 7.68/1.49    inference(definition_unfolding,[],[f24,f27])).
% 7.68/1.49  
% 7.68/1.49  fof(f10,conjecture,(
% 7.68/1.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1)))))),
% 7.68/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.68/1.49  
% 7.68/1.49  fof(f11,negated_conjecture,(
% 7.68/1.49    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1)))))),
% 7.68/1.49    inference(negated_conjecture,[],[f10])).
% 7.68/1.49  
% 7.68/1.49  fof(f19,plain,(
% 7.68/1.49    ? [X0] : (? [X1] : (~r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 7.68/1.49    inference(ennf_transformation,[],[f11])).
% 7.68/1.49  
% 7.68/1.49  fof(f21,plain,(
% 7.68/1.49    ( ! [X0] : (? [X1] : (~r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) & v1_relat_1(X1)) => (~r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(X0,sK1))) & v1_relat_1(sK1))) )),
% 7.68/1.49    introduced(choice_axiom,[])).
% 7.68/1.49  
% 7.68/1.49  fof(f20,plain,(
% 7.68/1.49    ? [X0] : (? [X1] : (~r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(sK0,X1))) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 7.68/1.49    introduced(choice_axiom,[])).
% 7.68/1.49  
% 7.68/1.49  fof(f22,plain,(
% 7.68/1.49    (~r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(sK0,sK1))) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 7.68/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f21,f20])).
% 7.68/1.49  
% 7.68/1.49  fof(f33,plain,(
% 7.68/1.49    v1_relat_1(sK0)),
% 7.68/1.49    inference(cnf_transformation,[],[f22])).
% 7.68/1.49  
% 7.68/1.49  fof(f34,plain,(
% 7.68/1.49    v1_relat_1(sK1)),
% 7.68/1.49    inference(cnf_transformation,[],[f22])).
% 7.68/1.49  
% 7.68/1.49  fof(f9,axiom,(
% 7.68/1.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) = k2_relat_1(k2_xboole_0(X0,X1))))),
% 7.68/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.68/1.49  
% 7.68/1.49  fof(f18,plain,(
% 7.68/1.49    ! [X0] : (! [X1] : (k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) = k2_relat_1(k2_xboole_0(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.68/1.49    inference(ennf_transformation,[],[f9])).
% 7.68/1.49  
% 7.68/1.49  fof(f32,plain,(
% 7.68/1.49    ( ! [X0,X1] : (k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) = k2_relat_1(k2_xboole_0(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.68/1.49    inference(cnf_transformation,[],[f18])).
% 7.68/1.49  
% 7.68/1.49  fof(f1,axiom,(
% 7.68/1.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 7.68/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.68/1.49  
% 7.68/1.49  fof(f23,plain,(
% 7.68/1.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 7.68/1.49    inference(cnf_transformation,[],[f1])).
% 7.68/1.49  
% 7.68/1.49  fof(f4,axiom,(
% 7.68/1.49    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 7.68/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.68/1.49  
% 7.68/1.49  fof(f26,plain,(
% 7.68/1.49    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 7.68/1.49    inference(cnf_transformation,[],[f4])).
% 7.68/1.49  
% 7.68/1.49  fof(f6,axiom,(
% 7.68/1.49    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k4_xboole_0(X0,X1)))),
% 7.68/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.68/1.49  
% 7.68/1.49  fof(f13,plain,(
% 7.68/1.49    ! [X0,X1] : (v1_relat_1(k4_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 7.68/1.49    inference(ennf_transformation,[],[f6])).
% 7.68/1.49  
% 7.68/1.49  fof(f28,plain,(
% 7.68/1.49    ( ! [X0,X1] : (v1_relat_1(k4_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 7.68/1.49    inference(cnf_transformation,[],[f13])).
% 7.68/1.49  
% 7.68/1.49  fof(f38,plain,(
% 7.68/1.49    ( ! [X0,X1] : (v1_relat_1(k6_subset_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 7.68/1.49    inference(definition_unfolding,[],[f28,f27])).
% 7.68/1.49  
% 7.68/1.49  fof(f3,axiom,(
% 7.68/1.49    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 7.68/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.68/1.49  
% 7.68/1.49  fof(f12,plain,(
% 7.68/1.49    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 7.68/1.49    inference(ennf_transformation,[],[f3])).
% 7.68/1.49  
% 7.68/1.49  fof(f25,plain,(
% 7.68/1.49    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 7.68/1.49    inference(cnf_transformation,[],[f12])).
% 7.68/1.49  
% 7.68/1.49  fof(f37,plain,(
% 7.68/1.49    ( ! [X2,X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 7.68/1.49    inference(definition_unfolding,[],[f25,f27])).
% 7.68/1.49  
% 7.68/1.49  fof(f35,plain,(
% 7.68/1.49    ~r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(sK0,sK1)))),
% 7.68/1.49    inference(cnf_transformation,[],[f22])).
% 7.68/1.49  
% 7.68/1.49  cnf(c_123,plain,
% 7.68/1.49      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.68/1.49      theory(equality) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_677,plain,
% 7.68/1.49      ( ~ r1_tarski(X0,X1)
% 7.68/1.49      | r1_tarski(k2_relat_1(X2),k2_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,sK1))))
% 7.68/1.49      | k2_relat_1(X2) != X0
% 7.68/1.49      | k2_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,sK1))) != X1 ),
% 7.68/1.49      inference(instantiation,[status(thm)],[c_123]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_1033,plain,
% 7.68/1.49      ( ~ r1_tarski(X0,k2_relat_1(X1))
% 7.68/1.49      | r1_tarski(k2_relat_1(X2),k2_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,sK1))))
% 7.68/1.49      | k2_relat_1(X2) != X0
% 7.68/1.49      | k2_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,sK1))) != k2_relat_1(X1) ),
% 7.68/1.49      inference(instantiation,[status(thm)],[c_677]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_7710,plain,
% 7.68/1.49      ( ~ r1_tarski(X0,k2_relat_1(k2_xboole_0(sK1,sK0)))
% 7.68/1.49      | r1_tarski(k2_relat_1(X1),k2_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,sK1))))
% 7.68/1.49      | k2_relat_1(X1) != X0
% 7.68/1.49      | k2_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,sK1))) != k2_relat_1(k2_xboole_0(sK1,sK0)) ),
% 7.68/1.49      inference(instantiation,[status(thm)],[c_1033]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_17780,plain,
% 7.68/1.49      ( r1_tarski(k2_relat_1(X0),k2_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,sK1))))
% 7.68/1.49      | ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(k2_xboole_0(sK1,sK0)))
% 7.68/1.49      | k2_relat_1(X0) != k2_relat_1(sK0)
% 7.68/1.49      | k2_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,sK1))) != k2_relat_1(k2_xboole_0(sK1,sK0)) ),
% 7.68/1.49      inference(instantiation,[status(thm)],[c_7710]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_17783,plain,
% 7.68/1.49      ( r1_tarski(k2_relat_1(sK0),k2_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,sK1))))
% 7.68/1.49      | ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(k2_xboole_0(sK1,sK0)))
% 7.68/1.49      | k2_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,sK1))) != k2_relat_1(k2_xboole_0(sK1,sK0))
% 7.68/1.49      | k2_relat_1(sK0) != k2_relat_1(sK0) ),
% 7.68/1.49      inference(instantiation,[status(thm)],[c_17780]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_1,plain,
% 7.68/1.49      ( k2_xboole_0(X0,k6_subset_1(X1,X0)) = k2_xboole_0(X0,X1) ),
% 7.68/1.49      inference(cnf_transformation,[],[f36]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_3901,plain,
% 7.68/1.49      ( k2_xboole_0(sK1,k6_subset_1(sK0,sK1)) = k2_xboole_0(sK1,sK0) ),
% 7.68/1.49      inference(instantiation,[status(thm)],[c_1]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_125,plain,
% 7.68/1.49      ( X0 != X1 | k2_relat_1(X0) = k2_relat_1(X1) ),
% 7.68/1.49      theory(equality) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_1736,plain,
% 7.68/1.49      ( k2_xboole_0(sK1,k6_subset_1(sK0,sK1)) != X0
% 7.68/1.49      | k2_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,sK1))) = k2_relat_1(X0) ),
% 7.68/1.49      inference(instantiation,[status(thm)],[c_125]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_3683,plain,
% 7.68/1.49      ( k2_xboole_0(sK1,k6_subset_1(sK0,sK1)) != k2_xboole_0(sK1,sK0)
% 7.68/1.49      | k2_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,sK1))) = k2_relat_1(k2_xboole_0(sK1,sK0)) ),
% 7.68/1.49      inference(instantiation,[status(thm)],[c_1736]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_11,negated_conjecture,
% 7.68/1.49      ( v1_relat_1(sK0) ),
% 7.68/1.49      inference(cnf_transformation,[],[f33]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_293,plain,
% 7.68/1.49      ( v1_relat_1(sK0) = iProver_top ),
% 7.68/1.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_10,negated_conjecture,
% 7.68/1.49      ( v1_relat_1(sK1) ),
% 7.68/1.49      inference(cnf_transformation,[],[f34]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_294,plain,
% 7.68/1.49      ( v1_relat_1(sK1) = iProver_top ),
% 7.68/1.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_8,plain,
% 7.68/1.49      ( ~ v1_relat_1(X0)
% 7.68/1.49      | ~ v1_relat_1(X1)
% 7.68/1.49      | k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) = k2_relat_1(k2_xboole_0(X0,X1)) ),
% 7.68/1.49      inference(cnf_transformation,[],[f32]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_296,plain,
% 7.68/1.49      ( k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) = k2_relat_1(k2_xboole_0(X0,X1))
% 7.68/1.49      | v1_relat_1(X0) != iProver_top
% 7.68/1.49      | v1_relat_1(X1) != iProver_top ),
% 7.68/1.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_645,plain,
% 7.68/1.49      ( k2_xboole_0(k2_relat_1(sK1),k2_relat_1(X0)) = k2_relat_1(k2_xboole_0(sK1,X0))
% 7.68/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.68/1.49      inference(superposition,[status(thm)],[c_294,c_296]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_771,plain,
% 7.68/1.49      ( k2_xboole_0(k2_relat_1(sK1),k2_relat_1(sK0)) = k2_relat_1(k2_xboole_0(sK1,sK0)) ),
% 7.68/1.49      inference(superposition,[status(thm)],[c_293,c_645]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_0,plain,
% 7.68/1.49      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 7.68/1.49      inference(cnf_transformation,[],[f23]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_3,plain,
% 7.68/1.49      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 7.68/1.49      inference(cnf_transformation,[],[f26]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_301,plain,
% 7.68/1.49      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 7.68/1.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_509,plain,
% 7.68/1.49      ( r1_tarski(X0,k2_xboole_0(X1,X0)) = iProver_top ),
% 7.68/1.49      inference(superposition,[status(thm)],[c_0,c_301]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_864,plain,
% 7.68/1.49      ( r1_tarski(k2_relat_1(sK0),k2_relat_1(k2_xboole_0(sK1,sK0))) = iProver_top ),
% 7.68/1.49      inference(superposition,[status(thm)],[c_771,c_509]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_872,plain,
% 7.68/1.49      ( r1_tarski(k2_relat_1(sK0),k2_relat_1(k2_xboole_0(sK1,sK0))) ),
% 7.68/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_864]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_4,plain,
% 7.68/1.49      ( ~ v1_relat_1(X0) | v1_relat_1(k6_subset_1(X0,X1)) ),
% 7.68/1.49      inference(cnf_transformation,[],[f38]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_545,plain,
% 7.68/1.49      ( v1_relat_1(k6_subset_1(sK0,sK1)) | ~ v1_relat_1(sK0) ),
% 7.68/1.49      inference(instantiation,[status(thm)],[c_4]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_527,plain,
% 7.68/1.49      ( ~ v1_relat_1(k6_subset_1(sK0,sK1))
% 7.68/1.49      | ~ v1_relat_1(sK1)
% 7.68/1.49      | k2_xboole_0(k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1))) = k2_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,sK1))) ),
% 7.68/1.49      inference(instantiation,[status(thm)],[c_8]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_324,plain,
% 7.68/1.49      ( ~ r1_tarski(X0,X1)
% 7.68/1.49      | r1_tarski(k2_relat_1(sK0),k2_xboole_0(k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1))))
% 7.68/1.49      | k2_xboole_0(k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1))) != X1
% 7.68/1.49      | k2_relat_1(sK0) != X0 ),
% 7.68/1.49      inference(instantiation,[status(thm)],[c_123]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_352,plain,
% 7.68/1.49      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 7.68/1.49      | r1_tarski(k2_relat_1(sK0),k2_xboole_0(k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1))))
% 7.68/1.49      | k2_xboole_0(k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1))) != X1
% 7.68/1.49      | k2_relat_1(sK0) != k2_relat_1(X0) ),
% 7.68/1.49      inference(instantiation,[status(thm)],[c_324]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_432,plain,
% 7.68/1.49      ( ~ r1_tarski(k2_relat_1(X0),k2_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,sK1))))
% 7.68/1.49      | r1_tarski(k2_relat_1(sK0),k2_xboole_0(k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1))))
% 7.68/1.49      | k2_xboole_0(k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1))) != k2_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,sK1)))
% 7.68/1.49      | k2_relat_1(sK0) != k2_relat_1(X0) ),
% 7.68/1.49      inference(instantiation,[status(thm)],[c_352]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_434,plain,
% 7.68/1.49      ( r1_tarski(k2_relat_1(sK0),k2_xboole_0(k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1))))
% 7.68/1.49      | ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,sK1))))
% 7.68/1.49      | k2_xboole_0(k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1))) != k2_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,sK1)))
% 7.68/1.49      | k2_relat_1(sK0) != k2_relat_1(sK0) ),
% 7.68/1.49      inference(instantiation,[status(thm)],[c_432]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_2,plain,
% 7.68/1.49      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
% 7.68/1.49      | r1_tarski(k6_subset_1(X0,X1),X2) ),
% 7.68/1.49      inference(cnf_transformation,[],[f37]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_316,plain,
% 7.68/1.49      ( r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(sK0,sK1)))
% 7.68/1.49      | ~ r1_tarski(k2_relat_1(sK0),k2_xboole_0(k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1)))) ),
% 7.68/1.49      inference(instantiation,[status(thm)],[c_2]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_119,plain,( X0 = X0 ),theory(equality) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_131,plain,
% 7.68/1.49      ( sK0 = sK0 ),
% 7.68/1.49      inference(instantiation,[status(thm)],[c_119]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_129,plain,
% 7.68/1.49      ( k2_relat_1(sK0) = k2_relat_1(sK0) | sK0 != sK0 ),
% 7.68/1.49      inference(instantiation,[status(thm)],[c_125]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(c_9,negated_conjecture,
% 7.68/1.49      ( ~ r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(sK0,sK1))) ),
% 7.68/1.49      inference(cnf_transformation,[],[f35]) ).
% 7.68/1.49  
% 7.68/1.49  cnf(contradiction,plain,
% 7.68/1.49      ( $false ),
% 7.68/1.49      inference(minisat,
% 7.68/1.49                [status(thm)],
% 7.68/1.49                [c_17783,c_3901,c_3683,c_872,c_545,c_527,c_434,c_316,
% 7.68/1.49                 c_131,c_129,c_9,c_10,c_11]) ).
% 7.68/1.49  
% 7.68/1.49  
% 7.68/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.68/1.49  
% 7.68/1.49  ------                               Statistics
% 7.68/1.49  
% 7.68/1.49  ------ General
% 7.68/1.49  
% 7.68/1.49  abstr_ref_over_cycles:                  0
% 7.68/1.49  abstr_ref_under_cycles:                 0
% 7.68/1.49  gc_basic_clause_elim:                   0
% 7.68/1.49  forced_gc_time:                         0
% 7.68/1.49  parsing_time:                           0.01
% 7.68/1.49  unif_index_cands_time:                  0.
% 7.68/1.49  unif_index_add_time:                    0.
% 7.68/1.49  orderings_time:                         0.
% 7.68/1.49  out_proof_time:                         0.006
% 7.68/1.49  total_time:                             0.542
% 7.68/1.49  num_of_symbols:                         39
% 7.68/1.49  num_of_terms:                           16683
% 7.68/1.49  
% 7.68/1.49  ------ Preprocessing
% 7.68/1.49  
% 7.68/1.49  num_of_splits:                          0
% 7.68/1.49  num_of_split_atoms:                     0
% 7.68/1.49  num_of_reused_defs:                     0
% 7.68/1.49  num_eq_ax_congr_red:                    2
% 7.68/1.49  num_of_sem_filtered_clauses:            1
% 7.68/1.49  num_of_subtypes:                        1
% 7.68/1.49  monotx_restored_types:                  0
% 7.68/1.49  sat_num_of_epr_types:                   0
% 7.68/1.49  sat_num_of_non_cyclic_types:            0
% 7.68/1.49  sat_guarded_non_collapsed_types:        0
% 7.68/1.49  num_pure_diseq_elim:                    0
% 7.68/1.49  simp_replaced_by:                       0
% 7.68/1.49  res_preprocessed:                       51
% 7.68/1.49  prep_upred:                             0
% 7.68/1.49  prep_unflattend:                        0
% 7.68/1.49  smt_new_axioms:                         0
% 7.68/1.49  pred_elim_cands:                        2
% 7.68/1.49  pred_elim:                              0
% 7.68/1.49  pred_elim_cl:                           0
% 7.68/1.49  pred_elim_cycles:                       1
% 7.68/1.49  merged_defs:                            0
% 7.68/1.49  merged_defs_ncl:                        0
% 7.68/1.49  bin_hyper_res:                          0
% 7.68/1.49  prep_cycles:                            3
% 7.68/1.49  pred_elim_time:                         0.
% 7.68/1.49  splitting_time:                         0.
% 7.68/1.49  sem_filter_time:                        0.
% 7.68/1.49  monotx_time:                            0.
% 7.68/1.49  subtype_inf_time:                       0.
% 7.68/1.49  
% 7.68/1.49  ------ Problem properties
% 7.68/1.49  
% 7.68/1.49  clauses:                                12
% 7.68/1.49  conjectures:                            3
% 7.68/1.49  epr:                                    2
% 7.68/1.49  horn:                                   12
% 7.68/1.49  ground:                                 3
% 7.68/1.49  unary:                                  6
% 7.68/1.49  binary:                                 2
% 7.68/1.49  lits:                                   24
% 7.68/1.49  lits_eq:                                3
% 7.68/1.49  fd_pure:                                0
% 7.68/1.49  fd_pseudo:                              0
% 7.68/1.49  fd_cond:                                0
% 7.68/1.49  fd_pseudo_cond:                         0
% 7.68/1.49  ac_symbols:                             0
% 7.68/1.49  
% 7.68/1.49  ------ Propositional Solver
% 7.68/1.49  
% 7.68/1.49  prop_solver_calls:                      32
% 7.68/1.49  prop_fast_solver_calls:                 467
% 7.68/1.49  smt_solver_calls:                       0
% 7.68/1.49  smt_fast_solver_calls:                  0
% 7.68/1.49  prop_num_of_clauses:                    6522
% 7.68/1.49  prop_preprocess_simplified:             13551
% 7.68/1.49  prop_fo_subsumed:                       0
% 7.68/1.49  prop_solver_time:                       0.
% 7.68/1.49  smt_solver_time:                        0.
% 7.68/1.49  smt_fast_solver_time:                   0.
% 7.68/1.49  prop_fast_solver_time:                  0.
% 7.68/1.49  prop_unsat_core_time:                   0.
% 7.68/1.49  
% 7.68/1.49  ------ QBF
% 7.68/1.49  
% 7.68/1.49  qbf_q_res:                              0
% 7.68/1.49  qbf_num_tautologies:                    0
% 7.68/1.49  qbf_prep_cycles:                        0
% 7.68/1.49  
% 7.68/1.49  ------ BMC1
% 7.68/1.49  
% 7.68/1.49  bmc1_current_bound:                     -1
% 7.68/1.49  bmc1_last_solved_bound:                 -1
% 7.68/1.49  bmc1_unsat_core_size:                   -1
% 7.68/1.49  bmc1_unsat_core_parents_size:           -1
% 7.68/1.49  bmc1_merge_next_fun:                    0
% 7.68/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.68/1.49  
% 7.68/1.49  ------ Instantiation
% 7.68/1.49  
% 7.68/1.49  inst_num_of_clauses:                    1990
% 7.68/1.49  inst_num_in_passive:                    587
% 7.68/1.49  inst_num_in_active:                     929
% 7.68/1.49  inst_num_in_unprocessed:                490
% 7.68/1.49  inst_num_of_loops:                      987
% 7.68/1.49  inst_num_of_learning_restarts:          0
% 7.68/1.49  inst_num_moves_active_passive:          51
% 7.68/1.49  inst_lit_activity:                      0
% 7.68/1.49  inst_lit_activity_moves:                0
% 7.68/1.49  inst_num_tautologies:                   0
% 7.68/1.49  inst_num_prop_implied:                  0
% 7.68/1.49  inst_num_existing_simplified:           0
% 7.68/1.49  inst_num_eq_res_simplified:             0
% 7.68/1.49  inst_num_child_elim:                    0
% 7.68/1.49  inst_num_of_dismatching_blockings:      2710
% 7.68/1.49  inst_num_of_non_proper_insts:           3475
% 7.68/1.49  inst_num_of_duplicates:                 0
% 7.68/1.49  inst_inst_num_from_inst_to_res:         0
% 7.68/1.49  inst_dismatching_checking_time:         0.
% 7.68/1.49  
% 7.68/1.49  ------ Resolution
% 7.68/1.49  
% 7.68/1.49  res_num_of_clauses:                     0
% 7.68/1.49  res_num_in_passive:                     0
% 7.68/1.49  res_num_in_active:                      0
% 7.68/1.49  res_num_of_loops:                       54
% 7.68/1.49  res_forward_subset_subsumed:            497
% 7.68/1.49  res_backward_subset_subsumed:           34
% 7.68/1.49  res_forward_subsumed:                   0
% 7.68/1.49  res_backward_subsumed:                  0
% 7.68/1.49  res_forward_subsumption_resolution:     0
% 7.68/1.49  res_backward_subsumption_resolution:    0
% 7.68/1.49  res_clause_to_clause_subsumption:       3151
% 7.68/1.49  res_orphan_elimination:                 0
% 7.68/1.49  res_tautology_del:                      290
% 7.68/1.49  res_num_eq_res_simplified:              0
% 7.68/1.49  res_num_sel_changes:                    0
% 7.68/1.49  res_moves_from_active_to_pass:          0
% 7.68/1.49  
% 7.68/1.49  ------ Superposition
% 7.68/1.49  
% 7.68/1.49  sup_time_total:                         0.
% 7.68/1.49  sup_time_generating:                    0.
% 7.68/1.49  sup_time_sim_full:                      0.
% 7.68/1.49  sup_time_sim_immed:                     0.
% 7.68/1.49  
% 7.68/1.49  sup_num_of_clauses:                     602
% 7.68/1.49  sup_num_in_active:                      190
% 7.68/1.49  sup_num_in_passive:                     412
% 7.68/1.49  sup_num_of_loops:                       196
% 7.68/1.49  sup_fw_superposition:                   494
% 7.68/1.49  sup_bw_superposition:                   577
% 7.68/1.49  sup_immediate_simplified:               123
% 7.68/1.49  sup_given_eliminated:                   4
% 7.68/1.49  comparisons_done:                       0
% 7.68/1.49  comparisons_avoided:                    0
% 7.68/1.49  
% 7.68/1.49  ------ Simplifications
% 7.68/1.49  
% 7.68/1.49  
% 7.68/1.49  sim_fw_subset_subsumed:                 0
% 7.68/1.49  sim_bw_subset_subsumed:                 0
% 7.68/1.49  sim_fw_subsumed:                        1
% 7.68/1.49  sim_bw_subsumed:                        0
% 7.68/1.49  sim_fw_subsumption_res:                 0
% 7.68/1.49  sim_bw_subsumption_res:                 0
% 7.68/1.49  sim_tautology_del:                      0
% 7.68/1.49  sim_eq_tautology_del:                   4
% 7.68/1.49  sim_eq_res_simp:                        0
% 7.68/1.49  sim_fw_demodulated:                     8
% 7.68/1.49  sim_bw_demodulated:                     14
% 7.68/1.49  sim_light_normalised:                   125
% 7.68/1.49  sim_joinable_taut:                      0
% 7.68/1.49  sim_joinable_simp:                      0
% 7.68/1.49  sim_ac_normalised:                      0
% 7.68/1.49  sim_smt_subsumption:                    0
% 7.68/1.49  
%------------------------------------------------------------------------------
