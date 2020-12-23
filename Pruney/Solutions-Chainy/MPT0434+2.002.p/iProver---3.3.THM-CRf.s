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
% DateTime   : Thu Dec  3 11:42:54 EST 2020

% Result     : Theorem 11.28s
% Output     : CNFRefutation 11.28s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 167 expanded)
%              Number of clauses        :   42 (  72 expanded)
%              Number of leaves         :   11 (  39 expanded)
%              Depth                    :   14
%              Number of atoms          :  129 ( 390 expanded)
%              Number of equality atoms :   50 (  87 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f16,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))
          & v1_relat_1(X1) )
     => ( ~ r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(sK1)),k1_relat_1(k6_subset_1(X0,sK1)))
        & v1_relat_1(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(sK0,X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ~ r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k6_subset_1(sK0,sK1)))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f16,f15])).

fof(f26,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f5,axiom,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f27,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k6_subset_1(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(definition_unfolding,[],[f20,f23])).

fof(f28,plain,(
    ~ r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k6_subset_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f17])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k6_subset_1(X1,X0)) ),
    inference(definition_unfolding,[],[f19,f23])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

cnf(c_9,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_165,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_322,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_165])).

cnf(c_4,plain,
    ( m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_94,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | k6_subset_1(X2,X3) != X1
    | k1_zfmisc_1(X0) != k1_zfmisc_1(X2) ),
    inference(resolution_lifted,[status(thm)],[c_4,c_5])).

cnf(c_95,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k6_subset_1(X1,X2))
    | k1_zfmisc_1(X0) != k1_zfmisc_1(X1) ),
    inference(unflattening,[status(thm)],[c_94])).

cnf(c_164,plain,
    ( ~ v1_relat_1(X0_37)
    | v1_relat_1(k6_subset_1(X1_37,X2_37))
    | k1_zfmisc_1(X0_37) != k1_zfmisc_1(X1_37) ),
    inference(subtyping,[status(esa)],[c_95])).

cnf(c_323,plain,
    ( k1_zfmisc_1(X0_37) != k1_zfmisc_1(X1_37)
    | v1_relat_1(X0_37) != iProver_top
    | v1_relat_1(k6_subset_1(X1_37,X2_37)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_164])).

cnf(c_1825,plain,
    ( v1_relat_1(X0_37) != iProver_top
    | v1_relat_1(k6_subset_1(X0_37,X1_37)) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_323])).

cnf(c_8,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_166,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_321,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_166])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_168,plain,
    ( ~ v1_relat_1(X0_37)
    | ~ v1_relat_1(X1_37)
    | k2_xboole_0(k1_relat_1(X0_37),k1_relat_1(X1_37)) = k1_relat_1(k2_xboole_0(X0_37,X1_37)) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_319,plain,
    ( k2_xboole_0(k1_relat_1(X0_37),k1_relat_1(X1_37)) = k1_relat_1(k2_xboole_0(X0_37,X1_37))
    | v1_relat_1(X0_37) != iProver_top
    | v1_relat_1(X1_37) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_168])).

cnf(c_1128,plain,
    ( k2_xboole_0(k1_relat_1(sK1),k1_relat_1(X0_37)) = k1_relat_1(k2_xboole_0(sK1,X0_37))
    | v1_relat_1(X0_37) != iProver_top ),
    inference(superposition,[status(thm)],[c_321,c_319])).

cnf(c_20584,plain,
    ( k2_xboole_0(k1_relat_1(sK1),k1_relat_1(k6_subset_1(X0_37,X1_37))) = k1_relat_1(k2_xboole_0(sK1,k6_subset_1(X0_37,X1_37)))
    | v1_relat_1(X0_37) != iProver_top ),
    inference(superposition,[status(thm)],[c_1825,c_1128])).

cnf(c_24817,plain,
    ( k2_xboole_0(k1_relat_1(sK1),k1_relat_1(k6_subset_1(sK0,X0_37))) = k1_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,X0_37))) ),
    inference(superposition,[status(thm)],[c_322,c_20584])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
    | r1_tarski(k6_subset_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_170,plain,
    ( ~ r1_tarski(X0_37,k2_xboole_0(X1_37,X2_37))
    | r1_tarski(k6_subset_1(X0_37,X1_37),X2_37) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_317,plain,
    ( r1_tarski(X0_37,k2_xboole_0(X1_37,X2_37)) != iProver_top
    | r1_tarski(k6_subset_1(X0_37,X1_37),X2_37) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_170])).

cnf(c_25463,plain,
    ( r1_tarski(X0_37,k1_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,X1_37)))) != iProver_top
    | r1_tarski(k6_subset_1(X0_37,k1_relat_1(sK1)),k1_relat_1(k6_subset_1(sK0,X1_37))) = iProver_top ),
    inference(superposition,[status(thm)],[c_24817,c_317])).

cnf(c_7,negated_conjecture,
    ( ~ r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k6_subset_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_167,negated_conjecture,
    ( ~ r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k6_subset_1(sK0,sK1))) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_320,plain,
    ( r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k6_subset_1(sK0,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_167])).

cnf(c_42245,plain,
    ( r1_tarski(k1_relat_1(sK0),k1_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_25463,c_320])).

cnf(c_1,plain,
    ( k2_xboole_0(X0,k6_subset_1(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_171,plain,
    ( k2_xboole_0(X0_37,k6_subset_1(X1_37,X0_37)) = k2_xboole_0(X0_37,X1_37) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1365,plain,
    ( k2_xboole_0(k1_relat_1(sK1),k1_relat_1(sK0)) = k1_relat_1(k2_xboole_0(sK1,sK0)) ),
    inference(superposition,[status(thm)],[c_322,c_1128])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_172,plain,
    ( k2_xboole_0(X0_37,X1_37) = k2_xboole_0(X1_37,X0_37) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1485,plain,
    ( k2_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) = k1_relat_1(k2_xboole_0(sK1,sK0)) ),
    inference(superposition,[status(thm)],[c_1365,c_172])).

cnf(c_1129,plain,
    ( k2_xboole_0(k1_relat_1(sK0),k1_relat_1(X0_37)) = k1_relat_1(k2_xboole_0(sK0,X0_37))
    | v1_relat_1(X0_37) != iProver_top ),
    inference(superposition,[status(thm)],[c_322,c_319])).

cnf(c_1502,plain,
    ( k2_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) = k1_relat_1(k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_321,c_1129])).

cnf(c_1829,plain,
    ( k1_relat_1(k2_xboole_0(sK0,sK1)) = k1_relat_1(k2_xboole_0(sK1,sK0)) ),
    inference(light_normalisation,[status(thm)],[c_1485,c_1502])).

cnf(c_42246,plain,
    ( r1_tarski(k1_relat_1(sK0),k1_relat_1(k2_xboole_0(sK0,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_42245,c_171,c_1829])).

cnf(c_3,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_169,plain,
    ( r1_tarski(X0_37,k2_xboole_0(X0_37,X1_37)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_318,plain,
    ( r1_tarski(X0_37,k2_xboole_0(X0_37,X1_37)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_169])).

cnf(c_1671,plain,
    ( r1_tarski(k1_relat_1(sK0),k1_relat_1(k2_xboole_0(sK0,sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1502,c_318])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_42246,c_1671])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:27:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 11.28/1.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.28/1.99  
% 11.28/1.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.28/1.99  
% 11.28/1.99  ------  iProver source info
% 11.28/1.99  
% 11.28/1.99  git: date: 2020-06-30 10:37:57 +0100
% 11.28/1.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.28/1.99  git: non_committed_changes: false
% 11.28/1.99  git: last_make_outside_of_git: false
% 11.28/1.99  
% 11.28/1.99  ------ 
% 11.28/1.99  
% 11.28/1.99  ------ Input Options
% 11.28/1.99  
% 11.28/1.99  --out_options                           all
% 11.28/1.99  --tptp_safe_out                         true
% 11.28/1.99  --problem_path                          ""
% 11.28/1.99  --include_path                          ""
% 11.28/1.99  --clausifier                            res/vclausify_rel
% 11.28/1.99  --clausifier_options                    ""
% 11.28/1.99  --stdin                                 false
% 11.28/1.99  --stats_out                             all
% 11.28/1.99  
% 11.28/1.99  ------ General Options
% 11.28/1.99  
% 11.28/1.99  --fof                                   false
% 11.28/1.99  --time_out_real                         305.
% 11.28/1.99  --time_out_virtual                      -1.
% 11.28/1.99  --symbol_type_check                     false
% 11.28/1.99  --clausify_out                          false
% 11.28/1.99  --sig_cnt_out                           false
% 11.28/1.99  --trig_cnt_out                          false
% 11.28/1.99  --trig_cnt_out_tolerance                1.
% 11.28/1.99  --trig_cnt_out_sk_spl                   false
% 11.28/1.99  --abstr_cl_out                          false
% 11.28/1.99  
% 11.28/1.99  ------ Global Options
% 11.28/1.99  
% 11.28/1.99  --schedule                              default
% 11.28/1.99  --add_important_lit                     false
% 11.28/1.99  --prop_solver_per_cl                    1000
% 11.28/1.99  --min_unsat_core                        false
% 11.28/1.99  --soft_assumptions                      false
% 11.28/1.99  --soft_lemma_size                       3
% 11.28/1.99  --prop_impl_unit_size                   0
% 11.28/1.99  --prop_impl_unit                        []
% 11.28/1.99  --share_sel_clauses                     true
% 11.28/1.99  --reset_solvers                         false
% 11.28/1.99  --bc_imp_inh                            [conj_cone]
% 11.28/1.99  --conj_cone_tolerance                   3.
% 11.28/1.99  --extra_neg_conj                        none
% 11.28/1.99  --large_theory_mode                     true
% 11.28/1.99  --prolific_symb_bound                   200
% 11.28/1.99  --lt_threshold                          2000
% 11.28/1.99  --clause_weak_htbl                      true
% 11.28/1.99  --gc_record_bc_elim                     false
% 11.28/1.99  
% 11.28/1.99  ------ Preprocessing Options
% 11.28/1.99  
% 11.28/1.99  --preprocessing_flag                    true
% 11.28/1.99  --time_out_prep_mult                    0.1
% 11.28/1.99  --splitting_mode                        input
% 11.28/1.99  --splitting_grd                         true
% 11.28/1.99  --splitting_cvd                         false
% 11.28/1.99  --splitting_cvd_svl                     false
% 11.28/1.99  --splitting_nvd                         32
% 11.28/1.99  --sub_typing                            true
% 11.28/1.99  --prep_gs_sim                           true
% 11.28/1.99  --prep_unflatten                        true
% 11.28/1.99  --prep_res_sim                          true
% 11.28/1.99  --prep_upred                            true
% 11.28/1.99  --prep_sem_filter                       exhaustive
% 11.28/1.99  --prep_sem_filter_out                   false
% 11.28/1.99  --pred_elim                             true
% 11.28/1.99  --res_sim_input                         true
% 11.28/1.99  --eq_ax_congr_red                       true
% 11.28/1.99  --pure_diseq_elim                       true
% 11.28/1.99  --brand_transform                       false
% 11.28/1.99  --non_eq_to_eq                          false
% 11.28/1.99  --prep_def_merge                        true
% 11.28/1.99  --prep_def_merge_prop_impl              false
% 11.28/1.99  --prep_def_merge_mbd                    true
% 11.28/1.99  --prep_def_merge_tr_red                 false
% 11.28/1.99  --prep_def_merge_tr_cl                  false
% 11.28/1.99  --smt_preprocessing                     true
% 11.28/1.99  --smt_ac_axioms                         fast
% 11.28/1.99  --preprocessed_out                      false
% 11.28/1.99  --preprocessed_stats                    false
% 11.28/1.99  
% 11.28/1.99  ------ Abstraction refinement Options
% 11.28/1.99  
% 11.28/1.99  --abstr_ref                             []
% 11.28/1.99  --abstr_ref_prep                        false
% 11.28/1.99  --abstr_ref_until_sat                   false
% 11.28/1.99  --abstr_ref_sig_restrict                funpre
% 11.28/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.28/1.99  --abstr_ref_under                       []
% 11.28/1.99  
% 11.28/1.99  ------ SAT Options
% 11.28/1.99  
% 11.28/1.99  --sat_mode                              false
% 11.28/1.99  --sat_fm_restart_options                ""
% 11.28/1.99  --sat_gr_def                            false
% 11.28/1.99  --sat_epr_types                         true
% 11.28/1.99  --sat_non_cyclic_types                  false
% 11.28/1.99  --sat_finite_models                     false
% 11.28/1.99  --sat_fm_lemmas                         false
% 11.28/1.99  --sat_fm_prep                           false
% 11.28/1.99  --sat_fm_uc_incr                        true
% 11.28/1.99  --sat_out_model                         small
% 11.28/1.99  --sat_out_clauses                       false
% 11.28/1.99  
% 11.28/1.99  ------ QBF Options
% 11.28/1.99  
% 11.28/1.99  --qbf_mode                              false
% 11.28/1.99  --qbf_elim_univ                         false
% 11.28/1.99  --qbf_dom_inst                          none
% 11.28/1.99  --qbf_dom_pre_inst                      false
% 11.28/1.99  --qbf_sk_in                             false
% 11.28/1.99  --qbf_pred_elim                         true
% 11.28/1.99  --qbf_split                             512
% 11.28/1.99  
% 11.28/1.99  ------ BMC1 Options
% 11.28/1.99  
% 11.28/1.99  --bmc1_incremental                      false
% 11.28/1.99  --bmc1_axioms                           reachable_all
% 11.28/1.99  --bmc1_min_bound                        0
% 11.28/1.99  --bmc1_max_bound                        -1
% 11.28/1.99  --bmc1_max_bound_default                -1
% 11.28/1.99  --bmc1_symbol_reachability              true
% 11.28/1.99  --bmc1_property_lemmas                  false
% 11.28/1.99  --bmc1_k_induction                      false
% 11.28/1.99  --bmc1_non_equiv_states                 false
% 11.28/1.99  --bmc1_deadlock                         false
% 11.28/1.99  --bmc1_ucm                              false
% 11.28/1.99  --bmc1_add_unsat_core                   none
% 11.28/1.99  --bmc1_unsat_core_children              false
% 11.28/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.28/1.99  --bmc1_out_stat                         full
% 11.28/1.99  --bmc1_ground_init                      false
% 11.28/1.99  --bmc1_pre_inst_next_state              false
% 11.28/1.99  --bmc1_pre_inst_state                   false
% 11.28/1.99  --bmc1_pre_inst_reach_state             false
% 11.28/1.99  --bmc1_out_unsat_core                   false
% 11.28/1.99  --bmc1_aig_witness_out                  false
% 11.28/1.99  --bmc1_verbose                          false
% 11.28/1.99  --bmc1_dump_clauses_tptp                false
% 11.28/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.28/1.99  --bmc1_dump_file                        -
% 11.28/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.28/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.28/1.99  --bmc1_ucm_extend_mode                  1
% 11.28/1.99  --bmc1_ucm_init_mode                    2
% 11.28/1.99  --bmc1_ucm_cone_mode                    none
% 11.28/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.28/1.99  --bmc1_ucm_relax_model                  4
% 11.28/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.28/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.28/1.99  --bmc1_ucm_layered_model                none
% 11.28/1.99  --bmc1_ucm_max_lemma_size               10
% 11.28/1.99  
% 11.28/1.99  ------ AIG Options
% 11.28/1.99  
% 11.28/1.99  --aig_mode                              false
% 11.28/1.99  
% 11.28/1.99  ------ Instantiation Options
% 11.28/1.99  
% 11.28/1.99  --instantiation_flag                    true
% 11.28/1.99  --inst_sos_flag                         true
% 11.28/1.99  --inst_sos_phase                        true
% 11.28/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.28/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.28/1.99  --inst_lit_sel_side                     num_symb
% 11.28/1.99  --inst_solver_per_active                1400
% 11.28/1.99  --inst_solver_calls_frac                1.
% 11.28/1.99  --inst_passive_queue_type               priority_queues
% 11.28/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.28/1.99  --inst_passive_queues_freq              [25;2]
% 11.28/1.99  --inst_dismatching                      true
% 11.28/1.99  --inst_eager_unprocessed_to_passive     true
% 11.28/1.99  --inst_prop_sim_given                   true
% 11.28/1.99  --inst_prop_sim_new                     false
% 11.28/1.99  --inst_subs_new                         false
% 11.28/1.99  --inst_eq_res_simp                      false
% 11.28/1.99  --inst_subs_given                       false
% 11.28/1.99  --inst_orphan_elimination               true
% 11.28/1.99  --inst_learning_loop_flag               true
% 11.28/1.99  --inst_learning_start                   3000
% 11.28/1.99  --inst_learning_factor                  2
% 11.28/1.99  --inst_start_prop_sim_after_learn       3
% 11.28/1.99  --inst_sel_renew                        solver
% 11.28/1.99  --inst_lit_activity_flag                true
% 11.28/1.99  --inst_restr_to_given                   false
% 11.28/1.99  --inst_activity_threshold               500
% 11.28/1.99  --inst_out_proof                        true
% 11.28/1.99  
% 11.28/1.99  ------ Resolution Options
% 11.28/1.99  
% 11.28/1.99  --resolution_flag                       true
% 11.28/1.99  --res_lit_sel                           adaptive
% 11.28/1.99  --res_lit_sel_side                      none
% 11.28/1.99  --res_ordering                          kbo
% 11.28/1.99  --res_to_prop_solver                    active
% 11.28/1.99  --res_prop_simpl_new                    false
% 11.28/1.99  --res_prop_simpl_given                  true
% 11.28/1.99  --res_passive_queue_type                priority_queues
% 11.28/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.28/1.99  --res_passive_queues_freq               [15;5]
% 11.28/1.99  --res_forward_subs                      full
% 11.28/1.99  --res_backward_subs                     full
% 11.28/1.99  --res_forward_subs_resolution           true
% 11.28/1.99  --res_backward_subs_resolution          true
% 11.28/1.99  --res_orphan_elimination                true
% 11.28/1.99  --res_time_limit                        2.
% 11.28/1.99  --res_out_proof                         true
% 11.28/1.99  
% 11.28/1.99  ------ Superposition Options
% 11.28/1.99  
% 11.28/1.99  --superposition_flag                    true
% 11.28/1.99  --sup_passive_queue_type                priority_queues
% 11.28/1.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.28/1.99  --sup_passive_queues_freq               [8;1;4]
% 11.28/1.99  --demod_completeness_check              fast
% 11.28/1.99  --demod_use_ground                      true
% 11.28/1.99  --sup_to_prop_solver                    passive
% 11.28/1.99  --sup_prop_simpl_new                    true
% 11.28/1.99  --sup_prop_simpl_given                  true
% 11.28/1.99  --sup_fun_splitting                     true
% 11.28/1.99  --sup_smt_interval                      50000
% 11.28/1.99  
% 11.28/1.99  ------ Superposition Simplification Setup
% 11.28/1.99  
% 11.28/1.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.28/1.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.28/1.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.28/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.28/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 11.28/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.28/1.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.28/1.99  --sup_immed_triv                        [TrivRules]
% 11.28/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.28/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.28/1.99  --sup_immed_bw_main                     []
% 11.28/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.28/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 11.28/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.28/1.99  --sup_input_bw                          []
% 11.28/1.99  
% 11.28/1.99  ------ Combination Options
% 11.28/1.99  
% 11.28/1.99  --comb_res_mult                         3
% 11.28/1.99  --comb_sup_mult                         2
% 11.28/1.99  --comb_inst_mult                        10
% 11.28/1.99  
% 11.28/1.99  ------ Debug Options
% 11.28/1.99  
% 11.28/1.99  --dbg_backtrace                         false
% 11.28/1.99  --dbg_dump_prop_clauses                 false
% 11.28/1.99  --dbg_dump_prop_clauses_file            -
% 11.28/1.99  --dbg_out_stat                          false
% 11.28/1.99  ------ Parsing...
% 11.28/1.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.28/1.99  
% 11.28/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 11.28/1.99  
% 11.28/1.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.28/1.99  
% 11.28/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.28/1.99  ------ Proving...
% 11.28/1.99  ------ Problem Properties 
% 11.28/1.99  
% 11.28/1.99  
% 11.28/1.99  clauses                                 9
% 11.28/1.99  conjectures                             3
% 11.28/1.99  EPR                                     2
% 11.28/1.99  Horn                                    9
% 11.28/1.99  unary                                   6
% 11.28/1.99  binary                                  1
% 11.28/1.99  lits                                    14
% 11.28/1.99  lits eq                                 4
% 11.28/1.99  fd_pure                                 0
% 11.28/1.99  fd_pseudo                               0
% 11.28/1.99  fd_cond                                 0
% 11.28/1.99  fd_pseudo_cond                          0
% 11.28/1.99  AC symbols                              0
% 11.28/1.99  
% 11.28/1.99  ------ Schedule dynamic 5 is on 
% 11.28/1.99  
% 11.28/1.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.28/1.99  
% 11.28/1.99  
% 11.28/1.99  ------ 
% 11.28/1.99  Current options:
% 11.28/1.99  ------ 
% 11.28/1.99  
% 11.28/1.99  ------ Input Options
% 11.28/1.99  
% 11.28/1.99  --out_options                           all
% 11.28/1.99  --tptp_safe_out                         true
% 11.28/1.99  --problem_path                          ""
% 11.28/1.99  --include_path                          ""
% 11.28/1.99  --clausifier                            res/vclausify_rel
% 11.28/1.99  --clausifier_options                    ""
% 11.28/1.99  --stdin                                 false
% 11.28/1.99  --stats_out                             all
% 11.28/1.99  
% 11.28/1.99  ------ General Options
% 11.28/1.99  
% 11.28/1.99  --fof                                   false
% 11.28/1.99  --time_out_real                         305.
% 11.28/1.99  --time_out_virtual                      -1.
% 11.28/1.99  --symbol_type_check                     false
% 11.28/1.99  --clausify_out                          false
% 11.28/1.99  --sig_cnt_out                           false
% 11.28/1.99  --trig_cnt_out                          false
% 11.28/1.99  --trig_cnt_out_tolerance                1.
% 11.28/1.99  --trig_cnt_out_sk_spl                   false
% 11.28/1.99  --abstr_cl_out                          false
% 11.28/1.99  
% 11.28/1.99  ------ Global Options
% 11.28/1.99  
% 11.28/1.99  --schedule                              default
% 11.28/1.99  --add_important_lit                     false
% 11.28/1.99  --prop_solver_per_cl                    1000
% 11.28/1.99  --min_unsat_core                        false
% 11.28/1.99  --soft_assumptions                      false
% 11.28/1.99  --soft_lemma_size                       3
% 11.28/1.99  --prop_impl_unit_size                   0
% 11.28/1.99  --prop_impl_unit                        []
% 11.28/1.99  --share_sel_clauses                     true
% 11.28/1.99  --reset_solvers                         false
% 11.28/1.99  --bc_imp_inh                            [conj_cone]
% 11.28/1.99  --conj_cone_tolerance                   3.
% 11.28/1.99  --extra_neg_conj                        none
% 11.28/1.99  --large_theory_mode                     true
% 11.28/1.99  --prolific_symb_bound                   200
% 11.28/1.99  --lt_threshold                          2000
% 11.28/1.99  --clause_weak_htbl                      true
% 11.28/1.99  --gc_record_bc_elim                     false
% 11.28/1.99  
% 11.28/1.99  ------ Preprocessing Options
% 11.28/1.99  
% 11.28/1.99  --preprocessing_flag                    true
% 11.28/1.99  --time_out_prep_mult                    0.1
% 11.28/1.99  --splitting_mode                        input
% 11.28/1.99  --splitting_grd                         true
% 11.28/1.99  --splitting_cvd                         false
% 11.28/1.99  --splitting_cvd_svl                     false
% 11.28/1.99  --splitting_nvd                         32
% 11.28/1.99  --sub_typing                            true
% 11.28/1.99  --prep_gs_sim                           true
% 11.28/1.99  --prep_unflatten                        true
% 11.28/1.99  --prep_res_sim                          true
% 11.28/1.99  --prep_upred                            true
% 11.28/1.99  --prep_sem_filter                       exhaustive
% 11.28/1.99  --prep_sem_filter_out                   false
% 11.28/1.99  --pred_elim                             true
% 11.28/1.99  --res_sim_input                         true
% 11.28/1.99  --eq_ax_congr_red                       true
% 11.28/1.99  --pure_diseq_elim                       true
% 11.28/1.99  --brand_transform                       false
% 11.28/1.99  --non_eq_to_eq                          false
% 11.28/1.99  --prep_def_merge                        true
% 11.28/1.99  --prep_def_merge_prop_impl              false
% 11.28/1.99  --prep_def_merge_mbd                    true
% 11.28/1.99  --prep_def_merge_tr_red                 false
% 11.28/1.99  --prep_def_merge_tr_cl                  false
% 11.28/1.99  --smt_preprocessing                     true
% 11.28/1.99  --smt_ac_axioms                         fast
% 11.28/1.99  --preprocessed_out                      false
% 11.28/1.99  --preprocessed_stats                    false
% 11.28/1.99  
% 11.28/1.99  ------ Abstraction refinement Options
% 11.28/1.99  
% 11.28/1.99  --abstr_ref                             []
% 11.28/1.99  --abstr_ref_prep                        false
% 11.28/1.99  --abstr_ref_until_sat                   false
% 11.28/1.99  --abstr_ref_sig_restrict                funpre
% 11.28/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.28/1.99  --abstr_ref_under                       []
% 11.28/1.99  
% 11.28/1.99  ------ SAT Options
% 11.28/1.99  
% 11.28/1.99  --sat_mode                              false
% 11.28/1.99  --sat_fm_restart_options                ""
% 11.28/1.99  --sat_gr_def                            false
% 11.28/1.99  --sat_epr_types                         true
% 11.28/1.99  --sat_non_cyclic_types                  false
% 11.28/1.99  --sat_finite_models                     false
% 11.28/1.99  --sat_fm_lemmas                         false
% 11.28/1.99  --sat_fm_prep                           false
% 11.28/1.99  --sat_fm_uc_incr                        true
% 11.28/1.99  --sat_out_model                         small
% 11.28/1.99  --sat_out_clauses                       false
% 11.28/1.99  
% 11.28/1.99  ------ QBF Options
% 11.28/1.99  
% 11.28/1.99  --qbf_mode                              false
% 11.28/1.99  --qbf_elim_univ                         false
% 11.28/1.99  --qbf_dom_inst                          none
% 11.28/1.99  --qbf_dom_pre_inst                      false
% 11.28/1.99  --qbf_sk_in                             false
% 11.28/1.99  --qbf_pred_elim                         true
% 11.28/1.99  --qbf_split                             512
% 11.28/1.99  
% 11.28/1.99  ------ BMC1 Options
% 11.28/1.99  
% 11.28/1.99  --bmc1_incremental                      false
% 11.28/1.99  --bmc1_axioms                           reachable_all
% 11.28/1.99  --bmc1_min_bound                        0
% 11.28/1.99  --bmc1_max_bound                        -1
% 11.28/1.99  --bmc1_max_bound_default                -1
% 11.28/1.99  --bmc1_symbol_reachability              true
% 11.28/1.99  --bmc1_property_lemmas                  false
% 11.28/1.99  --bmc1_k_induction                      false
% 11.28/1.99  --bmc1_non_equiv_states                 false
% 11.28/1.99  --bmc1_deadlock                         false
% 11.28/1.99  --bmc1_ucm                              false
% 11.28/1.99  --bmc1_add_unsat_core                   none
% 11.28/1.99  --bmc1_unsat_core_children              false
% 11.28/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.28/1.99  --bmc1_out_stat                         full
% 11.28/1.99  --bmc1_ground_init                      false
% 11.28/1.99  --bmc1_pre_inst_next_state              false
% 11.28/1.99  --bmc1_pre_inst_state                   false
% 11.28/1.99  --bmc1_pre_inst_reach_state             false
% 11.28/1.99  --bmc1_out_unsat_core                   false
% 11.28/1.99  --bmc1_aig_witness_out                  false
% 11.28/1.99  --bmc1_verbose                          false
% 11.28/1.99  --bmc1_dump_clauses_tptp                false
% 11.28/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.28/1.99  --bmc1_dump_file                        -
% 11.28/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.28/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.28/1.99  --bmc1_ucm_extend_mode                  1
% 11.28/1.99  --bmc1_ucm_init_mode                    2
% 11.28/1.99  --bmc1_ucm_cone_mode                    none
% 11.28/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.28/1.99  --bmc1_ucm_relax_model                  4
% 11.28/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.28/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.28/1.99  --bmc1_ucm_layered_model                none
% 11.28/1.99  --bmc1_ucm_max_lemma_size               10
% 11.28/1.99  
% 11.28/1.99  ------ AIG Options
% 11.28/1.99  
% 11.28/1.99  --aig_mode                              false
% 11.28/1.99  
% 11.28/1.99  ------ Instantiation Options
% 11.28/1.99  
% 11.28/1.99  --instantiation_flag                    true
% 11.28/1.99  --inst_sos_flag                         true
% 11.28/1.99  --inst_sos_phase                        true
% 11.28/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.28/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.28/1.99  --inst_lit_sel_side                     none
% 11.28/1.99  --inst_solver_per_active                1400
% 11.28/1.99  --inst_solver_calls_frac                1.
% 11.28/1.99  --inst_passive_queue_type               priority_queues
% 11.28/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.28/1.99  --inst_passive_queues_freq              [25;2]
% 11.28/1.99  --inst_dismatching                      true
% 11.28/1.99  --inst_eager_unprocessed_to_passive     true
% 11.28/1.99  --inst_prop_sim_given                   true
% 11.28/1.99  --inst_prop_sim_new                     false
% 11.28/1.99  --inst_subs_new                         false
% 11.28/1.99  --inst_eq_res_simp                      false
% 11.28/1.99  --inst_subs_given                       false
% 11.28/1.99  --inst_orphan_elimination               true
% 11.28/1.99  --inst_learning_loop_flag               true
% 11.28/1.99  --inst_learning_start                   3000
% 11.28/1.99  --inst_learning_factor                  2
% 11.28/1.99  --inst_start_prop_sim_after_learn       3
% 11.28/1.99  --inst_sel_renew                        solver
% 11.28/1.99  --inst_lit_activity_flag                true
% 11.28/1.99  --inst_restr_to_given                   false
% 11.28/1.99  --inst_activity_threshold               500
% 11.28/1.99  --inst_out_proof                        true
% 11.28/1.99  
% 11.28/1.99  ------ Resolution Options
% 11.28/1.99  
% 11.28/1.99  --resolution_flag                       false
% 11.28/1.99  --res_lit_sel                           adaptive
% 11.28/1.99  --res_lit_sel_side                      none
% 11.28/1.99  --res_ordering                          kbo
% 11.28/1.99  --res_to_prop_solver                    active
% 11.28/1.99  --res_prop_simpl_new                    false
% 11.28/1.99  --res_prop_simpl_given                  true
% 11.28/1.99  --res_passive_queue_type                priority_queues
% 11.28/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.28/1.99  --res_passive_queues_freq               [15;5]
% 11.28/1.99  --res_forward_subs                      full
% 11.28/1.99  --res_backward_subs                     full
% 11.28/1.99  --res_forward_subs_resolution           true
% 11.28/1.99  --res_backward_subs_resolution          true
% 11.28/1.99  --res_orphan_elimination                true
% 11.28/1.99  --res_time_limit                        2.
% 11.28/1.99  --res_out_proof                         true
% 11.28/1.99  
% 11.28/1.99  ------ Superposition Options
% 11.28/1.99  
% 11.28/1.99  --superposition_flag                    true
% 11.28/1.99  --sup_passive_queue_type                priority_queues
% 11.28/1.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.28/1.99  --sup_passive_queues_freq               [8;1;4]
% 11.28/1.99  --demod_completeness_check              fast
% 11.28/1.99  --demod_use_ground                      true
% 11.28/1.99  --sup_to_prop_solver                    passive
% 11.28/1.99  --sup_prop_simpl_new                    true
% 11.28/1.99  --sup_prop_simpl_given                  true
% 11.28/1.99  --sup_fun_splitting                     true
% 11.28/1.99  --sup_smt_interval                      50000
% 11.28/1.99  
% 11.28/1.99  ------ Superposition Simplification Setup
% 11.28/1.99  
% 11.28/1.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.28/1.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.28/1.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.28/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.28/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 11.28/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.28/1.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.28/1.99  --sup_immed_triv                        [TrivRules]
% 11.28/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.28/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.28/1.99  --sup_immed_bw_main                     []
% 11.28/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.28/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 11.28/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.28/1.99  --sup_input_bw                          []
% 11.28/1.99  
% 11.28/1.99  ------ Combination Options
% 11.28/1.99  
% 11.28/1.99  --comb_res_mult                         3
% 11.28/1.99  --comb_sup_mult                         2
% 11.28/1.99  --comb_inst_mult                        10
% 11.28/1.99  
% 11.28/1.99  ------ Debug Options
% 11.28/1.99  
% 11.28/1.99  --dbg_backtrace                         false
% 11.28/1.99  --dbg_dump_prop_clauses                 false
% 11.28/1.99  --dbg_dump_prop_clauses_file            -
% 11.28/1.99  --dbg_out_stat                          false
% 11.28/1.99  
% 11.28/1.99  
% 11.28/1.99  
% 11.28/1.99  
% 11.28/1.99  ------ Proving...
% 11.28/1.99  
% 11.28/1.99  
% 11.28/1.99  % SZS status Theorem for theBenchmark.p
% 11.28/1.99  
% 11.28/1.99  % SZS output start CNFRefutation for theBenchmark.p
% 11.28/1.99  
% 11.28/1.99  fof(f9,conjecture,(
% 11.28/1.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))))),
% 11.28/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.28/1.99  
% 11.28/1.99  fof(f10,negated_conjecture,(
% 11.28/1.99    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))))),
% 11.28/1.99    inference(negated_conjecture,[],[f9])).
% 11.28/1.99  
% 11.28/1.99  fof(f14,plain,(
% 11.28/1.99    ? [X0] : (? [X1] : (~r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 11.28/1.99    inference(ennf_transformation,[],[f10])).
% 11.28/1.99  
% 11.28/1.99  fof(f16,plain,(
% 11.28/1.99    ( ! [X0] : (? [X1] : (~r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) & v1_relat_1(X1)) => (~r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(sK1)),k1_relat_1(k6_subset_1(X0,sK1))) & v1_relat_1(sK1))) )),
% 11.28/1.99    introduced(choice_axiom,[])).
% 11.28/1.99  
% 11.28/1.99  fof(f15,plain,(
% 11.28/1.99    ? [X0] : (? [X1] : (~r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(sK0,X1))) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 11.28/1.99    introduced(choice_axiom,[])).
% 11.28/1.99  
% 11.28/1.99  fof(f17,plain,(
% 11.28/1.99    (~r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k6_subset_1(sK0,sK1))) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 11.28/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f16,f15])).
% 11.28/1.99  
% 11.28/1.99  fof(f26,plain,(
% 11.28/1.99    v1_relat_1(sK0)),
% 11.28/1.99    inference(cnf_transformation,[],[f17])).
% 11.28/1.99  
% 11.28/1.99  fof(f5,axiom,(
% 11.28/1.99    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))),
% 11.28/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.28/1.99  
% 11.28/1.99  fof(f22,plain,(
% 11.28/1.99    ( ! [X0,X1] : (m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 11.28/1.99    inference(cnf_transformation,[],[f5])).
% 11.28/1.99  
% 11.28/1.99  fof(f7,axiom,(
% 11.28/1.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 11.28/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.28/1.99  
% 11.28/1.99  fof(f12,plain,(
% 11.28/1.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 11.28/1.99    inference(ennf_transformation,[],[f7])).
% 11.28/1.99  
% 11.28/1.99  fof(f24,plain,(
% 11.28/1.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 11.28/1.99    inference(cnf_transformation,[],[f12])).
% 11.28/1.99  
% 11.28/1.99  fof(f27,plain,(
% 11.28/1.99    v1_relat_1(sK1)),
% 11.28/1.99    inference(cnf_transformation,[],[f17])).
% 11.28/1.99  
% 11.28/1.99  fof(f8,axiom,(
% 11.28/1.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1))))),
% 11.28/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.28/1.99  
% 11.28/1.99  fof(f13,plain,(
% 11.28/1.99    ! [X0] : (! [X1] : (k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 11.28/1.99    inference(ennf_transformation,[],[f8])).
% 11.28/1.99  
% 11.28/1.99  fof(f25,plain,(
% 11.28/1.99    ( ! [X0,X1] : (k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 11.28/1.99    inference(cnf_transformation,[],[f13])).
% 11.28/1.99  
% 11.28/1.99  fof(f3,axiom,(
% 11.28/1.99    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 11.28/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.28/1.99  
% 11.28/1.99  fof(f11,plain,(
% 11.28/1.99    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 11.28/1.99    inference(ennf_transformation,[],[f3])).
% 11.28/1.99  
% 11.28/1.99  fof(f20,plain,(
% 11.28/1.99    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 11.28/1.99    inference(cnf_transformation,[],[f11])).
% 11.28/1.99  
% 11.28/1.99  fof(f6,axiom,(
% 11.28/1.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 11.28/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.28/1.99  
% 11.28/1.99  fof(f23,plain,(
% 11.28/1.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 11.28/1.99    inference(cnf_transformation,[],[f6])).
% 11.28/1.99  
% 11.28/1.99  fof(f30,plain,(
% 11.28/1.99    ( ! [X2,X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 11.28/1.99    inference(definition_unfolding,[],[f20,f23])).
% 11.28/1.99  
% 11.28/1.99  fof(f28,plain,(
% 11.28/1.99    ~r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k6_subset_1(sK0,sK1)))),
% 11.28/1.99    inference(cnf_transformation,[],[f17])).
% 11.28/1.99  
% 11.28/1.99  fof(f2,axiom,(
% 11.28/1.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 11.28/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.28/1.99  
% 11.28/1.99  fof(f19,plain,(
% 11.28/1.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 11.28/1.99    inference(cnf_transformation,[],[f2])).
% 11.28/1.99  
% 11.28/1.99  fof(f29,plain,(
% 11.28/1.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k6_subset_1(X1,X0))) )),
% 11.28/1.99    inference(definition_unfolding,[],[f19,f23])).
% 11.28/1.99  
% 11.28/1.99  fof(f1,axiom,(
% 11.28/1.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 11.28/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.28/1.99  
% 11.28/1.99  fof(f18,plain,(
% 11.28/1.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 11.28/1.99    inference(cnf_transformation,[],[f1])).
% 11.28/1.99  
% 11.28/1.99  fof(f4,axiom,(
% 11.28/1.99    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 11.28/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.28/1.99  
% 11.28/1.99  fof(f21,plain,(
% 11.28/1.99    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 11.28/1.99    inference(cnf_transformation,[],[f4])).
% 11.28/1.99  
% 11.28/1.99  cnf(c_9,negated_conjecture,
% 11.28/1.99      ( v1_relat_1(sK0) ),
% 11.28/1.99      inference(cnf_transformation,[],[f26]) ).
% 11.28/1.99  
% 11.28/1.99  cnf(c_165,negated_conjecture,
% 11.28/1.99      ( v1_relat_1(sK0) ),
% 11.28/1.99      inference(subtyping,[status(esa)],[c_9]) ).
% 11.28/1.99  
% 11.28/1.99  cnf(c_322,plain,
% 11.28/1.99      ( v1_relat_1(sK0) = iProver_top ),
% 11.28/1.99      inference(predicate_to_equality,[status(thm)],[c_165]) ).
% 11.28/1.99  
% 11.28/1.99  cnf(c_4,plain,
% 11.28/1.99      ( m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
% 11.28/1.99      inference(cnf_transformation,[],[f22]) ).
% 11.28/1.99  
% 11.28/1.99  cnf(c_5,plain,
% 11.28/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.28/1.99      | ~ v1_relat_1(X1)
% 11.28/1.99      | v1_relat_1(X0) ),
% 11.28/1.99      inference(cnf_transformation,[],[f24]) ).
% 11.28/1.99  
% 11.28/1.99  cnf(c_94,plain,
% 11.28/1.99      ( ~ v1_relat_1(X0)
% 11.28/1.99      | v1_relat_1(X1)
% 11.28/1.99      | k6_subset_1(X2,X3) != X1
% 11.28/1.99      | k1_zfmisc_1(X0) != k1_zfmisc_1(X2) ),
% 11.28/1.99      inference(resolution_lifted,[status(thm)],[c_4,c_5]) ).
% 11.28/1.99  
% 11.28/1.99  cnf(c_95,plain,
% 11.28/1.99      ( ~ v1_relat_1(X0)
% 11.28/1.99      | v1_relat_1(k6_subset_1(X1,X2))
% 11.28/1.99      | k1_zfmisc_1(X0) != k1_zfmisc_1(X1) ),
% 11.28/1.99      inference(unflattening,[status(thm)],[c_94]) ).
% 11.28/1.99  
% 11.28/1.99  cnf(c_164,plain,
% 11.28/1.99      ( ~ v1_relat_1(X0_37)
% 11.28/1.99      | v1_relat_1(k6_subset_1(X1_37,X2_37))
% 11.28/1.99      | k1_zfmisc_1(X0_37) != k1_zfmisc_1(X1_37) ),
% 11.28/1.99      inference(subtyping,[status(esa)],[c_95]) ).
% 11.28/1.99  
% 11.28/1.99  cnf(c_323,plain,
% 11.28/1.99      ( k1_zfmisc_1(X0_37) != k1_zfmisc_1(X1_37)
% 11.28/1.99      | v1_relat_1(X0_37) != iProver_top
% 11.28/1.99      | v1_relat_1(k6_subset_1(X1_37,X2_37)) = iProver_top ),
% 11.28/1.99      inference(predicate_to_equality,[status(thm)],[c_164]) ).
% 11.28/1.99  
% 11.28/1.99  cnf(c_1825,plain,
% 11.28/1.99      ( v1_relat_1(X0_37) != iProver_top
% 11.28/1.99      | v1_relat_1(k6_subset_1(X0_37,X1_37)) = iProver_top ),
% 11.28/1.99      inference(equality_resolution,[status(thm)],[c_323]) ).
% 11.28/1.99  
% 11.28/1.99  cnf(c_8,negated_conjecture,
% 11.28/1.99      ( v1_relat_1(sK1) ),
% 11.28/1.99      inference(cnf_transformation,[],[f27]) ).
% 11.28/1.99  
% 11.28/1.99  cnf(c_166,negated_conjecture,
% 11.28/1.99      ( v1_relat_1(sK1) ),
% 11.28/1.99      inference(subtyping,[status(esa)],[c_8]) ).
% 11.28/1.99  
% 11.28/1.99  cnf(c_321,plain,
% 11.28/1.99      ( v1_relat_1(sK1) = iProver_top ),
% 11.28/1.99      inference(predicate_to_equality,[status(thm)],[c_166]) ).
% 11.28/1.99  
% 11.28/1.99  cnf(c_6,plain,
% 11.28/1.99      ( ~ v1_relat_1(X0)
% 11.28/1.99      | ~ v1_relat_1(X1)
% 11.28/1.99      | k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1)) ),
% 11.28/1.99      inference(cnf_transformation,[],[f25]) ).
% 11.28/1.99  
% 11.28/1.99  cnf(c_168,plain,
% 11.28/1.99      ( ~ v1_relat_1(X0_37)
% 11.28/1.99      | ~ v1_relat_1(X1_37)
% 11.28/1.99      | k2_xboole_0(k1_relat_1(X0_37),k1_relat_1(X1_37)) = k1_relat_1(k2_xboole_0(X0_37,X1_37)) ),
% 11.28/1.99      inference(subtyping,[status(esa)],[c_6]) ).
% 11.28/1.99  
% 11.28/1.99  cnf(c_319,plain,
% 11.28/1.99      ( k2_xboole_0(k1_relat_1(X0_37),k1_relat_1(X1_37)) = k1_relat_1(k2_xboole_0(X0_37,X1_37))
% 11.28/1.99      | v1_relat_1(X0_37) != iProver_top
% 11.28/1.99      | v1_relat_1(X1_37) != iProver_top ),
% 11.28/1.99      inference(predicate_to_equality,[status(thm)],[c_168]) ).
% 11.28/1.99  
% 11.28/1.99  cnf(c_1128,plain,
% 11.28/1.99      ( k2_xboole_0(k1_relat_1(sK1),k1_relat_1(X0_37)) = k1_relat_1(k2_xboole_0(sK1,X0_37))
% 11.28/1.99      | v1_relat_1(X0_37) != iProver_top ),
% 11.28/1.99      inference(superposition,[status(thm)],[c_321,c_319]) ).
% 11.28/1.99  
% 11.28/1.99  cnf(c_20584,plain,
% 11.28/1.99      ( k2_xboole_0(k1_relat_1(sK1),k1_relat_1(k6_subset_1(X0_37,X1_37))) = k1_relat_1(k2_xboole_0(sK1,k6_subset_1(X0_37,X1_37)))
% 11.28/1.99      | v1_relat_1(X0_37) != iProver_top ),
% 11.28/1.99      inference(superposition,[status(thm)],[c_1825,c_1128]) ).
% 11.28/1.99  
% 11.28/1.99  cnf(c_24817,plain,
% 11.28/1.99      ( k2_xboole_0(k1_relat_1(sK1),k1_relat_1(k6_subset_1(sK0,X0_37))) = k1_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,X0_37))) ),
% 11.28/1.99      inference(superposition,[status(thm)],[c_322,c_20584]) ).
% 11.28/1.99  
% 11.28/1.99  cnf(c_2,plain,
% 11.28/1.99      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
% 11.28/1.99      | r1_tarski(k6_subset_1(X0,X1),X2) ),
% 11.28/1.99      inference(cnf_transformation,[],[f30]) ).
% 11.28/1.99  
% 11.28/1.99  cnf(c_170,plain,
% 11.28/1.99      ( ~ r1_tarski(X0_37,k2_xboole_0(X1_37,X2_37))
% 11.28/1.99      | r1_tarski(k6_subset_1(X0_37,X1_37),X2_37) ),
% 11.28/1.99      inference(subtyping,[status(esa)],[c_2]) ).
% 11.28/1.99  
% 11.28/1.99  cnf(c_317,plain,
% 11.28/1.99      ( r1_tarski(X0_37,k2_xboole_0(X1_37,X2_37)) != iProver_top
% 11.28/1.99      | r1_tarski(k6_subset_1(X0_37,X1_37),X2_37) = iProver_top ),
% 11.28/1.99      inference(predicate_to_equality,[status(thm)],[c_170]) ).
% 11.28/1.99  
% 11.28/1.99  cnf(c_25463,plain,
% 11.28/1.99      ( r1_tarski(X0_37,k1_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,X1_37)))) != iProver_top
% 11.28/1.99      | r1_tarski(k6_subset_1(X0_37,k1_relat_1(sK1)),k1_relat_1(k6_subset_1(sK0,X1_37))) = iProver_top ),
% 11.28/1.99      inference(superposition,[status(thm)],[c_24817,c_317]) ).
% 11.28/1.99  
% 11.28/1.99  cnf(c_7,negated_conjecture,
% 11.28/1.99      ( ~ r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k6_subset_1(sK0,sK1))) ),
% 11.28/1.99      inference(cnf_transformation,[],[f28]) ).
% 11.28/1.99  
% 11.28/1.99  cnf(c_167,negated_conjecture,
% 11.28/1.99      ( ~ r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k6_subset_1(sK0,sK1))) ),
% 11.28/1.99      inference(subtyping,[status(esa)],[c_7]) ).
% 11.28/1.99  
% 11.28/1.99  cnf(c_320,plain,
% 11.28/1.99      ( r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k6_subset_1(sK0,sK1))) != iProver_top ),
% 11.28/1.99      inference(predicate_to_equality,[status(thm)],[c_167]) ).
% 11.28/1.99  
% 11.28/1.99  cnf(c_42245,plain,
% 11.28/1.99      ( r1_tarski(k1_relat_1(sK0),k1_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,sK1)))) != iProver_top ),
% 11.28/1.99      inference(superposition,[status(thm)],[c_25463,c_320]) ).
% 11.28/1.99  
% 11.28/1.99  cnf(c_1,plain,
% 11.28/1.99      ( k2_xboole_0(X0,k6_subset_1(X1,X0)) = k2_xboole_0(X0,X1) ),
% 11.28/1.99      inference(cnf_transformation,[],[f29]) ).
% 11.28/1.99  
% 11.28/1.99  cnf(c_171,plain,
% 11.28/1.99      ( k2_xboole_0(X0_37,k6_subset_1(X1_37,X0_37)) = k2_xboole_0(X0_37,X1_37) ),
% 11.28/1.99      inference(subtyping,[status(esa)],[c_1]) ).
% 11.28/1.99  
% 11.28/1.99  cnf(c_1365,plain,
% 11.28/1.99      ( k2_xboole_0(k1_relat_1(sK1),k1_relat_1(sK0)) = k1_relat_1(k2_xboole_0(sK1,sK0)) ),
% 11.28/1.99      inference(superposition,[status(thm)],[c_322,c_1128]) ).
% 11.28/1.99  
% 11.28/1.99  cnf(c_0,plain,
% 11.28/1.99      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 11.28/1.99      inference(cnf_transformation,[],[f18]) ).
% 11.28/1.99  
% 11.28/1.99  cnf(c_172,plain,
% 11.28/1.99      ( k2_xboole_0(X0_37,X1_37) = k2_xboole_0(X1_37,X0_37) ),
% 11.28/1.99      inference(subtyping,[status(esa)],[c_0]) ).
% 11.28/1.99  
% 11.28/1.99  cnf(c_1485,plain,
% 11.28/1.99      ( k2_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) = k1_relat_1(k2_xboole_0(sK1,sK0)) ),
% 11.28/1.99      inference(superposition,[status(thm)],[c_1365,c_172]) ).
% 11.28/1.99  
% 11.28/1.99  cnf(c_1129,plain,
% 11.28/1.99      ( k2_xboole_0(k1_relat_1(sK0),k1_relat_1(X0_37)) = k1_relat_1(k2_xboole_0(sK0,X0_37))
% 11.28/1.99      | v1_relat_1(X0_37) != iProver_top ),
% 11.28/1.99      inference(superposition,[status(thm)],[c_322,c_319]) ).
% 11.28/1.99  
% 11.28/1.99  cnf(c_1502,plain,
% 11.28/1.99      ( k2_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) = k1_relat_1(k2_xboole_0(sK0,sK1)) ),
% 11.28/1.99      inference(superposition,[status(thm)],[c_321,c_1129]) ).
% 11.28/1.99  
% 11.28/1.99  cnf(c_1829,plain,
% 11.28/1.99      ( k1_relat_1(k2_xboole_0(sK0,sK1)) = k1_relat_1(k2_xboole_0(sK1,sK0)) ),
% 11.28/1.99      inference(light_normalisation,[status(thm)],[c_1485,c_1502]) ).
% 11.28/1.99  
% 11.28/1.99  cnf(c_42246,plain,
% 11.28/1.99      ( r1_tarski(k1_relat_1(sK0),k1_relat_1(k2_xboole_0(sK0,sK1))) != iProver_top ),
% 11.28/1.99      inference(demodulation,[status(thm)],[c_42245,c_171,c_1829]) ).
% 11.28/1.99  
% 11.28/1.99  cnf(c_3,plain,
% 11.28/1.99      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 11.28/1.99      inference(cnf_transformation,[],[f21]) ).
% 11.28/1.99  
% 11.28/1.99  cnf(c_169,plain,
% 11.28/1.99      ( r1_tarski(X0_37,k2_xboole_0(X0_37,X1_37)) ),
% 11.28/1.99      inference(subtyping,[status(esa)],[c_3]) ).
% 11.28/1.99  
% 11.28/1.99  cnf(c_318,plain,
% 11.28/1.99      ( r1_tarski(X0_37,k2_xboole_0(X0_37,X1_37)) = iProver_top ),
% 11.28/1.99      inference(predicate_to_equality,[status(thm)],[c_169]) ).
% 11.28/1.99  
% 11.28/1.99  cnf(c_1671,plain,
% 11.28/1.99      ( r1_tarski(k1_relat_1(sK0),k1_relat_1(k2_xboole_0(sK0,sK1))) = iProver_top ),
% 11.28/1.99      inference(superposition,[status(thm)],[c_1502,c_318]) ).
% 11.28/1.99  
% 11.28/1.99  cnf(contradiction,plain,
% 11.28/1.99      ( $false ),
% 11.28/1.99      inference(minisat,[status(thm)],[c_42246,c_1671]) ).
% 11.28/1.99  
% 11.28/1.99  
% 11.28/1.99  % SZS output end CNFRefutation for theBenchmark.p
% 11.28/1.99  
% 11.28/1.99  ------                               Statistics
% 11.28/1.99  
% 11.28/1.99  ------ General
% 11.28/1.99  
% 11.28/1.99  abstr_ref_over_cycles:                  0
% 11.28/1.99  abstr_ref_under_cycles:                 0
% 11.28/1.99  gc_basic_clause_elim:                   0
% 11.28/1.99  forced_gc_time:                         0
% 11.28/1.99  parsing_time:                           0.041
% 11.28/1.99  unif_index_cands_time:                  0.
% 11.28/1.99  unif_index_add_time:                    0.
% 11.28/1.99  orderings_time:                         0.
% 11.28/1.99  out_proof_time:                         0.009
% 11.28/1.99  total_time:                             1.268
% 11.28/1.99  num_of_symbols:                         42
% 11.28/1.99  num_of_terms:                           28405
% 11.28/1.99  
% 11.28/1.99  ------ Preprocessing
% 11.28/1.99  
% 11.28/1.99  num_of_splits:                          0
% 11.28/1.99  num_of_split_atoms:                     0
% 11.28/1.99  num_of_reused_defs:                     0
% 11.28/1.99  num_eq_ax_congr_red:                    3
% 11.28/1.99  num_of_sem_filtered_clauses:            1
% 11.28/1.99  num_of_subtypes:                        2
% 11.28/1.99  monotx_restored_types:                  0
% 11.28/1.99  sat_num_of_epr_types:                   0
% 11.28/1.99  sat_num_of_non_cyclic_types:            0
% 11.28/1.99  sat_guarded_non_collapsed_types:        0
% 11.28/1.99  num_pure_diseq_elim:                    0
% 11.28/1.99  simp_replaced_by:                       0
% 11.28/1.99  res_preprocessed:                       56
% 11.28/1.99  prep_upred:                             0
% 11.28/1.99  prep_unflattend:                        1
% 11.28/1.99  smt_new_axioms:                         0
% 11.28/1.99  pred_elim_cands:                        2
% 11.28/1.99  pred_elim:                              1
% 11.28/1.99  pred_elim_cl:                           1
% 11.28/1.99  pred_elim_cycles:                       3
% 11.28/1.99  merged_defs:                            0
% 11.28/1.99  merged_defs_ncl:                        0
% 11.28/1.99  bin_hyper_res:                          0
% 11.28/1.99  prep_cycles:                            4
% 11.28/1.99  pred_elim_time:                         0.001
% 11.28/1.99  splitting_time:                         0.
% 11.28/1.99  sem_filter_time:                        0.
% 11.28/1.99  monotx_time:                            0.
% 11.28/1.99  subtype_inf_time:                       0.
% 11.28/1.99  
% 11.28/1.99  ------ Problem properties
% 11.28/1.99  
% 11.28/1.99  clauses:                                9
% 11.28/1.99  conjectures:                            3
% 11.28/1.99  epr:                                    2
% 11.28/1.99  horn:                                   9
% 11.28/1.99  ground:                                 3
% 11.28/1.99  unary:                                  6
% 11.28/1.99  binary:                                 1
% 11.28/1.99  lits:                                   14
% 11.28/1.99  lits_eq:                                4
% 11.28/1.99  fd_pure:                                0
% 11.28/1.99  fd_pseudo:                              0
% 11.28/1.99  fd_cond:                                0
% 11.28/1.99  fd_pseudo_cond:                         0
% 11.28/1.99  ac_symbols:                             0
% 11.28/1.99  
% 11.28/1.99  ------ Propositional Solver
% 11.28/1.99  
% 11.28/1.99  prop_solver_calls:                      38
% 11.28/1.99  prop_fast_solver_calls:                 617
% 11.28/1.99  smt_solver_calls:                       0
% 11.28/1.99  smt_fast_solver_calls:                  0
% 11.28/1.99  prop_num_of_clauses:                    12061
% 11.28/1.99  prop_preprocess_simplified:             24674
% 11.28/1.99  prop_fo_subsumed:                       0
% 11.28/1.99  prop_solver_time:                       0.
% 11.28/1.99  smt_solver_time:                        0.
% 11.28/1.99  smt_fast_solver_time:                   0.
% 11.28/1.99  prop_fast_solver_time:                  0.
% 11.28/1.99  prop_unsat_core_time:                   0.001
% 11.28/1.99  
% 11.28/1.99  ------ QBF
% 11.28/1.99  
% 11.28/1.99  qbf_q_res:                              0
% 11.28/1.99  qbf_num_tautologies:                    0
% 11.28/1.99  qbf_prep_cycles:                        0
% 11.28/1.99  
% 11.28/1.99  ------ BMC1
% 11.28/1.99  
% 11.28/1.99  bmc1_current_bound:                     -1
% 11.28/1.99  bmc1_last_solved_bound:                 -1
% 11.28/1.99  bmc1_unsat_core_size:                   -1
% 11.28/1.99  bmc1_unsat_core_parents_size:           -1
% 11.28/1.99  bmc1_merge_next_fun:                    0
% 11.28/1.99  bmc1_unsat_core_clauses_time:           0.
% 11.28/1.99  
% 11.28/1.99  ------ Instantiation
% 11.28/1.99  
% 11.28/1.99  inst_num_of_clauses:                    3978
% 11.28/1.99  inst_num_in_passive:                    1233
% 11.28/1.99  inst_num_in_active:                     1721
% 11.28/1.99  inst_num_in_unprocessed:                1031
% 11.28/1.99  inst_num_of_loops:                      1840
% 11.28/1.99  inst_num_of_learning_restarts:          0
% 11.28/1.99  inst_num_moves_active_passive:          110
% 11.28/1.99  inst_lit_activity:                      0
% 11.28/1.99  inst_lit_activity_moves:                0
% 11.28/1.99  inst_num_tautologies:                   0
% 11.28/1.99  inst_num_prop_implied:                  0
% 11.28/1.99  inst_num_existing_simplified:           0
% 11.28/1.99  inst_num_eq_res_simplified:             0
% 11.28/1.99  inst_num_child_elim:                    0
% 11.28/1.99  inst_num_of_dismatching_blockings:      9165
% 11.28/1.99  inst_num_of_non_proper_insts:           10298
% 11.28/1.99  inst_num_of_duplicates:                 0
% 11.28/1.99  inst_inst_num_from_inst_to_res:         0
% 11.28/1.99  inst_dismatching_checking_time:         0.
% 11.28/1.99  
% 11.28/1.99  ------ Resolution
% 11.28/1.99  
% 11.28/1.99  res_num_of_clauses:                     0
% 11.28/1.99  res_num_in_passive:                     0
% 11.28/1.99  res_num_in_active:                      0
% 11.28/1.99  res_num_of_loops:                       60
% 11.28/1.99  res_forward_subset_subsumed:            1350
% 11.28/1.99  res_backward_subset_subsumed:           18
% 11.28/1.99  res_forward_subsumed:                   0
% 11.28/1.99  res_backward_subsumed:                  0
% 11.28/1.99  res_forward_subsumption_resolution:     0
% 11.28/1.99  res_backward_subsumption_resolution:    0
% 11.28/1.99  res_clause_to_clause_subsumption:       17078
% 11.28/1.99  res_orphan_elimination:                 0
% 11.28/1.99  res_tautology_del:                      764
% 11.28/1.99  res_num_eq_res_simplified:              0
% 11.28/1.99  res_num_sel_changes:                    0
% 11.28/1.99  res_moves_from_active_to_pass:          0
% 11.28/1.99  
% 11.28/1.99  ------ Superposition
% 11.28/1.99  
% 11.28/1.99  sup_time_total:                         0.
% 11.28/1.99  sup_time_generating:                    0.
% 11.28/1.99  sup_time_sim_full:                      0.
% 11.28/1.99  sup_time_sim_immed:                     0.
% 11.28/1.99  
% 11.28/1.99  sup_num_of_clauses:                     820
% 11.28/1.99  sup_num_in_active:                      363
% 11.28/1.99  sup_num_in_passive:                     457
% 11.28/1.99  sup_num_of_loops:                       366
% 11.28/1.99  sup_fw_superposition:                   642
% 11.28/1.99  sup_bw_superposition:                   503
% 11.28/1.99  sup_immediate_simplified:               31
% 11.28/1.99  sup_given_eliminated:                   0
% 11.28/1.99  comparisons_done:                       0
% 11.28/1.99  comparisons_avoided:                    0
% 11.28/1.99  
% 11.28/1.99  ------ Simplifications
% 11.28/1.99  
% 11.28/1.99  
% 11.28/1.99  sim_fw_subset_subsumed:                 0
% 11.28/1.99  sim_bw_subset_subsumed:                 0
% 11.28/1.99  sim_fw_subsumed:                        12
% 11.28/1.99  sim_bw_subsumed:                        2
% 11.28/1.99  sim_fw_subsumption_res:                 0
% 11.28/1.99  sim_bw_subsumption_res:                 0
% 11.28/1.99  sim_tautology_del:                      0
% 11.28/1.99  sim_eq_tautology_del:                   0
% 11.28/1.99  sim_eq_res_simp:                        0
% 11.28/1.99  sim_fw_demodulated:                     1
% 11.28/1.99  sim_bw_demodulated:                     2
% 11.28/1.99  sim_light_normalised:                   31
% 11.28/1.99  sim_joinable_taut:                      0
% 11.28/1.99  sim_joinable_simp:                      0
% 11.28/1.99  sim_ac_normalised:                      0
% 11.28/1.99  sim_smt_subsumption:                    0
% 11.28/1.99  
%------------------------------------------------------------------------------
