%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1290+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:02 EST 2020

% Result     : Timeout 58.80s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :   71 ( 138 expanded)
%              Number of clauses        :   28 (  36 expanded)
%              Number of leaves         :   13 (  39 expanded)
%              Depth                    :   15
%              Number of atoms          :  148 ( 300 expanded)
%              Number of equality atoms :   65 (  97 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f460,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7703,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f460])).

fof(f502,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7791,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f502])).

fof(f458,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7686,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f458])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6996,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f11346,plain,(
    ! [X0] : o_0_0_xboole_0 = k1_subset_1(X0) ),
    inference(definition_unfolding,[],[f7686,f6996])).

fof(f11347,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,o_0_0_xboole_0) ),
    inference(definition_unfolding,[],[f7791,f11346])).

fof(f11772,plain,(
    ! [X0] : k3_subset_1(X0,o_0_0_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f7703,f11347])).

fof(f2236,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => r1_tarski(X1,k9_setfam_1(k2_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2237,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => r1_tarski(X1,k9_setfam_1(k2_struct_0(X0))) ) ) ),
    inference(negated_conjecture,[],[f2236])).

fof(f5017,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X1,k9_setfam_1(k2_struct_0(X0)))
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2237])).

fof(f6987,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X1,k9_setfam_1(k2_struct_0(X0)))
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ~ r1_tarski(sK795,k9_setfam_1(k2_struct_0(X0)))
        & m1_subset_1(sK795,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f6986,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(X1,k9_setfam_1(k2_struct_0(X0)))
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(X1,k9_setfam_1(k2_struct_0(sK794)))
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK794)))) )
      & l1_struct_0(sK794) ) ),
    introduced(choice_axiom,[])).

fof(f6988,plain,
    ( ~ r1_tarski(sK795,k9_setfam_1(k2_struct_0(sK794)))
    & m1_subset_1(sK795,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK794))))
    & l1_struct_0(sK794) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK794,sK795])],[f5017,f6987,f6986])).

fof(f11331,plain,(
    l1_struct_0(sK794) ),
    inference(cnf_transformation,[],[f6988])).

fof(f1827,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k3_subset_1(u1_struct_0(X0),k1_struct_0(X0)) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f4342,plain,(
    ! [X0] :
      ( k3_subset_1(u1_struct_0(X0),k1_struct_0(X0)) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1827])).

fof(f10573,plain,(
    ! [X0] :
      ( k3_subset_1(u1_struct_0(X0),k1_struct_0(X0)) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4342])).

fof(f2144,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( k3_subset_1(u1_struct_0(X0),X1) = k3_subset_1(u1_struct_0(X0),X2)
               => X1 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f4898,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | k3_subset_1(u1_struct_0(X0),X1) != k3_subset_1(u1_struct_0(X0),X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2144])).

fof(f4899,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | k3_subset_1(u1_struct_0(X0),X1) != k3_subset_1(u1_struct_0(X0),X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f4898])).

fof(f11194,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | k3_subset_1(u1_struct_0(X0),X1) != k3_subset_1(u1_struct_0(X0),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4899])).

fof(f1559,axiom,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9937,plain,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    inference(cnf_transformation,[],[f1559])).

fof(f13416,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | k3_subset_1(u1_struct_0(X0),X1) != k3_subset_1(u1_struct_0(X0),X2)
      | ~ m1_subset_1(X2,k9_setfam_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f11194,f9937,f9937])).

fof(f1779,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f4273,plain,(
    ! [X0] :
      ( m1_subset_1(k1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1779])).

fof(f10496,plain,(
    ! [X0] :
      ( m1_subset_1(k1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4273])).

fof(f13090,plain,(
    ! [X0] :
      ( m1_subset_1(k1_struct_0(X0),k9_setfam_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f10496,f9937])).

fof(f1772,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k1_xboole_0 = k1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f4265,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1772])).

fof(f10473,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4265])).

fof(f13074,plain,(
    ! [X0] :
      ( o_0_0_xboole_0 = k1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f10473,f6996])).

fof(f11333,plain,(
    ~ r1_tarski(sK795,k9_setfam_1(k2_struct_0(sK794))) ),
    inference(cnf_transformation,[],[f6988])).

fof(f609,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5467,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f609])).

fof(f7958,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f5467])).

fof(f11935,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k9_setfam_1(X1)) ) ),
    inference(definition_unfolding,[],[f7958,f9937])).

fof(f11332,plain,(
    m1_subset_1(sK795,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK794)))) ),
    inference(cnf_transformation,[],[f6988])).

fof(f13521,plain,(
    m1_subset_1(sK795,k9_setfam_1(k9_setfam_1(u1_struct_0(sK794)))) ),
    inference(definition_unfolding,[],[f11332,f9937,f9937])).

cnf(c_701,plain,
    ( k3_subset_1(X0,o_0_0_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f11772])).

cnf(c_4316,negated_conjecture,
    ( l1_struct_0(sK794) ),
    inference(cnf_transformation,[],[f11331])).

cnf(c_125631,plain,
    ( l1_struct_0(sK794) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4316])).

cnf(c_3557,plain,
    ( ~ l1_struct_0(X0)
    | k3_subset_1(u1_struct_0(X0),k1_struct_0(X0)) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f10573])).

cnf(c_126255,plain,
    ( k3_subset_1(u1_struct_0(X0),k1_struct_0(X0)) = k2_struct_0(X0)
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3557])).

cnf(c_181123,plain,
    ( k3_subset_1(u1_struct_0(sK794),k1_struct_0(sK794)) = k2_struct_0(sK794) ),
    inference(superposition,[status(thm)],[c_125631,c_126255])).

cnf(c_4177,plain,
    ( ~ m1_subset_1(X0,k9_setfam_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k9_setfam_1(u1_struct_0(X1)))
    | ~ l1_struct_0(X1)
    | X2 = X0
    | k3_subset_1(u1_struct_0(X1),X2) != k3_subset_1(u1_struct_0(X1),X0) ),
    inference(cnf_transformation,[],[f13416])).

cnf(c_125759,plain,
    ( X0 = X1
    | k3_subset_1(u1_struct_0(X2),X0) != k3_subset_1(u1_struct_0(X2),X1)
    | m1_subset_1(X1,k9_setfam_1(u1_struct_0(X2))) != iProver_top
    | m1_subset_1(X0,k9_setfam_1(u1_struct_0(X2))) != iProver_top
    | l1_struct_0(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4177])).

cnf(c_181682,plain,
    ( k3_subset_1(u1_struct_0(sK794),X0) != k2_struct_0(sK794)
    | k1_struct_0(sK794) = X0
    | m1_subset_1(X0,k9_setfam_1(u1_struct_0(sK794))) != iProver_top
    | m1_subset_1(k1_struct_0(sK794),k9_setfam_1(u1_struct_0(sK794))) != iProver_top
    | l1_struct_0(sK794) != iProver_top ),
    inference(superposition,[status(thm)],[c_181123,c_125759])).

cnf(c_4317,plain,
    ( l1_struct_0(sK794) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4316])).

cnf(c_3480,plain,
    ( m1_subset_1(k1_struct_0(X0),k9_setfam_1(u1_struct_0(X0)))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f13090])).

cnf(c_166536,plain,
    ( m1_subset_1(k1_struct_0(sK794),k9_setfam_1(u1_struct_0(sK794)))
    | ~ l1_struct_0(sK794) ),
    inference(instantiation,[status(thm)],[c_3480])).

cnf(c_166537,plain,
    ( m1_subset_1(k1_struct_0(sK794),k9_setfam_1(u1_struct_0(sK794))) = iProver_top
    | l1_struct_0(sK794) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_166536])).

cnf(c_181789,plain,
    ( k3_subset_1(u1_struct_0(sK794),X0) != k2_struct_0(sK794)
    | k1_struct_0(sK794) = X0
    | m1_subset_1(X0,k9_setfam_1(u1_struct_0(sK794))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_181682,c_4317,c_166537])).

cnf(c_181798,plain,
    ( k1_struct_0(sK794) = o_0_0_xboole_0
    | k2_struct_0(sK794) != u1_struct_0(sK794)
    | m1_subset_1(o_0_0_xboole_0,k9_setfam_1(u1_struct_0(sK794))) != iProver_top ),
    inference(superposition,[status(thm)],[c_701,c_181789])).

cnf(c_3457,plain,
    ( ~ l1_struct_0(X0)
    | k1_struct_0(X0) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f13074])).

cnf(c_166417,plain,
    ( ~ l1_struct_0(sK794)
    | k1_struct_0(sK794) = o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3457])).

cnf(c_181808,plain,
    ( k1_struct_0(sK794) = o_0_0_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_181798,c_4316,c_166417])).

cnf(c_181812,plain,
    ( k3_subset_1(u1_struct_0(sK794),o_0_0_xboole_0) = k2_struct_0(sK794) ),
    inference(demodulation,[status(thm)],[c_181808,c_181123])).

cnf(c_181814,plain,
    ( k2_struct_0(sK794) = u1_struct_0(sK794) ),
    inference(demodulation,[status(thm)],[c_181812,c_701])).

cnf(c_4314,negated_conjecture,
    ( ~ r1_tarski(sK795,k9_setfam_1(k2_struct_0(sK794))) ),
    inference(cnf_transformation,[],[f11333])).

cnf(c_125633,plain,
    ( r1_tarski(sK795,k9_setfam_1(k2_struct_0(sK794))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4314])).

cnf(c_181918,plain,
    ( r1_tarski(sK795,k9_setfam_1(u1_struct_0(sK794))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_181814,c_125633])).

cnf(c_956,plain,
    ( ~ m1_subset_1(X0,k9_setfam_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f11935])).

cnf(c_4315,negated_conjecture,
    ( m1_subset_1(sK795,k9_setfam_1(k9_setfam_1(u1_struct_0(sK794)))) ),
    inference(cnf_transformation,[],[f13521])).

cnf(c_169028,plain,
    ( r1_tarski(sK795,k9_setfam_1(u1_struct_0(sK794))) ),
    inference(resolution,[status(thm)],[c_956,c_4315])).

cnf(c_169029,plain,
    ( r1_tarski(sK795,k9_setfam_1(u1_struct_0(sK794))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_169028])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_181918,c_169029])).

%------------------------------------------------------------------------------
