%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:16:09 EST 2020

% Result     : Theorem 47.45s
% Output     : CNFRefutation 47.45s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 215 expanded)
%              Number of clauses        :   54 (  85 expanded)
%              Number of leaves         :   13 (  49 expanded)
%              Depth                    :   16
%              Number of atoms          :  149 ( 440 expanded)
%              Number of equality atoms :   65 ( 129 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_tarski(X0),k3_tarski(X1)) = k3_tarski(k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(k3_tarski(X0),k3_tarski(X1)) = k3_tarski(k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f40,plain,(
    ! [X0,X1] : k3_tarski(k3_tarski(k2_tarski(X0,X1))) = k3_tarski(k2_tarski(k3_tarski(X0),k3_tarski(X1))) ),
    inference(definition_unfolding,[],[f28,f27,f27])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f36,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(definition_unfolding,[],[f23,f27,f27])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f39,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f26,f27])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f37,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X0,k4_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f24,f27,f27])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) ) ),
    inference(definition_unfolding,[],[f25,f27])).

fof(f11,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f13,plain,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2))) ) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2)))
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2)))
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ~ r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),sK2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,sK2)))
        & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2)))
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
   => ( ? [X2] :
          ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),X2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X2)))
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2)))
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f21,f20])).

fof(f34,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f22])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k3_tarski(X1) = k5_setfam_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k3_tarski(X1) = k5_setfam_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k3_tarski(X1) = k5_setfam_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f33,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f22])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f35,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))) ),
    inference(cnf_transformation,[],[f22])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_4,plain,
    ( k3_tarski(k2_tarski(k3_tarski(X0),k3_tarski(X1))) = k3_tarski(k3_tarski(k2_tarski(X0,X1))) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_122,plain,
    ( k3_tarski(k2_tarski(k3_tarski(X0_40),k3_tarski(X1_40))) = k3_tarski(k3_tarski(k2_tarski(X0_40,X1_40))) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_0,plain,
    ( k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_126,plain,
    ( k3_tarski(k2_tarski(X0_40,X1_40)) = k3_tarski(k2_tarski(X1_40,X0_40)) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_3,plain,
    ( r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_123,plain,
    ( r1_tarski(X0_40,k3_tarski(k2_tarski(X0_40,X1_40))) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_314,plain,
    ( r1_tarski(X0_40,k3_tarski(k2_tarski(X0_40,X1_40))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_123])).

cnf(c_519,plain,
    ( r1_tarski(X0_40,k3_tarski(k2_tarski(X1_40,X0_40))) = iProver_top ),
    inference(superposition,[status(thm)],[c_126,c_314])).

cnf(c_673,plain,
    ( r1_tarski(k3_tarski(X0_40),k3_tarski(k3_tarski(k2_tarski(X1_40,X0_40)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_122,c_519])).

cnf(c_1,plain,
    ( k3_tarski(k2_tarski(X0,k4_xboole_0(X1,X0))) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_125,plain,
    ( k3_tarski(k2_tarski(X0_40,k4_xboole_0(X1_40,X0_40))) = k3_tarski(k2_tarski(X0_40,X1_40)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,k3_tarski(k2_tarski(X1,X2)))
    | r1_tarski(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_124,plain,
    ( ~ r1_tarski(X0_40,k3_tarski(k2_tarski(X1_40,X2_40)))
    | r1_tarski(k4_xboole_0(X0_40,X1_40),X2_40) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_313,plain,
    ( r1_tarski(X0_40,k3_tarski(k2_tarski(X1_40,X2_40))) != iProver_top
    | r1_tarski(k4_xboole_0(X0_40,X1_40),X2_40) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_124])).

cnf(c_671,plain,
    ( r1_tarski(X0_40,k3_tarski(k3_tarski(k2_tarski(X1_40,X2_40)))) != iProver_top
    | r1_tarski(k4_xboole_0(X0_40,k3_tarski(X1_40)),k3_tarski(X2_40)) = iProver_top ),
    inference(superposition,[status(thm)],[c_122,c_313])).

cnf(c_7908,plain,
    ( r1_tarski(X0_40,k3_tarski(k3_tarski(k2_tarski(X1_40,X2_40)))) != iProver_top
    | r1_tarski(k4_xboole_0(X0_40,k3_tarski(X1_40)),k3_tarski(k4_xboole_0(X2_40,X1_40))) = iProver_top ),
    inference(superposition,[status(thm)],[c_125,c_671])).

cnf(c_10,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_116,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_320,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_116])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k5_setfam_1(X1,X0) = k3_tarski(X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_118,plain,
    ( ~ m1_subset_1(X0_40,k1_zfmisc_1(k1_zfmisc_1(X0_41)))
    | k5_setfam_1(X0_41,X0_40) = k3_tarski(X0_40) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_318,plain,
    ( k5_setfam_1(X0_41,X0_40) = k3_tarski(X0_40)
    | m1_subset_1(X0_40,k1_zfmisc_1(k1_zfmisc_1(X0_41))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_118])).

cnf(c_4220,plain,
    ( k5_setfam_1(u1_struct_0(sK0),sK2) = k3_tarski(sK2) ),
    inference(superposition,[status(thm)],[c_320,c_318])).

cnf(c_11,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_115,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_321,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_115])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_120,plain,
    ( ~ m1_subset_1(X0_40,k1_zfmisc_1(X0_41))
    | k7_subset_1(X0_41,X0_40,X1_40) = k4_xboole_0(X0_40,X1_40) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_316,plain,
    ( k7_subset_1(X0_41,X0_40,X1_40) = k4_xboole_0(X0_40,X1_40)
    | m1_subset_1(X0_40,k1_zfmisc_1(X0_41)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_120])).

cnf(c_2149,plain,
    ( k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X0_40) = k4_xboole_0(sK1,X0_40) ),
    inference(superposition,[status(thm)],[c_321,c_316])).

cnf(c_9,negated_conjecture,
    ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_117,negated_conjecture,
    ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_319,plain,
    ( r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_117])).

cnf(c_2776,plain,
    ( r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2149,c_319])).

cnf(c_4561,plain,
    ( r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4220,c_2776])).

cnf(c_4221,plain,
    ( k5_setfam_1(u1_struct_0(sK0),sK1) = k3_tarski(sK1) ),
    inference(superposition,[status(thm)],[c_321,c_318])).

cnf(c_4562,plain,
    ( r1_tarski(k7_subset_1(u1_struct_0(sK0),k3_tarski(sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4561,c_4221])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k7_subset_1(X1,X0,X2),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_121,plain,
    ( ~ m1_subset_1(X0_40,k1_zfmisc_1(X0_41))
    | m1_subset_1(k7_subset_1(X0_41,X0_40,X1_40),k1_zfmisc_1(X0_41)) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_315,plain,
    ( m1_subset_1(X0_40,k1_zfmisc_1(X0_41)) != iProver_top
    | m1_subset_1(k7_subset_1(X0_41,X0_40,X1_40),k1_zfmisc_1(X0_41)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_121])).

cnf(c_2778,plain,
    ( m1_subset_1(k4_xboole_0(sK1,X0_40),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2149,c_315])).

cnf(c_12,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2897,plain,
    ( m1_subset_1(k4_xboole_0(sK1,X0_40),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2778,c_12])).

cnf(c_4225,plain,
    ( k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,X0_40)) = k3_tarski(k4_xboole_0(sK1,X0_40)) ),
    inference(superposition,[status(thm)],[c_2897,c_318])).

cnf(c_4563,plain,
    ( r1_tarski(k7_subset_1(u1_struct_0(sK0),k3_tarski(sK1),k3_tarski(sK2)),k3_tarski(k4_xboole_0(sK1,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4562,c_4225])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | m1_subset_1(k5_setfam_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_119,plain,
    ( ~ m1_subset_1(X0_40,k1_zfmisc_1(k1_zfmisc_1(X0_41)))
    | m1_subset_1(k5_setfam_1(X0_41,X0_40),k1_zfmisc_1(X0_41)) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_317,plain,
    ( m1_subset_1(X0_40,k1_zfmisc_1(k1_zfmisc_1(X0_41))) != iProver_top
    | m1_subset_1(k5_setfam_1(X0_41,X0_40),k1_zfmisc_1(X0_41)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_119])).

cnf(c_4641,plain,
    ( m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4221,c_317])).

cnf(c_4816,plain,
    ( m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4641,c_12])).

cnf(c_4820,plain,
    ( k7_subset_1(u1_struct_0(sK0),k3_tarski(sK1),X0_40) = k4_xboole_0(k3_tarski(sK1),X0_40) ),
    inference(superposition,[status(thm)],[c_4816,c_316])).

cnf(c_5880,plain,
    ( r1_tarski(k4_xboole_0(k3_tarski(sK1),k3_tarski(sK2)),k3_tarski(k4_xboole_0(sK1,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4563,c_4820])).

cnf(c_165667,plain,
    ( r1_tarski(k3_tarski(sK1),k3_tarski(k3_tarski(k2_tarski(sK2,sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7908,c_5880])).

cnf(c_166992,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_673,c_165667])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n007.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:18:36 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  % Running in FOF mode
% 47.45/6.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 47.45/6.50  
% 47.45/6.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 47.45/6.50  
% 47.45/6.50  ------  iProver source info
% 47.45/6.50  
% 47.45/6.50  git: date: 2020-06-30 10:37:57 +0100
% 47.45/6.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 47.45/6.50  git: non_committed_changes: false
% 47.45/6.50  git: last_make_outside_of_git: false
% 47.45/6.50  
% 47.45/6.50  ------ 
% 47.45/6.50  
% 47.45/6.50  ------ Input Options
% 47.45/6.50  
% 47.45/6.50  --out_options                           all
% 47.45/6.50  --tptp_safe_out                         true
% 47.45/6.50  --problem_path                          ""
% 47.45/6.50  --include_path                          ""
% 47.45/6.50  --clausifier                            res/vclausify_rel
% 47.45/6.50  --clausifier_options                    ""
% 47.45/6.50  --stdin                                 false
% 47.45/6.50  --stats_out                             all
% 47.45/6.50  
% 47.45/6.50  ------ General Options
% 47.45/6.50  
% 47.45/6.50  --fof                                   false
% 47.45/6.50  --time_out_real                         305.
% 47.45/6.50  --time_out_virtual                      -1.
% 47.45/6.50  --symbol_type_check                     false
% 47.45/6.50  --clausify_out                          false
% 47.45/6.50  --sig_cnt_out                           false
% 47.45/6.50  --trig_cnt_out                          false
% 47.45/6.50  --trig_cnt_out_tolerance                1.
% 47.45/6.50  --trig_cnt_out_sk_spl                   false
% 47.45/6.50  --abstr_cl_out                          false
% 47.45/6.50  
% 47.45/6.50  ------ Global Options
% 47.45/6.50  
% 47.45/6.50  --schedule                              default
% 47.45/6.50  --add_important_lit                     false
% 47.45/6.50  --prop_solver_per_cl                    1000
% 47.45/6.50  --min_unsat_core                        false
% 47.45/6.50  --soft_assumptions                      false
% 47.45/6.50  --soft_lemma_size                       3
% 47.45/6.50  --prop_impl_unit_size                   0
% 47.45/6.50  --prop_impl_unit                        []
% 47.45/6.50  --share_sel_clauses                     true
% 47.45/6.50  --reset_solvers                         false
% 47.45/6.50  --bc_imp_inh                            [conj_cone]
% 47.45/6.50  --conj_cone_tolerance                   3.
% 47.45/6.50  --extra_neg_conj                        none
% 47.45/6.50  --large_theory_mode                     true
% 47.45/6.50  --prolific_symb_bound                   200
% 47.45/6.50  --lt_threshold                          2000
% 47.45/6.50  --clause_weak_htbl                      true
% 47.45/6.50  --gc_record_bc_elim                     false
% 47.45/6.50  
% 47.45/6.50  ------ Preprocessing Options
% 47.45/6.50  
% 47.45/6.50  --preprocessing_flag                    true
% 47.45/6.50  --time_out_prep_mult                    0.1
% 47.45/6.50  --splitting_mode                        input
% 47.45/6.50  --splitting_grd                         true
% 47.45/6.50  --splitting_cvd                         false
% 47.45/6.50  --splitting_cvd_svl                     false
% 47.45/6.50  --splitting_nvd                         32
% 47.45/6.50  --sub_typing                            true
% 47.45/6.50  --prep_gs_sim                           true
% 47.45/6.50  --prep_unflatten                        true
% 47.45/6.50  --prep_res_sim                          true
% 47.45/6.50  --prep_upred                            true
% 47.45/6.50  --prep_sem_filter                       exhaustive
% 47.45/6.50  --prep_sem_filter_out                   false
% 47.45/6.50  --pred_elim                             true
% 47.45/6.50  --res_sim_input                         true
% 47.45/6.50  --eq_ax_congr_red                       true
% 47.45/6.50  --pure_diseq_elim                       true
% 47.45/6.50  --brand_transform                       false
% 47.45/6.50  --non_eq_to_eq                          false
% 47.45/6.50  --prep_def_merge                        true
% 47.45/6.50  --prep_def_merge_prop_impl              false
% 47.45/6.50  --prep_def_merge_mbd                    true
% 47.45/6.50  --prep_def_merge_tr_red                 false
% 47.45/6.50  --prep_def_merge_tr_cl                  false
% 47.45/6.50  --smt_preprocessing                     true
% 47.45/6.50  --smt_ac_axioms                         fast
% 47.45/6.50  --preprocessed_out                      false
% 47.45/6.50  --preprocessed_stats                    false
% 47.45/6.50  
% 47.45/6.50  ------ Abstraction refinement Options
% 47.45/6.50  
% 47.45/6.50  --abstr_ref                             []
% 47.45/6.50  --abstr_ref_prep                        false
% 47.45/6.50  --abstr_ref_until_sat                   false
% 47.45/6.50  --abstr_ref_sig_restrict                funpre
% 47.45/6.50  --abstr_ref_af_restrict_to_split_sk     false
% 47.45/6.50  --abstr_ref_under                       []
% 47.45/6.50  
% 47.45/6.50  ------ SAT Options
% 47.45/6.50  
% 47.45/6.50  --sat_mode                              false
% 47.45/6.50  --sat_fm_restart_options                ""
% 47.45/6.50  --sat_gr_def                            false
% 47.45/6.50  --sat_epr_types                         true
% 47.45/6.50  --sat_non_cyclic_types                  false
% 47.45/6.50  --sat_finite_models                     false
% 47.45/6.50  --sat_fm_lemmas                         false
% 47.45/6.50  --sat_fm_prep                           false
% 47.45/6.50  --sat_fm_uc_incr                        true
% 47.45/6.50  --sat_out_model                         small
% 47.45/6.50  --sat_out_clauses                       false
% 47.45/6.50  
% 47.45/6.50  ------ QBF Options
% 47.45/6.50  
% 47.45/6.50  --qbf_mode                              false
% 47.45/6.50  --qbf_elim_univ                         false
% 47.45/6.50  --qbf_dom_inst                          none
% 47.45/6.50  --qbf_dom_pre_inst                      false
% 47.45/6.50  --qbf_sk_in                             false
% 47.45/6.50  --qbf_pred_elim                         true
% 47.45/6.50  --qbf_split                             512
% 47.45/6.50  
% 47.45/6.50  ------ BMC1 Options
% 47.45/6.50  
% 47.45/6.50  --bmc1_incremental                      false
% 47.45/6.50  --bmc1_axioms                           reachable_all
% 47.45/6.50  --bmc1_min_bound                        0
% 47.45/6.50  --bmc1_max_bound                        -1
% 47.45/6.50  --bmc1_max_bound_default                -1
% 47.45/6.50  --bmc1_symbol_reachability              true
% 47.45/6.50  --bmc1_property_lemmas                  false
% 47.45/6.50  --bmc1_k_induction                      false
% 47.45/6.50  --bmc1_non_equiv_states                 false
% 47.45/6.50  --bmc1_deadlock                         false
% 47.45/6.50  --bmc1_ucm                              false
% 47.45/6.50  --bmc1_add_unsat_core                   none
% 47.45/6.50  --bmc1_unsat_core_children              false
% 47.45/6.50  --bmc1_unsat_core_extrapolate_axioms    false
% 47.45/6.50  --bmc1_out_stat                         full
% 47.45/6.50  --bmc1_ground_init                      false
% 47.45/6.50  --bmc1_pre_inst_next_state              false
% 47.45/6.50  --bmc1_pre_inst_state                   false
% 47.45/6.50  --bmc1_pre_inst_reach_state             false
% 47.45/6.50  --bmc1_out_unsat_core                   false
% 47.45/6.50  --bmc1_aig_witness_out                  false
% 47.45/6.50  --bmc1_verbose                          false
% 47.45/6.50  --bmc1_dump_clauses_tptp                false
% 47.45/6.50  --bmc1_dump_unsat_core_tptp             false
% 47.45/6.50  --bmc1_dump_file                        -
% 47.45/6.50  --bmc1_ucm_expand_uc_limit              128
% 47.45/6.50  --bmc1_ucm_n_expand_iterations          6
% 47.45/6.50  --bmc1_ucm_extend_mode                  1
% 47.45/6.50  --bmc1_ucm_init_mode                    2
% 47.45/6.50  --bmc1_ucm_cone_mode                    none
% 47.45/6.50  --bmc1_ucm_reduced_relation_type        0
% 47.45/6.50  --bmc1_ucm_relax_model                  4
% 47.45/6.50  --bmc1_ucm_full_tr_after_sat            true
% 47.45/6.50  --bmc1_ucm_expand_neg_assumptions       false
% 47.45/6.50  --bmc1_ucm_layered_model                none
% 47.45/6.50  --bmc1_ucm_max_lemma_size               10
% 47.45/6.50  
% 47.45/6.50  ------ AIG Options
% 47.45/6.50  
% 47.45/6.50  --aig_mode                              false
% 47.45/6.50  
% 47.45/6.50  ------ Instantiation Options
% 47.45/6.50  
% 47.45/6.50  --instantiation_flag                    true
% 47.45/6.50  --inst_sos_flag                         true
% 47.45/6.50  --inst_sos_phase                        true
% 47.45/6.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 47.45/6.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 47.45/6.50  --inst_lit_sel_side                     num_symb
% 47.45/6.50  --inst_solver_per_active                1400
% 47.45/6.50  --inst_solver_calls_frac                1.
% 47.45/6.50  --inst_passive_queue_type               priority_queues
% 47.45/6.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 47.45/6.50  --inst_passive_queues_freq              [25;2]
% 47.45/6.50  --inst_dismatching                      true
% 47.45/6.50  --inst_eager_unprocessed_to_passive     true
% 47.45/6.50  --inst_prop_sim_given                   true
% 47.45/6.50  --inst_prop_sim_new                     false
% 47.45/6.50  --inst_subs_new                         false
% 47.45/6.50  --inst_eq_res_simp                      false
% 47.45/6.50  --inst_subs_given                       false
% 47.45/6.50  --inst_orphan_elimination               true
% 47.45/6.50  --inst_learning_loop_flag               true
% 47.45/6.50  --inst_learning_start                   3000
% 47.45/6.50  --inst_learning_factor                  2
% 47.45/6.50  --inst_start_prop_sim_after_learn       3
% 47.45/6.50  --inst_sel_renew                        solver
% 47.45/6.50  --inst_lit_activity_flag                true
% 47.45/6.50  --inst_restr_to_given                   false
% 47.45/6.50  --inst_activity_threshold               500
% 47.45/6.50  --inst_out_proof                        true
% 47.45/6.50  
% 47.45/6.50  ------ Resolution Options
% 47.45/6.50  
% 47.45/6.50  --resolution_flag                       true
% 47.45/6.50  --res_lit_sel                           adaptive
% 47.45/6.50  --res_lit_sel_side                      none
% 47.45/6.50  --res_ordering                          kbo
% 47.45/6.50  --res_to_prop_solver                    active
% 47.45/6.50  --res_prop_simpl_new                    false
% 47.45/6.50  --res_prop_simpl_given                  true
% 47.45/6.50  --res_passive_queue_type                priority_queues
% 47.45/6.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 47.45/6.50  --res_passive_queues_freq               [15;5]
% 47.45/6.50  --res_forward_subs                      full
% 47.45/6.50  --res_backward_subs                     full
% 47.45/6.50  --res_forward_subs_resolution           true
% 47.45/6.50  --res_backward_subs_resolution          true
% 47.45/6.50  --res_orphan_elimination                true
% 47.45/6.50  --res_time_limit                        2.
% 47.45/6.50  --res_out_proof                         true
% 47.45/6.50  
% 47.45/6.50  ------ Superposition Options
% 47.45/6.50  
% 47.45/6.50  --superposition_flag                    true
% 47.45/6.50  --sup_passive_queue_type                priority_queues
% 47.45/6.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 47.45/6.50  --sup_passive_queues_freq               [8;1;4]
% 47.45/6.50  --demod_completeness_check              fast
% 47.45/6.50  --demod_use_ground                      true
% 47.45/6.50  --sup_to_prop_solver                    passive
% 47.45/6.50  --sup_prop_simpl_new                    true
% 47.45/6.50  --sup_prop_simpl_given                  true
% 47.45/6.50  --sup_fun_splitting                     true
% 47.45/6.50  --sup_smt_interval                      50000
% 47.45/6.50  
% 47.45/6.50  ------ Superposition Simplification Setup
% 47.45/6.50  
% 47.45/6.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 47.45/6.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 47.45/6.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 47.45/6.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 47.45/6.50  --sup_full_triv                         [TrivRules;PropSubs]
% 47.45/6.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 47.45/6.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 47.45/6.50  --sup_immed_triv                        [TrivRules]
% 47.45/6.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 47.45/6.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 47.45/6.50  --sup_immed_bw_main                     []
% 47.45/6.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 47.45/6.50  --sup_input_triv                        [Unflattening;TrivRules]
% 47.45/6.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 47.45/6.50  --sup_input_bw                          []
% 47.45/6.50  
% 47.45/6.50  ------ Combination Options
% 47.45/6.50  
% 47.45/6.50  --comb_res_mult                         3
% 47.45/6.50  --comb_sup_mult                         2
% 47.45/6.50  --comb_inst_mult                        10
% 47.45/6.50  
% 47.45/6.50  ------ Debug Options
% 47.45/6.50  
% 47.45/6.50  --dbg_backtrace                         false
% 47.45/6.50  --dbg_dump_prop_clauses                 false
% 47.45/6.50  --dbg_dump_prop_clauses_file            -
% 47.45/6.50  --dbg_out_stat                          false
% 47.45/6.50  ------ Parsing...
% 47.45/6.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 47.45/6.50  
% 47.45/6.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 47.45/6.50  
% 47.45/6.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 47.45/6.50  
% 47.45/6.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 47.45/6.50  ------ Proving...
% 47.45/6.50  ------ Problem Properties 
% 47.45/6.50  
% 47.45/6.50  
% 47.45/6.50  clauses                                 12
% 47.45/6.50  conjectures                             3
% 47.45/6.50  EPR                                     0
% 47.45/6.50  Horn                                    12
% 47.45/6.50  unary                                   7
% 47.45/6.50  binary                                  5
% 47.45/6.50  lits                                    17
% 47.45/6.50  lits eq                                 5
% 47.45/6.50  fd_pure                                 0
% 47.45/6.50  fd_pseudo                               0
% 47.45/6.50  fd_cond                                 0
% 47.45/6.50  fd_pseudo_cond                          0
% 47.45/6.50  AC symbols                              0
% 47.45/6.50  
% 47.45/6.50  ------ Schedule dynamic 5 is on 
% 47.45/6.50  
% 47.45/6.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 47.45/6.50  
% 47.45/6.50  
% 47.45/6.50  ------ 
% 47.45/6.50  Current options:
% 47.45/6.50  ------ 
% 47.45/6.50  
% 47.45/6.50  ------ Input Options
% 47.45/6.50  
% 47.45/6.50  --out_options                           all
% 47.45/6.50  --tptp_safe_out                         true
% 47.45/6.50  --problem_path                          ""
% 47.45/6.50  --include_path                          ""
% 47.45/6.50  --clausifier                            res/vclausify_rel
% 47.45/6.50  --clausifier_options                    ""
% 47.45/6.50  --stdin                                 false
% 47.45/6.50  --stats_out                             all
% 47.45/6.50  
% 47.45/6.50  ------ General Options
% 47.45/6.50  
% 47.45/6.50  --fof                                   false
% 47.45/6.50  --time_out_real                         305.
% 47.45/6.50  --time_out_virtual                      -1.
% 47.45/6.50  --symbol_type_check                     false
% 47.45/6.50  --clausify_out                          false
% 47.45/6.50  --sig_cnt_out                           false
% 47.45/6.50  --trig_cnt_out                          false
% 47.45/6.50  --trig_cnt_out_tolerance                1.
% 47.45/6.50  --trig_cnt_out_sk_spl                   false
% 47.45/6.50  --abstr_cl_out                          false
% 47.45/6.50  
% 47.45/6.50  ------ Global Options
% 47.45/6.50  
% 47.45/6.50  --schedule                              default
% 47.45/6.50  --add_important_lit                     false
% 47.45/6.50  --prop_solver_per_cl                    1000
% 47.45/6.50  --min_unsat_core                        false
% 47.45/6.50  --soft_assumptions                      false
% 47.45/6.50  --soft_lemma_size                       3
% 47.45/6.50  --prop_impl_unit_size                   0
% 47.45/6.50  --prop_impl_unit                        []
% 47.45/6.50  --share_sel_clauses                     true
% 47.45/6.50  --reset_solvers                         false
% 47.45/6.50  --bc_imp_inh                            [conj_cone]
% 47.45/6.50  --conj_cone_tolerance                   3.
% 47.45/6.50  --extra_neg_conj                        none
% 47.45/6.50  --large_theory_mode                     true
% 47.45/6.50  --prolific_symb_bound                   200
% 47.45/6.50  --lt_threshold                          2000
% 47.45/6.50  --clause_weak_htbl                      true
% 47.45/6.50  --gc_record_bc_elim                     false
% 47.45/6.50  
% 47.45/6.50  ------ Preprocessing Options
% 47.45/6.50  
% 47.45/6.50  --preprocessing_flag                    true
% 47.45/6.50  --time_out_prep_mult                    0.1
% 47.45/6.50  --splitting_mode                        input
% 47.45/6.50  --splitting_grd                         true
% 47.45/6.50  --splitting_cvd                         false
% 47.45/6.50  --splitting_cvd_svl                     false
% 47.45/6.50  --splitting_nvd                         32
% 47.45/6.50  --sub_typing                            true
% 47.45/6.50  --prep_gs_sim                           true
% 47.45/6.50  --prep_unflatten                        true
% 47.45/6.50  --prep_res_sim                          true
% 47.45/6.50  --prep_upred                            true
% 47.45/6.50  --prep_sem_filter                       exhaustive
% 47.45/6.50  --prep_sem_filter_out                   false
% 47.45/6.50  --pred_elim                             true
% 47.45/6.50  --res_sim_input                         true
% 47.45/6.50  --eq_ax_congr_red                       true
% 47.45/6.50  --pure_diseq_elim                       true
% 47.45/6.50  --brand_transform                       false
% 47.45/6.50  --non_eq_to_eq                          false
% 47.45/6.50  --prep_def_merge                        true
% 47.45/6.50  --prep_def_merge_prop_impl              false
% 47.45/6.50  --prep_def_merge_mbd                    true
% 47.45/6.50  --prep_def_merge_tr_red                 false
% 47.45/6.50  --prep_def_merge_tr_cl                  false
% 47.45/6.50  --smt_preprocessing                     true
% 47.45/6.50  --smt_ac_axioms                         fast
% 47.45/6.50  --preprocessed_out                      false
% 47.45/6.50  --preprocessed_stats                    false
% 47.45/6.50  
% 47.45/6.50  ------ Abstraction refinement Options
% 47.45/6.50  
% 47.45/6.50  --abstr_ref                             []
% 47.45/6.50  --abstr_ref_prep                        false
% 47.45/6.50  --abstr_ref_until_sat                   false
% 47.45/6.50  --abstr_ref_sig_restrict                funpre
% 47.45/6.50  --abstr_ref_af_restrict_to_split_sk     false
% 47.45/6.50  --abstr_ref_under                       []
% 47.45/6.50  
% 47.45/6.50  ------ SAT Options
% 47.45/6.50  
% 47.45/6.50  --sat_mode                              false
% 47.45/6.50  --sat_fm_restart_options                ""
% 47.45/6.50  --sat_gr_def                            false
% 47.45/6.50  --sat_epr_types                         true
% 47.45/6.50  --sat_non_cyclic_types                  false
% 47.45/6.50  --sat_finite_models                     false
% 47.45/6.50  --sat_fm_lemmas                         false
% 47.45/6.50  --sat_fm_prep                           false
% 47.45/6.50  --sat_fm_uc_incr                        true
% 47.45/6.50  --sat_out_model                         small
% 47.45/6.50  --sat_out_clauses                       false
% 47.45/6.50  
% 47.45/6.50  ------ QBF Options
% 47.45/6.50  
% 47.45/6.50  --qbf_mode                              false
% 47.45/6.50  --qbf_elim_univ                         false
% 47.45/6.50  --qbf_dom_inst                          none
% 47.45/6.50  --qbf_dom_pre_inst                      false
% 47.45/6.50  --qbf_sk_in                             false
% 47.45/6.50  --qbf_pred_elim                         true
% 47.45/6.50  --qbf_split                             512
% 47.45/6.50  
% 47.45/6.50  ------ BMC1 Options
% 47.45/6.50  
% 47.45/6.50  --bmc1_incremental                      false
% 47.45/6.50  --bmc1_axioms                           reachable_all
% 47.45/6.50  --bmc1_min_bound                        0
% 47.45/6.50  --bmc1_max_bound                        -1
% 47.45/6.50  --bmc1_max_bound_default                -1
% 47.45/6.50  --bmc1_symbol_reachability              true
% 47.45/6.50  --bmc1_property_lemmas                  false
% 47.45/6.50  --bmc1_k_induction                      false
% 47.45/6.50  --bmc1_non_equiv_states                 false
% 47.45/6.50  --bmc1_deadlock                         false
% 47.45/6.50  --bmc1_ucm                              false
% 47.45/6.50  --bmc1_add_unsat_core                   none
% 47.45/6.50  --bmc1_unsat_core_children              false
% 47.45/6.50  --bmc1_unsat_core_extrapolate_axioms    false
% 47.45/6.50  --bmc1_out_stat                         full
% 47.45/6.50  --bmc1_ground_init                      false
% 47.45/6.50  --bmc1_pre_inst_next_state              false
% 47.45/6.50  --bmc1_pre_inst_state                   false
% 47.45/6.50  --bmc1_pre_inst_reach_state             false
% 47.45/6.50  --bmc1_out_unsat_core                   false
% 47.45/6.50  --bmc1_aig_witness_out                  false
% 47.45/6.50  --bmc1_verbose                          false
% 47.45/6.50  --bmc1_dump_clauses_tptp                false
% 47.45/6.50  --bmc1_dump_unsat_core_tptp             false
% 47.45/6.50  --bmc1_dump_file                        -
% 47.45/6.50  --bmc1_ucm_expand_uc_limit              128
% 47.45/6.50  --bmc1_ucm_n_expand_iterations          6
% 47.45/6.50  --bmc1_ucm_extend_mode                  1
% 47.45/6.50  --bmc1_ucm_init_mode                    2
% 47.45/6.50  --bmc1_ucm_cone_mode                    none
% 47.45/6.50  --bmc1_ucm_reduced_relation_type        0
% 47.45/6.50  --bmc1_ucm_relax_model                  4
% 47.45/6.50  --bmc1_ucm_full_tr_after_sat            true
% 47.45/6.50  --bmc1_ucm_expand_neg_assumptions       false
% 47.45/6.50  --bmc1_ucm_layered_model                none
% 47.45/6.50  --bmc1_ucm_max_lemma_size               10
% 47.45/6.50  
% 47.45/6.50  ------ AIG Options
% 47.45/6.50  
% 47.45/6.50  --aig_mode                              false
% 47.45/6.50  
% 47.45/6.50  ------ Instantiation Options
% 47.45/6.50  
% 47.45/6.50  --instantiation_flag                    true
% 47.45/6.50  --inst_sos_flag                         true
% 47.45/6.50  --inst_sos_phase                        true
% 47.45/6.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 47.45/6.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 47.45/6.50  --inst_lit_sel_side                     none
% 47.45/6.50  --inst_solver_per_active                1400
% 47.45/6.50  --inst_solver_calls_frac                1.
% 47.45/6.50  --inst_passive_queue_type               priority_queues
% 47.45/6.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 47.45/6.50  --inst_passive_queues_freq              [25;2]
% 47.45/6.50  --inst_dismatching                      true
% 47.45/6.50  --inst_eager_unprocessed_to_passive     true
% 47.45/6.50  --inst_prop_sim_given                   true
% 47.45/6.50  --inst_prop_sim_new                     false
% 47.45/6.50  --inst_subs_new                         false
% 47.45/6.50  --inst_eq_res_simp                      false
% 47.45/6.50  --inst_subs_given                       false
% 47.45/6.50  --inst_orphan_elimination               true
% 47.45/6.50  --inst_learning_loop_flag               true
% 47.45/6.50  --inst_learning_start                   3000
% 47.45/6.50  --inst_learning_factor                  2
% 47.45/6.50  --inst_start_prop_sim_after_learn       3
% 47.45/6.50  --inst_sel_renew                        solver
% 47.45/6.50  --inst_lit_activity_flag                true
% 47.45/6.50  --inst_restr_to_given                   false
% 47.45/6.50  --inst_activity_threshold               500
% 47.45/6.50  --inst_out_proof                        true
% 47.45/6.50  
% 47.45/6.50  ------ Resolution Options
% 47.45/6.50  
% 47.45/6.50  --resolution_flag                       false
% 47.45/6.50  --res_lit_sel                           adaptive
% 47.45/6.50  --res_lit_sel_side                      none
% 47.45/6.50  --res_ordering                          kbo
% 47.45/6.50  --res_to_prop_solver                    active
% 47.45/6.50  --res_prop_simpl_new                    false
% 47.45/6.50  --res_prop_simpl_given                  true
% 47.45/6.50  --res_passive_queue_type                priority_queues
% 47.45/6.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 47.45/6.50  --res_passive_queues_freq               [15;5]
% 47.45/6.50  --res_forward_subs                      full
% 47.45/6.50  --res_backward_subs                     full
% 47.45/6.50  --res_forward_subs_resolution           true
% 47.45/6.50  --res_backward_subs_resolution          true
% 47.45/6.50  --res_orphan_elimination                true
% 47.45/6.50  --res_time_limit                        2.
% 47.45/6.50  --res_out_proof                         true
% 47.45/6.50  
% 47.45/6.50  ------ Superposition Options
% 47.45/6.50  
% 47.45/6.50  --superposition_flag                    true
% 47.45/6.50  --sup_passive_queue_type                priority_queues
% 47.45/6.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 47.45/6.50  --sup_passive_queues_freq               [8;1;4]
% 47.45/6.50  --demod_completeness_check              fast
% 47.45/6.50  --demod_use_ground                      true
% 47.45/6.50  --sup_to_prop_solver                    passive
% 47.45/6.50  --sup_prop_simpl_new                    true
% 47.45/6.50  --sup_prop_simpl_given                  true
% 47.45/6.50  --sup_fun_splitting                     true
% 47.45/6.50  --sup_smt_interval                      50000
% 47.45/6.50  
% 47.45/6.50  ------ Superposition Simplification Setup
% 47.45/6.50  
% 47.45/6.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 47.45/6.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 47.45/6.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 47.45/6.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 47.45/6.50  --sup_full_triv                         [TrivRules;PropSubs]
% 47.45/6.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 47.45/6.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 47.45/6.50  --sup_immed_triv                        [TrivRules]
% 47.45/6.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 47.45/6.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 47.45/6.50  --sup_immed_bw_main                     []
% 47.45/6.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 47.45/6.50  --sup_input_triv                        [Unflattening;TrivRules]
% 47.45/6.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 47.45/6.50  --sup_input_bw                          []
% 47.45/6.50  
% 47.45/6.50  ------ Combination Options
% 47.45/6.50  
% 47.45/6.50  --comb_res_mult                         3
% 47.45/6.50  --comb_sup_mult                         2
% 47.45/6.50  --comb_inst_mult                        10
% 47.45/6.50  
% 47.45/6.50  ------ Debug Options
% 47.45/6.50  
% 47.45/6.50  --dbg_backtrace                         false
% 47.45/6.50  --dbg_dump_prop_clauses                 false
% 47.45/6.50  --dbg_dump_prop_clauses_file            -
% 47.45/6.50  --dbg_out_stat                          false
% 47.45/6.50  
% 47.45/6.50  
% 47.45/6.50  
% 47.45/6.50  
% 47.45/6.50  ------ Proving...
% 47.45/6.50  
% 47.45/6.50  
% 47.45/6.50  % SZS status Theorem for theBenchmark.p
% 47.45/6.50  
% 47.45/6.50   Resolution empty clause
% 47.45/6.50  
% 47.45/6.50  % SZS output start CNFRefutation for theBenchmark.p
% 47.45/6.50  
% 47.45/6.50  fof(f6,axiom,(
% 47.45/6.50    ! [X0,X1] : k2_xboole_0(k3_tarski(X0),k3_tarski(X1)) = k3_tarski(k2_xboole_0(X0,X1))),
% 47.45/6.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.45/6.50  
% 47.45/6.50  fof(f28,plain,(
% 47.45/6.50    ( ! [X0,X1] : (k2_xboole_0(k3_tarski(X0),k3_tarski(X1)) = k3_tarski(k2_xboole_0(X0,X1))) )),
% 47.45/6.50    inference(cnf_transformation,[],[f6])).
% 47.45/6.50  
% 47.45/6.50  fof(f5,axiom,(
% 47.45/6.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 47.45/6.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.45/6.50  
% 47.45/6.50  fof(f27,plain,(
% 47.45/6.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 47.45/6.50    inference(cnf_transformation,[],[f5])).
% 47.45/6.50  
% 47.45/6.50  fof(f40,plain,(
% 47.45/6.50    ( ! [X0,X1] : (k3_tarski(k3_tarski(k2_tarski(X0,X1))) = k3_tarski(k2_tarski(k3_tarski(X0),k3_tarski(X1)))) )),
% 47.45/6.50    inference(definition_unfolding,[],[f28,f27,f27])).
% 47.45/6.50  
% 47.45/6.50  fof(f1,axiom,(
% 47.45/6.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 47.45/6.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.45/6.50  
% 47.45/6.50  fof(f23,plain,(
% 47.45/6.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 47.45/6.50    inference(cnf_transformation,[],[f1])).
% 47.45/6.50  
% 47.45/6.50  fof(f36,plain,(
% 47.45/6.50    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X1,X0))) )),
% 47.45/6.50    inference(definition_unfolding,[],[f23,f27,f27])).
% 47.45/6.50  
% 47.45/6.50  fof(f4,axiom,(
% 47.45/6.50    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 47.45/6.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.45/6.50  
% 47.45/6.50  fof(f26,plain,(
% 47.45/6.50    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 47.45/6.50    inference(cnf_transformation,[],[f4])).
% 47.45/6.50  
% 47.45/6.50  fof(f39,plain,(
% 47.45/6.50    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) )),
% 47.45/6.50    inference(definition_unfolding,[],[f26,f27])).
% 47.45/6.50  
% 47.45/6.50  fof(f2,axiom,(
% 47.45/6.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 47.45/6.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.45/6.50  
% 47.45/6.50  fof(f24,plain,(
% 47.45/6.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 47.45/6.50    inference(cnf_transformation,[],[f2])).
% 47.45/6.50  
% 47.45/6.50  fof(f37,plain,(
% 47.45/6.50    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X0,k4_xboole_0(X1,X0)))) )),
% 47.45/6.50    inference(definition_unfolding,[],[f24,f27,f27])).
% 47.45/6.50  
% 47.45/6.50  fof(f3,axiom,(
% 47.45/6.50    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 47.45/6.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.45/6.50  
% 47.45/6.50  fof(f14,plain,(
% 47.45/6.50    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 47.45/6.50    inference(ennf_transformation,[],[f3])).
% 47.45/6.50  
% 47.45/6.50  fof(f25,plain,(
% 47.45/6.50    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 47.45/6.50    inference(cnf_transformation,[],[f14])).
% 47.45/6.50  
% 47.45/6.50  fof(f38,plain,(
% 47.45/6.50    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k3_tarski(k2_tarski(X1,X2)))) )),
% 47.45/6.50    inference(definition_unfolding,[],[f25,f27])).
% 47.45/6.50  
% 47.45/6.50  fof(f11,conjecture,(
% 47.45/6.50    ! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2))))))),
% 47.45/6.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.45/6.50  
% 47.45/6.50  fof(f12,negated_conjecture,(
% 47.45/6.50    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2))))))),
% 47.45/6.50    inference(negated_conjecture,[],[f11])).
% 47.45/6.50  
% 47.45/6.50  fof(f13,plain,(
% 47.45/6.50    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2)))))),
% 47.45/6.50    inference(pure_predicate_removal,[],[f12])).
% 47.45/6.50  
% 47.45/6.50  fof(f19,plain,(
% 47.45/6.50    ? [X0,X1] : (? [X2] : (~r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 47.45/6.50    inference(ennf_transformation,[],[f13])).
% 47.45/6.50  
% 47.45/6.50  fof(f21,plain,(
% 47.45/6.50    ( ! [X0,X1] : (? [X2] : (~r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (~r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),sK2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))) )),
% 47.45/6.50    introduced(choice_axiom,[])).
% 47.45/6.50  
% 47.45/6.50  fof(f20,plain,(
% 47.45/6.50    ? [X0,X1] : (? [X2] : (~r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (? [X2] : (~r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),X2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X2))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 47.45/6.50    introduced(choice_axiom,[])).
% 47.45/6.50  
% 47.45/6.50  fof(f22,plain,(
% 47.45/6.50    (~r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 47.45/6.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f21,f20])).
% 47.45/6.50  
% 47.45/6.50  fof(f34,plain,(
% 47.45/6.50    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 47.45/6.50    inference(cnf_transformation,[],[f22])).
% 47.45/6.50  
% 47.45/6.50  fof(f10,axiom,(
% 47.45/6.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k3_tarski(X1) = k5_setfam_1(X0,X1))),
% 47.45/6.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.45/6.50  
% 47.45/6.50  fof(f18,plain,(
% 47.45/6.50    ! [X0,X1] : (k3_tarski(X1) = k5_setfam_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 47.45/6.50    inference(ennf_transformation,[],[f10])).
% 47.45/6.50  
% 47.45/6.50  fof(f32,plain,(
% 47.45/6.50    ( ! [X0,X1] : (k3_tarski(X1) = k5_setfam_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 47.45/6.50    inference(cnf_transformation,[],[f18])).
% 47.45/6.50  
% 47.45/6.50  fof(f33,plain,(
% 47.45/6.50    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 47.45/6.50    inference(cnf_transformation,[],[f22])).
% 47.45/6.50  
% 47.45/6.50  fof(f8,axiom,(
% 47.45/6.50    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 47.45/6.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.45/6.50  
% 47.45/6.50  fof(f16,plain,(
% 47.45/6.50    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 47.45/6.50    inference(ennf_transformation,[],[f8])).
% 47.45/6.50  
% 47.45/6.50  fof(f30,plain,(
% 47.45/6.50    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 47.45/6.50    inference(cnf_transformation,[],[f16])).
% 47.45/6.50  
% 47.45/6.50  fof(f35,plain,(
% 47.45/6.50    ~r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2)))),
% 47.45/6.50    inference(cnf_transformation,[],[f22])).
% 47.45/6.50  
% 47.45/6.50  fof(f7,axiom,(
% 47.45/6.50    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 47.45/6.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.45/6.50  
% 47.45/6.50  fof(f15,plain,(
% 47.45/6.50    ! [X0,X1,X2] : (m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 47.45/6.50    inference(ennf_transformation,[],[f7])).
% 47.45/6.50  
% 47.45/6.50  fof(f29,plain,(
% 47.45/6.50    ( ! [X2,X0,X1] : (m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 47.45/6.50    inference(cnf_transformation,[],[f15])).
% 47.45/6.50  
% 47.45/6.50  fof(f9,axiom,(
% 47.45/6.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)))),
% 47.45/6.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.45/6.50  
% 47.45/6.50  fof(f17,plain,(
% 47.45/6.50    ! [X0,X1] : (m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 47.45/6.50    inference(ennf_transformation,[],[f9])).
% 47.45/6.50  
% 47.45/6.50  fof(f31,plain,(
% 47.45/6.50    ( ! [X0,X1] : (m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 47.45/6.50    inference(cnf_transformation,[],[f17])).
% 47.45/6.50  
% 47.45/6.50  cnf(c_4,plain,
% 47.45/6.50      ( k3_tarski(k2_tarski(k3_tarski(X0),k3_tarski(X1))) = k3_tarski(k3_tarski(k2_tarski(X0,X1))) ),
% 47.45/6.50      inference(cnf_transformation,[],[f40]) ).
% 47.45/6.50  
% 47.45/6.50  cnf(c_122,plain,
% 47.45/6.50      ( k3_tarski(k2_tarski(k3_tarski(X0_40),k3_tarski(X1_40))) = k3_tarski(k3_tarski(k2_tarski(X0_40,X1_40))) ),
% 47.45/6.50      inference(subtyping,[status(esa)],[c_4]) ).
% 47.45/6.50  
% 47.45/6.50  cnf(c_0,plain,
% 47.45/6.50      ( k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X1,X0)) ),
% 47.45/6.50      inference(cnf_transformation,[],[f36]) ).
% 47.45/6.50  
% 47.45/6.50  cnf(c_126,plain,
% 47.45/6.50      ( k3_tarski(k2_tarski(X0_40,X1_40)) = k3_tarski(k2_tarski(X1_40,X0_40)) ),
% 47.45/6.50      inference(subtyping,[status(esa)],[c_0]) ).
% 47.45/6.50  
% 47.45/6.50  cnf(c_3,plain,
% 47.45/6.50      ( r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) ),
% 47.45/6.50      inference(cnf_transformation,[],[f39]) ).
% 47.45/6.50  
% 47.45/6.50  cnf(c_123,plain,
% 47.45/6.50      ( r1_tarski(X0_40,k3_tarski(k2_tarski(X0_40,X1_40))) ),
% 47.45/6.50      inference(subtyping,[status(esa)],[c_3]) ).
% 47.45/6.50  
% 47.45/6.50  cnf(c_314,plain,
% 47.45/6.50      ( r1_tarski(X0_40,k3_tarski(k2_tarski(X0_40,X1_40))) = iProver_top ),
% 47.45/6.50      inference(predicate_to_equality,[status(thm)],[c_123]) ).
% 47.45/6.50  
% 47.45/6.50  cnf(c_519,plain,
% 47.45/6.50      ( r1_tarski(X0_40,k3_tarski(k2_tarski(X1_40,X0_40))) = iProver_top ),
% 47.45/6.50      inference(superposition,[status(thm)],[c_126,c_314]) ).
% 47.45/6.50  
% 47.45/6.50  cnf(c_673,plain,
% 47.45/6.50      ( r1_tarski(k3_tarski(X0_40),k3_tarski(k3_tarski(k2_tarski(X1_40,X0_40)))) = iProver_top ),
% 47.45/6.50      inference(superposition,[status(thm)],[c_122,c_519]) ).
% 47.45/6.50  
% 47.45/6.50  cnf(c_1,plain,
% 47.45/6.50      ( k3_tarski(k2_tarski(X0,k4_xboole_0(X1,X0))) = k3_tarski(k2_tarski(X0,X1)) ),
% 47.45/6.50      inference(cnf_transformation,[],[f37]) ).
% 47.45/6.50  
% 47.45/6.50  cnf(c_125,plain,
% 47.45/6.50      ( k3_tarski(k2_tarski(X0_40,k4_xboole_0(X1_40,X0_40))) = k3_tarski(k2_tarski(X0_40,X1_40)) ),
% 47.45/6.50      inference(subtyping,[status(esa)],[c_1]) ).
% 47.45/6.50  
% 47.45/6.50  cnf(c_2,plain,
% 47.45/6.50      ( ~ r1_tarski(X0,k3_tarski(k2_tarski(X1,X2)))
% 47.45/6.50      | r1_tarski(k4_xboole_0(X0,X1),X2) ),
% 47.45/6.50      inference(cnf_transformation,[],[f38]) ).
% 47.45/6.50  
% 47.45/6.50  cnf(c_124,plain,
% 47.45/6.50      ( ~ r1_tarski(X0_40,k3_tarski(k2_tarski(X1_40,X2_40)))
% 47.45/6.50      | r1_tarski(k4_xboole_0(X0_40,X1_40),X2_40) ),
% 47.45/6.50      inference(subtyping,[status(esa)],[c_2]) ).
% 47.45/6.50  
% 47.45/6.50  cnf(c_313,plain,
% 47.45/6.50      ( r1_tarski(X0_40,k3_tarski(k2_tarski(X1_40,X2_40))) != iProver_top
% 47.45/6.50      | r1_tarski(k4_xboole_0(X0_40,X1_40),X2_40) = iProver_top ),
% 47.45/6.50      inference(predicate_to_equality,[status(thm)],[c_124]) ).
% 47.45/6.50  
% 47.45/6.50  cnf(c_671,plain,
% 47.45/6.50      ( r1_tarski(X0_40,k3_tarski(k3_tarski(k2_tarski(X1_40,X2_40)))) != iProver_top
% 47.45/6.50      | r1_tarski(k4_xboole_0(X0_40,k3_tarski(X1_40)),k3_tarski(X2_40)) = iProver_top ),
% 47.45/6.50      inference(superposition,[status(thm)],[c_122,c_313]) ).
% 47.45/6.50  
% 47.45/6.50  cnf(c_7908,plain,
% 47.45/6.50      ( r1_tarski(X0_40,k3_tarski(k3_tarski(k2_tarski(X1_40,X2_40)))) != iProver_top
% 47.45/6.50      | r1_tarski(k4_xboole_0(X0_40,k3_tarski(X1_40)),k3_tarski(k4_xboole_0(X2_40,X1_40))) = iProver_top ),
% 47.45/6.50      inference(superposition,[status(thm)],[c_125,c_671]) ).
% 47.45/6.50  
% 47.45/6.50  cnf(c_10,negated_conjecture,
% 47.45/6.50      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
% 47.45/6.50      inference(cnf_transformation,[],[f34]) ).
% 47.45/6.50  
% 47.45/6.50  cnf(c_116,negated_conjecture,
% 47.45/6.50      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
% 47.45/6.50      inference(subtyping,[status(esa)],[c_10]) ).
% 47.45/6.50  
% 47.45/6.50  cnf(c_320,plain,
% 47.45/6.50      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
% 47.45/6.50      inference(predicate_to_equality,[status(thm)],[c_116]) ).
% 47.45/6.50  
% 47.45/6.50  cnf(c_8,plain,
% 47.45/6.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 47.45/6.50      | k5_setfam_1(X1,X0) = k3_tarski(X0) ),
% 47.45/6.50      inference(cnf_transformation,[],[f32]) ).
% 47.45/6.50  
% 47.45/6.50  cnf(c_118,plain,
% 47.45/6.50      ( ~ m1_subset_1(X0_40,k1_zfmisc_1(k1_zfmisc_1(X0_41)))
% 47.45/6.50      | k5_setfam_1(X0_41,X0_40) = k3_tarski(X0_40) ),
% 47.45/6.50      inference(subtyping,[status(esa)],[c_8]) ).
% 47.45/6.50  
% 47.45/6.50  cnf(c_318,plain,
% 47.45/6.50      ( k5_setfam_1(X0_41,X0_40) = k3_tarski(X0_40)
% 47.45/6.50      | m1_subset_1(X0_40,k1_zfmisc_1(k1_zfmisc_1(X0_41))) != iProver_top ),
% 47.45/6.50      inference(predicate_to_equality,[status(thm)],[c_118]) ).
% 47.45/6.50  
% 47.45/6.50  cnf(c_4220,plain,
% 47.45/6.50      ( k5_setfam_1(u1_struct_0(sK0),sK2) = k3_tarski(sK2) ),
% 47.45/6.50      inference(superposition,[status(thm)],[c_320,c_318]) ).
% 47.45/6.50  
% 47.45/6.50  cnf(c_11,negated_conjecture,
% 47.45/6.50      ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
% 47.45/6.50      inference(cnf_transformation,[],[f33]) ).
% 47.45/6.50  
% 47.45/6.50  cnf(c_115,negated_conjecture,
% 47.45/6.50      ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
% 47.45/6.50      inference(subtyping,[status(esa)],[c_11]) ).
% 47.45/6.50  
% 47.45/6.50  cnf(c_321,plain,
% 47.45/6.50      ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
% 47.45/6.50      inference(predicate_to_equality,[status(thm)],[c_115]) ).
% 47.45/6.50  
% 47.45/6.50  cnf(c_6,plain,
% 47.45/6.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 47.45/6.50      | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 47.45/6.50      inference(cnf_transformation,[],[f30]) ).
% 47.45/6.50  
% 47.45/6.50  cnf(c_120,plain,
% 47.45/6.50      ( ~ m1_subset_1(X0_40,k1_zfmisc_1(X0_41))
% 47.45/6.50      | k7_subset_1(X0_41,X0_40,X1_40) = k4_xboole_0(X0_40,X1_40) ),
% 47.45/6.50      inference(subtyping,[status(esa)],[c_6]) ).
% 47.45/6.50  
% 47.45/6.50  cnf(c_316,plain,
% 47.45/6.50      ( k7_subset_1(X0_41,X0_40,X1_40) = k4_xboole_0(X0_40,X1_40)
% 47.45/6.50      | m1_subset_1(X0_40,k1_zfmisc_1(X0_41)) != iProver_top ),
% 47.45/6.50      inference(predicate_to_equality,[status(thm)],[c_120]) ).
% 47.45/6.50  
% 47.45/6.50  cnf(c_2149,plain,
% 47.45/6.50      ( k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X0_40) = k4_xboole_0(sK1,X0_40) ),
% 47.45/6.50      inference(superposition,[status(thm)],[c_321,c_316]) ).
% 47.45/6.50  
% 47.45/6.50  cnf(c_9,negated_conjecture,
% 47.45/6.50      ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))) ),
% 47.45/6.50      inference(cnf_transformation,[],[f35]) ).
% 47.45/6.50  
% 47.45/6.50  cnf(c_117,negated_conjecture,
% 47.45/6.50      ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))) ),
% 47.45/6.50      inference(subtyping,[status(esa)],[c_9]) ).
% 47.45/6.50  
% 47.45/6.50  cnf(c_319,plain,
% 47.45/6.50      ( r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))) != iProver_top ),
% 47.45/6.50      inference(predicate_to_equality,[status(thm)],[c_117]) ).
% 47.45/6.50  
% 47.45/6.50  cnf(c_2776,plain,
% 47.45/6.50      ( r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2))) != iProver_top ),
% 47.45/6.50      inference(demodulation,[status(thm)],[c_2149,c_319]) ).
% 47.45/6.50  
% 47.45/6.50  cnf(c_4561,plain,
% 47.45/6.50      ( r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2))) != iProver_top ),
% 47.45/6.50      inference(demodulation,[status(thm)],[c_4220,c_2776]) ).
% 47.45/6.50  
% 47.45/6.50  cnf(c_4221,plain,
% 47.45/6.50      ( k5_setfam_1(u1_struct_0(sK0),sK1) = k3_tarski(sK1) ),
% 47.45/6.50      inference(superposition,[status(thm)],[c_321,c_318]) ).
% 47.45/6.50  
% 47.45/6.50  cnf(c_4562,plain,
% 47.45/6.50      ( r1_tarski(k7_subset_1(u1_struct_0(sK0),k3_tarski(sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2))) != iProver_top ),
% 47.45/6.50      inference(light_normalisation,[status(thm)],[c_4561,c_4221]) ).
% 47.45/6.50  
% 47.45/6.50  cnf(c_5,plain,
% 47.45/6.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 47.45/6.50      | m1_subset_1(k7_subset_1(X1,X0,X2),k1_zfmisc_1(X1)) ),
% 47.45/6.50      inference(cnf_transformation,[],[f29]) ).
% 47.45/6.50  
% 47.45/6.50  cnf(c_121,plain,
% 47.45/6.50      ( ~ m1_subset_1(X0_40,k1_zfmisc_1(X0_41))
% 47.45/6.50      | m1_subset_1(k7_subset_1(X0_41,X0_40,X1_40),k1_zfmisc_1(X0_41)) ),
% 47.45/6.50      inference(subtyping,[status(esa)],[c_5]) ).
% 47.45/6.50  
% 47.45/6.50  cnf(c_315,plain,
% 47.45/6.50      ( m1_subset_1(X0_40,k1_zfmisc_1(X0_41)) != iProver_top
% 47.45/6.50      | m1_subset_1(k7_subset_1(X0_41,X0_40,X1_40),k1_zfmisc_1(X0_41)) = iProver_top ),
% 47.45/6.50      inference(predicate_to_equality,[status(thm)],[c_121]) ).
% 47.45/6.50  
% 47.45/6.50  cnf(c_2778,plain,
% 47.45/6.50      ( m1_subset_1(k4_xboole_0(sK1,X0_40),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
% 47.45/6.50      | m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
% 47.45/6.50      inference(superposition,[status(thm)],[c_2149,c_315]) ).
% 47.45/6.50  
% 47.45/6.50  cnf(c_12,plain,
% 47.45/6.50      ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
% 47.45/6.50      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 47.45/6.50  
% 47.45/6.50  cnf(c_2897,plain,
% 47.45/6.50      ( m1_subset_1(k4_xboole_0(sK1,X0_40),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
% 47.45/6.50      inference(global_propositional_subsumption,[status(thm)],[c_2778,c_12]) ).
% 47.45/6.50  
% 47.45/6.50  cnf(c_4225,plain,
% 47.45/6.50      ( k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,X0_40)) = k3_tarski(k4_xboole_0(sK1,X0_40)) ),
% 47.45/6.50      inference(superposition,[status(thm)],[c_2897,c_318]) ).
% 47.45/6.50  
% 47.45/6.50  cnf(c_4563,plain,
% 47.45/6.50      ( r1_tarski(k7_subset_1(u1_struct_0(sK0),k3_tarski(sK1),k3_tarski(sK2)),k3_tarski(k4_xboole_0(sK1,sK2))) != iProver_top ),
% 47.45/6.50      inference(demodulation,[status(thm)],[c_4562,c_4225]) ).
% 47.45/6.50  
% 47.45/6.50  cnf(c_7,plain,
% 47.45/6.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 47.45/6.50      | m1_subset_1(k5_setfam_1(X1,X0),k1_zfmisc_1(X1)) ),
% 47.45/6.50      inference(cnf_transformation,[],[f31]) ).
% 47.45/6.50  
% 47.45/6.50  cnf(c_119,plain,
% 47.45/6.50      ( ~ m1_subset_1(X0_40,k1_zfmisc_1(k1_zfmisc_1(X0_41)))
% 47.45/6.50      | m1_subset_1(k5_setfam_1(X0_41,X0_40),k1_zfmisc_1(X0_41)) ),
% 47.45/6.50      inference(subtyping,[status(esa)],[c_7]) ).
% 47.45/6.50  
% 47.45/6.50  cnf(c_317,plain,
% 47.45/6.50      ( m1_subset_1(X0_40,k1_zfmisc_1(k1_zfmisc_1(X0_41))) != iProver_top
% 47.45/6.50      | m1_subset_1(k5_setfam_1(X0_41,X0_40),k1_zfmisc_1(X0_41)) = iProver_top ),
% 47.45/6.50      inference(predicate_to_equality,[status(thm)],[c_119]) ).
% 47.45/6.50  
% 47.45/6.50  cnf(c_4641,plain,
% 47.45/6.50      ( m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 47.45/6.50      | m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
% 47.45/6.50      inference(superposition,[status(thm)],[c_4221,c_317]) ).
% 47.45/6.50  
% 47.45/6.50  cnf(c_4816,plain,
% 47.45/6.50      ( m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 47.45/6.50      inference(global_propositional_subsumption,[status(thm)],[c_4641,c_12]) ).
% 47.45/6.50  
% 47.45/6.50  cnf(c_4820,plain,
% 47.45/6.50      ( k7_subset_1(u1_struct_0(sK0),k3_tarski(sK1),X0_40) = k4_xboole_0(k3_tarski(sK1),X0_40) ),
% 47.45/6.50      inference(superposition,[status(thm)],[c_4816,c_316]) ).
% 47.45/6.50  
% 47.45/6.50  cnf(c_5880,plain,
% 47.45/6.50      ( r1_tarski(k4_xboole_0(k3_tarski(sK1),k3_tarski(sK2)),k3_tarski(k4_xboole_0(sK1,sK2))) != iProver_top ),
% 47.45/6.50      inference(demodulation,[status(thm)],[c_4563,c_4820]) ).
% 47.45/6.50  
% 47.45/6.50  cnf(c_165667,plain,
% 47.45/6.50      ( r1_tarski(k3_tarski(sK1),k3_tarski(k3_tarski(k2_tarski(sK2,sK1)))) != iProver_top ),
% 47.45/6.50      inference(superposition,[status(thm)],[c_7908,c_5880]) ).
% 47.45/6.50  
% 47.45/6.50  cnf(c_166992,plain,
% 47.45/6.50      ( $false ),
% 47.45/6.50      inference(superposition,[status(thm)],[c_673,c_165667]) ).
% 47.45/6.50  
% 47.45/6.50  
% 47.45/6.50  % SZS output end CNFRefutation for theBenchmark.p
% 47.45/6.50  
% 47.45/6.50  ------                               Statistics
% 47.45/6.50  
% 47.45/6.50  ------ General
% 47.45/6.50  
% 47.45/6.50  abstr_ref_over_cycles:                  0
% 47.45/6.50  abstr_ref_under_cycles:                 0
% 47.45/6.50  gc_basic_clause_elim:                   0
% 47.45/6.50  forced_gc_time:                         0
% 47.45/6.50  parsing_time:                           0.013
% 47.45/6.50  unif_index_cands_time:                  0.
% 47.45/6.50  unif_index_add_time:                    0.
% 47.45/6.50  orderings_time:                         0.
% 47.45/6.50  out_proof_time:                         0.011
% 47.45/6.50  total_time:                             5.553
% 47.45/6.50  num_of_symbols:                         46
% 47.45/6.50  num_of_terms:                           150850
% 47.45/6.50  
% 47.45/6.50  ------ Preprocessing
% 47.45/6.50  
% 47.45/6.50  num_of_splits:                          0
% 47.45/6.50  num_of_split_atoms:                     0
% 47.45/6.50  num_of_reused_defs:                     0
% 47.45/6.50  num_eq_ax_congr_red:                    9
% 47.45/6.50  num_of_sem_filtered_clauses:            1
% 47.45/6.50  num_of_subtypes:                        3
% 47.45/6.50  monotx_restored_types:                  0
% 47.45/6.50  sat_num_of_epr_types:                   0
% 47.45/6.50  sat_num_of_non_cyclic_types:            0
% 47.45/6.50  sat_guarded_non_collapsed_types:        0
% 47.45/6.50  num_pure_diseq_elim:                    0
% 47.45/6.50  simp_replaced_by:                       0
% 47.45/6.50  res_preprocessed:                       53
% 47.45/6.50  prep_upred:                             0
% 47.45/6.50  prep_unflattend:                        0
% 47.45/6.50  smt_new_axioms:                         0
% 47.45/6.50  pred_elim_cands:                        2
% 47.45/6.50  pred_elim:                              0
% 47.45/6.50  pred_elim_cl:                           0
% 47.45/6.50  pred_elim_cycles:                       1
% 47.45/6.50  merged_defs:                            0
% 47.45/6.50  merged_defs_ncl:                        0
% 47.45/6.50  bin_hyper_res:                          0
% 47.45/6.50  prep_cycles:                            3
% 47.45/6.50  pred_elim_time:                         0.
% 47.45/6.50  splitting_time:                         0.
% 47.45/6.50  sem_filter_time:                        0.
% 47.45/6.50  monotx_time:                            0.
% 47.45/6.50  subtype_inf_time:                       0.
% 47.45/6.50  
% 47.45/6.50  ------ Problem properties
% 47.45/6.50  
% 47.45/6.50  clauses:                                12
% 47.45/6.50  conjectures:                            3
% 47.45/6.50  epr:                                    0
% 47.45/6.50  horn:                                   12
% 47.45/6.50  ground:                                 3
% 47.45/6.50  unary:                                  7
% 47.45/6.50  binary:                                 5
% 47.45/6.50  lits:                                   17
% 47.45/6.50  lits_eq:                                5
% 47.45/6.50  fd_pure:                                0
% 47.45/6.50  fd_pseudo:                              0
% 47.45/6.50  fd_cond:                                0
% 47.45/6.50  fd_pseudo_cond:                         0
% 47.45/6.50  ac_symbols:                             0
% 47.45/6.50  
% 47.45/6.50  ------ Propositional Solver
% 47.45/6.50  
% 47.45/6.50  prop_solver_calls:                      58
% 47.45/6.50  prop_fast_solver_calls:                 1874
% 47.45/6.50  smt_solver_calls:                       0
% 47.45/6.50  smt_fast_solver_calls:                  0
% 47.45/6.50  prop_num_of_clauses:                    57217
% 47.45/6.50  prop_preprocess_simplified:             97632
% 47.45/6.50  prop_fo_subsumed:                       294
% 47.45/6.50  prop_solver_time:                       0.
% 47.45/6.50  smt_solver_time:                        0.
% 47.45/6.50  smt_fast_solver_time:                   0.
% 47.45/6.50  prop_fast_solver_time:                  0.
% 47.45/6.50  prop_unsat_core_time:                   0.
% 47.45/6.50  
% 47.45/6.50  ------ QBF
% 47.45/6.50  
% 47.45/6.50  qbf_q_res:                              0
% 47.45/6.50  qbf_num_tautologies:                    0
% 47.45/6.50  qbf_prep_cycles:                        0
% 47.45/6.50  
% 47.45/6.50  ------ BMC1
% 47.45/6.50  
% 47.45/6.50  bmc1_current_bound:                     -1
% 47.45/6.50  bmc1_last_solved_bound:                 -1
% 47.45/6.50  bmc1_unsat_core_size:                   -1
% 47.45/6.50  bmc1_unsat_core_parents_size:           -1
% 47.45/6.50  bmc1_merge_next_fun:                    0
% 47.45/6.50  bmc1_unsat_core_clauses_time:           0.
% 47.45/6.50  
% 47.45/6.50  ------ Instantiation
% 47.45/6.50  
% 47.45/6.50  inst_num_of_clauses:                    5917
% 47.45/6.50  inst_num_in_passive:                    3507
% 47.45/6.50  inst_num_in_active:                     4951
% 47.45/6.50  inst_num_in_unprocessed:                245
% 47.45/6.50  inst_num_of_loops:                      5359
% 47.45/6.50  inst_num_of_learning_restarts:          1
% 47.45/6.50  inst_num_moves_active_passive:          391
% 47.45/6.50  inst_lit_activity:                      0
% 47.45/6.50  inst_lit_activity_moves:                1
% 47.45/6.50  inst_num_tautologies:                   0
% 47.45/6.50  inst_num_prop_implied:                  0
% 47.45/6.50  inst_num_existing_simplified:           0
% 47.45/6.50  inst_num_eq_res_simplified:             0
% 47.45/6.50  inst_num_child_elim:                    0
% 47.45/6.50  inst_num_of_dismatching_blockings:      27834
% 47.45/6.50  inst_num_of_non_proper_insts:           27077
% 47.45/6.50  inst_num_of_duplicates:                 0
% 47.45/6.50  inst_inst_num_from_inst_to_res:         0
% 47.45/6.50  inst_dismatching_checking_time:         0.
% 47.45/6.50  
% 47.45/6.50  ------ Resolution
% 47.45/6.50  
% 47.45/6.50  res_num_of_clauses:                     20
% 47.45/6.50  res_num_in_passive:                     20
% 47.45/6.50  res_num_in_active:                      0
% 47.45/6.50  res_num_of_loops:                       56
% 47.45/6.50  res_forward_subset_subsumed:            3102
% 47.45/6.50  res_backward_subset_subsumed:           158
% 47.45/6.50  res_forward_subsumed:                   0
% 47.45/6.50  res_backward_subsumed:                  0
% 47.45/6.50  res_forward_subsumption_resolution:     0
% 47.45/6.50  res_backward_subsumption_resolution:    0
% 47.45/6.50  res_clause_to_clause_subsumption:       127427
% 47.45/6.50  res_orphan_elimination:                 0
% 47.45/6.50  res_tautology_del:                      3011
% 47.45/6.50  res_num_eq_res_simplified:              0
% 47.45/6.50  res_num_sel_changes:                    0
% 47.45/6.50  res_moves_from_active_to_pass:          0
% 47.45/6.50  
% 47.45/6.50  ------ Superposition
% 47.45/6.50  
% 47.45/6.50  sup_time_total:                         0.
% 47.45/6.50  sup_time_generating:                    0.
% 47.45/6.50  sup_time_sim_full:                      0.
% 47.45/6.50  sup_time_sim_immed:                     0.
% 47.45/6.50  
% 47.45/6.50  sup_num_of_clauses:                     7622
% 47.45/6.50  sup_num_in_active:                      1069
% 47.45/6.50  sup_num_in_passive:                     6553
% 47.45/6.50  sup_num_of_loops:                       1070
% 47.45/6.50  sup_fw_superposition:                   13051
% 47.45/6.50  sup_bw_superposition:                   3892
% 47.45/6.50  sup_immediate_simplified:               3597
% 47.45/6.50  sup_given_eliminated:                   0
% 47.45/6.50  comparisons_done:                       0
% 47.45/6.50  comparisons_avoided:                    0
% 47.45/6.50  
% 47.45/6.50  ------ Simplifications
% 47.45/6.50  
% 47.45/6.50  
% 47.45/6.50  sim_fw_subset_subsumed:                 0
% 47.45/6.50  sim_bw_subset_subsumed:                 0
% 47.45/6.50  sim_fw_subsumed:                        506
% 47.45/6.50  sim_bw_subsumed:                        86
% 47.45/6.50  sim_fw_subsumption_res:                 0
% 47.45/6.50  sim_bw_subsumption_res:                 0
% 47.45/6.50  sim_tautology_del:                      0
% 47.45/6.50  sim_eq_tautology_del:                   130
% 47.45/6.50  sim_eq_res_simp:                        0
% 47.45/6.50  sim_fw_demodulated:                     2365
% 47.45/6.50  sim_bw_demodulated:                     5
% 47.45/6.50  sim_light_normalised:                   902
% 47.45/6.50  sim_joinable_taut:                      0
% 47.45/6.50  sim_joinable_simp:                      0
% 47.45/6.50  sim_ac_normalised:                      0
% 47.45/6.50  sim_smt_subsumption:                    0
% 47.45/6.50  
%------------------------------------------------------------------------------
