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
% DateTime   : Thu Dec  3 12:16:10 EST 2020

% Result     : Theorem 35.21s
% Output     : CNFRefutation 35.68s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 184 expanded)
%              Number of clauses        :   52 (  78 expanded)
%              Number of leaves         :   14 (  39 expanded)
%              Depth                    :   17
%              Number of atoms          :  168 ( 407 expanded)
%              Number of equality atoms :   65 (  97 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_tarski(X0),k3_tarski(X1)) = k3_tarski(k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(k3_tarski(X0),k3_tarski(X1)) = k3_tarski(k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f13,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f15,plain,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2))) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2)))
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2)))
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ~ r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),sK2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,sK2)))
        & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
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

fof(f27,plain,
    ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2)))
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f26,f25])).

fof(f41,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f27])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k3_tarski(X1) = k5_setfam_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_tarski(X1) = k5_setfam_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k3_tarski(X1) = k5_setfam_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f9,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f42,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f27])).

fof(f43,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))) ),
    inference(cnf_transformation,[],[f27])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_7,plain,
    ( k2_xboole_0(k3_tarski(X0),k3_tarski(X1)) = k3_tarski(k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
    | r1_tarski(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_70002,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
    | r1_tarski(k4_xboole_0(X0,X1),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_70534,plain,
    ( r1_tarski(X0,k3_tarski(k2_xboole_0(X1,X2))) != iProver_top
    | r1_tarski(k4_xboole_0(X0,k3_tarski(X1)),k3_tarski(X2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_70002])).

cnf(c_2,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_70003,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_69994,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_69997,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_70196,plain,
    ( r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_69994,c_69997])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_70004,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_71265,plain,
    ( r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_70196,c_70004])).

cnf(c_11,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_69998,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k5_setfam_1(X1,X0) = k3_tarski(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_69999,plain,
    ( k5_setfam_1(X0,X1) = k3_tarski(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_70440,plain,
    ( k5_setfam_1(X0,X1) = k3_tarski(X1)
    | r1_tarski(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_69998,c_69999])).

cnf(c_91601,plain,
    ( k5_setfam_1(u1_struct_0(sK0),X0) = k3_tarski(X0)
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_71265,c_70440])).

cnf(c_93136,plain,
    ( k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,X0)) = k3_tarski(k4_xboole_0(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_70003,c_91601])).

cnf(c_8,plain,
    ( k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k3_tarski(X0),k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_70000,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k3_tarski(X0),k3_tarski(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_70220,plain,
    ( r1_tarski(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(k3_tarski(X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_8,c_70000])).

cnf(c_70421,plain,
    ( r1_tarski(k3_tarski(sK1),u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_70196,c_70220])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_109,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_11])).

cnf(c_110,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_109])).

cnf(c_135,plain,
    ( ~ r1_tarski(X0,X1)
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_9,c_110])).

cnf(c_69993,plain,
    ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_135])).

cnf(c_70491,plain,
    ( k7_subset_1(u1_struct_0(sK0),k3_tarski(sK1),X0) = k4_xboole_0(k3_tarski(sK1),X0) ),
    inference(superposition,[status(thm)],[c_70421,c_69993])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_69995,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_70441,plain,
    ( k5_setfam_1(u1_struct_0(sK0),sK2) = k3_tarski(sK2) ),
    inference(superposition,[status(thm)],[c_69995,c_69999])).

cnf(c_70281,plain,
    ( k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X0) = k4_xboole_0(sK1,X0) ),
    inference(superposition,[status(thm)],[c_70196,c_69993])).

cnf(c_13,negated_conjecture,
    ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_69996,plain,
    ( r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_70305,plain,
    ( r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_70281,c_69996])).

cnf(c_70459,plain,
    ( r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_70441,c_70305])).

cnf(c_70442,plain,
    ( k5_setfam_1(u1_struct_0(sK0),sK1) = k3_tarski(sK1) ),
    inference(superposition,[status(thm)],[c_69994,c_69999])).

cnf(c_70499,plain,
    ( r1_tarski(k7_subset_1(u1_struct_0(sK0),k3_tarski(sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_70459,c_70442])).

cnf(c_70513,plain,
    ( r1_tarski(k4_xboole_0(k3_tarski(sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_70491,c_70499])).

cnf(c_93178,plain,
    ( r1_tarski(k4_xboole_0(k3_tarski(sK1),k3_tarski(sK2)),k3_tarski(k4_xboole_0(sK1,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_93136,c_70513])).

cnf(c_94013,plain,
    ( r1_tarski(k3_tarski(sK1),k3_tarski(k2_xboole_0(sK2,k4_xboole_0(sK1,sK2)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_70534,c_93178])).

cnf(c_3,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_94015,plain,
    ( r1_tarski(k3_tarski(sK1),k3_tarski(k2_xboole_0(sK2,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_94013,c_3])).

cnf(c_5,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2))
    | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_70001,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2)) = iProver_top
    | r1_tarski(k4_xboole_0(X0,X1),X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_70346,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_70003,c_70001])).

cnf(c_70851,plain,
    ( r1_tarski(k3_tarski(X0),k3_tarski(k2_xboole_0(X1,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_70346])).

cnf(c_94324,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_94015,c_70851])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n024.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:35:06 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.35  % Running in FOF mode
% 35.21/5.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 35.21/5.00  
% 35.21/5.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 35.21/5.00  
% 35.21/5.00  ------  iProver source info
% 35.21/5.00  
% 35.21/5.00  git: date: 2020-06-30 10:37:57 +0100
% 35.21/5.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 35.21/5.00  git: non_committed_changes: false
% 35.21/5.00  git: last_make_outside_of_git: false
% 35.21/5.00  
% 35.21/5.00  ------ 
% 35.21/5.00  ------ Parsing...
% 35.21/5.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 35.21/5.00  
% 35.21/5.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 35.21/5.00  
% 35.21/5.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 35.21/5.00  
% 35.21/5.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.21/5.00  ------ Proving...
% 35.21/5.00  ------ Problem Properties 
% 35.21/5.00  
% 35.21/5.00  
% 35.21/5.00  clauses                                 16
% 35.21/5.00  conjectures                             3
% 35.21/5.00  EPR                                     1
% 35.21/5.00  Horn                                    16
% 35.21/5.00  unary                                   8
% 35.21/5.00  binary                                  7
% 35.21/5.00  lits                                    25
% 35.21/5.00  lits eq                                 6
% 35.21/5.00  fd_pure                                 0
% 35.21/5.00  fd_pseudo                               0
% 35.21/5.00  fd_cond                                 0
% 35.21/5.00  fd_pseudo_cond                          0
% 35.21/5.00  AC symbols                              0
% 35.21/5.00  
% 35.21/5.00  ------ Input Options Time Limit: Unbounded
% 35.21/5.00  
% 35.21/5.00  
% 35.21/5.00  
% 35.21/5.00  
% 35.21/5.00  ------ Preprocessing...
% 35.21/5.00  
% 35.21/5.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e ------ 
% 35.21/5.00  Current options:
% 35.21/5.00  ------ 
% 35.21/5.00  
% 35.21/5.00  
% 35.21/5.00  
% 35.21/5.00  
% 35.21/5.00  ------ Proving...
% 35.21/5.00  
% 35.21/5.00  
% 35.21/5.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.21/5.00  
% 35.21/5.00  ------ Proving...
% 35.21/5.00  
% 35.21/5.00  
% 35.21/5.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.21/5.00  
% 35.21/5.00  ------ Proving...
% 35.21/5.00  
% 35.21/5.00  
% 35.21/5.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 35.21/5.00  
% 35.21/5.00  ------ Proving...
% 35.21/5.00  
% 35.21/5.00  
% 35.21/5.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.21/5.00  
% 35.21/5.00  ------ Proving...
% 35.21/5.00  
% 35.21/5.00  
% 35.21/5.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 35.21/5.00  
% 35.21/5.00  ------ Proving...
% 35.21/5.00  
% 35.21/5.00  
% 35.21/5.00  ------ Preprocessing...
% 35.21/5.00  
% 35.21/5.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 35.21/5.00  
% 35.21/5.00  ------ Proving...
% 35.21/5.00  
% 35.21/5.00  
% 35.21/5.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.21/5.00  
% 35.21/5.00  ------ Proving...
% 35.21/5.00  
% 35.21/5.00  
% 35.21/5.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.21/5.00  
% 35.21/5.00  ------ Proving...
% 35.21/5.00  
% 35.21/5.00  
% 35.21/5.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 35.21/5.00  
% 35.21/5.00  ------ Proving...
% 35.21/5.00  
% 35.21/5.00  
% 35.21/5.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.21/5.00  
% 35.21/5.00  ------ Proving...
% 35.21/5.00  
% 35.21/5.00  
% 35.21/5.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 35.21/5.00  
% 35.21/5.00  ------ Proving...
% 35.21/5.00  
% 35.21/5.00  
% 35.21/5.00  ------ Preprocessing...
% 35.21/5.00  
% 35.21/5.00  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.21/5.00  
% 35.21/5.00  ------ Proving...
% 35.21/5.00  
% 35.21/5.00  
% 35.21/5.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.21/5.00  
% 35.21/5.00  ------ Proving...
% 35.21/5.00  
% 35.21/5.00  
% 35.21/5.00  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.21/5.00  
% 35.21/5.00  ------ Proving...
% 35.21/5.00  
% 35.21/5.00  
% 35.21/5.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.21/5.00  
% 35.21/5.00  ------ Proving...
% 35.21/5.00  
% 35.21/5.00  
% 35.21/5.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.21/5.00  
% 35.21/5.00  ------ Proving...
% 35.21/5.00  
% 35.21/5.00  
% 35.21/5.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 35.21/5.00  
% 35.21/5.00  ------ Proving...
% 35.21/5.00  
% 35.21/5.00  
% 35.21/5.00  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.21/5.00  
% 35.21/5.00  ------ Proving...
% 35.21/5.00  
% 35.21/5.00  
% 35.21/5.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 35.21/5.00  
% 35.21/5.00  ------ Proving...
% 35.21/5.00  
% 35.21/5.00  
% 35.21/5.00  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.21/5.00  
% 35.21/5.00  ------ Proving...
% 35.21/5.00  
% 35.21/5.00  
% 35.21/5.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 35.21/5.00  
% 35.21/5.00  ------ Proving...
% 35.21/5.00  
% 35.21/5.00  
% 35.21/5.00  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.21/5.00  
% 35.21/5.00  ------ Proving...
% 35.21/5.00  
% 35.21/5.00  
% 35.21/5.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 35.21/5.00  
% 35.21/5.00  ------ Proving...
% 35.21/5.00  
% 35.21/5.00  
% 35.21/5.00  % SZS status Theorem for theBenchmark.p
% 35.21/5.00  
% 35.21/5.00   Resolution empty clause
% 35.21/5.00  
% 35.21/5.00  % SZS output start CNFRefutation for theBenchmark.p
% 35.21/5.00  
% 35.21/5.00  fof(f8,axiom,(
% 35.21/5.00    ! [X0,X1] : k2_xboole_0(k3_tarski(X0),k3_tarski(X1)) = k3_tarski(k2_xboole_0(X0,X1))),
% 35.21/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.21/5.00  
% 35.21/5.00  fof(f35,plain,(
% 35.21/5.00    ( ! [X0,X1] : (k2_xboole_0(k3_tarski(X0),k3_tarski(X1)) = k3_tarski(k2_xboole_0(X0,X1))) )),
% 35.21/5.00    inference(cnf_transformation,[],[f8])).
% 35.21/5.00  
% 35.21/5.00  fof(f5,axiom,(
% 35.21/5.00    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 35.21/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.21/5.00  
% 35.21/5.00  fof(f18,plain,(
% 35.21/5.00    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 35.21/5.00    inference(ennf_transformation,[],[f5])).
% 35.21/5.00  
% 35.21/5.00  fof(f32,plain,(
% 35.21/5.00    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 35.21/5.00    inference(cnf_transformation,[],[f18])).
% 35.21/5.00  
% 35.21/5.00  fof(f3,axiom,(
% 35.21/5.00    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 35.21/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.21/5.00  
% 35.21/5.00  fof(f30,plain,(
% 35.21/5.00    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 35.21/5.00    inference(cnf_transformation,[],[f3])).
% 35.21/5.00  
% 35.21/5.00  fof(f13,conjecture,(
% 35.21/5.00    ! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2))))))),
% 35.21/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.21/5.00  
% 35.21/5.00  fof(f14,negated_conjecture,(
% 35.21/5.00    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2))))))),
% 35.21/5.00    inference(negated_conjecture,[],[f13])).
% 35.21/5.00  
% 35.21/5.00  fof(f15,plain,(
% 35.21/5.00    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2)))))),
% 35.21/5.00    inference(pure_predicate_removal,[],[f14])).
% 35.21/5.00  
% 35.21/5.00  fof(f23,plain,(
% 35.21/5.00    ? [X0,X1] : (? [X2] : (~r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 35.21/5.00    inference(ennf_transformation,[],[f15])).
% 35.21/5.00  
% 35.21/5.00  fof(f26,plain,(
% 35.21/5.00    ( ! [X0,X1] : (? [X2] : (~r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (~r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),sK2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))) )),
% 35.21/5.00    introduced(choice_axiom,[])).
% 35.21/5.00  
% 35.21/5.00  fof(f25,plain,(
% 35.21/5.00    ? [X0,X1] : (? [X2] : (~r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (? [X2] : (~r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),X2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X2))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 35.21/5.00    introduced(choice_axiom,[])).
% 35.21/5.00  
% 35.21/5.00  fof(f27,plain,(
% 35.21/5.00    (~r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 35.21/5.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f26,f25])).
% 35.21/5.00  
% 35.21/5.00  fof(f41,plain,(
% 35.21/5.00    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 35.21/5.00    inference(cnf_transformation,[],[f27])).
% 35.21/5.00  
% 35.21/5.00  fof(f12,axiom,(
% 35.21/5.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 35.21/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.21/5.00  
% 35.21/5.00  fof(f24,plain,(
% 35.21/5.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 35.68/5.00    inference(nnf_transformation,[],[f12])).
% 35.68/5.00  
% 35.68/5.00  fof(f39,plain,(
% 35.68/5.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 35.68/5.00    inference(cnf_transformation,[],[f24])).
% 35.68/5.00  
% 35.68/5.00  fof(f2,axiom,(
% 35.68/5.00    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 35.68/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.68/5.00  
% 35.68/5.00  fof(f16,plain,(
% 35.68/5.00    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 35.68/5.00    inference(ennf_transformation,[],[f2])).
% 35.68/5.00  
% 35.68/5.00  fof(f17,plain,(
% 35.68/5.00    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 35.68/5.00    inference(flattening,[],[f16])).
% 35.68/5.00  
% 35.68/5.00  fof(f29,plain,(
% 35.68/5.00    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 35.68/5.00    inference(cnf_transformation,[],[f17])).
% 35.68/5.00  
% 35.68/5.00  fof(f40,plain,(
% 35.68/5.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 35.68/5.00    inference(cnf_transformation,[],[f24])).
% 35.68/5.00  
% 35.68/5.00  fof(f11,axiom,(
% 35.68/5.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k3_tarski(X1) = k5_setfam_1(X0,X1))),
% 35.68/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.68/5.00  
% 35.68/5.00  fof(f22,plain,(
% 35.68/5.00    ! [X0,X1] : (k3_tarski(X1) = k5_setfam_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 35.68/5.00    inference(ennf_transformation,[],[f11])).
% 35.68/5.00  
% 35.68/5.00  fof(f38,plain,(
% 35.68/5.00    ( ! [X0,X1] : (k3_tarski(X1) = k5_setfam_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 35.68/5.00    inference(cnf_transformation,[],[f22])).
% 35.68/5.00  
% 35.68/5.00  fof(f9,axiom,(
% 35.68/5.00    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 35.68/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.68/5.00  
% 35.68/5.00  fof(f36,plain,(
% 35.68/5.00    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 35.68/5.00    inference(cnf_transformation,[],[f9])).
% 35.68/5.00  
% 35.68/5.00  fof(f7,axiom,(
% 35.68/5.00    ! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k3_tarski(X0),k3_tarski(X1)))),
% 35.68/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.68/5.00  
% 35.68/5.00  fof(f20,plain,(
% 35.68/5.00    ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_tarski(X0,X1))),
% 35.68/5.00    inference(ennf_transformation,[],[f7])).
% 35.68/5.00  
% 35.68/5.00  fof(f34,plain,(
% 35.68/5.00    ( ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_tarski(X0,X1)) )),
% 35.68/5.00    inference(cnf_transformation,[],[f20])).
% 35.68/5.00  
% 35.68/5.00  fof(f10,axiom,(
% 35.68/5.00    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 35.68/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.68/5.00  
% 35.68/5.00  fof(f21,plain,(
% 35.68/5.00    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 35.68/5.00    inference(ennf_transformation,[],[f10])).
% 35.68/5.00  
% 35.68/5.00  fof(f37,plain,(
% 35.68/5.00    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 35.68/5.00    inference(cnf_transformation,[],[f21])).
% 35.68/5.00  
% 35.68/5.00  fof(f42,plain,(
% 35.68/5.00    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 35.68/5.00    inference(cnf_transformation,[],[f27])).
% 35.68/5.00  
% 35.68/5.00  fof(f43,plain,(
% 35.68/5.00    ~r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2)))),
% 35.68/5.00    inference(cnf_transformation,[],[f27])).
% 35.68/5.00  
% 35.68/5.00  fof(f4,axiom,(
% 35.68/5.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 35.68/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.68/5.00  
% 35.68/5.00  fof(f31,plain,(
% 35.68/5.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 35.68/5.00    inference(cnf_transformation,[],[f4])).
% 35.68/5.00  
% 35.68/5.00  fof(f6,axiom,(
% 35.68/5.00    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 35.68/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.68/5.00  
% 35.68/5.00  fof(f19,plain,(
% 35.68/5.00    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 35.68/5.00    inference(ennf_transformation,[],[f6])).
% 35.68/5.00  
% 35.68/5.00  fof(f33,plain,(
% 35.68/5.00    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 35.68/5.00    inference(cnf_transformation,[],[f19])).
% 35.68/5.00  
% 35.68/5.00  cnf(c_7,plain,
% 35.68/5.00      ( k2_xboole_0(k3_tarski(X0),k3_tarski(X1)) = k3_tarski(k2_xboole_0(X0,X1)) ),
% 35.68/5.00      inference(cnf_transformation,[],[f35]) ).
% 35.68/5.00  
% 35.68/5.00  cnf(c_4,plain,
% 35.68/5.00      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2)) | r1_tarski(k4_xboole_0(X0,X1),X2) ),
% 35.68/5.00      inference(cnf_transformation,[],[f32]) ).
% 35.68/5.00  
% 35.68/5.00  cnf(c_70002,plain,
% 35.68/5.00      ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
% 35.68/5.00      | r1_tarski(k4_xboole_0(X0,X1),X2) = iProver_top ),
% 35.68/5.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 35.68/5.00  
% 35.68/5.00  cnf(c_70534,plain,
% 35.68/5.00      ( r1_tarski(X0,k3_tarski(k2_xboole_0(X1,X2))) != iProver_top
% 35.68/5.00      | r1_tarski(k4_xboole_0(X0,k3_tarski(X1)),k3_tarski(X2)) = iProver_top ),
% 35.68/5.00      inference(superposition,[status(thm)],[c_7,c_70002]) ).
% 35.68/5.00  
% 35.68/5.00  cnf(c_2,plain,
% 35.68/5.00      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 35.68/5.00      inference(cnf_transformation,[],[f30]) ).
% 35.68/5.00  
% 35.68/5.00  cnf(c_70003,plain,
% 35.68/5.00      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 35.68/5.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 35.68/5.00  
% 35.68/5.00  cnf(c_15,negated_conjecture,
% 35.68/5.00      ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
% 35.68/5.00      inference(cnf_transformation,[],[f41]) ).
% 35.68/5.00  
% 35.68/5.00  cnf(c_69994,plain,
% 35.68/5.00      ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
% 35.68/5.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 35.68/5.00  
% 35.68/5.00  cnf(c_12,plain,
% 35.68/5.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 35.68/5.00      inference(cnf_transformation,[],[f39]) ).
% 35.68/5.00  
% 35.68/5.00  cnf(c_69997,plain,
% 35.68/5.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 35.68/5.00      | r1_tarski(X0,X1) = iProver_top ),
% 35.68/5.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 35.68/5.00  
% 35.68/5.00  cnf(c_70196,plain,
% 35.68/5.00      ( r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 35.68/5.00      inference(superposition,[status(thm)],[c_69994,c_69997]) ).
% 35.68/5.00  
% 35.68/5.00  cnf(c_1,plain,
% 35.68/5.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X2,X0) | r1_tarski(X2,X1) ),
% 35.68/5.00      inference(cnf_transformation,[],[f29]) ).
% 35.68/5.00  
% 35.68/5.00  cnf(c_70004,plain,
% 35.68/5.00      ( r1_tarski(X0,X1) != iProver_top
% 35.68/5.00      | r1_tarski(X2,X0) != iProver_top
% 35.68/5.00      | r1_tarski(X2,X1) = iProver_top ),
% 35.68/5.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 35.68/5.00  
% 35.68/5.00  cnf(c_71265,plain,
% 35.68/5.00      ( r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 35.68/5.00      | r1_tarski(X0,sK1) != iProver_top ),
% 35.68/5.00      inference(superposition,[status(thm)],[c_70196,c_70004]) ).
% 35.68/5.00  
% 35.68/5.00  cnf(c_11,plain,
% 35.68/5.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 35.68/5.00      inference(cnf_transformation,[],[f40]) ).
% 35.68/5.01  
% 35.68/5.01  cnf(c_69998,plain,
% 35.68/5.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 35.68/5.01      | r1_tarski(X0,X1) != iProver_top ),
% 35.68/5.01      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 35.68/5.01  
% 35.68/5.01  cnf(c_10,plain,
% 35.68/5.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 35.68/5.01      | k5_setfam_1(X1,X0) = k3_tarski(X0) ),
% 35.68/5.01      inference(cnf_transformation,[],[f38]) ).
% 35.68/5.01  
% 35.68/5.01  cnf(c_69999,plain,
% 35.68/5.01      ( k5_setfam_1(X0,X1) = k3_tarski(X1)
% 35.68/5.01      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 35.68/5.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 35.68/5.01  
% 35.68/5.01  cnf(c_70440,plain,
% 35.68/5.01      ( k5_setfam_1(X0,X1) = k3_tarski(X1)
% 35.68/5.01      | r1_tarski(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 35.68/5.01      inference(superposition,[status(thm)],[c_69998,c_69999]) ).
% 35.68/5.01  
% 35.68/5.01  cnf(c_91601,plain,
% 35.68/5.01      ( k5_setfam_1(u1_struct_0(sK0),X0) = k3_tarski(X0)
% 35.68/5.01      | r1_tarski(X0,sK1) != iProver_top ),
% 35.68/5.01      inference(superposition,[status(thm)],[c_71265,c_70440]) ).
% 35.68/5.01  
% 35.68/5.01  cnf(c_93136,plain,
% 35.68/5.01      ( k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,X0)) = k3_tarski(k4_xboole_0(sK1,X0)) ),
% 35.68/5.01      inference(superposition,[status(thm)],[c_70003,c_91601]) ).
% 35.68/5.01  
% 35.68/5.01  cnf(c_8,plain,
% 35.68/5.01      ( k3_tarski(k1_zfmisc_1(X0)) = X0 ),
% 35.68/5.01      inference(cnf_transformation,[],[f36]) ).
% 35.68/5.01  
% 35.68/5.01  cnf(c_6,plain,
% 35.68/5.01      ( ~ r1_tarski(X0,X1) | r1_tarski(k3_tarski(X0),k3_tarski(X1)) ),
% 35.68/5.01      inference(cnf_transformation,[],[f34]) ).
% 35.68/5.01  
% 35.68/5.01  cnf(c_70000,plain,
% 35.68/5.01      ( r1_tarski(X0,X1) != iProver_top
% 35.68/5.01      | r1_tarski(k3_tarski(X0),k3_tarski(X1)) = iProver_top ),
% 35.68/5.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 35.68/5.01  
% 35.68/5.01  cnf(c_70220,plain,
% 35.68/5.01      ( r1_tarski(X0,k1_zfmisc_1(X1)) != iProver_top
% 35.68/5.01      | r1_tarski(k3_tarski(X0),X1) = iProver_top ),
% 35.68/5.01      inference(superposition,[status(thm)],[c_8,c_70000]) ).
% 35.68/5.01  
% 35.68/5.01  cnf(c_70421,plain,
% 35.68/5.01      ( r1_tarski(k3_tarski(sK1),u1_struct_0(sK0)) = iProver_top ),
% 35.68/5.01      inference(superposition,[status(thm)],[c_70196,c_70220]) ).
% 35.68/5.01  
% 35.68/5.01  cnf(c_9,plain,
% 35.68/5.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 35.68/5.01      | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 35.68/5.01      inference(cnf_transformation,[],[f37]) ).
% 35.68/5.01  
% 35.68/5.01  cnf(c_109,plain,
% 35.68/5.01      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 35.68/5.01      inference(prop_impl,[status(thm)],[c_11]) ).
% 35.68/5.01  
% 35.68/5.01  cnf(c_110,plain,
% 35.68/5.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 35.68/5.01      inference(renaming,[status(thm)],[c_109]) ).
% 35.68/5.01  
% 35.68/5.01  cnf(c_135,plain,
% 35.68/5.01      ( ~ r1_tarski(X0,X1) | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 35.68/5.01      inference(bin_hyper_res,[status(thm)],[c_9,c_110]) ).
% 35.68/5.01  
% 35.68/5.01  cnf(c_69993,plain,
% 35.68/5.01      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
% 35.68/5.01      | r1_tarski(X1,X0) != iProver_top ),
% 35.68/5.01      inference(predicate_to_equality,[status(thm)],[c_135]) ).
% 35.68/5.01  
% 35.68/5.01  cnf(c_70491,plain,
% 35.68/5.01      ( k7_subset_1(u1_struct_0(sK0),k3_tarski(sK1),X0) = k4_xboole_0(k3_tarski(sK1),X0) ),
% 35.68/5.01      inference(superposition,[status(thm)],[c_70421,c_69993]) ).
% 35.68/5.01  
% 35.68/5.01  cnf(c_14,negated_conjecture,
% 35.68/5.01      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
% 35.68/5.01      inference(cnf_transformation,[],[f42]) ).
% 35.68/5.01  
% 35.68/5.01  cnf(c_69995,plain,
% 35.68/5.01      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
% 35.68/5.01      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 35.68/5.01  
% 35.68/5.01  cnf(c_70441,plain,
% 35.68/5.01      ( k5_setfam_1(u1_struct_0(sK0),sK2) = k3_tarski(sK2) ),
% 35.68/5.01      inference(superposition,[status(thm)],[c_69995,c_69999]) ).
% 35.68/5.01  
% 35.68/5.01  cnf(c_70281,plain,
% 35.68/5.01      ( k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X0) = k4_xboole_0(sK1,X0) ),
% 35.68/5.01      inference(superposition,[status(thm)],[c_70196,c_69993]) ).
% 35.68/5.01  
% 35.68/5.01  cnf(c_13,negated_conjecture,
% 35.68/5.01      ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))) ),
% 35.68/5.01      inference(cnf_transformation,[],[f43]) ).
% 35.68/5.01  
% 35.68/5.01  cnf(c_69996,plain,
% 35.68/5.01      ( r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))) != iProver_top ),
% 35.68/5.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 35.68/5.01  
% 35.68/5.01  cnf(c_70305,plain,
% 35.68/5.01      ( r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2))) != iProver_top ),
% 35.68/5.01      inference(demodulation,[status(thm)],[c_70281,c_69996]) ).
% 35.68/5.01  
% 35.68/5.01  cnf(c_70459,plain,
% 35.68/5.01      ( r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2))) != iProver_top ),
% 35.68/5.01      inference(demodulation,[status(thm)],[c_70441,c_70305]) ).
% 35.68/5.01  
% 35.68/5.01  cnf(c_70442,plain,
% 35.68/5.01      ( k5_setfam_1(u1_struct_0(sK0),sK1) = k3_tarski(sK1) ),
% 35.68/5.01      inference(superposition,[status(thm)],[c_69994,c_69999]) ).
% 35.68/5.01  
% 35.68/5.01  cnf(c_70499,plain,
% 35.68/5.01      ( r1_tarski(k7_subset_1(u1_struct_0(sK0),k3_tarski(sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2))) != iProver_top ),
% 35.68/5.01      inference(light_normalisation,[status(thm)],[c_70459,c_70442]) ).
% 35.68/5.01  
% 35.68/5.01  cnf(c_70513,plain,
% 35.68/5.01      ( r1_tarski(k4_xboole_0(k3_tarski(sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2))) != iProver_top ),
% 35.68/5.01      inference(demodulation,[status(thm)],[c_70491,c_70499]) ).
% 35.68/5.01  
% 35.68/5.01  cnf(c_93178,plain,
% 35.68/5.01      ( r1_tarski(k4_xboole_0(k3_tarski(sK1),k3_tarski(sK2)),k3_tarski(k4_xboole_0(sK1,sK2))) != iProver_top ),
% 35.68/5.01      inference(demodulation,[status(thm)],[c_93136,c_70513]) ).
% 35.68/5.01  
% 35.68/5.01  cnf(c_94013,plain,
% 35.68/5.01      ( r1_tarski(k3_tarski(sK1),k3_tarski(k2_xboole_0(sK2,k4_xboole_0(sK1,sK2)))) != iProver_top ),
% 35.68/5.01      inference(superposition,[status(thm)],[c_70534,c_93178]) ).
% 35.68/5.01  
% 35.68/5.01  cnf(c_3,plain,
% 35.68/5.01      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 35.68/5.01      inference(cnf_transformation,[],[f31]) ).
% 35.68/5.01  
% 35.68/5.01  cnf(c_94015,plain,
% 35.68/5.01      ( r1_tarski(k3_tarski(sK1),k3_tarski(k2_xboole_0(sK2,sK1))) != iProver_top ),
% 35.68/5.01      inference(demodulation,[status(thm)],[c_94013,c_3]) ).
% 35.68/5.01  
% 35.68/5.01  cnf(c_5,plain,
% 35.68/5.01      ( r1_tarski(X0,k2_xboole_0(X1,X2)) | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ),
% 35.68/5.01      inference(cnf_transformation,[],[f33]) ).
% 35.68/5.01  
% 35.68/5.01  cnf(c_70001,plain,
% 35.68/5.01      ( r1_tarski(X0,k2_xboole_0(X1,X2)) = iProver_top
% 35.68/5.01      | r1_tarski(k4_xboole_0(X0,X1),X2) != iProver_top ),
% 35.68/5.01      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 35.68/5.01  
% 35.68/5.01  cnf(c_70346,plain,
% 35.68/5.01      ( r1_tarski(X0,k2_xboole_0(X1,X0)) = iProver_top ),
% 35.68/5.01      inference(superposition,[status(thm)],[c_70003,c_70001]) ).
% 35.68/5.01  
% 35.68/5.01  cnf(c_70851,plain,
% 35.68/5.01      ( r1_tarski(k3_tarski(X0),k3_tarski(k2_xboole_0(X1,X0))) = iProver_top ),
% 35.68/5.01      inference(superposition,[status(thm)],[c_7,c_70346]) ).
% 35.68/5.01  
% 35.68/5.01  cnf(c_94324,plain,
% 35.68/5.01      ( $false ),
% 35.68/5.01      inference(forward_subsumption_resolution,[status(thm)],[c_94015,c_70851]) ).
% 35.68/5.01  
% 35.68/5.01  
% 35.68/5.01  % SZS output end CNFRefutation for theBenchmark.p
% 35.68/5.01  
% 35.68/5.01  ------                               Statistics
% 35.68/5.01  
% 35.68/5.01  ------ Selected
% 35.68/5.01  
% 35.68/5.01  total_time:                             4.435
% 35.68/5.01  
%------------------------------------------------------------------------------
