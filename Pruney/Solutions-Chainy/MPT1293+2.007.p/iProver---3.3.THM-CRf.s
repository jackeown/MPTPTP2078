%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:16:08 EST 2020

% Result     : Theorem 28.04s
% Output     : CNFRefutation 28.04s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 256 expanded)
%              Number of clauses        :   56 (  96 expanded)
%              Number of leaves         :   14 (  58 expanded)
%              Depth                    :   16
%              Number of atoms          :  189 ( 557 expanded)
%              Number of equality atoms :   73 ( 142 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_tarski(X0),k3_tarski(X1)) = k3_tarski(k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(k3_tarski(X0),k3_tarski(X1)) = k3_tarski(k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f51,plain,(
    ! [X0,X1] : k3_tarski(k3_tarski(k2_tarski(X0,X1))) = k3_tarski(k2_tarski(k3_tarski(X0),k3_tarski(X1))) ),
    inference(definition_unfolding,[],[f37,f36,f36])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f23])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f53,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f30])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f48,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X0,k4_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f33,f36,f36])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k2_tarski(X1,X2)))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f35,f36])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) ) ),
    inference(definition_unfolding,[],[f34,f36])).

fof(f13,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f22,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2)))
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2)))
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ~ r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),sK2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,sK2)))
        & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
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

fof(f28,plain,
    ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2)))
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f27,f26])).

fof(f44,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f28])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k3_tarski(X1) = k5_setfam_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_tarski(X1) = k5_setfam_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k3_tarski(X1) = k5_setfam_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f45,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f28])).

fof(f46,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_7,plain,
    ( k3_tarski(k2_tarski(k3_tarski(X0),k3_tarski(X1))) = k3_tarski(k3_tarski(k2_tarski(X0,X1))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_697,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_4,plain,
    ( k3_tarski(k2_tarski(X0,k4_xboole_0(X1,X0))) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_6,plain,
    ( r1_tarski(X0,k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_695,plain,
    ( r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) = iProver_top
    | r1_tarski(k4_xboole_0(X0,X1),X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3413,plain,
    ( r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) = iProver_top
    | r1_tarski(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_695])).

cnf(c_7001,plain,
    ( r1_tarski(X0,k3_tarski(k2_tarski(X1,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_697,c_3413])).

cnf(c_103493,plain,
    ( r1_tarski(k3_tarski(X0),k3_tarski(k3_tarski(k2_tarski(X1,X0)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_7001])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,k3_tarski(k2_tarski(X1,X2)))
    | r1_tarski(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_696,plain,
    ( r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) != iProver_top
    | r1_tarski(k4_xboole_0(X0,X1),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3720,plain,
    ( r1_tarski(X0,k3_tarski(k3_tarski(k2_tarski(X1,X2)))) != iProver_top
    | r1_tarski(k4_xboole_0(X0,k3_tarski(X1)),k3_tarski(X2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_696])).

cnf(c_10275,plain,
    ( r1_tarski(X0,k3_tarski(k3_tarski(k2_tarski(X1,X2)))) != iProver_top
    | r1_tarski(k4_xboole_0(X0,k3_tarski(X1)),k3_tarski(k4_xboole_0(X2,X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_3720])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_688,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k5_setfam_1(X1,X0) = k3_tarski(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_693,plain,
    ( k5_setfam_1(X0,X1) = k3_tarski(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1483,plain,
    ( k5_setfam_1(u1_struct_0(sK0),sK1) = k3_tarski(sK1) ),
    inference(superposition,[status(thm)],[c_688,c_693])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | m1_subset_1(k5_setfam_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_694,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | m1_subset_1(k5_setfam_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3069,plain,
    ( m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1483,c_694])).

cnf(c_17,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3781,plain,
    ( m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3069,c_17])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_691,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3786,plain,
    ( r1_tarski(k3_tarski(sK1),u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3781,c_691])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_12,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_123,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_12])).

cnf(c_124,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_123])).

cnf(c_150,plain,
    ( ~ r1_tarski(X0,X1)
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_9,c_124])).

cnf(c_686,plain,
    ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_150])).

cnf(c_4018,plain,
    ( k7_subset_1(u1_struct_0(sK0),k3_tarski(sK1),X0) = k4_xboole_0(k3_tarski(sK1),X0) ),
    inference(superposition,[status(thm)],[c_3786,c_686])).

cnf(c_1354,plain,
    ( r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_688,c_691])).

cnf(c_1568,plain,
    ( k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X0) = k4_xboole_0(sK1,X0) ),
    inference(superposition,[status(thm)],[c_1354,c_686])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k7_subset_1(X1,X0,X2),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_149,plain,
    ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
    | ~ r1_tarski(X1,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_8,c_124])).

cnf(c_687,plain,
    ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) = iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_149])).

cnf(c_1956,plain,
    ( m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
    | r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1568,c_687])).

cnf(c_905,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | r1_tarski(X0,k1_zfmisc_1(X1)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1101,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_905])).

cnf(c_1102,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
    | r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1101])).

cnf(c_2573,plain,
    ( m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1956,c_17,c_1102])).

cnf(c_2581,plain,
    ( k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,X0)) = k3_tarski(k4_xboole_0(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_2573,c_693])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_689,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1482,plain,
    ( k5_setfam_1(u1_struct_0(sK0),sK2) = k3_tarski(sK2) ),
    inference(superposition,[status(thm)],[c_689,c_693])).

cnf(c_14,negated_conjecture,
    ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_690,plain,
    ( r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1571,plain,
    ( r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1482,c_690])).

cnf(c_1696,plain,
    ( r1_tarski(k7_subset_1(u1_struct_0(sK0),k3_tarski(sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1571,c_1483])).

cnf(c_1873,plain,
    ( r1_tarski(k7_subset_1(u1_struct_0(sK0),k3_tarski(sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1568,c_1696])).

cnf(c_2830,plain,
    ( r1_tarski(k7_subset_1(u1_struct_0(sK0),k3_tarski(sK1),k3_tarski(sK2)),k3_tarski(k4_xboole_0(sK1,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2581,c_1873])).

cnf(c_4474,plain,
    ( r1_tarski(k4_xboole_0(k3_tarski(sK1),k3_tarski(sK2)),k3_tarski(k4_xboole_0(sK1,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4018,c_2830])).

cnf(c_29158,plain,
    ( r1_tarski(k3_tarski(sK1),k3_tarski(k3_tarski(k2_tarski(sK2,sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_10275,c_4474])).

cnf(c_104660,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_103493,c_29158])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 11:15:42 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 28.04/3.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 28.04/3.99  
% 28.04/3.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 28.04/3.99  
% 28.04/3.99  ------  iProver source info
% 28.04/3.99  
% 28.04/3.99  git: date: 2020-06-30 10:37:57 +0100
% 28.04/3.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 28.04/3.99  git: non_committed_changes: false
% 28.04/3.99  git: last_make_outside_of_git: false
% 28.04/3.99  
% 28.04/3.99  ------ 
% 28.04/3.99  
% 28.04/3.99  ------ Input Options
% 28.04/3.99  
% 28.04/3.99  --out_options                           all
% 28.04/3.99  --tptp_safe_out                         true
% 28.04/3.99  --problem_path                          ""
% 28.04/3.99  --include_path                          ""
% 28.04/3.99  --clausifier                            res/vclausify_rel
% 28.04/3.99  --clausifier_options                    --mode clausify
% 28.04/3.99  --stdin                                 false
% 28.04/3.99  --stats_out                             all
% 28.04/3.99  
% 28.04/3.99  ------ General Options
% 28.04/3.99  
% 28.04/3.99  --fof                                   false
% 28.04/3.99  --time_out_real                         305.
% 28.04/3.99  --time_out_virtual                      -1.
% 28.04/3.99  --symbol_type_check                     false
% 28.04/3.99  --clausify_out                          false
% 28.04/3.99  --sig_cnt_out                           false
% 28.04/3.99  --trig_cnt_out                          false
% 28.04/3.99  --trig_cnt_out_tolerance                1.
% 28.04/3.99  --trig_cnt_out_sk_spl                   false
% 28.04/3.99  --abstr_cl_out                          false
% 28.04/3.99  
% 28.04/3.99  ------ Global Options
% 28.04/3.99  
% 28.04/3.99  --schedule                              default
% 28.04/3.99  --add_important_lit                     false
% 28.04/3.99  --prop_solver_per_cl                    1000
% 28.04/3.99  --min_unsat_core                        false
% 28.04/3.99  --soft_assumptions                      false
% 28.04/3.99  --soft_lemma_size                       3
% 28.04/3.99  --prop_impl_unit_size                   0
% 28.04/3.99  --prop_impl_unit                        []
% 28.04/3.99  --share_sel_clauses                     true
% 28.04/3.99  --reset_solvers                         false
% 28.04/3.99  --bc_imp_inh                            [conj_cone]
% 28.04/3.99  --conj_cone_tolerance                   3.
% 28.04/3.99  --extra_neg_conj                        none
% 28.04/3.99  --large_theory_mode                     true
% 28.04/3.99  --prolific_symb_bound                   200
% 28.04/3.99  --lt_threshold                          2000
% 28.04/3.99  --clause_weak_htbl                      true
% 28.04/3.99  --gc_record_bc_elim                     false
% 28.04/3.99  
% 28.04/3.99  ------ Preprocessing Options
% 28.04/3.99  
% 28.04/3.99  --preprocessing_flag                    true
% 28.04/3.99  --time_out_prep_mult                    0.1
% 28.04/3.99  --splitting_mode                        input
% 28.04/3.99  --splitting_grd                         true
% 28.04/3.99  --splitting_cvd                         false
% 28.04/3.99  --splitting_cvd_svl                     false
% 28.04/3.99  --splitting_nvd                         32
% 28.04/3.99  --sub_typing                            true
% 28.04/3.99  --prep_gs_sim                           true
% 28.04/3.99  --prep_unflatten                        true
% 28.04/3.99  --prep_res_sim                          true
% 28.04/3.99  --prep_upred                            true
% 28.04/3.99  --prep_sem_filter                       exhaustive
% 28.04/3.99  --prep_sem_filter_out                   false
% 28.04/3.99  --pred_elim                             true
% 28.04/3.99  --res_sim_input                         true
% 28.04/3.99  --eq_ax_congr_red                       true
% 28.04/3.99  --pure_diseq_elim                       true
% 28.04/3.99  --brand_transform                       false
% 28.04/3.99  --non_eq_to_eq                          false
% 28.04/3.99  --prep_def_merge                        true
% 28.04/3.99  --prep_def_merge_prop_impl              false
% 28.04/3.99  --prep_def_merge_mbd                    true
% 28.04/3.99  --prep_def_merge_tr_red                 false
% 28.04/3.99  --prep_def_merge_tr_cl                  false
% 28.04/3.99  --smt_preprocessing                     true
% 28.04/3.99  --smt_ac_axioms                         fast
% 28.04/3.99  --preprocessed_out                      false
% 28.04/3.99  --preprocessed_stats                    false
% 28.04/3.99  
% 28.04/3.99  ------ Abstraction refinement Options
% 28.04/3.99  
% 28.04/3.99  --abstr_ref                             []
% 28.04/3.99  --abstr_ref_prep                        false
% 28.04/3.99  --abstr_ref_until_sat                   false
% 28.04/3.99  --abstr_ref_sig_restrict                funpre
% 28.04/3.99  --abstr_ref_af_restrict_to_split_sk     false
% 28.04/3.99  --abstr_ref_under                       []
% 28.04/3.99  
% 28.04/3.99  ------ SAT Options
% 28.04/3.99  
% 28.04/3.99  --sat_mode                              false
% 28.04/3.99  --sat_fm_restart_options                ""
% 28.04/3.99  --sat_gr_def                            false
% 28.04/3.99  --sat_epr_types                         true
% 28.04/3.99  --sat_non_cyclic_types                  false
% 28.04/3.99  --sat_finite_models                     false
% 28.04/3.99  --sat_fm_lemmas                         false
% 28.04/3.99  --sat_fm_prep                           false
% 28.04/3.99  --sat_fm_uc_incr                        true
% 28.04/3.99  --sat_out_model                         small
% 28.04/3.99  --sat_out_clauses                       false
% 28.04/3.99  
% 28.04/3.99  ------ QBF Options
% 28.04/3.99  
% 28.04/3.99  --qbf_mode                              false
% 28.04/3.99  --qbf_elim_univ                         false
% 28.04/3.99  --qbf_dom_inst                          none
% 28.04/3.99  --qbf_dom_pre_inst                      false
% 28.04/3.99  --qbf_sk_in                             false
% 28.04/3.99  --qbf_pred_elim                         true
% 28.04/3.99  --qbf_split                             512
% 28.04/3.99  
% 28.04/3.99  ------ BMC1 Options
% 28.04/3.99  
% 28.04/3.99  --bmc1_incremental                      false
% 28.04/3.99  --bmc1_axioms                           reachable_all
% 28.04/3.99  --bmc1_min_bound                        0
% 28.04/3.99  --bmc1_max_bound                        -1
% 28.04/3.99  --bmc1_max_bound_default                -1
% 28.04/3.99  --bmc1_symbol_reachability              true
% 28.04/3.99  --bmc1_property_lemmas                  false
% 28.04/3.99  --bmc1_k_induction                      false
% 28.04/3.99  --bmc1_non_equiv_states                 false
% 28.04/3.99  --bmc1_deadlock                         false
% 28.04/3.99  --bmc1_ucm                              false
% 28.04/3.99  --bmc1_add_unsat_core                   none
% 28.04/3.99  --bmc1_unsat_core_children              false
% 28.04/3.99  --bmc1_unsat_core_extrapolate_axioms    false
% 28.04/3.99  --bmc1_out_stat                         full
% 28.04/3.99  --bmc1_ground_init                      false
% 28.04/3.99  --bmc1_pre_inst_next_state              false
% 28.04/3.99  --bmc1_pre_inst_state                   false
% 28.04/3.99  --bmc1_pre_inst_reach_state             false
% 28.04/3.99  --bmc1_out_unsat_core                   false
% 28.04/3.99  --bmc1_aig_witness_out                  false
% 28.04/3.99  --bmc1_verbose                          false
% 28.04/3.99  --bmc1_dump_clauses_tptp                false
% 28.04/3.99  --bmc1_dump_unsat_core_tptp             false
% 28.04/3.99  --bmc1_dump_file                        -
% 28.04/3.99  --bmc1_ucm_expand_uc_limit              128
% 28.04/3.99  --bmc1_ucm_n_expand_iterations          6
% 28.04/3.99  --bmc1_ucm_extend_mode                  1
% 28.04/3.99  --bmc1_ucm_init_mode                    2
% 28.04/3.99  --bmc1_ucm_cone_mode                    none
% 28.04/3.99  --bmc1_ucm_reduced_relation_type        0
% 28.04/3.99  --bmc1_ucm_relax_model                  4
% 28.04/3.99  --bmc1_ucm_full_tr_after_sat            true
% 28.04/3.99  --bmc1_ucm_expand_neg_assumptions       false
% 28.04/3.99  --bmc1_ucm_layered_model                none
% 28.04/3.99  --bmc1_ucm_max_lemma_size               10
% 28.04/3.99  
% 28.04/3.99  ------ AIG Options
% 28.04/3.99  
% 28.04/3.99  --aig_mode                              false
% 28.04/3.99  
% 28.04/3.99  ------ Instantiation Options
% 28.04/3.99  
% 28.04/3.99  --instantiation_flag                    true
% 28.04/3.99  --inst_sos_flag                         false
% 28.04/3.99  --inst_sos_phase                        true
% 28.04/3.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 28.04/3.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 28.04/3.99  --inst_lit_sel_side                     num_symb
% 28.04/3.99  --inst_solver_per_active                1400
% 28.04/3.99  --inst_solver_calls_frac                1.
% 28.04/3.99  --inst_passive_queue_type               priority_queues
% 28.04/3.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 28.04/3.99  --inst_passive_queues_freq              [25;2]
% 28.04/3.99  --inst_dismatching                      true
% 28.04/3.99  --inst_eager_unprocessed_to_passive     true
% 28.04/3.99  --inst_prop_sim_given                   true
% 28.04/3.99  --inst_prop_sim_new                     false
% 28.04/3.99  --inst_subs_new                         false
% 28.04/3.99  --inst_eq_res_simp                      false
% 28.04/3.99  --inst_subs_given                       false
% 28.04/3.99  --inst_orphan_elimination               true
% 28.04/3.99  --inst_learning_loop_flag               true
% 28.04/3.99  --inst_learning_start                   3000
% 28.04/3.99  --inst_learning_factor                  2
% 28.04/3.99  --inst_start_prop_sim_after_learn       3
% 28.04/3.99  --inst_sel_renew                        solver
% 28.04/3.99  --inst_lit_activity_flag                true
% 28.04/3.99  --inst_restr_to_given                   false
% 28.04/3.99  --inst_activity_threshold               500
% 28.04/3.99  --inst_out_proof                        true
% 28.04/3.99  
% 28.04/3.99  ------ Resolution Options
% 28.04/3.99  
% 28.04/3.99  --resolution_flag                       true
% 28.04/3.99  --res_lit_sel                           adaptive
% 28.04/3.99  --res_lit_sel_side                      none
% 28.04/3.99  --res_ordering                          kbo
% 28.04/3.99  --res_to_prop_solver                    active
% 28.04/3.99  --res_prop_simpl_new                    false
% 28.04/3.99  --res_prop_simpl_given                  true
% 28.04/3.99  --res_passive_queue_type                priority_queues
% 28.04/3.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 28.04/3.99  --res_passive_queues_freq               [15;5]
% 28.04/3.99  --res_forward_subs                      full
% 28.04/3.99  --res_backward_subs                     full
% 28.04/3.99  --res_forward_subs_resolution           true
% 28.04/3.99  --res_backward_subs_resolution          true
% 28.04/3.99  --res_orphan_elimination                true
% 28.04/3.99  --res_time_limit                        2.
% 28.04/3.99  --res_out_proof                         true
% 28.04/3.99  
% 28.04/3.99  ------ Superposition Options
% 28.04/3.99  
% 28.04/3.99  --superposition_flag                    true
% 28.04/3.99  --sup_passive_queue_type                priority_queues
% 28.04/3.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 28.04/3.99  --sup_passive_queues_freq               [8;1;4]
% 28.04/3.99  --demod_completeness_check              fast
% 28.04/3.99  --demod_use_ground                      true
% 28.04/3.99  --sup_to_prop_solver                    passive
% 28.04/3.99  --sup_prop_simpl_new                    true
% 28.04/3.99  --sup_prop_simpl_given                  true
% 28.04/3.99  --sup_fun_splitting                     false
% 28.04/3.99  --sup_smt_interval                      50000
% 28.04/3.99  
% 28.04/3.99  ------ Superposition Simplification Setup
% 28.04/3.99  
% 28.04/3.99  --sup_indices_passive                   []
% 28.04/3.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 28.04/3.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 28.04/3.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 28.04/3.99  --sup_full_triv                         [TrivRules;PropSubs]
% 28.04/3.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 28.04/3.99  --sup_full_bw                           [BwDemod]
% 28.04/3.99  --sup_immed_triv                        [TrivRules]
% 28.04/3.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 28.04/3.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 28.04/3.99  --sup_immed_bw_main                     []
% 28.04/3.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 28.04/3.99  --sup_input_triv                        [Unflattening;TrivRules]
% 28.04/3.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 28.04/3.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 28.04/3.99  
% 28.04/3.99  ------ Combination Options
% 28.04/3.99  
% 28.04/3.99  --comb_res_mult                         3
% 28.04/3.99  --comb_sup_mult                         2
% 28.04/3.99  --comb_inst_mult                        10
% 28.04/3.99  
% 28.04/3.99  ------ Debug Options
% 28.04/3.99  
% 28.04/3.99  --dbg_backtrace                         false
% 28.04/3.99  --dbg_dump_prop_clauses                 false
% 28.04/3.99  --dbg_dump_prop_clauses_file            -
% 28.04/3.99  --dbg_out_stat                          false
% 28.04/3.99  ------ Parsing...
% 28.04/3.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 28.04/3.99  
% 28.04/3.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 28.04/3.99  
% 28.04/3.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 28.04/3.99  
% 28.04/3.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 28.04/3.99  ------ Proving...
% 28.04/3.99  ------ Problem Properties 
% 28.04/3.99  
% 28.04/3.99  
% 28.04/3.99  clauses                                 16
% 28.04/3.99  conjectures                             3
% 28.04/3.99  EPR                                     2
% 28.04/3.99  Horn                                    16
% 28.04/3.99  unary                                   7
% 28.04/3.99  binary                                  8
% 28.04/3.99  lits                                    26
% 28.04/3.99  lits eq                                 6
% 28.04/3.99  fd_pure                                 0
% 28.04/3.99  fd_pseudo                               0
% 28.04/3.99  fd_cond                                 0
% 28.04/3.99  fd_pseudo_cond                          1
% 28.04/3.99  AC symbols                              0
% 28.04/3.99  
% 28.04/3.99  ------ Schedule dynamic 5 is on 
% 28.04/3.99  
% 28.04/3.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 28.04/3.99  
% 28.04/3.99  
% 28.04/3.99  ------ 
% 28.04/3.99  Current options:
% 28.04/3.99  ------ 
% 28.04/3.99  
% 28.04/3.99  ------ Input Options
% 28.04/3.99  
% 28.04/3.99  --out_options                           all
% 28.04/3.99  --tptp_safe_out                         true
% 28.04/3.99  --problem_path                          ""
% 28.04/3.99  --include_path                          ""
% 28.04/3.99  --clausifier                            res/vclausify_rel
% 28.04/3.99  --clausifier_options                    --mode clausify
% 28.04/3.99  --stdin                                 false
% 28.04/3.99  --stats_out                             all
% 28.04/3.99  
% 28.04/3.99  ------ General Options
% 28.04/3.99  
% 28.04/3.99  --fof                                   false
% 28.04/3.99  --time_out_real                         305.
% 28.04/3.99  --time_out_virtual                      -1.
% 28.04/3.99  --symbol_type_check                     false
% 28.04/3.99  --clausify_out                          false
% 28.04/3.99  --sig_cnt_out                           false
% 28.04/3.99  --trig_cnt_out                          false
% 28.04/3.99  --trig_cnt_out_tolerance                1.
% 28.04/3.99  --trig_cnt_out_sk_spl                   false
% 28.04/3.99  --abstr_cl_out                          false
% 28.04/3.99  
% 28.04/3.99  ------ Global Options
% 28.04/3.99  
% 28.04/3.99  --schedule                              default
% 28.04/3.99  --add_important_lit                     false
% 28.04/3.99  --prop_solver_per_cl                    1000
% 28.04/3.99  --min_unsat_core                        false
% 28.04/3.99  --soft_assumptions                      false
% 28.04/3.99  --soft_lemma_size                       3
% 28.04/3.99  --prop_impl_unit_size                   0
% 28.04/3.99  --prop_impl_unit                        []
% 28.04/3.99  --share_sel_clauses                     true
% 28.04/3.99  --reset_solvers                         false
% 28.04/3.99  --bc_imp_inh                            [conj_cone]
% 28.04/3.99  --conj_cone_tolerance                   3.
% 28.04/3.99  --extra_neg_conj                        none
% 28.04/3.99  --large_theory_mode                     true
% 28.04/3.99  --prolific_symb_bound                   200
% 28.04/3.99  --lt_threshold                          2000
% 28.04/3.99  --clause_weak_htbl                      true
% 28.04/3.99  --gc_record_bc_elim                     false
% 28.04/3.99  
% 28.04/3.99  ------ Preprocessing Options
% 28.04/3.99  
% 28.04/3.99  --preprocessing_flag                    true
% 28.04/3.99  --time_out_prep_mult                    0.1
% 28.04/3.99  --splitting_mode                        input
% 28.04/3.99  --splitting_grd                         true
% 28.04/3.99  --splitting_cvd                         false
% 28.04/3.99  --splitting_cvd_svl                     false
% 28.04/3.99  --splitting_nvd                         32
% 28.04/3.99  --sub_typing                            true
% 28.04/3.99  --prep_gs_sim                           true
% 28.04/3.99  --prep_unflatten                        true
% 28.04/3.99  --prep_res_sim                          true
% 28.04/3.99  --prep_upred                            true
% 28.04/3.99  --prep_sem_filter                       exhaustive
% 28.04/3.99  --prep_sem_filter_out                   false
% 28.04/3.99  --pred_elim                             true
% 28.04/3.99  --res_sim_input                         true
% 28.04/3.99  --eq_ax_congr_red                       true
% 28.04/3.99  --pure_diseq_elim                       true
% 28.04/3.99  --brand_transform                       false
% 28.04/3.99  --non_eq_to_eq                          false
% 28.04/3.99  --prep_def_merge                        true
% 28.04/3.99  --prep_def_merge_prop_impl              false
% 28.04/3.99  --prep_def_merge_mbd                    true
% 28.04/3.99  --prep_def_merge_tr_red                 false
% 28.04/3.99  --prep_def_merge_tr_cl                  false
% 28.04/3.99  --smt_preprocessing                     true
% 28.04/3.99  --smt_ac_axioms                         fast
% 28.04/3.99  --preprocessed_out                      false
% 28.04/3.99  --preprocessed_stats                    false
% 28.04/3.99  
% 28.04/3.99  ------ Abstraction refinement Options
% 28.04/3.99  
% 28.04/3.99  --abstr_ref                             []
% 28.04/3.99  --abstr_ref_prep                        false
% 28.04/3.99  --abstr_ref_until_sat                   false
% 28.04/3.99  --abstr_ref_sig_restrict                funpre
% 28.04/3.99  --abstr_ref_af_restrict_to_split_sk     false
% 28.04/3.99  --abstr_ref_under                       []
% 28.04/3.99  
% 28.04/3.99  ------ SAT Options
% 28.04/3.99  
% 28.04/3.99  --sat_mode                              false
% 28.04/3.99  --sat_fm_restart_options                ""
% 28.04/3.99  --sat_gr_def                            false
% 28.04/3.99  --sat_epr_types                         true
% 28.04/3.99  --sat_non_cyclic_types                  false
% 28.04/3.99  --sat_finite_models                     false
% 28.04/3.99  --sat_fm_lemmas                         false
% 28.04/3.99  --sat_fm_prep                           false
% 28.04/3.99  --sat_fm_uc_incr                        true
% 28.04/3.99  --sat_out_model                         small
% 28.04/3.99  --sat_out_clauses                       false
% 28.04/3.99  
% 28.04/3.99  ------ QBF Options
% 28.04/3.99  
% 28.04/3.99  --qbf_mode                              false
% 28.04/3.99  --qbf_elim_univ                         false
% 28.04/3.99  --qbf_dom_inst                          none
% 28.04/3.99  --qbf_dom_pre_inst                      false
% 28.04/3.99  --qbf_sk_in                             false
% 28.04/3.99  --qbf_pred_elim                         true
% 28.04/3.99  --qbf_split                             512
% 28.04/3.99  
% 28.04/3.99  ------ BMC1 Options
% 28.04/3.99  
% 28.04/3.99  --bmc1_incremental                      false
% 28.04/3.99  --bmc1_axioms                           reachable_all
% 28.04/3.99  --bmc1_min_bound                        0
% 28.04/3.99  --bmc1_max_bound                        -1
% 28.04/3.99  --bmc1_max_bound_default                -1
% 28.04/3.99  --bmc1_symbol_reachability              true
% 28.04/3.99  --bmc1_property_lemmas                  false
% 28.04/3.99  --bmc1_k_induction                      false
% 28.04/3.99  --bmc1_non_equiv_states                 false
% 28.04/3.99  --bmc1_deadlock                         false
% 28.04/3.99  --bmc1_ucm                              false
% 28.04/3.99  --bmc1_add_unsat_core                   none
% 28.04/3.99  --bmc1_unsat_core_children              false
% 28.04/3.99  --bmc1_unsat_core_extrapolate_axioms    false
% 28.04/3.99  --bmc1_out_stat                         full
% 28.04/3.99  --bmc1_ground_init                      false
% 28.04/3.99  --bmc1_pre_inst_next_state              false
% 28.04/3.99  --bmc1_pre_inst_state                   false
% 28.04/3.99  --bmc1_pre_inst_reach_state             false
% 28.04/3.99  --bmc1_out_unsat_core                   false
% 28.04/3.99  --bmc1_aig_witness_out                  false
% 28.04/3.99  --bmc1_verbose                          false
% 28.04/3.99  --bmc1_dump_clauses_tptp                false
% 28.04/3.99  --bmc1_dump_unsat_core_tptp             false
% 28.04/3.99  --bmc1_dump_file                        -
% 28.04/3.99  --bmc1_ucm_expand_uc_limit              128
% 28.04/3.99  --bmc1_ucm_n_expand_iterations          6
% 28.04/3.99  --bmc1_ucm_extend_mode                  1
% 28.04/3.99  --bmc1_ucm_init_mode                    2
% 28.04/3.99  --bmc1_ucm_cone_mode                    none
% 28.04/3.99  --bmc1_ucm_reduced_relation_type        0
% 28.04/3.99  --bmc1_ucm_relax_model                  4
% 28.04/3.99  --bmc1_ucm_full_tr_after_sat            true
% 28.04/3.99  --bmc1_ucm_expand_neg_assumptions       false
% 28.04/3.99  --bmc1_ucm_layered_model                none
% 28.04/3.99  --bmc1_ucm_max_lemma_size               10
% 28.04/3.99  
% 28.04/3.99  ------ AIG Options
% 28.04/3.99  
% 28.04/3.99  --aig_mode                              false
% 28.04/3.99  
% 28.04/3.99  ------ Instantiation Options
% 28.04/3.99  
% 28.04/3.99  --instantiation_flag                    true
% 28.04/3.99  --inst_sos_flag                         false
% 28.04/3.99  --inst_sos_phase                        true
% 28.04/3.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 28.04/3.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 28.04/3.99  --inst_lit_sel_side                     none
% 28.04/3.99  --inst_solver_per_active                1400
% 28.04/3.99  --inst_solver_calls_frac                1.
% 28.04/3.99  --inst_passive_queue_type               priority_queues
% 28.04/3.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 28.04/3.99  --inst_passive_queues_freq              [25;2]
% 28.04/3.99  --inst_dismatching                      true
% 28.04/3.99  --inst_eager_unprocessed_to_passive     true
% 28.04/3.99  --inst_prop_sim_given                   true
% 28.04/3.99  --inst_prop_sim_new                     false
% 28.04/3.99  --inst_subs_new                         false
% 28.04/3.99  --inst_eq_res_simp                      false
% 28.04/3.99  --inst_subs_given                       false
% 28.04/3.99  --inst_orphan_elimination               true
% 28.04/3.99  --inst_learning_loop_flag               true
% 28.04/3.99  --inst_learning_start                   3000
% 28.04/3.99  --inst_learning_factor                  2
% 28.04/3.99  --inst_start_prop_sim_after_learn       3
% 28.04/3.99  --inst_sel_renew                        solver
% 28.04/3.99  --inst_lit_activity_flag                true
% 28.04/3.99  --inst_restr_to_given                   false
% 28.04/3.99  --inst_activity_threshold               500
% 28.04/3.99  --inst_out_proof                        true
% 28.04/3.99  
% 28.04/3.99  ------ Resolution Options
% 28.04/3.99  
% 28.04/3.99  --resolution_flag                       false
% 28.04/3.99  --res_lit_sel                           adaptive
% 28.04/3.99  --res_lit_sel_side                      none
% 28.04/3.99  --res_ordering                          kbo
% 28.04/3.99  --res_to_prop_solver                    active
% 28.04/3.99  --res_prop_simpl_new                    false
% 28.04/3.99  --res_prop_simpl_given                  true
% 28.04/3.99  --res_passive_queue_type                priority_queues
% 28.04/3.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 28.04/3.99  --res_passive_queues_freq               [15;5]
% 28.04/3.99  --res_forward_subs                      full
% 28.04/3.99  --res_backward_subs                     full
% 28.04/3.99  --res_forward_subs_resolution           true
% 28.04/3.99  --res_backward_subs_resolution          true
% 28.04/3.99  --res_orphan_elimination                true
% 28.04/3.99  --res_time_limit                        2.
% 28.04/3.99  --res_out_proof                         true
% 28.04/3.99  
% 28.04/3.99  ------ Superposition Options
% 28.04/3.99  
% 28.04/3.99  --superposition_flag                    true
% 28.04/3.99  --sup_passive_queue_type                priority_queues
% 28.04/3.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 28.04/3.99  --sup_passive_queues_freq               [8;1;4]
% 28.04/3.99  --demod_completeness_check              fast
% 28.04/3.99  --demod_use_ground                      true
% 28.04/3.99  --sup_to_prop_solver                    passive
% 28.04/3.99  --sup_prop_simpl_new                    true
% 28.04/3.99  --sup_prop_simpl_given                  true
% 28.04/3.99  --sup_fun_splitting                     false
% 28.04/3.99  --sup_smt_interval                      50000
% 28.04/3.99  
% 28.04/3.99  ------ Superposition Simplification Setup
% 28.04/3.99  
% 28.04/3.99  --sup_indices_passive                   []
% 28.04/3.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 28.04/3.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 28.04/3.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 28.04/3.99  --sup_full_triv                         [TrivRules;PropSubs]
% 28.04/3.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 28.04/3.99  --sup_full_bw                           [BwDemod]
% 28.04/3.99  --sup_immed_triv                        [TrivRules]
% 28.04/3.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 28.04/3.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 28.04/3.99  --sup_immed_bw_main                     []
% 28.04/3.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 28.04/3.99  --sup_input_triv                        [Unflattening;TrivRules]
% 28.04/3.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 28.04/3.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 28.04/3.99  
% 28.04/3.99  ------ Combination Options
% 28.04/3.99  
% 28.04/3.99  --comb_res_mult                         3
% 28.04/3.99  --comb_sup_mult                         2
% 28.04/3.99  --comb_inst_mult                        10
% 28.04/3.99  
% 28.04/3.99  ------ Debug Options
% 28.04/3.99  
% 28.04/3.99  --dbg_backtrace                         false
% 28.04/3.99  --dbg_dump_prop_clauses                 false
% 28.04/3.99  --dbg_dump_prop_clauses_file            -
% 28.04/3.99  --dbg_out_stat                          false
% 28.04/3.99  
% 28.04/3.99  
% 28.04/3.99  
% 28.04/3.99  
% 28.04/3.99  ------ Proving...
% 28.04/3.99  
% 28.04/3.99  
% 28.04/3.99  % SZS status Theorem for theBenchmark.p
% 28.04/3.99  
% 28.04/3.99   Resolution empty clause
% 28.04/3.99  
% 28.04/3.99  % SZS output start CNFRefutation for theBenchmark.p
% 28.04/3.99  
% 28.04/3.99  fof(f7,axiom,(
% 28.04/3.99    ! [X0,X1] : k2_xboole_0(k3_tarski(X0),k3_tarski(X1)) = k3_tarski(k2_xboole_0(X0,X1))),
% 28.04/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 28.04/3.99  
% 28.04/3.99  fof(f37,plain,(
% 28.04/3.99    ( ! [X0,X1] : (k2_xboole_0(k3_tarski(X0),k3_tarski(X1)) = k3_tarski(k2_xboole_0(X0,X1))) )),
% 28.04/3.99    inference(cnf_transformation,[],[f7])).
% 28.04/3.99  
% 28.04/3.99  fof(f6,axiom,(
% 28.04/3.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 28.04/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 28.04/3.99  
% 28.04/3.99  fof(f36,plain,(
% 28.04/3.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 28.04/3.99    inference(cnf_transformation,[],[f6])).
% 28.04/3.99  
% 28.04/3.99  fof(f51,plain,(
% 28.04/3.99    ( ! [X0,X1] : (k3_tarski(k3_tarski(k2_tarski(X0,X1))) = k3_tarski(k2_tarski(k3_tarski(X0),k3_tarski(X1)))) )),
% 28.04/3.99    inference(definition_unfolding,[],[f37,f36,f36])).
% 28.04/3.99  
% 28.04/3.99  fof(f2,axiom,(
% 28.04/3.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 28.04/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 28.04/3.99  
% 28.04/3.99  fof(f23,plain,(
% 28.04/3.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 28.04/3.99    inference(nnf_transformation,[],[f2])).
% 28.04/3.99  
% 28.04/3.99  fof(f24,plain,(
% 28.04/3.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 28.04/3.99    inference(flattening,[],[f23])).
% 28.04/3.99  
% 28.04/3.99  fof(f30,plain,(
% 28.04/3.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 28.04/3.99    inference(cnf_transformation,[],[f24])).
% 28.04/3.99  
% 28.04/3.99  fof(f53,plain,(
% 28.04/3.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 28.04/3.99    inference(equality_resolution,[],[f30])).
% 28.04/3.99  
% 28.04/3.99  fof(f3,axiom,(
% 28.04/3.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 28.04/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 28.04/3.99  
% 28.04/3.99  fof(f33,plain,(
% 28.04/3.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 28.04/3.99    inference(cnf_transformation,[],[f3])).
% 28.04/3.99  
% 28.04/3.99  fof(f48,plain,(
% 28.04/3.99    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X0,k4_xboole_0(X1,X0)))) )),
% 28.04/3.99    inference(definition_unfolding,[],[f33,f36,f36])).
% 28.04/3.99  
% 28.04/3.99  fof(f5,axiom,(
% 28.04/3.99    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 28.04/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 28.04/3.99  
% 28.04/3.99  fof(f17,plain,(
% 28.04/3.99    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 28.04/3.99    inference(ennf_transformation,[],[f5])).
% 28.04/3.99  
% 28.04/3.99  fof(f35,plain,(
% 28.04/3.99    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 28.04/3.99    inference(cnf_transformation,[],[f17])).
% 28.04/3.99  
% 28.04/3.99  fof(f50,plain,(
% 28.04/3.99    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 28.04/3.99    inference(definition_unfolding,[],[f35,f36])).
% 28.04/3.99  
% 28.04/3.99  fof(f4,axiom,(
% 28.04/3.99    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 28.04/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 28.04/3.99  
% 28.04/3.99  fof(f16,plain,(
% 28.04/3.99    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 28.04/3.99    inference(ennf_transformation,[],[f4])).
% 28.04/3.99  
% 28.04/3.99  fof(f34,plain,(
% 28.04/3.99    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 28.04/3.99    inference(cnf_transformation,[],[f16])).
% 28.04/3.99  
% 28.04/3.99  fof(f49,plain,(
% 28.04/3.99    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k3_tarski(k2_tarski(X1,X2)))) )),
% 28.04/3.99    inference(definition_unfolding,[],[f34,f36])).
% 28.04/3.99  
% 28.04/3.99  fof(f13,conjecture,(
% 28.04/3.99    ! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2))))))),
% 28.04/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 28.04/3.99  
% 28.04/3.99  fof(f14,negated_conjecture,(
% 28.04/3.99    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2))))))),
% 28.04/3.99    inference(negated_conjecture,[],[f13])).
% 28.04/3.99  
% 28.04/3.99  fof(f15,plain,(
% 28.04/3.99    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2)))))),
% 28.04/3.99    inference(pure_predicate_removal,[],[f14])).
% 28.04/3.99  
% 28.04/3.99  fof(f22,plain,(
% 28.04/3.99    ? [X0,X1] : (? [X2] : (~r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 28.04/3.99    inference(ennf_transformation,[],[f15])).
% 28.04/3.99  
% 28.04/3.99  fof(f27,plain,(
% 28.04/3.99    ( ! [X0,X1] : (? [X2] : (~r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (~r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),sK2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))) )),
% 28.04/3.99    introduced(choice_axiom,[])).
% 28.04/3.99  
% 28.04/3.99  fof(f26,plain,(
% 28.04/3.99    ? [X0,X1] : (? [X2] : (~r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (? [X2] : (~r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),X2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X2))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 28.04/3.99    introduced(choice_axiom,[])).
% 28.04/3.99  
% 28.04/3.99  fof(f28,plain,(
% 28.04/3.99    (~r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 28.04/3.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f27,f26])).
% 28.04/3.99  
% 28.04/3.99  fof(f44,plain,(
% 28.04/3.99    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 28.04/3.99    inference(cnf_transformation,[],[f28])).
% 28.04/3.99  
% 28.04/3.99  fof(f11,axiom,(
% 28.04/3.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k3_tarski(X1) = k5_setfam_1(X0,X1))),
% 28.04/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 28.04/3.99  
% 28.04/3.99  fof(f21,plain,(
% 28.04/3.99    ! [X0,X1] : (k3_tarski(X1) = k5_setfam_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 28.04/3.99    inference(ennf_transformation,[],[f11])).
% 28.04/3.99  
% 28.04/3.99  fof(f41,plain,(
% 28.04/3.99    ( ! [X0,X1] : (k3_tarski(X1) = k5_setfam_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 28.04/3.99    inference(cnf_transformation,[],[f21])).
% 28.04/3.99  
% 28.04/3.99  fof(f10,axiom,(
% 28.04/3.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)))),
% 28.04/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 28.04/3.99  
% 28.04/3.99  fof(f20,plain,(
% 28.04/3.99    ! [X0,X1] : (m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 28.04/3.99    inference(ennf_transformation,[],[f10])).
% 28.04/3.99  
% 28.04/3.99  fof(f40,plain,(
% 28.04/3.99    ( ! [X0,X1] : (m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 28.04/3.99    inference(cnf_transformation,[],[f20])).
% 28.04/3.99  
% 28.04/3.99  fof(f12,axiom,(
% 28.04/3.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 28.04/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 28.04/3.99  
% 28.04/3.99  fof(f25,plain,(
% 28.04/3.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 28.04/3.99    inference(nnf_transformation,[],[f12])).
% 28.04/3.99  
% 28.04/3.99  fof(f42,plain,(
% 28.04/3.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 28.04/3.99    inference(cnf_transformation,[],[f25])).
% 28.04/3.99  
% 28.04/3.99  fof(f9,axiom,(
% 28.04/3.99    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 28.04/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 28.04/3.99  
% 28.04/3.99  fof(f19,plain,(
% 28.04/3.99    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 28.04/3.99    inference(ennf_transformation,[],[f9])).
% 28.04/3.99  
% 28.04/3.99  fof(f39,plain,(
% 28.04/3.99    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 28.04/3.99    inference(cnf_transformation,[],[f19])).
% 28.04/3.99  
% 28.04/3.99  fof(f43,plain,(
% 28.04/3.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 28.04/3.99    inference(cnf_transformation,[],[f25])).
% 28.04/3.99  
% 28.04/3.99  fof(f8,axiom,(
% 28.04/3.99    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 28.04/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 28.04/3.99  
% 28.04/3.99  fof(f18,plain,(
% 28.04/3.99    ! [X0,X1,X2] : (m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 28.04/3.99    inference(ennf_transformation,[],[f8])).
% 28.04/3.99  
% 28.04/3.99  fof(f38,plain,(
% 28.04/3.99    ( ! [X2,X0,X1] : (m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 28.04/3.99    inference(cnf_transformation,[],[f18])).
% 28.04/3.99  
% 28.04/3.99  fof(f45,plain,(
% 28.04/3.99    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 28.04/3.99    inference(cnf_transformation,[],[f28])).
% 28.04/3.99  
% 28.04/3.99  fof(f46,plain,(
% 28.04/3.99    ~r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2)))),
% 28.04/3.99    inference(cnf_transformation,[],[f28])).
% 28.04/3.99  
% 28.04/3.99  cnf(c_7,plain,
% 28.04/3.99      ( k3_tarski(k2_tarski(k3_tarski(X0),k3_tarski(X1))) = k3_tarski(k3_tarski(k2_tarski(X0,X1))) ),
% 28.04/3.99      inference(cnf_transformation,[],[f51]) ).
% 28.04/3.99  
% 28.04/3.99  cnf(c_3,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f53]) ).
% 28.04/3.99  
% 28.04/3.99  cnf(c_697,plain,
% 28.04/3.99      ( r1_tarski(X0,X0) = iProver_top ),
% 28.04/3.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 28.04/3.99  
% 28.04/3.99  cnf(c_4,plain,
% 28.04/3.99      ( k3_tarski(k2_tarski(X0,k4_xboole_0(X1,X0))) = k3_tarski(k2_tarski(X0,X1)) ),
% 28.04/3.99      inference(cnf_transformation,[],[f48]) ).
% 28.04/3.99  
% 28.04/3.99  cnf(c_6,plain,
% 28.04/3.99      ( r1_tarski(X0,k3_tarski(k2_tarski(X1,X2)))
% 28.04/3.99      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ),
% 28.04/3.99      inference(cnf_transformation,[],[f50]) ).
% 28.04/3.99  
% 28.04/3.99  cnf(c_695,plain,
% 28.04/3.99      ( r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) = iProver_top
% 28.04/3.99      | r1_tarski(k4_xboole_0(X0,X1),X2) != iProver_top ),
% 28.04/3.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 28.04/3.99  
% 28.04/3.99  cnf(c_3413,plain,
% 28.04/3.99      ( r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) = iProver_top
% 28.04/3.99      | r1_tarski(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) != iProver_top ),
% 28.04/3.99      inference(superposition,[status(thm)],[c_4,c_695]) ).
% 28.04/3.99  
% 28.04/3.99  cnf(c_7001,plain,
% 28.04/3.99      ( r1_tarski(X0,k3_tarski(k2_tarski(X1,X0))) = iProver_top ),
% 28.04/3.99      inference(superposition,[status(thm)],[c_697,c_3413]) ).
% 28.04/3.99  
% 28.04/3.99  cnf(c_103493,plain,
% 28.04/3.99      ( r1_tarski(k3_tarski(X0),k3_tarski(k3_tarski(k2_tarski(X1,X0)))) = iProver_top ),
% 28.04/3.99      inference(superposition,[status(thm)],[c_7,c_7001]) ).
% 28.04/3.99  
% 28.04/3.99  cnf(c_5,plain,
% 28.04/3.99      ( ~ r1_tarski(X0,k3_tarski(k2_tarski(X1,X2)))
% 28.04/3.99      | r1_tarski(k4_xboole_0(X0,X1),X2) ),
% 28.04/3.99      inference(cnf_transformation,[],[f49]) ).
% 28.04/3.99  
% 28.04/3.99  cnf(c_696,plain,
% 28.04/3.99      ( r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) != iProver_top
% 28.04/3.99      | r1_tarski(k4_xboole_0(X0,X1),X2) = iProver_top ),
% 28.04/3.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 28.04/3.99  
% 28.04/3.99  cnf(c_3720,plain,
% 28.04/3.99      ( r1_tarski(X0,k3_tarski(k3_tarski(k2_tarski(X1,X2)))) != iProver_top
% 28.04/3.99      | r1_tarski(k4_xboole_0(X0,k3_tarski(X1)),k3_tarski(X2)) = iProver_top ),
% 28.04/3.99      inference(superposition,[status(thm)],[c_7,c_696]) ).
% 28.04/3.99  
% 28.04/3.99  cnf(c_10275,plain,
% 28.04/3.99      ( r1_tarski(X0,k3_tarski(k3_tarski(k2_tarski(X1,X2)))) != iProver_top
% 28.04/3.99      | r1_tarski(k4_xboole_0(X0,k3_tarski(X1)),k3_tarski(k4_xboole_0(X2,X1))) = iProver_top ),
% 28.04/3.99      inference(superposition,[status(thm)],[c_4,c_3720]) ).
% 28.04/3.99  
% 28.04/3.99  cnf(c_16,negated_conjecture,
% 28.04/3.99      ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
% 28.04/3.99      inference(cnf_transformation,[],[f44]) ).
% 28.04/3.99  
% 28.04/3.99  cnf(c_688,plain,
% 28.04/3.99      ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
% 28.04/3.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 28.04/3.99  
% 28.04/3.99  cnf(c_11,plain,
% 28.04/3.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 28.04/3.99      | k5_setfam_1(X1,X0) = k3_tarski(X0) ),
% 28.04/3.99      inference(cnf_transformation,[],[f41]) ).
% 28.04/3.99  
% 28.04/3.99  cnf(c_693,plain,
% 28.04/3.99      ( k5_setfam_1(X0,X1) = k3_tarski(X1)
% 28.04/3.99      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 28.04/3.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 28.04/3.99  
% 28.04/3.99  cnf(c_1483,plain,
% 28.04/3.99      ( k5_setfam_1(u1_struct_0(sK0),sK1) = k3_tarski(sK1) ),
% 28.04/3.99      inference(superposition,[status(thm)],[c_688,c_693]) ).
% 28.04/3.99  
% 28.04/3.99  cnf(c_10,plain,
% 28.04/3.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 28.04/3.99      | m1_subset_1(k5_setfam_1(X1,X0),k1_zfmisc_1(X1)) ),
% 28.04/3.99      inference(cnf_transformation,[],[f40]) ).
% 28.04/3.99  
% 28.04/3.99  cnf(c_694,plain,
% 28.04/3.99      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 28.04/3.99      | m1_subset_1(k5_setfam_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 28.04/3.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 28.04/3.99  
% 28.04/3.99  cnf(c_3069,plain,
% 28.04/3.99      ( m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 28.04/3.99      | m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
% 28.04/3.99      inference(superposition,[status(thm)],[c_1483,c_694]) ).
% 28.04/3.99  
% 28.04/3.99  cnf(c_17,plain,
% 28.04/3.99      ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
% 28.04/3.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 28.04/3.99  
% 28.04/3.99  cnf(c_3781,plain,
% 28.04/3.99      ( m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 28.04/3.99      inference(global_propositional_subsumption,[status(thm)],[c_3069,c_17]) ).
% 28.04/3.99  
% 28.04/3.99  cnf(c_13,plain,
% 28.04/3.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 28.04/3.99      inference(cnf_transformation,[],[f42]) ).
% 28.04/3.99  
% 28.04/3.99  cnf(c_691,plain,
% 28.04/3.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 28.04/3.99      | r1_tarski(X0,X1) = iProver_top ),
% 28.04/3.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 28.04/3.99  
% 28.04/3.99  cnf(c_3786,plain,
% 28.04/3.99      ( r1_tarski(k3_tarski(sK1),u1_struct_0(sK0)) = iProver_top ),
% 28.04/3.99      inference(superposition,[status(thm)],[c_3781,c_691]) ).
% 28.04/3.99  
% 28.04/3.99  cnf(c_9,plain,
% 28.04/3.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 28.04/3.99      | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 28.04/3.99      inference(cnf_transformation,[],[f39]) ).
% 28.04/3.99  
% 28.04/3.99  cnf(c_12,plain,
% 28.04/3.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 28.04/3.99      inference(cnf_transformation,[],[f43]) ).
% 28.04/3.99  
% 28.04/3.99  cnf(c_123,plain,
% 28.04/3.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 28.04/3.99      inference(prop_impl,[status(thm)],[c_12]) ).
% 28.04/3.99  
% 28.04/3.99  cnf(c_124,plain,
% 28.04/3.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 28.04/3.99      inference(renaming,[status(thm)],[c_123]) ).
% 28.04/3.99  
% 28.04/3.99  cnf(c_150,plain,
% 28.04/3.99      ( ~ r1_tarski(X0,X1) | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 28.04/3.99      inference(bin_hyper_res,[status(thm)],[c_9,c_124]) ).
% 28.04/3.99  
% 28.04/3.99  cnf(c_686,plain,
% 28.04/3.99      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
% 28.04/3.99      | r1_tarski(X1,X0) != iProver_top ),
% 28.04/3.99      inference(predicate_to_equality,[status(thm)],[c_150]) ).
% 28.04/3.99  
% 28.04/3.99  cnf(c_4018,plain,
% 28.04/3.99      ( k7_subset_1(u1_struct_0(sK0),k3_tarski(sK1),X0) = k4_xboole_0(k3_tarski(sK1),X0) ),
% 28.04/3.99      inference(superposition,[status(thm)],[c_3786,c_686]) ).
% 28.04/3.99  
% 28.04/3.99  cnf(c_1354,plain,
% 28.04/3.99      ( r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 28.04/3.99      inference(superposition,[status(thm)],[c_688,c_691]) ).
% 28.04/3.99  
% 28.04/3.99  cnf(c_1568,plain,
% 28.04/3.99      ( k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X0) = k4_xboole_0(sK1,X0) ),
% 28.04/3.99      inference(superposition,[status(thm)],[c_1354,c_686]) ).
% 28.04/3.99  
% 28.04/3.99  cnf(c_8,plain,
% 28.04/3.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 28.04/3.99      | m1_subset_1(k7_subset_1(X1,X0,X2),k1_zfmisc_1(X1)) ),
% 28.04/3.99      inference(cnf_transformation,[],[f38]) ).
% 28.04/3.99  
% 28.04/3.99  cnf(c_149,plain,
% 28.04/3.99      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
% 28.04/3.99      | ~ r1_tarski(X1,X0) ),
% 28.04/3.99      inference(bin_hyper_res,[status(thm)],[c_8,c_124]) ).
% 28.04/3.99  
% 28.04/3.99  cnf(c_687,plain,
% 28.04/3.99      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) = iProver_top
% 28.04/3.99      | r1_tarski(X1,X0) != iProver_top ),
% 28.04/3.99      inference(predicate_to_equality,[status(thm)],[c_149]) ).
% 28.04/3.99  
% 28.04/3.99  cnf(c_1956,plain,
% 28.04/3.99      ( m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
% 28.04/3.99      | r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 28.04/3.99      inference(superposition,[status(thm)],[c_1568,c_687]) ).
% 28.04/3.99  
% 28.04/3.99  cnf(c_905,plain,
% 28.04/3.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 28.04/3.99      | r1_tarski(X0,k1_zfmisc_1(X1)) ),
% 28.04/3.99      inference(instantiation,[status(thm)],[c_13]) ).
% 28.04/3.99  
% 28.04/3.99  cnf(c_1101,plain,
% 28.04/3.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 28.04/3.99      | r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 28.04/3.99      inference(instantiation,[status(thm)],[c_905]) ).
% 28.04/3.99  
% 28.04/3.99  cnf(c_1102,plain,
% 28.04/3.99      ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
% 28.04/3.99      | r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 28.04/3.99      inference(predicate_to_equality,[status(thm)],[c_1101]) ).
% 28.04/3.99  
% 28.04/3.99  cnf(c_2573,plain,
% 28.04/3.99      ( m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
% 28.04/3.99      inference(global_propositional_subsumption,
% 28.04/3.99                [status(thm)],
% 28.04/3.99                [c_1956,c_17,c_1102]) ).
% 28.04/3.99  
% 28.04/3.99  cnf(c_2581,plain,
% 28.04/3.99      ( k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,X0)) = k3_tarski(k4_xboole_0(sK1,X0)) ),
% 28.04/3.99      inference(superposition,[status(thm)],[c_2573,c_693]) ).
% 28.04/3.99  
% 28.04/3.99  cnf(c_15,negated_conjecture,
% 28.04/3.99      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
% 28.04/3.99      inference(cnf_transformation,[],[f45]) ).
% 28.04/3.99  
% 28.04/3.99  cnf(c_689,plain,
% 28.04/3.99      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
% 28.04/3.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 28.04/3.99  
% 28.04/3.99  cnf(c_1482,plain,
% 28.04/3.99      ( k5_setfam_1(u1_struct_0(sK0),sK2) = k3_tarski(sK2) ),
% 28.04/3.99      inference(superposition,[status(thm)],[c_689,c_693]) ).
% 28.04/3.99  
% 28.04/3.99  cnf(c_14,negated_conjecture,
% 28.04/3.99      ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))) ),
% 28.04/3.99      inference(cnf_transformation,[],[f46]) ).
% 28.04/3.99  
% 28.04/3.99  cnf(c_690,plain,
% 28.04/3.99      ( r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))) != iProver_top ),
% 28.04/3.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 28.04/3.99  
% 28.04/3.99  cnf(c_1571,plain,
% 28.04/3.99      ( r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))) != iProver_top ),
% 28.04/3.99      inference(demodulation,[status(thm)],[c_1482,c_690]) ).
% 28.04/3.99  
% 28.04/3.99  cnf(c_1696,plain,
% 28.04/3.99      ( r1_tarski(k7_subset_1(u1_struct_0(sK0),k3_tarski(sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))) != iProver_top ),
% 28.04/3.99      inference(light_normalisation,[status(thm)],[c_1571,c_1483]) ).
% 28.04/3.99  
% 28.04/3.99  cnf(c_1873,plain,
% 28.04/3.99      ( r1_tarski(k7_subset_1(u1_struct_0(sK0),k3_tarski(sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2))) != iProver_top ),
% 28.04/3.99      inference(demodulation,[status(thm)],[c_1568,c_1696]) ).
% 28.04/3.99  
% 28.04/3.99  cnf(c_2830,plain,
% 28.04/3.99      ( r1_tarski(k7_subset_1(u1_struct_0(sK0),k3_tarski(sK1),k3_tarski(sK2)),k3_tarski(k4_xboole_0(sK1,sK2))) != iProver_top ),
% 28.04/3.99      inference(demodulation,[status(thm)],[c_2581,c_1873]) ).
% 28.04/3.99  
% 28.04/3.99  cnf(c_4474,plain,
% 28.04/3.99      ( r1_tarski(k4_xboole_0(k3_tarski(sK1),k3_tarski(sK2)),k3_tarski(k4_xboole_0(sK1,sK2))) != iProver_top ),
% 28.04/3.99      inference(demodulation,[status(thm)],[c_4018,c_2830]) ).
% 28.04/3.99  
% 28.04/3.99  cnf(c_29158,plain,
% 28.04/3.99      ( r1_tarski(k3_tarski(sK1),k3_tarski(k3_tarski(k2_tarski(sK2,sK1)))) != iProver_top ),
% 28.04/3.99      inference(superposition,[status(thm)],[c_10275,c_4474]) ).
% 28.04/3.99  
% 28.04/3.99  cnf(c_104660,plain,
% 28.04/3.99      ( $false ),
% 28.04/3.99      inference(superposition,[status(thm)],[c_103493,c_29158]) ).
% 28.04/3.99  
% 28.04/3.99  
% 28.04/3.99  % SZS output end CNFRefutation for theBenchmark.p
% 28.04/3.99  
% 28.04/3.99  ------                               Statistics
% 28.04/3.99  
% 28.04/3.99  ------ General
% 28.04/3.99  
% 28.04/3.99  abstr_ref_over_cycles:                  0
% 28.04/3.99  abstr_ref_under_cycles:                 0
% 28.04/3.99  gc_basic_clause_elim:                   0
% 28.04/3.99  forced_gc_time:                         0
% 28.04/3.99  parsing_time:                           0.007
% 28.04/3.99  unif_index_cands_time:                  0.
% 28.04/3.99  unif_index_add_time:                    0.
% 28.04/3.99  orderings_time:                         0.
% 28.04/3.99  out_proof_time:                         0.01
% 28.04/3.99  total_time:                             3.361
% 28.04/3.99  num_of_symbols:                         43
% 28.04/3.99  num_of_terms:                           163451
% 28.04/3.99  
% 28.04/3.99  ------ Preprocessing
% 28.04/3.99  
% 28.04/3.99  num_of_splits:                          0
% 28.04/3.99  num_of_split_atoms:                     0
% 28.04/3.99  num_of_reused_defs:                     0
% 28.04/3.99  num_eq_ax_congr_red:                    6
% 28.04/3.99  num_of_sem_filtered_clauses:            1
% 28.04/3.99  num_of_subtypes:                        0
% 28.04/3.99  monotx_restored_types:                  0
% 28.04/3.99  sat_num_of_epr_types:                   0
% 28.04/3.99  sat_num_of_non_cyclic_types:            0
% 28.04/3.99  sat_guarded_non_collapsed_types:        0
% 28.04/3.99  num_pure_diseq_elim:                    0
% 28.04/3.99  simp_replaced_by:                       0
% 28.04/3.99  res_preprocessed:                       85
% 28.04/3.99  prep_upred:                             0
% 28.04/3.99  prep_unflattend:                        0
% 28.04/3.99  smt_new_axioms:                         0
% 28.04/3.99  pred_elim_cands:                        2
% 28.04/3.99  pred_elim:                              0
% 28.04/3.99  pred_elim_cl:                           0
% 28.04/3.99  pred_elim_cycles:                       2
% 28.04/3.99  merged_defs:                            16
% 28.04/3.99  merged_defs_ncl:                        0
% 28.04/3.99  bin_hyper_res:                          18
% 28.04/3.99  prep_cycles:                            4
% 28.04/3.99  pred_elim_time:                         0.
% 28.04/3.99  splitting_time:                         0.
% 28.04/3.99  sem_filter_time:                        0.
% 28.04/3.99  monotx_time:                            0.
% 28.04/3.99  subtype_inf_time:                       0.
% 28.04/3.99  
% 28.04/3.99  ------ Problem properties
% 28.04/3.99  
% 28.04/3.99  clauses:                                16
% 28.04/3.99  conjectures:                            3
% 28.04/3.99  epr:                                    2
% 28.04/3.99  horn:                                   16
% 28.04/3.99  ground:                                 3
% 28.04/3.99  unary:                                  7
% 28.04/3.99  binary:                                 8
% 28.04/3.99  lits:                                   26
% 28.04/3.99  lits_eq:                                6
% 28.04/3.99  fd_pure:                                0
% 28.04/3.99  fd_pseudo:                              0
% 28.04/3.99  fd_cond:                                0
% 28.04/3.99  fd_pseudo_cond:                         1
% 28.04/3.99  ac_symbols:                             0
% 28.04/3.99  
% 28.04/3.99  ------ Propositional Solver
% 28.04/3.99  
% 28.04/3.99  prop_solver_calls:                      37
% 28.04/3.99  prop_fast_solver_calls:                 920
% 28.04/3.99  smt_solver_calls:                       0
% 28.04/3.99  smt_fast_solver_calls:                  0
% 28.04/3.99  prop_num_of_clauses:                    36875
% 28.04/3.99  prop_preprocess_simplified:             43726
% 28.04/3.99  prop_fo_subsumed:                       23
% 28.04/3.99  prop_solver_time:                       0.
% 28.04/3.99  smt_solver_time:                        0.
% 28.04/3.99  smt_fast_solver_time:                   0.
% 28.04/3.99  prop_fast_solver_time:                  0.
% 28.04/3.99  prop_unsat_core_time:                   0.
% 28.04/3.99  
% 28.04/3.99  ------ QBF
% 28.04/3.99  
% 28.04/3.99  qbf_q_res:                              0
% 28.04/3.99  qbf_num_tautologies:                    0
% 28.04/3.99  qbf_prep_cycles:                        0
% 28.04/3.99  
% 28.04/3.99  ------ BMC1
% 28.04/3.99  
% 28.04/3.99  bmc1_current_bound:                     -1
% 28.04/3.99  bmc1_last_solved_bound:                 -1
% 28.04/3.99  bmc1_unsat_core_size:                   -1
% 28.04/3.99  bmc1_unsat_core_parents_size:           -1
% 28.04/3.99  bmc1_merge_next_fun:                    0
% 28.04/3.99  bmc1_unsat_core_clauses_time:           0.
% 28.04/3.99  
% 28.04/3.99  ------ Instantiation
% 28.04/3.99  
% 28.04/3.99  inst_num_of_clauses:                    6080
% 28.04/3.99  inst_num_in_passive:                    1988
% 28.04/3.99  inst_num_in_active:                     1907
% 28.04/3.99  inst_num_in_unprocessed:                2186
% 28.04/3.99  inst_num_of_loops:                      2030
% 28.04/3.99  inst_num_of_learning_restarts:          0
% 28.04/3.99  inst_num_moves_active_passive:          121
% 28.04/3.99  inst_lit_activity:                      0
% 28.04/3.99  inst_lit_activity_moves:                0
% 28.04/3.99  inst_num_tautologies:                   0
% 28.04/3.99  inst_num_prop_implied:                  0
% 28.04/3.99  inst_num_existing_simplified:           0
% 28.04/3.99  inst_num_eq_res_simplified:             0
% 28.04/3.99  inst_num_child_elim:                    0
% 28.04/3.99  inst_num_of_dismatching_blockings:      8851
% 28.04/3.99  inst_num_of_non_proper_insts:           8816
% 28.04/3.99  inst_num_of_duplicates:                 0
% 28.04/3.99  inst_inst_num_from_inst_to_res:         0
% 28.04/3.99  inst_dismatching_checking_time:         0.
% 28.04/3.99  
% 28.04/3.99  ------ Resolution
% 28.04/3.99  
% 28.04/3.99  res_num_of_clauses:                     0
% 28.04/3.99  res_num_in_passive:                     0
% 28.04/3.99  res_num_in_active:                      0
% 28.04/3.99  res_num_of_loops:                       89
% 28.04/3.99  res_forward_subset_subsumed:            695
% 28.04/3.99  res_backward_subset_subsumed:           8
% 28.04/3.99  res_forward_subsumed:                   0
% 28.04/3.99  res_backward_subsumed:                  0
% 28.04/3.99  res_forward_subsumption_resolution:     0
% 28.04/3.99  res_backward_subsumption_resolution:    0
% 28.04/3.99  res_clause_to_clause_subsumption:       68469
% 28.04/3.99  res_orphan_elimination:                 0
% 28.04/3.99  res_tautology_del:                      514
% 28.04/3.99  res_num_eq_res_simplified:              0
% 28.04/3.99  res_num_sel_changes:                    0
% 28.04/3.99  res_moves_from_active_to_pass:          0
% 28.04/3.99  
% 28.04/3.99  ------ Superposition
% 28.04/3.99  
% 28.04/3.99  sup_time_total:                         0.
% 28.04/3.99  sup_time_generating:                    0.
% 28.04/3.99  sup_time_sim_full:                      0.
% 28.04/3.99  sup_time_sim_immed:                     0.
% 28.04/3.99  
% 28.04/3.99  sup_num_of_clauses:                     6126
% 28.04/3.99  sup_num_in_active:                      372
% 28.04/3.99  sup_num_in_passive:                     5754
% 28.04/3.99  sup_num_of_loops:                       405
% 28.04/3.99  sup_fw_superposition:                   7935
% 28.04/3.99  sup_bw_superposition:                   6195
% 28.04/3.99  sup_immediate_simplified:               5808
% 28.04/3.99  sup_given_eliminated:                   19
% 28.04/3.99  comparisons_done:                       0
% 28.04/3.99  comparisons_avoided:                    0
% 28.04/3.99  
% 28.04/3.99  ------ Simplifications
% 28.04/3.99  
% 28.04/3.99  
% 28.04/3.99  sim_fw_subset_subsumed:                 81
% 28.04/3.99  sim_bw_subset_subsumed:                 6
% 28.04/3.99  sim_fw_subsumed:                        1079
% 28.04/3.99  sim_bw_subsumed:                        248
% 28.04/3.99  sim_fw_subsumption_res:                 5
% 28.04/3.99  sim_bw_subsumption_res:                 0
% 28.04/3.99  sim_tautology_del:                      14
% 28.04/3.99  sim_eq_tautology_del:                   157
% 28.04/3.99  sim_eq_res_simp:                        0
% 28.04/3.99  sim_fw_demodulated:                     3347
% 28.04/3.99  sim_bw_demodulated:                     490
% 28.04/3.99  sim_light_normalised:                   1603
% 28.04/3.99  sim_joinable_taut:                      0
% 28.04/3.99  sim_joinable_simp:                      0
% 28.04/3.99  sim_ac_normalised:                      0
% 28.04/3.99  sim_smt_subsumption:                    0
% 28.04/3.99  
%------------------------------------------------------------------------------
