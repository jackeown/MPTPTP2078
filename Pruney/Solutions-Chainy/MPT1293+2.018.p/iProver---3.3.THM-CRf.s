%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:16:10 EST 2020

% Result     : Theorem 7.12s
% Output     : CNFRefutation 7.12s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 222 expanded)
%              Number of clauses        :   75 ( 105 expanded)
%              Number of leaves         :   18 (  57 expanded)
%              Depth                    :   17
%              Number of atoms          :  208 ( 569 expanded)
%              Number of equality atoms :   90 ( 131 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_tarski(X0),k3_tarski(X1)) = k3_tarski(k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(k3_tarski(X0),k3_tarski(X1)) = k3_tarski(k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

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

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2)))
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ~ r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),sK2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,sK2)))
        & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ? [X2] :
            ( ~ r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),sK1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),sK1,X2)))
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2)))
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),X1),k5_setfam_1(u1_struct_0(sK0),X2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & l1_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2)))
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f21,f20,f19])).

fof(f34,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f22])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( r1_tarski(X2,X1)
             => m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
              | ~ r1_tarski(X2,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ r1_tarski(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f33,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k3_tarski(X1) = k5_setfam_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( k3_tarski(X1) = k5_setfam_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k3_tarski(X1) = k5_setfam_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f35,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f22])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f36,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))) ),
    inference(cnf_transformation,[],[f22])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

cnf(c_5,plain,
    ( k2_xboole_0(k3_tarski(X0),k3_tarski(X1)) = k3_tarski(k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_232,plain,
    ( k2_xboole_0(k3_tarski(X0_41),k3_tarski(X1_41)) = k3_tarski(k2_xboole_0(X0_41,X1_41)) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
    | r1_tarski(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_234,plain,
    ( ~ r1_tarski(X0_41,k2_xboole_0(X1_41,X2_41))
    | r1_tarski(k4_xboole_0(X0_41,X1_41),X2_41) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_443,plain,
    ( r1_tarski(X0_41,k2_xboole_0(X1_41,X2_41)) != iProver_top
    | r1_tarski(k4_xboole_0(X0_41,X1_41),X2_41) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_234])).

cnf(c_1627,plain,
    ( r1_tarski(X0_41,k3_tarski(k2_xboole_0(X1_41,X2_41))) != iProver_top
    | r1_tarski(k4_xboole_0(X0_41,k3_tarski(X1_41)),k3_tarski(X2_41)) = iProver_top ),
    inference(superposition,[status(thm)],[c_232,c_443])).

cnf(c_1,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_236,plain,
    ( r1_tarski(k4_xboole_0(X0_41,X1_41),X0_41) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_442,plain,
    ( r1_tarski(k4_xboole_0(X0_41,X1_41),X0_41) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_236])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_226,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_450,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_226])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ r1_tarski(X2,X0)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_13,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_133,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ r1_tarski(X2,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_13])).

cnf(c_134,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ r1_tarski(X1,X0) ),
    inference(unflattening,[status(thm)],[c_133])).

cnf(c_225,plain,
    ( ~ m1_subset_1(X0_41,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | m1_subset_1(X1_41,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ r1_tarski(X1_41,X0_41) ),
    inference(subtyping,[status(esa)],[c_134])).

cnf(c_451,plain,
    ( m1_subset_1(X0_41,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
    | m1_subset_1(X1_41,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
    | r1_tarski(X1_41,X0_41) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_225])).

cnf(c_574,plain,
    ( m1_subset_1(X0_41,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
    | r1_tarski(X0_41,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_450,c_451])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k5_setfam_1(X1,X0) = k3_tarski(X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_229,plain,
    ( ~ m1_subset_1(X0_41,k1_zfmisc_1(k1_zfmisc_1(X0_42)))
    | k5_setfam_1(X0_42,X0_41) = k3_tarski(X0_41) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_447,plain,
    ( k5_setfam_1(X0_42,X0_41) = k3_tarski(X0_41)
    | m1_subset_1(X0_41,k1_zfmisc_1(k1_zfmisc_1(X0_42))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_229])).

cnf(c_5038,plain,
    ( k5_setfam_1(u1_struct_0(sK0),X0_41) = k3_tarski(X0_41)
    | r1_tarski(X0_41,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_574,c_447])).

cnf(c_5824,plain,
    ( k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,X0_41)) = k3_tarski(k4_xboole_0(sK1,X0_41)) ),
    inference(superposition,[status(thm)],[c_442,c_5038])).

cnf(c_11,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_227,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_449,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_227])).

cnf(c_5036,plain,
    ( k5_setfam_1(u1_struct_0(sK0),sK2) = k3_tarski(sK2) ),
    inference(superposition,[status(thm)],[c_449,c_447])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_231,plain,
    ( ~ m1_subset_1(X0_41,k1_zfmisc_1(X0_42))
    | k7_subset_1(X0_42,X0_41,X1_41) = k4_xboole_0(X0_41,X1_41) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_445,plain,
    ( k7_subset_1(X0_42,X0_41,X1_41) = k4_xboole_0(X0_41,X1_41)
    | m1_subset_1(X0_41,k1_zfmisc_1(X0_42)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_231])).

cnf(c_2672,plain,
    ( k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X0_41) = k4_xboole_0(sK1,X0_41) ),
    inference(superposition,[status(thm)],[c_450,c_445])).

cnf(c_10,negated_conjecture,
    ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_228,negated_conjecture,
    ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_448,plain,
    ( r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_228])).

cnf(c_3299,plain,
    ( r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2672,c_448])).

cnf(c_5618,plain,
    ( r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5036,c_3299])).

cnf(c_5037,plain,
    ( k5_setfam_1(u1_struct_0(sK0),sK1) = k3_tarski(sK1) ),
    inference(superposition,[status(thm)],[c_450,c_447])).

cnf(c_6261,plain,
    ( r1_tarski(k7_subset_1(u1_struct_0(sK0),k3_tarski(sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5618,c_5037])).

cnf(c_6371,plain,
    ( r1_tarski(k7_subset_1(u1_struct_0(sK0),k3_tarski(sK1),k3_tarski(sK2)),k3_tarski(k4_xboole_0(sK1,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5824,c_6261])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | m1_subset_1(k5_setfam_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_230,plain,
    ( ~ m1_subset_1(X0_41,k1_zfmisc_1(k1_zfmisc_1(X0_42)))
    | m1_subset_1(k5_setfam_1(X0_42,X0_41),k1_zfmisc_1(X0_42)) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_446,plain,
    ( m1_subset_1(X0_41,k1_zfmisc_1(k1_zfmisc_1(X0_42))) != iProver_top
    | m1_subset_1(k5_setfam_1(X0_42,X0_41),k1_zfmisc_1(X0_42)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_230])).

cnf(c_5819,plain,
    ( m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5037,c_446])).

cnf(c_15,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_243,plain,
    ( X0_41 != X1_41
    | k3_tarski(X0_41) = k3_tarski(X1_41) ),
    theory(equality)).

cnf(c_249,plain,
    ( k3_tarski(sK1) = k3_tarski(sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_243])).

cnf(c_239,plain,
    ( X0_41 = X0_41 ),
    theory(equality)).

cnf(c_254,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_239])).

cnf(c_515,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | k5_setfam_1(u1_struct_0(sK0),sK1) = k3_tarski(sK1) ),
    inference(instantiation,[status(thm)],[c_229])).

cnf(c_524,plain,
    ( m1_subset_1(k5_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(instantiation,[status(thm)],[c_230])).

cnf(c_525,plain,
    ( m1_subset_1(k5_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_524])).

cnf(c_240,plain,
    ( X0_41 != X1_41
    | X2_41 != X1_41
    | X2_41 = X0_41 ),
    theory(equality)).

cnf(c_671,plain,
    ( X0_41 != X1_41
    | X0_41 = k5_setfam_1(u1_struct_0(sK0),sK1)
    | k5_setfam_1(u1_struct_0(sK0),sK1) != X1_41 ),
    inference(instantiation,[status(thm)],[c_240])).

cnf(c_800,plain,
    ( X0_41 = k5_setfam_1(u1_struct_0(sK0),sK1)
    | X0_41 != k3_tarski(sK1)
    | k5_setfam_1(u1_struct_0(sK0),sK1) != k3_tarski(sK1) ),
    inference(instantiation,[status(thm)],[c_671])).

cnf(c_934,plain,
    ( k5_setfam_1(u1_struct_0(sK0),sK1) != k3_tarski(sK1)
    | k3_tarski(sK1) = k5_setfam_1(u1_struct_0(sK0),sK1)
    | k3_tarski(sK1) != k3_tarski(sK1) ),
    inference(instantiation,[status(thm)],[c_800])).

cnf(c_245,plain,
    ( ~ m1_subset_1(X0_41,X0_42)
    | m1_subset_1(X1_41,X0_42)
    | X1_41 != X0_41 ),
    theory(equality)).

cnf(c_600,plain,
    ( m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k5_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | X0_41 != k5_setfam_1(u1_struct_0(sK0),sK1) ),
    inference(instantiation,[status(thm)],[c_245])).

cnf(c_1501,plain,
    ( ~ m1_subset_1(k5_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | k3_tarski(sK1) != k5_setfam_1(u1_struct_0(sK0),sK1) ),
    inference(instantiation,[status(thm)],[c_600])).

cnf(c_1502,plain,
    ( k3_tarski(sK1) != k5_setfam_1(u1_struct_0(sK0),sK1)
    | m1_subset_1(k5_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1501])).

cnf(c_6253,plain,
    ( m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5819,c_12,c_15,c_249,c_254,c_515,c_525,c_934,c_1502])).

cnf(c_6258,plain,
    ( k7_subset_1(u1_struct_0(sK0),k3_tarski(sK1),X0_41) = k4_xboole_0(k3_tarski(sK1),X0_41) ),
    inference(superposition,[status(thm)],[c_6253,c_445])).

cnf(c_7643,plain,
    ( r1_tarski(k4_xboole_0(k3_tarski(sK1),k3_tarski(sK2)),k3_tarski(k4_xboole_0(sK1,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6371,c_6258])).

cnf(c_17482,plain,
    ( r1_tarski(k3_tarski(sK1),k3_tarski(k2_xboole_0(sK2,k4_xboole_0(sK1,sK2)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1627,c_7643])).

cnf(c_2,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_235,plain,
    ( k2_xboole_0(X0_41,k4_xboole_0(X1_41,X0_41)) = k2_xboole_0(X0_41,X1_41) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_17498,plain,
    ( r1_tarski(k3_tarski(sK1),k3_tarski(k2_xboole_0(sK2,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_17482,c_235])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_237,plain,
    ( k2_xboole_0(X0_41,X1_41) = k2_xboole_0(X1_41,X0_41) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_4,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_233,plain,
    ( r1_tarski(X0_41,k2_xboole_0(X0_41,X1_41)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_444,plain,
    ( r1_tarski(X0_41,k2_xboole_0(X0_41,X1_41)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_233])).

cnf(c_1045,plain,
    ( r1_tarski(X0_41,k2_xboole_0(X1_41,X0_41)) = iProver_top ),
    inference(superposition,[status(thm)],[c_237,c_444])).

cnf(c_1782,plain,
    ( r1_tarski(k3_tarski(X0_41),k3_tarski(k2_xboole_0(X1_41,X0_41))) = iProver_top ),
    inference(superposition,[status(thm)],[c_232,c_1045])).

cnf(c_17555,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_17498,c_1782])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:37:17 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.12/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.12/1.49  
% 7.12/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.12/1.49  
% 7.12/1.49  ------  iProver source info
% 7.12/1.49  
% 7.12/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.12/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.12/1.49  git: non_committed_changes: false
% 7.12/1.49  git: last_make_outside_of_git: false
% 7.12/1.49  
% 7.12/1.49  ------ 
% 7.12/1.49  
% 7.12/1.49  ------ Input Options
% 7.12/1.49  
% 7.12/1.49  --out_options                           all
% 7.12/1.49  --tptp_safe_out                         true
% 7.12/1.49  --problem_path                          ""
% 7.12/1.49  --include_path                          ""
% 7.12/1.49  --clausifier                            res/vclausify_rel
% 7.12/1.49  --clausifier_options                    --mode clausify
% 7.12/1.49  --stdin                                 false
% 7.12/1.49  --stats_out                             all
% 7.12/1.49  
% 7.12/1.49  ------ General Options
% 7.12/1.49  
% 7.12/1.49  --fof                                   false
% 7.12/1.49  --time_out_real                         305.
% 7.12/1.49  --time_out_virtual                      -1.
% 7.12/1.49  --symbol_type_check                     false
% 7.12/1.49  --clausify_out                          false
% 7.12/1.49  --sig_cnt_out                           false
% 7.12/1.49  --trig_cnt_out                          false
% 7.12/1.49  --trig_cnt_out_tolerance                1.
% 7.12/1.49  --trig_cnt_out_sk_spl                   false
% 7.12/1.49  --abstr_cl_out                          false
% 7.12/1.49  
% 7.12/1.49  ------ Global Options
% 7.12/1.49  
% 7.12/1.49  --schedule                              default
% 7.12/1.49  --add_important_lit                     false
% 7.12/1.49  --prop_solver_per_cl                    1000
% 7.12/1.49  --min_unsat_core                        false
% 7.12/1.49  --soft_assumptions                      false
% 7.12/1.49  --soft_lemma_size                       3
% 7.12/1.49  --prop_impl_unit_size                   0
% 7.12/1.49  --prop_impl_unit                        []
% 7.12/1.49  --share_sel_clauses                     true
% 7.12/1.49  --reset_solvers                         false
% 7.12/1.49  --bc_imp_inh                            [conj_cone]
% 7.12/1.49  --conj_cone_tolerance                   3.
% 7.12/1.49  --extra_neg_conj                        none
% 7.12/1.49  --large_theory_mode                     true
% 7.12/1.49  --prolific_symb_bound                   200
% 7.12/1.49  --lt_threshold                          2000
% 7.12/1.49  --clause_weak_htbl                      true
% 7.12/1.49  --gc_record_bc_elim                     false
% 7.12/1.49  
% 7.12/1.49  ------ Preprocessing Options
% 7.12/1.49  
% 7.12/1.49  --preprocessing_flag                    true
% 7.12/1.49  --time_out_prep_mult                    0.1
% 7.12/1.49  --splitting_mode                        input
% 7.12/1.49  --splitting_grd                         true
% 7.12/1.49  --splitting_cvd                         false
% 7.12/1.49  --splitting_cvd_svl                     false
% 7.12/1.49  --splitting_nvd                         32
% 7.12/1.49  --sub_typing                            true
% 7.12/1.49  --prep_gs_sim                           true
% 7.12/1.49  --prep_unflatten                        true
% 7.12/1.49  --prep_res_sim                          true
% 7.12/1.49  --prep_upred                            true
% 7.12/1.49  --prep_sem_filter                       exhaustive
% 7.12/1.49  --prep_sem_filter_out                   false
% 7.12/1.49  --pred_elim                             true
% 7.12/1.49  --res_sim_input                         true
% 7.12/1.49  --eq_ax_congr_red                       true
% 7.12/1.49  --pure_diseq_elim                       true
% 7.12/1.49  --brand_transform                       false
% 7.12/1.49  --non_eq_to_eq                          false
% 7.12/1.49  --prep_def_merge                        true
% 7.12/1.49  --prep_def_merge_prop_impl              false
% 7.12/1.49  --prep_def_merge_mbd                    true
% 7.12/1.49  --prep_def_merge_tr_red                 false
% 7.12/1.49  --prep_def_merge_tr_cl                  false
% 7.12/1.49  --smt_preprocessing                     true
% 7.12/1.49  --smt_ac_axioms                         fast
% 7.12/1.49  --preprocessed_out                      false
% 7.12/1.49  --preprocessed_stats                    false
% 7.12/1.49  
% 7.12/1.49  ------ Abstraction refinement Options
% 7.12/1.49  
% 7.12/1.49  --abstr_ref                             []
% 7.12/1.49  --abstr_ref_prep                        false
% 7.12/1.49  --abstr_ref_until_sat                   false
% 7.12/1.49  --abstr_ref_sig_restrict                funpre
% 7.12/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.12/1.49  --abstr_ref_under                       []
% 7.12/1.49  
% 7.12/1.49  ------ SAT Options
% 7.12/1.49  
% 7.12/1.49  --sat_mode                              false
% 7.12/1.49  --sat_fm_restart_options                ""
% 7.12/1.49  --sat_gr_def                            false
% 7.12/1.49  --sat_epr_types                         true
% 7.12/1.49  --sat_non_cyclic_types                  false
% 7.12/1.49  --sat_finite_models                     false
% 7.12/1.49  --sat_fm_lemmas                         false
% 7.12/1.49  --sat_fm_prep                           false
% 7.12/1.49  --sat_fm_uc_incr                        true
% 7.12/1.49  --sat_out_model                         small
% 7.12/1.49  --sat_out_clauses                       false
% 7.12/1.49  
% 7.12/1.49  ------ QBF Options
% 7.12/1.49  
% 7.12/1.49  --qbf_mode                              false
% 7.12/1.49  --qbf_elim_univ                         false
% 7.12/1.49  --qbf_dom_inst                          none
% 7.12/1.49  --qbf_dom_pre_inst                      false
% 7.12/1.49  --qbf_sk_in                             false
% 7.12/1.49  --qbf_pred_elim                         true
% 7.12/1.49  --qbf_split                             512
% 7.12/1.49  
% 7.12/1.49  ------ BMC1 Options
% 7.12/1.49  
% 7.12/1.49  --bmc1_incremental                      false
% 7.12/1.49  --bmc1_axioms                           reachable_all
% 7.12/1.49  --bmc1_min_bound                        0
% 7.12/1.49  --bmc1_max_bound                        -1
% 7.12/1.49  --bmc1_max_bound_default                -1
% 7.12/1.49  --bmc1_symbol_reachability              true
% 7.12/1.49  --bmc1_property_lemmas                  false
% 7.12/1.49  --bmc1_k_induction                      false
% 7.12/1.49  --bmc1_non_equiv_states                 false
% 7.12/1.49  --bmc1_deadlock                         false
% 7.12/1.49  --bmc1_ucm                              false
% 7.12/1.49  --bmc1_add_unsat_core                   none
% 7.12/1.49  --bmc1_unsat_core_children              false
% 7.12/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.12/1.49  --bmc1_out_stat                         full
% 7.12/1.49  --bmc1_ground_init                      false
% 7.12/1.49  --bmc1_pre_inst_next_state              false
% 7.12/1.49  --bmc1_pre_inst_state                   false
% 7.12/1.49  --bmc1_pre_inst_reach_state             false
% 7.12/1.49  --bmc1_out_unsat_core                   false
% 7.12/1.49  --bmc1_aig_witness_out                  false
% 7.12/1.49  --bmc1_verbose                          false
% 7.12/1.49  --bmc1_dump_clauses_tptp                false
% 7.12/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.12/1.49  --bmc1_dump_file                        -
% 7.12/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.12/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.12/1.49  --bmc1_ucm_extend_mode                  1
% 7.12/1.49  --bmc1_ucm_init_mode                    2
% 7.12/1.49  --bmc1_ucm_cone_mode                    none
% 7.12/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.12/1.49  --bmc1_ucm_relax_model                  4
% 7.12/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.12/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.12/1.49  --bmc1_ucm_layered_model                none
% 7.12/1.49  --bmc1_ucm_max_lemma_size               10
% 7.12/1.49  
% 7.12/1.49  ------ AIG Options
% 7.12/1.49  
% 7.12/1.49  --aig_mode                              false
% 7.12/1.49  
% 7.12/1.49  ------ Instantiation Options
% 7.12/1.49  
% 7.12/1.49  --instantiation_flag                    true
% 7.12/1.49  --inst_sos_flag                         false
% 7.12/1.49  --inst_sos_phase                        true
% 7.12/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.12/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.12/1.49  --inst_lit_sel_side                     num_symb
% 7.12/1.49  --inst_solver_per_active                1400
% 7.12/1.49  --inst_solver_calls_frac                1.
% 7.12/1.49  --inst_passive_queue_type               priority_queues
% 7.12/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.12/1.49  --inst_passive_queues_freq              [25;2]
% 7.12/1.49  --inst_dismatching                      true
% 7.12/1.49  --inst_eager_unprocessed_to_passive     true
% 7.12/1.49  --inst_prop_sim_given                   true
% 7.12/1.49  --inst_prop_sim_new                     false
% 7.12/1.49  --inst_subs_new                         false
% 7.12/1.49  --inst_eq_res_simp                      false
% 7.12/1.49  --inst_subs_given                       false
% 7.12/1.49  --inst_orphan_elimination               true
% 7.12/1.49  --inst_learning_loop_flag               true
% 7.12/1.49  --inst_learning_start                   3000
% 7.12/1.49  --inst_learning_factor                  2
% 7.12/1.49  --inst_start_prop_sim_after_learn       3
% 7.12/1.49  --inst_sel_renew                        solver
% 7.12/1.49  --inst_lit_activity_flag                true
% 7.12/1.49  --inst_restr_to_given                   false
% 7.12/1.49  --inst_activity_threshold               500
% 7.12/1.49  --inst_out_proof                        true
% 7.12/1.49  
% 7.12/1.49  ------ Resolution Options
% 7.12/1.49  
% 7.12/1.49  --resolution_flag                       true
% 7.12/1.49  --res_lit_sel                           adaptive
% 7.12/1.49  --res_lit_sel_side                      none
% 7.12/1.49  --res_ordering                          kbo
% 7.12/1.49  --res_to_prop_solver                    active
% 7.12/1.49  --res_prop_simpl_new                    false
% 7.12/1.49  --res_prop_simpl_given                  true
% 7.12/1.49  --res_passive_queue_type                priority_queues
% 7.12/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.12/1.49  --res_passive_queues_freq               [15;5]
% 7.12/1.49  --res_forward_subs                      full
% 7.12/1.49  --res_backward_subs                     full
% 7.12/1.49  --res_forward_subs_resolution           true
% 7.12/1.49  --res_backward_subs_resolution          true
% 7.12/1.49  --res_orphan_elimination                true
% 7.12/1.49  --res_time_limit                        2.
% 7.12/1.49  --res_out_proof                         true
% 7.12/1.49  
% 7.12/1.49  ------ Superposition Options
% 7.12/1.49  
% 7.12/1.49  --superposition_flag                    true
% 7.12/1.49  --sup_passive_queue_type                priority_queues
% 7.12/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.12/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.12/1.49  --demod_completeness_check              fast
% 7.12/1.49  --demod_use_ground                      true
% 7.12/1.49  --sup_to_prop_solver                    passive
% 7.12/1.49  --sup_prop_simpl_new                    true
% 7.12/1.49  --sup_prop_simpl_given                  true
% 7.12/1.49  --sup_fun_splitting                     false
% 7.12/1.49  --sup_smt_interval                      50000
% 7.12/1.49  
% 7.12/1.49  ------ Superposition Simplification Setup
% 7.12/1.49  
% 7.12/1.49  --sup_indices_passive                   []
% 7.12/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.12/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.12/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.12/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.12/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.12/1.49  --sup_full_bw                           [BwDemod]
% 7.12/1.49  --sup_immed_triv                        [TrivRules]
% 7.12/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.12/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.12/1.49  --sup_immed_bw_main                     []
% 7.12/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.12/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.12/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.12/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.12/1.49  
% 7.12/1.49  ------ Combination Options
% 7.12/1.49  
% 7.12/1.49  --comb_res_mult                         3
% 7.12/1.49  --comb_sup_mult                         2
% 7.12/1.49  --comb_inst_mult                        10
% 7.12/1.49  
% 7.12/1.49  ------ Debug Options
% 7.12/1.49  
% 7.12/1.49  --dbg_backtrace                         false
% 7.12/1.49  --dbg_dump_prop_clauses                 false
% 7.12/1.49  --dbg_dump_prop_clauses_file            -
% 7.12/1.49  --dbg_out_stat                          false
% 7.12/1.49  ------ Parsing...
% 7.12/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.12/1.49  
% 7.12/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.12/1.49  
% 7.12/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.12/1.49  
% 7.12/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.12/1.49  ------ Proving...
% 7.12/1.49  ------ Problem Properties 
% 7.12/1.49  
% 7.12/1.49  
% 7.12/1.49  clauses                                 13
% 7.12/1.49  conjectures                             3
% 7.12/1.49  EPR                                     0
% 7.12/1.49  Horn                                    13
% 7.12/1.49  unary                                   8
% 7.12/1.49  binary                                  4
% 7.12/1.49  lits                                    19
% 7.12/1.49  lits eq                                 5
% 7.12/1.49  fd_pure                                 0
% 7.12/1.49  fd_pseudo                               0
% 7.12/1.49  fd_cond                                 0
% 7.12/1.49  fd_pseudo_cond                          0
% 7.12/1.49  AC symbols                              0
% 7.12/1.49  
% 7.12/1.49  ------ Schedule dynamic 5 is on 
% 7.12/1.49  
% 7.12/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.12/1.49  
% 7.12/1.49  
% 7.12/1.49  ------ 
% 7.12/1.49  Current options:
% 7.12/1.49  ------ 
% 7.12/1.49  
% 7.12/1.49  ------ Input Options
% 7.12/1.49  
% 7.12/1.49  --out_options                           all
% 7.12/1.49  --tptp_safe_out                         true
% 7.12/1.49  --problem_path                          ""
% 7.12/1.49  --include_path                          ""
% 7.12/1.49  --clausifier                            res/vclausify_rel
% 7.12/1.49  --clausifier_options                    --mode clausify
% 7.12/1.49  --stdin                                 false
% 7.12/1.49  --stats_out                             all
% 7.12/1.49  
% 7.12/1.49  ------ General Options
% 7.12/1.49  
% 7.12/1.49  --fof                                   false
% 7.12/1.49  --time_out_real                         305.
% 7.12/1.49  --time_out_virtual                      -1.
% 7.12/1.49  --symbol_type_check                     false
% 7.12/1.49  --clausify_out                          false
% 7.12/1.49  --sig_cnt_out                           false
% 7.12/1.49  --trig_cnt_out                          false
% 7.12/1.49  --trig_cnt_out_tolerance                1.
% 7.12/1.49  --trig_cnt_out_sk_spl                   false
% 7.12/1.49  --abstr_cl_out                          false
% 7.12/1.49  
% 7.12/1.49  ------ Global Options
% 7.12/1.49  
% 7.12/1.49  --schedule                              default
% 7.12/1.49  --add_important_lit                     false
% 7.12/1.49  --prop_solver_per_cl                    1000
% 7.12/1.49  --min_unsat_core                        false
% 7.12/1.49  --soft_assumptions                      false
% 7.12/1.49  --soft_lemma_size                       3
% 7.12/1.49  --prop_impl_unit_size                   0
% 7.12/1.49  --prop_impl_unit                        []
% 7.12/1.49  --share_sel_clauses                     true
% 7.12/1.49  --reset_solvers                         false
% 7.12/1.49  --bc_imp_inh                            [conj_cone]
% 7.12/1.49  --conj_cone_tolerance                   3.
% 7.12/1.49  --extra_neg_conj                        none
% 7.12/1.49  --large_theory_mode                     true
% 7.12/1.49  --prolific_symb_bound                   200
% 7.12/1.49  --lt_threshold                          2000
% 7.12/1.49  --clause_weak_htbl                      true
% 7.12/1.49  --gc_record_bc_elim                     false
% 7.12/1.49  
% 7.12/1.49  ------ Preprocessing Options
% 7.12/1.49  
% 7.12/1.49  --preprocessing_flag                    true
% 7.12/1.49  --time_out_prep_mult                    0.1
% 7.12/1.49  --splitting_mode                        input
% 7.12/1.49  --splitting_grd                         true
% 7.12/1.49  --splitting_cvd                         false
% 7.12/1.49  --splitting_cvd_svl                     false
% 7.12/1.49  --splitting_nvd                         32
% 7.12/1.49  --sub_typing                            true
% 7.12/1.49  --prep_gs_sim                           true
% 7.12/1.49  --prep_unflatten                        true
% 7.12/1.49  --prep_res_sim                          true
% 7.12/1.49  --prep_upred                            true
% 7.12/1.49  --prep_sem_filter                       exhaustive
% 7.12/1.49  --prep_sem_filter_out                   false
% 7.12/1.49  --pred_elim                             true
% 7.12/1.49  --res_sim_input                         true
% 7.12/1.49  --eq_ax_congr_red                       true
% 7.12/1.49  --pure_diseq_elim                       true
% 7.12/1.49  --brand_transform                       false
% 7.12/1.49  --non_eq_to_eq                          false
% 7.12/1.49  --prep_def_merge                        true
% 7.12/1.49  --prep_def_merge_prop_impl              false
% 7.12/1.49  --prep_def_merge_mbd                    true
% 7.12/1.49  --prep_def_merge_tr_red                 false
% 7.12/1.49  --prep_def_merge_tr_cl                  false
% 7.12/1.49  --smt_preprocessing                     true
% 7.12/1.49  --smt_ac_axioms                         fast
% 7.12/1.49  --preprocessed_out                      false
% 7.12/1.49  --preprocessed_stats                    false
% 7.12/1.49  
% 7.12/1.49  ------ Abstraction refinement Options
% 7.12/1.49  
% 7.12/1.49  --abstr_ref                             []
% 7.12/1.49  --abstr_ref_prep                        false
% 7.12/1.49  --abstr_ref_until_sat                   false
% 7.12/1.49  --abstr_ref_sig_restrict                funpre
% 7.12/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.12/1.49  --abstr_ref_under                       []
% 7.12/1.49  
% 7.12/1.49  ------ SAT Options
% 7.12/1.49  
% 7.12/1.49  --sat_mode                              false
% 7.12/1.49  --sat_fm_restart_options                ""
% 7.12/1.49  --sat_gr_def                            false
% 7.12/1.49  --sat_epr_types                         true
% 7.12/1.49  --sat_non_cyclic_types                  false
% 7.12/1.49  --sat_finite_models                     false
% 7.12/1.49  --sat_fm_lemmas                         false
% 7.12/1.49  --sat_fm_prep                           false
% 7.12/1.49  --sat_fm_uc_incr                        true
% 7.12/1.49  --sat_out_model                         small
% 7.12/1.49  --sat_out_clauses                       false
% 7.12/1.49  
% 7.12/1.49  ------ QBF Options
% 7.12/1.49  
% 7.12/1.49  --qbf_mode                              false
% 7.12/1.49  --qbf_elim_univ                         false
% 7.12/1.49  --qbf_dom_inst                          none
% 7.12/1.49  --qbf_dom_pre_inst                      false
% 7.12/1.49  --qbf_sk_in                             false
% 7.12/1.49  --qbf_pred_elim                         true
% 7.12/1.49  --qbf_split                             512
% 7.12/1.49  
% 7.12/1.49  ------ BMC1 Options
% 7.12/1.49  
% 7.12/1.49  --bmc1_incremental                      false
% 7.12/1.49  --bmc1_axioms                           reachable_all
% 7.12/1.49  --bmc1_min_bound                        0
% 7.12/1.49  --bmc1_max_bound                        -1
% 7.12/1.49  --bmc1_max_bound_default                -1
% 7.12/1.49  --bmc1_symbol_reachability              true
% 7.12/1.49  --bmc1_property_lemmas                  false
% 7.12/1.49  --bmc1_k_induction                      false
% 7.12/1.49  --bmc1_non_equiv_states                 false
% 7.12/1.49  --bmc1_deadlock                         false
% 7.12/1.49  --bmc1_ucm                              false
% 7.12/1.49  --bmc1_add_unsat_core                   none
% 7.12/1.49  --bmc1_unsat_core_children              false
% 7.12/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.12/1.49  --bmc1_out_stat                         full
% 7.12/1.49  --bmc1_ground_init                      false
% 7.12/1.49  --bmc1_pre_inst_next_state              false
% 7.12/1.49  --bmc1_pre_inst_state                   false
% 7.12/1.49  --bmc1_pre_inst_reach_state             false
% 7.12/1.49  --bmc1_out_unsat_core                   false
% 7.12/1.49  --bmc1_aig_witness_out                  false
% 7.12/1.49  --bmc1_verbose                          false
% 7.12/1.49  --bmc1_dump_clauses_tptp                false
% 7.12/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.12/1.49  --bmc1_dump_file                        -
% 7.12/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.12/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.12/1.49  --bmc1_ucm_extend_mode                  1
% 7.12/1.49  --bmc1_ucm_init_mode                    2
% 7.12/1.49  --bmc1_ucm_cone_mode                    none
% 7.12/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.12/1.49  --bmc1_ucm_relax_model                  4
% 7.12/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.12/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.12/1.49  --bmc1_ucm_layered_model                none
% 7.12/1.49  --bmc1_ucm_max_lemma_size               10
% 7.12/1.49  
% 7.12/1.49  ------ AIG Options
% 7.12/1.49  
% 7.12/1.49  --aig_mode                              false
% 7.12/1.49  
% 7.12/1.49  ------ Instantiation Options
% 7.12/1.49  
% 7.12/1.49  --instantiation_flag                    true
% 7.12/1.49  --inst_sos_flag                         false
% 7.12/1.49  --inst_sos_phase                        true
% 7.12/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.12/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.12/1.49  --inst_lit_sel_side                     none
% 7.12/1.49  --inst_solver_per_active                1400
% 7.12/1.49  --inst_solver_calls_frac                1.
% 7.12/1.49  --inst_passive_queue_type               priority_queues
% 7.12/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.12/1.49  --inst_passive_queues_freq              [25;2]
% 7.12/1.49  --inst_dismatching                      true
% 7.12/1.49  --inst_eager_unprocessed_to_passive     true
% 7.12/1.49  --inst_prop_sim_given                   true
% 7.12/1.49  --inst_prop_sim_new                     false
% 7.12/1.49  --inst_subs_new                         false
% 7.12/1.49  --inst_eq_res_simp                      false
% 7.12/1.49  --inst_subs_given                       false
% 7.12/1.49  --inst_orphan_elimination               true
% 7.12/1.49  --inst_learning_loop_flag               true
% 7.12/1.49  --inst_learning_start                   3000
% 7.12/1.49  --inst_learning_factor                  2
% 7.12/1.49  --inst_start_prop_sim_after_learn       3
% 7.12/1.49  --inst_sel_renew                        solver
% 7.12/1.49  --inst_lit_activity_flag                true
% 7.12/1.49  --inst_restr_to_given                   false
% 7.12/1.49  --inst_activity_threshold               500
% 7.12/1.49  --inst_out_proof                        true
% 7.12/1.49  
% 7.12/1.49  ------ Resolution Options
% 7.12/1.49  
% 7.12/1.49  --resolution_flag                       false
% 7.12/1.49  --res_lit_sel                           adaptive
% 7.12/1.49  --res_lit_sel_side                      none
% 7.12/1.49  --res_ordering                          kbo
% 7.12/1.49  --res_to_prop_solver                    active
% 7.12/1.49  --res_prop_simpl_new                    false
% 7.12/1.49  --res_prop_simpl_given                  true
% 7.12/1.49  --res_passive_queue_type                priority_queues
% 7.12/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.12/1.49  --res_passive_queues_freq               [15;5]
% 7.12/1.49  --res_forward_subs                      full
% 7.12/1.49  --res_backward_subs                     full
% 7.12/1.49  --res_forward_subs_resolution           true
% 7.12/1.49  --res_backward_subs_resolution          true
% 7.12/1.49  --res_orphan_elimination                true
% 7.12/1.49  --res_time_limit                        2.
% 7.12/1.49  --res_out_proof                         true
% 7.12/1.49  
% 7.12/1.49  ------ Superposition Options
% 7.12/1.49  
% 7.12/1.49  --superposition_flag                    true
% 7.12/1.49  --sup_passive_queue_type                priority_queues
% 7.12/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.12/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.12/1.49  --demod_completeness_check              fast
% 7.12/1.49  --demod_use_ground                      true
% 7.12/1.49  --sup_to_prop_solver                    passive
% 7.12/1.49  --sup_prop_simpl_new                    true
% 7.12/1.49  --sup_prop_simpl_given                  true
% 7.12/1.49  --sup_fun_splitting                     false
% 7.12/1.49  --sup_smt_interval                      50000
% 7.12/1.49  
% 7.12/1.49  ------ Superposition Simplification Setup
% 7.12/1.49  
% 7.12/1.49  --sup_indices_passive                   []
% 7.12/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.12/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.12/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.12/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.12/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.12/1.49  --sup_full_bw                           [BwDemod]
% 7.12/1.49  --sup_immed_triv                        [TrivRules]
% 7.12/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.12/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.12/1.49  --sup_immed_bw_main                     []
% 7.12/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.12/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.12/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.12/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.12/1.49  
% 7.12/1.49  ------ Combination Options
% 7.12/1.49  
% 7.12/1.49  --comb_res_mult                         3
% 7.12/1.49  --comb_sup_mult                         2
% 7.12/1.49  --comb_inst_mult                        10
% 7.12/1.49  
% 7.12/1.49  ------ Debug Options
% 7.12/1.49  
% 7.12/1.49  --dbg_backtrace                         false
% 7.12/1.49  --dbg_dump_prop_clauses                 false
% 7.12/1.49  --dbg_dump_prop_clauses_file            -
% 7.12/1.49  --dbg_out_stat                          false
% 7.12/1.49  
% 7.12/1.49  
% 7.12/1.49  
% 7.12/1.49  
% 7.12/1.49  ------ Proving...
% 7.12/1.49  
% 7.12/1.49  
% 7.12/1.49  % SZS status Theorem for theBenchmark.p
% 7.12/1.49  
% 7.12/1.49   Resolution empty clause
% 7.12/1.49  
% 7.12/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.12/1.49  
% 7.12/1.49  fof(f6,axiom,(
% 7.12/1.49    ! [X0,X1] : k2_xboole_0(k3_tarski(X0),k3_tarski(X1)) = k3_tarski(k2_xboole_0(X0,X1))),
% 7.12/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.12/1.49  
% 7.12/1.49  fof(f28,plain,(
% 7.12/1.49    ( ! [X0,X1] : (k2_xboole_0(k3_tarski(X0),k3_tarski(X1)) = k3_tarski(k2_xboole_0(X0,X1))) )),
% 7.12/1.49    inference(cnf_transformation,[],[f6])).
% 7.12/1.49  
% 7.12/1.49  fof(f4,axiom,(
% 7.12/1.49    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 7.12/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.12/1.49  
% 7.12/1.49  fof(f13,plain,(
% 7.12/1.49    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 7.12/1.49    inference(ennf_transformation,[],[f4])).
% 7.12/1.49  
% 7.12/1.49  fof(f26,plain,(
% 7.12/1.49    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 7.12/1.49    inference(cnf_transformation,[],[f13])).
% 7.12/1.49  
% 7.12/1.49  fof(f2,axiom,(
% 7.12/1.49    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 7.12/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.12/1.49  
% 7.12/1.49  fof(f24,plain,(
% 7.12/1.49    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 7.12/1.49    inference(cnf_transformation,[],[f2])).
% 7.12/1.49  
% 7.12/1.49  fof(f11,conjecture,(
% 7.12/1.49    ! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2))))))),
% 7.12/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.12/1.49  
% 7.12/1.49  fof(f12,negated_conjecture,(
% 7.12/1.49    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2))))))),
% 7.12/1.49    inference(negated_conjecture,[],[f11])).
% 7.12/1.49  
% 7.12/1.49  fof(f18,plain,(
% 7.12/1.49    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_struct_0(X0))),
% 7.12/1.49    inference(ennf_transformation,[],[f12])).
% 7.12/1.49  
% 7.12/1.49  fof(f21,plain,(
% 7.12/1.49    ( ! [X0,X1] : (? [X2] : (~r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (~r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),sK2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))) )),
% 7.12/1.49    introduced(choice_axiom,[])).
% 7.12/1.49  
% 7.12/1.49  fof(f20,plain,(
% 7.12/1.49    ( ! [X0] : (? [X1] : (? [X2] : (~r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (? [X2] : (~r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),sK1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),sK1,X2))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))) )),
% 7.12/1.49    introduced(choice_axiom,[])).
% 7.12/1.49  
% 7.12/1.49  fof(f19,plain,(
% 7.12/1.49    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k7_subset_1(u1_struct_0(X0),k5_setfam_1(u1_struct_0(X0),X1),k5_setfam_1(u1_struct_0(X0),X2)),k5_setfam_1(u1_struct_0(X0),k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),X1),k5_setfam_1(u1_struct_0(sK0),X2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_struct_0(sK0))),
% 7.12/1.49    introduced(choice_axiom,[])).
% 7.12/1.49  
% 7.12/1.49  fof(f22,plain,(
% 7.12/1.49    ((~r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_struct_0(sK0)),
% 7.12/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f21,f20,f19])).
% 7.12/1.49  
% 7.12/1.49  fof(f34,plain,(
% 7.12/1.49    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 7.12/1.49    inference(cnf_transformation,[],[f22])).
% 7.12/1.49  
% 7.12/1.49  fof(f10,axiom,(
% 7.12/1.49    ! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (r1_tarski(X2,X1) => m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))))),
% 7.12/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.12/1.49  
% 7.12/1.49  fof(f17,plain,(
% 7.12/1.49    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_struct_0(X0))),
% 7.12/1.49    inference(ennf_transformation,[],[f10])).
% 7.12/1.49  
% 7.12/1.49  fof(f32,plain,(
% 7.12/1.49    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_struct_0(X0)) )),
% 7.12/1.49    inference(cnf_transformation,[],[f17])).
% 7.12/1.49  
% 7.12/1.49  fof(f33,plain,(
% 7.12/1.49    l1_struct_0(sK0)),
% 7.12/1.49    inference(cnf_transformation,[],[f22])).
% 7.12/1.49  
% 7.12/1.49  fof(f9,axiom,(
% 7.12/1.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k3_tarski(X1) = k5_setfam_1(X0,X1))),
% 7.12/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.12/1.49  
% 7.12/1.49  fof(f16,plain,(
% 7.12/1.49    ! [X0,X1] : (k3_tarski(X1) = k5_setfam_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 7.12/1.49    inference(ennf_transformation,[],[f9])).
% 7.12/1.49  
% 7.12/1.49  fof(f31,plain,(
% 7.12/1.49    ( ! [X0,X1] : (k3_tarski(X1) = k5_setfam_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 7.12/1.49    inference(cnf_transformation,[],[f16])).
% 7.12/1.49  
% 7.12/1.49  fof(f35,plain,(
% 7.12/1.49    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 7.12/1.49    inference(cnf_transformation,[],[f22])).
% 7.12/1.49  
% 7.12/1.49  fof(f7,axiom,(
% 7.12/1.49    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 7.12/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.12/1.49  
% 7.12/1.49  fof(f14,plain,(
% 7.12/1.49    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.12/1.49    inference(ennf_transformation,[],[f7])).
% 7.12/1.49  
% 7.12/1.49  fof(f29,plain,(
% 7.12/1.49    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.12/1.49    inference(cnf_transformation,[],[f14])).
% 7.12/1.49  
% 7.12/1.49  fof(f36,plain,(
% 7.12/1.49    ~r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2)))),
% 7.12/1.49    inference(cnf_transformation,[],[f22])).
% 7.12/1.49  
% 7.12/1.49  fof(f8,axiom,(
% 7.12/1.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)))),
% 7.12/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.12/1.49  
% 7.12/1.49  fof(f15,plain,(
% 7.12/1.49    ! [X0,X1] : (m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 7.12/1.49    inference(ennf_transformation,[],[f8])).
% 7.12/1.49  
% 7.12/1.49  fof(f30,plain,(
% 7.12/1.49    ( ! [X0,X1] : (m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 7.12/1.49    inference(cnf_transformation,[],[f15])).
% 7.12/1.49  
% 7.12/1.49  fof(f3,axiom,(
% 7.12/1.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 7.12/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.12/1.49  
% 7.12/1.49  fof(f25,plain,(
% 7.12/1.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 7.12/1.49    inference(cnf_transformation,[],[f3])).
% 7.12/1.49  
% 7.12/1.49  fof(f1,axiom,(
% 7.12/1.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 7.12/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.12/1.49  
% 7.12/1.49  fof(f23,plain,(
% 7.12/1.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 7.12/1.49    inference(cnf_transformation,[],[f1])).
% 7.12/1.49  
% 7.12/1.49  fof(f5,axiom,(
% 7.12/1.49    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 7.12/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.12/1.49  
% 7.12/1.49  fof(f27,plain,(
% 7.12/1.49    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 7.12/1.49    inference(cnf_transformation,[],[f5])).
% 7.12/1.49  
% 7.12/1.49  cnf(c_5,plain,
% 7.12/1.49      ( k2_xboole_0(k3_tarski(X0),k3_tarski(X1)) = k3_tarski(k2_xboole_0(X0,X1)) ),
% 7.12/1.49      inference(cnf_transformation,[],[f28]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_232,plain,
% 7.12/1.49      ( k2_xboole_0(k3_tarski(X0_41),k3_tarski(X1_41)) = k3_tarski(k2_xboole_0(X0_41,X1_41)) ),
% 7.12/1.49      inference(subtyping,[status(esa)],[c_5]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_3,plain,
% 7.12/1.49      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2)) | r1_tarski(k4_xboole_0(X0,X1),X2) ),
% 7.12/1.49      inference(cnf_transformation,[],[f26]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_234,plain,
% 7.12/1.49      ( ~ r1_tarski(X0_41,k2_xboole_0(X1_41,X2_41))
% 7.12/1.49      | r1_tarski(k4_xboole_0(X0_41,X1_41),X2_41) ),
% 7.12/1.49      inference(subtyping,[status(esa)],[c_3]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_443,plain,
% 7.12/1.49      ( r1_tarski(X0_41,k2_xboole_0(X1_41,X2_41)) != iProver_top
% 7.12/1.49      | r1_tarski(k4_xboole_0(X0_41,X1_41),X2_41) = iProver_top ),
% 7.12/1.49      inference(predicate_to_equality,[status(thm)],[c_234]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_1627,plain,
% 7.12/1.49      ( r1_tarski(X0_41,k3_tarski(k2_xboole_0(X1_41,X2_41))) != iProver_top
% 7.12/1.49      | r1_tarski(k4_xboole_0(X0_41,k3_tarski(X1_41)),k3_tarski(X2_41)) = iProver_top ),
% 7.12/1.49      inference(superposition,[status(thm)],[c_232,c_443]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_1,plain,
% 7.12/1.49      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 7.12/1.49      inference(cnf_transformation,[],[f24]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_236,plain,
% 7.12/1.49      ( r1_tarski(k4_xboole_0(X0_41,X1_41),X0_41) ),
% 7.12/1.49      inference(subtyping,[status(esa)],[c_1]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_442,plain,
% 7.12/1.49      ( r1_tarski(k4_xboole_0(X0_41,X1_41),X0_41) = iProver_top ),
% 7.12/1.49      inference(predicate_to_equality,[status(thm)],[c_236]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_12,negated_conjecture,
% 7.12/1.49      ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
% 7.12/1.49      inference(cnf_transformation,[],[f34]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_226,negated_conjecture,
% 7.12/1.49      ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
% 7.12/1.49      inference(subtyping,[status(esa)],[c_12]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_450,plain,
% 7.12/1.49      ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
% 7.12/1.49      inference(predicate_to_equality,[status(thm)],[c_226]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_9,plain,
% 7.12/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 7.12/1.49      | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 7.12/1.49      | ~ r1_tarski(X2,X0)
% 7.12/1.49      | ~ l1_struct_0(X1) ),
% 7.12/1.49      inference(cnf_transformation,[],[f32]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_13,negated_conjecture,
% 7.12/1.49      ( l1_struct_0(sK0) ),
% 7.12/1.49      inference(cnf_transformation,[],[f33]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_133,plain,
% 7.12/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 7.12/1.49      | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 7.12/1.49      | ~ r1_tarski(X2,X0)
% 7.12/1.49      | sK0 != X1 ),
% 7.12/1.49      inference(resolution_lifted,[status(thm)],[c_9,c_13]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_134,plain,
% 7.12/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 7.12/1.49      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 7.12/1.49      | ~ r1_tarski(X1,X0) ),
% 7.12/1.49      inference(unflattening,[status(thm)],[c_133]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_225,plain,
% 7.12/1.49      ( ~ m1_subset_1(X0_41,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 7.12/1.49      | m1_subset_1(X1_41,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 7.12/1.49      | ~ r1_tarski(X1_41,X0_41) ),
% 7.12/1.49      inference(subtyping,[status(esa)],[c_134]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_451,plain,
% 7.12/1.49      ( m1_subset_1(X0_41,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top
% 7.12/1.49      | m1_subset_1(X1_41,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
% 7.12/1.49      | r1_tarski(X1_41,X0_41) != iProver_top ),
% 7.12/1.49      inference(predicate_to_equality,[status(thm)],[c_225]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_574,plain,
% 7.12/1.49      ( m1_subset_1(X0_41,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top
% 7.12/1.49      | r1_tarski(X0_41,sK1) != iProver_top ),
% 7.12/1.49      inference(superposition,[status(thm)],[c_450,c_451]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_8,plain,
% 7.12/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 7.12/1.49      | k5_setfam_1(X1,X0) = k3_tarski(X0) ),
% 7.12/1.49      inference(cnf_transformation,[],[f31]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_229,plain,
% 7.12/1.49      ( ~ m1_subset_1(X0_41,k1_zfmisc_1(k1_zfmisc_1(X0_42)))
% 7.12/1.49      | k5_setfam_1(X0_42,X0_41) = k3_tarski(X0_41) ),
% 7.12/1.49      inference(subtyping,[status(esa)],[c_8]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_447,plain,
% 7.12/1.49      ( k5_setfam_1(X0_42,X0_41) = k3_tarski(X0_41)
% 7.12/1.49      | m1_subset_1(X0_41,k1_zfmisc_1(k1_zfmisc_1(X0_42))) != iProver_top ),
% 7.12/1.49      inference(predicate_to_equality,[status(thm)],[c_229]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_5038,plain,
% 7.12/1.49      ( k5_setfam_1(u1_struct_0(sK0),X0_41) = k3_tarski(X0_41)
% 7.12/1.49      | r1_tarski(X0_41,sK1) != iProver_top ),
% 7.12/1.49      inference(superposition,[status(thm)],[c_574,c_447]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_5824,plain,
% 7.12/1.49      ( k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,X0_41)) = k3_tarski(k4_xboole_0(sK1,X0_41)) ),
% 7.12/1.49      inference(superposition,[status(thm)],[c_442,c_5038]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_11,negated_conjecture,
% 7.12/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
% 7.12/1.49      inference(cnf_transformation,[],[f35]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_227,negated_conjecture,
% 7.12/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
% 7.12/1.49      inference(subtyping,[status(esa)],[c_11]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_449,plain,
% 7.12/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
% 7.12/1.49      inference(predicate_to_equality,[status(thm)],[c_227]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_5036,plain,
% 7.12/1.49      ( k5_setfam_1(u1_struct_0(sK0),sK2) = k3_tarski(sK2) ),
% 7.12/1.49      inference(superposition,[status(thm)],[c_449,c_447]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_6,plain,
% 7.12/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.12/1.49      | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 7.12/1.49      inference(cnf_transformation,[],[f29]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_231,plain,
% 7.12/1.49      ( ~ m1_subset_1(X0_41,k1_zfmisc_1(X0_42))
% 7.12/1.49      | k7_subset_1(X0_42,X0_41,X1_41) = k4_xboole_0(X0_41,X1_41) ),
% 7.12/1.49      inference(subtyping,[status(esa)],[c_6]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_445,plain,
% 7.12/1.49      ( k7_subset_1(X0_42,X0_41,X1_41) = k4_xboole_0(X0_41,X1_41)
% 7.12/1.49      | m1_subset_1(X0_41,k1_zfmisc_1(X0_42)) != iProver_top ),
% 7.12/1.49      inference(predicate_to_equality,[status(thm)],[c_231]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_2672,plain,
% 7.12/1.49      ( k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,X0_41) = k4_xboole_0(sK1,X0_41) ),
% 7.12/1.49      inference(superposition,[status(thm)],[c_450,c_445]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_10,negated_conjecture,
% 7.12/1.49      ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))) ),
% 7.12/1.49      inference(cnf_transformation,[],[f36]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_228,negated_conjecture,
% 7.12/1.49      ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))) ),
% 7.12/1.49      inference(subtyping,[status(esa)],[c_10]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_448,plain,
% 7.12/1.49      ( r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2))) != iProver_top ),
% 7.12/1.49      inference(predicate_to_equality,[status(thm)],[c_228]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_3299,plain,
% 7.12/1.49      ( r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k5_setfam_1(u1_struct_0(sK0),sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2))) != iProver_top ),
% 7.12/1.49      inference(demodulation,[status(thm)],[c_2672,c_448]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_5618,plain,
% 7.12/1.49      ( r1_tarski(k7_subset_1(u1_struct_0(sK0),k5_setfam_1(u1_struct_0(sK0),sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2))) != iProver_top ),
% 7.12/1.49      inference(demodulation,[status(thm)],[c_5036,c_3299]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_5037,plain,
% 7.12/1.49      ( k5_setfam_1(u1_struct_0(sK0),sK1) = k3_tarski(sK1) ),
% 7.12/1.49      inference(superposition,[status(thm)],[c_450,c_447]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_6261,plain,
% 7.12/1.49      ( r1_tarski(k7_subset_1(u1_struct_0(sK0),k3_tarski(sK1),k3_tarski(sK2)),k5_setfam_1(u1_struct_0(sK0),k4_xboole_0(sK1,sK2))) != iProver_top ),
% 7.12/1.49      inference(light_normalisation,[status(thm)],[c_5618,c_5037]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_6371,plain,
% 7.12/1.49      ( r1_tarski(k7_subset_1(u1_struct_0(sK0),k3_tarski(sK1),k3_tarski(sK2)),k3_tarski(k4_xboole_0(sK1,sK2))) != iProver_top ),
% 7.12/1.49      inference(demodulation,[status(thm)],[c_5824,c_6261]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_7,plain,
% 7.12/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 7.12/1.49      | m1_subset_1(k5_setfam_1(X1,X0),k1_zfmisc_1(X1)) ),
% 7.12/1.49      inference(cnf_transformation,[],[f30]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_230,plain,
% 7.12/1.49      ( ~ m1_subset_1(X0_41,k1_zfmisc_1(k1_zfmisc_1(X0_42)))
% 7.12/1.49      | m1_subset_1(k5_setfam_1(X0_42,X0_41),k1_zfmisc_1(X0_42)) ),
% 7.12/1.49      inference(subtyping,[status(esa)],[c_7]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_446,plain,
% 7.12/1.49      ( m1_subset_1(X0_41,k1_zfmisc_1(k1_zfmisc_1(X0_42))) != iProver_top
% 7.12/1.49      | m1_subset_1(k5_setfam_1(X0_42,X0_41),k1_zfmisc_1(X0_42)) = iProver_top ),
% 7.12/1.49      inference(predicate_to_equality,[status(thm)],[c_230]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_5819,plain,
% 7.12/1.49      ( m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 7.12/1.49      | m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
% 7.12/1.49      inference(superposition,[status(thm)],[c_5037,c_446]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_15,plain,
% 7.12/1.49      ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) = iProver_top ),
% 7.12/1.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_243,plain,
% 7.12/1.49      ( X0_41 != X1_41 | k3_tarski(X0_41) = k3_tarski(X1_41) ),
% 7.12/1.49      theory(equality) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_249,plain,
% 7.12/1.49      ( k3_tarski(sK1) = k3_tarski(sK1) | sK1 != sK1 ),
% 7.12/1.49      inference(instantiation,[status(thm)],[c_243]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_239,plain,( X0_41 = X0_41 ),theory(equality) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_254,plain,
% 7.12/1.49      ( sK1 = sK1 ),
% 7.12/1.49      inference(instantiation,[status(thm)],[c_239]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_515,plain,
% 7.12/1.49      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
% 7.12/1.49      | k5_setfam_1(u1_struct_0(sK0),sK1) = k3_tarski(sK1) ),
% 7.12/1.49      inference(instantiation,[status(thm)],[c_229]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_524,plain,
% 7.12/1.49      ( m1_subset_1(k5_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 7.12/1.49      | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
% 7.12/1.49      inference(instantiation,[status(thm)],[c_230]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_525,plain,
% 7.12/1.49      ( m1_subset_1(k5_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 7.12/1.49      | m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) != iProver_top ),
% 7.12/1.49      inference(predicate_to_equality,[status(thm)],[c_524]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_240,plain,
% 7.12/1.49      ( X0_41 != X1_41 | X2_41 != X1_41 | X2_41 = X0_41 ),
% 7.12/1.49      theory(equality) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_671,plain,
% 7.12/1.49      ( X0_41 != X1_41
% 7.12/1.49      | X0_41 = k5_setfam_1(u1_struct_0(sK0),sK1)
% 7.12/1.49      | k5_setfam_1(u1_struct_0(sK0),sK1) != X1_41 ),
% 7.12/1.49      inference(instantiation,[status(thm)],[c_240]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_800,plain,
% 7.12/1.49      ( X0_41 = k5_setfam_1(u1_struct_0(sK0),sK1)
% 7.12/1.49      | X0_41 != k3_tarski(sK1)
% 7.12/1.49      | k5_setfam_1(u1_struct_0(sK0),sK1) != k3_tarski(sK1) ),
% 7.12/1.49      inference(instantiation,[status(thm)],[c_671]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_934,plain,
% 7.12/1.49      ( k5_setfam_1(u1_struct_0(sK0),sK1) != k3_tarski(sK1)
% 7.12/1.49      | k3_tarski(sK1) = k5_setfam_1(u1_struct_0(sK0),sK1)
% 7.12/1.49      | k3_tarski(sK1) != k3_tarski(sK1) ),
% 7.12/1.49      inference(instantiation,[status(thm)],[c_800]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_245,plain,
% 7.12/1.49      ( ~ m1_subset_1(X0_41,X0_42)
% 7.12/1.49      | m1_subset_1(X1_41,X0_42)
% 7.12/1.49      | X1_41 != X0_41 ),
% 7.12/1.49      theory(equality) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_600,plain,
% 7.12/1.49      ( m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.12/1.49      | ~ m1_subset_1(k5_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 7.12/1.49      | X0_41 != k5_setfam_1(u1_struct_0(sK0),sK1) ),
% 7.12/1.49      inference(instantiation,[status(thm)],[c_245]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_1501,plain,
% 7.12/1.49      ( ~ m1_subset_1(k5_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 7.12/1.49      | m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 7.12/1.49      | k3_tarski(sK1) != k5_setfam_1(u1_struct_0(sK0),sK1) ),
% 7.12/1.49      inference(instantiation,[status(thm)],[c_600]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_1502,plain,
% 7.12/1.49      ( k3_tarski(sK1) != k5_setfam_1(u1_struct_0(sK0),sK1)
% 7.12/1.49      | m1_subset_1(k5_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.12/1.49      | m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 7.12/1.49      inference(predicate_to_equality,[status(thm)],[c_1501]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_6253,plain,
% 7.12/1.49      ( m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 7.12/1.49      inference(global_propositional_subsumption,
% 7.12/1.49                [status(thm)],
% 7.12/1.49                [c_5819,c_12,c_15,c_249,c_254,c_515,c_525,c_934,c_1502]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_6258,plain,
% 7.12/1.49      ( k7_subset_1(u1_struct_0(sK0),k3_tarski(sK1),X0_41) = k4_xboole_0(k3_tarski(sK1),X0_41) ),
% 7.12/1.49      inference(superposition,[status(thm)],[c_6253,c_445]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_7643,plain,
% 7.12/1.49      ( r1_tarski(k4_xboole_0(k3_tarski(sK1),k3_tarski(sK2)),k3_tarski(k4_xboole_0(sK1,sK2))) != iProver_top ),
% 7.12/1.49      inference(demodulation,[status(thm)],[c_6371,c_6258]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_17482,plain,
% 7.12/1.49      ( r1_tarski(k3_tarski(sK1),k3_tarski(k2_xboole_0(sK2,k4_xboole_0(sK1,sK2)))) != iProver_top ),
% 7.12/1.49      inference(superposition,[status(thm)],[c_1627,c_7643]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_2,plain,
% 7.12/1.49      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 7.12/1.49      inference(cnf_transformation,[],[f25]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_235,plain,
% 7.12/1.49      ( k2_xboole_0(X0_41,k4_xboole_0(X1_41,X0_41)) = k2_xboole_0(X0_41,X1_41) ),
% 7.12/1.49      inference(subtyping,[status(esa)],[c_2]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_17498,plain,
% 7.12/1.49      ( r1_tarski(k3_tarski(sK1),k3_tarski(k2_xboole_0(sK2,sK1))) != iProver_top ),
% 7.12/1.49      inference(demodulation,[status(thm)],[c_17482,c_235]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_0,plain,
% 7.12/1.49      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 7.12/1.49      inference(cnf_transformation,[],[f23]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_237,plain,
% 7.12/1.49      ( k2_xboole_0(X0_41,X1_41) = k2_xboole_0(X1_41,X0_41) ),
% 7.12/1.49      inference(subtyping,[status(esa)],[c_0]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_4,plain,
% 7.12/1.49      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 7.12/1.49      inference(cnf_transformation,[],[f27]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_233,plain,
% 7.12/1.49      ( r1_tarski(X0_41,k2_xboole_0(X0_41,X1_41)) ),
% 7.12/1.49      inference(subtyping,[status(esa)],[c_4]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_444,plain,
% 7.12/1.49      ( r1_tarski(X0_41,k2_xboole_0(X0_41,X1_41)) = iProver_top ),
% 7.12/1.49      inference(predicate_to_equality,[status(thm)],[c_233]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_1045,plain,
% 7.12/1.49      ( r1_tarski(X0_41,k2_xboole_0(X1_41,X0_41)) = iProver_top ),
% 7.12/1.49      inference(superposition,[status(thm)],[c_237,c_444]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_1782,plain,
% 7.12/1.49      ( r1_tarski(k3_tarski(X0_41),k3_tarski(k2_xboole_0(X1_41,X0_41))) = iProver_top ),
% 7.12/1.49      inference(superposition,[status(thm)],[c_232,c_1045]) ).
% 7.12/1.49  
% 7.12/1.49  cnf(c_17555,plain,
% 7.12/1.49      ( $false ),
% 7.12/1.49      inference(forward_subsumption_resolution,[status(thm)],[c_17498,c_1782]) ).
% 7.12/1.49  
% 7.12/1.49  
% 7.12/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.12/1.49  
% 7.12/1.49  ------                               Statistics
% 7.12/1.49  
% 7.12/1.49  ------ General
% 7.12/1.49  
% 7.12/1.49  abstr_ref_over_cycles:                  0
% 7.12/1.49  abstr_ref_under_cycles:                 0
% 7.12/1.49  gc_basic_clause_elim:                   0
% 7.12/1.49  forced_gc_time:                         0
% 7.12/1.49  parsing_time:                           0.008
% 7.12/1.49  unif_index_cands_time:                  0.
% 7.12/1.49  unif_index_add_time:                    0.
% 7.12/1.49  orderings_time:                         0.
% 7.12/1.49  out_proof_time:                         0.007
% 7.12/1.49  total_time:                             0.537
% 7.12/1.49  num_of_symbols:                         47
% 7.12/1.49  num_of_terms:                           20909
% 7.12/1.49  
% 7.12/1.49  ------ Preprocessing
% 7.12/1.49  
% 7.12/1.49  num_of_splits:                          0
% 7.12/1.49  num_of_split_atoms:                     0
% 7.12/1.49  num_of_reused_defs:                     0
% 7.12/1.49  num_eq_ax_congr_red:                    11
% 7.12/1.49  num_of_sem_filtered_clauses:            1
% 7.12/1.49  num_of_subtypes:                        3
% 7.12/1.49  monotx_restored_types:                  0
% 7.12/1.49  sat_num_of_epr_types:                   0
% 7.12/1.49  sat_num_of_non_cyclic_types:            0
% 7.12/1.49  sat_guarded_non_collapsed_types:        0
% 7.12/1.49  num_pure_diseq_elim:                    0
% 7.12/1.49  simp_replaced_by:                       0
% 7.12/1.49  res_preprocessed:                       70
% 7.12/1.49  prep_upred:                             0
% 7.12/1.49  prep_unflattend:                        1
% 7.12/1.49  smt_new_axioms:                         0
% 7.12/1.49  pred_elim_cands:                        2
% 7.12/1.49  pred_elim:                              1
% 7.12/1.49  pred_elim_cl:                           1
% 7.12/1.49  pred_elim_cycles:                       3
% 7.12/1.49  merged_defs:                            0
% 7.12/1.49  merged_defs_ncl:                        0
% 7.12/1.49  bin_hyper_res:                          0
% 7.12/1.49  prep_cycles:                            4
% 7.12/1.49  pred_elim_time:                         0.001
% 7.12/1.49  splitting_time:                         0.
% 7.12/1.49  sem_filter_time:                        0.
% 7.12/1.49  monotx_time:                            0.
% 7.12/1.49  subtype_inf_time:                       0.
% 7.12/1.49  
% 7.12/1.49  ------ Problem properties
% 7.12/1.49  
% 7.12/1.49  clauses:                                13
% 7.12/1.49  conjectures:                            3
% 7.12/1.49  epr:                                    0
% 7.12/1.49  horn:                                   13
% 7.12/1.49  ground:                                 3
% 7.12/1.49  unary:                                  8
% 7.12/1.49  binary:                                 4
% 7.12/1.49  lits:                                   19
% 7.12/1.49  lits_eq:                                5
% 7.12/1.49  fd_pure:                                0
% 7.12/1.49  fd_pseudo:                              0
% 7.12/1.49  fd_cond:                                0
% 7.12/1.49  fd_pseudo_cond:                         0
% 7.12/1.49  ac_symbols:                             0
% 7.12/1.49  
% 7.12/1.49  ------ Propositional Solver
% 7.12/1.49  
% 7.12/1.49  prop_solver_calls:                      30
% 7.12/1.49  prop_fast_solver_calls:                 513
% 7.12/1.49  smt_solver_calls:                       0
% 7.12/1.49  smt_fast_solver_calls:                  0
% 7.12/1.49  prop_num_of_clauses:                    5911
% 7.12/1.49  prop_preprocess_simplified:             10242
% 7.12/1.49  prop_fo_subsumed:                       2
% 7.12/1.49  prop_solver_time:                       0.
% 7.12/1.49  smt_solver_time:                        0.
% 7.12/1.49  smt_fast_solver_time:                   0.
% 7.12/1.49  prop_fast_solver_time:                  0.
% 7.12/1.49  prop_unsat_core_time:                   0.
% 7.12/1.49  
% 7.12/1.49  ------ QBF
% 7.12/1.49  
% 7.12/1.49  qbf_q_res:                              0
% 7.12/1.49  qbf_num_tautologies:                    0
% 7.12/1.49  qbf_prep_cycles:                        0
% 7.12/1.49  
% 7.12/1.49  ------ BMC1
% 7.12/1.49  
% 7.12/1.49  bmc1_current_bound:                     -1
% 7.12/1.49  bmc1_last_solved_bound:                 -1
% 7.12/1.49  bmc1_unsat_core_size:                   -1
% 7.12/1.49  bmc1_unsat_core_parents_size:           -1
% 7.12/1.49  bmc1_merge_next_fun:                    0
% 7.12/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.12/1.49  
% 7.12/1.49  ------ Instantiation
% 7.12/1.49  
% 7.12/1.49  inst_num_of_clauses:                    1608
% 7.12/1.49  inst_num_in_passive:                    115
% 7.12/1.49  inst_num_in_active:                     715
% 7.12/1.49  inst_num_in_unprocessed:                778
% 7.12/1.49  inst_num_of_loops:                      740
% 7.12/1.49  inst_num_of_learning_restarts:          0
% 7.12/1.49  inst_num_moves_active_passive:          21
% 7.12/1.49  inst_lit_activity:                      0
% 7.12/1.49  inst_lit_activity_moves:                0
% 7.12/1.49  inst_num_tautologies:                   0
% 7.12/1.49  inst_num_prop_implied:                  0
% 7.12/1.49  inst_num_existing_simplified:           0
% 7.12/1.49  inst_num_eq_res_simplified:             0
% 7.12/1.49  inst_num_child_elim:                    0
% 7.12/1.49  inst_num_of_dismatching_blockings:      2382
% 7.12/1.49  inst_num_of_non_proper_insts:           2925
% 7.12/1.49  inst_num_of_duplicates:                 0
% 7.12/1.49  inst_inst_num_from_inst_to_res:         0
% 7.12/1.49  inst_dismatching_checking_time:         0.
% 7.12/1.49  
% 7.12/1.49  ------ Resolution
% 7.12/1.49  
% 7.12/1.49  res_num_of_clauses:                     0
% 7.12/1.49  res_num_in_passive:                     0
% 7.12/1.49  res_num_in_active:                      0
% 7.12/1.49  res_num_of_loops:                       74
% 7.12/1.49  res_forward_subset_subsumed:            384
% 7.12/1.49  res_backward_subset_subsumed:           8
% 7.12/1.49  res_forward_subsumed:                   0
% 7.12/1.49  res_backward_subsumed:                  0
% 7.12/1.49  res_forward_subsumption_resolution:     0
% 7.12/1.49  res_backward_subsumption_resolution:    0
% 7.12/1.49  res_clause_to_clause_subsumption:       5309
% 7.12/1.49  res_orphan_elimination:                 0
% 7.12/1.49  res_tautology_del:                      287
% 7.12/1.49  res_num_eq_res_simplified:              0
% 7.12/1.49  res_num_sel_changes:                    0
% 7.12/1.49  res_moves_from_active_to_pass:          0
% 7.12/1.49  
% 7.12/1.49  ------ Superposition
% 7.12/1.49  
% 7.12/1.49  sup_time_total:                         0.
% 7.12/1.49  sup_time_generating:                    0.
% 7.12/1.49  sup_time_sim_full:                      0.
% 7.12/1.49  sup_time_sim_immed:                     0.
% 7.12/1.49  
% 7.12/1.49  sup_num_of_clauses:                     699
% 7.12/1.49  sup_num_in_active:                      143
% 7.12/1.49  sup_num_in_passive:                     556
% 7.12/1.49  sup_num_of_loops:                       147
% 7.12/1.49  sup_fw_superposition:                   631
% 7.12/1.49  sup_bw_superposition:                   605
% 7.12/1.49  sup_immediate_simplified:               59
% 7.12/1.49  sup_given_eliminated:                   0
% 7.12/1.49  comparisons_done:                       0
% 7.12/1.49  comparisons_avoided:                    0
% 7.12/1.49  
% 7.12/1.49  ------ Simplifications
% 7.12/1.49  
% 7.12/1.49  
% 7.12/1.49  sim_fw_subset_subsumed:                 0
% 7.12/1.49  sim_bw_subset_subsumed:                 3
% 7.12/1.49  sim_fw_subsumed:                        27
% 7.12/1.49  sim_bw_subsumed:                        6
% 7.12/1.49  sim_fw_subsumption_res:                 1
% 7.12/1.49  sim_bw_subsumption_res:                 0
% 7.12/1.49  sim_tautology_del:                      0
% 7.12/1.49  sim_eq_tautology_del:                   3
% 7.12/1.49  sim_eq_res_simp:                        0
% 7.12/1.49  sim_fw_demodulated:                     17
% 7.12/1.49  sim_bw_demodulated:                     3
% 7.12/1.49  sim_light_normalised:                   22
% 7.12/1.49  sim_joinable_taut:                      0
% 7.12/1.49  sim_joinable_simp:                      0
% 7.12/1.49  sim_ac_normalised:                      0
% 7.12/1.49  sim_smt_subsumption:                    0
% 7.12/1.49  
%------------------------------------------------------------------------------
