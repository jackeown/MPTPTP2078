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
% DateTime   : Thu Dec  3 12:13:52 EST 2020

% Result     : Theorem 7.65s
% Output     : CNFRefutation 7.65s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 341 expanded)
%              Number of clauses        :   81 ( 152 expanded)
%              Number of leaves         :   12 (  78 expanded)
%              Depth                    :   20
%              Number of atoms          :  281 (1019 expanded)
%              Number of equality atoms :   81 ( 122 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f9,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)))
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,sK2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,sK2)))
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ~ r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,sK1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),sK1,X2)))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)))
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f24,f23,f22])).

fof(f35,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f36,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f25])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f37,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f25])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f14])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f38,plain,(
    ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(cnf_transformation,[],[f25])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f11])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_12,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_175,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_12])).

cnf(c_176,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X1,X0)
    | r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_175])).

cnf(c_328,plain,
    ( ~ m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1_40,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X1_40,X0_40)
    | r1_tarski(k1_tops_1(sK0,X1_40),k1_tops_1(sK0,X0_40)) ),
    inference(subtyping,[status(esa)],[c_176])).

cnf(c_669,plain,
    ( m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1_40,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X1_40,X0_40) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X1_40),k1_tops_1(sK0,X0_40)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_328])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(k2_xboole_0(X2,X0),X1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_334,plain,
    ( ~ r1_tarski(X0_40,X1_40)
    | ~ r1_tarski(X2_40,X1_40)
    | r1_tarski(k2_xboole_0(X2_40,X0_40),X1_40) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_663,plain,
    ( r1_tarski(X0_40,X1_40) != iProver_top
    | r1_tarski(X2_40,X1_40) != iProver_top
    | r1_tarski(k2_xboole_0(X2_40,X0_40),X1_40) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_334])).

cnf(c_11,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_329,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_668,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_329])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_193,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_12])).

cnf(c_194,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_193])).

cnf(c_327,plain,
    ( ~ m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k1_tops_1(sK0,X0_40),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_194])).

cnf(c_670,plain,
    ( m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k1_tops_1(sK0,X0_40),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_327])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_332,plain,
    ( ~ m1_subset_1(X0_40,k1_zfmisc_1(X1_40))
    | r1_tarski(X0_40,X1_40) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_665,plain,
    ( m1_subset_1(X0_40,k1_zfmisc_1(X1_40)) != iProver_top
    | r1_tarski(X0_40,X1_40) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_332])).

cnf(c_1229,plain,
    ( m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0_40),u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_670,c_665])).

cnf(c_10,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_330,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_667,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_330])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_5,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_99,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_5])).

cnf(c_100,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_99])).

cnf(c_123,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,X1)
    | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_4,c_100])).

cnf(c_255,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_5])).

cnf(c_256,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_255])).

cnf(c_278,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_123,c_256])).

cnf(c_326,plain,
    ( ~ r1_tarski(X0_40,X1_40)
    | ~ r1_tarski(X2_40,X1_40)
    | k4_subset_1(X1_40,X2_40,X0_40) = k2_xboole_0(X2_40,X0_40) ),
    inference(subtyping,[status(esa)],[c_278])).

cnf(c_671,plain,
    ( k4_subset_1(X0_40,X1_40,X2_40) = k2_xboole_0(X1_40,X2_40)
    | r1_tarski(X2_40,X0_40) != iProver_top
    | r1_tarski(X1_40,X0_40) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_326])).

cnf(c_1899,plain,
    ( k4_subset_1(u1_struct_0(sK0),X0_40,k1_tops_1(sK0,X1_40)) = k2_xboole_0(X0_40,k1_tops_1(sK0,X1_40))
    | m1_subset_1(X1_40,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0_40,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1229,c_671])).

cnf(c_9656,plain,
    ( k4_subset_1(u1_struct_0(sK0),X0_40,k1_tops_1(sK0,sK2)) = k2_xboole_0(X0_40,k1_tops_1(sK0,sK2))
    | r1_tarski(X0_40,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_667,c_1899])).

cnf(c_9814,plain,
    ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X0_40),k1_tops_1(sK0,sK2)) = k2_xboole_0(k1_tops_1(sK0,X0_40),k1_tops_1(sK0,sK2))
    | m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1229,c_9656])).

cnf(c_10695,plain,
    ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
    inference(superposition,[status(thm)],[c_668,c_9814])).

cnf(c_1228,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_668,c_665])).

cnf(c_1227,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_667,c_665])).

cnf(c_1893,plain,
    ( k4_subset_1(u1_struct_0(sK0),X0_40,sK2) = k2_xboole_0(X0_40,sK2)
    | r1_tarski(X0_40,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1227,c_671])).

cnf(c_2594,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_1228,c_1893])).

cnf(c_9,negated_conjecture,
    ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_331,negated_conjecture,
    ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_666,plain,
    ( r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_331])).

cnf(c_2694,plain,
    ( r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2594,c_666])).

cnf(c_10953,plain,
    ( r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10695,c_2694])).

cnf(c_11803,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_663,c_10953])).

cnf(c_14,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_15,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_754,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_332])).

cnf(c_755,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_754])).

cnf(c_757,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_332])).

cnf(c_758,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_757])).

cnf(c_846,plain,
    ( ~ r1_tarski(X0_40,u1_struct_0(sK0))
    | r1_tarski(k2_xboole_0(X0_40,sK2),u1_struct_0(sK0))
    | ~ r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_334])).

cnf(c_848,plain,
    ( r1_tarski(X0_40,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(k2_xboole_0(X0_40,sK2),u1_struct_0(sK0)) = iProver_top
    | r1_tarski(sK2,u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_846])).

cnf(c_850,plain,
    ( r1_tarski(k2_xboole_0(sK1,sK2),u1_struct_0(sK0)) = iProver_top
    | r1_tarski(sK2,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(sK1,u1_struct_0(sK0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_848])).

cnf(c_333,plain,
    ( m1_subset_1(X0_40,k1_zfmisc_1(X1_40))
    | ~ r1_tarski(X0_40,X1_40) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_945,plain,
    ( m1_subset_1(k2_xboole_0(X0_40,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k2_xboole_0(X0_40,sK2),u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_333])).

cnf(c_946,plain,
    ( m1_subset_1(k2_xboole_0(X0_40,sK2),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | r1_tarski(k2_xboole_0(X0_40,sK2),u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_945])).

cnf(c_948,plain,
    ( m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | r1_tarski(k2_xboole_0(sK1,sK2),u1_struct_0(sK0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_946])).

cnf(c_744,plain,
    ( ~ m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_xboole_0(X0_40,X1_40),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0_40,k2_xboole_0(X0_40,X1_40))
    | r1_tarski(k1_tops_1(sK0,X0_40),k1_tops_1(sK0,k2_xboole_0(X0_40,X1_40))) ),
    inference(instantiation,[status(thm)],[c_328])).

cnf(c_1315,plain,
    ( ~ m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_xboole_0(X0_40,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0_40,k2_xboole_0(X0_40,sK2))
    | r1_tarski(k1_tops_1(sK0,X0_40),k1_tops_1(sK0,k2_xboole_0(X0_40,sK2))) ),
    inference(instantiation,[status(thm)],[c_744])).

cnf(c_1316,plain,
    ( m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_xboole_0(X0_40,sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0_40,k2_xboole_0(X0_40,sK2)) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0_40),k1_tops_1(sK0,k2_xboole_0(X0_40,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1315])).

cnf(c_1318,plain,
    ( m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) = iProver_top
    | r1_tarski(sK1,k2_xboole_0(sK1,sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1316])).

cnf(c_2,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_335,plain,
    ( r1_tarski(X0_40,k2_xboole_0(X0_40,X1_40)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1426,plain,
    ( r1_tarski(X0_40,k2_xboole_0(X0_40,sK2)) ),
    inference(instantiation,[status(thm)],[c_335])).

cnf(c_1427,plain,
    ( r1_tarski(X0_40,k2_xboole_0(X0_40,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1426])).

cnf(c_1429,plain,
    ( r1_tarski(sK1,k2_xboole_0(sK1,sK2)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1427])).

cnf(c_13063,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11803,c_14,c_15,c_755,c_758,c_850,c_948,c_1318,c_1429])).

cnf(c_13068,plain,
    ( m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK2,k2_xboole_0(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_669,c_13063])).

cnf(c_14204,plain,
    ( r1_tarski(sK2,k2_xboole_0(sK1,sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13068,c_14,c_15,c_755,c_758,c_850,c_948])).

cnf(c_0,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_337,plain,
    ( r1_tarski(k4_xboole_0(X0_40,X1_40),X0_40) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_660,plain,
    ( r1_tarski(k4_xboole_0(X0_40,X1_40),X0_40) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_337])).

cnf(c_1,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2))
    | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_336,plain,
    ( r1_tarski(X0_40,k2_xboole_0(X1_40,X2_40))
    | ~ r1_tarski(k4_xboole_0(X0_40,X1_40),X2_40) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_661,plain,
    ( r1_tarski(X0_40,k2_xboole_0(X1_40,X2_40)) = iProver_top
    | r1_tarski(k4_xboole_0(X0_40,X1_40),X2_40) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_336])).

cnf(c_1215,plain,
    ( r1_tarski(X0_40,k2_xboole_0(X1_40,X0_40)) = iProver_top ),
    inference(superposition,[status(thm)],[c_660,c_661])).

cnf(c_14209,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_14204,c_1215])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:21:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 7.65/1.51  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.65/1.51  
% 7.65/1.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.65/1.51  
% 7.65/1.51  ------  iProver source info
% 7.65/1.51  
% 7.65/1.51  git: date: 2020-06-30 10:37:57 +0100
% 7.65/1.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.65/1.51  git: non_committed_changes: false
% 7.65/1.51  git: last_make_outside_of_git: false
% 7.65/1.51  
% 7.65/1.51  ------ 
% 7.65/1.51  
% 7.65/1.51  ------ Input Options
% 7.65/1.51  
% 7.65/1.51  --out_options                           all
% 7.65/1.51  --tptp_safe_out                         true
% 7.65/1.51  --problem_path                          ""
% 7.65/1.51  --include_path                          ""
% 7.65/1.51  --clausifier                            res/vclausify_rel
% 7.65/1.51  --clausifier_options                    --mode clausify
% 7.65/1.51  --stdin                                 false
% 7.65/1.51  --stats_out                             all
% 7.65/1.51  
% 7.65/1.51  ------ General Options
% 7.65/1.51  
% 7.65/1.51  --fof                                   false
% 7.65/1.51  --time_out_real                         305.
% 7.65/1.51  --time_out_virtual                      -1.
% 7.65/1.51  --symbol_type_check                     false
% 7.65/1.51  --clausify_out                          false
% 7.65/1.51  --sig_cnt_out                           false
% 7.65/1.51  --trig_cnt_out                          false
% 7.65/1.51  --trig_cnt_out_tolerance                1.
% 7.65/1.51  --trig_cnt_out_sk_spl                   false
% 7.65/1.51  --abstr_cl_out                          false
% 7.65/1.51  
% 7.65/1.51  ------ Global Options
% 7.65/1.51  
% 7.65/1.51  --schedule                              default
% 7.65/1.51  --add_important_lit                     false
% 7.65/1.51  --prop_solver_per_cl                    1000
% 7.65/1.51  --min_unsat_core                        false
% 7.65/1.51  --soft_assumptions                      false
% 7.65/1.51  --soft_lemma_size                       3
% 7.65/1.51  --prop_impl_unit_size                   0
% 7.65/1.51  --prop_impl_unit                        []
% 7.65/1.51  --share_sel_clauses                     true
% 7.65/1.51  --reset_solvers                         false
% 7.65/1.51  --bc_imp_inh                            [conj_cone]
% 7.65/1.51  --conj_cone_tolerance                   3.
% 7.65/1.51  --extra_neg_conj                        none
% 7.65/1.51  --large_theory_mode                     true
% 7.65/1.51  --prolific_symb_bound                   200
% 7.65/1.51  --lt_threshold                          2000
% 7.65/1.51  --clause_weak_htbl                      true
% 7.65/1.51  --gc_record_bc_elim                     false
% 7.65/1.51  
% 7.65/1.51  ------ Preprocessing Options
% 7.65/1.51  
% 7.65/1.51  --preprocessing_flag                    true
% 7.65/1.51  --time_out_prep_mult                    0.1
% 7.65/1.51  --splitting_mode                        input
% 7.65/1.51  --splitting_grd                         true
% 7.65/1.51  --splitting_cvd                         false
% 7.65/1.51  --splitting_cvd_svl                     false
% 7.65/1.51  --splitting_nvd                         32
% 7.65/1.51  --sub_typing                            true
% 7.65/1.51  --prep_gs_sim                           true
% 7.65/1.51  --prep_unflatten                        true
% 7.65/1.51  --prep_res_sim                          true
% 7.65/1.51  --prep_upred                            true
% 7.65/1.51  --prep_sem_filter                       exhaustive
% 7.65/1.51  --prep_sem_filter_out                   false
% 7.65/1.51  --pred_elim                             true
% 7.65/1.51  --res_sim_input                         true
% 7.65/1.51  --eq_ax_congr_red                       true
% 7.65/1.51  --pure_diseq_elim                       true
% 7.65/1.51  --brand_transform                       false
% 7.65/1.51  --non_eq_to_eq                          false
% 7.65/1.51  --prep_def_merge                        true
% 7.65/1.51  --prep_def_merge_prop_impl              false
% 7.65/1.51  --prep_def_merge_mbd                    true
% 7.65/1.51  --prep_def_merge_tr_red                 false
% 7.65/1.51  --prep_def_merge_tr_cl                  false
% 7.65/1.51  --smt_preprocessing                     true
% 7.65/1.51  --smt_ac_axioms                         fast
% 7.65/1.51  --preprocessed_out                      false
% 7.65/1.51  --preprocessed_stats                    false
% 7.65/1.51  
% 7.65/1.51  ------ Abstraction refinement Options
% 7.65/1.51  
% 7.65/1.51  --abstr_ref                             []
% 7.65/1.51  --abstr_ref_prep                        false
% 7.65/1.51  --abstr_ref_until_sat                   false
% 7.65/1.51  --abstr_ref_sig_restrict                funpre
% 7.65/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 7.65/1.51  --abstr_ref_under                       []
% 7.65/1.51  
% 7.65/1.51  ------ SAT Options
% 7.65/1.51  
% 7.65/1.51  --sat_mode                              false
% 7.65/1.51  --sat_fm_restart_options                ""
% 7.65/1.51  --sat_gr_def                            false
% 7.65/1.51  --sat_epr_types                         true
% 7.65/1.51  --sat_non_cyclic_types                  false
% 7.65/1.51  --sat_finite_models                     false
% 7.65/1.51  --sat_fm_lemmas                         false
% 7.65/1.51  --sat_fm_prep                           false
% 7.65/1.51  --sat_fm_uc_incr                        true
% 7.65/1.51  --sat_out_model                         small
% 7.65/1.51  --sat_out_clauses                       false
% 7.65/1.51  
% 7.65/1.51  ------ QBF Options
% 7.65/1.51  
% 7.65/1.51  --qbf_mode                              false
% 7.65/1.51  --qbf_elim_univ                         false
% 7.65/1.51  --qbf_dom_inst                          none
% 7.65/1.51  --qbf_dom_pre_inst                      false
% 7.65/1.51  --qbf_sk_in                             false
% 7.65/1.51  --qbf_pred_elim                         true
% 7.65/1.51  --qbf_split                             512
% 7.65/1.51  
% 7.65/1.51  ------ BMC1 Options
% 7.65/1.51  
% 7.65/1.51  --bmc1_incremental                      false
% 7.65/1.51  --bmc1_axioms                           reachable_all
% 7.65/1.51  --bmc1_min_bound                        0
% 7.65/1.51  --bmc1_max_bound                        -1
% 7.65/1.51  --bmc1_max_bound_default                -1
% 7.65/1.51  --bmc1_symbol_reachability              true
% 7.65/1.51  --bmc1_property_lemmas                  false
% 7.65/1.51  --bmc1_k_induction                      false
% 7.65/1.51  --bmc1_non_equiv_states                 false
% 7.65/1.51  --bmc1_deadlock                         false
% 7.65/1.51  --bmc1_ucm                              false
% 7.65/1.51  --bmc1_add_unsat_core                   none
% 7.65/1.51  --bmc1_unsat_core_children              false
% 7.65/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 7.65/1.51  --bmc1_out_stat                         full
% 7.65/1.51  --bmc1_ground_init                      false
% 7.65/1.51  --bmc1_pre_inst_next_state              false
% 7.65/1.51  --bmc1_pre_inst_state                   false
% 7.65/1.51  --bmc1_pre_inst_reach_state             false
% 7.65/1.51  --bmc1_out_unsat_core                   false
% 7.65/1.51  --bmc1_aig_witness_out                  false
% 7.65/1.51  --bmc1_verbose                          false
% 7.65/1.51  --bmc1_dump_clauses_tptp                false
% 7.65/1.51  --bmc1_dump_unsat_core_tptp             false
% 7.65/1.51  --bmc1_dump_file                        -
% 7.65/1.51  --bmc1_ucm_expand_uc_limit              128
% 7.65/1.51  --bmc1_ucm_n_expand_iterations          6
% 7.65/1.51  --bmc1_ucm_extend_mode                  1
% 7.65/1.51  --bmc1_ucm_init_mode                    2
% 7.65/1.51  --bmc1_ucm_cone_mode                    none
% 7.65/1.51  --bmc1_ucm_reduced_relation_type        0
% 7.65/1.51  --bmc1_ucm_relax_model                  4
% 7.65/1.51  --bmc1_ucm_full_tr_after_sat            true
% 7.65/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 7.65/1.51  --bmc1_ucm_layered_model                none
% 7.65/1.51  --bmc1_ucm_max_lemma_size               10
% 7.65/1.51  
% 7.65/1.51  ------ AIG Options
% 7.65/1.51  
% 7.65/1.51  --aig_mode                              false
% 7.65/1.51  
% 7.65/1.51  ------ Instantiation Options
% 7.65/1.51  
% 7.65/1.51  --instantiation_flag                    true
% 7.65/1.51  --inst_sos_flag                         false
% 7.65/1.51  --inst_sos_phase                        true
% 7.65/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.65/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.65/1.51  --inst_lit_sel_side                     num_symb
% 7.65/1.51  --inst_solver_per_active                1400
% 7.65/1.51  --inst_solver_calls_frac                1.
% 7.65/1.51  --inst_passive_queue_type               priority_queues
% 7.65/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.65/1.51  --inst_passive_queues_freq              [25;2]
% 7.65/1.51  --inst_dismatching                      true
% 7.65/1.51  --inst_eager_unprocessed_to_passive     true
% 7.65/1.51  --inst_prop_sim_given                   true
% 7.65/1.51  --inst_prop_sim_new                     false
% 7.65/1.51  --inst_subs_new                         false
% 7.65/1.51  --inst_eq_res_simp                      false
% 7.65/1.51  --inst_subs_given                       false
% 7.65/1.51  --inst_orphan_elimination               true
% 7.65/1.51  --inst_learning_loop_flag               true
% 7.65/1.51  --inst_learning_start                   3000
% 7.65/1.51  --inst_learning_factor                  2
% 7.65/1.51  --inst_start_prop_sim_after_learn       3
% 7.65/1.51  --inst_sel_renew                        solver
% 7.65/1.51  --inst_lit_activity_flag                true
% 7.65/1.51  --inst_restr_to_given                   false
% 7.65/1.51  --inst_activity_threshold               500
% 7.65/1.51  --inst_out_proof                        true
% 7.65/1.51  
% 7.65/1.51  ------ Resolution Options
% 7.65/1.51  
% 7.65/1.51  --resolution_flag                       true
% 7.65/1.51  --res_lit_sel                           adaptive
% 7.65/1.51  --res_lit_sel_side                      none
% 7.65/1.51  --res_ordering                          kbo
% 7.65/1.51  --res_to_prop_solver                    active
% 7.65/1.51  --res_prop_simpl_new                    false
% 7.65/1.51  --res_prop_simpl_given                  true
% 7.65/1.51  --res_passive_queue_type                priority_queues
% 7.65/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.65/1.51  --res_passive_queues_freq               [15;5]
% 7.65/1.51  --res_forward_subs                      full
% 7.65/1.51  --res_backward_subs                     full
% 7.65/1.51  --res_forward_subs_resolution           true
% 7.65/1.51  --res_backward_subs_resolution          true
% 7.65/1.51  --res_orphan_elimination                true
% 7.65/1.51  --res_time_limit                        2.
% 7.65/1.51  --res_out_proof                         true
% 7.65/1.51  
% 7.65/1.51  ------ Superposition Options
% 7.65/1.51  
% 7.65/1.51  --superposition_flag                    true
% 7.65/1.51  --sup_passive_queue_type                priority_queues
% 7.65/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.65/1.51  --sup_passive_queues_freq               [8;1;4]
% 7.65/1.51  --demod_completeness_check              fast
% 7.65/1.51  --demod_use_ground                      true
% 7.65/1.51  --sup_to_prop_solver                    passive
% 7.65/1.51  --sup_prop_simpl_new                    true
% 7.65/1.51  --sup_prop_simpl_given                  true
% 7.65/1.51  --sup_fun_splitting                     false
% 7.65/1.51  --sup_smt_interval                      50000
% 7.65/1.51  
% 7.65/1.51  ------ Superposition Simplification Setup
% 7.65/1.51  
% 7.65/1.51  --sup_indices_passive                   []
% 7.65/1.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.65/1.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.65/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.65/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 7.65/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.65/1.51  --sup_full_bw                           [BwDemod]
% 7.65/1.51  --sup_immed_triv                        [TrivRules]
% 7.65/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.65/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.65/1.51  --sup_immed_bw_main                     []
% 7.65/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.65/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 7.65/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.65/1.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.65/1.51  
% 7.65/1.51  ------ Combination Options
% 7.65/1.51  
% 7.65/1.51  --comb_res_mult                         3
% 7.65/1.51  --comb_sup_mult                         2
% 7.65/1.51  --comb_inst_mult                        10
% 7.65/1.51  
% 7.65/1.51  ------ Debug Options
% 7.65/1.51  
% 7.65/1.51  --dbg_backtrace                         false
% 7.65/1.51  --dbg_dump_prop_clauses                 false
% 7.65/1.51  --dbg_dump_prop_clauses_file            -
% 7.65/1.51  --dbg_out_stat                          false
% 7.65/1.51  ------ Parsing...
% 7.65/1.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.65/1.51  
% 7.65/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.65/1.51  
% 7.65/1.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.65/1.51  
% 7.65/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.65/1.51  ------ Proving...
% 7.65/1.51  ------ Problem Properties 
% 7.65/1.51  
% 7.65/1.51  
% 7.65/1.51  clauses                                 12
% 7.65/1.51  conjectures                             3
% 7.65/1.51  EPR                                     0
% 7.65/1.51  Horn                                    12
% 7.65/1.51  unary                                   5
% 7.65/1.51  binary                                  4
% 7.65/1.51  lits                                    23
% 7.65/1.51  lits eq                                 1
% 7.65/1.51  fd_pure                                 0
% 7.65/1.51  fd_pseudo                               0
% 7.65/1.51  fd_cond                                 0
% 7.65/1.51  fd_pseudo_cond                          0
% 7.65/1.51  AC symbols                              0
% 7.65/1.51  
% 7.65/1.51  ------ Schedule dynamic 5 is on 
% 7.65/1.51  
% 7.65/1.51  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.65/1.51  
% 7.65/1.51  
% 7.65/1.51  ------ 
% 7.65/1.51  Current options:
% 7.65/1.51  ------ 
% 7.65/1.51  
% 7.65/1.51  ------ Input Options
% 7.65/1.51  
% 7.65/1.51  --out_options                           all
% 7.65/1.51  --tptp_safe_out                         true
% 7.65/1.51  --problem_path                          ""
% 7.65/1.51  --include_path                          ""
% 7.65/1.51  --clausifier                            res/vclausify_rel
% 7.65/1.51  --clausifier_options                    --mode clausify
% 7.65/1.51  --stdin                                 false
% 7.65/1.51  --stats_out                             all
% 7.65/1.51  
% 7.65/1.51  ------ General Options
% 7.65/1.51  
% 7.65/1.51  --fof                                   false
% 7.65/1.51  --time_out_real                         305.
% 7.65/1.51  --time_out_virtual                      -1.
% 7.65/1.51  --symbol_type_check                     false
% 7.65/1.51  --clausify_out                          false
% 7.65/1.51  --sig_cnt_out                           false
% 7.65/1.51  --trig_cnt_out                          false
% 7.65/1.51  --trig_cnt_out_tolerance                1.
% 7.65/1.51  --trig_cnt_out_sk_spl                   false
% 7.65/1.51  --abstr_cl_out                          false
% 7.65/1.51  
% 7.65/1.51  ------ Global Options
% 7.65/1.51  
% 7.65/1.51  --schedule                              default
% 7.65/1.51  --add_important_lit                     false
% 7.65/1.51  --prop_solver_per_cl                    1000
% 7.65/1.51  --min_unsat_core                        false
% 7.65/1.51  --soft_assumptions                      false
% 7.65/1.51  --soft_lemma_size                       3
% 7.65/1.51  --prop_impl_unit_size                   0
% 7.65/1.51  --prop_impl_unit                        []
% 7.65/1.51  --share_sel_clauses                     true
% 7.65/1.51  --reset_solvers                         false
% 7.65/1.51  --bc_imp_inh                            [conj_cone]
% 7.65/1.51  --conj_cone_tolerance                   3.
% 7.65/1.51  --extra_neg_conj                        none
% 7.65/1.51  --large_theory_mode                     true
% 7.65/1.51  --prolific_symb_bound                   200
% 7.65/1.51  --lt_threshold                          2000
% 7.65/1.51  --clause_weak_htbl                      true
% 7.65/1.51  --gc_record_bc_elim                     false
% 7.65/1.51  
% 7.65/1.51  ------ Preprocessing Options
% 7.65/1.51  
% 7.65/1.51  --preprocessing_flag                    true
% 7.65/1.51  --time_out_prep_mult                    0.1
% 7.65/1.51  --splitting_mode                        input
% 7.65/1.51  --splitting_grd                         true
% 7.65/1.51  --splitting_cvd                         false
% 7.65/1.51  --splitting_cvd_svl                     false
% 7.65/1.51  --splitting_nvd                         32
% 7.65/1.51  --sub_typing                            true
% 7.65/1.51  --prep_gs_sim                           true
% 7.65/1.51  --prep_unflatten                        true
% 7.65/1.51  --prep_res_sim                          true
% 7.65/1.51  --prep_upred                            true
% 7.65/1.51  --prep_sem_filter                       exhaustive
% 7.65/1.51  --prep_sem_filter_out                   false
% 7.65/1.51  --pred_elim                             true
% 7.65/1.51  --res_sim_input                         true
% 7.65/1.51  --eq_ax_congr_red                       true
% 7.65/1.51  --pure_diseq_elim                       true
% 7.65/1.51  --brand_transform                       false
% 7.65/1.51  --non_eq_to_eq                          false
% 7.65/1.51  --prep_def_merge                        true
% 7.65/1.51  --prep_def_merge_prop_impl              false
% 7.65/1.51  --prep_def_merge_mbd                    true
% 7.65/1.51  --prep_def_merge_tr_red                 false
% 7.65/1.51  --prep_def_merge_tr_cl                  false
% 7.65/1.51  --smt_preprocessing                     true
% 7.65/1.51  --smt_ac_axioms                         fast
% 7.65/1.51  --preprocessed_out                      false
% 7.65/1.51  --preprocessed_stats                    false
% 7.65/1.51  
% 7.65/1.51  ------ Abstraction refinement Options
% 7.65/1.51  
% 7.65/1.51  --abstr_ref                             []
% 7.65/1.51  --abstr_ref_prep                        false
% 7.65/1.51  --abstr_ref_until_sat                   false
% 7.65/1.51  --abstr_ref_sig_restrict                funpre
% 7.65/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 7.65/1.51  --abstr_ref_under                       []
% 7.65/1.51  
% 7.65/1.51  ------ SAT Options
% 7.65/1.51  
% 7.65/1.51  --sat_mode                              false
% 7.65/1.51  --sat_fm_restart_options                ""
% 7.65/1.51  --sat_gr_def                            false
% 7.65/1.51  --sat_epr_types                         true
% 7.65/1.51  --sat_non_cyclic_types                  false
% 7.65/1.51  --sat_finite_models                     false
% 7.65/1.51  --sat_fm_lemmas                         false
% 7.65/1.51  --sat_fm_prep                           false
% 7.65/1.51  --sat_fm_uc_incr                        true
% 7.65/1.51  --sat_out_model                         small
% 7.65/1.51  --sat_out_clauses                       false
% 7.65/1.51  
% 7.65/1.51  ------ QBF Options
% 7.65/1.51  
% 7.65/1.51  --qbf_mode                              false
% 7.65/1.51  --qbf_elim_univ                         false
% 7.65/1.51  --qbf_dom_inst                          none
% 7.65/1.51  --qbf_dom_pre_inst                      false
% 7.65/1.51  --qbf_sk_in                             false
% 7.65/1.51  --qbf_pred_elim                         true
% 7.65/1.51  --qbf_split                             512
% 7.65/1.51  
% 7.65/1.51  ------ BMC1 Options
% 7.65/1.51  
% 7.65/1.51  --bmc1_incremental                      false
% 7.65/1.51  --bmc1_axioms                           reachable_all
% 7.65/1.51  --bmc1_min_bound                        0
% 7.65/1.51  --bmc1_max_bound                        -1
% 7.65/1.51  --bmc1_max_bound_default                -1
% 7.65/1.51  --bmc1_symbol_reachability              true
% 7.65/1.51  --bmc1_property_lemmas                  false
% 7.65/1.51  --bmc1_k_induction                      false
% 7.65/1.51  --bmc1_non_equiv_states                 false
% 7.65/1.51  --bmc1_deadlock                         false
% 7.65/1.51  --bmc1_ucm                              false
% 7.65/1.51  --bmc1_add_unsat_core                   none
% 7.65/1.51  --bmc1_unsat_core_children              false
% 7.65/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 7.65/1.51  --bmc1_out_stat                         full
% 7.65/1.51  --bmc1_ground_init                      false
% 7.65/1.51  --bmc1_pre_inst_next_state              false
% 7.65/1.51  --bmc1_pre_inst_state                   false
% 7.65/1.51  --bmc1_pre_inst_reach_state             false
% 7.65/1.51  --bmc1_out_unsat_core                   false
% 7.65/1.51  --bmc1_aig_witness_out                  false
% 7.65/1.51  --bmc1_verbose                          false
% 7.65/1.51  --bmc1_dump_clauses_tptp                false
% 7.65/1.51  --bmc1_dump_unsat_core_tptp             false
% 7.65/1.51  --bmc1_dump_file                        -
% 7.65/1.51  --bmc1_ucm_expand_uc_limit              128
% 7.65/1.51  --bmc1_ucm_n_expand_iterations          6
% 7.65/1.51  --bmc1_ucm_extend_mode                  1
% 7.65/1.51  --bmc1_ucm_init_mode                    2
% 7.65/1.51  --bmc1_ucm_cone_mode                    none
% 7.65/1.51  --bmc1_ucm_reduced_relation_type        0
% 7.65/1.51  --bmc1_ucm_relax_model                  4
% 7.65/1.51  --bmc1_ucm_full_tr_after_sat            true
% 7.65/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 7.65/1.51  --bmc1_ucm_layered_model                none
% 7.65/1.51  --bmc1_ucm_max_lemma_size               10
% 7.65/1.51  
% 7.65/1.51  ------ AIG Options
% 7.65/1.51  
% 7.65/1.51  --aig_mode                              false
% 7.65/1.51  
% 7.65/1.51  ------ Instantiation Options
% 7.65/1.51  
% 7.65/1.51  --instantiation_flag                    true
% 7.65/1.51  --inst_sos_flag                         false
% 7.65/1.51  --inst_sos_phase                        true
% 7.65/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.65/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.65/1.51  --inst_lit_sel_side                     none
% 7.65/1.51  --inst_solver_per_active                1400
% 7.65/1.51  --inst_solver_calls_frac                1.
% 7.65/1.51  --inst_passive_queue_type               priority_queues
% 7.65/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.65/1.51  --inst_passive_queues_freq              [25;2]
% 7.65/1.51  --inst_dismatching                      true
% 7.65/1.51  --inst_eager_unprocessed_to_passive     true
% 7.65/1.51  --inst_prop_sim_given                   true
% 7.65/1.51  --inst_prop_sim_new                     false
% 7.65/1.51  --inst_subs_new                         false
% 7.65/1.51  --inst_eq_res_simp                      false
% 7.65/1.51  --inst_subs_given                       false
% 7.65/1.51  --inst_orphan_elimination               true
% 7.65/1.51  --inst_learning_loop_flag               true
% 7.65/1.51  --inst_learning_start                   3000
% 7.65/1.51  --inst_learning_factor                  2
% 7.65/1.51  --inst_start_prop_sim_after_learn       3
% 7.65/1.51  --inst_sel_renew                        solver
% 7.65/1.51  --inst_lit_activity_flag                true
% 7.65/1.51  --inst_restr_to_given                   false
% 7.65/1.51  --inst_activity_threshold               500
% 7.65/1.51  --inst_out_proof                        true
% 7.65/1.51  
% 7.65/1.51  ------ Resolution Options
% 7.65/1.51  
% 7.65/1.51  --resolution_flag                       false
% 7.65/1.51  --res_lit_sel                           adaptive
% 7.65/1.51  --res_lit_sel_side                      none
% 7.65/1.51  --res_ordering                          kbo
% 7.65/1.51  --res_to_prop_solver                    active
% 7.65/1.51  --res_prop_simpl_new                    false
% 7.65/1.51  --res_prop_simpl_given                  true
% 7.65/1.51  --res_passive_queue_type                priority_queues
% 7.65/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.65/1.51  --res_passive_queues_freq               [15;5]
% 7.65/1.51  --res_forward_subs                      full
% 7.65/1.51  --res_backward_subs                     full
% 7.65/1.51  --res_forward_subs_resolution           true
% 7.65/1.51  --res_backward_subs_resolution          true
% 7.65/1.51  --res_orphan_elimination                true
% 7.65/1.51  --res_time_limit                        2.
% 7.65/1.51  --res_out_proof                         true
% 7.65/1.51  
% 7.65/1.51  ------ Superposition Options
% 7.65/1.51  
% 7.65/1.51  --superposition_flag                    true
% 7.65/1.51  --sup_passive_queue_type                priority_queues
% 7.65/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.65/1.51  --sup_passive_queues_freq               [8;1;4]
% 7.65/1.51  --demod_completeness_check              fast
% 7.65/1.51  --demod_use_ground                      true
% 7.65/1.51  --sup_to_prop_solver                    passive
% 7.65/1.51  --sup_prop_simpl_new                    true
% 7.65/1.51  --sup_prop_simpl_given                  true
% 7.65/1.51  --sup_fun_splitting                     false
% 7.65/1.51  --sup_smt_interval                      50000
% 7.65/1.51  
% 7.65/1.51  ------ Superposition Simplification Setup
% 7.65/1.51  
% 7.65/1.51  --sup_indices_passive                   []
% 7.65/1.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.65/1.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.65/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.65/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 7.65/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.65/1.51  --sup_full_bw                           [BwDemod]
% 7.65/1.51  --sup_immed_triv                        [TrivRules]
% 7.65/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.65/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.65/1.51  --sup_immed_bw_main                     []
% 7.65/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.65/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 7.65/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.65/1.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.65/1.51  
% 7.65/1.51  ------ Combination Options
% 7.65/1.51  
% 7.65/1.51  --comb_res_mult                         3
% 7.65/1.51  --comb_sup_mult                         2
% 7.65/1.51  --comb_inst_mult                        10
% 7.65/1.51  
% 7.65/1.51  ------ Debug Options
% 7.65/1.51  
% 7.65/1.51  --dbg_backtrace                         false
% 7.65/1.51  --dbg_dump_prop_clauses                 false
% 7.65/1.51  --dbg_dump_prop_clauses_file            -
% 7.65/1.51  --dbg_out_stat                          false
% 7.65/1.51  
% 7.65/1.51  
% 7.65/1.51  
% 7.65/1.51  
% 7.65/1.51  ------ Proving...
% 7.65/1.51  
% 7.65/1.51  
% 7.65/1.51  % SZS status Theorem for theBenchmark.p
% 7.65/1.51  
% 7.65/1.51   Resolution empty clause
% 7.65/1.51  
% 7.65/1.51  % SZS output start CNFRefutation for theBenchmark.p
% 7.65/1.51  
% 7.65/1.51  fof(f8,axiom,(
% 7.65/1.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 7.65/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.65/1.51  
% 7.65/1.51  fof(f18,plain,(
% 7.65/1.51    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.65/1.51    inference(ennf_transformation,[],[f8])).
% 7.65/1.51  
% 7.65/1.51  fof(f19,plain,(
% 7.65/1.51    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.65/1.51    inference(flattening,[],[f18])).
% 7.65/1.51  
% 7.65/1.51  fof(f34,plain,(
% 7.65/1.51    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.65/1.51    inference(cnf_transformation,[],[f19])).
% 7.65/1.51  
% 7.65/1.51  fof(f9,conjecture,(
% 7.65/1.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))))))),
% 7.65/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.65/1.51  
% 7.65/1.51  fof(f10,negated_conjecture,(
% 7.65/1.51    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))))))),
% 7.65/1.51    inference(negated_conjecture,[],[f9])).
% 7.65/1.51  
% 7.65/1.51  fof(f20,plain,(
% 7.65/1.51    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 7.65/1.51    inference(ennf_transformation,[],[f10])).
% 7.65/1.51  
% 7.65/1.51  fof(f24,plain,(
% 7.65/1.51    ( ! [X0,X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,sK2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 7.65/1.51    introduced(choice_axiom,[])).
% 7.65/1.51  
% 7.65/1.51  fof(f23,plain,(
% 7.65/1.51    ( ! [X0] : (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,sK1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),sK1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 7.65/1.51    introduced(choice_axiom,[])).
% 7.65/1.51  
% 7.65/1.51  fof(f22,plain,(
% 7.65/1.51    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 7.65/1.51    introduced(choice_axiom,[])).
% 7.65/1.51  
% 7.65/1.51  fof(f25,plain,(
% 7.65/1.51    ((~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 7.65/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f24,f23,f22])).
% 7.65/1.51  
% 7.65/1.51  fof(f35,plain,(
% 7.65/1.51    l1_pre_topc(sK0)),
% 7.65/1.51    inference(cnf_transformation,[],[f25])).
% 7.65/1.51  
% 7.65/1.51  fof(f4,axiom,(
% 7.65/1.51    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 7.65/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.65/1.51  
% 7.65/1.51  fof(f12,plain,(
% 7.65/1.51    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 7.65/1.51    inference(ennf_transformation,[],[f4])).
% 7.65/1.51  
% 7.65/1.51  fof(f13,plain,(
% 7.65/1.51    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 7.65/1.51    inference(flattening,[],[f12])).
% 7.65/1.51  
% 7.65/1.51  fof(f29,plain,(
% 7.65/1.51    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 7.65/1.51    inference(cnf_transformation,[],[f13])).
% 7.65/1.51  
% 7.65/1.51  fof(f36,plain,(
% 7.65/1.51    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 7.65/1.51    inference(cnf_transformation,[],[f25])).
% 7.65/1.51  
% 7.65/1.51  fof(f7,axiom,(
% 7.65/1.51    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 7.65/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.65/1.51  
% 7.65/1.51  fof(f16,plain,(
% 7.65/1.51    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 7.65/1.51    inference(ennf_transformation,[],[f7])).
% 7.65/1.51  
% 7.65/1.51  fof(f17,plain,(
% 7.65/1.51    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 7.65/1.51    inference(flattening,[],[f16])).
% 7.65/1.51  
% 7.65/1.51  fof(f33,plain,(
% 7.65/1.51    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.65/1.51    inference(cnf_transformation,[],[f17])).
% 7.65/1.51  
% 7.65/1.51  fof(f6,axiom,(
% 7.65/1.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.65/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.65/1.51  
% 7.65/1.51  fof(f21,plain,(
% 7.65/1.51    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.65/1.51    inference(nnf_transformation,[],[f6])).
% 7.65/1.51  
% 7.65/1.51  fof(f31,plain,(
% 7.65/1.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.65/1.51    inference(cnf_transformation,[],[f21])).
% 7.65/1.51  
% 7.65/1.51  fof(f37,plain,(
% 7.65/1.51    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 7.65/1.51    inference(cnf_transformation,[],[f25])).
% 7.65/1.51  
% 7.65/1.51  fof(f5,axiom,(
% 7.65/1.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 7.65/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.65/1.51  
% 7.65/1.51  fof(f14,plain,(
% 7.65/1.51    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 7.65/1.51    inference(ennf_transformation,[],[f5])).
% 7.65/1.51  
% 7.65/1.51  fof(f15,plain,(
% 7.65/1.51    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.65/1.51    inference(flattening,[],[f14])).
% 7.65/1.51  
% 7.65/1.51  fof(f30,plain,(
% 7.65/1.51    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.65/1.51    inference(cnf_transformation,[],[f15])).
% 7.65/1.51  
% 7.65/1.51  fof(f32,plain,(
% 7.65/1.51    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.65/1.51    inference(cnf_transformation,[],[f21])).
% 7.65/1.51  
% 7.65/1.51  fof(f38,plain,(
% 7.65/1.51    ~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))),
% 7.65/1.51    inference(cnf_transformation,[],[f25])).
% 7.65/1.51  
% 7.65/1.51  fof(f3,axiom,(
% 7.65/1.51    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 7.65/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.65/1.51  
% 7.65/1.51  fof(f28,plain,(
% 7.65/1.51    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 7.65/1.51    inference(cnf_transformation,[],[f3])).
% 7.65/1.51  
% 7.65/1.51  fof(f1,axiom,(
% 7.65/1.51    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 7.65/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.65/1.51  
% 7.65/1.51  fof(f26,plain,(
% 7.65/1.51    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 7.65/1.51    inference(cnf_transformation,[],[f1])).
% 7.65/1.51  
% 7.65/1.51  fof(f2,axiom,(
% 7.65/1.51    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 7.65/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.65/1.51  
% 7.65/1.51  fof(f11,plain,(
% 7.65/1.51    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 7.65/1.51    inference(ennf_transformation,[],[f2])).
% 7.65/1.51  
% 7.65/1.51  fof(f27,plain,(
% 7.65/1.51    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 7.65/1.51    inference(cnf_transformation,[],[f11])).
% 7.65/1.51  
% 7.65/1.51  cnf(c_8,plain,
% 7.65/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.65/1.51      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 7.65/1.51      | ~ r1_tarski(X0,X2)
% 7.65/1.51      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 7.65/1.51      | ~ l1_pre_topc(X1) ),
% 7.65/1.51      inference(cnf_transformation,[],[f34]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_12,negated_conjecture,
% 7.65/1.51      ( l1_pre_topc(sK0) ),
% 7.65/1.51      inference(cnf_transformation,[],[f35]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_175,plain,
% 7.65/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.65/1.51      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 7.65/1.51      | ~ r1_tarski(X0,X2)
% 7.65/1.51      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 7.65/1.51      | sK0 != X1 ),
% 7.65/1.51      inference(resolution_lifted,[status(thm)],[c_8,c_12]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_176,plain,
% 7.65/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.65/1.51      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.65/1.51      | ~ r1_tarski(X1,X0)
% 7.65/1.51      | r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,X0)) ),
% 7.65/1.51      inference(unflattening,[status(thm)],[c_175]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_328,plain,
% 7.65/1.51      ( ~ m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.65/1.51      | ~ m1_subset_1(X1_40,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.65/1.51      | ~ r1_tarski(X1_40,X0_40)
% 7.65/1.51      | r1_tarski(k1_tops_1(sK0,X1_40),k1_tops_1(sK0,X0_40)) ),
% 7.65/1.51      inference(subtyping,[status(esa)],[c_176]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_669,plain,
% 7.65/1.51      ( m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.65/1.51      | m1_subset_1(X1_40,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.65/1.51      | r1_tarski(X1_40,X0_40) != iProver_top
% 7.65/1.51      | r1_tarski(k1_tops_1(sK0,X1_40),k1_tops_1(sK0,X0_40)) = iProver_top ),
% 7.65/1.51      inference(predicate_to_equality,[status(thm)],[c_328]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_3,plain,
% 7.65/1.51      ( ~ r1_tarski(X0,X1)
% 7.65/1.51      | ~ r1_tarski(X2,X1)
% 7.65/1.51      | r1_tarski(k2_xboole_0(X2,X0),X1) ),
% 7.65/1.51      inference(cnf_transformation,[],[f29]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_334,plain,
% 7.65/1.51      ( ~ r1_tarski(X0_40,X1_40)
% 7.65/1.51      | ~ r1_tarski(X2_40,X1_40)
% 7.65/1.51      | r1_tarski(k2_xboole_0(X2_40,X0_40),X1_40) ),
% 7.65/1.51      inference(subtyping,[status(esa)],[c_3]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_663,plain,
% 7.65/1.51      ( r1_tarski(X0_40,X1_40) != iProver_top
% 7.65/1.51      | r1_tarski(X2_40,X1_40) != iProver_top
% 7.65/1.51      | r1_tarski(k2_xboole_0(X2_40,X0_40),X1_40) = iProver_top ),
% 7.65/1.51      inference(predicate_to_equality,[status(thm)],[c_334]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_11,negated_conjecture,
% 7.65/1.51      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.65/1.51      inference(cnf_transformation,[],[f36]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_329,negated_conjecture,
% 7.65/1.51      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.65/1.51      inference(subtyping,[status(esa)],[c_11]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_668,plain,
% 7.65/1.51      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 7.65/1.51      inference(predicate_to_equality,[status(thm)],[c_329]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_7,plain,
% 7.65/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.65/1.51      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.65/1.51      | ~ l1_pre_topc(X1) ),
% 7.65/1.51      inference(cnf_transformation,[],[f33]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_193,plain,
% 7.65/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.65/1.51      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.65/1.51      | sK0 != X1 ),
% 7.65/1.51      inference(resolution_lifted,[status(thm)],[c_7,c_12]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_194,plain,
% 7.65/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.65/1.51      | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.65/1.51      inference(unflattening,[status(thm)],[c_193]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_327,plain,
% 7.65/1.51      ( ~ m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.65/1.51      | m1_subset_1(k1_tops_1(sK0,X0_40),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.65/1.51      inference(subtyping,[status(esa)],[c_194]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_670,plain,
% 7.65/1.51      ( m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.65/1.51      | m1_subset_1(k1_tops_1(sK0,X0_40),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 7.65/1.51      inference(predicate_to_equality,[status(thm)],[c_327]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_6,plain,
% 7.65/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.65/1.51      inference(cnf_transformation,[],[f31]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_332,plain,
% 7.65/1.51      ( ~ m1_subset_1(X0_40,k1_zfmisc_1(X1_40)) | r1_tarski(X0_40,X1_40) ),
% 7.65/1.51      inference(subtyping,[status(esa)],[c_6]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_665,plain,
% 7.65/1.51      ( m1_subset_1(X0_40,k1_zfmisc_1(X1_40)) != iProver_top
% 7.65/1.51      | r1_tarski(X0_40,X1_40) = iProver_top ),
% 7.65/1.51      inference(predicate_to_equality,[status(thm)],[c_332]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_1229,plain,
% 7.65/1.51      ( m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.65/1.51      | r1_tarski(k1_tops_1(sK0,X0_40),u1_struct_0(sK0)) = iProver_top ),
% 7.65/1.51      inference(superposition,[status(thm)],[c_670,c_665]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_10,negated_conjecture,
% 7.65/1.51      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.65/1.51      inference(cnf_transformation,[],[f37]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_330,negated_conjecture,
% 7.65/1.51      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.65/1.51      inference(subtyping,[status(esa)],[c_10]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_667,plain,
% 7.65/1.51      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 7.65/1.51      inference(predicate_to_equality,[status(thm)],[c_330]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_4,plain,
% 7.65/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.65/1.51      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 7.65/1.51      | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
% 7.65/1.51      inference(cnf_transformation,[],[f30]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_5,plain,
% 7.65/1.51      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.65/1.51      inference(cnf_transformation,[],[f32]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_99,plain,
% 7.65/1.51      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 7.65/1.51      inference(prop_impl,[status(thm)],[c_5]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_100,plain,
% 7.65/1.51      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.65/1.51      inference(renaming,[status(thm)],[c_99]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_123,plain,
% 7.65/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.65/1.51      | ~ r1_tarski(X2,X1)
% 7.65/1.51      | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
% 7.65/1.51      inference(bin_hyper_res,[status(thm)],[c_4,c_100]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_255,plain,
% 7.65/1.51      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 7.65/1.51      inference(prop_impl,[status(thm)],[c_5]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_256,plain,
% 7.65/1.51      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.65/1.51      inference(renaming,[status(thm)],[c_255]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_278,plain,
% 7.65/1.51      ( ~ r1_tarski(X0,X1)
% 7.65/1.51      | ~ r1_tarski(X2,X1)
% 7.65/1.51      | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
% 7.65/1.51      inference(bin_hyper_res,[status(thm)],[c_123,c_256]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_326,plain,
% 7.65/1.51      ( ~ r1_tarski(X0_40,X1_40)
% 7.65/1.51      | ~ r1_tarski(X2_40,X1_40)
% 7.65/1.51      | k4_subset_1(X1_40,X2_40,X0_40) = k2_xboole_0(X2_40,X0_40) ),
% 7.65/1.51      inference(subtyping,[status(esa)],[c_278]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_671,plain,
% 7.65/1.51      ( k4_subset_1(X0_40,X1_40,X2_40) = k2_xboole_0(X1_40,X2_40)
% 7.65/1.51      | r1_tarski(X2_40,X0_40) != iProver_top
% 7.65/1.51      | r1_tarski(X1_40,X0_40) != iProver_top ),
% 7.65/1.51      inference(predicate_to_equality,[status(thm)],[c_326]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_1899,plain,
% 7.65/1.51      ( k4_subset_1(u1_struct_0(sK0),X0_40,k1_tops_1(sK0,X1_40)) = k2_xboole_0(X0_40,k1_tops_1(sK0,X1_40))
% 7.65/1.51      | m1_subset_1(X1_40,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.65/1.51      | r1_tarski(X0_40,u1_struct_0(sK0)) != iProver_top ),
% 7.65/1.51      inference(superposition,[status(thm)],[c_1229,c_671]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_9656,plain,
% 7.65/1.51      ( k4_subset_1(u1_struct_0(sK0),X0_40,k1_tops_1(sK0,sK2)) = k2_xboole_0(X0_40,k1_tops_1(sK0,sK2))
% 7.65/1.51      | r1_tarski(X0_40,u1_struct_0(sK0)) != iProver_top ),
% 7.65/1.51      inference(superposition,[status(thm)],[c_667,c_1899]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_9814,plain,
% 7.65/1.51      ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X0_40),k1_tops_1(sK0,sK2)) = k2_xboole_0(k1_tops_1(sK0,X0_40),k1_tops_1(sK0,sK2))
% 7.65/1.51      | m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.65/1.51      inference(superposition,[status(thm)],[c_1229,c_9656]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_10695,plain,
% 7.65/1.51      ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
% 7.65/1.51      inference(superposition,[status(thm)],[c_668,c_9814]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_1228,plain,
% 7.65/1.51      ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
% 7.65/1.51      inference(superposition,[status(thm)],[c_668,c_665]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_1227,plain,
% 7.65/1.51      ( r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
% 7.65/1.51      inference(superposition,[status(thm)],[c_667,c_665]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_1893,plain,
% 7.65/1.51      ( k4_subset_1(u1_struct_0(sK0),X0_40,sK2) = k2_xboole_0(X0_40,sK2)
% 7.65/1.51      | r1_tarski(X0_40,u1_struct_0(sK0)) != iProver_top ),
% 7.65/1.51      inference(superposition,[status(thm)],[c_1227,c_671]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_2594,plain,
% 7.65/1.51      ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2) ),
% 7.65/1.51      inference(superposition,[status(thm)],[c_1228,c_1893]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_9,negated_conjecture,
% 7.65/1.51      ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
% 7.65/1.51      inference(cnf_transformation,[],[f38]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_331,negated_conjecture,
% 7.65/1.51      ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
% 7.65/1.51      inference(subtyping,[status(esa)],[c_9]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_666,plain,
% 7.65/1.51      ( r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) != iProver_top ),
% 7.65/1.51      inference(predicate_to_equality,[status(thm)],[c_331]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_2694,plain,
% 7.65/1.51      ( r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) != iProver_top ),
% 7.65/1.51      inference(demodulation,[status(thm)],[c_2594,c_666]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_10953,plain,
% 7.65/1.51      ( r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) != iProver_top ),
% 7.65/1.51      inference(demodulation,[status(thm)],[c_10695,c_2694]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_11803,plain,
% 7.65/1.51      ( r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) != iProver_top
% 7.65/1.51      | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) != iProver_top ),
% 7.65/1.51      inference(superposition,[status(thm)],[c_663,c_10953]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_14,plain,
% 7.65/1.51      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 7.65/1.51      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_15,plain,
% 7.65/1.51      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 7.65/1.51      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_754,plain,
% 7.65/1.51      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.65/1.51      | r1_tarski(sK2,u1_struct_0(sK0)) ),
% 7.65/1.51      inference(instantiation,[status(thm)],[c_332]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_755,plain,
% 7.65/1.51      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.65/1.51      | r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
% 7.65/1.51      inference(predicate_to_equality,[status(thm)],[c_754]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_757,plain,
% 7.65/1.51      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.65/1.51      | r1_tarski(sK1,u1_struct_0(sK0)) ),
% 7.65/1.51      inference(instantiation,[status(thm)],[c_332]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_758,plain,
% 7.65/1.51      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.65/1.51      | r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
% 7.65/1.51      inference(predicate_to_equality,[status(thm)],[c_757]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_846,plain,
% 7.65/1.51      ( ~ r1_tarski(X0_40,u1_struct_0(sK0))
% 7.65/1.51      | r1_tarski(k2_xboole_0(X0_40,sK2),u1_struct_0(sK0))
% 7.65/1.51      | ~ r1_tarski(sK2,u1_struct_0(sK0)) ),
% 7.65/1.51      inference(instantiation,[status(thm)],[c_334]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_848,plain,
% 7.65/1.51      ( r1_tarski(X0_40,u1_struct_0(sK0)) != iProver_top
% 7.65/1.51      | r1_tarski(k2_xboole_0(X0_40,sK2),u1_struct_0(sK0)) = iProver_top
% 7.65/1.51      | r1_tarski(sK2,u1_struct_0(sK0)) != iProver_top ),
% 7.65/1.51      inference(predicate_to_equality,[status(thm)],[c_846]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_850,plain,
% 7.65/1.51      ( r1_tarski(k2_xboole_0(sK1,sK2),u1_struct_0(sK0)) = iProver_top
% 7.65/1.51      | r1_tarski(sK2,u1_struct_0(sK0)) != iProver_top
% 7.65/1.51      | r1_tarski(sK1,u1_struct_0(sK0)) != iProver_top ),
% 7.65/1.51      inference(instantiation,[status(thm)],[c_848]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_333,plain,
% 7.65/1.51      ( m1_subset_1(X0_40,k1_zfmisc_1(X1_40)) | ~ r1_tarski(X0_40,X1_40) ),
% 7.65/1.51      inference(subtyping,[status(esa)],[c_5]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_945,plain,
% 7.65/1.51      ( m1_subset_1(k2_xboole_0(X0_40,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 7.65/1.51      | ~ r1_tarski(k2_xboole_0(X0_40,sK2),u1_struct_0(sK0)) ),
% 7.65/1.51      inference(instantiation,[status(thm)],[c_333]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_946,plain,
% 7.65/1.51      ( m1_subset_1(k2_xboole_0(X0_40,sK2),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 7.65/1.51      | r1_tarski(k2_xboole_0(X0_40,sK2),u1_struct_0(sK0)) != iProver_top ),
% 7.65/1.51      inference(predicate_to_equality,[status(thm)],[c_945]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_948,plain,
% 7.65/1.51      ( m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 7.65/1.51      | r1_tarski(k2_xboole_0(sK1,sK2),u1_struct_0(sK0)) != iProver_top ),
% 7.65/1.51      inference(instantiation,[status(thm)],[c_946]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_744,plain,
% 7.65/1.51      ( ~ m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.65/1.51      | ~ m1_subset_1(k2_xboole_0(X0_40,X1_40),k1_zfmisc_1(u1_struct_0(sK0)))
% 7.65/1.51      | ~ r1_tarski(X0_40,k2_xboole_0(X0_40,X1_40))
% 7.65/1.51      | r1_tarski(k1_tops_1(sK0,X0_40),k1_tops_1(sK0,k2_xboole_0(X0_40,X1_40))) ),
% 7.65/1.51      inference(instantiation,[status(thm)],[c_328]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_1315,plain,
% 7.65/1.51      ( ~ m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.65/1.51      | ~ m1_subset_1(k2_xboole_0(X0_40,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 7.65/1.51      | ~ r1_tarski(X0_40,k2_xboole_0(X0_40,sK2))
% 7.65/1.51      | r1_tarski(k1_tops_1(sK0,X0_40),k1_tops_1(sK0,k2_xboole_0(X0_40,sK2))) ),
% 7.65/1.51      inference(instantiation,[status(thm)],[c_744]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_1316,plain,
% 7.65/1.51      ( m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.65/1.51      | m1_subset_1(k2_xboole_0(X0_40,sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.65/1.51      | r1_tarski(X0_40,k2_xboole_0(X0_40,sK2)) != iProver_top
% 7.65/1.51      | r1_tarski(k1_tops_1(sK0,X0_40),k1_tops_1(sK0,k2_xboole_0(X0_40,sK2))) = iProver_top ),
% 7.65/1.51      inference(predicate_to_equality,[status(thm)],[c_1315]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_1318,plain,
% 7.65/1.51      ( m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.65/1.51      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.65/1.51      | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) = iProver_top
% 7.65/1.51      | r1_tarski(sK1,k2_xboole_0(sK1,sK2)) != iProver_top ),
% 7.65/1.51      inference(instantiation,[status(thm)],[c_1316]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_2,plain,
% 7.65/1.51      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 7.65/1.51      inference(cnf_transformation,[],[f28]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_335,plain,
% 7.65/1.51      ( r1_tarski(X0_40,k2_xboole_0(X0_40,X1_40)) ),
% 7.65/1.51      inference(subtyping,[status(esa)],[c_2]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_1426,plain,
% 7.65/1.51      ( r1_tarski(X0_40,k2_xboole_0(X0_40,sK2)) ),
% 7.65/1.51      inference(instantiation,[status(thm)],[c_335]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_1427,plain,
% 7.65/1.51      ( r1_tarski(X0_40,k2_xboole_0(X0_40,sK2)) = iProver_top ),
% 7.65/1.51      inference(predicate_to_equality,[status(thm)],[c_1426]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_1429,plain,
% 7.65/1.51      ( r1_tarski(sK1,k2_xboole_0(sK1,sK2)) = iProver_top ),
% 7.65/1.51      inference(instantiation,[status(thm)],[c_1427]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_13063,plain,
% 7.65/1.51      ( r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) != iProver_top ),
% 7.65/1.51      inference(global_propositional_subsumption,
% 7.65/1.51                [status(thm)],
% 7.65/1.51                [c_11803,c_14,c_15,c_755,c_758,c_850,c_948,c_1318,c_1429]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_13068,plain,
% 7.65/1.51      ( m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.65/1.51      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.65/1.51      | r1_tarski(sK2,k2_xboole_0(sK1,sK2)) != iProver_top ),
% 7.65/1.51      inference(superposition,[status(thm)],[c_669,c_13063]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_14204,plain,
% 7.65/1.51      ( r1_tarski(sK2,k2_xboole_0(sK1,sK2)) != iProver_top ),
% 7.65/1.51      inference(global_propositional_subsumption,
% 7.65/1.51                [status(thm)],
% 7.65/1.51                [c_13068,c_14,c_15,c_755,c_758,c_850,c_948]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_0,plain,
% 7.65/1.51      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 7.65/1.51      inference(cnf_transformation,[],[f26]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_337,plain,
% 7.65/1.51      ( r1_tarski(k4_xboole_0(X0_40,X1_40),X0_40) ),
% 7.65/1.51      inference(subtyping,[status(esa)],[c_0]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_660,plain,
% 7.65/1.51      ( r1_tarski(k4_xboole_0(X0_40,X1_40),X0_40) = iProver_top ),
% 7.65/1.51      inference(predicate_to_equality,[status(thm)],[c_337]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_1,plain,
% 7.65/1.51      ( r1_tarski(X0,k2_xboole_0(X1,X2)) | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ),
% 7.65/1.51      inference(cnf_transformation,[],[f27]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_336,plain,
% 7.65/1.51      ( r1_tarski(X0_40,k2_xboole_0(X1_40,X2_40))
% 7.65/1.51      | ~ r1_tarski(k4_xboole_0(X0_40,X1_40),X2_40) ),
% 7.65/1.51      inference(subtyping,[status(esa)],[c_1]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_661,plain,
% 7.65/1.51      ( r1_tarski(X0_40,k2_xboole_0(X1_40,X2_40)) = iProver_top
% 7.65/1.51      | r1_tarski(k4_xboole_0(X0_40,X1_40),X2_40) != iProver_top ),
% 7.65/1.51      inference(predicate_to_equality,[status(thm)],[c_336]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_1215,plain,
% 7.65/1.51      ( r1_tarski(X0_40,k2_xboole_0(X1_40,X0_40)) = iProver_top ),
% 7.65/1.51      inference(superposition,[status(thm)],[c_660,c_661]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_14209,plain,
% 7.65/1.51      ( $false ),
% 7.65/1.51      inference(forward_subsumption_resolution,[status(thm)],[c_14204,c_1215]) ).
% 7.65/1.51  
% 7.65/1.51  
% 7.65/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 7.65/1.51  
% 7.65/1.51  ------                               Statistics
% 7.65/1.51  
% 7.65/1.51  ------ General
% 7.65/1.51  
% 7.65/1.51  abstr_ref_over_cycles:                  0
% 7.65/1.51  abstr_ref_under_cycles:                 0
% 7.65/1.51  gc_basic_clause_elim:                   0
% 7.65/1.51  forced_gc_time:                         0
% 7.65/1.51  parsing_time:                           0.011
% 7.65/1.51  unif_index_cands_time:                  0.
% 7.65/1.51  unif_index_add_time:                    0.
% 7.65/1.51  orderings_time:                         0.
% 7.65/1.51  out_proof_time:                         0.015
% 7.65/1.51  total_time:                             0.665
% 7.65/1.51  num_of_symbols:                         46
% 7.65/1.51  num_of_terms:                           23761
% 7.65/1.51  
% 7.65/1.51  ------ Preprocessing
% 7.65/1.51  
% 7.65/1.51  num_of_splits:                          0
% 7.65/1.51  num_of_split_atoms:                     0
% 7.65/1.51  num_of_reused_defs:                     0
% 7.65/1.51  num_eq_ax_congr_red:                    14
% 7.65/1.51  num_of_sem_filtered_clauses:            1
% 7.65/1.51  num_of_subtypes:                        3
% 7.65/1.51  monotx_restored_types:                  0
% 7.65/1.51  sat_num_of_epr_types:                   0
% 7.65/1.51  sat_num_of_non_cyclic_types:            0
% 7.65/1.51  sat_guarded_non_collapsed_types:        0
% 7.65/1.51  num_pure_diseq_elim:                    0
% 7.65/1.51  simp_replaced_by:                       0
% 7.65/1.51  res_preprocessed:                       66
% 7.65/1.51  prep_upred:                             0
% 7.65/1.51  prep_unflattend:                        2
% 7.65/1.51  smt_new_axioms:                         0
% 7.65/1.51  pred_elim_cands:                        2
% 7.65/1.51  pred_elim:                              1
% 7.65/1.51  pred_elim_cl:                           1
% 7.65/1.51  pred_elim_cycles:                       3
% 7.65/1.51  merged_defs:                            8
% 7.65/1.51  merged_defs_ncl:                        0
% 7.65/1.51  bin_hyper_res:                          10
% 7.65/1.51  prep_cycles:                            4
% 7.65/1.51  pred_elim_time:                         0.001
% 7.65/1.51  splitting_time:                         0.
% 7.65/1.51  sem_filter_time:                        0.
% 7.65/1.51  monotx_time:                            0.
% 7.65/1.51  subtype_inf_time:                       0.
% 7.65/1.51  
% 7.65/1.51  ------ Problem properties
% 7.65/1.51  
% 7.65/1.51  clauses:                                12
% 7.65/1.51  conjectures:                            3
% 7.65/1.51  epr:                                    0
% 7.65/1.51  horn:                                   12
% 7.65/1.51  ground:                                 3
% 7.65/1.51  unary:                                  5
% 7.65/1.51  binary:                                 4
% 7.65/1.51  lits:                                   23
% 7.65/1.51  lits_eq:                                1
% 7.65/1.51  fd_pure:                                0
% 7.65/1.51  fd_pseudo:                              0
% 7.65/1.51  fd_cond:                                0
% 7.65/1.51  fd_pseudo_cond:                         0
% 7.65/1.51  ac_symbols:                             0
% 7.65/1.51  
% 7.65/1.51  ------ Propositional Solver
% 7.65/1.51  
% 7.65/1.51  prop_solver_calls:                      28
% 7.65/1.51  prop_fast_solver_calls:                 483
% 7.65/1.51  smt_solver_calls:                       0
% 7.65/1.51  smt_fast_solver_calls:                  0
% 7.65/1.51  prop_num_of_clauses:                    6108
% 7.65/1.51  prop_preprocess_simplified:             15850
% 7.65/1.51  prop_fo_subsumed:                       3
% 7.65/1.51  prop_solver_time:                       0.
% 7.65/1.51  smt_solver_time:                        0.
% 7.65/1.51  smt_fast_solver_time:                   0.
% 7.65/1.51  prop_fast_solver_time:                  0.
% 7.65/1.51  prop_unsat_core_time:                   0.
% 7.65/1.51  
% 7.65/1.51  ------ QBF
% 7.65/1.51  
% 7.65/1.51  qbf_q_res:                              0
% 7.65/1.51  qbf_num_tautologies:                    0
% 7.65/1.51  qbf_prep_cycles:                        0
% 7.65/1.51  
% 7.65/1.51  ------ BMC1
% 7.65/1.51  
% 7.65/1.51  bmc1_current_bound:                     -1
% 7.65/1.51  bmc1_last_solved_bound:                 -1
% 7.65/1.51  bmc1_unsat_core_size:                   -1
% 7.65/1.51  bmc1_unsat_core_parents_size:           -1
% 7.65/1.51  bmc1_merge_next_fun:                    0
% 7.65/1.51  bmc1_unsat_core_clauses_time:           0.
% 7.65/1.51  
% 7.65/1.51  ------ Instantiation
% 7.65/1.51  
% 7.65/1.51  inst_num_of_clauses:                    1710
% 7.65/1.51  inst_num_in_passive:                    1121
% 7.65/1.51  inst_num_in_active:                     564
% 7.65/1.51  inst_num_in_unprocessed:                25
% 7.65/1.51  inst_num_of_loops:                      610
% 7.65/1.51  inst_num_of_learning_restarts:          0
% 7.65/1.51  inst_num_moves_active_passive:          45
% 7.65/1.51  inst_lit_activity:                      0
% 7.65/1.51  inst_lit_activity_moves:                0
% 7.65/1.51  inst_num_tautologies:                   0
% 7.65/1.51  inst_num_prop_implied:                  0
% 7.65/1.51  inst_num_existing_simplified:           0
% 7.65/1.51  inst_num_eq_res_simplified:             0
% 7.65/1.51  inst_num_child_elim:                    0
% 7.65/1.51  inst_num_of_dismatching_blockings:      1502
% 7.65/1.51  inst_num_of_non_proper_insts:           1696
% 7.65/1.51  inst_num_of_duplicates:                 0
% 7.65/1.51  inst_inst_num_from_inst_to_res:         0
% 7.65/1.51  inst_dismatching_checking_time:         0.
% 7.65/1.51  
% 7.65/1.51  ------ Resolution
% 7.65/1.51  
% 7.65/1.51  res_num_of_clauses:                     0
% 7.65/1.51  res_num_in_passive:                     0
% 7.65/1.51  res_num_in_active:                      0
% 7.65/1.51  res_num_of_loops:                       70
% 7.65/1.51  res_forward_subset_subsumed:            163
% 7.65/1.51  res_backward_subset_subsumed:           2
% 7.65/1.51  res_forward_subsumed:                   0
% 7.65/1.51  res_backward_subsumed:                  0
% 7.65/1.51  res_forward_subsumption_resolution:     0
% 7.65/1.51  res_backward_subsumption_resolution:    0
% 7.65/1.51  res_clause_to_clause_subsumption:       1252
% 7.65/1.51  res_orphan_elimination:                 0
% 7.65/1.51  res_tautology_del:                      71
% 7.65/1.51  res_num_eq_res_simplified:              0
% 7.65/1.51  res_num_sel_changes:                    0
% 7.65/1.51  res_moves_from_active_to_pass:          0
% 7.65/1.51  
% 7.65/1.51  ------ Superposition
% 7.65/1.51  
% 7.65/1.51  sup_time_total:                         0.
% 7.65/1.51  sup_time_generating:                    0.
% 7.65/1.51  sup_time_sim_full:                      0.
% 7.65/1.51  sup_time_sim_immed:                     0.
% 7.65/1.51  
% 7.65/1.51  sup_num_of_clauses:                     250
% 7.65/1.51  sup_num_in_active:                      118
% 7.65/1.51  sup_num_in_passive:                     132
% 7.65/1.51  sup_num_of_loops:                       120
% 7.65/1.51  sup_fw_superposition:                   220
% 7.65/1.51  sup_bw_superposition:                   23
% 7.65/1.51  sup_immediate_simplified:               0
% 7.65/1.51  sup_given_eliminated:                   0
% 7.65/1.51  comparisons_done:                       0
% 7.65/1.51  comparisons_avoided:                    0
% 7.65/1.51  
% 7.65/1.51  ------ Simplifications
% 7.65/1.51  
% 7.65/1.51  
% 7.65/1.51  sim_fw_subset_subsumed:                 0
% 7.65/1.51  sim_bw_subset_subsumed:                 0
% 7.65/1.51  sim_fw_subsumed:                        0
% 7.65/1.51  sim_bw_subsumed:                        0
% 7.65/1.51  sim_fw_subsumption_res:                 1
% 7.65/1.51  sim_bw_subsumption_res:                 0
% 7.65/1.51  sim_tautology_del:                      1
% 7.65/1.51  sim_eq_tautology_del:                   0
% 7.65/1.51  sim_eq_res_simp:                        0
% 7.65/1.51  sim_fw_demodulated:                     0
% 7.65/1.51  sim_bw_demodulated:                     2
% 7.65/1.51  sim_light_normalised:                   0
% 7.65/1.51  sim_joinable_taut:                      0
% 7.65/1.51  sim_joinable_simp:                      0
% 7.65/1.51  sim_ac_normalised:                      0
% 7.65/1.51  sim_smt_subsumption:                    0
% 7.65/1.51  
%------------------------------------------------------------------------------
