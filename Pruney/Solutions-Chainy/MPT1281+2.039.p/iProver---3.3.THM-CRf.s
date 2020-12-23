%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:15:46 EST 2020

% Result     : Theorem 3.51s
% Output     : CNFRefutation 3.51s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 413 expanded)
%              Number of clauses        :   76 ( 142 expanded)
%              Number of leaves         :   12 (  96 expanded)
%              Depth                    :   18
%              Number of atoms          :  270 (1363 expanded)
%              Number of equality atoms :   96 ( 144 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v5_tops_1(X1,X0)
           => r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v5_tops_1(X1,X0)
             => r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1)))
          & v5_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1)))
          & v5_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1)))
          & v5_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_tarski(k2_tops_1(X0,sK1),k2_pre_topc(X0,k1_tops_1(X0,sK1)))
        & v5_tops_1(sK1,X0)
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1)))
            & v5_tops_1(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(sK0,X1),k2_pre_topc(sK0,k1_tops_1(sK0,X1)))
          & v5_tops_1(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))
    & v5_tops_1(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f27,f26])).

fof(f41,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f28])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f40,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f4,axiom,(
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
    inference(nnf_transformation,[],[f4])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v5_tops_1(X1,X0)
          <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_tops_1(X1,X0)
          <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_tops_1(X1,X0)
              | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1 )
            & ( k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1
              | ~ v5_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1
      | ~ v5_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f42,plain,(
    v5_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f43,plain,(
    ~ r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_608,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_926,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_608])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_14,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_233,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_14])).

cnf(c_234,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_233])).

cnf(c_602,plain,
    ( ~ m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k1_tops_1(sK0,X0_42),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_234])).

cnf(c_931,plain,
    ( m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k1_tops_1(sK0,X0_42),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_602])).

cnf(c_6,plain,
    ( r1_tarski(X0,k2_pre_topc(X1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_245,plain,
    ( r1_tarski(X0,k2_pre_topc(X1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_14])).

cnf(c_246,plain,
    ( r1_tarski(X0,k2_pre_topc(sK0,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_245])).

cnf(c_601,plain,
    ( r1_tarski(X0_42,k2_pre_topc(sK0,X0_42))
    | ~ m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_246])).

cnf(c_932,plain,
    ( r1_tarski(X0_42,k2_pre_topc(sK0,X0_42)) = iProver_top
    | m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_601])).

cnf(c_1132,plain,
    ( r1_tarski(k1_tops_1(sK0,X0_42),k2_pre_topc(sK0,k1_tops_1(sK0,X0_42))) = iProver_top
    | m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_931,c_932])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k4_xboole_0(X1,X0) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_119,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_3])).

cnf(c_142,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X1,X0) = k3_subset_1(X1,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_0,c_119])).

cnf(c_607,plain,
    ( ~ r1_tarski(X0_42,X1_42)
    | k4_xboole_0(X1_42,X0_42) = k3_subset_1(X1_42,X0_42) ),
    inference(subtyping,[status(esa)],[c_142])).

cnf(c_927,plain,
    ( k4_xboole_0(X0_42,X1_42) = k3_subset_1(X0_42,X1_42)
    | r1_tarski(X1_42,X0_42) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_607])).

cnf(c_2086,plain,
    ( k4_xboole_0(k2_pre_topc(sK0,k1_tops_1(sK0,X0_42)),k1_tops_1(sK0,X0_42)) = k3_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,X0_42)),k1_tops_1(sK0,X0_42))
    | m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1132,c_927])).

cnf(c_10137,plain,
    ( k4_xboole_0(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1)) = k3_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_926,c_2086])).

cnf(c_8,plain,
    ( ~ v5_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k1_tops_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_12,negated_conjecture,
    ( v5_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_212,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k1_tops_1(X1,X0)) = X0
    | sK1 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_12])).

cnf(c_213,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = sK1 ),
    inference(unflattening,[status(thm)],[c_212])).

cnf(c_215,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_213,c_14,c_13])).

cnf(c_604,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = sK1 ),
    inference(subtyping,[status(esa)],[c_215])).

cnf(c_4,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_610,plain,
    ( r1_tarski(X0_42,X1_42)
    | ~ m1_subset_1(X0_42,k1_zfmisc_1(X1_42)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_924,plain,
    ( r1_tarski(X0_42,X1_42) = iProver_top
    | m1_subset_1(X0_42,k1_zfmisc_1(X1_42)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_610])).

cnf(c_1272,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_926,c_924])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_144,plain,
    ( ~ r1_tarski(X0,X1)
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_2,c_119])).

cnf(c_605,plain,
    ( ~ r1_tarski(X0_42,X1_42)
    | k7_subset_1(X1_42,X0_42,X2_42) = k4_xboole_0(X0_42,X2_42) ),
    inference(subtyping,[status(esa)],[c_144])).

cnf(c_929,plain,
    ( k7_subset_1(X0_42,X1_42,X2_42) = k4_xboole_0(X1_42,X2_42)
    | r1_tarski(X1_42,X0_42) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_605])).

cnf(c_1738,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0_42) = k4_xboole_0(sK1,X0_42) ),
    inference(superposition,[status(thm)],[c_1272,c_929])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k2_pre_topc(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_257,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,k2_pre_topc(X1,X0)) = k2_pre_topc(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_14])).

cnf(c_258,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k2_pre_topc(sK0,X0)) = k2_pre_topc(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_257])).

cnf(c_600,plain,
    ( ~ m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k2_pre_topc(sK0,X0_42)) = k2_pre_topc(sK0,X0_42) ),
    inference(subtyping,[status(esa)],[c_258])).

cnf(c_933,plain,
    ( k2_pre_topc(sK0,k2_pre_topc(sK0,X0_42)) = k2_pre_topc(sK0,X0_42)
    | m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_600])).

cnf(c_1185,plain,
    ( k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,X0_42))) = k2_pre_topc(sK0,k1_tops_1(sK0,X0_42))
    | m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_931,c_933])).

cnf(c_2202,plain,
    ( k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_926,c_1185])).

cnf(c_2206,plain,
    ( k2_pre_topc(sK0,sK1) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2202,c_604])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_221,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_14])).

cnf(c_222,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_221])).

cnf(c_603,plain,
    ( ~ m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0_42),k1_tops_1(sK0,X0_42)) = k2_tops_1(sK0,X0_42) ),
    inference(subtyping,[status(esa)],[c_222])).

cnf(c_930,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0_42),k1_tops_1(sK0,X0_42)) = k2_tops_1(sK0,X0_42)
    | m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_603])).

cnf(c_1405,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_926,c_930])).

cnf(c_2347,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_2206,c_1405])).

cnf(c_2688,plain,
    ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_1738,c_2347])).

cnf(c_10141,plain,
    ( k3_subset_1(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_10137,c_604,c_2688])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_143,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(bin_hyper_res,[status(thm)],[c_1,c_119])).

cnf(c_606,plain,
    ( ~ r1_tarski(X0_42,X1_42)
    | m1_subset_1(k3_subset_1(X1_42,X0_42),k1_zfmisc_1(X1_42)) ),
    inference(subtyping,[status(esa)],[c_143])).

cnf(c_928,plain,
    ( r1_tarski(X0_42,X1_42) != iProver_top
    | m1_subset_1(k3_subset_1(X1_42,X0_42),k1_zfmisc_1(X1_42)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_606])).

cnf(c_1394,plain,
    ( r1_tarski(X0_42,X1_42) != iProver_top
    | r1_tarski(k3_subset_1(X1_42,X0_42),X1_42) = iProver_top ),
    inference(superposition,[status(thm)],[c_928,c_924])).

cnf(c_10495,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_10141,c_1394])).

cnf(c_611,plain,
    ( ~ r1_tarski(X0_42,X1_42)
    | m1_subset_1(X0_42,k1_zfmisc_1(X1_42)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_923,plain,
    ( r1_tarski(X0_42,X1_42) != iProver_top
    | m1_subset_1(X0_42,k1_zfmisc_1(X1_42)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_611])).

cnf(c_1268,plain,
    ( r1_tarski(X0_42,k2_pre_topc(sK0,X0_42)) = iProver_top
    | r1_tarski(X0_42,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_923,c_932])).

cnf(c_1560,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_604,c_1268])).

cnf(c_1029,plain,
    ( r1_tarski(k1_tops_1(sK0,X0_42),u1_struct_0(sK0))
    | ~ m1_subset_1(k1_tops_1(sK0,X0_42),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_610])).

cnf(c_1030,plain,
    ( r1_tarski(k1_tops_1(sK0,X0_42),u1_struct_0(sK0)) = iProver_top
    | m1_subset_1(k1_tops_1(sK0,X0_42),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1029])).

cnf(c_1032,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) = iProver_top
    | m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1030])).

cnf(c_11,negated_conjecture,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_609,negated_conjecture,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_925,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_609])).

cnf(c_934,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_925,c_604])).

cnf(c_653,plain,
    ( m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k1_tops_1(sK0,X0_42),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_602])).

cnf(c_655,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_653])).

cnf(c_16,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10495,c_1560,c_1032,c_934,c_655,c_16])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:18:08 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.51/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.51/0.98  
% 3.51/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.51/0.98  
% 3.51/0.98  ------  iProver source info
% 3.51/0.98  
% 3.51/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.51/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.51/0.98  git: non_committed_changes: false
% 3.51/0.98  git: last_make_outside_of_git: false
% 3.51/0.98  
% 3.51/0.98  ------ 
% 3.51/0.98  
% 3.51/0.98  ------ Input Options
% 3.51/0.98  
% 3.51/0.98  --out_options                           all
% 3.51/0.98  --tptp_safe_out                         true
% 3.51/0.98  --problem_path                          ""
% 3.51/0.98  --include_path                          ""
% 3.51/0.98  --clausifier                            res/vclausify_rel
% 3.51/0.98  --clausifier_options                    ""
% 3.51/0.98  --stdin                                 false
% 3.51/0.98  --stats_out                             all
% 3.51/0.98  
% 3.51/0.98  ------ General Options
% 3.51/0.98  
% 3.51/0.98  --fof                                   false
% 3.51/0.98  --time_out_real                         305.
% 3.51/0.98  --time_out_virtual                      -1.
% 3.51/0.98  --symbol_type_check                     false
% 3.51/0.98  --clausify_out                          false
% 3.51/0.98  --sig_cnt_out                           false
% 3.51/0.98  --trig_cnt_out                          false
% 3.51/0.98  --trig_cnt_out_tolerance                1.
% 3.51/0.98  --trig_cnt_out_sk_spl                   false
% 3.51/0.98  --abstr_cl_out                          false
% 3.51/0.98  
% 3.51/0.98  ------ Global Options
% 3.51/0.98  
% 3.51/0.98  --schedule                              default
% 3.51/0.98  --add_important_lit                     false
% 3.51/0.98  --prop_solver_per_cl                    1000
% 3.51/0.98  --min_unsat_core                        false
% 3.51/0.98  --soft_assumptions                      false
% 3.51/0.98  --soft_lemma_size                       3
% 3.51/0.98  --prop_impl_unit_size                   0
% 3.51/0.98  --prop_impl_unit                        []
% 3.51/0.98  --share_sel_clauses                     true
% 3.51/0.98  --reset_solvers                         false
% 3.51/0.98  --bc_imp_inh                            [conj_cone]
% 3.51/0.98  --conj_cone_tolerance                   3.
% 3.51/0.98  --extra_neg_conj                        none
% 3.51/0.98  --large_theory_mode                     true
% 3.51/0.98  --prolific_symb_bound                   200
% 3.51/0.98  --lt_threshold                          2000
% 3.51/0.98  --clause_weak_htbl                      true
% 3.51/0.98  --gc_record_bc_elim                     false
% 3.51/0.98  
% 3.51/0.98  ------ Preprocessing Options
% 3.51/0.98  
% 3.51/0.98  --preprocessing_flag                    true
% 3.51/0.98  --time_out_prep_mult                    0.1
% 3.51/0.98  --splitting_mode                        input
% 3.51/0.98  --splitting_grd                         true
% 3.51/0.98  --splitting_cvd                         false
% 3.51/0.98  --splitting_cvd_svl                     false
% 3.51/0.98  --splitting_nvd                         32
% 3.51/0.98  --sub_typing                            true
% 3.51/0.98  --prep_gs_sim                           true
% 3.51/0.98  --prep_unflatten                        true
% 3.51/0.98  --prep_res_sim                          true
% 3.51/0.98  --prep_upred                            true
% 3.51/0.98  --prep_sem_filter                       exhaustive
% 3.51/0.98  --prep_sem_filter_out                   false
% 3.51/0.98  --pred_elim                             true
% 3.51/0.98  --res_sim_input                         true
% 3.51/0.98  --eq_ax_congr_red                       true
% 3.51/0.98  --pure_diseq_elim                       true
% 3.51/0.98  --brand_transform                       false
% 3.51/0.98  --non_eq_to_eq                          false
% 3.51/0.98  --prep_def_merge                        true
% 3.51/0.98  --prep_def_merge_prop_impl              false
% 3.51/0.98  --prep_def_merge_mbd                    true
% 3.51/0.98  --prep_def_merge_tr_red                 false
% 3.51/0.98  --prep_def_merge_tr_cl                  false
% 3.51/0.98  --smt_preprocessing                     true
% 3.51/0.98  --smt_ac_axioms                         fast
% 3.51/0.98  --preprocessed_out                      false
% 3.51/0.98  --preprocessed_stats                    false
% 3.51/0.98  
% 3.51/0.98  ------ Abstraction refinement Options
% 3.51/0.98  
% 3.51/0.98  --abstr_ref                             []
% 3.51/0.98  --abstr_ref_prep                        false
% 3.51/0.98  --abstr_ref_until_sat                   false
% 3.51/0.98  --abstr_ref_sig_restrict                funpre
% 3.51/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.51/0.98  --abstr_ref_under                       []
% 3.51/0.98  
% 3.51/0.98  ------ SAT Options
% 3.51/0.98  
% 3.51/0.98  --sat_mode                              false
% 3.51/0.98  --sat_fm_restart_options                ""
% 3.51/0.98  --sat_gr_def                            false
% 3.51/0.98  --sat_epr_types                         true
% 3.51/0.98  --sat_non_cyclic_types                  false
% 3.51/0.98  --sat_finite_models                     false
% 3.51/0.98  --sat_fm_lemmas                         false
% 3.51/0.98  --sat_fm_prep                           false
% 3.51/0.98  --sat_fm_uc_incr                        true
% 3.51/0.98  --sat_out_model                         small
% 3.51/0.98  --sat_out_clauses                       false
% 3.51/0.98  
% 3.51/0.98  ------ QBF Options
% 3.51/0.98  
% 3.51/0.98  --qbf_mode                              false
% 3.51/0.98  --qbf_elim_univ                         false
% 3.51/0.98  --qbf_dom_inst                          none
% 3.51/0.98  --qbf_dom_pre_inst                      false
% 3.51/0.98  --qbf_sk_in                             false
% 3.51/0.98  --qbf_pred_elim                         true
% 3.51/0.98  --qbf_split                             512
% 3.51/0.98  
% 3.51/0.98  ------ BMC1 Options
% 3.51/0.98  
% 3.51/0.98  --bmc1_incremental                      false
% 3.51/0.98  --bmc1_axioms                           reachable_all
% 3.51/0.98  --bmc1_min_bound                        0
% 3.51/0.98  --bmc1_max_bound                        -1
% 3.51/0.98  --bmc1_max_bound_default                -1
% 3.51/0.98  --bmc1_symbol_reachability              true
% 3.51/0.98  --bmc1_property_lemmas                  false
% 3.51/0.98  --bmc1_k_induction                      false
% 3.51/0.98  --bmc1_non_equiv_states                 false
% 3.51/0.98  --bmc1_deadlock                         false
% 3.51/0.98  --bmc1_ucm                              false
% 3.51/0.98  --bmc1_add_unsat_core                   none
% 3.51/0.98  --bmc1_unsat_core_children              false
% 3.51/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.51/0.98  --bmc1_out_stat                         full
% 3.51/0.98  --bmc1_ground_init                      false
% 3.51/0.98  --bmc1_pre_inst_next_state              false
% 3.51/0.98  --bmc1_pre_inst_state                   false
% 3.51/0.98  --bmc1_pre_inst_reach_state             false
% 3.51/0.98  --bmc1_out_unsat_core                   false
% 3.51/0.98  --bmc1_aig_witness_out                  false
% 3.51/0.98  --bmc1_verbose                          false
% 3.51/0.98  --bmc1_dump_clauses_tptp                false
% 3.51/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.51/0.98  --bmc1_dump_file                        -
% 3.51/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.51/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.51/0.98  --bmc1_ucm_extend_mode                  1
% 3.51/0.98  --bmc1_ucm_init_mode                    2
% 3.51/0.98  --bmc1_ucm_cone_mode                    none
% 3.51/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.51/0.98  --bmc1_ucm_relax_model                  4
% 3.51/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.51/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.51/0.98  --bmc1_ucm_layered_model                none
% 3.51/0.98  --bmc1_ucm_max_lemma_size               10
% 3.51/0.98  
% 3.51/0.98  ------ AIG Options
% 3.51/0.98  
% 3.51/0.98  --aig_mode                              false
% 3.51/0.98  
% 3.51/0.98  ------ Instantiation Options
% 3.51/0.98  
% 3.51/0.98  --instantiation_flag                    true
% 3.51/0.98  --inst_sos_flag                         true
% 3.51/0.98  --inst_sos_phase                        true
% 3.51/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.51/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.51/0.98  --inst_lit_sel_side                     num_symb
% 3.51/0.98  --inst_solver_per_active                1400
% 3.51/0.98  --inst_solver_calls_frac                1.
% 3.51/0.98  --inst_passive_queue_type               priority_queues
% 3.51/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.51/0.98  --inst_passive_queues_freq              [25;2]
% 3.51/0.98  --inst_dismatching                      true
% 3.51/0.98  --inst_eager_unprocessed_to_passive     true
% 3.51/0.98  --inst_prop_sim_given                   true
% 3.51/0.98  --inst_prop_sim_new                     false
% 3.51/0.98  --inst_subs_new                         false
% 3.51/0.98  --inst_eq_res_simp                      false
% 3.51/0.98  --inst_subs_given                       false
% 3.51/0.98  --inst_orphan_elimination               true
% 3.51/0.98  --inst_learning_loop_flag               true
% 3.51/0.98  --inst_learning_start                   3000
% 3.51/0.98  --inst_learning_factor                  2
% 3.51/0.98  --inst_start_prop_sim_after_learn       3
% 3.51/0.98  --inst_sel_renew                        solver
% 3.51/0.98  --inst_lit_activity_flag                true
% 3.51/0.98  --inst_restr_to_given                   false
% 3.51/0.98  --inst_activity_threshold               500
% 3.51/0.98  --inst_out_proof                        true
% 3.51/0.98  
% 3.51/0.98  ------ Resolution Options
% 3.51/0.98  
% 3.51/0.98  --resolution_flag                       true
% 3.51/0.98  --res_lit_sel                           adaptive
% 3.51/0.98  --res_lit_sel_side                      none
% 3.51/0.98  --res_ordering                          kbo
% 3.51/0.98  --res_to_prop_solver                    active
% 3.51/0.98  --res_prop_simpl_new                    false
% 3.51/0.98  --res_prop_simpl_given                  true
% 3.51/0.98  --res_passive_queue_type                priority_queues
% 3.51/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.51/0.98  --res_passive_queues_freq               [15;5]
% 3.51/0.98  --res_forward_subs                      full
% 3.51/0.98  --res_backward_subs                     full
% 3.51/0.98  --res_forward_subs_resolution           true
% 3.51/0.98  --res_backward_subs_resolution          true
% 3.51/0.98  --res_orphan_elimination                true
% 3.51/0.98  --res_time_limit                        2.
% 3.51/0.98  --res_out_proof                         true
% 3.51/0.98  
% 3.51/0.98  ------ Superposition Options
% 3.51/0.98  
% 3.51/0.98  --superposition_flag                    true
% 3.51/0.98  --sup_passive_queue_type                priority_queues
% 3.51/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.51/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.51/0.98  --demod_completeness_check              fast
% 3.51/0.98  --demod_use_ground                      true
% 3.51/0.98  --sup_to_prop_solver                    passive
% 3.51/0.98  --sup_prop_simpl_new                    true
% 3.51/0.98  --sup_prop_simpl_given                  true
% 3.51/0.98  --sup_fun_splitting                     true
% 3.51/0.98  --sup_smt_interval                      50000
% 3.51/0.98  
% 3.51/0.98  ------ Superposition Simplification Setup
% 3.51/0.98  
% 3.51/0.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.51/0.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.51/0.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.51/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.51/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.51/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.51/0.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.51/0.98  --sup_immed_triv                        [TrivRules]
% 3.51/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.51/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.51/0.98  --sup_immed_bw_main                     []
% 3.51/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.51/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.51/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.51/0.98  --sup_input_bw                          []
% 3.51/0.98  
% 3.51/0.98  ------ Combination Options
% 3.51/0.98  
% 3.51/0.98  --comb_res_mult                         3
% 3.51/0.98  --comb_sup_mult                         2
% 3.51/0.98  --comb_inst_mult                        10
% 3.51/0.98  
% 3.51/0.98  ------ Debug Options
% 3.51/0.98  
% 3.51/0.98  --dbg_backtrace                         false
% 3.51/0.98  --dbg_dump_prop_clauses                 false
% 3.51/0.98  --dbg_dump_prop_clauses_file            -
% 3.51/0.98  --dbg_out_stat                          false
% 3.51/0.98  ------ Parsing...
% 3.51/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.51/0.98  
% 3.51/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.51/0.98  
% 3.51/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.51/0.98  
% 3.51/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.51/0.98  ------ Proving...
% 3.51/0.98  ------ Problem Properties 
% 3.51/0.98  
% 3.51/0.98  
% 3.51/0.98  clauses                                 12
% 3.51/0.98  conjectures                             2
% 3.51/0.98  EPR                                     0
% 3.51/0.98  Horn                                    12
% 3.51/0.98  unary                                   3
% 3.51/0.98  binary                                  9
% 3.51/0.98  lits                                    21
% 3.51/0.98  lits eq                                 5
% 3.51/0.98  fd_pure                                 0
% 3.51/0.98  fd_pseudo                               0
% 3.51/0.98  fd_cond                                 0
% 3.51/0.98  fd_pseudo_cond                          0
% 3.51/0.98  AC symbols                              0
% 3.51/0.98  
% 3.51/0.98  ------ Schedule dynamic 5 is on 
% 3.51/0.98  
% 3.51/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.51/0.98  
% 3.51/0.98  
% 3.51/0.98  ------ 
% 3.51/0.98  Current options:
% 3.51/0.98  ------ 
% 3.51/0.98  
% 3.51/0.98  ------ Input Options
% 3.51/0.98  
% 3.51/0.98  --out_options                           all
% 3.51/0.98  --tptp_safe_out                         true
% 3.51/0.98  --problem_path                          ""
% 3.51/0.98  --include_path                          ""
% 3.51/0.98  --clausifier                            res/vclausify_rel
% 3.51/0.98  --clausifier_options                    ""
% 3.51/0.98  --stdin                                 false
% 3.51/0.98  --stats_out                             all
% 3.51/0.98  
% 3.51/0.98  ------ General Options
% 3.51/0.98  
% 3.51/0.98  --fof                                   false
% 3.51/0.98  --time_out_real                         305.
% 3.51/0.98  --time_out_virtual                      -1.
% 3.51/0.98  --symbol_type_check                     false
% 3.51/0.98  --clausify_out                          false
% 3.51/0.98  --sig_cnt_out                           false
% 3.51/0.98  --trig_cnt_out                          false
% 3.51/0.98  --trig_cnt_out_tolerance                1.
% 3.51/0.98  --trig_cnt_out_sk_spl                   false
% 3.51/0.98  --abstr_cl_out                          false
% 3.51/0.98  
% 3.51/0.98  ------ Global Options
% 3.51/0.98  
% 3.51/0.98  --schedule                              default
% 3.51/0.98  --add_important_lit                     false
% 3.51/0.98  --prop_solver_per_cl                    1000
% 3.51/0.98  --min_unsat_core                        false
% 3.51/0.98  --soft_assumptions                      false
% 3.51/0.98  --soft_lemma_size                       3
% 3.51/0.98  --prop_impl_unit_size                   0
% 3.51/0.98  --prop_impl_unit                        []
% 3.51/0.98  --share_sel_clauses                     true
% 3.51/0.98  --reset_solvers                         false
% 3.51/0.98  --bc_imp_inh                            [conj_cone]
% 3.51/0.98  --conj_cone_tolerance                   3.
% 3.51/0.98  --extra_neg_conj                        none
% 3.51/0.98  --large_theory_mode                     true
% 3.51/0.98  --prolific_symb_bound                   200
% 3.51/0.98  --lt_threshold                          2000
% 3.51/0.98  --clause_weak_htbl                      true
% 3.51/0.98  --gc_record_bc_elim                     false
% 3.51/0.98  
% 3.51/0.98  ------ Preprocessing Options
% 3.51/0.98  
% 3.51/0.98  --preprocessing_flag                    true
% 3.51/0.98  --time_out_prep_mult                    0.1
% 3.51/0.98  --splitting_mode                        input
% 3.51/0.98  --splitting_grd                         true
% 3.51/0.98  --splitting_cvd                         false
% 3.51/0.98  --splitting_cvd_svl                     false
% 3.51/0.98  --splitting_nvd                         32
% 3.51/0.98  --sub_typing                            true
% 3.51/0.98  --prep_gs_sim                           true
% 3.51/0.98  --prep_unflatten                        true
% 3.51/0.98  --prep_res_sim                          true
% 3.51/0.98  --prep_upred                            true
% 3.51/0.98  --prep_sem_filter                       exhaustive
% 3.51/0.98  --prep_sem_filter_out                   false
% 3.51/0.98  --pred_elim                             true
% 3.51/0.98  --res_sim_input                         true
% 3.51/0.98  --eq_ax_congr_red                       true
% 3.51/0.98  --pure_diseq_elim                       true
% 3.51/0.98  --brand_transform                       false
% 3.51/0.98  --non_eq_to_eq                          false
% 3.51/0.98  --prep_def_merge                        true
% 3.51/0.98  --prep_def_merge_prop_impl              false
% 3.51/0.98  --prep_def_merge_mbd                    true
% 3.51/0.98  --prep_def_merge_tr_red                 false
% 3.51/0.98  --prep_def_merge_tr_cl                  false
% 3.51/0.98  --smt_preprocessing                     true
% 3.51/0.98  --smt_ac_axioms                         fast
% 3.51/0.98  --preprocessed_out                      false
% 3.51/0.98  --preprocessed_stats                    false
% 3.51/0.98  
% 3.51/0.98  ------ Abstraction refinement Options
% 3.51/0.98  
% 3.51/0.98  --abstr_ref                             []
% 3.51/0.98  --abstr_ref_prep                        false
% 3.51/0.98  --abstr_ref_until_sat                   false
% 3.51/0.98  --abstr_ref_sig_restrict                funpre
% 3.51/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.51/0.98  --abstr_ref_under                       []
% 3.51/0.98  
% 3.51/0.98  ------ SAT Options
% 3.51/0.98  
% 3.51/0.98  --sat_mode                              false
% 3.51/0.98  --sat_fm_restart_options                ""
% 3.51/0.98  --sat_gr_def                            false
% 3.51/0.98  --sat_epr_types                         true
% 3.51/0.98  --sat_non_cyclic_types                  false
% 3.51/0.98  --sat_finite_models                     false
% 3.51/0.98  --sat_fm_lemmas                         false
% 3.51/0.98  --sat_fm_prep                           false
% 3.51/0.98  --sat_fm_uc_incr                        true
% 3.51/0.98  --sat_out_model                         small
% 3.51/0.98  --sat_out_clauses                       false
% 3.51/0.98  
% 3.51/0.98  ------ QBF Options
% 3.51/0.98  
% 3.51/0.98  --qbf_mode                              false
% 3.51/0.98  --qbf_elim_univ                         false
% 3.51/0.98  --qbf_dom_inst                          none
% 3.51/0.98  --qbf_dom_pre_inst                      false
% 3.51/0.98  --qbf_sk_in                             false
% 3.51/0.98  --qbf_pred_elim                         true
% 3.51/0.98  --qbf_split                             512
% 3.51/0.98  
% 3.51/0.98  ------ BMC1 Options
% 3.51/0.98  
% 3.51/0.98  --bmc1_incremental                      false
% 3.51/0.98  --bmc1_axioms                           reachable_all
% 3.51/0.98  --bmc1_min_bound                        0
% 3.51/0.98  --bmc1_max_bound                        -1
% 3.51/0.98  --bmc1_max_bound_default                -1
% 3.51/0.98  --bmc1_symbol_reachability              true
% 3.51/0.98  --bmc1_property_lemmas                  false
% 3.51/0.98  --bmc1_k_induction                      false
% 3.51/0.98  --bmc1_non_equiv_states                 false
% 3.51/0.98  --bmc1_deadlock                         false
% 3.51/0.98  --bmc1_ucm                              false
% 3.51/0.98  --bmc1_add_unsat_core                   none
% 3.51/0.98  --bmc1_unsat_core_children              false
% 3.51/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.51/0.98  --bmc1_out_stat                         full
% 3.51/0.98  --bmc1_ground_init                      false
% 3.51/0.98  --bmc1_pre_inst_next_state              false
% 3.51/0.98  --bmc1_pre_inst_state                   false
% 3.51/0.98  --bmc1_pre_inst_reach_state             false
% 3.51/0.98  --bmc1_out_unsat_core                   false
% 3.51/0.98  --bmc1_aig_witness_out                  false
% 3.51/0.98  --bmc1_verbose                          false
% 3.51/0.98  --bmc1_dump_clauses_tptp                false
% 3.51/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.51/0.98  --bmc1_dump_file                        -
% 3.51/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.51/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.51/0.98  --bmc1_ucm_extend_mode                  1
% 3.51/0.98  --bmc1_ucm_init_mode                    2
% 3.51/0.98  --bmc1_ucm_cone_mode                    none
% 3.51/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.51/0.98  --bmc1_ucm_relax_model                  4
% 3.51/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.51/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.51/0.98  --bmc1_ucm_layered_model                none
% 3.51/0.98  --bmc1_ucm_max_lemma_size               10
% 3.51/0.98  
% 3.51/0.98  ------ AIG Options
% 3.51/0.98  
% 3.51/0.98  --aig_mode                              false
% 3.51/0.98  
% 3.51/0.98  ------ Instantiation Options
% 3.51/0.98  
% 3.51/0.98  --instantiation_flag                    true
% 3.51/0.98  --inst_sos_flag                         true
% 3.51/0.98  --inst_sos_phase                        true
% 3.51/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.51/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.51/0.98  --inst_lit_sel_side                     none
% 3.51/0.98  --inst_solver_per_active                1400
% 3.51/0.98  --inst_solver_calls_frac                1.
% 3.51/0.98  --inst_passive_queue_type               priority_queues
% 3.51/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.51/0.98  --inst_passive_queues_freq              [25;2]
% 3.51/0.98  --inst_dismatching                      true
% 3.51/0.98  --inst_eager_unprocessed_to_passive     true
% 3.51/0.98  --inst_prop_sim_given                   true
% 3.51/0.98  --inst_prop_sim_new                     false
% 3.51/0.98  --inst_subs_new                         false
% 3.51/0.98  --inst_eq_res_simp                      false
% 3.51/0.98  --inst_subs_given                       false
% 3.51/0.98  --inst_orphan_elimination               true
% 3.51/0.98  --inst_learning_loop_flag               true
% 3.51/0.98  --inst_learning_start                   3000
% 3.51/0.98  --inst_learning_factor                  2
% 3.51/0.98  --inst_start_prop_sim_after_learn       3
% 3.51/0.98  --inst_sel_renew                        solver
% 3.51/0.98  --inst_lit_activity_flag                true
% 3.51/0.98  --inst_restr_to_given                   false
% 3.51/0.98  --inst_activity_threshold               500
% 3.51/0.98  --inst_out_proof                        true
% 3.51/0.98  
% 3.51/0.98  ------ Resolution Options
% 3.51/0.98  
% 3.51/0.98  --resolution_flag                       false
% 3.51/0.98  --res_lit_sel                           adaptive
% 3.51/0.98  --res_lit_sel_side                      none
% 3.51/0.98  --res_ordering                          kbo
% 3.51/0.98  --res_to_prop_solver                    active
% 3.51/0.98  --res_prop_simpl_new                    false
% 3.51/0.98  --res_prop_simpl_given                  true
% 3.51/0.98  --res_passive_queue_type                priority_queues
% 3.51/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.51/0.98  --res_passive_queues_freq               [15;5]
% 3.51/0.98  --res_forward_subs                      full
% 3.51/0.98  --res_backward_subs                     full
% 3.51/0.98  --res_forward_subs_resolution           true
% 3.51/0.98  --res_backward_subs_resolution          true
% 3.51/0.98  --res_orphan_elimination                true
% 3.51/0.98  --res_time_limit                        2.
% 3.51/0.98  --res_out_proof                         true
% 3.51/0.98  
% 3.51/0.98  ------ Superposition Options
% 3.51/0.98  
% 3.51/0.98  --superposition_flag                    true
% 3.51/0.98  --sup_passive_queue_type                priority_queues
% 3.51/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.51/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.51/0.98  --demod_completeness_check              fast
% 3.51/0.98  --demod_use_ground                      true
% 3.51/0.98  --sup_to_prop_solver                    passive
% 3.51/0.98  --sup_prop_simpl_new                    true
% 3.51/0.98  --sup_prop_simpl_given                  true
% 3.51/0.98  --sup_fun_splitting                     true
% 3.51/0.98  --sup_smt_interval                      50000
% 3.51/0.98  
% 3.51/0.98  ------ Superposition Simplification Setup
% 3.51/0.98  
% 3.51/0.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.51/0.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.51/0.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.51/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.51/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.51/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.51/0.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.51/0.98  --sup_immed_triv                        [TrivRules]
% 3.51/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.51/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.51/0.98  --sup_immed_bw_main                     []
% 3.51/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.51/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.51/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.51/0.98  --sup_input_bw                          []
% 3.51/0.98  
% 3.51/0.98  ------ Combination Options
% 3.51/0.98  
% 3.51/0.98  --comb_res_mult                         3
% 3.51/0.98  --comb_sup_mult                         2
% 3.51/0.98  --comb_inst_mult                        10
% 3.51/0.98  
% 3.51/0.98  ------ Debug Options
% 3.51/0.98  
% 3.51/0.98  --dbg_backtrace                         false
% 3.51/0.98  --dbg_dump_prop_clauses                 false
% 3.51/0.98  --dbg_dump_prop_clauses_file            -
% 3.51/0.98  --dbg_out_stat                          false
% 3.51/0.98  
% 3.51/0.98  
% 3.51/0.98  
% 3.51/0.98  
% 3.51/0.98  ------ Proving...
% 3.51/0.98  
% 3.51/0.98  
% 3.51/0.98  % SZS status Theorem for theBenchmark.p
% 3.51/0.98  
% 3.51/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.51/0.98  
% 3.51/0.98  fof(f10,conjecture,(
% 3.51/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v5_tops_1(X1,X0) => r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))))))),
% 3.51/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/0.98  
% 3.51/0.98  fof(f11,negated_conjecture,(
% 3.51/0.98    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v5_tops_1(X1,X0) => r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))))))),
% 3.51/0.98    inference(negated_conjecture,[],[f10])).
% 3.51/0.98  
% 3.51/0.98  fof(f22,plain,(
% 3.51/0.98    ? [X0] : (? [X1] : ((~r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))) & v5_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.51/0.98    inference(ennf_transformation,[],[f11])).
% 3.51/0.98  
% 3.51/0.98  fof(f23,plain,(
% 3.51/0.98    ? [X0] : (? [X1] : (~r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))) & v5_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.51/0.98    inference(flattening,[],[f22])).
% 3.51/0.98  
% 3.51/0.98  fof(f27,plain,(
% 3.51/0.98    ( ! [X0] : (? [X1] : (~r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))) & v5_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~r1_tarski(k2_tops_1(X0,sK1),k2_pre_topc(X0,k1_tops_1(X0,sK1))) & v5_tops_1(sK1,X0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.51/0.98    introduced(choice_axiom,[])).
% 3.51/0.98  
% 3.51/0.98  fof(f26,plain,(
% 3.51/0.98    ? [X0] : (? [X1] : (~r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))) & v5_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (~r1_tarski(k2_tops_1(sK0,X1),k2_pre_topc(sK0,k1_tops_1(sK0,X1))) & v5_tops_1(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 3.51/0.98    introduced(choice_axiom,[])).
% 3.51/0.98  
% 3.51/0.98  fof(f28,plain,(
% 3.51/0.98    (~r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) & v5_tops_1(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 3.51/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f27,f26])).
% 3.51/0.98  
% 3.51/0.98  fof(f41,plain,(
% 3.51/0.98    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.51/0.98    inference(cnf_transformation,[],[f28])).
% 3.51/0.98  
% 3.51/0.98  fof(f8,axiom,(
% 3.51/0.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.51/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/0.98  
% 3.51/0.98  fof(f19,plain,(
% 3.51/0.98    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.51/0.98    inference(ennf_transformation,[],[f8])).
% 3.51/0.98  
% 3.51/0.98  fof(f20,plain,(
% 3.51/0.98    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.51/0.98    inference(flattening,[],[f19])).
% 3.51/0.98  
% 3.51/0.98  fof(f38,plain,(
% 3.51/0.98    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.51/0.98    inference(cnf_transformation,[],[f20])).
% 3.51/0.98  
% 3.51/0.98  fof(f40,plain,(
% 3.51/0.98    l1_pre_topc(sK0)),
% 3.51/0.98    inference(cnf_transformation,[],[f28])).
% 3.51/0.98  
% 3.51/0.98  fof(f6,axiom,(
% 3.51/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 3.51/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/0.98  
% 3.51/0.98  fof(f17,plain,(
% 3.51/0.98    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.51/0.98    inference(ennf_transformation,[],[f6])).
% 3.51/0.98  
% 3.51/0.98  fof(f35,plain,(
% 3.51/0.98    ( ! [X0,X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.51/0.98    inference(cnf_transformation,[],[f17])).
% 3.51/0.98  
% 3.51/0.98  fof(f1,axiom,(
% 3.51/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1))),
% 3.51/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/0.98  
% 3.51/0.98  fof(f12,plain,(
% 3.51/0.98    ! [X0,X1] : (k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.51/0.98    inference(ennf_transformation,[],[f1])).
% 3.51/0.98  
% 3.51/0.98  fof(f29,plain,(
% 3.51/0.98    ( ! [X0,X1] : (k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.51/0.98    inference(cnf_transformation,[],[f12])).
% 3.51/0.98  
% 3.51/0.98  fof(f4,axiom,(
% 3.51/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.51/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/0.98  
% 3.51/0.98  fof(f24,plain,(
% 3.51/0.98    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.51/0.98    inference(nnf_transformation,[],[f4])).
% 3.51/0.98  
% 3.51/0.98  fof(f33,plain,(
% 3.51/0.98    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.51/0.98    inference(cnf_transformation,[],[f24])).
% 3.51/0.98  
% 3.51/0.98  fof(f7,axiom,(
% 3.51/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v5_tops_1(X1,X0) <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1)))),
% 3.51/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/0.98  
% 3.51/0.98  fof(f18,plain,(
% 3.51/0.98    ! [X0] : (! [X1] : ((v5_tops_1(X1,X0) <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.51/0.98    inference(ennf_transformation,[],[f7])).
% 3.51/0.98  
% 3.51/0.98  fof(f25,plain,(
% 3.51/0.98    ! [X0] : (! [X1] : (((v5_tops_1(X1,X0) | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1) & (k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 | ~v5_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.51/0.98    inference(nnf_transformation,[],[f18])).
% 3.51/0.98  
% 3.51/0.98  fof(f36,plain,(
% 3.51/0.98    ( ! [X0,X1] : (k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 | ~v5_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.51/0.98    inference(cnf_transformation,[],[f25])).
% 3.51/0.98  
% 3.51/0.98  fof(f42,plain,(
% 3.51/0.98    v5_tops_1(sK1,sK0)),
% 3.51/0.98    inference(cnf_transformation,[],[f28])).
% 3.51/0.98  
% 3.51/0.98  fof(f32,plain,(
% 3.51/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.51/0.98    inference(cnf_transformation,[],[f24])).
% 3.51/0.98  
% 3.51/0.98  fof(f3,axiom,(
% 3.51/0.98    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 3.51/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/0.98  
% 3.51/0.98  fof(f14,plain,(
% 3.51/0.98    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.51/0.98    inference(ennf_transformation,[],[f3])).
% 3.51/0.98  
% 3.51/0.98  fof(f31,plain,(
% 3.51/0.98    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.51/0.98    inference(cnf_transformation,[],[f14])).
% 3.51/0.98  
% 3.51/0.98  fof(f5,axiom,(
% 3.51/0.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)))),
% 3.51/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/0.98  
% 3.51/0.98  fof(f15,plain,(
% 3.51/0.98    ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.51/0.98    inference(ennf_transformation,[],[f5])).
% 3.51/0.98  
% 3.51/0.98  fof(f16,plain,(
% 3.51/0.98    ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.51/0.98    inference(flattening,[],[f15])).
% 3.51/0.98  
% 3.51/0.98  fof(f34,plain,(
% 3.51/0.98    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.51/0.98    inference(cnf_transformation,[],[f16])).
% 3.51/0.98  
% 3.51/0.98  fof(f9,axiom,(
% 3.51/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)))),
% 3.51/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/0.98  
% 3.51/0.98  fof(f21,plain,(
% 3.51/0.98    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.51/0.98    inference(ennf_transformation,[],[f9])).
% 3.51/0.98  
% 3.51/0.98  fof(f39,plain,(
% 3.51/0.98    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.51/0.98    inference(cnf_transformation,[],[f21])).
% 3.51/0.98  
% 3.51/0.98  fof(f2,axiom,(
% 3.51/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 3.51/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.51/0.98  
% 3.51/0.98  fof(f13,plain,(
% 3.51/0.98    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.51/0.98    inference(ennf_transformation,[],[f2])).
% 3.51/0.98  
% 3.51/0.98  fof(f30,plain,(
% 3.51/0.98    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.51/0.98    inference(cnf_transformation,[],[f13])).
% 3.51/0.98  
% 3.51/0.98  fof(f43,plain,(
% 3.51/0.98    ~r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))),
% 3.51/0.98    inference(cnf_transformation,[],[f28])).
% 3.51/0.98  
% 3.51/0.98  cnf(c_13,negated_conjecture,
% 3.51/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.51/0.98      inference(cnf_transformation,[],[f41]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_608,negated_conjecture,
% 3.51/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.51/0.98      inference(subtyping,[status(esa)],[c_13]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_926,plain,
% 3.51/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.51/0.98      inference(predicate_to_equality,[status(thm)],[c_608]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_9,plain,
% 3.51/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.51/0.98      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.51/0.98      | ~ l1_pre_topc(X1) ),
% 3.51/0.98      inference(cnf_transformation,[],[f38]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_14,negated_conjecture,
% 3.51/0.98      ( l1_pre_topc(sK0) ),
% 3.51/0.98      inference(cnf_transformation,[],[f40]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_233,plain,
% 3.51/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.51/0.98      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.51/0.98      | sK0 != X1 ),
% 3.51/0.98      inference(resolution_lifted,[status(thm)],[c_9,c_14]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_234,plain,
% 3.51/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.51/0.98      | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.51/0.98      inference(unflattening,[status(thm)],[c_233]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_602,plain,
% 3.51/0.98      ( ~ m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.51/0.98      | m1_subset_1(k1_tops_1(sK0,X0_42),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.51/0.98      inference(subtyping,[status(esa)],[c_234]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_931,plain,
% 3.51/0.98      ( m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.51/0.98      | m1_subset_1(k1_tops_1(sK0,X0_42),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.51/0.98      inference(predicate_to_equality,[status(thm)],[c_602]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_6,plain,
% 3.51/0.98      ( r1_tarski(X0,k2_pre_topc(X1,X0))
% 3.51/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.51/0.98      | ~ l1_pre_topc(X1) ),
% 3.51/0.98      inference(cnf_transformation,[],[f35]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_245,plain,
% 3.51/0.98      ( r1_tarski(X0,k2_pre_topc(X1,X0))
% 3.51/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.51/0.98      | sK0 != X1 ),
% 3.51/0.98      inference(resolution_lifted,[status(thm)],[c_6,c_14]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_246,plain,
% 3.51/0.98      ( r1_tarski(X0,k2_pre_topc(sK0,X0))
% 3.51/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.51/0.98      inference(unflattening,[status(thm)],[c_245]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_601,plain,
% 3.51/0.98      ( r1_tarski(X0_42,k2_pre_topc(sK0,X0_42))
% 3.51/0.98      | ~ m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.51/0.98      inference(subtyping,[status(esa)],[c_246]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_932,plain,
% 3.51/0.98      ( r1_tarski(X0_42,k2_pre_topc(sK0,X0_42)) = iProver_top
% 3.51/0.98      | m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.51/0.98      inference(predicate_to_equality,[status(thm)],[c_601]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_1132,plain,
% 3.51/0.98      ( r1_tarski(k1_tops_1(sK0,X0_42),k2_pre_topc(sK0,k1_tops_1(sK0,X0_42))) = iProver_top
% 3.51/0.98      | m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.51/0.98      inference(superposition,[status(thm)],[c_931,c_932]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_0,plain,
% 3.51/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.51/0.98      | k4_xboole_0(X1,X0) = k3_subset_1(X1,X0) ),
% 3.51/0.98      inference(cnf_transformation,[],[f29]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_3,plain,
% 3.51/0.98      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.51/0.98      inference(cnf_transformation,[],[f33]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_119,plain,
% 3.51/0.98      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.51/0.98      inference(prop_impl,[status(thm)],[c_3]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_142,plain,
% 3.51/0.98      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X1,X0) = k3_subset_1(X1,X0) ),
% 3.51/0.98      inference(bin_hyper_res,[status(thm)],[c_0,c_119]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_607,plain,
% 3.51/0.98      ( ~ r1_tarski(X0_42,X1_42)
% 3.51/0.98      | k4_xboole_0(X1_42,X0_42) = k3_subset_1(X1_42,X0_42) ),
% 3.51/0.98      inference(subtyping,[status(esa)],[c_142]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_927,plain,
% 3.51/0.98      ( k4_xboole_0(X0_42,X1_42) = k3_subset_1(X0_42,X1_42)
% 3.51/0.98      | r1_tarski(X1_42,X0_42) != iProver_top ),
% 3.51/0.98      inference(predicate_to_equality,[status(thm)],[c_607]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_2086,plain,
% 3.51/0.98      ( k4_xboole_0(k2_pre_topc(sK0,k1_tops_1(sK0,X0_42)),k1_tops_1(sK0,X0_42)) = k3_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,X0_42)),k1_tops_1(sK0,X0_42))
% 3.51/0.98      | m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.51/0.98      inference(superposition,[status(thm)],[c_1132,c_927]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_10137,plain,
% 3.51/0.98      ( k4_xboole_0(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1)) = k3_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1)) ),
% 3.51/0.98      inference(superposition,[status(thm)],[c_926,c_2086]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_8,plain,
% 3.51/0.98      ( ~ v5_tops_1(X0,X1)
% 3.51/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.51/0.98      | ~ l1_pre_topc(X1)
% 3.51/0.98      | k2_pre_topc(X1,k1_tops_1(X1,X0)) = X0 ),
% 3.51/0.98      inference(cnf_transformation,[],[f36]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_12,negated_conjecture,
% 3.51/0.98      ( v5_tops_1(sK1,sK0) ),
% 3.51/0.98      inference(cnf_transformation,[],[f42]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_212,plain,
% 3.51/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.51/0.98      | ~ l1_pre_topc(X1)
% 3.51/0.98      | k2_pre_topc(X1,k1_tops_1(X1,X0)) = X0
% 3.51/0.98      | sK1 != X0
% 3.51/0.98      | sK0 != X1 ),
% 3.51/0.98      inference(resolution_lifted,[status(thm)],[c_8,c_12]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_213,plain,
% 3.51/0.98      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.51/0.98      | ~ l1_pre_topc(sK0)
% 3.51/0.98      | k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = sK1 ),
% 3.51/0.98      inference(unflattening,[status(thm)],[c_212]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_215,plain,
% 3.51/0.98      ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = sK1 ),
% 3.51/0.98      inference(global_propositional_subsumption,
% 3.51/0.98                [status(thm)],
% 3.51/0.98                [c_213,c_14,c_13]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_604,plain,
% 3.51/0.98      ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = sK1 ),
% 3.51/0.98      inference(subtyping,[status(esa)],[c_215]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_4,plain,
% 3.51/0.98      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.51/0.98      inference(cnf_transformation,[],[f32]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_610,plain,
% 3.51/0.98      ( r1_tarski(X0_42,X1_42)
% 3.51/0.98      | ~ m1_subset_1(X0_42,k1_zfmisc_1(X1_42)) ),
% 3.51/0.98      inference(subtyping,[status(esa)],[c_4]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_924,plain,
% 3.51/0.98      ( r1_tarski(X0_42,X1_42) = iProver_top
% 3.51/0.98      | m1_subset_1(X0_42,k1_zfmisc_1(X1_42)) != iProver_top ),
% 3.51/0.98      inference(predicate_to_equality,[status(thm)],[c_610]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_1272,plain,
% 3.51/0.98      ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
% 3.51/0.98      inference(superposition,[status(thm)],[c_926,c_924]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_2,plain,
% 3.51/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.51/0.98      | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 3.51/0.98      inference(cnf_transformation,[],[f31]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_144,plain,
% 3.51/0.98      ( ~ r1_tarski(X0,X1) | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 3.51/0.98      inference(bin_hyper_res,[status(thm)],[c_2,c_119]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_605,plain,
% 3.51/0.98      ( ~ r1_tarski(X0_42,X1_42)
% 3.51/0.98      | k7_subset_1(X1_42,X0_42,X2_42) = k4_xboole_0(X0_42,X2_42) ),
% 3.51/0.98      inference(subtyping,[status(esa)],[c_144]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_929,plain,
% 3.51/0.98      ( k7_subset_1(X0_42,X1_42,X2_42) = k4_xboole_0(X1_42,X2_42)
% 3.51/0.98      | r1_tarski(X1_42,X0_42) != iProver_top ),
% 3.51/0.98      inference(predicate_to_equality,[status(thm)],[c_605]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_1738,plain,
% 3.51/0.98      ( k7_subset_1(u1_struct_0(sK0),sK1,X0_42) = k4_xboole_0(sK1,X0_42) ),
% 3.51/0.98      inference(superposition,[status(thm)],[c_1272,c_929]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_5,plain,
% 3.51/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.51/0.98      | ~ l1_pre_topc(X1)
% 3.51/0.98      | k2_pre_topc(X1,k2_pre_topc(X1,X0)) = k2_pre_topc(X1,X0) ),
% 3.51/0.98      inference(cnf_transformation,[],[f34]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_257,plain,
% 3.51/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.51/0.98      | k2_pre_topc(X1,k2_pre_topc(X1,X0)) = k2_pre_topc(X1,X0)
% 3.51/0.98      | sK0 != X1 ),
% 3.51/0.98      inference(resolution_lifted,[status(thm)],[c_5,c_14]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_258,plain,
% 3.51/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.51/0.98      | k2_pre_topc(sK0,k2_pre_topc(sK0,X0)) = k2_pre_topc(sK0,X0) ),
% 3.51/0.98      inference(unflattening,[status(thm)],[c_257]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_600,plain,
% 3.51/0.98      ( ~ m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.51/0.98      | k2_pre_topc(sK0,k2_pre_topc(sK0,X0_42)) = k2_pre_topc(sK0,X0_42) ),
% 3.51/0.98      inference(subtyping,[status(esa)],[c_258]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_933,plain,
% 3.51/0.98      ( k2_pre_topc(sK0,k2_pre_topc(sK0,X0_42)) = k2_pre_topc(sK0,X0_42)
% 3.51/0.98      | m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.51/0.98      inference(predicate_to_equality,[status(thm)],[c_600]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_1185,plain,
% 3.51/0.98      ( k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,X0_42))) = k2_pre_topc(sK0,k1_tops_1(sK0,X0_42))
% 3.51/0.98      | m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.51/0.98      inference(superposition,[status(thm)],[c_931,c_933]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_2202,plain,
% 3.51/0.98      ( k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) ),
% 3.51/0.98      inference(superposition,[status(thm)],[c_926,c_1185]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_2206,plain,
% 3.51/0.98      ( k2_pre_topc(sK0,sK1) = sK1 ),
% 3.51/0.98      inference(light_normalisation,[status(thm)],[c_2202,c_604]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_10,plain,
% 3.51/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.51/0.98      | ~ l1_pre_topc(X1)
% 3.51/0.98      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
% 3.51/0.98      inference(cnf_transformation,[],[f39]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_221,plain,
% 3.51/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.51/0.98      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0)
% 3.51/0.98      | sK0 != X1 ),
% 3.51/0.98      inference(resolution_lifted,[status(thm)],[c_10,c_14]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_222,plain,
% 3.51/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.51/0.98      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
% 3.51/0.98      inference(unflattening,[status(thm)],[c_221]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_603,plain,
% 3.51/0.98      ( ~ m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.51/0.98      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0_42),k1_tops_1(sK0,X0_42)) = k2_tops_1(sK0,X0_42) ),
% 3.51/0.98      inference(subtyping,[status(esa)],[c_222]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_930,plain,
% 3.51/0.98      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0_42),k1_tops_1(sK0,X0_42)) = k2_tops_1(sK0,X0_42)
% 3.51/0.98      | m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.51/0.98      inference(predicate_to_equality,[status(thm)],[c_603]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_1405,plain,
% 3.51/0.98      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 3.51/0.98      inference(superposition,[status(thm)],[c_926,c_930]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_2347,plain,
% 3.51/0.98      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 3.51/0.98      inference(demodulation,[status(thm)],[c_2206,c_1405]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_2688,plain,
% 3.51/0.98      ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 3.51/0.98      inference(superposition,[status(thm)],[c_1738,c_2347]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_10141,plain,
% 3.51/0.98      ( k3_subset_1(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 3.51/0.98      inference(light_normalisation,[status(thm)],[c_10137,c_604,c_2688]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_1,plain,
% 3.51/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.51/0.98      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 3.51/0.98      inference(cnf_transformation,[],[f30]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_143,plain,
% 3.51/0.98      ( ~ r1_tarski(X0,X1)
% 3.51/0.98      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 3.51/0.98      inference(bin_hyper_res,[status(thm)],[c_1,c_119]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_606,plain,
% 3.51/0.98      ( ~ r1_tarski(X0_42,X1_42)
% 3.51/0.98      | m1_subset_1(k3_subset_1(X1_42,X0_42),k1_zfmisc_1(X1_42)) ),
% 3.51/0.98      inference(subtyping,[status(esa)],[c_143]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_928,plain,
% 3.51/0.98      ( r1_tarski(X0_42,X1_42) != iProver_top
% 3.51/0.98      | m1_subset_1(k3_subset_1(X1_42,X0_42),k1_zfmisc_1(X1_42)) = iProver_top ),
% 3.51/0.98      inference(predicate_to_equality,[status(thm)],[c_606]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_1394,plain,
% 3.51/0.98      ( r1_tarski(X0_42,X1_42) != iProver_top
% 3.51/0.98      | r1_tarski(k3_subset_1(X1_42,X0_42),X1_42) = iProver_top ),
% 3.51/0.98      inference(superposition,[status(thm)],[c_928,c_924]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_10495,plain,
% 3.51/0.98      ( r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top
% 3.51/0.98      | r1_tarski(k1_tops_1(sK0,sK1),sK1) != iProver_top ),
% 3.51/0.98      inference(superposition,[status(thm)],[c_10141,c_1394]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_611,plain,
% 3.51/0.98      ( ~ r1_tarski(X0_42,X1_42)
% 3.51/0.98      | m1_subset_1(X0_42,k1_zfmisc_1(X1_42)) ),
% 3.51/0.98      inference(subtyping,[status(esa)],[c_3]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_923,plain,
% 3.51/0.98      ( r1_tarski(X0_42,X1_42) != iProver_top
% 3.51/0.98      | m1_subset_1(X0_42,k1_zfmisc_1(X1_42)) = iProver_top ),
% 3.51/0.98      inference(predicate_to_equality,[status(thm)],[c_611]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_1268,plain,
% 3.51/0.98      ( r1_tarski(X0_42,k2_pre_topc(sK0,X0_42)) = iProver_top
% 3.51/0.98      | r1_tarski(X0_42,u1_struct_0(sK0)) != iProver_top ),
% 3.51/0.98      inference(superposition,[status(thm)],[c_923,c_932]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_1560,plain,
% 3.51/0.98      ( r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) != iProver_top
% 3.51/0.98      | r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
% 3.51/0.98      inference(superposition,[status(thm)],[c_604,c_1268]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_1029,plain,
% 3.51/0.98      ( r1_tarski(k1_tops_1(sK0,X0_42),u1_struct_0(sK0))
% 3.51/0.98      | ~ m1_subset_1(k1_tops_1(sK0,X0_42),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.51/0.98      inference(instantiation,[status(thm)],[c_610]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_1030,plain,
% 3.51/0.98      ( r1_tarski(k1_tops_1(sK0,X0_42),u1_struct_0(sK0)) = iProver_top
% 3.51/0.98      | m1_subset_1(k1_tops_1(sK0,X0_42),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.51/0.98      inference(predicate_to_equality,[status(thm)],[c_1029]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_1032,plain,
% 3.51/0.98      ( r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) = iProver_top
% 3.51/0.98      | m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.51/0.98      inference(instantiation,[status(thm)],[c_1030]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_11,negated_conjecture,
% 3.51/0.98      ( ~ r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
% 3.51/0.98      inference(cnf_transformation,[],[f43]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_609,negated_conjecture,
% 3.51/0.98      ( ~ r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
% 3.51/0.98      inference(subtyping,[status(esa)],[c_11]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_925,plain,
% 3.51/0.98      ( r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != iProver_top ),
% 3.51/0.98      inference(predicate_to_equality,[status(thm)],[c_609]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_934,plain,
% 3.51/0.98      ( r1_tarski(k2_tops_1(sK0,sK1),sK1) != iProver_top ),
% 3.51/0.98      inference(light_normalisation,[status(thm)],[c_925,c_604]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_653,plain,
% 3.51/0.98      ( m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.51/0.98      | m1_subset_1(k1_tops_1(sK0,X0_42),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.51/0.98      inference(predicate_to_equality,[status(thm)],[c_602]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_655,plain,
% 3.51/0.98      ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 3.51/0.98      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.51/0.98      inference(instantiation,[status(thm)],[c_653]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(c_16,plain,
% 3.51/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.51/0.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.51/0.98  
% 3.51/0.98  cnf(contradiction,plain,
% 3.51/0.98      ( $false ),
% 3.51/0.98      inference(minisat,
% 3.51/0.98                [status(thm)],
% 3.51/0.98                [c_10495,c_1560,c_1032,c_934,c_655,c_16]) ).
% 3.51/0.98  
% 3.51/0.98  
% 3.51/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.51/0.98  
% 3.51/0.98  ------                               Statistics
% 3.51/0.98  
% 3.51/0.98  ------ General
% 3.51/0.98  
% 3.51/0.98  abstr_ref_over_cycles:                  0
% 3.51/0.98  abstr_ref_under_cycles:                 0
% 3.51/0.98  gc_basic_clause_elim:                   0
% 3.51/0.98  forced_gc_time:                         0
% 3.51/0.98  parsing_time:                           0.008
% 3.51/0.98  unif_index_cands_time:                  0.
% 3.51/0.98  unif_index_add_time:                    0.
% 3.51/0.98  orderings_time:                         0.
% 3.51/0.98  out_proof_time:                         0.01
% 3.51/0.98  total_time:                             0.303
% 3.51/0.98  num_of_symbols:                         48
% 3.51/0.98  num_of_terms:                           5736
% 3.51/0.98  
% 3.51/0.98  ------ Preprocessing
% 3.51/0.98  
% 3.51/0.98  num_of_splits:                          0
% 3.51/0.98  num_of_split_atoms:                     0
% 3.51/0.98  num_of_reused_defs:                     0
% 3.51/0.98  num_eq_ax_congr_red:                    16
% 3.51/0.98  num_of_sem_filtered_clauses:            1
% 3.51/0.98  num_of_subtypes:                        3
% 3.51/0.98  monotx_restored_types:                  0
% 3.51/0.98  sat_num_of_epr_types:                   0
% 3.51/0.98  sat_num_of_non_cyclic_types:            0
% 3.51/0.98  sat_guarded_non_collapsed_types:        0
% 3.51/0.98  num_pure_diseq_elim:                    0
% 3.51/0.98  simp_replaced_by:                       0
% 3.51/0.98  res_preprocessed:                       72
% 3.51/0.98  prep_upred:                             0
% 3.51/0.98  prep_unflattend:                        28
% 3.51/0.98  smt_new_axioms:                         0
% 3.51/0.98  pred_elim_cands:                        2
% 3.51/0.98  pred_elim:                              2
% 3.51/0.98  pred_elim_cl:                           3
% 3.51/0.98  pred_elim_cycles:                       4
% 3.51/0.98  merged_defs:                            8
% 3.51/0.98  merged_defs_ncl:                        0
% 3.51/0.98  bin_hyper_res:                          11
% 3.51/0.98  prep_cycles:                            4
% 3.51/0.98  pred_elim_time:                         0.004
% 3.51/0.98  splitting_time:                         0.
% 3.51/0.98  sem_filter_time:                        0.
% 3.51/0.98  monotx_time:                            0.
% 3.51/0.98  subtype_inf_time:                       0.
% 3.51/0.98  
% 3.51/0.98  ------ Problem properties
% 3.51/0.98  
% 3.51/0.98  clauses:                                12
% 3.51/0.98  conjectures:                            2
% 3.51/0.98  epr:                                    0
% 3.51/0.98  horn:                                   12
% 3.51/0.98  ground:                                 3
% 3.51/0.98  unary:                                  3
% 3.51/0.98  binary:                                 9
% 3.51/0.98  lits:                                   21
% 3.51/0.98  lits_eq:                                5
% 3.51/0.98  fd_pure:                                0
% 3.51/0.98  fd_pseudo:                              0
% 3.51/0.98  fd_cond:                                0
% 3.51/0.98  fd_pseudo_cond:                         0
% 3.51/0.98  ac_symbols:                             0
% 3.51/0.98  
% 3.51/0.98  ------ Propositional Solver
% 3.51/0.98  
% 3.51/0.98  prop_solver_calls:                      32
% 3.51/0.98  prop_fast_solver_calls:                 575
% 3.51/0.98  smt_solver_calls:                       0
% 3.51/0.98  smt_fast_solver_calls:                  0
% 3.51/0.98  prop_num_of_clauses:                    3424
% 3.51/0.98  prop_preprocess_simplified:             8077
% 3.51/0.98  prop_fo_subsumed:                       3
% 3.51/0.98  prop_solver_time:                       0.
% 3.51/0.98  smt_solver_time:                        0.
% 3.51/0.98  smt_fast_solver_time:                   0.
% 3.51/0.98  prop_fast_solver_time:                  0.
% 3.51/0.98  prop_unsat_core_time:                   0.
% 3.51/0.98  
% 3.51/0.98  ------ QBF
% 3.51/0.98  
% 3.51/0.98  qbf_q_res:                              0
% 3.51/0.98  qbf_num_tautologies:                    0
% 3.51/0.98  qbf_prep_cycles:                        0
% 3.51/0.98  
% 3.51/0.98  ------ BMC1
% 3.51/0.98  
% 3.51/0.98  bmc1_current_bound:                     -1
% 3.51/0.98  bmc1_last_solved_bound:                 -1
% 3.51/0.98  bmc1_unsat_core_size:                   -1
% 3.51/0.98  bmc1_unsat_core_parents_size:           -1
% 3.51/0.98  bmc1_merge_next_fun:                    0
% 3.51/0.98  bmc1_unsat_core_clauses_time:           0.
% 3.51/0.98  
% 3.51/0.98  ------ Instantiation
% 3.51/0.98  
% 3.51/0.98  inst_num_of_clauses:                    1182
% 3.51/0.98  inst_num_in_passive:                    2
% 3.51/0.98  inst_num_in_active:                     667
% 3.51/0.98  inst_num_in_unprocessed:                514
% 3.51/0.98  inst_num_of_loops:                      710
% 3.51/0.98  inst_num_of_learning_restarts:          0
% 3.51/0.98  inst_num_moves_active_passive:          37
% 3.51/0.98  inst_lit_activity:                      0
% 3.51/0.98  inst_lit_activity_moves:                0
% 3.51/0.98  inst_num_tautologies:                   0
% 3.51/0.98  inst_num_prop_implied:                  0
% 3.51/0.98  inst_num_existing_simplified:           0
% 3.51/0.98  inst_num_eq_res_simplified:             0
% 3.51/0.98  inst_num_child_elim:                    0
% 3.51/0.98  inst_num_of_dismatching_blockings:      1069
% 3.51/0.98  inst_num_of_non_proper_insts:           2167
% 3.51/0.98  inst_num_of_duplicates:                 0
% 3.51/0.98  inst_inst_num_from_inst_to_res:         0
% 3.51/0.98  inst_dismatching_checking_time:         0.
% 3.51/0.98  
% 3.51/0.98  ------ Resolution
% 3.51/0.98  
% 3.51/0.98  res_num_of_clauses:                     0
% 3.51/0.98  res_num_in_passive:                     0
% 3.51/0.98  res_num_in_active:                      0
% 3.51/0.98  res_num_of_loops:                       76
% 3.51/0.98  res_forward_subset_subsumed:            18
% 3.51/0.98  res_backward_subset_subsumed:           4
% 3.51/0.98  res_forward_subsumed:                   0
% 3.51/0.98  res_backward_subsumed:                  0
% 3.51/0.98  res_forward_subsumption_resolution:     0
% 3.51/0.98  res_backward_subsumption_resolution:    0
% 3.51/0.98  res_clause_to_clause_subsumption:       1094
% 3.51/0.98  res_orphan_elimination:                 0
% 3.51/0.98  res_tautology_del:                      192
% 3.51/0.98  res_num_eq_res_simplified:              0
% 3.51/0.98  res_num_sel_changes:                    0
% 3.51/0.98  res_moves_from_active_to_pass:          0
% 3.51/0.98  
% 3.51/0.98  ------ Superposition
% 3.51/0.98  
% 3.51/0.98  sup_time_total:                         0.
% 3.51/0.98  sup_time_generating:                    0.
% 3.51/0.98  sup_time_sim_full:                      0.
% 3.51/0.98  sup_time_sim_immed:                     0.
% 3.51/0.98  
% 3.51/0.98  sup_num_of_clauses:                     224
% 3.51/0.98  sup_num_in_active:                      133
% 3.51/0.98  sup_num_in_passive:                     91
% 3.51/0.98  sup_num_of_loops:                       141
% 3.51/0.98  sup_fw_superposition:                   261
% 3.51/0.98  sup_bw_superposition:                   50
% 3.51/0.98  sup_immediate_simplified:               6
% 3.51/0.98  sup_given_eliminated:                   0
% 3.51/0.98  comparisons_done:                       0
% 3.51/0.98  comparisons_avoided:                    0
% 3.51/0.98  
% 3.51/0.98  ------ Simplifications
% 3.51/0.98  
% 3.51/0.98  
% 3.51/0.98  sim_fw_subset_subsumed:                 2
% 3.51/0.98  sim_bw_subset_subsumed:                 0
% 3.51/0.98  sim_fw_subsumed:                        0
% 3.51/0.98  sim_bw_subsumed:                        0
% 3.51/0.98  sim_fw_subsumption_res:                 0
% 3.51/0.98  sim_bw_subsumption_res:                 0
% 3.51/0.98  sim_tautology_del:                      1
% 3.51/0.98  sim_eq_tautology_del:                   3
% 3.51/0.98  sim_eq_res_simp:                        0
% 3.51/0.98  sim_fw_demodulated:                     0
% 3.51/0.98  sim_bw_demodulated:                     9
% 3.51/0.98  sim_light_normalised:                   7
% 3.51/0.98  sim_joinable_taut:                      0
% 3.51/0.98  sim_joinable_simp:                      0
% 3.51/0.98  sim_ac_normalised:                      0
% 3.51/0.98  sim_smt_subsumption:                    0
% 3.51/0.98  
%------------------------------------------------------------------------------
