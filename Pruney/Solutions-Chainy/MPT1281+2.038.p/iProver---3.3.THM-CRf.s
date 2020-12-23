%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:15:46 EST 2020

% Result     : Theorem 3.56s
% Output     : CNFRefutation 3.56s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 343 expanded)
%              Number of clauses        :   66 ( 120 expanded)
%              Number of leaves         :   12 (  79 expanded)
%              Depth                    :   17
%              Number of atoms          :  261 (1137 expanded)
%              Number of equality atoms :   95 ( 146 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v5_tops_1(X1,X0)
          <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_tops_1(X1,X0)
          <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_tops_1(X1,X0)
              | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1 )
            & ( k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1
              | ~ v5_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1
      | ~ v5_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f40,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f42,plain,(
    v5_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

cnf(c_187,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_587,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_187])).

cnf(c_4,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_196,plain,
    ( r1_tarski(X0_42,X1_42)
    | ~ m1_subset_1(X0_42,k1_zfmisc_1(X1_42)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_578,plain,
    ( r1_tarski(X0_42,X1_42) = iProver_top
    | m1_subset_1(X0_42,k1_zfmisc_1(X1_42)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_196])).

cnf(c_839,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_587,c_578])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_104,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_3])).

cnf(c_131,plain,
    ( ~ r1_tarski(X0,X1)
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_2,c_104])).

cnf(c_183,plain,
    ( ~ r1_tarski(X0_42,X1_42)
    | k7_subset_1(X1_42,X0_42,X2_42) = k4_xboole_0(X0_42,X2_42) ),
    inference(subtyping,[status(esa)],[c_131])).

cnf(c_591,plain,
    ( k7_subset_1(X0_42,X1_42,X2_42) = k4_xboole_0(X1_42,X2_42)
    | r1_tarski(X1_42,X0_42) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_183])).

cnf(c_1777,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0_42) = k4_xboole_0(sK1,X0_42) ),
    inference(superposition,[status(thm)],[c_839,c_591])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_192,plain,
    ( ~ m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(X0_44)))
    | m1_subset_1(k1_tops_1(X0_44,X0_42),k1_zfmisc_1(u1_struct_0(X0_44)))
    | ~ l1_pre_topc(X0_44) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_582,plain,
    ( m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(X0_44))) != iProver_top
    | m1_subset_1(k1_tops_1(X0_44,X0_42),k1_zfmisc_1(u1_struct_0(X0_44))) = iProver_top
    | l1_pre_topc(X0_44) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_192])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k2_pre_topc(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_195,plain,
    ( ~ m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(X0_44)))
    | ~ l1_pre_topc(X0_44)
    | k2_pre_topc(X0_44,k2_pre_topc(X0_44,X0_42)) = k2_pre_topc(X0_44,X0_42) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_579,plain,
    ( k2_pre_topc(X0_44,k2_pre_topc(X0_44,X0_42)) = k2_pre_topc(X0_44,X0_42)
    | m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(X0_44))) != iProver_top
    | l1_pre_topc(X0_44) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_195])).

cnf(c_1176,plain,
    ( k2_pre_topc(X0_44,k2_pre_topc(X0_44,k1_tops_1(X0_44,X0_42))) = k2_pre_topc(X0_44,k1_tops_1(X0_44,X0_42))
    | m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(X0_44))) != iProver_top
    | l1_pre_topc(X0_44) != iProver_top ),
    inference(superposition,[status(thm)],[c_582,c_579])).

cnf(c_3263,plain,
    ( k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = k2_pre_topc(sK0,k1_tops_1(sK0,sK1))
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_587,c_1176])).

cnf(c_7,plain,
    ( ~ v5_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k1_tops_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_193,plain,
    ( ~ v5_tops_1(X0_42,X0_44)
    | ~ m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(X0_44)))
    | ~ l1_pre_topc(X0_44)
    | k2_pre_topc(X0_44,k1_tops_1(X0_44,X0_42)) = X0_42 ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_581,plain,
    ( k2_pre_topc(X0_44,k1_tops_1(X0_44,X0_42)) = X0_42
    | v5_tops_1(X0_42,X0_44) != iProver_top
    | m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(X0_44))) != iProver_top
    | l1_pre_topc(X0_44) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_193])).

cnf(c_1798,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = sK1
    | v5_tops_1(sK1,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_587,c_581])).

cnf(c_14,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_12,negated_conjecture,
    ( v5_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_232,plain,
    ( ~ v5_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = sK1 ),
    inference(instantiation,[status(thm)],[c_193])).

cnf(c_1950,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1798,c_14,c_13,c_12,c_232])).

cnf(c_3287,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3263,c_1950])).

cnf(c_15,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3301,plain,
    ( k2_pre_topc(sK0,sK1) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3287,c_15])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_191,plain,
    ( ~ m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(X0_44)))
    | ~ l1_pre_topc(X0_44)
    | k7_subset_1(u1_struct_0(X0_44),k2_pre_topc(X0_44,X0_42),k1_tops_1(X0_44,X0_42)) = k2_tops_1(X0_44,X0_42) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_583,plain,
    ( k7_subset_1(u1_struct_0(X0_44),k2_pre_topc(X0_44,X0_42),k1_tops_1(X0_44,X0_42)) = k2_tops_1(X0_44,X0_42)
    | m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(X0_44))) != iProver_top
    | l1_pre_topc(X0_44) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_191])).

cnf(c_1209,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_587,c_583])).

cnf(c_238,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_191])).

cnf(c_1453,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1209,c_14,c_13,c_238])).

cnf(c_3304,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_3301,c_1453])).

cnf(c_3503,plain,
    ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_1777,c_3304])).

cnf(c_10,plain,
    ( r1_tarski(k1_tops_1(X0,X1),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_190,plain,
    ( r1_tarski(k1_tops_1(X0_44,X0_42),X0_42)
    | ~ m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(X0_44)))
    | ~ l1_pre_topc(X0_44) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_584,plain,
    ( r1_tarski(k1_tops_1(X0_44,X0_42),X0_42) = iProver_top
    | m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(X0_44))) != iProver_top
    | l1_pre_topc(X0_44) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_190])).

cnf(c_1064,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_587,c_584])).

cnf(c_16,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_240,plain,
    ( r1_tarski(k1_tops_1(X0_44,X0_42),X0_42) = iProver_top
    | m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(X0_44))) != iProver_top
    | l1_pre_topc(X0_44) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_190])).

cnf(c_242,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_240])).

cnf(c_1356,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1064,c_15,c_16,c_242])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k4_xboole_0(X1,X0) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_129,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X1,X0) = k3_subset_1(X1,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_0,c_104])).

cnf(c_185,plain,
    ( ~ r1_tarski(X0_42,X1_42)
    | k4_xboole_0(X1_42,X0_42) = k3_subset_1(X1_42,X0_42) ),
    inference(subtyping,[status(esa)],[c_129])).

cnf(c_589,plain,
    ( k4_xboole_0(X0_42,X1_42) = k3_subset_1(X0_42,X1_42)
    | r1_tarski(X1_42,X0_42) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_185])).

cnf(c_1361,plain,
    ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k3_subset_1(sK1,k1_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_1356,c_589])).

cnf(c_3506,plain,
    ( k3_subset_1(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_3503,c_1361])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_130,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(bin_hyper_res,[status(thm)],[c_1,c_104])).

cnf(c_184,plain,
    ( ~ r1_tarski(X0_42,X1_42)
    | m1_subset_1(k3_subset_1(X1_42,X0_42),k1_zfmisc_1(X1_42)) ),
    inference(subtyping,[status(esa)],[c_130])).

cnf(c_590,plain,
    ( r1_tarski(X0_42,X1_42) != iProver_top
    | m1_subset_1(k3_subset_1(X1_42,X0_42),k1_zfmisc_1(X1_42)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_184])).

cnf(c_1597,plain,
    ( r1_tarski(X0_42,X1_42) != iProver_top
    | r1_tarski(k3_subset_1(X1_42,X0_42),X1_42) = iProver_top ),
    inference(superposition,[status(thm)],[c_590,c_578])).

cnf(c_3629,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3506,c_1597])).

cnf(c_11,negated_conjecture,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_189,negated_conjecture,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_585,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_189])).

cnf(c_1953,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1950,c_585])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3629,c_1953,c_242,c_16,c_15])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:05:31 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.56/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.56/0.99  
% 3.56/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.56/0.99  
% 3.56/0.99  ------  iProver source info
% 3.56/0.99  
% 3.56/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.56/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.56/0.99  git: non_committed_changes: false
% 3.56/0.99  git: last_make_outside_of_git: false
% 3.56/0.99  
% 3.56/0.99  ------ 
% 3.56/0.99  ------ Parsing...
% 3.56/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.56/0.99  
% 3.56/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.56/0.99  
% 3.56/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.56/0.99  
% 3.56/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.56/0.99  ------ Proving...
% 3.56/0.99  ------ Problem Properties 
% 3.56/0.99  
% 3.56/0.99  
% 3.56/0.99  clauses                                 15
% 3.56/0.99  conjectures                             4
% 3.56/0.99  EPR                                     2
% 3.56/0.99  Horn                                    15
% 3.56/0.99  unary                                   4
% 3.56/0.99  binary                                  5
% 3.56/0.99  lits                                    34
% 3.56/0.99  lits eq                                 6
% 3.56/0.99  fd_pure                                 0
% 3.56/0.99  fd_pseudo                               0
% 3.56/0.99  fd_cond                                 0
% 3.56/0.99  fd_pseudo_cond                          0
% 3.56/0.99  AC symbols                              0
% 3.56/0.99  
% 3.56/0.99  ------ Input Options Time Limit: Unbounded
% 3.56/0.99  
% 3.56/0.99  
% 3.56/0.99  ------ 
% 3.56/0.99  Current options:
% 3.56/0.99  ------ 
% 3.56/0.99  
% 3.56/0.99  
% 3.56/0.99  
% 3.56/0.99  
% 3.56/0.99  ------ Proving...
% 3.56/0.99  
% 3.56/0.99  
% 3.56/0.99  % SZS status Theorem for theBenchmark.p
% 3.56/0.99  
% 3.56/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.56/0.99  
% 3.56/0.99  fof(f10,conjecture,(
% 3.56/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v5_tops_1(X1,X0) => r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))))))),
% 3.56/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.56/0.99  
% 3.56/0.99  fof(f11,negated_conjecture,(
% 3.56/0.99    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v5_tops_1(X1,X0) => r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))))))),
% 3.56/0.99    inference(negated_conjecture,[],[f10])).
% 3.56/0.99  
% 3.56/0.99  fof(f22,plain,(
% 3.56/0.99    ? [X0] : (? [X1] : ((~r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))) & v5_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.56/0.99    inference(ennf_transformation,[],[f11])).
% 3.56/0.99  
% 3.56/0.99  fof(f23,plain,(
% 3.56/0.99    ? [X0] : (? [X1] : (~r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))) & v5_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.56/0.99    inference(flattening,[],[f22])).
% 3.56/0.99  
% 3.56/0.99  fof(f27,plain,(
% 3.56/0.99    ( ! [X0] : (? [X1] : (~r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))) & v5_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~r1_tarski(k2_tops_1(X0,sK1),k2_pre_topc(X0,k1_tops_1(X0,sK1))) & v5_tops_1(sK1,X0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.56/0.99    introduced(choice_axiom,[])).
% 3.56/0.99  
% 3.56/0.99  fof(f26,plain,(
% 3.56/0.99    ? [X0] : (? [X1] : (~r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))) & v5_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (~r1_tarski(k2_tops_1(sK0,X1),k2_pre_topc(sK0,k1_tops_1(sK0,X1))) & v5_tops_1(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 3.56/0.99    introduced(choice_axiom,[])).
% 3.56/0.99  
% 3.56/0.99  fof(f28,plain,(
% 3.56/0.99    (~r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) & v5_tops_1(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 3.56/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f27,f26])).
% 3.56/0.99  
% 3.56/0.99  fof(f41,plain,(
% 3.56/0.99    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.56/0.99    inference(cnf_transformation,[],[f28])).
% 3.56/0.99  
% 3.56/0.99  fof(f4,axiom,(
% 3.56/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.56/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.56/0.99  
% 3.56/0.99  fof(f24,plain,(
% 3.56/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.56/0.99    inference(nnf_transformation,[],[f4])).
% 3.56/0.99  
% 3.56/0.99  fof(f32,plain,(
% 3.56/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.56/0.99    inference(cnf_transformation,[],[f24])).
% 3.56/0.99  
% 3.56/0.99  fof(f3,axiom,(
% 3.56/0.99    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 3.56/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.56/0.99  
% 3.56/0.99  fof(f14,plain,(
% 3.56/0.99    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.56/0.99    inference(ennf_transformation,[],[f3])).
% 3.56/0.99  
% 3.56/0.99  fof(f31,plain,(
% 3.56/0.99    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.56/0.99    inference(cnf_transformation,[],[f14])).
% 3.56/0.99  
% 3.56/0.99  fof(f33,plain,(
% 3.56/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.56/0.99    inference(cnf_transformation,[],[f24])).
% 3.56/0.99  
% 3.56/0.99  fof(f7,axiom,(
% 3.56/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.56/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.56/0.99  
% 3.56/0.99  fof(f18,plain,(
% 3.56/0.99    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.56/0.99    inference(ennf_transformation,[],[f7])).
% 3.56/0.99  
% 3.56/0.99  fof(f19,plain,(
% 3.56/0.99    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.56/0.99    inference(flattening,[],[f18])).
% 3.56/0.99  
% 3.56/0.99  fof(f37,plain,(
% 3.56/0.99    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.56/0.99    inference(cnf_transformation,[],[f19])).
% 3.56/0.99  
% 3.56/0.99  fof(f5,axiom,(
% 3.56/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)))),
% 3.56/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.56/0.99  
% 3.56/0.99  fof(f15,plain,(
% 3.56/0.99    ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.56/0.99    inference(ennf_transformation,[],[f5])).
% 3.56/0.99  
% 3.56/0.99  fof(f16,plain,(
% 3.56/0.99    ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.56/0.99    inference(flattening,[],[f15])).
% 3.56/0.99  
% 3.56/0.99  fof(f34,plain,(
% 3.56/0.99    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.56/0.99    inference(cnf_transformation,[],[f16])).
% 3.56/0.99  
% 3.56/0.99  fof(f6,axiom,(
% 3.56/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v5_tops_1(X1,X0) <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1)))),
% 3.56/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.56/0.99  
% 3.56/0.99  fof(f17,plain,(
% 3.56/0.99    ! [X0] : (! [X1] : ((v5_tops_1(X1,X0) <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.56/0.99    inference(ennf_transformation,[],[f6])).
% 3.56/0.99  
% 3.56/0.99  fof(f25,plain,(
% 3.56/0.99    ! [X0] : (! [X1] : (((v5_tops_1(X1,X0) | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1) & (k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 | ~v5_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.56/0.99    inference(nnf_transformation,[],[f17])).
% 3.56/0.99  
% 3.56/0.99  fof(f35,plain,(
% 3.56/0.99    ( ! [X0,X1] : (k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 | ~v5_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.56/0.99    inference(cnf_transformation,[],[f25])).
% 3.56/0.99  
% 3.56/0.99  fof(f40,plain,(
% 3.56/0.99    l1_pre_topc(sK0)),
% 3.56/0.99    inference(cnf_transformation,[],[f28])).
% 3.56/0.99  
% 3.56/0.99  fof(f42,plain,(
% 3.56/0.99    v5_tops_1(sK1,sK0)),
% 3.56/0.99    inference(cnf_transformation,[],[f28])).
% 3.56/0.99  
% 3.56/0.99  fof(f8,axiom,(
% 3.56/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)))),
% 3.56/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.56/0.99  
% 3.56/0.99  fof(f20,plain,(
% 3.56/0.99    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.56/0.99    inference(ennf_transformation,[],[f8])).
% 3.56/0.99  
% 3.56/0.99  fof(f38,plain,(
% 3.56/0.99    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.56/0.99    inference(cnf_transformation,[],[f20])).
% 3.56/0.99  
% 3.56/0.99  fof(f9,axiom,(
% 3.56/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 3.56/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.56/0.99  
% 3.56/0.99  fof(f21,plain,(
% 3.56/0.99    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.56/0.99    inference(ennf_transformation,[],[f9])).
% 3.56/0.99  
% 3.56/0.99  fof(f39,plain,(
% 3.56/0.99    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.56/0.99    inference(cnf_transformation,[],[f21])).
% 3.56/0.99  
% 3.56/0.99  fof(f1,axiom,(
% 3.56/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1))),
% 3.56/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.56/0.99  
% 3.56/0.99  fof(f12,plain,(
% 3.56/0.99    ! [X0,X1] : (k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.56/0.99    inference(ennf_transformation,[],[f1])).
% 3.56/0.99  
% 3.56/0.99  fof(f29,plain,(
% 3.56/0.99    ( ! [X0,X1] : (k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.56/0.99    inference(cnf_transformation,[],[f12])).
% 3.56/0.99  
% 3.56/0.99  fof(f2,axiom,(
% 3.56/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 3.56/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.56/0.99  
% 3.56/0.99  fof(f13,plain,(
% 3.56/0.99    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.56/0.99    inference(ennf_transformation,[],[f2])).
% 3.56/0.99  
% 3.56/0.99  fof(f30,plain,(
% 3.56/0.99    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.56/0.99    inference(cnf_transformation,[],[f13])).
% 3.56/0.99  
% 3.56/0.99  fof(f43,plain,(
% 3.56/0.99    ~r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))),
% 3.56/0.99    inference(cnf_transformation,[],[f28])).
% 3.56/0.99  
% 3.56/0.99  cnf(c_13,negated_conjecture,
% 3.56/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.56/0.99      inference(cnf_transformation,[],[f41]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_187,negated_conjecture,
% 3.56/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.56/0.99      inference(subtyping,[status(esa)],[c_13]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_587,plain,
% 3.56/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.56/0.99      inference(predicate_to_equality,[status(thm)],[c_187]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_4,plain,
% 3.56/0.99      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.56/0.99      inference(cnf_transformation,[],[f32]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_196,plain,
% 3.56/0.99      ( r1_tarski(X0_42,X1_42)
% 3.56/0.99      | ~ m1_subset_1(X0_42,k1_zfmisc_1(X1_42)) ),
% 3.56/0.99      inference(subtyping,[status(esa)],[c_4]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_578,plain,
% 3.56/0.99      ( r1_tarski(X0_42,X1_42) = iProver_top
% 3.56/0.99      | m1_subset_1(X0_42,k1_zfmisc_1(X1_42)) != iProver_top ),
% 3.56/0.99      inference(predicate_to_equality,[status(thm)],[c_196]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_839,plain,
% 3.56/0.99      ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
% 3.56/0.99      inference(superposition,[status(thm)],[c_587,c_578]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_2,plain,
% 3.56/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.56/0.99      | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 3.56/0.99      inference(cnf_transformation,[],[f31]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_3,plain,
% 3.56/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.56/0.99      inference(cnf_transformation,[],[f33]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_104,plain,
% 3.56/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.56/0.99      inference(prop_impl,[status(thm)],[c_3]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_131,plain,
% 3.56/0.99      ( ~ r1_tarski(X0,X1) | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 3.56/0.99      inference(bin_hyper_res,[status(thm)],[c_2,c_104]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_183,plain,
% 3.56/0.99      ( ~ r1_tarski(X0_42,X1_42)
% 3.56/0.99      | k7_subset_1(X1_42,X0_42,X2_42) = k4_xboole_0(X0_42,X2_42) ),
% 3.56/0.99      inference(subtyping,[status(esa)],[c_131]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_591,plain,
% 3.56/0.99      ( k7_subset_1(X0_42,X1_42,X2_42) = k4_xboole_0(X1_42,X2_42)
% 3.56/0.99      | r1_tarski(X1_42,X0_42) != iProver_top ),
% 3.56/0.99      inference(predicate_to_equality,[status(thm)],[c_183]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_1777,plain,
% 3.56/0.99      ( k7_subset_1(u1_struct_0(sK0),sK1,X0_42) = k4_xboole_0(sK1,X0_42) ),
% 3.56/0.99      inference(superposition,[status(thm)],[c_839,c_591]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_8,plain,
% 3.56/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.56/0.99      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.56/0.99      | ~ l1_pre_topc(X1) ),
% 3.56/0.99      inference(cnf_transformation,[],[f37]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_192,plain,
% 3.56/0.99      ( ~ m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(X0_44)))
% 3.56/0.99      | m1_subset_1(k1_tops_1(X0_44,X0_42),k1_zfmisc_1(u1_struct_0(X0_44)))
% 3.56/0.99      | ~ l1_pre_topc(X0_44) ),
% 3.56/0.99      inference(subtyping,[status(esa)],[c_8]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_582,plain,
% 3.56/0.99      ( m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(X0_44))) != iProver_top
% 3.56/0.99      | m1_subset_1(k1_tops_1(X0_44,X0_42),k1_zfmisc_1(u1_struct_0(X0_44))) = iProver_top
% 3.56/0.99      | l1_pre_topc(X0_44) != iProver_top ),
% 3.56/0.99      inference(predicate_to_equality,[status(thm)],[c_192]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_5,plain,
% 3.56/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.56/0.99      | ~ l1_pre_topc(X1)
% 3.56/0.99      | k2_pre_topc(X1,k2_pre_topc(X1,X0)) = k2_pre_topc(X1,X0) ),
% 3.56/0.99      inference(cnf_transformation,[],[f34]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_195,plain,
% 3.56/0.99      ( ~ m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(X0_44)))
% 3.56/0.99      | ~ l1_pre_topc(X0_44)
% 3.56/0.99      | k2_pre_topc(X0_44,k2_pre_topc(X0_44,X0_42)) = k2_pre_topc(X0_44,X0_42) ),
% 3.56/0.99      inference(subtyping,[status(esa)],[c_5]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_579,plain,
% 3.56/0.99      ( k2_pre_topc(X0_44,k2_pre_topc(X0_44,X0_42)) = k2_pre_topc(X0_44,X0_42)
% 3.56/0.99      | m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(X0_44))) != iProver_top
% 3.56/0.99      | l1_pre_topc(X0_44) != iProver_top ),
% 3.56/0.99      inference(predicate_to_equality,[status(thm)],[c_195]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_1176,plain,
% 3.56/0.99      ( k2_pre_topc(X0_44,k2_pre_topc(X0_44,k1_tops_1(X0_44,X0_42))) = k2_pre_topc(X0_44,k1_tops_1(X0_44,X0_42))
% 3.56/0.99      | m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(X0_44))) != iProver_top
% 3.56/0.99      | l1_pre_topc(X0_44) != iProver_top ),
% 3.56/0.99      inference(superposition,[status(thm)],[c_582,c_579]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_3263,plain,
% 3.56/0.99      ( k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = k2_pre_topc(sK0,k1_tops_1(sK0,sK1))
% 3.56/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.56/0.99      inference(superposition,[status(thm)],[c_587,c_1176]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_7,plain,
% 3.56/0.99      ( ~ v5_tops_1(X0,X1)
% 3.56/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.56/0.99      | ~ l1_pre_topc(X1)
% 3.56/0.99      | k2_pre_topc(X1,k1_tops_1(X1,X0)) = X0 ),
% 3.56/0.99      inference(cnf_transformation,[],[f35]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_193,plain,
% 3.56/0.99      ( ~ v5_tops_1(X0_42,X0_44)
% 3.56/0.99      | ~ m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(X0_44)))
% 3.56/0.99      | ~ l1_pre_topc(X0_44)
% 3.56/0.99      | k2_pre_topc(X0_44,k1_tops_1(X0_44,X0_42)) = X0_42 ),
% 3.56/0.99      inference(subtyping,[status(esa)],[c_7]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_581,plain,
% 3.56/0.99      ( k2_pre_topc(X0_44,k1_tops_1(X0_44,X0_42)) = X0_42
% 3.56/0.99      | v5_tops_1(X0_42,X0_44) != iProver_top
% 3.56/0.99      | m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(X0_44))) != iProver_top
% 3.56/0.99      | l1_pre_topc(X0_44) != iProver_top ),
% 3.56/0.99      inference(predicate_to_equality,[status(thm)],[c_193]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_1798,plain,
% 3.56/0.99      ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = sK1
% 3.56/0.99      | v5_tops_1(sK1,sK0) != iProver_top
% 3.56/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.56/0.99      inference(superposition,[status(thm)],[c_587,c_581]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_14,negated_conjecture,
% 3.56/0.99      ( l1_pre_topc(sK0) ),
% 3.56/0.99      inference(cnf_transformation,[],[f40]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_12,negated_conjecture,
% 3.56/0.99      ( v5_tops_1(sK1,sK0) ),
% 3.56/0.99      inference(cnf_transformation,[],[f42]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_232,plain,
% 3.56/0.99      ( ~ v5_tops_1(sK1,sK0)
% 3.56/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.56/0.99      | ~ l1_pre_topc(sK0)
% 3.56/0.99      | k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = sK1 ),
% 3.56/0.99      inference(instantiation,[status(thm)],[c_193]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_1950,plain,
% 3.56/0.99      ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = sK1 ),
% 3.56/0.99      inference(global_propositional_subsumption,
% 3.56/0.99                [status(thm)],
% 3.56/0.99                [c_1798,c_14,c_13,c_12,c_232]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_3287,plain,
% 3.56/0.99      ( k2_pre_topc(sK0,sK1) = sK1 | l1_pre_topc(sK0) != iProver_top ),
% 3.56/0.99      inference(light_normalisation,[status(thm)],[c_3263,c_1950]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_15,plain,
% 3.56/0.99      ( l1_pre_topc(sK0) = iProver_top ),
% 3.56/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_3301,plain,
% 3.56/0.99      ( k2_pre_topc(sK0,sK1) = sK1 ),
% 3.56/0.99      inference(global_propositional_subsumption,
% 3.56/0.99                [status(thm)],
% 3.56/0.99                [c_3287,c_15]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_9,plain,
% 3.56/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.56/0.99      | ~ l1_pre_topc(X1)
% 3.56/0.99      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
% 3.56/0.99      inference(cnf_transformation,[],[f38]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_191,plain,
% 3.56/0.99      ( ~ m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(X0_44)))
% 3.56/0.99      | ~ l1_pre_topc(X0_44)
% 3.56/0.99      | k7_subset_1(u1_struct_0(X0_44),k2_pre_topc(X0_44,X0_42),k1_tops_1(X0_44,X0_42)) = k2_tops_1(X0_44,X0_42) ),
% 3.56/0.99      inference(subtyping,[status(esa)],[c_9]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_583,plain,
% 3.56/0.99      ( k7_subset_1(u1_struct_0(X0_44),k2_pre_topc(X0_44,X0_42),k1_tops_1(X0_44,X0_42)) = k2_tops_1(X0_44,X0_42)
% 3.56/0.99      | m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(X0_44))) != iProver_top
% 3.56/0.99      | l1_pre_topc(X0_44) != iProver_top ),
% 3.56/0.99      inference(predicate_to_equality,[status(thm)],[c_191]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_1209,plain,
% 3.56/0.99      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 3.56/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.56/0.99      inference(superposition,[status(thm)],[c_587,c_583]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_238,plain,
% 3.56/0.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.56/0.99      | ~ l1_pre_topc(sK0)
% 3.56/0.99      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 3.56/0.99      inference(instantiation,[status(thm)],[c_191]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_1453,plain,
% 3.56/0.99      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 3.56/0.99      inference(global_propositional_subsumption,
% 3.56/0.99                [status(thm)],
% 3.56/0.99                [c_1209,c_14,c_13,c_238]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_3304,plain,
% 3.56/0.99      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 3.56/0.99      inference(demodulation,[status(thm)],[c_3301,c_1453]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_3503,plain,
% 3.56/0.99      ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 3.56/0.99      inference(superposition,[status(thm)],[c_1777,c_3304]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_10,plain,
% 3.56/0.99      ( r1_tarski(k1_tops_1(X0,X1),X1)
% 3.56/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.56/0.99      | ~ l1_pre_topc(X0) ),
% 3.56/0.99      inference(cnf_transformation,[],[f39]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_190,plain,
% 3.56/0.99      ( r1_tarski(k1_tops_1(X0_44,X0_42),X0_42)
% 3.56/0.99      | ~ m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(X0_44)))
% 3.56/0.99      | ~ l1_pre_topc(X0_44) ),
% 3.56/0.99      inference(subtyping,[status(esa)],[c_10]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_584,plain,
% 3.56/0.99      ( r1_tarski(k1_tops_1(X0_44,X0_42),X0_42) = iProver_top
% 3.56/0.99      | m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(X0_44))) != iProver_top
% 3.56/0.99      | l1_pre_topc(X0_44) != iProver_top ),
% 3.56/0.99      inference(predicate_to_equality,[status(thm)],[c_190]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_1064,plain,
% 3.56/0.99      ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top
% 3.56/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.56/0.99      inference(superposition,[status(thm)],[c_587,c_584]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_16,plain,
% 3.56/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.56/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_240,plain,
% 3.56/0.99      ( r1_tarski(k1_tops_1(X0_44,X0_42),X0_42) = iProver_top
% 3.56/0.99      | m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(X0_44))) != iProver_top
% 3.56/0.99      | l1_pre_topc(X0_44) != iProver_top ),
% 3.56/0.99      inference(predicate_to_equality,[status(thm)],[c_190]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_242,plain,
% 3.56/0.99      ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top
% 3.56/0.99      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.56/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.56/0.99      inference(instantiation,[status(thm)],[c_240]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_1356,plain,
% 3.56/0.99      ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
% 3.56/0.99      inference(global_propositional_subsumption,
% 3.56/0.99                [status(thm)],
% 3.56/0.99                [c_1064,c_15,c_16,c_242]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_0,plain,
% 3.56/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.56/0.99      | k4_xboole_0(X1,X0) = k3_subset_1(X1,X0) ),
% 3.56/0.99      inference(cnf_transformation,[],[f29]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_129,plain,
% 3.56/0.99      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X1,X0) = k3_subset_1(X1,X0) ),
% 3.56/0.99      inference(bin_hyper_res,[status(thm)],[c_0,c_104]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_185,plain,
% 3.56/0.99      ( ~ r1_tarski(X0_42,X1_42)
% 3.56/0.99      | k4_xboole_0(X1_42,X0_42) = k3_subset_1(X1_42,X0_42) ),
% 3.56/0.99      inference(subtyping,[status(esa)],[c_129]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_589,plain,
% 3.56/0.99      ( k4_xboole_0(X0_42,X1_42) = k3_subset_1(X0_42,X1_42)
% 3.56/0.99      | r1_tarski(X1_42,X0_42) != iProver_top ),
% 3.56/0.99      inference(predicate_to_equality,[status(thm)],[c_185]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_1361,plain,
% 3.56/0.99      ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k3_subset_1(sK1,k1_tops_1(sK0,sK1)) ),
% 3.56/0.99      inference(superposition,[status(thm)],[c_1356,c_589]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_3506,plain,
% 3.56/0.99      ( k3_subset_1(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 3.56/0.99      inference(demodulation,[status(thm)],[c_3503,c_1361]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_1,plain,
% 3.56/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.56/0.99      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 3.56/0.99      inference(cnf_transformation,[],[f30]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_130,plain,
% 3.56/0.99      ( ~ r1_tarski(X0,X1)
% 3.56/0.99      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 3.56/0.99      inference(bin_hyper_res,[status(thm)],[c_1,c_104]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_184,plain,
% 3.56/0.99      ( ~ r1_tarski(X0_42,X1_42)
% 3.56/0.99      | m1_subset_1(k3_subset_1(X1_42,X0_42),k1_zfmisc_1(X1_42)) ),
% 3.56/0.99      inference(subtyping,[status(esa)],[c_130]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_590,plain,
% 3.56/0.99      ( r1_tarski(X0_42,X1_42) != iProver_top
% 3.56/0.99      | m1_subset_1(k3_subset_1(X1_42,X0_42),k1_zfmisc_1(X1_42)) = iProver_top ),
% 3.56/0.99      inference(predicate_to_equality,[status(thm)],[c_184]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_1597,plain,
% 3.56/0.99      ( r1_tarski(X0_42,X1_42) != iProver_top
% 3.56/0.99      | r1_tarski(k3_subset_1(X1_42,X0_42),X1_42) = iProver_top ),
% 3.56/0.99      inference(superposition,[status(thm)],[c_590,c_578]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_3629,plain,
% 3.56/0.99      ( r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top
% 3.56/0.99      | r1_tarski(k1_tops_1(sK0,sK1),sK1) != iProver_top ),
% 3.56/0.99      inference(superposition,[status(thm)],[c_3506,c_1597]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_11,negated_conjecture,
% 3.56/0.99      ( ~ r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
% 3.56/0.99      inference(cnf_transformation,[],[f43]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_189,negated_conjecture,
% 3.56/0.99      ( ~ r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
% 3.56/0.99      inference(subtyping,[status(esa)],[c_11]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_585,plain,
% 3.56/0.99      ( r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != iProver_top ),
% 3.56/0.99      inference(predicate_to_equality,[status(thm)],[c_189]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(c_1953,plain,
% 3.56/0.99      ( r1_tarski(k2_tops_1(sK0,sK1),sK1) != iProver_top ),
% 3.56/0.99      inference(demodulation,[status(thm)],[c_1950,c_585]) ).
% 3.56/0.99  
% 3.56/0.99  cnf(contradiction,plain,
% 3.56/0.99      ( $false ),
% 3.56/0.99      inference(minisat,[status(thm)],[c_3629,c_1953,c_242,c_16,c_15]) ).
% 3.56/0.99  
% 3.56/0.99  
% 3.56/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.56/0.99  
% 3.56/0.99  ------                               Statistics
% 3.56/0.99  
% 3.56/0.99  ------ Selected
% 3.56/0.99  
% 3.56/0.99  total_time:                             0.146
% 3.56/0.99  
%------------------------------------------------------------------------------
