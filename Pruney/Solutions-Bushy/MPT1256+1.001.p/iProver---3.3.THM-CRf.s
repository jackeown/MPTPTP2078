%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1256+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:14 EST 2020

% Result     : Theorem 15.53s
% Output     : CNFRefutation 15.53s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 426 expanded)
%              Number of clauses        :   86 ( 184 expanded)
%              Number of leaves         :   14 (  90 expanded)
%              Depth                    :   16
%              Number of atoms          :  343 (1136 expanded)
%              Number of equality atoms :  125 ( 212 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,sK1)),k2_tops_1(X0,sK1))
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1))
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,X1)),k2_tops_1(sK0,X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_tops_1(sK0,sK1))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f31,f30])).

fof(f47,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f32])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f46,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k2_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k2_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k2_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_tarski(X1,X2)
              | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
            & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | ~ r1_tarski(X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f48,plain,(
    ~ r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_tops_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_198,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_609,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_198])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_208,plain,
    ( ~ m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(X0_42)))
    | m1_subset_1(k2_pre_topc(X0_42,X0_40),k1_zfmisc_1(u1_struct_0(X0_42)))
    | ~ l1_pre_topc(X0_42) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_599,plain,
    ( m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(X0_42))) != iProver_top
    | m1_subset_1(k2_pre_topc(X0_42,X0_40),k1_zfmisc_1(u1_struct_0(X0_42))) = iProver_top
    | l1_pre_topc(X0_42) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_208])).

cnf(c_10,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_202,plain,
    ( r1_tarski(X0_40,X1_40)
    | ~ m1_subset_1(X0_40,k1_zfmisc_1(X1_40)) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_605,plain,
    ( r1_tarski(X0_40,X1_40) = iProver_top
    | m1_subset_1(X0_40,k1_zfmisc_1(X1_40)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_202])).

cnf(c_1454,plain,
    ( r1_tarski(k2_pre_topc(X0_42,X0_40),u1_struct_0(X0_42)) = iProver_top
    | m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(X0_42))) != iProver_top
    | l1_pre_topc(X0_42) != iProver_top ),
    inference(superposition,[status(thm)],[c_599,c_605])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X0,X2) = k9_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_112,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_9])).

cnf(c_139,plain,
    ( ~ r1_tarski(X0,X1)
    | k9_subset_1(X1,X0,X2) = k9_subset_1(X1,X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_0,c_112])).

cnf(c_196,plain,
    ( ~ r1_tarski(X0_40,X1_40)
    | k9_subset_1(X1_40,X0_40,X2_40) = k9_subset_1(X1_40,X2_40,X0_40) ),
    inference(subtyping,[status(esa)],[c_139])).

cnf(c_611,plain,
    ( k9_subset_1(X0_40,X1_40,X2_40) = k9_subset_1(X0_40,X2_40,X1_40)
    | r1_tarski(X1_40,X0_40) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_196])).

cnf(c_4243,plain,
    ( k9_subset_1(u1_struct_0(X0_42),k2_pre_topc(X0_42,X0_40),X1_40) = k9_subset_1(u1_struct_0(X0_42),X1_40,k2_pre_topc(X0_42,X0_40))
    | m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(X0_42))) != iProver_top
    | l1_pre_topc(X0_42) != iProver_top ),
    inference(superposition,[status(thm)],[c_1454,c_611])).

cnf(c_48233,plain,
    ( k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X0_40) = k9_subset_1(u1_struct_0(sK0),X0_40,k2_pre_topc(sK0,sK1))
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_609,c_4243])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_141,plain,
    ( ~ r1_tarski(X0,X1)
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_5,c_112])).

cnf(c_194,plain,
    ( ~ r1_tarski(X0_40,X1_40)
    | k9_subset_1(X1_40,X2_40,X0_40) = k3_xboole_0(X2_40,X0_40) ),
    inference(subtyping,[status(esa)],[c_141])).

cnf(c_613,plain,
    ( k9_subset_1(X0_40,X1_40,X2_40) = k3_xboole_0(X1_40,X2_40)
    | r1_tarski(X2_40,X0_40) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_194])).

cnf(c_4242,plain,
    ( k9_subset_1(u1_struct_0(X0_42),X0_40,k2_pre_topc(X0_42,X1_40)) = k3_xboole_0(X0_40,k2_pre_topc(X0_42,X1_40))
    | m1_subset_1(X1_40,k1_zfmisc_1(u1_struct_0(X0_42))) != iProver_top
    | l1_pre_topc(X0_42) != iProver_top ),
    inference(superposition,[status(thm)],[c_1454,c_613])).

cnf(c_45943,plain,
    ( k9_subset_1(u1_struct_0(sK0),X0_40,k2_pre_topc(sK0,sK1)) = k3_xboole_0(X0_40,k2_pre_topc(sK0,sK1))
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_609,c_4242])).

cnf(c_15,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_16,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_45982,plain,
    ( k9_subset_1(u1_struct_0(sK0),X0_40,k2_pre_topc(sK0,sK1)) = k3_xboole_0(X0_40,k2_pre_topc(sK0,sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_45943,c_16])).

cnf(c_48257,plain,
    ( k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X0_40) = k3_xboole_0(X0_40,k2_pre_topc(sK0,sK1))
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_48233,c_45982])).

cnf(c_49517,plain,
    ( k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X0_40) = k3_xboole_0(X0_40,k2_pre_topc(sK0,sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_48257,c_16])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_209,plain,
    ( ~ m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(X0_42)))
    | ~ l1_pre_topc(X0_42)
    | k9_subset_1(u1_struct_0(X0_42),k2_pre_topc(X0_42,X0_40),k2_pre_topc(X0_42,k3_subset_1(u1_struct_0(X0_42),X0_40))) = k2_tops_1(X0_42,X0_40) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_598,plain,
    ( k9_subset_1(u1_struct_0(X0_42),k2_pre_topc(X0_42,X0_40),k2_pre_topc(X0_42,k3_subset_1(u1_struct_0(X0_42),X0_40))) = k2_tops_1(X0_42,X0_40)
    | m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(X0_42))) != iProver_top
    | l1_pre_topc(X0_42) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_209])).

cnf(c_1453,plain,
    ( k9_subset_1(u1_struct_0(X0_42),k2_pre_topc(X0_42,k2_pre_topc(X0_42,X0_40)),k2_pre_topc(X0_42,k3_subset_1(u1_struct_0(X0_42),k2_pre_topc(X0_42,X0_40)))) = k2_tops_1(X0_42,k2_pre_topc(X0_42,X0_40))
    | m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(X0_42))) != iProver_top
    | l1_pre_topc(X0_42) != iProver_top ),
    inference(superposition,[status(thm)],[c_599,c_598])).

cnf(c_7781,plain,
    ( k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)))) = k2_tops_1(sK0,k2_pre_topc(sK0,sK1))
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_609,c_1453])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k2_pre_topc(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_207,plain,
    ( ~ m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(X0_42)))
    | ~ l1_pre_topc(X0_42)
    | k2_pre_topc(X0_42,k2_pre_topc(X0_42,X0_40)) = k2_pre_topc(X0_42,X0_40) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_600,plain,
    ( k2_pre_topc(X0_42,k2_pre_topc(X0_42,X0_40)) = k2_pre_topc(X0_42,X0_40)
    | m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(X0_42))) != iProver_top
    | l1_pre_topc(X0_42) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_207])).

cnf(c_1632,plain,
    ( k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)) = k2_pre_topc(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_609,c_600])).

cnf(c_238,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_207])).

cnf(c_1839,plain,
    ( k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1632,c_15,c_14,c_238])).

cnf(c_7805,plain,
    ( k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)))) = k2_tops_1(sK0,k2_pre_topc(sK0,sK1))
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7781,c_1839])).

cnf(c_8780,plain,
    ( k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)))) = k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7805,c_16])).

cnf(c_49528,plain,
    ( k3_xboole_0(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))),k2_pre_topc(sK0,sK1)) = k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_49517,c_8780])).

cnf(c_1199,plain,
    ( k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k2_tops_1(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_609,c_598])).

cnf(c_232,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k2_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_209])).

cnf(c_1845,plain,
    ( k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k2_tops_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1199,c_15,c_14,c_232])).

cnf(c_49525,plain,
    ( k3_xboole_0(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_49517,c_1845])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_206,plain,
    ( ~ r1_tarski(X0_40,X1_40)
    | r1_tarski(k3_xboole_0(X0_40,X2_40),k3_xboole_0(X1_40,X2_40)) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_601,plain,
    ( r1_tarski(X0_40,X1_40) != iProver_top
    | r1_tarski(k3_xboole_0(X0_40,X2_40),k3_xboole_0(X1_40,X2_40)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_206])).

cnf(c_49535,plain,
    ( r1_tarski(X0_40,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) != iProver_top
    | r1_tarski(k3_xboole_0(X0_40,k2_pre_topc(sK0,sK1)),k2_tops_1(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_49525,c_601])).

cnf(c_50267,plain,
    ( r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_tops_1(sK0,sK1)) = iProver_top
    | r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_49528,c_49535])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_pre_topc(X2,X0),k2_pre_topc(X2,X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_200,plain,
    ( ~ r1_tarski(X0_40,X1_40)
    | r1_tarski(k2_pre_topc(X0_42,X0_40),k2_pre_topc(X0_42,X1_40))
    | ~ m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(X0_42)))
    | ~ m1_subset_1(X1_40,k1_zfmisc_1(u1_struct_0(X0_42)))
    | ~ l1_pre_topc(X0_42) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1759,plain,
    ( ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(X0_42,X0_40)),k3_subset_1(u1_struct_0(sK0),X0_40))
    | r1_tarski(k2_pre_topc(X1_42,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(X0_42,X0_40))),k2_pre_topc(X1_42,k3_subset_1(u1_struct_0(sK0),X0_40)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0_40),k1_zfmisc_1(u1_struct_0(X1_42)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(X0_42,X0_40)),k1_zfmisc_1(u1_struct_0(X1_42)))
    | ~ l1_pre_topc(X1_42) ),
    inference(instantiation,[status(thm)],[c_200])).

cnf(c_1790,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(X0_42,X0_40)),k3_subset_1(u1_struct_0(sK0),X0_40)) != iProver_top
    | r1_tarski(k2_pre_topc(X1_42,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(X0_42,X0_40))),k2_pre_topc(X1_42,k3_subset_1(u1_struct_0(sK0),X0_40))) = iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0_40),k1_zfmisc_1(u1_struct_0(X1_42))) != iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(X0_42,X0_40)),k1_zfmisc_1(u1_struct_0(X1_42))) != iProver_top
    | l1_pre_topc(X1_42) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1759])).

cnf(c_1792,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),k3_subset_1(u1_struct_0(sK0),sK1)) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1790])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k3_subset_1(X2,X1),k3_subset_1(X2,X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_204,plain,
    ( ~ r1_tarski(X0_40,X1_40)
    | r1_tarski(k3_subset_1(X2_40,X1_40),k3_subset_1(X2_40,X0_40))
    | ~ m1_subset_1(X1_40,k1_zfmisc_1(X2_40))
    | ~ m1_subset_1(X0_40,k1_zfmisc_1(X2_40)) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_806,plain,
    ( ~ r1_tarski(X0_40,k2_pre_topc(X0_42,X0_40))
    | r1_tarski(k3_subset_1(X1_40,k2_pre_topc(X0_42,X0_40)),k3_subset_1(X1_40,X0_40))
    | ~ m1_subset_1(X0_40,k1_zfmisc_1(X1_40))
    | ~ m1_subset_1(k2_pre_topc(X0_42,X0_40),k1_zfmisc_1(X1_40)) ),
    inference(instantiation,[status(thm)],[c_204])).

cnf(c_1252,plain,
    ( ~ r1_tarski(X0_40,k2_pre_topc(X0_42,X0_40))
    | r1_tarski(k3_subset_1(u1_struct_0(X0_42),k2_pre_topc(X0_42,X0_40)),k3_subset_1(u1_struct_0(X0_42),X0_40))
    | ~ m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(X0_42)))
    | ~ m1_subset_1(k2_pre_topc(X0_42,X0_40),k1_zfmisc_1(u1_struct_0(X0_42))) ),
    inference(instantiation,[status(thm)],[c_806])).

cnf(c_1253,plain,
    ( r1_tarski(X0_40,k2_pre_topc(X0_42,X0_40)) != iProver_top
    | r1_tarski(k3_subset_1(u1_struct_0(X0_42),k2_pre_topc(X0_42,X0_40)),k3_subset_1(u1_struct_0(X0_42),X0_40)) = iProver_top
    | m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(X0_42))) != iProver_top
    | m1_subset_1(k2_pre_topc(X0_42,X0_40),k1_zfmisc_1(u1_struct_0(X0_42))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1252])).

cnf(c_1255,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),k3_subset_1(u1_struct_0(sK0),sK1)) = iProver_top
    | r1_tarski(sK1,k2_pre_topc(sK0,sK1)) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1253])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_140,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(bin_hyper_res,[status(thm)],[c_3,c_112])).

cnf(c_195,plain,
    ( ~ r1_tarski(X0_40,X1_40)
    | m1_subset_1(k3_subset_1(X1_40,X0_40),k1_zfmisc_1(X1_40)) ),
    inference(subtyping,[status(esa)],[c_140])).

cnf(c_922,plain,
    ( ~ r1_tarski(k2_pre_topc(X0_42,X0_40),u1_struct_0(X0_42))
    | m1_subset_1(k3_subset_1(u1_struct_0(X0_42),k2_pre_topc(X0_42,X0_40)),k1_zfmisc_1(u1_struct_0(X0_42))) ),
    inference(instantiation,[status(thm)],[c_195])).

cnf(c_928,plain,
    ( r1_tarski(k2_pre_topc(X0_42,X0_40),u1_struct_0(X0_42)) != iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(X0_42),k2_pre_topc(X0_42,X0_40)),k1_zfmisc_1(u1_struct_0(X0_42))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_922])).

cnf(c_930,plain,
    ( r1_tarski(k2_pre_topc(sK0,sK1),u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_928])).

cnf(c_848,plain,
    ( ~ r1_tarski(sK1,u1_struct_0(sK0))
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_195])).

cnf(c_850,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_848])).

cnf(c_758,plain,
    ( r1_tarski(k2_pre_topc(X0_42,X0_40),u1_struct_0(X0_42))
    | ~ m1_subset_1(k2_pre_topc(X0_42,X0_40),k1_zfmisc_1(u1_struct_0(X0_42))) ),
    inference(instantiation,[status(thm)],[c_202])).

cnf(c_759,plain,
    ( r1_tarski(k2_pre_topc(X0_42,X0_40),u1_struct_0(X0_42)) = iProver_top
    | m1_subset_1(k2_pre_topc(X0_42,X0_40),k1_zfmisc_1(u1_struct_0(X0_42))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_758])).

cnf(c_761,plain,
    ( r1_tarski(k2_pre_topc(sK0,sK1),u1_struct_0(sK0)) = iProver_top
    | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_759])).

cnf(c_740,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_202])).

cnf(c_741,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_740])).

cnf(c_11,plain,
    ( r1_tarski(X0,k2_pre_topc(X1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_201,plain,
    ( r1_tarski(X0_40,k2_pre_topc(X0_42,X0_40))
    | ~ m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(X0_42)))
    | ~ l1_pre_topc(X0_42) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_255,plain,
    ( r1_tarski(X0_40,k2_pre_topc(X0_42,X0_40)) = iProver_top
    | m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(X0_42))) != iProver_top
    | l1_pre_topc(X0_42) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_201])).

cnf(c_257,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1)) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_255])).

cnf(c_234,plain,
    ( m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(X0_42))) != iProver_top
    | m1_subset_1(k2_pre_topc(X0_42,X0_40),k1_zfmisc_1(u1_struct_0(X0_42))) = iProver_top
    | l1_pre_topc(X0_42) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_208])).

cnf(c_236,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_234])).

cnf(c_13,negated_conjecture,
    ( ~ r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_tops_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_18,plain,
    ( r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_tops_1(sK0,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_17,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_50267,c_1792,c_1255,c_930,c_850,c_761,c_741,c_257,c_236,c_18,c_17,c_16])).


%------------------------------------------------------------------------------
