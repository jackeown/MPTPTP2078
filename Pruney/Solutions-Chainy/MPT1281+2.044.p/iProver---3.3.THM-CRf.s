%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:15:47 EST 2020

% Result     : Theorem 3.84s
% Output     : CNFRefutation 3.84s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 329 expanded)
%              Number of clauses        :   65 ( 110 expanded)
%              Number of leaves         :   12 (  77 expanded)
%              Depth                    :   18
%              Number of atoms          :  260 (1112 expanded)
%              Number of equality atoms :   80 ( 113 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    5 (   2 average)

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

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1)))
          & v5_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1)))
          & v5_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1)))
          & v5_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_tarski(k2_tops_1(X0,sK1),k2_pre_topc(X0,k1_tops_1(X0,sK1)))
        & v5_tops_1(sK1,X0)
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
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

fof(f29,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))
    & v5_tops_1(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f28,f27])).

fof(f41,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f29])).

fof(f6,axiom,(
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
    inference(ennf_transformation,[],[f6])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f40,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f15])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f5,axiom,(
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
    inference(ennf_transformation,[],[f5])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_tops_1(X1,X0)
              | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1 )
            & ( k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1
              | ~ v5_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1
      | ~ v5_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f42,plain,(
    v5_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f43,plain,(
    ~ r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_309,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1751,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_309])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_13,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_204,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_13])).

cnf(c_205,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_204])).

cnf(c_304,plain,
    ( ~ m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k1_tops_1(sK0,X0_42),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_205])).

cnf(c_1750,plain,
    ( m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k1_tops_1(sK0,X0_42),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_304])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_192,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_13])).

cnf(c_193,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_192])).

cnf(c_305,plain,
    ( ~ m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_tops_1(sK0,X0_42),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_193])).

cnf(c_1749,plain,
    ( m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_tops_1(sK0,X0_42),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_305])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_311,plain,
    ( ~ m1_subset_1(X0_42,k1_zfmisc_1(X0_44))
    | ~ m1_subset_1(X1_42,k1_zfmisc_1(X0_44))
    | k4_subset_1(X0_44,X1_42,X0_42) = k2_xboole_0(X1_42,X0_42) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1746,plain,
    ( k4_subset_1(X0_44,X0_42,X1_42) = k2_xboole_0(X0_42,X1_42)
    | m1_subset_1(X0_42,k1_zfmisc_1(X0_44)) != iProver_top
    | m1_subset_1(X1_42,k1_zfmisc_1(X0_44)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_311])).

cnf(c_1957,plain,
    ( k4_subset_1(u1_struct_0(sK0),X0_42,k2_tops_1(sK0,X1_42)) = k2_xboole_0(X0_42,k2_tops_1(sK0,X1_42))
    | m1_subset_1(X1_42,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1749,c_1746])).

cnf(c_3106,plain,
    ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X0_42),k2_tops_1(sK0,X1_42)) = k2_xboole_0(k1_tops_1(sK0,X0_42),k2_tops_1(sK0,X1_42))
    | m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1_42,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1750,c_1957])).

cnf(c_6838,plain,
    ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k2_tops_1(sK0,X0_42)) = k2_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,X0_42))
    | m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1751,c_3106])).

cnf(c_7300,plain,
    ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,X0_42))) = k2_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,X0_42)))
    | m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1750,c_6838])).

cnf(c_7330,plain,
    ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1))) = k2_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1))) ),
    inference(superposition,[status(thm)],[c_1751,c_7300])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_180,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_13])).

cnf(c_181,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_180])).

cnf(c_306,plain,
    ( ~ m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),X0_42,k2_tops_1(sK0,X0_42)) = k2_pre_topc(sK0,X0_42) ),
    inference(subtyping,[status(esa)],[c_181])).

cnf(c_1748,plain,
    ( k4_subset_1(u1_struct_0(sK0),X0_42,k2_tops_1(sK0,X0_42)) = k2_pre_topc(sK0,X0_42)
    | m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_306])).

cnf(c_1885,plain,
    ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X0_42),k2_tops_1(sK0,k1_tops_1(sK0,X0_42))) = k2_pre_topc(sK0,k1_tops_1(sK0,X0_42))
    | m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1750,c_1748])).

cnf(c_2192,plain,
    ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1))) = k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_1751,c_1885])).

cnf(c_5,plain,
    ( ~ v5_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k1_tops_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_11,negated_conjecture,
    ( v5_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_159,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k1_tops_1(X1,X0)) = X0
    | sK1 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_11])).

cnf(c_160,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = sK1 ),
    inference(unflattening,[status(thm)],[c_159])).

cnf(c_162,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_160,c_13,c_12])).

cnf(c_308,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = sK1 ),
    inference(subtyping,[status(esa)],[c_162])).

cnf(c_2204,plain,
    ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1))) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2192,c_308])).

cnf(c_7342,plain,
    ( k2_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1))) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_7330,c_2204])).

cnf(c_1,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_313,plain,
    ( r1_tarski(k4_xboole_0(X0_42,X1_42),X0_42) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1744,plain,
    ( r1_tarski(k4_xboole_0(X0_42,X1_42),X0_42) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_313])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k2_tops_1(X1,k2_pre_topc(X1,X0)),k2_tops_1(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_168,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k2_tops_1(X1,k2_pre_topc(X1,X0)),k2_tops_1(X1,X0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_13])).

cnf(c_169,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,X0)),k2_tops_1(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_168])).

cnf(c_307,plain,
    ( ~ m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,X0_42)),k2_tops_1(sK0,X0_42)) ),
    inference(subtyping,[status(esa)],[c_169])).

cnf(c_1747,plain,
    ( m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,X0_42)),k2_tops_1(sK0,X0_42)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_307])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_314,plain,
    ( ~ r1_tarski(X0_42,X1_42)
    | ~ r1_tarski(X2_42,X0_42)
    | r1_tarski(X2_42,X1_42) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1743,plain,
    ( r1_tarski(X0_42,X1_42) != iProver_top
    | r1_tarski(X2_42,X0_42) != iProver_top
    | r1_tarski(X2_42,X1_42) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_314])).

cnf(c_1908,plain,
    ( m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X1_42,k2_tops_1(sK0,X0_42)) = iProver_top
    | r1_tarski(X1_42,k2_tops_1(sK0,k2_pre_topc(sK0,X0_42))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1747,c_1743])).

cnf(c_2477,plain,
    ( m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k4_xboole_0(k2_tops_1(sK0,k2_pre_topc(sK0,X0_42)),X1_42),k2_tops_1(sK0,X0_42)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1744,c_1908])).

cnf(c_4754,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k4_xboole_0(k2_tops_1(sK0,sK1),X0_42),k2_tops_1(sK0,k1_tops_1(sK0,sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_308,c_2477])).

cnf(c_15,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_353,plain,
    ( m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k1_tops_1(sK0,X0_42),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_304])).

cnf(c_355,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_353])).

cnf(c_4890,plain,
    ( r1_tarski(k4_xboole_0(k2_tops_1(sK0,sK1),X0_42),k2_tops_1(sK0,k1_tops_1(sK0,sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4754,c_15,c_355])).

cnf(c_2,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2))
    | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_312,plain,
    ( r1_tarski(X0_42,k2_xboole_0(X1_42,X2_42))
    | ~ r1_tarski(k4_xboole_0(X0_42,X1_42),X2_42) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1745,plain,
    ( r1_tarski(X0_42,k2_xboole_0(X1_42,X2_42)) = iProver_top
    | r1_tarski(k4_xboole_0(X0_42,X1_42),X2_42) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_312])).

cnf(c_4897,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),k2_xboole_0(X0_42,k2_tops_1(sK0,k1_tops_1(sK0,sK1)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4890,c_1745])).

cnf(c_7383,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_7342,c_4897])).

cnf(c_10,negated_conjecture,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_310,negated_conjecture,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1752,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_310])).

cnf(c_1762,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1752,c_308])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7383,c_1762])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:11:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.84/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.84/1.00  
% 3.84/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.84/1.00  
% 3.84/1.00  ------  iProver source info
% 3.84/1.00  
% 3.84/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.84/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.84/1.00  git: non_committed_changes: false
% 3.84/1.00  git: last_make_outside_of_git: false
% 3.84/1.00  
% 3.84/1.00  ------ 
% 3.84/1.00  ------ Parsing...
% 3.84/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.84/1.00  
% 3.84/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.84/1.00  
% 3.84/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.84/1.00  
% 3.84/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.84/1.00  ------ Proving...
% 3.84/1.00  ------ Problem Properties 
% 3.84/1.00  
% 3.84/1.00  
% 3.84/1.00  clauses                                 11
% 3.84/1.00  conjectures                             2
% 3.84/1.00  EPR                                     1
% 3.84/1.00  Horn                                    11
% 3.84/1.00  unary                                   4
% 3.84/1.00  binary                                  5
% 3.84/1.00  lits                                    20
% 3.84/1.00  lits eq                                 3
% 3.84/1.00  fd_pure                                 0
% 3.84/1.00  fd_pseudo                               0
% 3.84/1.00  fd_cond                                 0
% 3.84/1.00  fd_pseudo_cond                          0
% 3.84/1.00  AC symbols                              0
% 3.84/1.00  
% 3.84/1.00  ------ Input Options Time Limit: Unbounded
% 3.84/1.00  
% 3.84/1.00  
% 3.84/1.00  
% 3.84/1.00  
% 3.84/1.00  ------ Preprocessing...
% 3.84/1.00  
% 3.84/1.00  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 3.84/1.00  Current options:
% 3.84/1.00  ------ 
% 3.84/1.00  
% 3.84/1.00  
% 3.84/1.00  
% 3.84/1.00  
% 3.84/1.00  ------ Proving...
% 3.84/1.00  
% 3.84/1.00  
% 3.84/1.00  ------ Preprocessing...
% 3.84/1.00  
% 3.84/1.00  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.84/1.00  
% 3.84/1.00  ------ Proving...
% 3.84/1.00  
% 3.84/1.00  
% 3.84/1.00  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.84/1.00  
% 3.84/1.00  ------ Proving...
% 3.84/1.00  
% 3.84/1.00  
% 3.84/1.00  ------ Preprocessing...
% 3.84/1.00  
% 3.84/1.00  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.84/1.00  
% 3.84/1.00  ------ Proving...
% 3.84/1.00  
% 3.84/1.00  
% 3.84/1.00  ------ Preprocessing...
% 3.84/1.00  
% 3.84/1.00  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.84/1.00  
% 3.84/1.00  ------ Proving...
% 3.84/1.00  
% 3.84/1.00  
% 3.84/1.00  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.84/1.00  
% 3.84/1.00  ------ Proving...
% 3.84/1.00  
% 3.84/1.00  
% 3.84/1.00  ------ Preprocessing...
% 3.84/1.00  
% 3.84/1.00  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.84/1.00  
% 3.84/1.00  ------ Proving...
% 3.84/1.00  
% 3.84/1.00  
% 3.84/1.00  ------ Preprocessing...
% 3.84/1.00  
% 3.84/1.00  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.84/1.00  
% 3.84/1.00  ------ Proving...
% 3.84/1.00  
% 3.84/1.00  
% 3.84/1.00  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.84/1.00  
% 3.84/1.00  ------ Proving...
% 3.84/1.00  
% 3.84/1.00  
% 3.84/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.84/1.00  
% 3.84/1.00  ------ Proving...
% 3.84/1.00  
% 3.84/1.00  
% 3.84/1.00  % SZS status Theorem for theBenchmark.p
% 3.84/1.00  
% 3.84/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.84/1.00  
% 3.84/1.00  fof(f10,conjecture,(
% 3.84/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v5_tops_1(X1,X0) => r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))))))),
% 3.84/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/1.00  
% 3.84/1.00  fof(f11,negated_conjecture,(
% 3.84/1.00    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v5_tops_1(X1,X0) => r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))))))),
% 3.84/1.00    inference(negated_conjecture,[],[f10])).
% 3.84/1.00  
% 3.84/1.00  fof(f24,plain,(
% 3.84/1.00    ? [X0] : (? [X1] : ((~r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))) & v5_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.84/1.00    inference(ennf_transformation,[],[f11])).
% 3.84/1.00  
% 3.84/1.00  fof(f25,plain,(
% 3.84/1.00    ? [X0] : (? [X1] : (~r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))) & v5_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.84/1.00    inference(flattening,[],[f24])).
% 3.84/1.00  
% 3.84/1.00  fof(f28,plain,(
% 3.84/1.00    ( ! [X0] : (? [X1] : (~r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))) & v5_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~r1_tarski(k2_tops_1(X0,sK1),k2_pre_topc(X0,k1_tops_1(X0,sK1))) & v5_tops_1(sK1,X0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.84/1.00    introduced(choice_axiom,[])).
% 3.84/1.00  
% 3.84/1.00  fof(f27,plain,(
% 3.84/1.00    ? [X0] : (? [X1] : (~r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))) & v5_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (~r1_tarski(k2_tops_1(sK0,X1),k2_pre_topc(sK0,k1_tops_1(sK0,X1))) & v5_tops_1(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 3.84/1.00    introduced(choice_axiom,[])).
% 3.84/1.00  
% 3.84/1.00  fof(f29,plain,(
% 3.84/1.00    (~r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) & v5_tops_1(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 3.84/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f28,f27])).
% 3.84/1.00  
% 3.84/1.00  fof(f41,plain,(
% 3.84/1.00    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.84/1.00    inference(cnf_transformation,[],[f29])).
% 3.84/1.00  
% 3.84/1.00  fof(f6,axiom,(
% 3.84/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.84/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/1.00  
% 3.84/1.00  fof(f18,plain,(
% 3.84/1.00    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.84/1.00    inference(ennf_transformation,[],[f6])).
% 3.84/1.00  
% 3.84/1.00  fof(f19,plain,(
% 3.84/1.00    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.84/1.00    inference(flattening,[],[f18])).
% 3.84/1.00  
% 3.84/1.00  fof(f36,plain,(
% 3.84/1.00    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.84/1.00    inference(cnf_transformation,[],[f19])).
% 3.84/1.00  
% 3.84/1.00  fof(f40,plain,(
% 3.84/1.00    l1_pre_topc(sK0)),
% 3.84/1.00    inference(cnf_transformation,[],[f29])).
% 3.84/1.00  
% 3.84/1.00  fof(f7,axiom,(
% 3.84/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.84/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/1.00  
% 3.84/1.00  fof(f20,plain,(
% 3.84/1.00    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.84/1.00    inference(ennf_transformation,[],[f7])).
% 3.84/1.00  
% 3.84/1.00  fof(f21,plain,(
% 3.84/1.00    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.84/1.00    inference(flattening,[],[f20])).
% 3.84/1.00  
% 3.84/1.00  fof(f37,plain,(
% 3.84/1.00    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.84/1.00    inference(cnf_transformation,[],[f21])).
% 3.84/1.00  
% 3.84/1.00  fof(f4,axiom,(
% 3.84/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 3.84/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/1.00  
% 3.84/1.00  fof(f15,plain,(
% 3.84/1.00    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 3.84/1.00    inference(ennf_transformation,[],[f4])).
% 3.84/1.00  
% 3.84/1.00  fof(f16,plain,(
% 3.84/1.00    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.84/1.00    inference(flattening,[],[f15])).
% 3.84/1.00  
% 3.84/1.00  fof(f33,plain,(
% 3.84/1.00    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.84/1.00    inference(cnf_transformation,[],[f16])).
% 3.84/1.00  
% 3.84/1.00  fof(f8,axiom,(
% 3.84/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)))),
% 3.84/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/1.00  
% 3.84/1.00  fof(f22,plain,(
% 3.84/1.00    ! [X0] : (! [X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.84/1.00    inference(ennf_transformation,[],[f8])).
% 3.84/1.00  
% 3.84/1.00  fof(f38,plain,(
% 3.84/1.00    ( ! [X0,X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.84/1.00    inference(cnf_transformation,[],[f22])).
% 3.84/1.00  
% 3.84/1.00  fof(f5,axiom,(
% 3.84/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v5_tops_1(X1,X0) <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1)))),
% 3.84/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/1.00  
% 3.84/1.00  fof(f17,plain,(
% 3.84/1.00    ! [X0] : (! [X1] : ((v5_tops_1(X1,X0) <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.84/1.00    inference(ennf_transformation,[],[f5])).
% 3.84/1.00  
% 3.84/1.00  fof(f26,plain,(
% 3.84/1.00    ! [X0] : (! [X1] : (((v5_tops_1(X1,X0) | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1) & (k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 | ~v5_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.84/1.00    inference(nnf_transformation,[],[f17])).
% 3.84/1.00  
% 3.84/1.00  fof(f34,plain,(
% 3.84/1.00    ( ! [X0,X1] : (k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 | ~v5_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.84/1.00    inference(cnf_transformation,[],[f26])).
% 3.84/1.00  
% 3.84/1.00  fof(f42,plain,(
% 3.84/1.00    v5_tops_1(sK1,sK0)),
% 3.84/1.00    inference(cnf_transformation,[],[f29])).
% 3.84/1.00  
% 3.84/1.00  fof(f2,axiom,(
% 3.84/1.00    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 3.84/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/1.00  
% 3.84/1.00  fof(f31,plain,(
% 3.84/1.00    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 3.84/1.00    inference(cnf_transformation,[],[f2])).
% 3.84/1.00  
% 3.84/1.00  fof(f9,axiom,(
% 3.84/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1))))),
% 3.84/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/1.00  
% 3.84/1.00  fof(f23,plain,(
% 3.84/1.00    ! [X0] : (! [X1] : (r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.84/1.00    inference(ennf_transformation,[],[f9])).
% 3.84/1.00  
% 3.84/1.00  fof(f39,plain,(
% 3.84/1.00    ( ! [X0,X1] : (r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.84/1.00    inference(cnf_transformation,[],[f23])).
% 3.84/1.00  
% 3.84/1.00  fof(f1,axiom,(
% 3.84/1.00    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 3.84/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/1.00  
% 3.84/1.00  fof(f12,plain,(
% 3.84/1.00    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 3.84/1.00    inference(ennf_transformation,[],[f1])).
% 3.84/1.00  
% 3.84/1.00  fof(f13,plain,(
% 3.84/1.00    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 3.84/1.00    inference(flattening,[],[f12])).
% 3.84/1.00  
% 3.84/1.00  fof(f30,plain,(
% 3.84/1.00    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 3.84/1.00    inference(cnf_transformation,[],[f13])).
% 3.84/1.00  
% 3.84/1.00  fof(f3,axiom,(
% 3.84/1.00    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 3.84/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/1.00  
% 3.84/1.00  fof(f14,plain,(
% 3.84/1.00    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 3.84/1.00    inference(ennf_transformation,[],[f3])).
% 3.84/1.00  
% 3.84/1.00  fof(f32,plain,(
% 3.84/1.00    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 3.84/1.00    inference(cnf_transformation,[],[f14])).
% 3.84/1.00  
% 3.84/1.00  fof(f43,plain,(
% 3.84/1.00    ~r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))),
% 3.84/1.00    inference(cnf_transformation,[],[f29])).
% 3.84/1.00  
% 3.84/1.00  cnf(c_12,negated_conjecture,
% 3.84/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.84/1.00      inference(cnf_transformation,[],[f41]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_309,negated_conjecture,
% 3.84/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.84/1.00      inference(subtyping,[status(esa)],[c_12]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_1751,plain,
% 3.84/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.84/1.00      inference(predicate_to_equality,[status(thm)],[c_309]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_6,plain,
% 3.84/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.84/1.00      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.84/1.00      | ~ l1_pre_topc(X1) ),
% 3.84/1.00      inference(cnf_transformation,[],[f36]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_13,negated_conjecture,
% 3.84/1.00      ( l1_pre_topc(sK0) ),
% 3.84/1.00      inference(cnf_transformation,[],[f40]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_204,plain,
% 3.84/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.84/1.00      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.84/1.00      | sK0 != X1 ),
% 3.84/1.00      inference(resolution_lifted,[status(thm)],[c_6,c_13]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_205,plain,
% 3.84/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.84/1.00      | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.84/1.00      inference(unflattening,[status(thm)],[c_204]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_304,plain,
% 3.84/1.00      ( ~ m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.84/1.00      | m1_subset_1(k1_tops_1(sK0,X0_42),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.84/1.00      inference(subtyping,[status(esa)],[c_205]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_1750,plain,
% 3.84/1.00      ( m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.84/1.00      | m1_subset_1(k1_tops_1(sK0,X0_42),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.84/1.00      inference(predicate_to_equality,[status(thm)],[c_304]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_7,plain,
% 3.84/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.84/1.00      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.84/1.00      | ~ l1_pre_topc(X1) ),
% 3.84/1.00      inference(cnf_transformation,[],[f37]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_192,plain,
% 3.84/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.84/1.00      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.84/1.00      | sK0 != X1 ),
% 3.84/1.00      inference(resolution_lifted,[status(thm)],[c_7,c_13]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_193,plain,
% 3.84/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.84/1.00      | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.84/1.00      inference(unflattening,[status(thm)],[c_192]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_305,plain,
% 3.84/1.00      ( ~ m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.84/1.00      | m1_subset_1(k2_tops_1(sK0,X0_42),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.84/1.00      inference(subtyping,[status(esa)],[c_193]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_1749,plain,
% 3.84/1.00      ( m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.84/1.00      | m1_subset_1(k2_tops_1(sK0,X0_42),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.84/1.00      inference(predicate_to_equality,[status(thm)],[c_305]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_3,plain,
% 3.84/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.84/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.84/1.00      | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
% 3.84/1.00      inference(cnf_transformation,[],[f33]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_311,plain,
% 3.84/1.00      ( ~ m1_subset_1(X0_42,k1_zfmisc_1(X0_44))
% 3.84/1.00      | ~ m1_subset_1(X1_42,k1_zfmisc_1(X0_44))
% 3.84/1.00      | k4_subset_1(X0_44,X1_42,X0_42) = k2_xboole_0(X1_42,X0_42) ),
% 3.84/1.00      inference(subtyping,[status(esa)],[c_3]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_1746,plain,
% 3.84/1.00      ( k4_subset_1(X0_44,X0_42,X1_42) = k2_xboole_0(X0_42,X1_42)
% 3.84/1.00      | m1_subset_1(X0_42,k1_zfmisc_1(X0_44)) != iProver_top
% 3.84/1.00      | m1_subset_1(X1_42,k1_zfmisc_1(X0_44)) != iProver_top ),
% 3.84/1.00      inference(predicate_to_equality,[status(thm)],[c_311]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_1957,plain,
% 3.84/1.00      ( k4_subset_1(u1_struct_0(sK0),X0_42,k2_tops_1(sK0,X1_42)) = k2_xboole_0(X0_42,k2_tops_1(sK0,X1_42))
% 3.84/1.00      | m1_subset_1(X1_42,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.84/1.00      | m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_1749,c_1746]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_3106,plain,
% 3.84/1.00      ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X0_42),k2_tops_1(sK0,X1_42)) = k2_xboole_0(k1_tops_1(sK0,X0_42),k2_tops_1(sK0,X1_42))
% 3.84/1.00      | m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.84/1.00      | m1_subset_1(X1_42,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_1750,c_1957]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_6838,plain,
% 3.84/1.00      ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k2_tops_1(sK0,X0_42)) = k2_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,X0_42))
% 3.84/1.00      | m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_1751,c_3106]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_7300,plain,
% 3.84/1.00      ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,X0_42))) = k2_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,X0_42)))
% 3.84/1.00      | m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_1750,c_6838]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_7330,plain,
% 3.84/1.00      ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1))) = k2_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1))) ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_1751,c_7300]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_8,plain,
% 3.84/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.84/1.00      | ~ l1_pre_topc(X1)
% 3.84/1.00      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
% 3.84/1.00      inference(cnf_transformation,[],[f38]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_180,plain,
% 3.84/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.84/1.00      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0)
% 3.84/1.00      | sK0 != X1 ),
% 3.84/1.00      inference(resolution_lifted,[status(thm)],[c_8,c_13]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_181,plain,
% 3.84/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.84/1.00      | k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0) ),
% 3.84/1.00      inference(unflattening,[status(thm)],[c_180]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_306,plain,
% 3.84/1.00      ( ~ m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.84/1.00      | k4_subset_1(u1_struct_0(sK0),X0_42,k2_tops_1(sK0,X0_42)) = k2_pre_topc(sK0,X0_42) ),
% 3.84/1.00      inference(subtyping,[status(esa)],[c_181]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_1748,plain,
% 3.84/1.00      ( k4_subset_1(u1_struct_0(sK0),X0_42,k2_tops_1(sK0,X0_42)) = k2_pre_topc(sK0,X0_42)
% 3.84/1.00      | m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.84/1.00      inference(predicate_to_equality,[status(thm)],[c_306]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_1885,plain,
% 3.84/1.00      ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X0_42),k2_tops_1(sK0,k1_tops_1(sK0,X0_42))) = k2_pre_topc(sK0,k1_tops_1(sK0,X0_42))
% 3.84/1.00      | m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_1750,c_1748]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_2192,plain,
% 3.84/1.00      ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1))) = k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_1751,c_1885]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_5,plain,
% 3.84/1.00      ( ~ v5_tops_1(X0,X1)
% 3.84/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.84/1.00      | ~ l1_pre_topc(X1)
% 3.84/1.00      | k2_pre_topc(X1,k1_tops_1(X1,X0)) = X0 ),
% 3.84/1.00      inference(cnf_transformation,[],[f34]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_11,negated_conjecture,
% 3.84/1.00      ( v5_tops_1(sK1,sK0) ),
% 3.84/1.00      inference(cnf_transformation,[],[f42]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_159,plain,
% 3.84/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.84/1.00      | ~ l1_pre_topc(X1)
% 3.84/1.00      | k2_pre_topc(X1,k1_tops_1(X1,X0)) = X0
% 3.84/1.00      | sK1 != X0
% 3.84/1.00      | sK0 != X1 ),
% 3.84/1.00      inference(resolution_lifted,[status(thm)],[c_5,c_11]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_160,plain,
% 3.84/1.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.84/1.00      | ~ l1_pre_topc(sK0)
% 3.84/1.00      | k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = sK1 ),
% 3.84/1.00      inference(unflattening,[status(thm)],[c_159]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_162,plain,
% 3.84/1.00      ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = sK1 ),
% 3.84/1.00      inference(global_propositional_subsumption,
% 3.84/1.00                [status(thm)],
% 3.84/1.00                [c_160,c_13,c_12]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_308,plain,
% 3.84/1.00      ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = sK1 ),
% 3.84/1.00      inference(subtyping,[status(esa)],[c_162]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_2204,plain,
% 3.84/1.00      ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1))) = sK1 ),
% 3.84/1.00      inference(light_normalisation,[status(thm)],[c_2192,c_308]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_7342,plain,
% 3.84/1.00      ( k2_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,k1_tops_1(sK0,sK1))) = sK1 ),
% 3.84/1.00      inference(light_normalisation,[status(thm)],[c_7330,c_2204]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_1,plain,
% 3.84/1.00      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 3.84/1.00      inference(cnf_transformation,[],[f31]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_313,plain,
% 3.84/1.00      ( r1_tarski(k4_xboole_0(X0_42,X1_42),X0_42) ),
% 3.84/1.00      inference(subtyping,[status(esa)],[c_1]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_1744,plain,
% 3.84/1.00      ( r1_tarski(k4_xboole_0(X0_42,X1_42),X0_42) = iProver_top ),
% 3.84/1.00      inference(predicate_to_equality,[status(thm)],[c_313]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_9,plain,
% 3.84/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.84/1.00      | r1_tarski(k2_tops_1(X1,k2_pre_topc(X1,X0)),k2_tops_1(X1,X0))
% 3.84/1.00      | ~ l1_pre_topc(X1) ),
% 3.84/1.00      inference(cnf_transformation,[],[f39]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_168,plain,
% 3.84/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.84/1.00      | r1_tarski(k2_tops_1(X1,k2_pre_topc(X1,X0)),k2_tops_1(X1,X0))
% 3.84/1.00      | sK0 != X1 ),
% 3.84/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_13]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_169,plain,
% 3.84/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.84/1.00      | r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,X0)),k2_tops_1(sK0,X0)) ),
% 3.84/1.00      inference(unflattening,[status(thm)],[c_168]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_307,plain,
% 3.84/1.00      ( ~ m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.84/1.00      | r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,X0_42)),k2_tops_1(sK0,X0_42)) ),
% 3.84/1.00      inference(subtyping,[status(esa)],[c_169]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_1747,plain,
% 3.84/1.00      ( m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.84/1.00      | r1_tarski(k2_tops_1(sK0,k2_pre_topc(sK0,X0_42)),k2_tops_1(sK0,X0_42)) = iProver_top ),
% 3.84/1.00      inference(predicate_to_equality,[status(thm)],[c_307]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_0,plain,
% 3.84/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X2,X0) | r1_tarski(X2,X1) ),
% 3.84/1.00      inference(cnf_transformation,[],[f30]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_314,plain,
% 3.84/1.00      ( ~ r1_tarski(X0_42,X1_42)
% 3.84/1.00      | ~ r1_tarski(X2_42,X0_42)
% 3.84/1.00      | r1_tarski(X2_42,X1_42) ),
% 3.84/1.00      inference(subtyping,[status(esa)],[c_0]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_1743,plain,
% 3.84/1.00      ( r1_tarski(X0_42,X1_42) != iProver_top
% 3.84/1.00      | r1_tarski(X2_42,X0_42) != iProver_top
% 3.84/1.00      | r1_tarski(X2_42,X1_42) = iProver_top ),
% 3.84/1.00      inference(predicate_to_equality,[status(thm)],[c_314]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_1908,plain,
% 3.84/1.00      ( m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.84/1.00      | r1_tarski(X1_42,k2_tops_1(sK0,X0_42)) = iProver_top
% 3.84/1.00      | r1_tarski(X1_42,k2_tops_1(sK0,k2_pre_topc(sK0,X0_42))) != iProver_top ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_1747,c_1743]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_2477,plain,
% 3.84/1.00      ( m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.84/1.00      | r1_tarski(k4_xboole_0(k2_tops_1(sK0,k2_pre_topc(sK0,X0_42)),X1_42),k2_tops_1(sK0,X0_42)) = iProver_top ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_1744,c_1908]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_4754,plain,
% 3.84/1.00      ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.84/1.00      | r1_tarski(k4_xboole_0(k2_tops_1(sK0,sK1),X0_42),k2_tops_1(sK0,k1_tops_1(sK0,sK1))) = iProver_top ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_308,c_2477]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_15,plain,
% 3.84/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.84/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_353,plain,
% 3.84/1.00      ( m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.84/1.00      | m1_subset_1(k1_tops_1(sK0,X0_42),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.84/1.00      inference(predicate_to_equality,[status(thm)],[c_304]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_355,plain,
% 3.84/1.00      ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 3.84/1.00      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.84/1.00      inference(instantiation,[status(thm)],[c_353]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_4890,plain,
% 3.84/1.00      ( r1_tarski(k4_xboole_0(k2_tops_1(sK0,sK1),X0_42),k2_tops_1(sK0,k1_tops_1(sK0,sK1))) = iProver_top ),
% 3.84/1.00      inference(global_propositional_subsumption,
% 3.84/1.00                [status(thm)],
% 3.84/1.00                [c_4754,c_15,c_355]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_2,plain,
% 3.84/1.00      ( r1_tarski(X0,k2_xboole_0(X1,X2))
% 3.84/1.00      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ),
% 3.84/1.00      inference(cnf_transformation,[],[f32]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_312,plain,
% 3.84/1.00      ( r1_tarski(X0_42,k2_xboole_0(X1_42,X2_42))
% 3.84/1.00      | ~ r1_tarski(k4_xboole_0(X0_42,X1_42),X2_42) ),
% 3.84/1.00      inference(subtyping,[status(esa)],[c_2]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_1745,plain,
% 3.84/1.00      ( r1_tarski(X0_42,k2_xboole_0(X1_42,X2_42)) = iProver_top
% 3.84/1.00      | r1_tarski(k4_xboole_0(X0_42,X1_42),X2_42) != iProver_top ),
% 3.84/1.00      inference(predicate_to_equality,[status(thm)],[c_312]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_4897,plain,
% 3.84/1.00      ( r1_tarski(k2_tops_1(sK0,sK1),k2_xboole_0(X0_42,k2_tops_1(sK0,k1_tops_1(sK0,sK1)))) = iProver_top ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_4890,c_1745]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_7383,plain,
% 3.84/1.00      ( r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_7342,c_4897]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_10,negated_conjecture,
% 3.84/1.00      ( ~ r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
% 3.84/1.00      inference(cnf_transformation,[],[f43]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_310,negated_conjecture,
% 3.84/1.00      ( ~ r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
% 3.84/1.00      inference(subtyping,[status(esa)],[c_10]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_1752,plain,
% 3.84/1.00      ( r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != iProver_top ),
% 3.84/1.00      inference(predicate_to_equality,[status(thm)],[c_310]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_1762,plain,
% 3.84/1.00      ( r1_tarski(k2_tops_1(sK0,sK1),sK1) != iProver_top ),
% 3.84/1.00      inference(light_normalisation,[status(thm)],[c_1752,c_308]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(contradiction,plain,
% 3.84/1.00      ( $false ),
% 3.84/1.00      inference(minisat,[status(thm)],[c_7383,c_1762]) ).
% 3.84/1.00  
% 3.84/1.00  
% 3.84/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.84/1.00  
% 3.84/1.00  ------                               Statistics
% 3.84/1.00  
% 3.84/1.00  ------ Selected
% 3.84/1.00  
% 3.84/1.00  total_time:                             0.379
% 3.84/1.00  
%------------------------------------------------------------------------------
