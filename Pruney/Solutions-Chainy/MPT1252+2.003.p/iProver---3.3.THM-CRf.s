%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:14:06 EST 2020

% Result     : Theorem 7.57s
% Output     : CNFRefutation 7.57s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 715 expanded)
%              Number of clauses        :   86 ( 254 expanded)
%              Number of leaves         :   14 ( 174 expanded)
%              Depth                    :   20
%              Number of atoms          :  353 (2051 expanded)
%              Number of equality atoms :  132 ( 281 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k2_tops_1(X0,k2_tops_1(X0,X1)),k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => r1_tarski(k2_tops_1(X0,k2_tops_1(X0,X1)),k2_tops_1(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(X0,k2_tops_1(X0,X1)),k2_tops_1(X0,X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(X0,k2_tops_1(X0,X1)),k2_tops_1(X0,X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_tarski(k2_tops_1(X0,k2_tops_1(X0,sK1)),k2_tops_1(X0,sK1))
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k2_tops_1(X0,k2_tops_1(X0,X1)),k2_tops_1(X0,X1))
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,X1)),k2_tops_1(sK0,X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f32,f31])).

fof(f49,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f33])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f48,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_tarski(X1,X2)
              | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
            & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | ~ r1_tarski(X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f28])).

fof(f36,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k2_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k2_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k2_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2)))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f50,plain,(
    ~ r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_659,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_16,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_201,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_16])).

cnf(c_202,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_201])).

cnf(c_657,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_202])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_189,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_16])).

cnf(c_190,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_189])).

cnf(c_658,plain,
    ( k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_190])).

cnf(c_1090,plain,
    ( k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,X0),k2_tops_1(sK0,k2_tops_1(sK0,X0))) = k2_pre_topc(sK0,k2_tops_1(sK0,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_657,c_658])).

cnf(c_2703,plain,
    ( k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k2_pre_topc(sK0,k2_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_659,c_1090])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | r1_tarski(k3_subset_1(X1,k4_subset_1(X1,X0,X2)),k3_subset_1(X1,X0)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_662,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(k3_subset_1(X1,k4_subset_1(X1,X0,X2)),k3_subset_1(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2715,plain,
    ( m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1))),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2703,c_662])).

cnf(c_18,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_701,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_202])).

cnf(c_702,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_701])).

cnf(c_755,plain,
    ( m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_202])).

cnf(c_756,plain,
    ( m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_755])).

cnf(c_18730,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1))),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2715,c_18,c_702,c_756])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | r1_tarski(X0,X2)
    | ~ r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X0)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_664,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X2) = iProver_top
    | r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_18736,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k2_tops_1(sK0,sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_18730,c_664])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_252,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_16])).

cnf(c_253,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_252])).

cnf(c_754,plain,
    ( ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_253])).

cnf(c_758,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_754])).

cnf(c_2268,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k4_subset_1(X1,X0,X2),k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,k4_subset_1(X1,X0,X2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_662,c_664])).

cnf(c_4660,plain,
    ( m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_tops_1(sK0,sK1),k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_tops_1(sK0,k2_tops_1(sK0,sK1)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2703,c_2268])).

cnf(c_4671,plain,
    ( m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k2_tops_1(sK0,sK1))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4660,c_2703])).

cnf(c_19069,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k2_tops_1(sK0,sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_18736,c_18,c_702,c_756,c_758,c_4671])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_667,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_19073,plain,
    ( k2_pre_topc(sK0,k2_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | r1_tarski(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_19069,c_667])).

cnf(c_653,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_253])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_665,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k2_pre_topc(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_240,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,k2_pre_topc(X1,X0)) = k2_pre_topc(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_16])).

cnf(c_241,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k2_pre_topc(sK0,X0)) = k2_pre_topc(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_240])).

cnf(c_654,plain,
    ( k2_pre_topc(sK0,k2_pre_topc(sK0,X0)) = k2_pre_topc(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_241])).

cnf(c_1284,plain,
    ( k2_pre_topc(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_665,c_654])).

cnf(c_1885,plain,
    ( k2_pre_topc(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(superposition,[status(thm)],[c_659,c_1284])).

cnf(c_922,plain,
    ( k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_659,c_654])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X0,X2)),k9_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k2_pre_topc(X1,X2)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_225,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X0,X2)),k9_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k2_pre_topc(X1,X2)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_16])).

cnf(c_226,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k2_pre_topc(sK0,X1))) ),
    inference(unflattening,[status(thm)],[c_225])).

cnf(c_655,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k2_pre_topc(sK0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_226])).

cnf(c_1203,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X0)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_922,c_655])).

cnf(c_714,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_253])).

cnf(c_715,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_714])).

cnf(c_3115,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X0)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1203,c_18,c_715])).

cnf(c_3125,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1885,c_3115])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_213,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k9_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k2_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_16])).

cnf(c_214,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k2_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_213])).

cnf(c_656,plain,
    ( k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k2_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_214])).

cnf(c_1559,plain,
    ( k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_659,c_656])).

cnf(c_3128,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3125,c_1559])).

cnf(c_3303,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_653,c_3128])).

cnf(c_3306,plain,
    ( k2_pre_topc(sK0,k2_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k2_tops_1(sK0,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3303,c_667])).

cnf(c_3307,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k2_tops_1(sK0,sK1)))
    | k2_pre_topc(sK0,k2_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3306])).

cnf(c_4676,plain,
    ( ~ m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k2_tops_1(sK0,sK1))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4671])).

cnf(c_973,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_6741,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_973])).

cnf(c_19178,plain,
    ( k2_pre_topc(sK0,k2_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_19073,c_15,c_701,c_755,c_754,c_3307,c_4676,c_6741])).

cnf(c_1560,plain,
    ( k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,X0)),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,X0)))) = k2_tops_1(sK0,k2_tops_1(sK0,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_657,c_656])).

cnf(c_3859,plain,
    ( k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)))) = k2_tops_1(sK0,k2_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_659,c_1560])).

cnf(c_19187,plain,
    ( k9_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)))) = k2_tops_1(sK0,k2_tops_1(sK0,sK1)) ),
    inference(demodulation,[status(thm)],[c_19178,c_3859])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | r1_tarski(k3_subset_1(X1,X0),k3_subset_1(X1,k9_subset_1(X1,X0,X2))) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_661,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(k3_subset_1(X1,X0),k3_subset_1(X1,k9_subset_1(X1,X0,X2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_19334,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_19187,c_661])).

cnf(c_717,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_253])).

cnf(c_15451,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_717])).

cnf(c_15452,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15451])).

cnf(c_4643,plain,
    ( ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_973])).

cnf(c_4644,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4643])).

cnf(c_691,plain,
    ( ~ m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(X0))
    | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(X0))
    | r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1))
    | ~ r1_tarski(k3_subset_1(X0,k2_tops_1(sK0,sK1)),k3_subset_1(X0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_793,plain,
    ( ~ m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1))
    | ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)))) ),
    inference(instantiation,[status(thm)],[c_691])).

cnf(c_794,plain,
    ( m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) = iProver_top
    | r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_793])).

cnf(c_14,negated_conjecture,
    ( ~ r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_19,plain,
    ( r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_19334,c_15452,c_4644,c_794,c_756,c_702,c_19,c_18])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:22:59 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.57/1.48  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.57/1.48  
% 7.57/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.57/1.48  
% 7.57/1.48  ------  iProver source info
% 7.57/1.48  
% 7.57/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.57/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.57/1.48  git: non_committed_changes: false
% 7.57/1.48  git: last_make_outside_of_git: false
% 7.57/1.48  
% 7.57/1.48  ------ 
% 7.57/1.48  
% 7.57/1.48  ------ Input Options
% 7.57/1.48  
% 7.57/1.48  --out_options                           all
% 7.57/1.48  --tptp_safe_out                         true
% 7.57/1.48  --problem_path                          ""
% 7.57/1.48  --include_path                          ""
% 7.57/1.48  --clausifier                            res/vclausify_rel
% 7.57/1.48  --clausifier_options                    ""
% 7.57/1.48  --stdin                                 false
% 7.57/1.48  --stats_out                             all
% 7.57/1.48  
% 7.57/1.48  ------ General Options
% 7.57/1.48  
% 7.57/1.48  --fof                                   false
% 7.57/1.48  --time_out_real                         305.
% 7.57/1.48  --time_out_virtual                      -1.
% 7.57/1.48  --symbol_type_check                     false
% 7.57/1.48  --clausify_out                          false
% 7.57/1.48  --sig_cnt_out                           false
% 7.57/1.48  --trig_cnt_out                          false
% 7.57/1.48  --trig_cnt_out_tolerance                1.
% 7.57/1.48  --trig_cnt_out_sk_spl                   false
% 7.57/1.48  --abstr_cl_out                          false
% 7.57/1.48  
% 7.57/1.48  ------ Global Options
% 7.57/1.48  
% 7.57/1.48  --schedule                              default
% 7.57/1.48  --add_important_lit                     false
% 7.57/1.48  --prop_solver_per_cl                    1000
% 7.57/1.48  --min_unsat_core                        false
% 7.57/1.48  --soft_assumptions                      false
% 7.57/1.48  --soft_lemma_size                       3
% 7.57/1.48  --prop_impl_unit_size                   0
% 7.57/1.48  --prop_impl_unit                        []
% 7.57/1.48  --share_sel_clauses                     true
% 7.57/1.48  --reset_solvers                         false
% 7.57/1.48  --bc_imp_inh                            [conj_cone]
% 7.57/1.48  --conj_cone_tolerance                   3.
% 7.57/1.48  --extra_neg_conj                        none
% 7.57/1.48  --large_theory_mode                     true
% 7.57/1.48  --prolific_symb_bound                   200
% 7.57/1.48  --lt_threshold                          2000
% 7.57/1.48  --clause_weak_htbl                      true
% 7.57/1.48  --gc_record_bc_elim                     false
% 7.57/1.48  
% 7.57/1.48  ------ Preprocessing Options
% 7.57/1.48  
% 7.57/1.48  --preprocessing_flag                    true
% 7.57/1.48  --time_out_prep_mult                    0.1
% 7.57/1.48  --splitting_mode                        input
% 7.57/1.48  --splitting_grd                         true
% 7.57/1.48  --splitting_cvd                         false
% 7.57/1.48  --splitting_cvd_svl                     false
% 7.57/1.48  --splitting_nvd                         32
% 7.57/1.48  --sub_typing                            true
% 7.57/1.48  --prep_gs_sim                           true
% 7.57/1.48  --prep_unflatten                        true
% 7.57/1.48  --prep_res_sim                          true
% 7.57/1.48  --prep_upred                            true
% 7.57/1.48  --prep_sem_filter                       exhaustive
% 7.57/1.48  --prep_sem_filter_out                   false
% 7.57/1.48  --pred_elim                             true
% 7.57/1.48  --res_sim_input                         true
% 7.57/1.48  --eq_ax_congr_red                       true
% 7.57/1.48  --pure_diseq_elim                       true
% 7.57/1.48  --brand_transform                       false
% 7.57/1.48  --non_eq_to_eq                          false
% 7.57/1.48  --prep_def_merge                        true
% 7.57/1.48  --prep_def_merge_prop_impl              false
% 7.57/1.48  --prep_def_merge_mbd                    true
% 7.57/1.48  --prep_def_merge_tr_red                 false
% 7.57/1.48  --prep_def_merge_tr_cl                  false
% 7.57/1.48  --smt_preprocessing                     true
% 7.57/1.48  --smt_ac_axioms                         fast
% 7.57/1.48  --preprocessed_out                      false
% 7.57/1.48  --preprocessed_stats                    false
% 7.57/1.48  
% 7.57/1.48  ------ Abstraction refinement Options
% 7.57/1.48  
% 7.57/1.48  --abstr_ref                             []
% 7.57/1.48  --abstr_ref_prep                        false
% 7.57/1.48  --abstr_ref_until_sat                   false
% 7.57/1.48  --abstr_ref_sig_restrict                funpre
% 7.57/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.57/1.48  --abstr_ref_under                       []
% 7.57/1.48  
% 7.57/1.48  ------ SAT Options
% 7.57/1.48  
% 7.57/1.48  --sat_mode                              false
% 7.57/1.48  --sat_fm_restart_options                ""
% 7.57/1.48  --sat_gr_def                            false
% 7.57/1.48  --sat_epr_types                         true
% 7.57/1.48  --sat_non_cyclic_types                  false
% 7.57/1.48  --sat_finite_models                     false
% 7.57/1.48  --sat_fm_lemmas                         false
% 7.57/1.48  --sat_fm_prep                           false
% 7.57/1.48  --sat_fm_uc_incr                        true
% 7.57/1.48  --sat_out_model                         small
% 7.57/1.48  --sat_out_clauses                       false
% 7.57/1.48  
% 7.57/1.48  ------ QBF Options
% 7.57/1.48  
% 7.57/1.48  --qbf_mode                              false
% 7.57/1.48  --qbf_elim_univ                         false
% 7.57/1.48  --qbf_dom_inst                          none
% 7.57/1.48  --qbf_dom_pre_inst                      false
% 7.57/1.48  --qbf_sk_in                             false
% 7.57/1.48  --qbf_pred_elim                         true
% 7.57/1.48  --qbf_split                             512
% 7.57/1.48  
% 7.57/1.48  ------ BMC1 Options
% 7.57/1.48  
% 7.57/1.48  --bmc1_incremental                      false
% 7.57/1.48  --bmc1_axioms                           reachable_all
% 7.57/1.48  --bmc1_min_bound                        0
% 7.57/1.48  --bmc1_max_bound                        -1
% 7.57/1.48  --bmc1_max_bound_default                -1
% 7.57/1.48  --bmc1_symbol_reachability              true
% 7.57/1.48  --bmc1_property_lemmas                  false
% 7.57/1.48  --bmc1_k_induction                      false
% 7.57/1.48  --bmc1_non_equiv_states                 false
% 7.57/1.48  --bmc1_deadlock                         false
% 7.57/1.48  --bmc1_ucm                              false
% 7.57/1.48  --bmc1_add_unsat_core                   none
% 7.57/1.48  --bmc1_unsat_core_children              false
% 7.57/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.57/1.48  --bmc1_out_stat                         full
% 7.57/1.48  --bmc1_ground_init                      false
% 7.57/1.48  --bmc1_pre_inst_next_state              false
% 7.57/1.48  --bmc1_pre_inst_state                   false
% 7.57/1.48  --bmc1_pre_inst_reach_state             false
% 7.57/1.48  --bmc1_out_unsat_core                   false
% 7.57/1.48  --bmc1_aig_witness_out                  false
% 7.57/1.48  --bmc1_verbose                          false
% 7.57/1.48  --bmc1_dump_clauses_tptp                false
% 7.57/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.57/1.48  --bmc1_dump_file                        -
% 7.57/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.57/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.57/1.48  --bmc1_ucm_extend_mode                  1
% 7.57/1.48  --bmc1_ucm_init_mode                    2
% 7.57/1.48  --bmc1_ucm_cone_mode                    none
% 7.57/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.57/1.48  --bmc1_ucm_relax_model                  4
% 7.57/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.57/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.57/1.48  --bmc1_ucm_layered_model                none
% 7.57/1.48  --bmc1_ucm_max_lemma_size               10
% 7.57/1.48  
% 7.57/1.48  ------ AIG Options
% 7.57/1.48  
% 7.57/1.48  --aig_mode                              false
% 7.57/1.48  
% 7.57/1.48  ------ Instantiation Options
% 7.57/1.48  
% 7.57/1.48  --instantiation_flag                    true
% 7.57/1.48  --inst_sos_flag                         true
% 7.57/1.48  --inst_sos_phase                        true
% 7.57/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.57/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.57/1.48  --inst_lit_sel_side                     num_symb
% 7.57/1.48  --inst_solver_per_active                1400
% 7.57/1.48  --inst_solver_calls_frac                1.
% 7.57/1.48  --inst_passive_queue_type               priority_queues
% 7.57/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.57/1.48  --inst_passive_queues_freq              [25;2]
% 7.57/1.48  --inst_dismatching                      true
% 7.57/1.48  --inst_eager_unprocessed_to_passive     true
% 7.57/1.48  --inst_prop_sim_given                   true
% 7.57/1.48  --inst_prop_sim_new                     false
% 7.57/1.48  --inst_subs_new                         false
% 7.57/1.48  --inst_eq_res_simp                      false
% 7.57/1.48  --inst_subs_given                       false
% 7.57/1.48  --inst_orphan_elimination               true
% 7.57/1.48  --inst_learning_loop_flag               true
% 7.57/1.48  --inst_learning_start                   3000
% 7.57/1.48  --inst_learning_factor                  2
% 7.57/1.48  --inst_start_prop_sim_after_learn       3
% 7.57/1.48  --inst_sel_renew                        solver
% 7.57/1.48  --inst_lit_activity_flag                true
% 7.57/1.48  --inst_restr_to_given                   false
% 7.57/1.48  --inst_activity_threshold               500
% 7.57/1.48  --inst_out_proof                        true
% 7.57/1.48  
% 7.57/1.48  ------ Resolution Options
% 7.57/1.48  
% 7.57/1.48  --resolution_flag                       true
% 7.57/1.48  --res_lit_sel                           adaptive
% 7.57/1.48  --res_lit_sel_side                      none
% 7.57/1.48  --res_ordering                          kbo
% 7.57/1.48  --res_to_prop_solver                    active
% 7.57/1.48  --res_prop_simpl_new                    false
% 7.57/1.48  --res_prop_simpl_given                  true
% 7.57/1.48  --res_passive_queue_type                priority_queues
% 7.57/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.57/1.48  --res_passive_queues_freq               [15;5]
% 7.57/1.48  --res_forward_subs                      full
% 7.57/1.48  --res_backward_subs                     full
% 7.57/1.48  --res_forward_subs_resolution           true
% 7.57/1.48  --res_backward_subs_resolution          true
% 7.57/1.48  --res_orphan_elimination                true
% 7.57/1.48  --res_time_limit                        2.
% 7.57/1.48  --res_out_proof                         true
% 7.57/1.48  
% 7.57/1.48  ------ Superposition Options
% 7.57/1.48  
% 7.57/1.48  --superposition_flag                    true
% 7.57/1.48  --sup_passive_queue_type                priority_queues
% 7.57/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.57/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.57/1.48  --demod_completeness_check              fast
% 7.57/1.48  --demod_use_ground                      true
% 7.57/1.48  --sup_to_prop_solver                    passive
% 7.57/1.48  --sup_prop_simpl_new                    true
% 7.57/1.48  --sup_prop_simpl_given                  true
% 7.57/1.48  --sup_fun_splitting                     true
% 7.57/1.48  --sup_smt_interval                      50000
% 7.57/1.48  
% 7.57/1.48  ------ Superposition Simplification Setup
% 7.57/1.48  
% 7.57/1.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.57/1.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.57/1.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.57/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.57/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.57/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.57/1.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.57/1.48  --sup_immed_triv                        [TrivRules]
% 7.57/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.57/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.57/1.48  --sup_immed_bw_main                     []
% 7.57/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.57/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.57/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.57/1.48  --sup_input_bw                          []
% 7.57/1.48  
% 7.57/1.48  ------ Combination Options
% 7.57/1.48  
% 7.57/1.48  --comb_res_mult                         3
% 7.57/1.48  --comb_sup_mult                         2
% 7.57/1.48  --comb_inst_mult                        10
% 7.57/1.48  
% 7.57/1.48  ------ Debug Options
% 7.57/1.48  
% 7.57/1.48  --dbg_backtrace                         false
% 7.57/1.48  --dbg_dump_prop_clauses                 false
% 7.57/1.48  --dbg_dump_prop_clauses_file            -
% 7.57/1.48  --dbg_out_stat                          false
% 7.57/1.48  ------ Parsing...
% 7.57/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.57/1.48  
% 7.57/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.57/1.48  
% 7.57/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.57/1.48  
% 7.57/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.57/1.48  ------ Proving...
% 7.57/1.48  ------ Problem Properties 
% 7.57/1.48  
% 7.57/1.48  
% 7.57/1.48  clauses                                 15
% 7.57/1.48  conjectures                             2
% 7.57/1.48  EPR                                     2
% 7.57/1.48  Horn                                    15
% 7.57/1.48  unary                                   3
% 7.57/1.48  binary                                  6
% 7.57/1.48  lits                                    35
% 7.57/1.48  lits eq                                 4
% 7.57/1.48  fd_pure                                 0
% 7.57/1.48  fd_pseudo                               0
% 7.57/1.48  fd_cond                                 0
% 7.57/1.48  fd_pseudo_cond                          1
% 7.57/1.48  AC symbols                              0
% 7.57/1.48  
% 7.57/1.48  ------ Schedule dynamic 5 is on 
% 7.57/1.48  
% 7.57/1.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.57/1.48  
% 7.57/1.48  
% 7.57/1.48  ------ 
% 7.57/1.48  Current options:
% 7.57/1.48  ------ 
% 7.57/1.48  
% 7.57/1.48  ------ Input Options
% 7.57/1.48  
% 7.57/1.48  --out_options                           all
% 7.57/1.48  --tptp_safe_out                         true
% 7.57/1.48  --problem_path                          ""
% 7.57/1.48  --include_path                          ""
% 7.57/1.48  --clausifier                            res/vclausify_rel
% 7.57/1.48  --clausifier_options                    ""
% 7.57/1.48  --stdin                                 false
% 7.57/1.48  --stats_out                             all
% 7.57/1.48  
% 7.57/1.48  ------ General Options
% 7.57/1.48  
% 7.57/1.48  --fof                                   false
% 7.57/1.48  --time_out_real                         305.
% 7.57/1.48  --time_out_virtual                      -1.
% 7.57/1.48  --symbol_type_check                     false
% 7.57/1.48  --clausify_out                          false
% 7.57/1.48  --sig_cnt_out                           false
% 7.57/1.48  --trig_cnt_out                          false
% 7.57/1.48  --trig_cnt_out_tolerance                1.
% 7.57/1.48  --trig_cnt_out_sk_spl                   false
% 7.57/1.48  --abstr_cl_out                          false
% 7.57/1.48  
% 7.57/1.48  ------ Global Options
% 7.57/1.48  
% 7.57/1.48  --schedule                              default
% 7.57/1.48  --add_important_lit                     false
% 7.57/1.48  --prop_solver_per_cl                    1000
% 7.57/1.48  --min_unsat_core                        false
% 7.57/1.48  --soft_assumptions                      false
% 7.57/1.48  --soft_lemma_size                       3
% 7.57/1.48  --prop_impl_unit_size                   0
% 7.57/1.48  --prop_impl_unit                        []
% 7.57/1.48  --share_sel_clauses                     true
% 7.57/1.48  --reset_solvers                         false
% 7.57/1.48  --bc_imp_inh                            [conj_cone]
% 7.57/1.48  --conj_cone_tolerance                   3.
% 7.57/1.48  --extra_neg_conj                        none
% 7.57/1.48  --large_theory_mode                     true
% 7.57/1.48  --prolific_symb_bound                   200
% 7.57/1.48  --lt_threshold                          2000
% 7.57/1.48  --clause_weak_htbl                      true
% 7.57/1.48  --gc_record_bc_elim                     false
% 7.57/1.48  
% 7.57/1.48  ------ Preprocessing Options
% 7.57/1.48  
% 7.57/1.48  --preprocessing_flag                    true
% 7.57/1.48  --time_out_prep_mult                    0.1
% 7.57/1.48  --splitting_mode                        input
% 7.57/1.48  --splitting_grd                         true
% 7.57/1.48  --splitting_cvd                         false
% 7.57/1.48  --splitting_cvd_svl                     false
% 7.57/1.48  --splitting_nvd                         32
% 7.57/1.48  --sub_typing                            true
% 7.57/1.48  --prep_gs_sim                           true
% 7.57/1.48  --prep_unflatten                        true
% 7.57/1.48  --prep_res_sim                          true
% 7.57/1.48  --prep_upred                            true
% 7.57/1.48  --prep_sem_filter                       exhaustive
% 7.57/1.48  --prep_sem_filter_out                   false
% 7.57/1.48  --pred_elim                             true
% 7.57/1.48  --res_sim_input                         true
% 7.57/1.48  --eq_ax_congr_red                       true
% 7.57/1.48  --pure_diseq_elim                       true
% 7.57/1.48  --brand_transform                       false
% 7.57/1.48  --non_eq_to_eq                          false
% 7.57/1.48  --prep_def_merge                        true
% 7.57/1.48  --prep_def_merge_prop_impl              false
% 7.57/1.48  --prep_def_merge_mbd                    true
% 7.57/1.48  --prep_def_merge_tr_red                 false
% 7.57/1.48  --prep_def_merge_tr_cl                  false
% 7.57/1.48  --smt_preprocessing                     true
% 7.57/1.48  --smt_ac_axioms                         fast
% 7.57/1.48  --preprocessed_out                      false
% 7.57/1.48  --preprocessed_stats                    false
% 7.57/1.48  
% 7.57/1.48  ------ Abstraction refinement Options
% 7.57/1.48  
% 7.57/1.48  --abstr_ref                             []
% 7.57/1.48  --abstr_ref_prep                        false
% 7.57/1.48  --abstr_ref_until_sat                   false
% 7.57/1.48  --abstr_ref_sig_restrict                funpre
% 7.57/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.57/1.48  --abstr_ref_under                       []
% 7.57/1.48  
% 7.57/1.48  ------ SAT Options
% 7.57/1.48  
% 7.57/1.48  --sat_mode                              false
% 7.57/1.48  --sat_fm_restart_options                ""
% 7.57/1.48  --sat_gr_def                            false
% 7.57/1.48  --sat_epr_types                         true
% 7.57/1.48  --sat_non_cyclic_types                  false
% 7.57/1.48  --sat_finite_models                     false
% 7.57/1.48  --sat_fm_lemmas                         false
% 7.57/1.48  --sat_fm_prep                           false
% 7.57/1.48  --sat_fm_uc_incr                        true
% 7.57/1.48  --sat_out_model                         small
% 7.57/1.48  --sat_out_clauses                       false
% 7.57/1.48  
% 7.57/1.48  ------ QBF Options
% 7.57/1.48  
% 7.57/1.48  --qbf_mode                              false
% 7.57/1.48  --qbf_elim_univ                         false
% 7.57/1.48  --qbf_dom_inst                          none
% 7.57/1.48  --qbf_dom_pre_inst                      false
% 7.57/1.48  --qbf_sk_in                             false
% 7.57/1.48  --qbf_pred_elim                         true
% 7.57/1.48  --qbf_split                             512
% 7.57/1.48  
% 7.57/1.48  ------ BMC1 Options
% 7.57/1.48  
% 7.57/1.48  --bmc1_incremental                      false
% 7.57/1.48  --bmc1_axioms                           reachable_all
% 7.57/1.48  --bmc1_min_bound                        0
% 7.57/1.48  --bmc1_max_bound                        -1
% 7.57/1.48  --bmc1_max_bound_default                -1
% 7.57/1.48  --bmc1_symbol_reachability              true
% 7.57/1.48  --bmc1_property_lemmas                  false
% 7.57/1.48  --bmc1_k_induction                      false
% 7.57/1.48  --bmc1_non_equiv_states                 false
% 7.57/1.48  --bmc1_deadlock                         false
% 7.57/1.48  --bmc1_ucm                              false
% 7.57/1.48  --bmc1_add_unsat_core                   none
% 7.57/1.48  --bmc1_unsat_core_children              false
% 7.57/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.57/1.48  --bmc1_out_stat                         full
% 7.57/1.48  --bmc1_ground_init                      false
% 7.57/1.48  --bmc1_pre_inst_next_state              false
% 7.57/1.48  --bmc1_pre_inst_state                   false
% 7.57/1.48  --bmc1_pre_inst_reach_state             false
% 7.57/1.48  --bmc1_out_unsat_core                   false
% 7.57/1.48  --bmc1_aig_witness_out                  false
% 7.57/1.48  --bmc1_verbose                          false
% 7.57/1.48  --bmc1_dump_clauses_tptp                false
% 7.57/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.57/1.48  --bmc1_dump_file                        -
% 7.57/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.57/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.57/1.48  --bmc1_ucm_extend_mode                  1
% 7.57/1.48  --bmc1_ucm_init_mode                    2
% 7.57/1.48  --bmc1_ucm_cone_mode                    none
% 7.57/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.57/1.48  --bmc1_ucm_relax_model                  4
% 7.57/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.57/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.57/1.48  --bmc1_ucm_layered_model                none
% 7.57/1.48  --bmc1_ucm_max_lemma_size               10
% 7.57/1.48  
% 7.57/1.48  ------ AIG Options
% 7.57/1.48  
% 7.57/1.48  --aig_mode                              false
% 7.57/1.48  
% 7.57/1.48  ------ Instantiation Options
% 7.57/1.48  
% 7.57/1.48  --instantiation_flag                    true
% 7.57/1.48  --inst_sos_flag                         true
% 7.57/1.48  --inst_sos_phase                        true
% 7.57/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.57/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.57/1.48  --inst_lit_sel_side                     none
% 7.57/1.48  --inst_solver_per_active                1400
% 7.57/1.48  --inst_solver_calls_frac                1.
% 7.57/1.48  --inst_passive_queue_type               priority_queues
% 7.57/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.57/1.48  --inst_passive_queues_freq              [25;2]
% 7.57/1.48  --inst_dismatching                      true
% 7.57/1.48  --inst_eager_unprocessed_to_passive     true
% 7.57/1.48  --inst_prop_sim_given                   true
% 7.57/1.48  --inst_prop_sim_new                     false
% 7.57/1.48  --inst_subs_new                         false
% 7.57/1.48  --inst_eq_res_simp                      false
% 7.57/1.48  --inst_subs_given                       false
% 7.57/1.48  --inst_orphan_elimination               true
% 7.57/1.48  --inst_learning_loop_flag               true
% 7.57/1.48  --inst_learning_start                   3000
% 7.57/1.48  --inst_learning_factor                  2
% 7.57/1.48  --inst_start_prop_sim_after_learn       3
% 7.57/1.48  --inst_sel_renew                        solver
% 7.57/1.48  --inst_lit_activity_flag                true
% 7.57/1.48  --inst_restr_to_given                   false
% 7.57/1.48  --inst_activity_threshold               500
% 7.57/1.48  --inst_out_proof                        true
% 7.57/1.48  
% 7.57/1.48  ------ Resolution Options
% 7.57/1.48  
% 7.57/1.48  --resolution_flag                       false
% 7.57/1.48  --res_lit_sel                           adaptive
% 7.57/1.48  --res_lit_sel_side                      none
% 7.57/1.48  --res_ordering                          kbo
% 7.57/1.48  --res_to_prop_solver                    active
% 7.57/1.48  --res_prop_simpl_new                    false
% 7.57/1.48  --res_prop_simpl_given                  true
% 7.57/1.48  --res_passive_queue_type                priority_queues
% 7.57/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.57/1.48  --res_passive_queues_freq               [15;5]
% 7.57/1.48  --res_forward_subs                      full
% 7.57/1.48  --res_backward_subs                     full
% 7.57/1.48  --res_forward_subs_resolution           true
% 7.57/1.48  --res_backward_subs_resolution          true
% 7.57/1.48  --res_orphan_elimination                true
% 7.57/1.48  --res_time_limit                        2.
% 7.57/1.48  --res_out_proof                         true
% 7.57/1.48  
% 7.57/1.48  ------ Superposition Options
% 7.57/1.48  
% 7.57/1.48  --superposition_flag                    true
% 7.57/1.48  --sup_passive_queue_type                priority_queues
% 7.57/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.57/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.57/1.48  --demod_completeness_check              fast
% 7.57/1.48  --demod_use_ground                      true
% 7.57/1.48  --sup_to_prop_solver                    passive
% 7.57/1.48  --sup_prop_simpl_new                    true
% 7.57/1.48  --sup_prop_simpl_given                  true
% 7.57/1.48  --sup_fun_splitting                     true
% 7.57/1.48  --sup_smt_interval                      50000
% 7.57/1.48  
% 7.57/1.48  ------ Superposition Simplification Setup
% 7.57/1.48  
% 7.57/1.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.57/1.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.57/1.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.57/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.57/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.57/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.57/1.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.57/1.48  --sup_immed_triv                        [TrivRules]
% 7.57/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.57/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.57/1.48  --sup_immed_bw_main                     []
% 7.57/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.57/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.57/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.57/1.48  --sup_input_bw                          []
% 7.57/1.48  
% 7.57/1.48  ------ Combination Options
% 7.57/1.48  
% 7.57/1.48  --comb_res_mult                         3
% 7.57/1.48  --comb_sup_mult                         2
% 7.57/1.48  --comb_inst_mult                        10
% 7.57/1.48  
% 7.57/1.48  ------ Debug Options
% 7.57/1.48  
% 7.57/1.48  --dbg_backtrace                         false
% 7.57/1.48  --dbg_dump_prop_clauses                 false
% 7.57/1.48  --dbg_dump_prop_clauses_file            -
% 7.57/1.48  --dbg_out_stat                          false
% 7.57/1.48  
% 7.57/1.48  
% 7.57/1.48  
% 7.57/1.48  
% 7.57/1.48  ------ Proving...
% 7.57/1.48  
% 7.57/1.48  
% 7.57/1.48  % SZS status Theorem for theBenchmark.p
% 7.57/1.48  
% 7.57/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.57/1.48  
% 7.57/1.48  fof(f12,conjecture,(
% 7.57/1.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k2_tops_1(X0,k2_tops_1(X0,X1)),k2_tops_1(X0,X1))))),
% 7.57/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.57/1.48  
% 7.57/1.48  fof(f13,negated_conjecture,(
% 7.57/1.48    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k2_tops_1(X0,k2_tops_1(X0,X1)),k2_tops_1(X0,X1))))),
% 7.57/1.48    inference(negated_conjecture,[],[f12])).
% 7.57/1.48  
% 7.57/1.48  fof(f27,plain,(
% 7.57/1.48    ? [X0] : (? [X1] : (~r1_tarski(k2_tops_1(X0,k2_tops_1(X0,X1)),k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 7.57/1.48    inference(ennf_transformation,[],[f13])).
% 7.57/1.48  
% 7.57/1.48  fof(f32,plain,(
% 7.57/1.48    ( ! [X0] : (? [X1] : (~r1_tarski(k2_tops_1(X0,k2_tops_1(X0,X1)),k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~r1_tarski(k2_tops_1(X0,k2_tops_1(X0,sK1)),k2_tops_1(X0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 7.57/1.48    introduced(choice_axiom,[])).
% 7.57/1.48  
% 7.57/1.48  fof(f31,plain,(
% 7.57/1.48    ? [X0] : (? [X1] : (~r1_tarski(k2_tops_1(X0,k2_tops_1(X0,X1)),k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (~r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,X1)),k2_tops_1(sK0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 7.57/1.48    introduced(choice_axiom,[])).
% 7.57/1.48  
% 7.57/1.48  fof(f33,plain,(
% 7.57/1.48    (~r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 7.57/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f32,f31])).
% 7.57/1.48  
% 7.57/1.48  fof(f49,plain,(
% 7.57/1.48    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 7.57/1.48    inference(cnf_transformation,[],[f33])).
% 7.57/1.48  
% 7.57/1.48  fof(f10,axiom,(
% 7.57/1.48    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 7.57/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.57/1.48  
% 7.57/1.48  fof(f24,plain,(
% 7.57/1.48    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 7.57/1.48    inference(ennf_transformation,[],[f10])).
% 7.57/1.48  
% 7.57/1.48  fof(f25,plain,(
% 7.57/1.48    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 7.57/1.48    inference(flattening,[],[f24])).
% 7.57/1.48  
% 7.57/1.48  fof(f46,plain,(
% 7.57/1.48    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.57/1.48    inference(cnf_transformation,[],[f25])).
% 7.57/1.48  
% 7.57/1.48  fof(f48,plain,(
% 7.57/1.48    l1_pre_topc(sK0)),
% 7.57/1.48    inference(cnf_transformation,[],[f33])).
% 7.57/1.48  
% 7.57/1.48  fof(f11,axiom,(
% 7.57/1.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)))),
% 7.57/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.57/1.48  
% 7.57/1.48  fof(f26,plain,(
% 7.57/1.48    ! [X0] : (! [X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.57/1.48    inference(ennf_transformation,[],[f11])).
% 7.57/1.48  
% 7.57/1.48  fof(f47,plain,(
% 7.57/1.48    ( ! [X0,X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.57/1.48    inference(cnf_transformation,[],[f26])).
% 7.57/1.48  
% 7.57/1.48  fof(f4,axiom,(
% 7.57/1.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))))),
% 7.57/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.57/1.48  
% 7.57/1.48  fof(f16,plain,(
% 7.57/1.48    ! [X0,X1] : (! [X2] : (r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.57/1.48    inference(ennf_transformation,[],[f4])).
% 7.57/1.48  
% 7.57/1.48  fof(f40,plain,(
% 7.57/1.48    ( ! [X2,X0,X1] : (r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.57/1.48    inference(cnf_transformation,[],[f16])).
% 7.57/1.48  
% 7.57/1.48  fof(f3,axiom,(
% 7.57/1.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 7.57/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.57/1.48  
% 7.57/1.48  fof(f15,plain,(
% 7.57/1.48    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.57/1.48    inference(ennf_transformation,[],[f3])).
% 7.57/1.48  
% 7.57/1.48  fof(f30,plain,(
% 7.57/1.48    ! [X0,X1] : (! [X2] : (((r1_tarski(X1,X2) | ~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.57/1.48    inference(nnf_transformation,[],[f15])).
% 7.57/1.48  
% 7.57/1.48  fof(f39,plain,(
% 7.57/1.48    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.57/1.48    inference(cnf_transformation,[],[f30])).
% 7.57/1.48  
% 7.57/1.48  fof(f6,axiom,(
% 7.57/1.48    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 7.57/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.57/1.48  
% 7.57/1.48  fof(f18,plain,(
% 7.57/1.48    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 7.57/1.48    inference(ennf_transformation,[],[f6])).
% 7.57/1.48  
% 7.57/1.48  fof(f19,plain,(
% 7.57/1.48    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 7.57/1.48    inference(flattening,[],[f18])).
% 7.57/1.48  
% 7.57/1.48  fof(f42,plain,(
% 7.57/1.48    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.57/1.48    inference(cnf_transformation,[],[f19])).
% 7.57/1.48  
% 7.57/1.48  fof(f1,axiom,(
% 7.57/1.48    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.57/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.57/1.48  
% 7.57/1.48  fof(f28,plain,(
% 7.57/1.48    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.57/1.48    inference(nnf_transformation,[],[f1])).
% 7.57/1.48  
% 7.57/1.48  fof(f29,plain,(
% 7.57/1.48    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.57/1.48    inference(flattening,[],[f28])).
% 7.57/1.48  
% 7.57/1.48  fof(f36,plain,(
% 7.57/1.48    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.57/1.48    inference(cnf_transformation,[],[f29])).
% 7.57/1.48  
% 7.57/1.48  fof(f2,axiom,(
% 7.57/1.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 7.57/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.57/1.48  
% 7.57/1.48  fof(f14,plain,(
% 7.57/1.48    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.57/1.48    inference(ennf_transformation,[],[f2])).
% 7.57/1.48  
% 7.57/1.48  fof(f37,plain,(
% 7.57/1.48    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.57/1.48    inference(cnf_transformation,[],[f14])).
% 7.57/1.48  
% 7.57/1.48  fof(f7,axiom,(
% 7.57/1.48    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)))),
% 7.57/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.57/1.48  
% 7.57/1.48  fof(f20,plain,(
% 7.57/1.48    ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 7.57/1.48    inference(ennf_transformation,[],[f7])).
% 7.57/1.48  
% 7.57/1.48  fof(f21,plain,(
% 7.57/1.48    ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 7.57/1.48    inference(flattening,[],[f20])).
% 7.57/1.48  
% 7.57/1.48  fof(f43,plain,(
% 7.57/1.48    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.57/1.48    inference(cnf_transformation,[],[f21])).
% 7.57/1.48  
% 7.57/1.48  fof(f8,axiom,(
% 7.57/1.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))))))),
% 7.57/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.57/1.48  
% 7.57/1.48  fof(f22,plain,(
% 7.57/1.48    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.57/1.48    inference(ennf_transformation,[],[f8])).
% 7.57/1.48  
% 7.57/1.48  fof(f44,plain,(
% 7.57/1.48    ( ! [X2,X0,X1] : (r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.57/1.48    inference(cnf_transformation,[],[f22])).
% 7.57/1.48  
% 7.57/1.48  fof(f9,axiom,(
% 7.57/1.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k2_tops_1(X0,X1)))),
% 7.57/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.57/1.48  
% 7.57/1.48  fof(f23,plain,(
% 7.57/1.48    ! [X0] : (! [X1] : (k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.57/1.48    inference(ennf_transformation,[],[f9])).
% 7.57/1.48  
% 7.57/1.48  fof(f45,plain,(
% 7.57/1.48    ( ! [X0,X1] : (k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.57/1.48    inference(cnf_transformation,[],[f23])).
% 7.57/1.48  
% 7.57/1.48  fof(f5,axiom,(
% 7.57/1.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2)))))),
% 7.57/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.57/1.48  
% 7.57/1.48  fof(f17,plain,(
% 7.57/1.48    ! [X0,X1] : (! [X2] : (r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.57/1.48    inference(ennf_transformation,[],[f5])).
% 7.57/1.48  
% 7.57/1.48  fof(f41,plain,(
% 7.57/1.48    ( ! [X2,X0,X1] : (r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.57/1.48    inference(cnf_transformation,[],[f17])).
% 7.57/1.48  
% 7.57/1.48  fof(f50,plain,(
% 7.57/1.48    ~r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1))),
% 7.57/1.48    inference(cnf_transformation,[],[f33])).
% 7.57/1.48  
% 7.57/1.48  cnf(c_15,negated_conjecture,
% 7.57/1.49      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.57/1.49      inference(cnf_transformation,[],[f49]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_659,plain,
% 7.57/1.49      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 7.57/1.49      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_12,plain,
% 7.57/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.57/1.49      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.57/1.49      | ~ l1_pre_topc(X1) ),
% 7.57/1.49      inference(cnf_transformation,[],[f46]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_16,negated_conjecture,
% 7.57/1.49      ( l1_pre_topc(sK0) ),
% 7.57/1.49      inference(cnf_transformation,[],[f48]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_201,plain,
% 7.57/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.57/1.49      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.57/1.49      | sK0 != X1 ),
% 7.57/1.49      inference(resolution_lifted,[status(thm)],[c_12,c_16]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_202,plain,
% 7.57/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.57/1.49      | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.57/1.49      inference(unflattening,[status(thm)],[c_201]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_657,plain,
% 7.57/1.49      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.57/1.49      | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 7.57/1.49      inference(predicate_to_equality,[status(thm)],[c_202]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_13,plain,
% 7.57/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.57/1.49      | ~ l1_pre_topc(X1)
% 7.57/1.49      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
% 7.57/1.49      inference(cnf_transformation,[],[f47]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_189,plain,
% 7.57/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.57/1.49      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0)
% 7.57/1.49      | sK0 != X1 ),
% 7.57/1.49      inference(resolution_lifted,[status(thm)],[c_13,c_16]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_190,plain,
% 7.57/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.57/1.49      | k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0) ),
% 7.57/1.49      inference(unflattening,[status(thm)],[c_189]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_658,plain,
% 7.57/1.49      ( k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0)
% 7.57/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.57/1.49      inference(predicate_to_equality,[status(thm)],[c_190]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_1090,plain,
% 7.57/1.49      ( k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,X0),k2_tops_1(sK0,k2_tops_1(sK0,X0))) = k2_pre_topc(sK0,k2_tops_1(sK0,X0))
% 7.57/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.57/1.49      inference(superposition,[status(thm)],[c_657,c_658]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_2703,plain,
% 7.57/1.49      ( k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k2_pre_topc(sK0,k2_tops_1(sK0,sK1)) ),
% 7.57/1.49      inference(superposition,[status(thm)],[c_659,c_1090]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_6,plain,
% 7.57/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.57/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 7.57/1.49      | r1_tarski(k3_subset_1(X1,k4_subset_1(X1,X0,X2)),k3_subset_1(X1,X0)) ),
% 7.57/1.49      inference(cnf_transformation,[],[f40]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_662,plain,
% 7.57/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.57/1.49      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 7.57/1.49      | r1_tarski(k3_subset_1(X1,k4_subset_1(X1,X0,X2)),k3_subset_1(X1,X0)) = iProver_top ),
% 7.57/1.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_2715,plain,
% 7.57/1.49      ( m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.57/1.49      | m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.57/1.49      | r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1))),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) = iProver_top ),
% 7.57/1.49      inference(superposition,[status(thm)],[c_2703,c_662]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_18,plain,
% 7.57/1.49      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 7.57/1.49      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_701,plain,
% 7.57/1.49      ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 7.57/1.49      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.57/1.49      inference(instantiation,[status(thm)],[c_202]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_702,plain,
% 7.57/1.49      ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 7.57/1.49      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.57/1.49      inference(predicate_to_equality,[status(thm)],[c_701]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_755,plain,
% 7.57/1.49      ( m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
% 7.57/1.49      | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.57/1.49      inference(instantiation,[status(thm)],[c_202]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_756,plain,
% 7.57/1.49      ( m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 7.57/1.49      | m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.57/1.49      inference(predicate_to_equality,[status(thm)],[c_755]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_18730,plain,
% 7.57/1.49      ( r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1))),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) = iProver_top ),
% 7.57/1.49      inference(global_propositional_subsumption,
% 7.57/1.49                [status(thm)],
% 7.57/1.49                [c_2715,c_18,c_702,c_756]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_4,plain,
% 7.57/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.57/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 7.57/1.49      | r1_tarski(X0,X2)
% 7.57/1.49      | ~ r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X0)) ),
% 7.57/1.49      inference(cnf_transformation,[],[f39]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_664,plain,
% 7.57/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.57/1.49      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 7.57/1.49      | r1_tarski(X0,X2) = iProver_top
% 7.57/1.49      | r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X0)) != iProver_top ),
% 7.57/1.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_18736,plain,
% 7.57/1.49      ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.57/1.49      | m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.57/1.49      | r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k2_tops_1(sK0,sK1))) = iProver_top ),
% 7.57/1.49      inference(superposition,[status(thm)],[c_18730,c_664]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_8,plain,
% 7.57/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.57/1.49      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.57/1.49      | ~ l1_pre_topc(X1) ),
% 7.57/1.49      inference(cnf_transformation,[],[f42]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_252,plain,
% 7.57/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.57/1.49      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.57/1.49      | sK0 != X1 ),
% 7.57/1.49      inference(resolution_lifted,[status(thm)],[c_8,c_16]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_253,plain,
% 7.57/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.57/1.49      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.57/1.49      inference(unflattening,[status(thm)],[c_252]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_754,plain,
% 7.57/1.49      ( ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 7.57/1.49      | m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.57/1.49      inference(instantiation,[status(thm)],[c_253]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_758,plain,
% 7.57/1.49      ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.57/1.49      | m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 7.57/1.49      inference(predicate_to_equality,[status(thm)],[c_754]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_2268,plain,
% 7.57/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.57/1.49      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 7.57/1.49      | m1_subset_1(k4_subset_1(X1,X0,X2),k1_zfmisc_1(X1)) != iProver_top
% 7.57/1.49      | r1_tarski(X0,k4_subset_1(X1,X0,X2)) = iProver_top ),
% 7.57/1.49      inference(superposition,[status(thm)],[c_662,c_664]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_4660,plain,
% 7.57/1.49      ( m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.57/1.49      | m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.57/1.49      | m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.57/1.49      | r1_tarski(k2_tops_1(sK0,sK1),k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_tops_1(sK0,k2_tops_1(sK0,sK1)))) = iProver_top ),
% 7.57/1.49      inference(superposition,[status(thm)],[c_2703,c_2268]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_4671,plain,
% 7.57/1.49      ( m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.57/1.49      | m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.57/1.49      | m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.57/1.49      | r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k2_tops_1(sK0,sK1))) = iProver_top ),
% 7.57/1.49      inference(light_normalisation,[status(thm)],[c_4660,c_2703]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_19069,plain,
% 7.57/1.49      ( r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k2_tops_1(sK0,sK1))) = iProver_top ),
% 7.57/1.49      inference(global_propositional_subsumption,
% 7.57/1.49                [status(thm)],
% 7.57/1.49                [c_18736,c_18,c_702,c_756,c_758,c_4671]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_0,plain,
% 7.57/1.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 7.57/1.49      inference(cnf_transformation,[],[f36]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_667,plain,
% 7.57/1.49      ( X0 = X1
% 7.57/1.49      | r1_tarski(X0,X1) != iProver_top
% 7.57/1.49      | r1_tarski(X1,X0) != iProver_top ),
% 7.57/1.49      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_19073,plain,
% 7.57/1.49      ( k2_pre_topc(sK0,k2_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 7.57/1.49      | r1_tarski(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) != iProver_top ),
% 7.57/1.49      inference(superposition,[status(thm)],[c_19069,c_667]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_653,plain,
% 7.57/1.49      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.57/1.49      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 7.57/1.49      inference(predicate_to_equality,[status(thm)],[c_253]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_3,plain,
% 7.57/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.57/1.49      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 7.57/1.49      inference(cnf_transformation,[],[f37]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_665,plain,
% 7.57/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.57/1.49      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 7.57/1.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_9,plain,
% 7.57/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.57/1.49      | ~ l1_pre_topc(X1)
% 7.57/1.49      | k2_pre_topc(X1,k2_pre_topc(X1,X0)) = k2_pre_topc(X1,X0) ),
% 7.57/1.49      inference(cnf_transformation,[],[f43]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_240,plain,
% 7.57/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.57/1.49      | k2_pre_topc(X1,k2_pre_topc(X1,X0)) = k2_pre_topc(X1,X0)
% 7.57/1.49      | sK0 != X1 ),
% 7.57/1.49      inference(resolution_lifted,[status(thm)],[c_9,c_16]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_241,plain,
% 7.57/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.57/1.49      | k2_pre_topc(sK0,k2_pre_topc(sK0,X0)) = k2_pre_topc(sK0,X0) ),
% 7.57/1.49      inference(unflattening,[status(thm)],[c_240]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_654,plain,
% 7.57/1.49      ( k2_pre_topc(sK0,k2_pre_topc(sK0,X0)) = k2_pre_topc(sK0,X0)
% 7.57/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.57/1.49      inference(predicate_to_equality,[status(thm)],[c_241]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_1284,plain,
% 7.57/1.49      ( k2_pre_topc(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))
% 7.57/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.57/1.49      inference(superposition,[status(thm)],[c_665,c_654]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_1885,plain,
% 7.57/1.49      ( k2_pre_topc(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
% 7.57/1.49      inference(superposition,[status(thm)],[c_659,c_1284]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_922,plain,
% 7.57/1.49      ( k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 7.57/1.49      inference(superposition,[status(thm)],[c_659,c_654]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_10,plain,
% 7.57/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.57/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 7.57/1.49      | r1_tarski(k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X0,X2)),k9_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k2_pre_topc(X1,X2)))
% 7.57/1.49      | ~ l1_pre_topc(X1) ),
% 7.57/1.49      inference(cnf_transformation,[],[f44]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_225,plain,
% 7.57/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.57/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 7.57/1.49      | r1_tarski(k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X0,X2)),k9_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k2_pre_topc(X1,X2)))
% 7.57/1.49      | sK0 != X1 ),
% 7.57/1.49      inference(resolution_lifted,[status(thm)],[c_10,c_16]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_226,plain,
% 7.57/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.57/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.57/1.49      | r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k2_pre_topc(sK0,X1))) ),
% 7.57/1.49      inference(unflattening,[status(thm)],[c_225]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_655,plain,
% 7.57/1.49      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.57/1.49      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.57/1.49      | r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k2_pre_topc(sK0,X1))) = iProver_top ),
% 7.57/1.49      inference(predicate_to_equality,[status(thm)],[c_226]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_1203,plain,
% 7.57/1.49      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.57/1.49      | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.57/1.49      | r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X0)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X0))) = iProver_top ),
% 7.57/1.49      inference(superposition,[status(thm)],[c_922,c_655]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_714,plain,
% 7.57/1.49      ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 7.57/1.49      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.57/1.49      inference(instantiation,[status(thm)],[c_253]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_715,plain,
% 7.57/1.49      ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 7.57/1.49      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.57/1.49      inference(predicate_to_equality,[status(thm)],[c_714]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_3115,plain,
% 7.57/1.49      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.57/1.49      | r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X0)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X0))) = iProver_top ),
% 7.57/1.49      inference(global_propositional_subsumption,
% 7.57/1.49                [status(thm)],
% 7.57/1.49                [c_1203,c_18,c_715]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_3125,plain,
% 7.57/1.49      ( m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.57/1.49      | r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))) = iProver_top ),
% 7.57/1.49      inference(superposition,[status(thm)],[c_1885,c_3115]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_11,plain,
% 7.57/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.57/1.49      | ~ l1_pre_topc(X1)
% 7.57/1.49      | k9_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k2_tops_1(X1,X0) ),
% 7.57/1.49      inference(cnf_transformation,[],[f45]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_213,plain,
% 7.57/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.57/1.49      | k9_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k2_tops_1(X1,X0)
% 7.57/1.49      | sK0 != X1 ),
% 7.57/1.49      inference(resolution_lifted,[status(thm)],[c_11,c_16]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_214,plain,
% 7.57/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.57/1.49      | k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k2_tops_1(sK0,X0) ),
% 7.57/1.49      inference(unflattening,[status(thm)],[c_213]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_656,plain,
% 7.57/1.49      ( k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k2_tops_1(sK0,X0)
% 7.57/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.57/1.49      inference(predicate_to_equality,[status(thm)],[c_214]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_1559,plain,
% 7.57/1.49      ( k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k2_tops_1(sK0,sK1) ),
% 7.57/1.49      inference(superposition,[status(thm)],[c_659,c_656]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_3128,plain,
% 7.57/1.49      ( m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.57/1.49      | r1_tarski(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) = iProver_top ),
% 7.57/1.49      inference(light_normalisation,[status(thm)],[c_3125,c_1559]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_3303,plain,
% 7.57/1.49      ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.57/1.49      | r1_tarski(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) = iProver_top ),
% 7.57/1.49      inference(superposition,[status(thm)],[c_653,c_3128]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_3306,plain,
% 7.57/1.49      ( k2_pre_topc(sK0,k2_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 7.57/1.49      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.57/1.49      | r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k2_tops_1(sK0,sK1))) != iProver_top ),
% 7.57/1.49      inference(superposition,[status(thm)],[c_3303,c_667]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_3307,plain,
% 7.57/1.49      ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 7.57/1.49      | ~ r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k2_tops_1(sK0,sK1)))
% 7.57/1.49      | k2_pre_topc(sK0,k2_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 7.57/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_3306]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_4676,plain,
% 7.57/1.49      ( ~ m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
% 7.57/1.49      | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 7.57/1.49      | ~ m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
% 7.57/1.49      | r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k2_tops_1(sK0,sK1))) ),
% 7.57/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_4671]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_973,plain,
% 7.57/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.57/1.49      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.57/1.49      inference(instantiation,[status(thm)],[c_3]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_6741,plain,
% 7.57/1.49      ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 7.57/1.49      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.57/1.49      inference(instantiation,[status(thm)],[c_973]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_19178,plain,
% 7.57/1.49      ( k2_pre_topc(sK0,k2_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 7.57/1.49      inference(global_propositional_subsumption,
% 7.57/1.49                [status(thm)],
% 7.57/1.49                [c_19073,c_15,c_701,c_755,c_754,c_3307,c_4676,c_6741]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_1560,plain,
% 7.57/1.49      ( k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,X0)),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,X0)))) = k2_tops_1(sK0,k2_tops_1(sK0,X0))
% 7.57/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.57/1.49      inference(superposition,[status(thm)],[c_657,c_656]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_3859,plain,
% 7.57/1.49      ( k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)))) = k2_tops_1(sK0,k2_tops_1(sK0,sK1)) ),
% 7.57/1.49      inference(superposition,[status(thm)],[c_659,c_1560]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_19187,plain,
% 7.57/1.49      ( k9_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)))) = k2_tops_1(sK0,k2_tops_1(sK0,sK1)) ),
% 7.57/1.49      inference(demodulation,[status(thm)],[c_19178,c_3859]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_7,plain,
% 7.57/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.57/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 7.57/1.49      | r1_tarski(k3_subset_1(X1,X0),k3_subset_1(X1,k9_subset_1(X1,X0,X2))) ),
% 7.57/1.49      inference(cnf_transformation,[],[f41]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_661,plain,
% 7.57/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.57/1.49      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 7.57/1.49      | r1_tarski(k3_subset_1(X1,X0),k3_subset_1(X1,k9_subset_1(X1,X0,X2))) = iProver_top ),
% 7.57/1.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_19334,plain,
% 7.57/1.49      ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.57/1.49      | m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.57/1.49      | r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)))) = iProver_top ),
% 7.57/1.49      inference(superposition,[status(thm)],[c_19187,c_661]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_717,plain,
% 7.57/1.49      ( m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)),k1_zfmisc_1(u1_struct_0(sK0)))
% 7.57/1.49      | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.57/1.49      inference(instantiation,[status(thm)],[c_253]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_15451,plain,
% 7.57/1.49      ( m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
% 7.57/1.49      | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.57/1.49      inference(instantiation,[status(thm)],[c_717]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_15452,plain,
% 7.57/1.49      ( m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 7.57/1.49      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.57/1.49      inference(predicate_to_equality,[status(thm)],[c_15451]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_4643,plain,
% 7.57/1.49      ( ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 7.57/1.49      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.57/1.49      inference(instantiation,[status(thm)],[c_973]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_4644,plain,
% 7.57/1.49      ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.57/1.49      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 7.57/1.49      inference(predicate_to_equality,[status(thm)],[c_4643]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_691,plain,
% 7.57/1.49      ( ~ m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(X0))
% 7.57/1.49      | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(X0))
% 7.57/1.49      | r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1))
% 7.57/1.49      | ~ r1_tarski(k3_subset_1(X0,k2_tops_1(sK0,sK1)),k3_subset_1(X0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))) ),
% 7.57/1.49      inference(instantiation,[status(thm)],[c_4]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_793,plain,
% 7.57/1.49      ( ~ m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
% 7.57/1.49      | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 7.57/1.49      | r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1))
% 7.57/1.49      | ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)))) ),
% 7.57/1.49      inference(instantiation,[status(thm)],[c_691]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_794,plain,
% 7.57/1.49      ( m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.57/1.49      | m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.57/1.49      | r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) = iProver_top
% 7.57/1.49      | r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)))) != iProver_top ),
% 7.57/1.49      inference(predicate_to_equality,[status(thm)],[c_793]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_14,negated_conjecture,
% 7.57/1.49      ( ~ r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) ),
% 7.57/1.49      inference(cnf_transformation,[],[f50]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(c_19,plain,
% 7.57/1.49      ( r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) != iProver_top ),
% 7.57/1.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.57/1.49  
% 7.57/1.49  cnf(contradiction,plain,
% 7.57/1.49      ( $false ),
% 7.57/1.49      inference(minisat,
% 7.57/1.49                [status(thm)],
% 7.57/1.49                [c_19334,c_15452,c_4644,c_794,c_756,c_702,c_19,c_18]) ).
% 7.57/1.49  
% 7.57/1.49  
% 7.57/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.57/1.49  
% 7.57/1.49  ------                               Statistics
% 7.57/1.49  
% 7.57/1.49  ------ General
% 7.57/1.49  
% 7.57/1.49  abstr_ref_over_cycles:                  0
% 7.57/1.49  abstr_ref_under_cycles:                 0
% 7.57/1.49  gc_basic_clause_elim:                   0
% 7.57/1.49  forced_gc_time:                         0
% 7.57/1.49  parsing_time:                           0.009
% 7.57/1.49  unif_index_cands_time:                  0.
% 7.57/1.49  unif_index_add_time:                    0.
% 7.57/1.49  orderings_time:                         0.
% 7.57/1.49  out_proof_time:                         0.014
% 7.57/1.49  total_time:                             0.764
% 7.57/1.49  num_of_symbols:                         43
% 7.57/1.49  num_of_terms:                           33508
% 7.57/1.49  
% 7.57/1.49  ------ Preprocessing
% 7.57/1.49  
% 7.57/1.49  num_of_splits:                          0
% 7.57/1.49  num_of_split_atoms:                     0
% 7.57/1.49  num_of_reused_defs:                     0
% 7.57/1.49  num_eq_ax_congr_red:                    4
% 7.57/1.49  num_of_sem_filtered_clauses:            1
% 7.57/1.49  num_of_subtypes:                        0
% 7.57/1.49  monotx_restored_types:                  0
% 7.57/1.49  sat_num_of_epr_types:                   0
% 7.57/1.49  sat_num_of_non_cyclic_types:            0
% 7.57/1.49  sat_guarded_non_collapsed_types:        0
% 7.57/1.49  num_pure_diseq_elim:                    0
% 7.57/1.49  simp_replaced_by:                       0
% 7.57/1.49  res_preprocessed:                       84
% 7.57/1.49  prep_upred:                             0
% 7.57/1.49  prep_unflattend:                        6
% 7.57/1.49  smt_new_axioms:                         0
% 7.57/1.49  pred_elim_cands:                        2
% 7.57/1.49  pred_elim:                              1
% 7.57/1.49  pred_elim_cl:                           1
% 7.57/1.49  pred_elim_cycles:                       3
% 7.57/1.49  merged_defs:                            0
% 7.57/1.49  merged_defs_ncl:                        0
% 7.57/1.49  bin_hyper_res:                          0
% 7.57/1.49  prep_cycles:                            4
% 7.57/1.49  pred_elim_time:                         0.002
% 7.57/1.49  splitting_time:                         0.
% 7.57/1.49  sem_filter_time:                        0.
% 7.57/1.49  monotx_time:                            0.
% 7.57/1.49  subtype_inf_time:                       0.
% 7.57/1.49  
% 7.57/1.49  ------ Problem properties
% 7.57/1.49  
% 7.57/1.49  clauses:                                15
% 7.57/1.49  conjectures:                            2
% 7.57/1.49  epr:                                    2
% 7.57/1.49  horn:                                   15
% 7.57/1.49  ground:                                 2
% 7.57/1.49  unary:                                  3
% 7.57/1.49  binary:                                 6
% 7.57/1.49  lits:                                   35
% 7.57/1.49  lits_eq:                                4
% 7.57/1.49  fd_pure:                                0
% 7.57/1.49  fd_pseudo:                              0
% 7.57/1.49  fd_cond:                                0
% 7.57/1.49  fd_pseudo_cond:                         1
% 7.57/1.49  ac_symbols:                             0
% 7.57/1.49  
% 7.57/1.49  ------ Propositional Solver
% 7.57/1.49  
% 7.57/1.49  prop_solver_calls:                      34
% 7.57/1.49  prop_fast_solver_calls:                 900
% 7.57/1.49  smt_solver_calls:                       0
% 7.57/1.49  smt_fast_solver_calls:                  0
% 7.57/1.49  prop_num_of_clauses:                    11227
% 7.57/1.49  prop_preprocess_simplified:             13520
% 7.57/1.49  prop_fo_subsumed:                       20
% 7.57/1.49  prop_solver_time:                       0.
% 7.57/1.49  smt_solver_time:                        0.
% 7.57/1.49  smt_fast_solver_time:                   0.
% 7.57/1.49  prop_fast_solver_time:                  0.
% 7.57/1.49  prop_unsat_core_time:                   0.001
% 7.57/1.49  
% 7.57/1.49  ------ QBF
% 7.57/1.49  
% 7.57/1.49  qbf_q_res:                              0
% 7.57/1.49  qbf_num_tautologies:                    0
% 7.57/1.49  qbf_prep_cycles:                        0
% 7.57/1.49  
% 7.57/1.49  ------ BMC1
% 7.57/1.49  
% 7.57/1.49  bmc1_current_bound:                     -1
% 7.57/1.49  bmc1_last_solved_bound:                 -1
% 7.57/1.49  bmc1_unsat_core_size:                   -1
% 7.57/1.49  bmc1_unsat_core_parents_size:           -1
% 7.57/1.49  bmc1_merge_next_fun:                    0
% 7.57/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.57/1.49  
% 7.57/1.49  ------ Instantiation
% 7.57/1.49  
% 7.57/1.49  inst_num_of_clauses:                    2856
% 7.57/1.49  inst_num_in_passive:                    461
% 7.57/1.49  inst_num_in_active:                     1118
% 7.57/1.49  inst_num_in_unprocessed:                1277
% 7.57/1.49  inst_num_of_loops:                      1170
% 7.57/1.49  inst_num_of_learning_restarts:          0
% 7.57/1.49  inst_num_moves_active_passive:          48
% 7.57/1.49  inst_lit_activity:                      0
% 7.57/1.49  inst_lit_activity_moves:                1
% 7.57/1.49  inst_num_tautologies:                   0
% 7.57/1.49  inst_num_prop_implied:                  0
% 7.57/1.49  inst_num_existing_simplified:           0
% 7.57/1.49  inst_num_eq_res_simplified:             0
% 7.57/1.49  inst_num_child_elim:                    0
% 7.57/1.49  inst_num_of_dismatching_blockings:      2086
% 7.57/1.49  inst_num_of_non_proper_insts:           2667
% 7.57/1.49  inst_num_of_duplicates:                 0
% 7.57/1.49  inst_inst_num_from_inst_to_res:         0
% 7.57/1.49  inst_dismatching_checking_time:         0.
% 7.57/1.49  
% 7.57/1.49  ------ Resolution
% 7.57/1.49  
% 7.57/1.49  res_num_of_clauses:                     0
% 7.57/1.49  res_num_in_passive:                     0
% 7.57/1.49  res_num_in_active:                      0
% 7.57/1.49  res_num_of_loops:                       88
% 7.57/1.49  res_forward_subset_subsumed:            270
% 7.57/1.49  res_backward_subset_subsumed:           0
% 7.57/1.49  res_forward_subsumed:                   0
% 7.57/1.49  res_backward_subsumed:                  0
% 7.57/1.49  res_forward_subsumption_resolution:     0
% 7.57/1.49  res_backward_subsumption_resolution:    0
% 7.57/1.49  res_clause_to_clause_subsumption:       6102
% 7.57/1.49  res_orphan_elimination:                 0
% 7.57/1.49  res_tautology_del:                      83
% 7.57/1.49  res_num_eq_res_simplified:              0
% 7.57/1.49  res_num_sel_changes:                    0
% 7.57/1.49  res_moves_from_active_to_pass:          0
% 7.57/1.49  
% 7.57/1.49  ------ Superposition
% 7.57/1.49  
% 7.57/1.49  sup_time_total:                         0.
% 7.57/1.49  sup_time_generating:                    0.
% 7.57/1.49  sup_time_sim_full:                      0.
% 7.57/1.49  sup_time_sim_immed:                     0.
% 7.57/1.49  
% 7.57/1.49  sup_num_of_clauses:                     1203
% 7.57/1.49  sup_num_in_active:                      216
% 7.57/1.49  sup_num_in_passive:                     987
% 7.57/1.49  sup_num_of_loops:                       232
% 7.57/1.49  sup_fw_superposition:                   761
% 7.57/1.49  sup_bw_superposition:                   641
% 7.57/1.49  sup_immediate_simplified:               287
% 7.57/1.49  sup_given_eliminated:                   0
% 7.57/1.49  comparisons_done:                       0
% 7.57/1.49  comparisons_avoided:                    0
% 7.57/1.49  
% 7.57/1.49  ------ Simplifications
% 7.57/1.49  
% 7.57/1.49  
% 7.57/1.49  sim_fw_subset_subsumed:                 3
% 7.57/1.49  sim_bw_subset_subsumed:                 5
% 7.57/1.49  sim_fw_subsumed:                        17
% 7.57/1.49  sim_bw_subsumed:                        0
% 7.57/1.49  sim_fw_subsumption_res:                 0
% 7.57/1.49  sim_bw_subsumption_res:                 0
% 7.57/1.49  sim_tautology_del:                      52
% 7.57/1.49  sim_eq_tautology_del:                   91
% 7.57/1.49  sim_eq_res_simp:                        0
% 7.57/1.49  sim_fw_demodulated:                     23
% 7.57/1.49  sim_bw_demodulated:                     16
% 7.57/1.49  sim_light_normalised:                   255
% 7.57/1.49  sim_joinable_taut:                      0
% 7.57/1.49  sim_joinable_simp:                      0
% 7.57/1.49  sim_ac_normalised:                      0
% 7.57/1.49  sim_smt_subsumption:                    0
% 7.57/1.49  
%------------------------------------------------------------------------------
