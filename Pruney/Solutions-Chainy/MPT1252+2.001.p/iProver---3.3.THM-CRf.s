%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:14:06 EST 2020

% Result     : Theorem 19.66s
% Output     : CNFRefutation 19.66s
% Verified   : 
% Statistics : Number of formulae       :  155 (1908 expanded)
%              Number of clauses        :  100 ( 673 expanded)
%              Number of leaves         :   16 ( 472 expanded)
%              Depth                    :   23
%              Number of atoms          :  392 (5318 expanded)
%              Number of equality atoms :  161 ( 720 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k2_tops_1(X0,k2_tops_1(X0,X1)),k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => r1_tarski(k2_tops_1(X0,k2_tops_1(X0,X1)),k2_tops_1(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(X0,k2_tops_1(X0,X1)),k2_tops_1(X0,X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(X0,k2_tops_1(X0,X1)),k2_tops_1(X0,X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_tarski(k2_tops_1(X0,k2_tops_1(X0,sK1)),k2_tops_1(X0,sK1))
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
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

fof(f38,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f32,f37,f36])).

fof(f56,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f38])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f55,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f16])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f33])).

fof(f41,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k2_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k2_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k2_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_tarski(X1,X2)
              | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
            & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | ~ r1_tarski(X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f57,plain,(
    ~ r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_743,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X0)) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_18,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_224,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X0)) = k2_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_18])).

cnf(c_225,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k2_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_224])).

cnf(c_741,plain,
    ( k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k2_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_225])).

cnf(c_1131,plain,
    ( k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_743,c_741])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_236,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_18])).

cnf(c_237,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_236])).

cnf(c_740,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_237])).

cnf(c_1140,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1131,c_740])).

cnf(c_20,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_789,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_237])).

cnf(c_790,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_789])).

cnf(c_1837,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1140,c_20,c_790])).

cnf(c_1844,plain,
    ( k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) = k2_tops_1(sK0,k2_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_1837,c_741])).

cnf(c_2441,plain,
    ( m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1844,c_740])).

cnf(c_843,plain,
    ( m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_237])).

cnf(c_844,plain,
    ( m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_843])).

cnf(c_3675,plain,
    ( m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2441,c_20,c_790,c_844])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X0,X2) = k4_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_750,plain,
    ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1958,plain,
    ( k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1837,c_750])).

cnf(c_3688,plain,
    ( k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_tops_1(sK0,k2_tops_1(sK0,sK1))) ),
    inference(superposition,[status(thm)],[c_3675,c_1958])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_212,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_18])).

cnf(c_213,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_212])).

cnf(c_742,plain,
    ( k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_213])).

cnf(c_1843,plain,
    ( k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k2_pre_topc(sK0,k2_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_1837,c_742])).

cnf(c_3702,plain,
    ( k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k2_tops_1(sK0,sK1)) ),
    inference(light_normalisation,[status(thm)],[c_3688,c_1843])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | r1_tarski(k3_subset_1(X1,k4_subset_1(X1,X2,X0)),k3_subset_1(X1,X2)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_745,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(k3_subset_1(X1,k4_subset_1(X1,X2,X0)),k3_subset_1(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2694,plain,
    ( m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1))),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1843,c_745])).

cnf(c_24670,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1))),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2694,c_20,c_790,c_844])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_752,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_24674,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1))) = k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))
    | r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_24670,c_752])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_287,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_18])).

cnf(c_288,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_287])).

cnf(c_842,plain,
    ( ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_288])).

cnf(c_846,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_842])).

cnf(c_736,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_288])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_749,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k2_pre_topc(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_275,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,k2_pre_topc(X1,X0)) = k2_pre_topc(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_18])).

cnf(c_276,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k2_pre_topc(sK0,X0)) = k2_pre_topc(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_275])).

cnf(c_737,plain,
    ( k2_pre_topc(sK0,k2_pre_topc(sK0,X0)) = k2_pre_topc(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_276])).

cnf(c_1381,plain,
    ( k2_pre_topc(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_749,c_737])).

cnf(c_3502,plain,
    ( k2_pre_topc(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(superposition,[status(thm)],[c_743,c_1381])).

cnf(c_987,plain,
    ( k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_743,c_737])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X0,X2)),k9_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k2_pre_topc(X1,X2)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_260,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X0,X2)),k9_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k2_pre_topc(X1,X2)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_18])).

cnf(c_261,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k2_pre_topc(sK0,X1))) ),
    inference(unflattening,[status(thm)],[c_260])).

cnf(c_738,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k2_pre_topc(sK0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_261])).

cnf(c_1262,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X0)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_987,c_738])).

cnf(c_802,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_288])).

cnf(c_803,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_802])).

cnf(c_3526,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X0)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1262,c_20,c_803])).

cnf(c_3538,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3502,c_3526])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_248,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k9_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k2_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_18])).

cnf(c_249,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k2_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_248])).

cnf(c_739,plain,
    ( k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k2_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_249])).

cnf(c_1699,plain,
    ( k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_743,c_739])).

cnf(c_3540,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3538,c_1699])).

cnf(c_3749,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_736,c_3540])).

cnf(c_1061,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_5094,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_1061])).

cnf(c_5095,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5094])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,X0)
    | r1_tarski(k3_subset_1(X1,X0),k3_subset_1(X1,X2)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_746,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(k3_subset_1(X1,X0),k3_subset_1(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2035,plain,
    ( k3_subset_1(X0,X1) = k3_subset_1(X0,X2)
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_746,c_752])).

cnf(c_24676,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1))) = k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))
    | m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_24670,c_2035])).

cnf(c_24684,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1))) = k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_24674,c_20,c_790,c_846,c_3749,c_5095,c_24676])).

cnf(c_24691,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_24684,c_749])).

cnf(c_5487,plain,
    ( ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_1061])).

cnf(c_5488,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5487])).

cnf(c_24772,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_24691,c_20,c_790,c_5488])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_748,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1371,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0))) = k2_pre_topc(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_736,c_748])).

cnf(c_2898,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_pre_topc(sK0,X0)))) = k2_pre_topc(sK0,k2_pre_topc(sK0,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_736,c_1371])).

cnf(c_4368,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))))) = k2_pre_topc(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_749,c_2898])).

cnf(c_24928,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))))))) = k2_pre_topc(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))))) ),
    inference(superposition,[status(thm)],[c_24772,c_4368])).

cnf(c_1841,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_1837,c_748])).

cnf(c_1845,plain,
    ( k2_pre_topc(sK0,k2_pre_topc(sK0,k2_tops_1(sK0,sK1))) = k2_pre_topc(sK0,k2_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_1837,c_737])).

cnf(c_25060,plain,
    ( k2_pre_topc(sK0,k2_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_24928,c_1841,c_1845,c_24684])).

cnf(c_65089,plain,
    ( k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_3702,c_3702,c_25060])).

cnf(c_65092,plain,
    ( m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_65089,c_745])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | r1_tarski(X2,X0)
    | ~ r1_tarski(k3_subset_1(X1,X0),k3_subset_1(X1,X2)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_779,plain,
    ( ~ m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(X0))
    | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(X0))
    | r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1))
    | ~ r1_tarski(k3_subset_1(X0,k2_tops_1(sK0,sK1)),k3_subset_1(X0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_896,plain,
    ( ~ m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1))
    | ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)))) ),
    inference(instantiation,[status(thm)],[c_779])).

cnf(c_897,plain,
    ( m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) = iProver_top
    | r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_896])).

cnf(c_16,negated_conjecture,
    ( ~ r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_21,plain,
    ( r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_65092,c_897,c_844,c_790,c_21,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:36:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 19.66/2.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.66/2.99  
% 19.66/2.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.66/2.99  
% 19.66/2.99  ------  iProver source info
% 19.66/2.99  
% 19.66/2.99  git: date: 2020-06-30 10:37:57 +0100
% 19.66/2.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.66/2.99  git: non_committed_changes: false
% 19.66/2.99  git: last_make_outside_of_git: false
% 19.66/2.99  
% 19.66/2.99  ------ 
% 19.66/2.99  
% 19.66/2.99  ------ Input Options
% 19.66/2.99  
% 19.66/2.99  --out_options                           all
% 19.66/2.99  --tptp_safe_out                         true
% 19.66/2.99  --problem_path                          ""
% 19.66/2.99  --include_path                          ""
% 19.66/2.99  --clausifier                            res/vclausify_rel
% 19.66/2.99  --clausifier_options                    ""
% 19.66/2.99  --stdin                                 false
% 19.66/2.99  --stats_out                             all
% 19.66/2.99  
% 19.66/2.99  ------ General Options
% 19.66/2.99  
% 19.66/2.99  --fof                                   false
% 19.66/2.99  --time_out_real                         305.
% 19.66/2.99  --time_out_virtual                      -1.
% 19.66/2.99  --symbol_type_check                     false
% 19.66/2.99  --clausify_out                          false
% 19.66/2.99  --sig_cnt_out                           false
% 19.66/2.99  --trig_cnt_out                          false
% 19.66/2.99  --trig_cnt_out_tolerance                1.
% 19.66/2.99  --trig_cnt_out_sk_spl                   false
% 19.66/2.99  --abstr_cl_out                          false
% 19.66/2.99  
% 19.66/2.99  ------ Global Options
% 19.66/2.99  
% 19.66/2.99  --schedule                              default
% 19.66/2.99  --add_important_lit                     false
% 19.66/2.99  --prop_solver_per_cl                    1000
% 19.66/2.99  --min_unsat_core                        false
% 19.66/2.99  --soft_assumptions                      false
% 19.66/2.99  --soft_lemma_size                       3
% 19.66/2.99  --prop_impl_unit_size                   0
% 19.66/2.99  --prop_impl_unit                        []
% 19.66/2.99  --share_sel_clauses                     true
% 19.66/2.99  --reset_solvers                         false
% 19.66/2.99  --bc_imp_inh                            [conj_cone]
% 19.66/2.99  --conj_cone_tolerance                   3.
% 19.66/2.99  --extra_neg_conj                        none
% 19.66/2.99  --large_theory_mode                     true
% 19.66/2.99  --prolific_symb_bound                   200
% 19.66/2.99  --lt_threshold                          2000
% 19.66/2.99  --clause_weak_htbl                      true
% 19.66/2.99  --gc_record_bc_elim                     false
% 19.66/2.99  
% 19.66/2.99  ------ Preprocessing Options
% 19.66/2.99  
% 19.66/2.99  --preprocessing_flag                    true
% 19.66/2.99  --time_out_prep_mult                    0.1
% 19.66/2.99  --splitting_mode                        input
% 19.66/2.99  --splitting_grd                         true
% 19.66/2.99  --splitting_cvd                         false
% 19.66/2.99  --splitting_cvd_svl                     false
% 19.66/2.99  --splitting_nvd                         32
% 19.66/2.99  --sub_typing                            true
% 19.66/2.99  --prep_gs_sim                           true
% 19.66/2.99  --prep_unflatten                        true
% 19.66/2.99  --prep_res_sim                          true
% 19.66/2.99  --prep_upred                            true
% 19.66/2.99  --prep_sem_filter                       exhaustive
% 19.66/2.99  --prep_sem_filter_out                   false
% 19.66/2.99  --pred_elim                             true
% 19.66/2.99  --res_sim_input                         true
% 19.66/2.99  --eq_ax_congr_red                       true
% 19.66/2.99  --pure_diseq_elim                       true
% 19.66/2.99  --brand_transform                       false
% 19.66/2.99  --non_eq_to_eq                          false
% 19.66/2.99  --prep_def_merge                        true
% 19.66/2.99  --prep_def_merge_prop_impl              false
% 19.66/2.99  --prep_def_merge_mbd                    true
% 19.66/2.99  --prep_def_merge_tr_red                 false
% 19.66/2.99  --prep_def_merge_tr_cl                  false
% 19.66/2.99  --smt_preprocessing                     true
% 19.66/2.99  --smt_ac_axioms                         fast
% 19.66/2.99  --preprocessed_out                      false
% 19.66/2.99  --preprocessed_stats                    false
% 19.66/2.99  
% 19.66/2.99  ------ Abstraction refinement Options
% 19.66/2.99  
% 19.66/2.99  --abstr_ref                             []
% 19.66/2.99  --abstr_ref_prep                        false
% 19.66/2.99  --abstr_ref_until_sat                   false
% 19.66/2.99  --abstr_ref_sig_restrict                funpre
% 19.66/2.99  --abstr_ref_af_restrict_to_split_sk     false
% 19.66/2.99  --abstr_ref_under                       []
% 19.66/2.99  
% 19.66/2.99  ------ SAT Options
% 19.66/2.99  
% 19.66/2.99  --sat_mode                              false
% 19.66/2.99  --sat_fm_restart_options                ""
% 19.66/2.99  --sat_gr_def                            false
% 19.66/2.99  --sat_epr_types                         true
% 19.66/2.99  --sat_non_cyclic_types                  false
% 19.66/2.99  --sat_finite_models                     false
% 19.66/2.99  --sat_fm_lemmas                         false
% 19.66/2.99  --sat_fm_prep                           false
% 19.66/2.99  --sat_fm_uc_incr                        true
% 19.66/2.99  --sat_out_model                         small
% 19.66/2.99  --sat_out_clauses                       false
% 19.66/2.99  
% 19.66/2.99  ------ QBF Options
% 19.66/2.99  
% 19.66/2.99  --qbf_mode                              false
% 19.66/2.99  --qbf_elim_univ                         false
% 19.66/2.99  --qbf_dom_inst                          none
% 19.66/2.99  --qbf_dom_pre_inst                      false
% 19.66/2.99  --qbf_sk_in                             false
% 19.66/2.99  --qbf_pred_elim                         true
% 19.66/2.99  --qbf_split                             512
% 19.66/2.99  
% 19.66/2.99  ------ BMC1 Options
% 19.66/2.99  
% 19.66/2.99  --bmc1_incremental                      false
% 19.66/2.99  --bmc1_axioms                           reachable_all
% 19.66/2.99  --bmc1_min_bound                        0
% 19.66/2.99  --bmc1_max_bound                        -1
% 19.66/2.99  --bmc1_max_bound_default                -1
% 19.66/2.99  --bmc1_symbol_reachability              true
% 19.66/2.99  --bmc1_property_lemmas                  false
% 19.66/2.99  --bmc1_k_induction                      false
% 19.66/2.99  --bmc1_non_equiv_states                 false
% 19.66/2.99  --bmc1_deadlock                         false
% 19.66/2.99  --bmc1_ucm                              false
% 19.66/2.99  --bmc1_add_unsat_core                   none
% 19.66/2.99  --bmc1_unsat_core_children              false
% 19.66/2.99  --bmc1_unsat_core_extrapolate_axioms    false
% 19.66/2.99  --bmc1_out_stat                         full
% 19.66/2.99  --bmc1_ground_init                      false
% 19.66/2.99  --bmc1_pre_inst_next_state              false
% 19.66/2.99  --bmc1_pre_inst_state                   false
% 19.66/2.99  --bmc1_pre_inst_reach_state             false
% 19.66/2.99  --bmc1_out_unsat_core                   false
% 19.66/2.99  --bmc1_aig_witness_out                  false
% 19.66/2.99  --bmc1_verbose                          false
% 19.66/2.99  --bmc1_dump_clauses_tptp                false
% 19.66/2.99  --bmc1_dump_unsat_core_tptp             false
% 19.66/2.99  --bmc1_dump_file                        -
% 19.66/2.99  --bmc1_ucm_expand_uc_limit              128
% 19.66/2.99  --bmc1_ucm_n_expand_iterations          6
% 19.66/2.99  --bmc1_ucm_extend_mode                  1
% 19.66/2.99  --bmc1_ucm_init_mode                    2
% 19.66/2.99  --bmc1_ucm_cone_mode                    none
% 19.66/2.99  --bmc1_ucm_reduced_relation_type        0
% 19.66/2.99  --bmc1_ucm_relax_model                  4
% 19.66/2.99  --bmc1_ucm_full_tr_after_sat            true
% 19.66/2.99  --bmc1_ucm_expand_neg_assumptions       false
% 19.66/2.99  --bmc1_ucm_layered_model                none
% 19.66/2.99  --bmc1_ucm_max_lemma_size               10
% 19.66/2.99  
% 19.66/2.99  ------ AIG Options
% 19.66/2.99  
% 19.66/2.99  --aig_mode                              false
% 19.66/2.99  
% 19.66/2.99  ------ Instantiation Options
% 19.66/2.99  
% 19.66/2.99  --instantiation_flag                    true
% 19.66/2.99  --inst_sos_flag                         true
% 19.66/2.99  --inst_sos_phase                        true
% 19.66/2.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.66/2.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.66/2.99  --inst_lit_sel_side                     num_symb
% 19.66/2.99  --inst_solver_per_active                1400
% 19.66/2.99  --inst_solver_calls_frac                1.
% 19.66/2.99  --inst_passive_queue_type               priority_queues
% 19.66/2.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.66/2.99  --inst_passive_queues_freq              [25;2]
% 19.66/2.99  --inst_dismatching                      true
% 19.66/2.99  --inst_eager_unprocessed_to_passive     true
% 19.66/2.99  --inst_prop_sim_given                   true
% 19.66/2.99  --inst_prop_sim_new                     false
% 19.66/2.99  --inst_subs_new                         false
% 19.66/2.99  --inst_eq_res_simp                      false
% 19.66/2.99  --inst_subs_given                       false
% 19.66/2.99  --inst_orphan_elimination               true
% 19.66/2.99  --inst_learning_loop_flag               true
% 19.66/2.99  --inst_learning_start                   3000
% 19.66/2.99  --inst_learning_factor                  2
% 19.66/2.99  --inst_start_prop_sim_after_learn       3
% 19.66/2.99  --inst_sel_renew                        solver
% 19.66/2.99  --inst_lit_activity_flag                true
% 19.66/2.99  --inst_restr_to_given                   false
% 19.66/2.99  --inst_activity_threshold               500
% 19.66/2.99  --inst_out_proof                        true
% 19.66/2.99  
% 19.66/2.99  ------ Resolution Options
% 19.66/2.99  
% 19.66/2.99  --resolution_flag                       true
% 19.66/2.99  --res_lit_sel                           adaptive
% 19.66/2.99  --res_lit_sel_side                      none
% 19.66/2.99  --res_ordering                          kbo
% 19.66/2.99  --res_to_prop_solver                    active
% 19.66/2.99  --res_prop_simpl_new                    false
% 19.66/2.99  --res_prop_simpl_given                  true
% 19.66/2.99  --res_passive_queue_type                priority_queues
% 19.66/2.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.66/2.99  --res_passive_queues_freq               [15;5]
% 19.66/2.99  --res_forward_subs                      full
% 19.66/2.99  --res_backward_subs                     full
% 19.66/2.99  --res_forward_subs_resolution           true
% 19.66/2.99  --res_backward_subs_resolution          true
% 19.66/2.99  --res_orphan_elimination                true
% 19.66/2.99  --res_time_limit                        2.
% 19.66/2.99  --res_out_proof                         true
% 19.66/2.99  
% 19.66/2.99  ------ Superposition Options
% 19.66/2.99  
% 19.66/2.99  --superposition_flag                    true
% 19.66/2.99  --sup_passive_queue_type                priority_queues
% 19.66/2.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.66/2.99  --sup_passive_queues_freq               [8;1;4]
% 19.66/2.99  --demod_completeness_check              fast
% 19.66/2.99  --demod_use_ground                      true
% 19.66/2.99  --sup_to_prop_solver                    passive
% 19.66/2.99  --sup_prop_simpl_new                    true
% 19.66/2.99  --sup_prop_simpl_given                  true
% 19.66/2.99  --sup_fun_splitting                     true
% 19.66/2.99  --sup_smt_interval                      50000
% 19.66/2.99  
% 19.66/2.99  ------ Superposition Simplification Setup
% 19.66/2.99  
% 19.66/2.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 19.66/2.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 19.66/2.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 19.66/2.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 19.66/2.99  --sup_full_triv                         [TrivRules;PropSubs]
% 19.66/2.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 19.66/2.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 19.66/2.99  --sup_immed_triv                        [TrivRules]
% 19.66/2.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.66/2.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.66/2.99  --sup_immed_bw_main                     []
% 19.66/2.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 19.66/2.99  --sup_input_triv                        [Unflattening;TrivRules]
% 19.66/2.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.66/2.99  --sup_input_bw                          []
% 19.66/2.99  
% 19.66/2.99  ------ Combination Options
% 19.66/2.99  
% 19.66/2.99  --comb_res_mult                         3
% 19.66/2.99  --comb_sup_mult                         2
% 19.66/2.99  --comb_inst_mult                        10
% 19.66/2.99  
% 19.66/2.99  ------ Debug Options
% 19.66/2.99  
% 19.66/2.99  --dbg_backtrace                         false
% 19.66/2.99  --dbg_dump_prop_clauses                 false
% 19.66/2.99  --dbg_dump_prop_clauses_file            -
% 19.66/2.99  --dbg_out_stat                          false
% 19.66/2.99  ------ Parsing...
% 19.66/2.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.66/2.99  
% 19.66/2.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 19.66/2.99  
% 19.66/2.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.66/2.99  
% 19.66/2.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.66/2.99  ------ Proving...
% 19.66/2.99  ------ Problem Properties 
% 19.66/2.99  
% 19.66/2.99  
% 19.66/2.99  clauses                                 17
% 19.66/2.99  conjectures                             2
% 19.66/2.99  EPR                                     2
% 19.66/2.99  Horn                                    17
% 19.66/2.99  unary                                   3
% 19.66/2.99  binary                                  8
% 19.66/2.99  lits                                    39
% 19.66/2.99  lits eq                                 7
% 19.66/2.99  fd_pure                                 0
% 19.66/2.99  fd_pseudo                               0
% 19.66/2.99  fd_cond                                 0
% 19.66/2.99  fd_pseudo_cond                          1
% 19.66/2.99  AC symbols                              0
% 19.66/2.99  
% 19.66/2.99  ------ Schedule dynamic 5 is on 
% 19.66/2.99  
% 19.66/2.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 19.66/2.99  
% 19.66/2.99  
% 19.66/2.99  ------ 
% 19.66/2.99  Current options:
% 19.66/2.99  ------ 
% 19.66/2.99  
% 19.66/2.99  ------ Input Options
% 19.66/2.99  
% 19.66/2.99  --out_options                           all
% 19.66/2.99  --tptp_safe_out                         true
% 19.66/2.99  --problem_path                          ""
% 19.66/2.99  --include_path                          ""
% 19.66/2.99  --clausifier                            res/vclausify_rel
% 19.66/2.99  --clausifier_options                    ""
% 19.66/2.99  --stdin                                 false
% 19.66/2.99  --stats_out                             all
% 19.66/2.99  
% 19.66/2.99  ------ General Options
% 19.66/2.99  
% 19.66/2.99  --fof                                   false
% 19.66/2.99  --time_out_real                         305.
% 19.66/2.99  --time_out_virtual                      -1.
% 19.66/2.99  --symbol_type_check                     false
% 19.66/2.99  --clausify_out                          false
% 19.66/2.99  --sig_cnt_out                           false
% 19.66/2.99  --trig_cnt_out                          false
% 19.66/2.99  --trig_cnt_out_tolerance                1.
% 19.66/2.99  --trig_cnt_out_sk_spl                   false
% 19.66/2.99  --abstr_cl_out                          false
% 19.66/2.99  
% 19.66/2.99  ------ Global Options
% 19.66/2.99  
% 19.66/2.99  --schedule                              default
% 19.66/2.99  --add_important_lit                     false
% 19.66/2.99  --prop_solver_per_cl                    1000
% 19.66/2.99  --min_unsat_core                        false
% 19.66/2.99  --soft_assumptions                      false
% 19.66/2.99  --soft_lemma_size                       3
% 19.66/2.99  --prop_impl_unit_size                   0
% 19.66/2.99  --prop_impl_unit                        []
% 19.66/2.99  --share_sel_clauses                     true
% 19.66/2.99  --reset_solvers                         false
% 19.66/2.99  --bc_imp_inh                            [conj_cone]
% 19.66/2.99  --conj_cone_tolerance                   3.
% 19.66/2.99  --extra_neg_conj                        none
% 19.66/2.99  --large_theory_mode                     true
% 19.66/2.99  --prolific_symb_bound                   200
% 19.66/2.99  --lt_threshold                          2000
% 19.66/2.99  --clause_weak_htbl                      true
% 19.66/2.99  --gc_record_bc_elim                     false
% 19.66/2.99  
% 19.66/2.99  ------ Preprocessing Options
% 19.66/2.99  
% 19.66/2.99  --preprocessing_flag                    true
% 19.66/2.99  --time_out_prep_mult                    0.1
% 19.66/2.99  --splitting_mode                        input
% 19.66/2.99  --splitting_grd                         true
% 19.66/2.99  --splitting_cvd                         false
% 19.66/2.99  --splitting_cvd_svl                     false
% 19.66/2.99  --splitting_nvd                         32
% 19.66/2.99  --sub_typing                            true
% 19.66/2.99  --prep_gs_sim                           true
% 19.66/2.99  --prep_unflatten                        true
% 19.66/2.99  --prep_res_sim                          true
% 19.66/2.99  --prep_upred                            true
% 19.66/2.99  --prep_sem_filter                       exhaustive
% 19.66/2.99  --prep_sem_filter_out                   false
% 19.66/2.99  --pred_elim                             true
% 19.66/2.99  --res_sim_input                         true
% 19.66/2.99  --eq_ax_congr_red                       true
% 19.66/2.99  --pure_diseq_elim                       true
% 19.66/2.99  --brand_transform                       false
% 19.66/2.99  --non_eq_to_eq                          false
% 19.66/2.99  --prep_def_merge                        true
% 19.66/2.99  --prep_def_merge_prop_impl              false
% 19.66/2.99  --prep_def_merge_mbd                    true
% 19.66/2.99  --prep_def_merge_tr_red                 false
% 19.66/2.99  --prep_def_merge_tr_cl                  false
% 19.66/2.99  --smt_preprocessing                     true
% 19.66/2.99  --smt_ac_axioms                         fast
% 19.66/2.99  --preprocessed_out                      false
% 19.66/2.99  --preprocessed_stats                    false
% 19.66/2.99  
% 19.66/2.99  ------ Abstraction refinement Options
% 19.66/2.99  
% 19.66/2.99  --abstr_ref                             []
% 19.66/2.99  --abstr_ref_prep                        false
% 19.66/2.99  --abstr_ref_until_sat                   false
% 19.66/2.99  --abstr_ref_sig_restrict                funpre
% 19.66/2.99  --abstr_ref_af_restrict_to_split_sk     false
% 19.66/2.99  --abstr_ref_under                       []
% 19.66/2.99  
% 19.66/2.99  ------ SAT Options
% 19.66/2.99  
% 19.66/2.99  --sat_mode                              false
% 19.66/2.99  --sat_fm_restart_options                ""
% 19.66/2.99  --sat_gr_def                            false
% 19.66/2.99  --sat_epr_types                         true
% 19.66/2.99  --sat_non_cyclic_types                  false
% 19.66/2.99  --sat_finite_models                     false
% 19.66/2.99  --sat_fm_lemmas                         false
% 19.66/2.99  --sat_fm_prep                           false
% 19.66/2.99  --sat_fm_uc_incr                        true
% 19.66/2.99  --sat_out_model                         small
% 19.66/2.99  --sat_out_clauses                       false
% 19.66/2.99  
% 19.66/2.99  ------ QBF Options
% 19.66/2.99  
% 19.66/2.99  --qbf_mode                              false
% 19.66/2.99  --qbf_elim_univ                         false
% 19.66/2.99  --qbf_dom_inst                          none
% 19.66/2.99  --qbf_dom_pre_inst                      false
% 19.66/2.99  --qbf_sk_in                             false
% 19.66/2.99  --qbf_pred_elim                         true
% 19.66/2.99  --qbf_split                             512
% 19.66/2.99  
% 19.66/2.99  ------ BMC1 Options
% 19.66/2.99  
% 19.66/2.99  --bmc1_incremental                      false
% 19.66/2.99  --bmc1_axioms                           reachable_all
% 19.66/2.99  --bmc1_min_bound                        0
% 19.66/2.99  --bmc1_max_bound                        -1
% 19.66/2.99  --bmc1_max_bound_default                -1
% 19.66/2.99  --bmc1_symbol_reachability              true
% 19.66/2.99  --bmc1_property_lemmas                  false
% 19.66/2.99  --bmc1_k_induction                      false
% 19.66/2.99  --bmc1_non_equiv_states                 false
% 19.66/2.99  --bmc1_deadlock                         false
% 19.66/2.99  --bmc1_ucm                              false
% 19.66/2.99  --bmc1_add_unsat_core                   none
% 19.66/2.99  --bmc1_unsat_core_children              false
% 19.66/2.99  --bmc1_unsat_core_extrapolate_axioms    false
% 19.66/2.99  --bmc1_out_stat                         full
% 19.66/2.99  --bmc1_ground_init                      false
% 19.66/2.99  --bmc1_pre_inst_next_state              false
% 19.66/2.99  --bmc1_pre_inst_state                   false
% 19.66/2.99  --bmc1_pre_inst_reach_state             false
% 19.66/2.99  --bmc1_out_unsat_core                   false
% 19.66/2.99  --bmc1_aig_witness_out                  false
% 19.66/2.99  --bmc1_verbose                          false
% 19.66/2.99  --bmc1_dump_clauses_tptp                false
% 19.66/2.99  --bmc1_dump_unsat_core_tptp             false
% 19.66/2.99  --bmc1_dump_file                        -
% 19.66/2.99  --bmc1_ucm_expand_uc_limit              128
% 19.66/2.99  --bmc1_ucm_n_expand_iterations          6
% 19.66/2.99  --bmc1_ucm_extend_mode                  1
% 19.66/2.99  --bmc1_ucm_init_mode                    2
% 19.66/2.99  --bmc1_ucm_cone_mode                    none
% 19.66/2.99  --bmc1_ucm_reduced_relation_type        0
% 19.66/2.99  --bmc1_ucm_relax_model                  4
% 19.66/2.99  --bmc1_ucm_full_tr_after_sat            true
% 19.66/2.99  --bmc1_ucm_expand_neg_assumptions       false
% 19.66/2.99  --bmc1_ucm_layered_model                none
% 19.66/2.99  --bmc1_ucm_max_lemma_size               10
% 19.66/2.99  
% 19.66/2.99  ------ AIG Options
% 19.66/2.99  
% 19.66/2.99  --aig_mode                              false
% 19.66/2.99  
% 19.66/2.99  ------ Instantiation Options
% 19.66/2.99  
% 19.66/2.99  --instantiation_flag                    true
% 19.66/2.99  --inst_sos_flag                         true
% 19.66/2.99  --inst_sos_phase                        true
% 19.66/2.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.66/2.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.66/2.99  --inst_lit_sel_side                     none
% 19.66/2.99  --inst_solver_per_active                1400
% 19.66/2.99  --inst_solver_calls_frac                1.
% 19.66/2.99  --inst_passive_queue_type               priority_queues
% 19.66/2.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.66/2.99  --inst_passive_queues_freq              [25;2]
% 19.66/2.99  --inst_dismatching                      true
% 19.66/2.99  --inst_eager_unprocessed_to_passive     true
% 19.66/2.99  --inst_prop_sim_given                   true
% 19.66/2.99  --inst_prop_sim_new                     false
% 19.66/2.99  --inst_subs_new                         false
% 19.66/2.99  --inst_eq_res_simp                      false
% 19.66/2.99  --inst_subs_given                       false
% 19.66/2.99  --inst_orphan_elimination               true
% 19.66/2.99  --inst_learning_loop_flag               true
% 19.66/2.99  --inst_learning_start                   3000
% 19.66/2.99  --inst_learning_factor                  2
% 19.66/2.99  --inst_start_prop_sim_after_learn       3
% 19.66/2.99  --inst_sel_renew                        solver
% 19.66/2.99  --inst_lit_activity_flag                true
% 19.66/2.99  --inst_restr_to_given                   false
% 19.66/2.99  --inst_activity_threshold               500
% 19.66/2.99  --inst_out_proof                        true
% 19.66/2.99  
% 19.66/2.99  ------ Resolution Options
% 19.66/2.99  
% 19.66/2.99  --resolution_flag                       false
% 19.66/2.99  --res_lit_sel                           adaptive
% 19.66/2.99  --res_lit_sel_side                      none
% 19.66/2.99  --res_ordering                          kbo
% 19.66/2.99  --res_to_prop_solver                    active
% 19.66/2.99  --res_prop_simpl_new                    false
% 19.66/2.99  --res_prop_simpl_given                  true
% 19.66/2.99  --res_passive_queue_type                priority_queues
% 19.66/2.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.66/2.99  --res_passive_queues_freq               [15;5]
% 19.66/2.99  --res_forward_subs                      full
% 19.66/2.99  --res_backward_subs                     full
% 19.66/2.99  --res_forward_subs_resolution           true
% 19.66/2.99  --res_backward_subs_resolution          true
% 19.66/2.99  --res_orphan_elimination                true
% 19.66/2.99  --res_time_limit                        2.
% 19.66/2.99  --res_out_proof                         true
% 19.66/2.99  
% 19.66/2.99  ------ Superposition Options
% 19.66/2.99  
% 19.66/2.99  --superposition_flag                    true
% 19.66/2.99  --sup_passive_queue_type                priority_queues
% 19.66/2.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.66/2.99  --sup_passive_queues_freq               [8;1;4]
% 19.66/2.99  --demod_completeness_check              fast
% 19.66/2.99  --demod_use_ground                      true
% 19.66/2.99  --sup_to_prop_solver                    passive
% 19.66/2.99  --sup_prop_simpl_new                    true
% 19.66/2.99  --sup_prop_simpl_given                  true
% 19.66/2.99  --sup_fun_splitting                     true
% 19.66/2.99  --sup_smt_interval                      50000
% 19.66/2.99  
% 19.66/2.99  ------ Superposition Simplification Setup
% 19.66/2.99  
% 19.66/2.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 19.66/2.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 19.66/2.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 19.66/2.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 19.66/2.99  --sup_full_triv                         [TrivRules;PropSubs]
% 19.66/2.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 19.66/2.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 19.66/2.99  --sup_immed_triv                        [TrivRules]
% 19.66/2.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.66/2.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.66/2.99  --sup_immed_bw_main                     []
% 19.66/2.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 19.66/2.99  --sup_input_triv                        [Unflattening;TrivRules]
% 19.66/2.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.66/2.99  --sup_input_bw                          []
% 19.66/2.99  
% 19.66/2.99  ------ Combination Options
% 19.66/2.99  
% 19.66/2.99  --comb_res_mult                         3
% 19.66/2.99  --comb_sup_mult                         2
% 19.66/2.99  --comb_inst_mult                        10
% 19.66/2.99  
% 19.66/2.99  ------ Debug Options
% 19.66/2.99  
% 19.66/2.99  --dbg_backtrace                         false
% 19.66/2.99  --dbg_dump_prop_clauses                 false
% 19.66/2.99  --dbg_dump_prop_clauses_file            -
% 19.66/2.99  --dbg_out_stat                          false
% 19.66/2.99  
% 19.66/2.99  
% 19.66/2.99  
% 19.66/2.99  
% 19.66/2.99  ------ Proving...
% 19.66/2.99  
% 19.66/2.99  
% 19.66/2.99  % SZS status Theorem for theBenchmark.p
% 19.66/2.99  
% 19.66/2.99  % SZS output start CNFRefutation for theBenchmark.p
% 19.66/2.99  
% 19.66/2.99  fof(f14,conjecture,(
% 19.66/2.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k2_tops_1(X0,k2_tops_1(X0,X1)),k2_tops_1(X0,X1))))),
% 19.66/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.66/2.99  
% 19.66/2.99  fof(f15,negated_conjecture,(
% 19.66/2.99    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k2_tops_1(X0,k2_tops_1(X0,X1)),k2_tops_1(X0,X1))))),
% 19.66/2.99    inference(negated_conjecture,[],[f14])).
% 19.66/2.99  
% 19.66/2.99  fof(f32,plain,(
% 19.66/2.99    ? [X0] : (? [X1] : (~r1_tarski(k2_tops_1(X0,k2_tops_1(X0,X1)),k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 19.66/2.99    inference(ennf_transformation,[],[f15])).
% 19.66/2.99  
% 19.66/2.99  fof(f37,plain,(
% 19.66/2.99    ( ! [X0] : (? [X1] : (~r1_tarski(k2_tops_1(X0,k2_tops_1(X0,X1)),k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~r1_tarski(k2_tops_1(X0,k2_tops_1(X0,sK1)),k2_tops_1(X0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 19.66/2.99    introduced(choice_axiom,[])).
% 19.66/2.99  
% 19.66/2.99  fof(f36,plain,(
% 19.66/2.99    ? [X0] : (? [X1] : (~r1_tarski(k2_tops_1(X0,k2_tops_1(X0,X1)),k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (~r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,X1)),k2_tops_1(sK0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 19.66/2.99    introduced(choice_axiom,[])).
% 19.66/2.99  
% 19.66/2.99  fof(f38,plain,(
% 19.66/2.99    (~r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 19.66/2.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f32,f37,f36])).
% 19.66/2.99  
% 19.66/2.99  fof(f56,plain,(
% 19.66/2.99    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 19.66/2.99    inference(cnf_transformation,[],[f38])).
% 19.66/2.99  
% 19.66/2.99  fof(f12,axiom,(
% 19.66/2.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))))),
% 19.66/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.66/2.99  
% 19.66/2.99  fof(f30,plain,(
% 19.66/2.99    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 19.66/2.99    inference(ennf_transformation,[],[f12])).
% 19.66/2.99  
% 19.66/2.99  fof(f53,plain,(
% 19.66/2.99    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 19.66/2.99    inference(cnf_transformation,[],[f30])).
% 19.66/2.99  
% 19.66/2.99  fof(f55,plain,(
% 19.66/2.99    l1_pre_topc(sK0)),
% 19.66/2.99    inference(cnf_transformation,[],[f38])).
% 19.66/2.99  
% 19.66/2.99  fof(f11,axiom,(
% 19.66/2.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 19.66/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.66/2.99  
% 19.66/2.99  fof(f28,plain,(
% 19.66/2.99    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 19.66/2.99    inference(ennf_transformation,[],[f11])).
% 19.66/2.99  
% 19.66/2.99  fof(f29,plain,(
% 19.66/2.99    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 19.66/2.99    inference(flattening,[],[f28])).
% 19.66/2.99  
% 19.66/2.99  fof(f52,plain,(
% 19.66/2.99    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 19.66/2.99    inference(cnf_transformation,[],[f29])).
% 19.66/2.99  
% 19.66/2.99  fof(f2,axiom,(
% 19.66/2.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1))),
% 19.66/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.66/2.99  
% 19.66/2.99  fof(f16,plain,(
% 19.66/2.99    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 19.66/2.99    inference(ennf_transformation,[],[f2])).
% 19.66/2.99  
% 19.66/2.99  fof(f17,plain,(
% 19.66/2.99    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 19.66/2.99    inference(flattening,[],[f16])).
% 19.66/2.99  
% 19.66/2.99  fof(f42,plain,(
% 19.66/2.99    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 19.66/2.99    inference(cnf_transformation,[],[f17])).
% 19.66/2.99  
% 19.66/2.99  fof(f13,axiom,(
% 19.66/2.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)))),
% 19.66/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.66/2.99  
% 19.66/2.99  fof(f31,plain,(
% 19.66/2.99    ! [X0] : (! [X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 19.66/2.99    inference(ennf_transformation,[],[f13])).
% 19.66/2.99  
% 19.66/2.99  fof(f54,plain,(
% 19.66/2.99    ( ! [X0,X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 19.66/2.99    inference(cnf_transformation,[],[f31])).
% 19.66/2.99  
% 19.66/2.99  fof(f6,axiom,(
% 19.66/2.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))))),
% 19.66/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.66/2.99  
% 19.66/2.99  fof(f21,plain,(
% 19.66/2.99    ! [X0,X1] : (! [X2] : (r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 19.66/2.99    inference(ennf_transformation,[],[f6])).
% 19.66/2.99  
% 19.66/2.99  fof(f47,plain,(
% 19.66/2.99    ( ! [X2,X0,X1] : (r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 19.66/2.99    inference(cnf_transformation,[],[f21])).
% 19.66/2.99  
% 19.66/2.99  fof(f1,axiom,(
% 19.66/2.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 19.66/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.66/2.99  
% 19.66/2.99  fof(f33,plain,(
% 19.66/2.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 19.66/2.99    inference(nnf_transformation,[],[f1])).
% 19.66/2.99  
% 19.66/2.99  fof(f34,plain,(
% 19.66/2.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 19.66/2.99    inference(flattening,[],[f33])).
% 19.66/2.99  
% 19.66/2.99  fof(f41,plain,(
% 19.66/2.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 19.66/2.99    inference(cnf_transformation,[],[f34])).
% 19.66/2.99  
% 19.66/2.99  fof(f7,axiom,(
% 19.66/2.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 19.66/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.66/2.99  
% 19.66/2.99  fof(f22,plain,(
% 19.66/2.99    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 19.66/2.99    inference(ennf_transformation,[],[f7])).
% 19.66/2.99  
% 19.66/2.99  fof(f23,plain,(
% 19.66/2.99    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 19.66/2.99    inference(flattening,[],[f22])).
% 19.66/2.99  
% 19.66/2.99  fof(f48,plain,(
% 19.66/2.99    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 19.66/2.99    inference(cnf_transformation,[],[f23])).
% 19.66/2.99  
% 19.66/2.99  fof(f3,axiom,(
% 19.66/2.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 19.66/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.66/2.99  
% 19.66/2.99  fof(f18,plain,(
% 19.66/2.99    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 19.66/2.99    inference(ennf_transformation,[],[f3])).
% 19.66/2.99  
% 19.66/2.99  fof(f43,plain,(
% 19.66/2.99    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 19.66/2.99    inference(cnf_transformation,[],[f18])).
% 19.66/2.99  
% 19.66/2.99  fof(f8,axiom,(
% 19.66/2.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)))),
% 19.66/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.66/2.99  
% 19.66/2.99  fof(f24,plain,(
% 19.66/2.99    ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 19.66/2.99    inference(ennf_transformation,[],[f8])).
% 19.66/2.99  
% 19.66/2.99  fof(f25,plain,(
% 19.66/2.99    ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 19.66/2.99    inference(flattening,[],[f24])).
% 19.66/2.99  
% 19.66/2.99  fof(f49,plain,(
% 19.66/2.99    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 19.66/2.99    inference(cnf_transformation,[],[f25])).
% 19.66/2.99  
% 19.66/2.99  fof(f9,axiom,(
% 19.66/2.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))))))),
% 19.66/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.66/2.99  
% 19.66/2.99  fof(f26,plain,(
% 19.66/2.99    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 19.66/2.99    inference(ennf_transformation,[],[f9])).
% 19.66/2.99  
% 19.66/2.99  fof(f50,plain,(
% 19.66/2.99    ( ! [X2,X0,X1] : (r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 19.66/2.99    inference(cnf_transformation,[],[f26])).
% 19.66/2.99  
% 19.66/2.99  fof(f10,axiom,(
% 19.66/2.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k2_tops_1(X0,X1)))),
% 19.66/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.66/2.99  
% 19.66/2.99  fof(f27,plain,(
% 19.66/2.99    ! [X0] : (! [X1] : (k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 19.66/2.99    inference(ennf_transformation,[],[f10])).
% 19.66/2.99  
% 19.66/2.99  fof(f51,plain,(
% 19.66/2.99    ( ! [X0,X1] : (k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 19.66/2.99    inference(cnf_transformation,[],[f27])).
% 19.66/2.99  
% 19.66/2.99  fof(f5,axiom,(
% 19.66/2.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 19.66/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.66/2.99  
% 19.66/2.99  fof(f20,plain,(
% 19.66/2.99    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 19.66/2.99    inference(ennf_transformation,[],[f5])).
% 19.66/2.99  
% 19.66/2.99  fof(f35,plain,(
% 19.66/2.99    ! [X0,X1] : (! [X2] : (((r1_tarski(X1,X2) | ~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 19.66/2.99    inference(nnf_transformation,[],[f20])).
% 19.66/2.99  
% 19.66/2.99  fof(f45,plain,(
% 19.66/2.99    ( ! [X2,X0,X1] : (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 19.66/2.99    inference(cnf_transformation,[],[f35])).
% 19.66/2.99  
% 19.66/2.99  fof(f4,axiom,(
% 19.66/2.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 19.66/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.66/2.99  
% 19.66/2.99  fof(f19,plain,(
% 19.66/2.99    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 19.66/2.99    inference(ennf_transformation,[],[f4])).
% 19.66/2.99  
% 19.66/2.99  fof(f44,plain,(
% 19.66/2.99    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 19.66/2.99    inference(cnf_transformation,[],[f19])).
% 19.66/2.99  
% 19.66/2.99  fof(f46,plain,(
% 19.66/2.99    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 19.66/2.99    inference(cnf_transformation,[],[f35])).
% 19.66/2.99  
% 19.66/2.99  fof(f57,plain,(
% 19.66/2.99    ~r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1))),
% 19.66/2.99    inference(cnf_transformation,[],[f38])).
% 19.66/2.99  
% 19.66/2.99  cnf(c_17,negated_conjecture,
% 19.66/2.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 19.66/2.99      inference(cnf_transformation,[],[f56]) ).
% 19.66/2.99  
% 19.66/2.99  cnf(c_743,plain,
% 19.66/2.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 19.66/2.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 19.66/2.99  
% 19.66/2.99  cnf(c_14,plain,
% 19.66/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.66/2.99      | ~ l1_pre_topc(X1)
% 19.66/2.99      | k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X0)) = k2_tops_1(X1,X0) ),
% 19.66/2.99      inference(cnf_transformation,[],[f53]) ).
% 19.66/2.99  
% 19.66/2.99  cnf(c_18,negated_conjecture,
% 19.66/2.99      ( l1_pre_topc(sK0) ),
% 19.66/2.99      inference(cnf_transformation,[],[f55]) ).
% 19.66/2.99  
% 19.66/2.99  cnf(c_224,plain,
% 19.66/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.66/2.99      | k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X0)) = k2_tops_1(X1,X0)
% 19.66/2.99      | sK0 != X1 ),
% 19.66/2.99      inference(resolution_lifted,[status(thm)],[c_14,c_18]) ).
% 19.66/2.99  
% 19.66/2.99  cnf(c_225,plain,
% 19.66/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 19.66/2.99      | k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k2_tops_1(sK0,X0) ),
% 19.66/2.99      inference(unflattening,[status(thm)],[c_224]) ).
% 19.66/2.99  
% 19.66/2.99  cnf(c_741,plain,
% 19.66/2.99      ( k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k2_tops_1(sK0,X0)
% 19.66/2.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 19.66/2.99      inference(predicate_to_equality,[status(thm)],[c_225]) ).
% 19.66/2.99  
% 19.66/2.99  cnf(c_1131,plain,
% 19.66/2.99      ( k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_tops_1(sK0,sK1) ),
% 19.66/2.99      inference(superposition,[status(thm)],[c_743,c_741]) ).
% 19.66/2.99  
% 19.66/2.99  cnf(c_13,plain,
% 19.66/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.66/2.99      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 19.66/2.99      | ~ l1_pre_topc(X1) ),
% 19.66/2.99      inference(cnf_transformation,[],[f52]) ).
% 19.66/2.99  
% 19.66/2.99  cnf(c_236,plain,
% 19.66/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.66/2.99      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 19.66/2.99      | sK0 != X1 ),
% 19.66/2.99      inference(resolution_lifted,[status(thm)],[c_13,c_18]) ).
% 19.66/2.99  
% 19.66/2.99  cnf(c_237,plain,
% 19.66/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 19.66/2.99      | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 19.66/2.99      inference(unflattening,[status(thm)],[c_236]) ).
% 19.66/2.99  
% 19.66/2.99  cnf(c_740,plain,
% 19.66/2.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 19.66/2.99      | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 19.66/2.99      inference(predicate_to_equality,[status(thm)],[c_237]) ).
% 19.66/2.99  
% 19.66/2.99  cnf(c_1140,plain,
% 19.66/2.99      ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 19.66/2.99      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 19.66/2.99      inference(superposition,[status(thm)],[c_1131,c_740]) ).
% 19.66/2.99  
% 19.66/2.99  cnf(c_20,plain,
% 19.66/2.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 19.66/2.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 19.66/2.99  
% 19.66/2.99  cnf(c_789,plain,
% 19.66/2.99      ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 19.66/2.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 19.66/2.99      inference(instantiation,[status(thm)],[c_237]) ).
% 19.66/2.99  
% 19.66/2.99  cnf(c_790,plain,
% 19.66/2.99      ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 19.66/2.99      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 19.66/2.99      inference(predicate_to_equality,[status(thm)],[c_789]) ).
% 19.66/2.99  
% 19.66/2.99  cnf(c_1837,plain,
% 19.66/2.99      ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 19.66/2.99      inference(global_propositional_subsumption,
% 19.66/2.99                [status(thm)],
% 19.66/2.99                [c_1140,c_20,c_790]) ).
% 19.66/2.99  
% 19.66/2.99  cnf(c_1844,plain,
% 19.66/2.99      ( k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) = k2_tops_1(sK0,k2_tops_1(sK0,sK1)) ),
% 19.66/2.99      inference(superposition,[status(thm)],[c_1837,c_741]) ).
% 19.66/2.99  
% 19.66/2.99  cnf(c_2441,plain,
% 19.66/2.99      ( m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 19.66/2.99      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 19.66/2.99      inference(superposition,[status(thm)],[c_1844,c_740]) ).
% 19.66/2.99  
% 19.66/2.99  cnf(c_843,plain,
% 19.66/2.99      ( m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
% 19.66/2.99      | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 19.66/2.99      inference(instantiation,[status(thm)],[c_237]) ).
% 19.66/2.99  
% 19.66/2.99  cnf(c_844,plain,
% 19.66/2.99      ( m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 19.66/2.99      | m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 19.66/2.99      inference(predicate_to_equality,[status(thm)],[c_843]) ).
% 19.66/2.99  
% 19.66/2.99  cnf(c_3675,plain,
% 19.66/2.99      ( m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 19.66/2.99      inference(global_propositional_subsumption,
% 19.66/2.99                [status(thm)],
% 19.66/2.99                [c_2441,c_20,c_790,c_844]) ).
% 19.66/2.99  
% 19.66/2.99  cnf(c_3,plain,
% 19.66/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 19.66/2.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 19.66/2.99      | k4_subset_1(X1,X0,X2) = k4_subset_1(X1,X2,X0) ),
% 19.66/2.99      inference(cnf_transformation,[],[f42]) ).
% 19.66/2.99  
% 19.66/2.99  cnf(c_750,plain,
% 19.66/2.99      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
% 19.66/2.99      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 19.66/2.99      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
% 19.66/2.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 19.66/2.99  
% 19.66/2.99  cnf(c_1958,plain,
% 19.66/2.99      ( k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),X0)
% 19.66/2.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 19.66/2.99      inference(superposition,[status(thm)],[c_1837,c_750]) ).
% 19.66/2.99  
% 19.66/2.99  cnf(c_3688,plain,
% 19.66/2.99      ( k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_tops_1(sK0,k2_tops_1(sK0,sK1))) ),
% 19.66/2.99      inference(superposition,[status(thm)],[c_3675,c_1958]) ).
% 19.66/2.99  
% 19.66/2.99  cnf(c_15,plain,
% 19.66/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.66/2.99      | ~ l1_pre_topc(X1)
% 19.66/2.99      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
% 19.66/2.99      inference(cnf_transformation,[],[f54]) ).
% 19.66/2.99  
% 19.66/2.99  cnf(c_212,plain,
% 19.66/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.66/2.99      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0)
% 19.66/2.99      | sK0 != X1 ),
% 19.66/2.99      inference(resolution_lifted,[status(thm)],[c_15,c_18]) ).
% 19.66/2.99  
% 19.66/2.99  cnf(c_213,plain,
% 19.66/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 19.66/2.99      | k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0) ),
% 19.66/2.99      inference(unflattening,[status(thm)],[c_212]) ).
% 19.66/2.99  
% 19.66/2.99  cnf(c_742,plain,
% 19.66/2.99      ( k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0)
% 19.66/2.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 19.66/2.99      inference(predicate_to_equality,[status(thm)],[c_213]) ).
% 19.66/2.99  
% 19.66/2.99  cnf(c_1843,plain,
% 19.66/2.99      ( k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k2_pre_topc(sK0,k2_tops_1(sK0,sK1)) ),
% 19.66/2.99      inference(superposition,[status(thm)],[c_1837,c_742]) ).
% 19.66/2.99  
% 19.66/2.99  cnf(c_3702,plain,
% 19.66/2.99      ( k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k2_tops_1(sK0,sK1)) ),
% 19.66/2.99      inference(light_normalisation,[status(thm)],[c_3688,c_1843]) ).
% 19.66/2.99  
% 19.66/2.99  cnf(c_8,plain,
% 19.66/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 19.66/2.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 19.66/2.99      | r1_tarski(k3_subset_1(X1,k4_subset_1(X1,X2,X0)),k3_subset_1(X1,X2)) ),
% 19.66/2.99      inference(cnf_transformation,[],[f47]) ).
% 19.66/2.99  
% 19.66/2.99  cnf(c_745,plain,
% 19.66/2.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 19.66/2.99      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 19.66/2.99      | r1_tarski(k3_subset_1(X1,k4_subset_1(X1,X2,X0)),k3_subset_1(X1,X2)) = iProver_top ),
% 19.66/2.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 19.66/2.99  
% 19.66/2.99  cnf(c_2694,plain,
% 19.66/2.99      ( m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 19.66/2.99      | m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 19.66/2.99      | r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1))),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) = iProver_top ),
% 19.66/2.99      inference(superposition,[status(thm)],[c_1843,c_745]) ).
% 19.66/2.99  
% 19.66/2.99  cnf(c_24670,plain,
% 19.66/2.99      ( r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1))),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) = iProver_top ),
% 19.66/2.99      inference(global_propositional_subsumption,
% 19.66/2.99                [status(thm)],
% 19.66/2.99                [c_2694,c_20,c_790,c_844]) ).
% 19.66/2.99  
% 19.66/2.99  cnf(c_0,plain,
% 19.66/2.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 19.66/2.99      inference(cnf_transformation,[],[f41]) ).
% 19.66/2.99  
% 19.66/2.99  cnf(c_752,plain,
% 19.66/2.99      ( X0 = X1
% 19.66/2.99      | r1_tarski(X0,X1) != iProver_top
% 19.66/2.99      | r1_tarski(X1,X0) != iProver_top ),
% 19.66/2.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 19.66/2.99  
% 19.66/2.99  cnf(c_24674,plain,
% 19.66/2.99      ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1))) = k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))
% 19.66/2.99      | r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1)))) != iProver_top ),
% 19.66/2.99      inference(superposition,[status(thm)],[c_24670,c_752]) ).
% 19.66/2.99  
% 19.66/2.99  cnf(c_9,plain,
% 19.66/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.66/2.99      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 19.66/2.99      | ~ l1_pre_topc(X1) ),
% 19.66/2.99      inference(cnf_transformation,[],[f48]) ).
% 19.66/2.99  
% 19.66/2.99  cnf(c_287,plain,
% 19.66/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.66/2.99      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 19.66/2.99      | sK0 != X1 ),
% 19.66/2.99      inference(resolution_lifted,[status(thm)],[c_9,c_18]) ).
% 19.66/2.99  
% 19.66/2.99  cnf(c_288,plain,
% 19.66/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 19.66/2.99      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 19.66/2.99      inference(unflattening,[status(thm)],[c_287]) ).
% 19.66/2.99  
% 19.66/2.99  cnf(c_842,plain,
% 19.66/2.99      ( ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 19.66/2.99      | m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 19.66/2.99      inference(instantiation,[status(thm)],[c_288]) ).
% 19.66/2.99  
% 19.66/2.99  cnf(c_846,plain,
% 19.66/2.99      ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 19.66/2.99      | m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 19.66/2.99      inference(predicate_to_equality,[status(thm)],[c_842]) ).
% 19.66/2.99  
% 19.66/2.99  cnf(c_736,plain,
% 19.66/2.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 19.66/2.99      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 19.66/2.99      inference(predicate_to_equality,[status(thm)],[c_288]) ).
% 19.66/2.99  
% 19.66/2.99  cnf(c_4,plain,
% 19.66/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 19.66/2.99      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 19.66/2.99      inference(cnf_transformation,[],[f43]) ).
% 19.66/2.99  
% 19.66/2.99  cnf(c_749,plain,
% 19.66/2.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 19.66/2.99      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 19.66/2.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 19.66/2.99  
% 19.66/2.99  cnf(c_10,plain,
% 19.66/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.66/2.99      | ~ l1_pre_topc(X1)
% 19.66/2.99      | k2_pre_topc(X1,k2_pre_topc(X1,X0)) = k2_pre_topc(X1,X0) ),
% 19.66/2.99      inference(cnf_transformation,[],[f49]) ).
% 19.66/2.99  
% 19.66/2.99  cnf(c_275,plain,
% 19.66/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.66/2.99      | k2_pre_topc(X1,k2_pre_topc(X1,X0)) = k2_pre_topc(X1,X0)
% 19.66/2.99      | sK0 != X1 ),
% 19.66/2.99      inference(resolution_lifted,[status(thm)],[c_10,c_18]) ).
% 19.66/2.99  
% 19.66/2.99  cnf(c_276,plain,
% 19.66/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 19.66/2.99      | k2_pre_topc(sK0,k2_pre_topc(sK0,X0)) = k2_pre_topc(sK0,X0) ),
% 19.66/2.99      inference(unflattening,[status(thm)],[c_275]) ).
% 19.66/2.99  
% 19.66/2.99  cnf(c_737,plain,
% 19.66/2.99      ( k2_pre_topc(sK0,k2_pre_topc(sK0,X0)) = k2_pre_topc(sK0,X0)
% 19.66/2.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 19.66/2.99      inference(predicate_to_equality,[status(thm)],[c_276]) ).
% 19.66/2.99  
% 19.66/2.99  cnf(c_1381,plain,
% 19.66/2.99      ( k2_pre_topc(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))
% 19.66/2.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 19.66/2.99      inference(superposition,[status(thm)],[c_749,c_737]) ).
% 19.66/2.99  
% 19.66/2.99  cnf(c_3502,plain,
% 19.66/2.99      ( k2_pre_topc(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
% 19.66/2.99      inference(superposition,[status(thm)],[c_743,c_1381]) ).
% 19.66/2.99  
% 19.66/2.99  cnf(c_987,plain,
% 19.66/2.99      ( k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 19.66/2.99      inference(superposition,[status(thm)],[c_743,c_737]) ).
% 19.66/2.99  
% 19.66/2.99  cnf(c_11,plain,
% 19.66/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.66/2.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 19.66/2.99      | r1_tarski(k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X0,X2)),k9_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k2_pre_topc(X1,X2)))
% 19.66/2.99      | ~ l1_pre_topc(X1) ),
% 19.66/2.99      inference(cnf_transformation,[],[f50]) ).
% 19.66/2.99  
% 19.66/2.99  cnf(c_260,plain,
% 19.66/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.66/2.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 19.66/2.99      | r1_tarski(k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X0,X2)),k9_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k2_pre_topc(X1,X2)))
% 19.66/2.99      | sK0 != X1 ),
% 19.66/2.99      inference(resolution_lifted,[status(thm)],[c_11,c_18]) ).
% 19.66/2.99  
% 19.66/2.99  cnf(c_261,plain,
% 19.66/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 19.66/2.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 19.66/2.99      | r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k2_pre_topc(sK0,X1))) ),
% 19.66/2.99      inference(unflattening,[status(thm)],[c_260]) ).
% 19.66/2.99  
% 19.66/2.99  cnf(c_738,plain,
% 19.66/2.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 19.66/2.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 19.66/2.99      | r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k2_pre_topc(sK0,X1))) = iProver_top ),
% 19.66/2.99      inference(predicate_to_equality,[status(thm)],[c_261]) ).
% 19.66/2.99  
% 19.66/2.99  cnf(c_1262,plain,
% 19.66/2.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 19.66/2.99      | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 19.66/2.99      | r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X0)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X0))) = iProver_top ),
% 19.66/2.99      inference(superposition,[status(thm)],[c_987,c_738]) ).
% 19.66/2.99  
% 19.66/2.99  cnf(c_802,plain,
% 19.66/2.99      ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 19.66/2.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 19.66/2.99      inference(instantiation,[status(thm)],[c_288]) ).
% 19.66/2.99  
% 19.66/2.99  cnf(c_803,plain,
% 19.66/2.99      ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 19.66/2.99      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 19.66/2.99      inference(predicate_to_equality,[status(thm)],[c_802]) ).
% 19.66/2.99  
% 19.66/2.99  cnf(c_3526,plain,
% 19.66/2.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 19.66/2.99      | r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X0)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X0))) = iProver_top ),
% 19.66/2.99      inference(global_propositional_subsumption,
% 19.66/2.99                [status(thm)],
% 19.66/2.99                [c_1262,c_20,c_803]) ).
% 19.66/2.99  
% 19.66/2.99  cnf(c_3538,plain,
% 19.66/2.99      ( m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 19.66/2.99      | r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))) = iProver_top ),
% 19.66/2.99      inference(superposition,[status(thm)],[c_3502,c_3526]) ).
% 19.66/2.99  
% 19.66/2.99  cnf(c_12,plain,
% 19.66/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.66/2.99      | ~ l1_pre_topc(X1)
% 19.66/2.99      | k9_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k2_tops_1(X1,X0) ),
% 19.66/2.99      inference(cnf_transformation,[],[f51]) ).
% 19.66/2.99  
% 19.66/2.99  cnf(c_248,plain,
% 19.66/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.66/2.99      | k9_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k2_tops_1(X1,X0)
% 19.66/2.99      | sK0 != X1 ),
% 19.66/2.99      inference(resolution_lifted,[status(thm)],[c_12,c_18]) ).
% 19.66/2.99  
% 19.66/2.99  cnf(c_249,plain,
% 19.66/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 19.66/2.99      | k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k2_tops_1(sK0,X0) ),
% 19.66/2.99      inference(unflattening,[status(thm)],[c_248]) ).
% 19.66/2.99  
% 19.66/2.99  cnf(c_739,plain,
% 19.66/2.99      ( k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k2_tops_1(sK0,X0)
% 19.66/2.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 19.66/2.99      inference(predicate_to_equality,[status(thm)],[c_249]) ).
% 19.66/2.99  
% 19.66/2.99  cnf(c_1699,plain,
% 19.66/2.99      ( k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k2_tops_1(sK0,sK1) ),
% 19.66/2.99      inference(superposition,[status(thm)],[c_743,c_739]) ).
% 19.66/2.99  
% 19.66/2.99  cnf(c_3540,plain,
% 19.66/2.99      ( m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 19.66/2.99      | r1_tarski(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) = iProver_top ),
% 19.66/2.99      inference(light_normalisation,[status(thm)],[c_3538,c_1699]) ).
% 19.66/2.99  
% 19.66/2.99  cnf(c_3749,plain,
% 19.66/2.99      ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 19.66/2.99      | r1_tarski(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) = iProver_top ),
% 19.66/2.99      inference(superposition,[status(thm)],[c_736,c_3540]) ).
% 19.66/2.99  
% 19.66/2.99  cnf(c_1061,plain,
% 19.66/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 19.66/2.99      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 19.66/2.99      inference(instantiation,[status(thm)],[c_4]) ).
% 19.66/2.99  
% 19.66/2.99  cnf(c_5094,plain,
% 19.66/2.99      ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 19.66/2.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 19.66/2.99      inference(instantiation,[status(thm)],[c_1061]) ).
% 19.66/2.99  
% 19.66/2.99  cnf(c_5095,plain,
% 19.66/2.99      ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 19.66/2.99      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 19.66/2.99      inference(predicate_to_equality,[status(thm)],[c_5094]) ).
% 19.66/2.99  
% 19.66/2.99  cnf(c_7,plain,
% 19.66/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 19.66/2.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 19.66/2.99      | ~ r1_tarski(X2,X0)
% 19.66/2.99      | r1_tarski(k3_subset_1(X1,X0),k3_subset_1(X1,X2)) ),
% 19.66/2.99      inference(cnf_transformation,[],[f45]) ).
% 19.66/2.99  
% 19.66/2.99  cnf(c_746,plain,
% 19.66/2.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 19.66/2.99      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 19.66/2.99      | r1_tarski(X2,X0) != iProver_top
% 19.66/2.99      | r1_tarski(k3_subset_1(X1,X0),k3_subset_1(X1,X2)) = iProver_top ),
% 19.66/2.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 19.66/2.99  
% 19.66/2.99  cnf(c_2035,plain,
% 19.66/2.99      ( k3_subset_1(X0,X1) = k3_subset_1(X0,X2)
% 19.66/2.99      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
% 19.66/2.99      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 19.66/2.99      | r1_tarski(X1,X2) != iProver_top
% 19.66/2.99      | r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,X2)) != iProver_top ),
% 19.66/2.99      inference(superposition,[status(thm)],[c_746,c_752]) ).
% 19.66/2.99  
% 19.66/2.99  cnf(c_24676,plain,
% 19.66/2.99      ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1))) = k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))
% 19.66/2.99      | m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 19.66/2.99      | m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 19.66/2.99      | r1_tarski(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) != iProver_top ),
% 19.66/2.99      inference(superposition,[status(thm)],[c_24670,c_2035]) ).
% 19.66/2.99  
% 19.66/2.99  cnf(c_24684,plain,
% 19.66/2.99      ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,sK1))) = k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)) ),
% 19.66/2.99      inference(global_propositional_subsumption,
% 19.66/2.99                [status(thm)],
% 19.66/2.99                [c_24674,c_20,c_790,c_846,c_3749,c_5095,c_24676]) ).
% 19.66/2.99  
% 19.66/2.99  cnf(c_24691,plain,
% 19.66/2.99      ( m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 19.66/2.99      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 19.66/2.99      inference(superposition,[status(thm)],[c_24684,c_749]) ).
% 19.66/2.99  
% 19.66/2.99  cnf(c_5487,plain,
% 19.66/2.99      ( ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 19.66/2.99      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 19.66/2.99      inference(instantiation,[status(thm)],[c_1061]) ).
% 19.66/2.99  
% 19.66/2.99  cnf(c_5488,plain,
% 19.66/2.99      ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 19.66/2.99      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 19.66/2.99      inference(predicate_to_equality,[status(thm)],[c_5487]) ).
% 19.66/2.99  
% 19.66/2.99  cnf(c_24772,plain,
% 19.66/2.99      ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 19.66/2.99      inference(global_propositional_subsumption,
% 19.66/2.99                [status(thm)],
% 19.66/2.99                [c_24691,c_20,c_790,c_5488]) ).
% 19.66/2.99  
% 19.66/2.99  cnf(c_5,plain,
% 19.66/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 19.66/2.99      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 19.66/2.99      inference(cnf_transformation,[],[f44]) ).
% 19.66/2.99  
% 19.66/2.99  cnf(c_748,plain,
% 19.66/2.99      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 19.66/2.99      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 19.66/2.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 19.66/2.99  
% 19.66/2.99  cnf(c_1371,plain,
% 19.66/2.99      ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0))) = k2_pre_topc(sK0,X0)
% 19.66/2.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 19.66/2.99      inference(superposition,[status(thm)],[c_736,c_748]) ).
% 19.66/2.99  
% 19.66/2.99  cnf(c_2898,plain,
% 19.66/2.99      ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_pre_topc(sK0,X0)))) = k2_pre_topc(sK0,k2_pre_topc(sK0,X0))
% 19.66/2.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 19.66/2.99      inference(superposition,[status(thm)],[c_736,c_1371]) ).
% 19.66/2.99  
% 19.66/2.99  cnf(c_4368,plain,
% 19.66/2.99      ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))))) = k2_pre_topc(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)))
% 19.66/2.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 19.66/2.99      inference(superposition,[status(thm)],[c_749,c_2898]) ).
% 19.66/2.99  
% 19.66/2.99  cnf(c_24928,plain,
% 19.66/2.99      ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))))))) = k2_pre_topc(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))))) ),
% 19.66/2.99      inference(superposition,[status(thm)],[c_24772,c_4368]) ).
% 19.66/2.99  
% 19.66/2.99  cnf(c_1841,plain,
% 19.66/2.99      ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) = k2_tops_1(sK0,sK1) ),
% 19.66/2.99      inference(superposition,[status(thm)],[c_1837,c_748]) ).
% 19.66/2.99  
% 19.66/2.99  cnf(c_1845,plain,
% 19.66/2.99      ( k2_pre_topc(sK0,k2_pre_topc(sK0,k2_tops_1(sK0,sK1))) = k2_pre_topc(sK0,k2_tops_1(sK0,sK1)) ),
% 19.66/2.99      inference(superposition,[status(thm)],[c_1837,c_737]) ).
% 19.66/2.99  
% 19.66/2.99  cnf(c_25060,plain,
% 19.66/2.99      ( k2_pre_topc(sK0,k2_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 19.66/2.99      inference(light_normalisation,
% 19.66/2.99                [status(thm)],
% 19.66/2.99                [c_24928,c_1841,c_1845,c_24684]) ).
% 19.66/2.99  
% 19.66/2.99  cnf(c_65089,plain,
% 19.66/2.99      ( k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 19.66/2.99      inference(light_normalisation,
% 19.66/2.99                [status(thm)],
% 19.66/2.99                [c_3702,c_3702,c_25060]) ).
% 19.66/2.99  
% 19.66/2.99  cnf(c_65092,plain,
% 19.66/2.99      ( m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 19.66/2.99      | m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 19.66/2.99      | r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)))) = iProver_top ),
% 19.66/2.99      inference(superposition,[status(thm)],[c_65089,c_745]) ).
% 19.66/2.99  
% 19.66/2.99  cnf(c_6,plain,
% 19.66/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 19.66/2.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 19.66/2.99      | r1_tarski(X2,X0)
% 19.66/2.99      | ~ r1_tarski(k3_subset_1(X1,X0),k3_subset_1(X1,X2)) ),
% 19.66/2.99      inference(cnf_transformation,[],[f46]) ).
% 19.66/2.99  
% 19.66/2.99  cnf(c_779,plain,
% 19.66/2.99      ( ~ m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(X0))
% 19.66/2.99      | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(X0))
% 19.66/2.99      | r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1))
% 19.66/2.99      | ~ r1_tarski(k3_subset_1(X0,k2_tops_1(sK0,sK1)),k3_subset_1(X0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))) ),
% 19.66/2.99      inference(instantiation,[status(thm)],[c_6]) ).
% 19.66/2.99  
% 19.66/2.99  cnf(c_896,plain,
% 19.66/2.99      ( ~ m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
% 19.66/2.99      | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 19.66/2.99      | r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1))
% 19.66/2.99      | ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)))) ),
% 19.66/2.99      inference(instantiation,[status(thm)],[c_779]) ).
% 19.66/2.99  
% 19.66/2.99  cnf(c_897,plain,
% 19.66/2.99      ( m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 19.66/2.99      | m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 19.66/2.99      | r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) = iProver_top
% 19.66/2.99      | r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)))) != iProver_top ),
% 19.66/2.99      inference(predicate_to_equality,[status(thm)],[c_896]) ).
% 19.66/2.99  
% 19.66/2.99  cnf(c_16,negated_conjecture,
% 19.66/2.99      ( ~ r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) ),
% 19.66/2.99      inference(cnf_transformation,[],[f57]) ).
% 19.66/2.99  
% 19.66/2.99  cnf(c_21,plain,
% 19.66/2.99      ( r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) != iProver_top ),
% 19.66/2.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 19.66/2.99  
% 19.66/2.99  cnf(contradiction,plain,
% 19.66/2.99      ( $false ),
% 19.66/2.99      inference(minisat,
% 19.66/2.99                [status(thm)],
% 19.66/2.99                [c_65092,c_897,c_844,c_790,c_21,c_20]) ).
% 19.66/2.99  
% 19.66/2.99  
% 19.66/2.99  % SZS output end CNFRefutation for theBenchmark.p
% 19.66/2.99  
% 19.66/2.99  ------                               Statistics
% 19.66/2.99  
% 19.66/2.99  ------ General
% 19.66/2.99  
% 19.66/2.99  abstr_ref_over_cycles:                  0
% 19.66/2.99  abstr_ref_under_cycles:                 0
% 19.66/2.99  gc_basic_clause_elim:                   0
% 19.66/2.99  forced_gc_time:                         0
% 19.66/2.99  parsing_time:                           0.015
% 19.66/2.99  unif_index_cands_time:                  0.
% 19.66/2.99  unif_index_add_time:                    0.
% 19.66/2.99  orderings_time:                         0.
% 19.66/2.99  out_proof_time:                         0.019
% 19.66/2.99  total_time:                             2.353
% 19.66/2.99  num_of_symbols:                         43
% 19.66/2.99  num_of_terms:                           78765
% 19.66/2.99  
% 19.66/2.99  ------ Preprocessing
% 19.66/2.99  
% 19.66/2.99  num_of_splits:                          0
% 19.66/2.99  num_of_split_atoms:                     0
% 19.66/2.99  num_of_reused_defs:                     0
% 19.66/2.99  num_eq_ax_congr_red:                    4
% 19.66/2.99  num_of_sem_filtered_clauses:            1
% 19.66/2.99  num_of_subtypes:                        0
% 19.66/2.99  monotx_restored_types:                  0
% 19.66/2.99  sat_num_of_epr_types:                   0
% 19.66/2.99  sat_num_of_non_cyclic_types:            0
% 19.66/2.99  sat_guarded_non_collapsed_types:        0
% 19.66/2.99  num_pure_diseq_elim:                    0
% 19.66/2.99  simp_replaced_by:                       0
% 19.66/2.99  res_preprocessed:                       92
% 19.66/2.99  prep_upred:                             0
% 19.66/2.99  prep_unflattend:                        7
% 19.66/2.99  smt_new_axioms:                         0
% 19.66/2.99  pred_elim_cands:                        2
% 19.66/2.99  pred_elim:                              1
% 19.66/2.99  pred_elim_cl:                           1
% 19.66/2.99  pred_elim_cycles:                       3
% 19.66/2.99  merged_defs:                            0
% 19.66/2.99  merged_defs_ncl:                        0
% 19.66/2.99  bin_hyper_res:                          0
% 19.66/2.99  prep_cycles:                            4
% 19.66/2.99  pred_elim_time:                         0.003
% 19.66/2.99  splitting_time:                         0.
% 19.66/2.99  sem_filter_time:                        0.
% 19.66/2.99  monotx_time:                            0.001
% 19.66/2.99  subtype_inf_time:                       0.
% 19.66/2.99  
% 19.66/2.99  ------ Problem properties
% 19.66/2.99  
% 19.66/2.99  clauses:                                17
% 19.66/2.99  conjectures:                            2
% 19.66/2.99  epr:                                    2
% 19.66/2.99  horn:                                   17
% 19.66/2.99  ground:                                 2
% 19.66/2.99  unary:                                  3
% 19.66/2.99  binary:                                 8
% 19.66/2.99  lits:                                   39
% 19.66/2.99  lits_eq:                                7
% 19.66/2.99  fd_pure:                                0
% 19.66/2.99  fd_pseudo:                              0
% 19.66/2.99  fd_cond:                                0
% 19.66/2.99  fd_pseudo_cond:                         1
% 19.66/2.99  ac_symbols:                             0
% 19.66/2.99  
% 19.66/2.99  ------ Propositional Solver
% 19.66/2.99  
% 19.66/2.99  prop_solver_calls:                      48
% 19.66/2.99  prop_fast_solver_calls:                 2390
% 19.66/2.99  smt_solver_calls:                       0
% 19.66/2.99  smt_fast_solver_calls:                  0
% 19.66/2.99  prop_num_of_clauses:                    25234
% 19.66/2.99  prop_preprocess_simplified:             35910
% 19.66/2.99  prop_fo_subsumed:                       75
% 19.66/2.99  prop_solver_time:                       0.
% 19.66/2.99  smt_solver_time:                        0.
% 19.66/2.99  smt_fast_solver_time:                   0.
% 19.66/2.99  prop_fast_solver_time:                  0.
% 19.66/2.99  prop_unsat_core_time:                   0.002
% 19.66/2.99  
% 19.66/2.99  ------ QBF
% 19.66/2.99  
% 19.66/2.99  qbf_q_res:                              0
% 19.66/2.99  qbf_num_tautologies:                    0
% 19.66/2.99  qbf_prep_cycles:                        0
% 19.66/2.99  
% 19.66/2.99  ------ BMC1
% 19.66/2.99  
% 19.66/2.99  bmc1_current_bound:                     -1
% 19.66/2.99  bmc1_last_solved_bound:                 -1
% 19.66/2.99  bmc1_unsat_core_size:                   -1
% 19.66/2.99  bmc1_unsat_core_parents_size:           -1
% 19.66/2.99  bmc1_merge_next_fun:                    0
% 19.66/2.99  bmc1_unsat_core_clauses_time:           0.
% 19.66/2.99  
% 19.66/2.99  ------ Instantiation
% 19.66/2.99  
% 19.66/2.99  inst_num_of_clauses:                    2369
% 19.66/2.99  inst_num_in_passive:                    95
% 19.66/2.99  inst_num_in_active:                     4271
% 19.66/2.99  inst_num_in_unprocessed:                892
% 19.66/2.99  inst_num_of_loops:                      4519
% 19.66/2.99  inst_num_of_learning_restarts:          1
% 19.66/2.99  inst_num_moves_active_passive:          244
% 19.66/2.99  inst_lit_activity:                      0
% 19.66/2.99  inst_lit_activity_moves:                4
% 19.66/2.99  inst_num_tautologies:                   0
% 19.66/2.99  inst_num_prop_implied:                  0
% 19.66/2.99  inst_num_existing_simplified:           0
% 19.66/2.99  inst_num_eq_res_simplified:             0
% 19.66/2.99  inst_num_child_elim:                    0
% 19.66/2.99  inst_num_of_dismatching_blockings:      9248
% 19.66/2.99  inst_num_of_non_proper_insts:           8621
% 19.66/2.99  inst_num_of_duplicates:                 0
% 19.66/2.99  inst_inst_num_from_inst_to_res:         0
% 19.66/2.99  inst_dismatching_checking_time:         0.
% 19.66/2.99  
% 19.66/2.99  ------ Resolution
% 19.66/2.99  
% 19.66/2.99  res_num_of_clauses:                     28
% 19.66/2.99  res_num_in_passive:                     28
% 19.66/2.99  res_num_in_active:                      0
% 19.66/2.99  res_num_of_loops:                       96
% 19.66/2.99  res_forward_subset_subsumed:            544
% 19.66/2.99  res_backward_subset_subsumed:           50
% 19.66/2.99  res_forward_subsumed:                   0
% 19.66/2.99  res_backward_subsumed:                  0
% 19.66/2.99  res_forward_subsumption_resolution:     0
% 19.66/2.99  res_backward_subsumption_resolution:    0
% 19.66/2.99  res_clause_to_clause_subsumption:       20651
% 19.66/2.99  res_orphan_elimination:                 0
% 19.66/2.99  res_tautology_del:                      446
% 19.66/2.99  res_num_eq_res_simplified:              0
% 19.66/2.99  res_num_sel_changes:                    0
% 19.66/2.99  res_moves_from_active_to_pass:          0
% 19.66/2.99  
% 19.66/2.99  ------ Superposition
% 19.66/2.99  
% 19.66/2.99  sup_time_total:                         0.
% 19.66/2.99  sup_time_generating:                    0.
% 19.66/2.99  sup_time_sim_full:                      0.
% 19.66/2.99  sup_time_sim_immed:                     0.
% 19.66/2.99  
% 19.66/2.99  sup_num_of_clauses:                     4193
% 19.66/2.99  sup_num_in_active:                      897
% 19.66/2.99  sup_num_in_passive:                     3296
% 19.66/2.99  sup_num_of_loops:                       903
% 19.66/2.99  sup_fw_superposition:                   7094
% 19.66/2.99  sup_bw_superposition:                   3424
% 19.66/2.99  sup_immediate_simplified:               4157
% 19.66/2.99  sup_given_eliminated:                   0
% 19.66/2.99  comparisons_done:                       0
% 19.66/2.99  comparisons_avoided:                    0
% 19.66/2.99  
% 19.66/2.99  ------ Simplifications
% 19.66/2.99  
% 19.66/2.99  
% 19.66/2.99  sim_fw_subset_subsumed:                 11
% 19.66/2.99  sim_bw_subset_subsumed:                 6
% 19.66/2.99  sim_fw_subsumed:                        28
% 19.66/2.99  sim_bw_subsumed:                        0
% 19.66/2.99  sim_fw_subsumption_res:                 0
% 19.66/2.99  sim_bw_subsumption_res:                 0
% 19.66/2.99  sim_tautology_del:                      28
% 19.66/2.99  sim_eq_tautology_del:                   3650
% 19.66/2.99  sim_eq_res_simp:                        0
% 19.66/2.99  sim_fw_demodulated:                     61
% 19.66/2.99  sim_bw_demodulated:                     6
% 19.66/2.99  sim_light_normalised:                   4102
% 19.66/2.99  sim_joinable_taut:                      0
% 19.66/2.99  sim_joinable_simp:                      0
% 19.66/2.99  sim_ac_normalised:                      0
% 19.66/2.99  sim_smt_subsumption:                    0
% 19.66/2.99  
%------------------------------------------------------------------------------
