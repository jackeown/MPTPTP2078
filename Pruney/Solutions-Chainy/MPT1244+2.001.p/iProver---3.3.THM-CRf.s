%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:14:04 EST 2020

% Result     : Theorem 4.07s
% Output     : CNFRefutation 4.07s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 638 expanded)
%              Number of clauses        :   77 ( 222 expanded)
%              Number of leaves         :   14 ( 159 expanded)
%              Depth                    :   20
%              Number of atoms          :  362 (1907 expanded)
%              Number of equality atoms :  161 ( 606 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    6 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,k1_tops_1(X0,X1)) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,k1_tops_1(X0,X1)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => k2_pre_topc(X0,k1_tops_1(X0,X1)) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,k1_tops_1(X0,X1)))) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_pre_topc(X0,k1_tops_1(X0,X1)) != k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,k1_tops_1(X0,X1))))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k2_pre_topc(X0,k1_tops_1(X0,X1)) != k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,k1_tops_1(X0,X1))))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k2_pre_topc(X0,k1_tops_1(X0,sK1)) != k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,k1_tops_1(X0,sK1))))
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k2_pre_topc(X0,k1_tops_1(X0,X1)) != k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,k1_tops_1(X0,X1))))
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( k2_pre_topc(sK0,k1_tops_1(sK0,X1)) != k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,X1))))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) != k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f30,f29])).

fof(f44,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f31])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f43,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f6,axiom,(
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
    inference(ennf_transformation,[],[f6])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f27])).

fof(f34,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f45,plain,(
    k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) != k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))) ),
    inference(cnf_transformation,[],[f31])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_578,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,k1_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_13,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_174,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,k1_tops_1(X1,X0)) = k1_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_13])).

cnf(c_175,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,k1_tops_1(sK0,X0)) = k1_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_174])).

cnf(c_575,plain,
    ( k1_tops_1(sK0,k1_tops_1(sK0,X0)) = k1_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_175])).

cnf(c_1461,plain,
    ( k1_tops_1(sK0,k1_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_578,c_575])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_144,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_13])).

cnf(c_145,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X1,X0)
    | r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_144])).

cnf(c_577,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_145])).

cnf(c_1670,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),X0) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1461,c_577])).

cnf(c_15,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_186,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_13])).

cnf(c_187,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_186])).

cnf(c_657,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_187])).

cnf(c_658,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_657])).

cnf(c_4410,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),X0) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1670,c_15,c_658])).

cnf(c_574,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_187])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_240,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_13])).

cnf(c_241,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_240])).

cnf(c_570,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_241])).

cnf(c_1463,plain,
    ( k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,X0))) = k1_tops_1(sK0,k2_pre_topc(sK0,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_570,c_575])).

cnf(c_3102,plain,
    ( k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,X0)))) = k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,X0)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_574,c_1463])).

cnf(c_4166,plain,
    ( k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))) = k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
    inference(superposition,[status(thm)],[c_578,c_3102])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_580,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1672,plain,
    ( k1_tops_1(sK0,X0) = k1_tops_1(sK0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_577,c_580])).

cnf(c_4423,plain,
    ( k1_tops_1(sK0,X0) = k1_tops_1(sK0,sK1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4410,c_1672])).

cnf(c_7254,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | k1_tops_1(sK0,X0) = k1_tops_1(sK0,sK1)
    | r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4423,c_15])).

cnf(c_7255,plain,
    ( k1_tops_1(sK0,X0) = k1_tops_1(sK0,sK1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_7254])).

cnf(c_7265,plain,
    ( k1_tops_1(sK0,k1_tops_1(sK0,X0)) = k1_tops_1(sK0,sK1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),sK1) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_574,c_7255])).

cnf(c_14714,plain,
    ( k1_tops_1(sK0,k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))))) = k1_tops_1(sK0,sK1)
    | m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))),sK1) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4166,c_7265])).

cnf(c_14739,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = k1_tops_1(sK0,sK1)
    | m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))),sK1) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_14714,c_4166])).

cnf(c_11,negated_conjecture,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) != k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_717,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_241])).

cnf(c_721,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_717])).

cnf(c_363,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_691,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))) != X0
    | k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) != X0
    | k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))) ),
    inference(instantiation,[status(thm)],[c_363])).

cnf(c_826,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))) != k2_pre_topc(sK0,k1_tops_1(sK0,sK1))
    | k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))))
    | k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) != k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_691])).

cnf(c_362,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_827,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_362])).

cnf(c_865,plain,
    ( m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_187])).

cnf(c_866,plain,
    ( m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_865])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_162,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_13])).

cnf(c_163,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,X0),X0) ),
    inference(unflattening,[status(thm)],[c_162])).

cnf(c_576,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_163])).

cnf(c_922,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),k2_pre_topc(sK0,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_570,c_576])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k2_pre_topc(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_228,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,k2_pre_topc(X1,X0)) = k2_pre_topc(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_13])).

cnf(c_229,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k2_pre_topc(sK0,X0)) = k2_pre_topc(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_228])).

cnf(c_571,plain,
    ( k2_pre_topc(sK0,k2_pre_topc(sK0,X0)) = k2_pre_topc(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_229])).

cnf(c_1302,plain,
    ( k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,X0))) = k2_pre_topc(sK0,k1_tops_1(sK0,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_574,c_571])).

cnf(c_2517,plain,
    ( k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_578,c_1302])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k2_pre_topc(X1,X0),k2_pre_topc(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_198,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k2_pre_topc(X1,X0),k2_pre_topc(X1,X2))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_13])).

cnf(c_199,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X1,X0)
    | r1_tarski(k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_198])).

cnf(c_573,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_199])).

cnf(c_2544,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2517,c_573])).

cnf(c_7625,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2544,c_15,c_658,c_721])).

cnf(c_1112,plain,
    ( k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_573,c_580])).

cnf(c_7640,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k2_pre_topc(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7625,c_1112])).

cnf(c_12272,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k2_pre_topc(sK0,X0)
    | r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7640,c_15,c_658])).

cnf(c_12273,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k2_pre_topc(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_12272])).

cnf(c_12285,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))) = k2_pre_topc(sK0,k1_tops_1(sK0,sK1))
    | m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_922,c_12273])).

cnf(c_17410,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14739,c_15,c_11,c_658,c_721,c_826,c_827,c_866,c_12285])).

cnf(c_17417,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4410,c_17410])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_216,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,X0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_13])).

cnf(c_217,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(X0,k2_pre_topc(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_216])).

cnf(c_714,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
    inference(instantiation,[status(thm)],[c_217])).

cnf(c_727,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_714])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_17417,c_727,c_721,c_658,c_15])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:33:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 4.07/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.07/1.00  
% 4.07/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.07/1.00  
% 4.07/1.00  ------  iProver source info
% 4.07/1.00  
% 4.07/1.00  git: date: 2020-06-30 10:37:57 +0100
% 4.07/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.07/1.00  git: non_committed_changes: false
% 4.07/1.00  git: last_make_outside_of_git: false
% 4.07/1.00  
% 4.07/1.00  ------ 
% 4.07/1.00  
% 4.07/1.00  ------ Input Options
% 4.07/1.00  
% 4.07/1.00  --out_options                           all
% 4.07/1.00  --tptp_safe_out                         true
% 4.07/1.00  --problem_path                          ""
% 4.07/1.00  --include_path                          ""
% 4.07/1.00  --clausifier                            res/vclausify_rel
% 4.07/1.00  --clausifier_options                    --mode clausify
% 4.07/1.00  --stdin                                 false
% 4.07/1.00  --stats_out                             all
% 4.07/1.00  
% 4.07/1.00  ------ General Options
% 4.07/1.00  
% 4.07/1.00  --fof                                   false
% 4.07/1.00  --time_out_real                         305.
% 4.07/1.00  --time_out_virtual                      -1.
% 4.07/1.00  --symbol_type_check                     false
% 4.07/1.00  --clausify_out                          false
% 4.07/1.00  --sig_cnt_out                           false
% 4.07/1.00  --trig_cnt_out                          false
% 4.07/1.00  --trig_cnt_out_tolerance                1.
% 4.07/1.00  --trig_cnt_out_sk_spl                   false
% 4.07/1.00  --abstr_cl_out                          false
% 4.07/1.00  
% 4.07/1.00  ------ Global Options
% 4.07/1.00  
% 4.07/1.00  --schedule                              default
% 4.07/1.00  --add_important_lit                     false
% 4.07/1.00  --prop_solver_per_cl                    1000
% 4.07/1.00  --min_unsat_core                        false
% 4.07/1.00  --soft_assumptions                      false
% 4.07/1.00  --soft_lemma_size                       3
% 4.07/1.00  --prop_impl_unit_size                   0
% 4.07/1.00  --prop_impl_unit                        []
% 4.07/1.00  --share_sel_clauses                     true
% 4.07/1.00  --reset_solvers                         false
% 4.07/1.00  --bc_imp_inh                            [conj_cone]
% 4.07/1.00  --conj_cone_tolerance                   3.
% 4.07/1.00  --extra_neg_conj                        none
% 4.07/1.00  --large_theory_mode                     true
% 4.07/1.00  --prolific_symb_bound                   200
% 4.07/1.00  --lt_threshold                          2000
% 4.07/1.00  --clause_weak_htbl                      true
% 4.07/1.00  --gc_record_bc_elim                     false
% 4.07/1.00  
% 4.07/1.00  ------ Preprocessing Options
% 4.07/1.00  
% 4.07/1.00  --preprocessing_flag                    true
% 4.07/1.00  --time_out_prep_mult                    0.1
% 4.07/1.00  --splitting_mode                        input
% 4.07/1.00  --splitting_grd                         true
% 4.07/1.00  --splitting_cvd                         false
% 4.07/1.00  --splitting_cvd_svl                     false
% 4.07/1.00  --splitting_nvd                         32
% 4.07/1.00  --sub_typing                            true
% 4.07/1.00  --prep_gs_sim                           true
% 4.07/1.00  --prep_unflatten                        true
% 4.07/1.00  --prep_res_sim                          true
% 4.07/1.00  --prep_upred                            true
% 4.07/1.00  --prep_sem_filter                       exhaustive
% 4.07/1.00  --prep_sem_filter_out                   false
% 4.07/1.00  --pred_elim                             true
% 4.07/1.00  --res_sim_input                         true
% 4.07/1.00  --eq_ax_congr_red                       true
% 4.07/1.00  --pure_diseq_elim                       true
% 4.07/1.00  --brand_transform                       false
% 4.07/1.00  --non_eq_to_eq                          false
% 4.07/1.00  --prep_def_merge                        true
% 4.07/1.00  --prep_def_merge_prop_impl              false
% 4.07/1.00  --prep_def_merge_mbd                    true
% 4.07/1.00  --prep_def_merge_tr_red                 false
% 4.07/1.00  --prep_def_merge_tr_cl                  false
% 4.07/1.00  --smt_preprocessing                     true
% 4.07/1.00  --smt_ac_axioms                         fast
% 4.07/1.00  --preprocessed_out                      false
% 4.07/1.00  --preprocessed_stats                    false
% 4.07/1.00  
% 4.07/1.00  ------ Abstraction refinement Options
% 4.07/1.00  
% 4.07/1.00  --abstr_ref                             []
% 4.07/1.00  --abstr_ref_prep                        false
% 4.07/1.00  --abstr_ref_until_sat                   false
% 4.07/1.00  --abstr_ref_sig_restrict                funpre
% 4.07/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 4.07/1.00  --abstr_ref_under                       []
% 4.07/1.00  
% 4.07/1.00  ------ SAT Options
% 4.07/1.00  
% 4.07/1.00  --sat_mode                              false
% 4.07/1.00  --sat_fm_restart_options                ""
% 4.07/1.00  --sat_gr_def                            false
% 4.07/1.00  --sat_epr_types                         true
% 4.07/1.00  --sat_non_cyclic_types                  false
% 4.07/1.00  --sat_finite_models                     false
% 4.07/1.00  --sat_fm_lemmas                         false
% 4.07/1.00  --sat_fm_prep                           false
% 4.07/1.00  --sat_fm_uc_incr                        true
% 4.07/1.00  --sat_out_model                         small
% 4.07/1.00  --sat_out_clauses                       false
% 4.07/1.00  
% 4.07/1.00  ------ QBF Options
% 4.07/1.00  
% 4.07/1.00  --qbf_mode                              false
% 4.07/1.00  --qbf_elim_univ                         false
% 4.07/1.00  --qbf_dom_inst                          none
% 4.07/1.00  --qbf_dom_pre_inst                      false
% 4.07/1.00  --qbf_sk_in                             false
% 4.07/1.00  --qbf_pred_elim                         true
% 4.07/1.00  --qbf_split                             512
% 4.07/1.00  
% 4.07/1.00  ------ BMC1 Options
% 4.07/1.00  
% 4.07/1.00  --bmc1_incremental                      false
% 4.07/1.00  --bmc1_axioms                           reachable_all
% 4.07/1.00  --bmc1_min_bound                        0
% 4.07/1.00  --bmc1_max_bound                        -1
% 4.07/1.00  --bmc1_max_bound_default                -1
% 4.07/1.00  --bmc1_symbol_reachability              true
% 4.07/1.00  --bmc1_property_lemmas                  false
% 4.07/1.00  --bmc1_k_induction                      false
% 4.07/1.00  --bmc1_non_equiv_states                 false
% 4.07/1.00  --bmc1_deadlock                         false
% 4.07/1.00  --bmc1_ucm                              false
% 4.07/1.00  --bmc1_add_unsat_core                   none
% 4.07/1.00  --bmc1_unsat_core_children              false
% 4.07/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 4.07/1.00  --bmc1_out_stat                         full
% 4.07/1.00  --bmc1_ground_init                      false
% 4.07/1.00  --bmc1_pre_inst_next_state              false
% 4.07/1.00  --bmc1_pre_inst_state                   false
% 4.07/1.00  --bmc1_pre_inst_reach_state             false
% 4.07/1.00  --bmc1_out_unsat_core                   false
% 4.07/1.00  --bmc1_aig_witness_out                  false
% 4.07/1.00  --bmc1_verbose                          false
% 4.07/1.00  --bmc1_dump_clauses_tptp                false
% 4.07/1.00  --bmc1_dump_unsat_core_tptp             false
% 4.07/1.00  --bmc1_dump_file                        -
% 4.07/1.00  --bmc1_ucm_expand_uc_limit              128
% 4.07/1.00  --bmc1_ucm_n_expand_iterations          6
% 4.07/1.00  --bmc1_ucm_extend_mode                  1
% 4.07/1.00  --bmc1_ucm_init_mode                    2
% 4.07/1.00  --bmc1_ucm_cone_mode                    none
% 4.07/1.00  --bmc1_ucm_reduced_relation_type        0
% 4.07/1.00  --bmc1_ucm_relax_model                  4
% 4.07/1.00  --bmc1_ucm_full_tr_after_sat            true
% 4.07/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 4.07/1.00  --bmc1_ucm_layered_model                none
% 4.07/1.00  --bmc1_ucm_max_lemma_size               10
% 4.07/1.00  
% 4.07/1.00  ------ AIG Options
% 4.07/1.00  
% 4.07/1.00  --aig_mode                              false
% 4.07/1.00  
% 4.07/1.00  ------ Instantiation Options
% 4.07/1.00  
% 4.07/1.00  --instantiation_flag                    true
% 4.07/1.00  --inst_sos_flag                         false
% 4.07/1.00  --inst_sos_phase                        true
% 4.07/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.07/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.07/1.00  --inst_lit_sel_side                     num_symb
% 4.07/1.00  --inst_solver_per_active                1400
% 4.07/1.00  --inst_solver_calls_frac                1.
% 4.07/1.00  --inst_passive_queue_type               priority_queues
% 4.07/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.07/1.00  --inst_passive_queues_freq              [25;2]
% 4.07/1.00  --inst_dismatching                      true
% 4.07/1.00  --inst_eager_unprocessed_to_passive     true
% 4.07/1.00  --inst_prop_sim_given                   true
% 4.07/1.00  --inst_prop_sim_new                     false
% 4.07/1.00  --inst_subs_new                         false
% 4.07/1.00  --inst_eq_res_simp                      false
% 4.07/1.00  --inst_subs_given                       false
% 4.07/1.00  --inst_orphan_elimination               true
% 4.07/1.00  --inst_learning_loop_flag               true
% 4.07/1.00  --inst_learning_start                   3000
% 4.07/1.00  --inst_learning_factor                  2
% 4.07/1.00  --inst_start_prop_sim_after_learn       3
% 4.07/1.00  --inst_sel_renew                        solver
% 4.07/1.00  --inst_lit_activity_flag                true
% 4.07/1.00  --inst_restr_to_given                   false
% 4.07/1.00  --inst_activity_threshold               500
% 4.07/1.00  --inst_out_proof                        true
% 4.07/1.00  
% 4.07/1.00  ------ Resolution Options
% 4.07/1.00  
% 4.07/1.00  --resolution_flag                       true
% 4.07/1.00  --res_lit_sel                           adaptive
% 4.07/1.00  --res_lit_sel_side                      none
% 4.07/1.00  --res_ordering                          kbo
% 4.07/1.00  --res_to_prop_solver                    active
% 4.07/1.00  --res_prop_simpl_new                    false
% 4.07/1.00  --res_prop_simpl_given                  true
% 4.07/1.00  --res_passive_queue_type                priority_queues
% 4.07/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.07/1.00  --res_passive_queues_freq               [15;5]
% 4.07/1.00  --res_forward_subs                      full
% 4.07/1.00  --res_backward_subs                     full
% 4.07/1.00  --res_forward_subs_resolution           true
% 4.07/1.00  --res_backward_subs_resolution          true
% 4.07/1.00  --res_orphan_elimination                true
% 4.07/1.00  --res_time_limit                        2.
% 4.07/1.00  --res_out_proof                         true
% 4.07/1.00  
% 4.07/1.00  ------ Superposition Options
% 4.07/1.00  
% 4.07/1.00  --superposition_flag                    true
% 4.07/1.00  --sup_passive_queue_type                priority_queues
% 4.07/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.07/1.00  --sup_passive_queues_freq               [8;1;4]
% 4.07/1.00  --demod_completeness_check              fast
% 4.07/1.00  --demod_use_ground                      true
% 4.07/1.00  --sup_to_prop_solver                    passive
% 4.07/1.00  --sup_prop_simpl_new                    true
% 4.07/1.00  --sup_prop_simpl_given                  true
% 4.07/1.00  --sup_fun_splitting                     false
% 4.07/1.00  --sup_smt_interval                      50000
% 4.07/1.00  
% 4.07/1.00  ------ Superposition Simplification Setup
% 4.07/1.00  
% 4.07/1.00  --sup_indices_passive                   []
% 4.07/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.07/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.07/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.07/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 4.07/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.07/1.00  --sup_full_bw                           [BwDemod]
% 4.07/1.00  --sup_immed_triv                        [TrivRules]
% 4.07/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.07/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.07/1.00  --sup_immed_bw_main                     []
% 4.07/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.07/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 4.07/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.07/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.07/1.00  
% 4.07/1.00  ------ Combination Options
% 4.07/1.00  
% 4.07/1.00  --comb_res_mult                         3
% 4.07/1.00  --comb_sup_mult                         2
% 4.07/1.00  --comb_inst_mult                        10
% 4.07/1.00  
% 4.07/1.00  ------ Debug Options
% 4.07/1.00  
% 4.07/1.00  --dbg_backtrace                         false
% 4.07/1.00  --dbg_dump_prop_clauses                 false
% 4.07/1.00  --dbg_dump_prop_clauses_file            -
% 4.07/1.00  --dbg_out_stat                          false
% 4.07/1.00  ------ Parsing...
% 4.07/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.07/1.00  
% 4.07/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 4.07/1.00  
% 4.07/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.07/1.00  
% 4.07/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.07/1.00  ------ Proving...
% 4.07/1.00  ------ Problem Properties 
% 4.07/1.00  
% 4.07/1.00  
% 4.07/1.00  clauses                                 12
% 4.07/1.00  conjectures                             2
% 4.07/1.00  EPR                                     2
% 4.07/1.00  Horn                                    12
% 4.07/1.00  unary                                   3
% 4.07/1.00  binary                                  6
% 4.07/1.00  lits                                    26
% 4.07/1.00  lits eq                                 4
% 4.07/1.00  fd_pure                                 0
% 4.07/1.00  fd_pseudo                               0
% 4.07/1.00  fd_cond                                 0
% 4.07/1.00  fd_pseudo_cond                          1
% 4.07/1.00  AC symbols                              0
% 4.07/1.00  
% 4.07/1.00  ------ Schedule dynamic 5 is on 
% 4.07/1.00  
% 4.07/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 4.07/1.00  
% 4.07/1.00  
% 4.07/1.00  ------ 
% 4.07/1.00  Current options:
% 4.07/1.00  ------ 
% 4.07/1.00  
% 4.07/1.00  ------ Input Options
% 4.07/1.00  
% 4.07/1.00  --out_options                           all
% 4.07/1.00  --tptp_safe_out                         true
% 4.07/1.00  --problem_path                          ""
% 4.07/1.00  --include_path                          ""
% 4.07/1.00  --clausifier                            res/vclausify_rel
% 4.07/1.00  --clausifier_options                    --mode clausify
% 4.07/1.00  --stdin                                 false
% 4.07/1.00  --stats_out                             all
% 4.07/1.00  
% 4.07/1.00  ------ General Options
% 4.07/1.00  
% 4.07/1.00  --fof                                   false
% 4.07/1.00  --time_out_real                         305.
% 4.07/1.00  --time_out_virtual                      -1.
% 4.07/1.00  --symbol_type_check                     false
% 4.07/1.00  --clausify_out                          false
% 4.07/1.00  --sig_cnt_out                           false
% 4.07/1.00  --trig_cnt_out                          false
% 4.07/1.00  --trig_cnt_out_tolerance                1.
% 4.07/1.00  --trig_cnt_out_sk_spl                   false
% 4.07/1.00  --abstr_cl_out                          false
% 4.07/1.00  
% 4.07/1.00  ------ Global Options
% 4.07/1.00  
% 4.07/1.00  --schedule                              default
% 4.07/1.00  --add_important_lit                     false
% 4.07/1.00  --prop_solver_per_cl                    1000
% 4.07/1.00  --min_unsat_core                        false
% 4.07/1.00  --soft_assumptions                      false
% 4.07/1.00  --soft_lemma_size                       3
% 4.07/1.00  --prop_impl_unit_size                   0
% 4.07/1.00  --prop_impl_unit                        []
% 4.07/1.00  --share_sel_clauses                     true
% 4.07/1.00  --reset_solvers                         false
% 4.07/1.00  --bc_imp_inh                            [conj_cone]
% 4.07/1.00  --conj_cone_tolerance                   3.
% 4.07/1.00  --extra_neg_conj                        none
% 4.07/1.00  --large_theory_mode                     true
% 4.07/1.00  --prolific_symb_bound                   200
% 4.07/1.00  --lt_threshold                          2000
% 4.07/1.00  --clause_weak_htbl                      true
% 4.07/1.00  --gc_record_bc_elim                     false
% 4.07/1.00  
% 4.07/1.00  ------ Preprocessing Options
% 4.07/1.00  
% 4.07/1.00  --preprocessing_flag                    true
% 4.07/1.00  --time_out_prep_mult                    0.1
% 4.07/1.00  --splitting_mode                        input
% 4.07/1.00  --splitting_grd                         true
% 4.07/1.00  --splitting_cvd                         false
% 4.07/1.00  --splitting_cvd_svl                     false
% 4.07/1.00  --splitting_nvd                         32
% 4.07/1.00  --sub_typing                            true
% 4.07/1.00  --prep_gs_sim                           true
% 4.07/1.00  --prep_unflatten                        true
% 4.07/1.00  --prep_res_sim                          true
% 4.07/1.00  --prep_upred                            true
% 4.07/1.00  --prep_sem_filter                       exhaustive
% 4.07/1.00  --prep_sem_filter_out                   false
% 4.07/1.00  --pred_elim                             true
% 4.07/1.00  --res_sim_input                         true
% 4.07/1.00  --eq_ax_congr_red                       true
% 4.07/1.00  --pure_diseq_elim                       true
% 4.07/1.00  --brand_transform                       false
% 4.07/1.00  --non_eq_to_eq                          false
% 4.07/1.00  --prep_def_merge                        true
% 4.07/1.00  --prep_def_merge_prop_impl              false
% 4.07/1.00  --prep_def_merge_mbd                    true
% 4.07/1.00  --prep_def_merge_tr_red                 false
% 4.07/1.00  --prep_def_merge_tr_cl                  false
% 4.07/1.00  --smt_preprocessing                     true
% 4.07/1.00  --smt_ac_axioms                         fast
% 4.07/1.00  --preprocessed_out                      false
% 4.07/1.00  --preprocessed_stats                    false
% 4.07/1.00  
% 4.07/1.00  ------ Abstraction refinement Options
% 4.07/1.00  
% 4.07/1.00  --abstr_ref                             []
% 4.07/1.00  --abstr_ref_prep                        false
% 4.07/1.00  --abstr_ref_until_sat                   false
% 4.07/1.00  --abstr_ref_sig_restrict                funpre
% 4.07/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 4.07/1.00  --abstr_ref_under                       []
% 4.07/1.00  
% 4.07/1.00  ------ SAT Options
% 4.07/1.00  
% 4.07/1.00  --sat_mode                              false
% 4.07/1.00  --sat_fm_restart_options                ""
% 4.07/1.00  --sat_gr_def                            false
% 4.07/1.00  --sat_epr_types                         true
% 4.07/1.00  --sat_non_cyclic_types                  false
% 4.07/1.00  --sat_finite_models                     false
% 4.07/1.00  --sat_fm_lemmas                         false
% 4.07/1.00  --sat_fm_prep                           false
% 4.07/1.00  --sat_fm_uc_incr                        true
% 4.07/1.00  --sat_out_model                         small
% 4.07/1.00  --sat_out_clauses                       false
% 4.07/1.00  
% 4.07/1.00  ------ QBF Options
% 4.07/1.00  
% 4.07/1.00  --qbf_mode                              false
% 4.07/1.00  --qbf_elim_univ                         false
% 4.07/1.00  --qbf_dom_inst                          none
% 4.07/1.00  --qbf_dom_pre_inst                      false
% 4.07/1.00  --qbf_sk_in                             false
% 4.07/1.00  --qbf_pred_elim                         true
% 4.07/1.00  --qbf_split                             512
% 4.07/1.00  
% 4.07/1.00  ------ BMC1 Options
% 4.07/1.00  
% 4.07/1.00  --bmc1_incremental                      false
% 4.07/1.00  --bmc1_axioms                           reachable_all
% 4.07/1.00  --bmc1_min_bound                        0
% 4.07/1.00  --bmc1_max_bound                        -1
% 4.07/1.00  --bmc1_max_bound_default                -1
% 4.07/1.00  --bmc1_symbol_reachability              true
% 4.07/1.00  --bmc1_property_lemmas                  false
% 4.07/1.00  --bmc1_k_induction                      false
% 4.07/1.00  --bmc1_non_equiv_states                 false
% 4.07/1.00  --bmc1_deadlock                         false
% 4.07/1.00  --bmc1_ucm                              false
% 4.07/1.00  --bmc1_add_unsat_core                   none
% 4.07/1.00  --bmc1_unsat_core_children              false
% 4.07/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 4.07/1.00  --bmc1_out_stat                         full
% 4.07/1.00  --bmc1_ground_init                      false
% 4.07/1.00  --bmc1_pre_inst_next_state              false
% 4.07/1.00  --bmc1_pre_inst_state                   false
% 4.07/1.00  --bmc1_pre_inst_reach_state             false
% 4.07/1.00  --bmc1_out_unsat_core                   false
% 4.07/1.00  --bmc1_aig_witness_out                  false
% 4.07/1.00  --bmc1_verbose                          false
% 4.07/1.00  --bmc1_dump_clauses_tptp                false
% 4.07/1.00  --bmc1_dump_unsat_core_tptp             false
% 4.07/1.00  --bmc1_dump_file                        -
% 4.07/1.00  --bmc1_ucm_expand_uc_limit              128
% 4.07/1.00  --bmc1_ucm_n_expand_iterations          6
% 4.07/1.00  --bmc1_ucm_extend_mode                  1
% 4.07/1.00  --bmc1_ucm_init_mode                    2
% 4.07/1.00  --bmc1_ucm_cone_mode                    none
% 4.07/1.00  --bmc1_ucm_reduced_relation_type        0
% 4.07/1.00  --bmc1_ucm_relax_model                  4
% 4.07/1.00  --bmc1_ucm_full_tr_after_sat            true
% 4.07/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 4.07/1.00  --bmc1_ucm_layered_model                none
% 4.07/1.00  --bmc1_ucm_max_lemma_size               10
% 4.07/1.00  
% 4.07/1.00  ------ AIG Options
% 4.07/1.00  
% 4.07/1.00  --aig_mode                              false
% 4.07/1.00  
% 4.07/1.00  ------ Instantiation Options
% 4.07/1.00  
% 4.07/1.00  --instantiation_flag                    true
% 4.07/1.00  --inst_sos_flag                         false
% 4.07/1.00  --inst_sos_phase                        true
% 4.07/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.07/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.07/1.00  --inst_lit_sel_side                     none
% 4.07/1.00  --inst_solver_per_active                1400
% 4.07/1.00  --inst_solver_calls_frac                1.
% 4.07/1.00  --inst_passive_queue_type               priority_queues
% 4.07/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.07/1.00  --inst_passive_queues_freq              [25;2]
% 4.07/1.00  --inst_dismatching                      true
% 4.07/1.00  --inst_eager_unprocessed_to_passive     true
% 4.07/1.00  --inst_prop_sim_given                   true
% 4.07/1.00  --inst_prop_sim_new                     false
% 4.07/1.00  --inst_subs_new                         false
% 4.07/1.00  --inst_eq_res_simp                      false
% 4.07/1.00  --inst_subs_given                       false
% 4.07/1.00  --inst_orphan_elimination               true
% 4.07/1.00  --inst_learning_loop_flag               true
% 4.07/1.00  --inst_learning_start                   3000
% 4.07/1.00  --inst_learning_factor                  2
% 4.07/1.00  --inst_start_prop_sim_after_learn       3
% 4.07/1.00  --inst_sel_renew                        solver
% 4.07/1.00  --inst_lit_activity_flag                true
% 4.07/1.00  --inst_restr_to_given                   false
% 4.07/1.00  --inst_activity_threshold               500
% 4.07/1.00  --inst_out_proof                        true
% 4.07/1.00  
% 4.07/1.00  ------ Resolution Options
% 4.07/1.00  
% 4.07/1.00  --resolution_flag                       false
% 4.07/1.00  --res_lit_sel                           adaptive
% 4.07/1.00  --res_lit_sel_side                      none
% 4.07/1.00  --res_ordering                          kbo
% 4.07/1.00  --res_to_prop_solver                    active
% 4.07/1.00  --res_prop_simpl_new                    false
% 4.07/1.00  --res_prop_simpl_given                  true
% 4.07/1.00  --res_passive_queue_type                priority_queues
% 4.07/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.07/1.00  --res_passive_queues_freq               [15;5]
% 4.07/1.00  --res_forward_subs                      full
% 4.07/1.00  --res_backward_subs                     full
% 4.07/1.00  --res_forward_subs_resolution           true
% 4.07/1.00  --res_backward_subs_resolution          true
% 4.07/1.00  --res_orphan_elimination                true
% 4.07/1.00  --res_time_limit                        2.
% 4.07/1.00  --res_out_proof                         true
% 4.07/1.00  
% 4.07/1.00  ------ Superposition Options
% 4.07/1.00  
% 4.07/1.00  --superposition_flag                    true
% 4.07/1.00  --sup_passive_queue_type                priority_queues
% 4.07/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.07/1.00  --sup_passive_queues_freq               [8;1;4]
% 4.07/1.00  --demod_completeness_check              fast
% 4.07/1.00  --demod_use_ground                      true
% 4.07/1.00  --sup_to_prop_solver                    passive
% 4.07/1.00  --sup_prop_simpl_new                    true
% 4.07/1.00  --sup_prop_simpl_given                  true
% 4.07/1.00  --sup_fun_splitting                     false
% 4.07/1.00  --sup_smt_interval                      50000
% 4.07/1.00  
% 4.07/1.00  ------ Superposition Simplification Setup
% 4.07/1.00  
% 4.07/1.00  --sup_indices_passive                   []
% 4.07/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.07/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.07/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.07/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 4.07/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.07/1.00  --sup_full_bw                           [BwDemod]
% 4.07/1.00  --sup_immed_triv                        [TrivRules]
% 4.07/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.07/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.07/1.00  --sup_immed_bw_main                     []
% 4.07/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.07/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 4.07/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.07/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.07/1.00  
% 4.07/1.00  ------ Combination Options
% 4.07/1.00  
% 4.07/1.00  --comb_res_mult                         3
% 4.07/1.00  --comb_sup_mult                         2
% 4.07/1.00  --comb_inst_mult                        10
% 4.07/1.00  
% 4.07/1.00  ------ Debug Options
% 4.07/1.00  
% 4.07/1.00  --dbg_backtrace                         false
% 4.07/1.00  --dbg_dump_prop_clauses                 false
% 4.07/1.00  --dbg_dump_prop_clauses_file            -
% 4.07/1.00  --dbg_out_stat                          false
% 4.07/1.00  
% 4.07/1.00  
% 4.07/1.00  
% 4.07/1.00  
% 4.07/1.00  ------ Proving...
% 4.07/1.00  
% 4.07/1.00  
% 4.07/1.00  % SZS status Theorem for theBenchmark.p
% 4.07/1.00  
% 4.07/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 4.07/1.00  
% 4.07/1.00  fof(f10,conjecture,(
% 4.07/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,k1_tops_1(X0,X1)) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,k1_tops_1(X0,X1))))))),
% 4.07/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.07/1.00  
% 4.07/1.00  fof(f11,negated_conjecture,(
% 4.07/1.00    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,k1_tops_1(X0,X1)) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,k1_tops_1(X0,X1))))))),
% 4.07/1.00    inference(negated_conjecture,[],[f10])).
% 4.07/1.00  
% 4.07/1.00  fof(f26,plain,(
% 4.07/1.00    ? [X0] : (? [X1] : (k2_pre_topc(X0,k1_tops_1(X0,X1)) != k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,k1_tops_1(X0,X1)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 4.07/1.00    inference(ennf_transformation,[],[f11])).
% 4.07/1.00  
% 4.07/1.00  fof(f30,plain,(
% 4.07/1.00    ( ! [X0] : (? [X1] : (k2_pre_topc(X0,k1_tops_1(X0,X1)) != k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,k1_tops_1(X0,X1)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (k2_pre_topc(X0,k1_tops_1(X0,sK1)) != k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,k1_tops_1(X0,sK1)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 4.07/1.00    introduced(choice_axiom,[])).
% 4.07/1.00  
% 4.07/1.00  fof(f29,plain,(
% 4.07/1.00    ? [X0] : (? [X1] : (k2_pre_topc(X0,k1_tops_1(X0,X1)) != k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,k1_tops_1(X0,X1)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (k2_pre_topc(sK0,k1_tops_1(sK0,X1)) != k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,X1)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 4.07/1.00    introduced(choice_axiom,[])).
% 4.07/1.00  
% 4.07/1.00  fof(f31,plain,(
% 4.07/1.00    (k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) != k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 4.07/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f30,f29])).
% 4.07/1.00  
% 4.07/1.00  fof(f44,plain,(
% 4.07/1.00    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 4.07/1.00    inference(cnf_transformation,[],[f31])).
% 4.07/1.00  
% 4.07/1.00  fof(f7,axiom,(
% 4.07/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)))),
% 4.07/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.07/1.00  
% 4.07/1.00  fof(f21,plain,(
% 4.07/1.00    ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 4.07/1.00    inference(ennf_transformation,[],[f7])).
% 4.07/1.00  
% 4.07/1.00  fof(f22,plain,(
% 4.07/1.00    ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 4.07/1.00    inference(flattening,[],[f21])).
% 4.07/1.00  
% 4.07/1.00  fof(f40,plain,(
% 4.07/1.00    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 4.07/1.00    inference(cnf_transformation,[],[f22])).
% 4.07/1.00  
% 4.07/1.00  fof(f43,plain,(
% 4.07/1.00    l1_pre_topc(sK0)),
% 4.07/1.00    inference(cnf_transformation,[],[f31])).
% 4.07/1.00  
% 4.07/1.00  fof(f9,axiom,(
% 4.07/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 4.07/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.07/1.00  
% 4.07/1.00  fof(f24,plain,(
% 4.07/1.00    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.07/1.00    inference(ennf_transformation,[],[f9])).
% 4.07/1.00  
% 4.07/1.00  fof(f25,plain,(
% 4.07/1.00    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.07/1.00    inference(flattening,[],[f24])).
% 4.07/1.00  
% 4.07/1.00  fof(f42,plain,(
% 4.07/1.00    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 4.07/1.00    inference(cnf_transformation,[],[f25])).
% 4.07/1.00  
% 4.07/1.00  fof(f6,axiom,(
% 4.07/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 4.07/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.07/1.00  
% 4.07/1.00  fof(f19,plain,(
% 4.07/1.00    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 4.07/1.00    inference(ennf_transformation,[],[f6])).
% 4.07/1.00  
% 4.07/1.00  fof(f20,plain,(
% 4.07/1.00    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 4.07/1.00    inference(flattening,[],[f19])).
% 4.07/1.00  
% 4.07/1.00  fof(f39,plain,(
% 4.07/1.00    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 4.07/1.00    inference(cnf_transformation,[],[f20])).
% 4.07/1.00  
% 4.07/1.00  fof(f2,axiom,(
% 4.07/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 4.07/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.07/1.00  
% 4.07/1.00  fof(f12,plain,(
% 4.07/1.00    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 4.07/1.00    inference(ennf_transformation,[],[f2])).
% 4.07/1.00  
% 4.07/1.00  fof(f13,plain,(
% 4.07/1.00    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 4.07/1.00    inference(flattening,[],[f12])).
% 4.07/1.00  
% 4.07/1.00  fof(f35,plain,(
% 4.07/1.00    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 4.07/1.00    inference(cnf_transformation,[],[f13])).
% 4.07/1.00  
% 4.07/1.00  fof(f1,axiom,(
% 4.07/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 4.07/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.07/1.00  
% 4.07/1.00  fof(f27,plain,(
% 4.07/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.07/1.00    inference(nnf_transformation,[],[f1])).
% 4.07/1.00  
% 4.07/1.00  fof(f28,plain,(
% 4.07/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.07/1.00    inference(flattening,[],[f27])).
% 4.07/1.00  
% 4.07/1.00  fof(f34,plain,(
% 4.07/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 4.07/1.00    inference(cnf_transformation,[],[f28])).
% 4.07/1.00  
% 4.07/1.00  fof(f45,plain,(
% 4.07/1.00    k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) != k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))))),
% 4.07/1.00    inference(cnf_transformation,[],[f31])).
% 4.07/1.00  
% 4.07/1.00  fof(f8,axiom,(
% 4.07/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 4.07/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.07/1.00  
% 4.07/1.00  fof(f23,plain,(
% 4.07/1.00    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.07/1.00    inference(ennf_transformation,[],[f8])).
% 4.07/1.00  
% 4.07/1.00  fof(f41,plain,(
% 4.07/1.00    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 4.07/1.00    inference(cnf_transformation,[],[f23])).
% 4.07/1.00  
% 4.07/1.00  fof(f3,axiom,(
% 4.07/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)))),
% 4.07/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.07/1.00  
% 4.07/1.00  fof(f14,plain,(
% 4.07/1.00    ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 4.07/1.00    inference(ennf_transformation,[],[f3])).
% 4.07/1.00  
% 4.07/1.00  fof(f15,plain,(
% 4.07/1.00    ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 4.07/1.00    inference(flattening,[],[f14])).
% 4.07/1.00  
% 4.07/1.00  fof(f36,plain,(
% 4.07/1.00    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 4.07/1.00    inference(cnf_transformation,[],[f15])).
% 4.07/1.00  
% 4.07/1.00  fof(f5,axiom,(
% 4.07/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))))))),
% 4.07/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.07/1.00  
% 4.07/1.00  fof(f17,plain,(
% 4.07/1.00    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.07/1.00    inference(ennf_transformation,[],[f5])).
% 4.07/1.00  
% 4.07/1.00  fof(f18,plain,(
% 4.07/1.00    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.07/1.00    inference(flattening,[],[f17])).
% 4.07/1.00  
% 4.07/1.00  fof(f38,plain,(
% 4.07/1.00    ( ! [X2,X0,X1] : (r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 4.07/1.00    inference(cnf_transformation,[],[f18])).
% 4.07/1.00  
% 4.07/1.00  fof(f4,axiom,(
% 4.07/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 4.07/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.07/1.00  
% 4.07/1.00  fof(f16,plain,(
% 4.07/1.00    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.07/1.00    inference(ennf_transformation,[],[f4])).
% 4.07/1.00  
% 4.07/1.00  fof(f37,plain,(
% 4.07/1.00    ( ! [X0,X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 4.07/1.00    inference(cnf_transformation,[],[f16])).
% 4.07/1.00  
% 4.07/1.00  cnf(c_12,negated_conjecture,
% 4.07/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 4.07/1.00      inference(cnf_transformation,[],[f44]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_578,plain,
% 4.07/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 4.07/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_8,plain,
% 4.07/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.07/1.00      | ~ l1_pre_topc(X1)
% 4.07/1.00      | k1_tops_1(X1,k1_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
% 4.07/1.00      inference(cnf_transformation,[],[f40]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_13,negated_conjecture,
% 4.07/1.00      ( l1_pre_topc(sK0) ),
% 4.07/1.00      inference(cnf_transformation,[],[f43]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_174,plain,
% 4.07/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.07/1.00      | k1_tops_1(X1,k1_tops_1(X1,X0)) = k1_tops_1(X1,X0)
% 4.07/1.00      | sK0 != X1 ),
% 4.07/1.00      inference(resolution_lifted,[status(thm)],[c_8,c_13]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_175,plain,
% 4.07/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 4.07/1.00      | k1_tops_1(sK0,k1_tops_1(sK0,X0)) = k1_tops_1(sK0,X0) ),
% 4.07/1.00      inference(unflattening,[status(thm)],[c_174]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_575,plain,
% 4.07/1.00      ( k1_tops_1(sK0,k1_tops_1(sK0,X0)) = k1_tops_1(sK0,X0)
% 4.07/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 4.07/1.00      inference(predicate_to_equality,[status(thm)],[c_175]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_1461,plain,
% 4.07/1.00      ( k1_tops_1(sK0,k1_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
% 4.07/1.00      inference(superposition,[status(thm)],[c_578,c_575]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_10,plain,
% 4.07/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.07/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 4.07/1.00      | ~ r1_tarski(X0,X2)
% 4.07/1.00      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 4.07/1.00      | ~ l1_pre_topc(X1) ),
% 4.07/1.00      inference(cnf_transformation,[],[f42]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_144,plain,
% 4.07/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.07/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 4.07/1.00      | ~ r1_tarski(X0,X2)
% 4.07/1.00      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 4.07/1.00      | sK0 != X1 ),
% 4.07/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_13]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_145,plain,
% 4.07/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 4.07/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 4.07/1.00      | ~ r1_tarski(X1,X0)
% 4.07/1.00      | r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,X0)) ),
% 4.07/1.00      inference(unflattening,[status(thm)],[c_144]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_577,plain,
% 4.07/1.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 4.07/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 4.07/1.00      | r1_tarski(X1,X0) != iProver_top
% 4.07/1.00      | r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,X0)) = iProver_top ),
% 4.07/1.00      inference(predicate_to_equality,[status(thm)],[c_145]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_1670,plain,
% 4.07/1.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 4.07/1.00      | m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 4.07/1.00      | r1_tarski(k1_tops_1(sK0,sK1),X0) != iProver_top
% 4.07/1.00      | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,X0)) = iProver_top ),
% 4.07/1.00      inference(superposition,[status(thm)],[c_1461,c_577]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_15,plain,
% 4.07/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 4.07/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_7,plain,
% 4.07/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.07/1.00      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 4.07/1.00      | ~ l1_pre_topc(X1) ),
% 4.07/1.00      inference(cnf_transformation,[],[f39]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_186,plain,
% 4.07/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.07/1.00      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 4.07/1.00      | sK0 != X1 ),
% 4.07/1.00      inference(resolution_lifted,[status(thm)],[c_7,c_13]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_187,plain,
% 4.07/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 4.07/1.00      | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 4.07/1.00      inference(unflattening,[status(thm)],[c_186]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_657,plain,
% 4.07/1.00      ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 4.07/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 4.07/1.00      inference(instantiation,[status(thm)],[c_187]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_658,plain,
% 4.07/1.00      ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 4.07/1.00      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 4.07/1.00      inference(predicate_to_equality,[status(thm)],[c_657]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_4410,plain,
% 4.07/1.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 4.07/1.00      | r1_tarski(k1_tops_1(sK0,sK1),X0) != iProver_top
% 4.07/1.00      | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,X0)) = iProver_top ),
% 4.07/1.00      inference(global_propositional_subsumption,
% 4.07/1.00                [status(thm)],
% 4.07/1.00                [c_1670,c_15,c_658]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_574,plain,
% 4.07/1.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 4.07/1.00      | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 4.07/1.00      inference(predicate_to_equality,[status(thm)],[c_187]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_3,plain,
% 4.07/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.07/1.00      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 4.07/1.00      | ~ l1_pre_topc(X1) ),
% 4.07/1.00      inference(cnf_transformation,[],[f35]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_240,plain,
% 4.07/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.07/1.00      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 4.07/1.00      | sK0 != X1 ),
% 4.07/1.00      inference(resolution_lifted,[status(thm)],[c_3,c_13]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_241,plain,
% 4.07/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 4.07/1.00      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 4.07/1.00      inference(unflattening,[status(thm)],[c_240]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_570,plain,
% 4.07/1.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 4.07/1.00      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 4.07/1.00      inference(predicate_to_equality,[status(thm)],[c_241]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_1463,plain,
% 4.07/1.00      ( k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,X0))) = k1_tops_1(sK0,k2_pre_topc(sK0,X0))
% 4.07/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 4.07/1.00      inference(superposition,[status(thm)],[c_570,c_575]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_3102,plain,
% 4.07/1.00      ( k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,X0)))) = k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,X0)))
% 4.07/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 4.07/1.00      inference(superposition,[status(thm)],[c_574,c_1463]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_4166,plain,
% 4.07/1.00      ( k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))) = k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
% 4.07/1.00      inference(superposition,[status(thm)],[c_578,c_3102]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_0,plain,
% 4.07/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 4.07/1.00      inference(cnf_transformation,[],[f34]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_580,plain,
% 4.07/1.00      ( X0 = X1
% 4.07/1.00      | r1_tarski(X0,X1) != iProver_top
% 4.07/1.00      | r1_tarski(X1,X0) != iProver_top ),
% 4.07/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_1672,plain,
% 4.07/1.00      ( k1_tops_1(sK0,X0) = k1_tops_1(sK0,X1)
% 4.07/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 4.07/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 4.07/1.00      | r1_tarski(X0,X1) != iProver_top
% 4.07/1.00      | r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,X0)) != iProver_top ),
% 4.07/1.00      inference(superposition,[status(thm)],[c_577,c_580]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_4423,plain,
% 4.07/1.00      ( k1_tops_1(sK0,X0) = k1_tops_1(sK0,sK1)
% 4.07/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 4.07/1.00      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 4.07/1.00      | r1_tarski(X0,sK1) != iProver_top
% 4.07/1.00      | r1_tarski(k1_tops_1(sK0,sK1),X0) != iProver_top ),
% 4.07/1.00      inference(superposition,[status(thm)],[c_4410,c_1672]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_7254,plain,
% 4.07/1.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 4.07/1.00      | k1_tops_1(sK0,X0) = k1_tops_1(sK0,sK1)
% 4.07/1.00      | r1_tarski(X0,sK1) != iProver_top
% 4.07/1.00      | r1_tarski(k1_tops_1(sK0,sK1),X0) != iProver_top ),
% 4.07/1.00      inference(global_propositional_subsumption,
% 4.07/1.00                [status(thm)],
% 4.07/1.00                [c_4423,c_15]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_7255,plain,
% 4.07/1.00      ( k1_tops_1(sK0,X0) = k1_tops_1(sK0,sK1)
% 4.07/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 4.07/1.00      | r1_tarski(X0,sK1) != iProver_top
% 4.07/1.00      | r1_tarski(k1_tops_1(sK0,sK1),X0) != iProver_top ),
% 4.07/1.00      inference(renaming,[status(thm)],[c_7254]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_7265,plain,
% 4.07/1.00      ( k1_tops_1(sK0,k1_tops_1(sK0,X0)) = k1_tops_1(sK0,sK1)
% 4.07/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 4.07/1.00      | r1_tarski(k1_tops_1(sK0,X0),sK1) != iProver_top
% 4.07/1.00      | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,X0)) != iProver_top ),
% 4.07/1.00      inference(superposition,[status(thm)],[c_574,c_7255]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_14714,plain,
% 4.07/1.00      ( k1_tops_1(sK0,k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))))) = k1_tops_1(sK0,sK1)
% 4.07/1.00      | m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 4.07/1.00      | r1_tarski(k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))),sK1) != iProver_top
% 4.07/1.00      | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))) != iProver_top ),
% 4.07/1.00      inference(superposition,[status(thm)],[c_4166,c_7265]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_14739,plain,
% 4.07/1.00      ( k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = k1_tops_1(sK0,sK1)
% 4.07/1.00      | m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 4.07/1.00      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))),sK1) != iProver_top
% 4.07/1.00      | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))) != iProver_top ),
% 4.07/1.00      inference(light_normalisation,[status(thm)],[c_14714,c_4166]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_11,negated_conjecture,
% 4.07/1.00      ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) != k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))) ),
% 4.07/1.00      inference(cnf_transformation,[],[f45]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_717,plain,
% 4.07/1.00      ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 4.07/1.00      | m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 4.07/1.00      inference(instantiation,[status(thm)],[c_241]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_721,plain,
% 4.07/1.00      ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 4.07/1.00      | m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 4.07/1.00      inference(predicate_to_equality,[status(thm)],[c_717]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_363,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_691,plain,
% 4.07/1.00      ( k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))) != X0
% 4.07/1.00      | k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) != X0
% 4.07/1.00      | k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))) ),
% 4.07/1.00      inference(instantiation,[status(thm)],[c_363]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_826,plain,
% 4.07/1.00      ( k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))) != k2_pre_topc(sK0,k1_tops_1(sK0,sK1))
% 4.07/1.00      | k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))))
% 4.07/1.00      | k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) != k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) ),
% 4.07/1.00      inference(instantiation,[status(thm)],[c_691]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_362,plain,( X0 = X0 ),theory(equality) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_827,plain,
% 4.07/1.00      ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) ),
% 4.07/1.00      inference(instantiation,[status(thm)],[c_362]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_865,plain,
% 4.07/1.00      ( m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
% 4.07/1.00      | ~ m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 4.07/1.00      inference(instantiation,[status(thm)],[c_187]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_866,plain,
% 4.07/1.00      ( m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 4.07/1.00      | m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 4.07/1.00      inference(predicate_to_equality,[status(thm)],[c_865]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_9,plain,
% 4.07/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.07/1.00      | r1_tarski(k1_tops_1(X1,X0),X0)
% 4.07/1.00      | ~ l1_pre_topc(X1) ),
% 4.07/1.00      inference(cnf_transformation,[],[f41]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_162,plain,
% 4.07/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.07/1.00      | r1_tarski(k1_tops_1(X1,X0),X0)
% 4.07/1.00      | sK0 != X1 ),
% 4.07/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_13]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_163,plain,
% 4.07/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 4.07/1.00      | r1_tarski(k1_tops_1(sK0,X0),X0) ),
% 4.07/1.00      inference(unflattening,[status(thm)],[c_162]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_576,plain,
% 4.07/1.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 4.07/1.00      | r1_tarski(k1_tops_1(sK0,X0),X0) = iProver_top ),
% 4.07/1.00      inference(predicate_to_equality,[status(thm)],[c_163]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_922,plain,
% 4.07/1.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 4.07/1.00      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),k2_pre_topc(sK0,X0)) = iProver_top ),
% 4.07/1.00      inference(superposition,[status(thm)],[c_570,c_576]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_4,plain,
% 4.07/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.07/1.00      | ~ l1_pre_topc(X1)
% 4.07/1.00      | k2_pre_topc(X1,k2_pre_topc(X1,X0)) = k2_pre_topc(X1,X0) ),
% 4.07/1.00      inference(cnf_transformation,[],[f36]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_228,plain,
% 4.07/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.07/1.00      | k2_pre_topc(X1,k2_pre_topc(X1,X0)) = k2_pre_topc(X1,X0)
% 4.07/1.00      | sK0 != X1 ),
% 4.07/1.00      inference(resolution_lifted,[status(thm)],[c_4,c_13]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_229,plain,
% 4.07/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 4.07/1.00      | k2_pre_topc(sK0,k2_pre_topc(sK0,X0)) = k2_pre_topc(sK0,X0) ),
% 4.07/1.00      inference(unflattening,[status(thm)],[c_228]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_571,plain,
% 4.07/1.00      ( k2_pre_topc(sK0,k2_pre_topc(sK0,X0)) = k2_pre_topc(sK0,X0)
% 4.07/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 4.07/1.00      inference(predicate_to_equality,[status(thm)],[c_229]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_1302,plain,
% 4.07/1.00      ( k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,X0))) = k2_pre_topc(sK0,k1_tops_1(sK0,X0))
% 4.07/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 4.07/1.00      inference(superposition,[status(thm)],[c_574,c_571]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_2517,plain,
% 4.07/1.00      ( k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) ),
% 4.07/1.00      inference(superposition,[status(thm)],[c_578,c_1302]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_6,plain,
% 4.07/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.07/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 4.07/1.00      | ~ r1_tarski(X0,X2)
% 4.07/1.00      | r1_tarski(k2_pre_topc(X1,X0),k2_pre_topc(X1,X2))
% 4.07/1.00      | ~ l1_pre_topc(X1) ),
% 4.07/1.00      inference(cnf_transformation,[],[f38]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_198,plain,
% 4.07/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.07/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 4.07/1.00      | ~ r1_tarski(X0,X2)
% 4.07/1.00      | r1_tarski(k2_pre_topc(X1,X0),k2_pre_topc(X1,X2))
% 4.07/1.00      | sK0 != X1 ),
% 4.07/1.00      inference(resolution_lifted,[status(thm)],[c_6,c_13]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_199,plain,
% 4.07/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 4.07/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 4.07/1.00      | ~ r1_tarski(X1,X0)
% 4.07/1.00      | r1_tarski(k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X0)) ),
% 4.07/1.00      inference(unflattening,[status(thm)],[c_198]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_573,plain,
% 4.07/1.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 4.07/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 4.07/1.00      | r1_tarski(X1,X0) != iProver_top
% 4.07/1.00      | r1_tarski(k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X0)) = iProver_top ),
% 4.07/1.00      inference(predicate_to_equality,[status(thm)],[c_199]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_2544,plain,
% 4.07/1.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 4.07/1.00      | m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 4.07/1.00      | r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != iProver_top
% 4.07/1.00      | r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = iProver_top ),
% 4.07/1.00      inference(superposition,[status(thm)],[c_2517,c_573]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_7625,plain,
% 4.07/1.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 4.07/1.00      | r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != iProver_top
% 4.07/1.00      | r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = iProver_top ),
% 4.07/1.00      inference(global_propositional_subsumption,
% 4.07/1.00                [status(thm)],
% 4.07/1.00                [c_2544,c_15,c_658,c_721]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_1112,plain,
% 4.07/1.00      ( k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,X1)
% 4.07/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 4.07/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 4.07/1.00      | r1_tarski(X0,X1) != iProver_top
% 4.07/1.00      | r1_tarski(k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X0)) != iProver_top ),
% 4.07/1.00      inference(superposition,[status(thm)],[c_573,c_580]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_7640,plain,
% 4.07/1.00      ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k2_pre_topc(sK0,X0)
% 4.07/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 4.07/1.00      | m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 4.07/1.00      | r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != iProver_top
% 4.07/1.00      | r1_tarski(k1_tops_1(sK0,sK1),X0) != iProver_top ),
% 4.07/1.00      inference(superposition,[status(thm)],[c_7625,c_1112]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_12272,plain,
% 4.07/1.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 4.07/1.00      | k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k2_pre_topc(sK0,X0)
% 4.07/1.00      | r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != iProver_top
% 4.07/1.00      | r1_tarski(k1_tops_1(sK0,sK1),X0) != iProver_top ),
% 4.07/1.00      inference(global_propositional_subsumption,
% 4.07/1.00                [status(thm)],
% 4.07/1.00                [c_7640,c_15,c_658]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_12273,plain,
% 4.07/1.00      ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k2_pre_topc(sK0,X0)
% 4.07/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 4.07/1.00      | r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != iProver_top
% 4.07/1.00      | r1_tarski(k1_tops_1(sK0,sK1),X0) != iProver_top ),
% 4.07/1.00      inference(renaming,[status(thm)],[c_12272]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_12285,plain,
% 4.07/1.00      ( k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))) = k2_pre_topc(sK0,k1_tops_1(sK0,sK1))
% 4.07/1.00      | m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 4.07/1.00      | m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 4.07/1.00      | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))) != iProver_top ),
% 4.07/1.00      inference(superposition,[status(thm)],[c_922,c_12273]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_17410,plain,
% 4.07/1.00      ( r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))) != iProver_top ),
% 4.07/1.00      inference(global_propositional_subsumption,
% 4.07/1.00                [status(thm)],
% 4.07/1.00                [c_14739,c_15,c_11,c_658,c_721,c_826,c_827,c_866,c_12285]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_17417,plain,
% 4.07/1.00      ( m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 4.07/1.00      | r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != iProver_top ),
% 4.07/1.00      inference(superposition,[status(thm)],[c_4410,c_17410]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_5,plain,
% 4.07/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.07/1.00      | r1_tarski(X0,k2_pre_topc(X1,X0))
% 4.07/1.00      | ~ l1_pre_topc(X1) ),
% 4.07/1.00      inference(cnf_transformation,[],[f37]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_216,plain,
% 4.07/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.07/1.00      | r1_tarski(X0,k2_pre_topc(X1,X0))
% 4.07/1.00      | sK0 != X1 ),
% 4.07/1.00      inference(resolution_lifted,[status(thm)],[c_5,c_13]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_217,plain,
% 4.07/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 4.07/1.00      | r1_tarski(X0,k2_pre_topc(sK0,X0)) ),
% 4.07/1.00      inference(unflattening,[status(thm)],[c_216]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_714,plain,
% 4.07/1.00      ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 4.07/1.00      | r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
% 4.07/1.00      inference(instantiation,[status(thm)],[c_217]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(c_727,plain,
% 4.07/1.00      ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 4.07/1.00      | r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = iProver_top ),
% 4.07/1.00      inference(predicate_to_equality,[status(thm)],[c_714]) ).
% 4.07/1.00  
% 4.07/1.00  cnf(contradiction,plain,
% 4.07/1.00      ( $false ),
% 4.07/1.00      inference(minisat,[status(thm)],[c_17417,c_727,c_721,c_658,c_15]) ).
% 4.07/1.00  
% 4.07/1.00  
% 4.07/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 4.07/1.00  
% 4.07/1.00  ------                               Statistics
% 4.07/1.00  
% 4.07/1.00  ------ General
% 4.07/1.00  
% 4.07/1.00  abstr_ref_over_cycles:                  0
% 4.07/1.00  abstr_ref_under_cycles:                 0
% 4.07/1.00  gc_basic_clause_elim:                   0
% 4.07/1.00  forced_gc_time:                         0
% 4.07/1.00  parsing_time:                           0.007
% 4.07/1.00  unif_index_cands_time:                  0.
% 4.07/1.00  unif_index_add_time:                    0.
% 4.07/1.00  orderings_time:                         0.
% 4.07/1.00  out_proof_time:                         0.011
% 4.07/1.00  total_time:                             0.504
% 4.07/1.00  num_of_symbols:                         40
% 4.07/1.00  num_of_terms:                           15781
% 4.07/1.00  
% 4.07/1.00  ------ Preprocessing
% 4.07/1.00  
% 4.07/1.00  num_of_splits:                          0
% 4.07/1.00  num_of_split_atoms:                     0
% 4.07/1.00  num_of_reused_defs:                     0
% 4.07/1.00  num_eq_ax_congr_red:                    0
% 4.07/1.00  num_of_sem_filtered_clauses:            1
% 4.07/1.00  num_of_subtypes:                        0
% 4.07/1.00  monotx_restored_types:                  0
% 4.07/1.00  sat_num_of_epr_types:                   0
% 4.07/1.00  sat_num_of_non_cyclic_types:            0
% 4.07/1.00  sat_guarded_non_collapsed_types:        0
% 4.07/1.00  num_pure_diseq_elim:                    0
% 4.07/1.00  simp_replaced_by:                       0
% 4.07/1.00  res_preprocessed:                       66
% 4.07/1.00  prep_upred:                             0
% 4.07/1.00  prep_unflattend:                        8
% 4.07/1.00  smt_new_axioms:                         0
% 4.07/1.00  pred_elim_cands:                        2
% 4.07/1.00  pred_elim:                              1
% 4.07/1.00  pred_elim_cl:                           1
% 4.07/1.00  pred_elim_cycles:                       3
% 4.07/1.00  merged_defs:                            0
% 4.07/1.00  merged_defs_ncl:                        0
% 4.07/1.00  bin_hyper_res:                          0
% 4.07/1.00  prep_cycles:                            4
% 4.07/1.00  pred_elim_time:                         0.003
% 4.07/1.00  splitting_time:                         0.
% 4.07/1.00  sem_filter_time:                        0.
% 4.07/1.00  monotx_time:                            0.
% 4.07/1.00  subtype_inf_time:                       0.
% 4.07/1.00  
% 4.07/1.00  ------ Problem properties
% 4.07/1.00  
% 4.07/1.00  clauses:                                12
% 4.07/1.00  conjectures:                            2
% 4.07/1.00  epr:                                    2
% 4.07/1.00  horn:                                   12
% 4.07/1.00  ground:                                 2
% 4.07/1.00  unary:                                  3
% 4.07/1.00  binary:                                 6
% 4.07/1.00  lits:                                   26
% 4.07/1.00  lits_eq:                                4
% 4.07/1.00  fd_pure:                                0
% 4.07/1.00  fd_pseudo:                              0
% 4.07/1.00  fd_cond:                                0
% 4.07/1.00  fd_pseudo_cond:                         1
% 4.07/1.00  ac_symbols:                             0
% 4.07/1.00  
% 4.07/1.00  ------ Propositional Solver
% 4.07/1.00  
% 4.07/1.00  prop_solver_calls:                      29
% 4.07/1.00  prop_fast_solver_calls:                 1141
% 4.07/1.00  smt_solver_calls:                       0
% 4.07/1.00  smt_fast_solver_calls:                  0
% 4.07/1.00  prop_num_of_clauses:                    5689
% 4.07/1.00  prop_preprocess_simplified:             8321
% 4.07/1.00  prop_fo_subsumed:                       67
% 4.07/1.00  prop_solver_time:                       0.
% 4.07/1.00  smt_solver_time:                        0.
% 4.07/1.00  smt_fast_solver_time:                   0.
% 4.07/1.00  prop_fast_solver_time:                  0.
% 4.07/1.00  prop_unsat_core_time:                   0.
% 4.07/1.00  
% 4.07/1.00  ------ QBF
% 4.07/1.00  
% 4.07/1.00  qbf_q_res:                              0
% 4.07/1.00  qbf_num_tautologies:                    0
% 4.07/1.00  qbf_prep_cycles:                        0
% 4.07/1.00  
% 4.07/1.00  ------ BMC1
% 4.07/1.00  
% 4.07/1.00  bmc1_current_bound:                     -1
% 4.07/1.00  bmc1_last_solved_bound:                 -1
% 4.07/1.00  bmc1_unsat_core_size:                   -1
% 4.07/1.00  bmc1_unsat_core_parents_size:           -1
% 4.07/1.00  bmc1_merge_next_fun:                    0
% 4.07/1.00  bmc1_unsat_core_clauses_time:           0.
% 4.07/1.00  
% 4.07/1.00  ------ Instantiation
% 4.07/1.00  
% 4.07/1.00  inst_num_of_clauses:                    1599
% 4.07/1.00  inst_num_in_passive:                    270
% 4.07/1.00  inst_num_in_active:                     1064
% 4.07/1.00  inst_num_in_unprocessed:                265
% 4.07/1.00  inst_num_of_loops:                      1080
% 4.07/1.00  inst_num_of_learning_restarts:          0
% 4.07/1.00  inst_num_moves_active_passive:          13
% 4.07/1.00  inst_lit_activity:                      0
% 4.07/1.00  inst_lit_activity_moves:                1
% 4.07/1.00  inst_num_tautologies:                   0
% 4.07/1.00  inst_num_prop_implied:                  0
% 4.07/1.00  inst_num_existing_simplified:           0
% 4.07/1.00  inst_num_eq_res_simplified:             0
% 4.07/1.00  inst_num_child_elim:                    0
% 4.07/1.00  inst_num_of_dismatching_blockings:      3159
% 4.07/1.00  inst_num_of_non_proper_insts:           1500
% 4.07/1.00  inst_num_of_duplicates:                 0
% 4.07/1.00  inst_inst_num_from_inst_to_res:         0
% 4.07/1.00  inst_dismatching_checking_time:         0.
% 4.07/1.00  
% 4.07/1.00  ------ Resolution
% 4.07/1.00  
% 4.07/1.00  res_num_of_clauses:                     0
% 4.07/1.00  res_num_in_passive:                     0
% 4.07/1.00  res_num_in_active:                      0
% 4.07/1.00  res_num_of_loops:                       70
% 4.07/1.00  res_forward_subset_subsumed:            66
% 4.07/1.00  res_backward_subset_subsumed:           2
% 4.07/1.00  res_forward_subsumed:                   0
% 4.07/1.00  res_backward_subsumed:                  0
% 4.07/1.00  res_forward_subsumption_resolution:     0
% 4.07/1.00  res_backward_subsumption_resolution:    0
% 4.07/1.00  res_clause_to_clause_subsumption:       4139
% 4.07/1.00  res_orphan_elimination:                 0
% 4.07/1.00  res_tautology_del:                      31
% 4.07/1.00  res_num_eq_res_simplified:              0
% 4.07/1.00  res_num_sel_changes:                    0
% 4.07/1.00  res_moves_from_active_to_pass:          0
% 4.07/1.00  
% 4.07/1.00  ------ Superposition
% 4.07/1.00  
% 4.07/1.00  sup_time_total:                         0.
% 4.07/1.00  sup_time_generating:                    0.
% 4.07/1.00  sup_time_sim_full:                      0.
% 4.07/1.00  sup_time_sim_immed:                     0.
% 4.07/1.00  
% 4.07/1.00  sup_num_of_clauses:                     438
% 4.07/1.00  sup_num_in_active:                      216
% 4.07/1.00  sup_num_in_passive:                     222
% 4.07/1.00  sup_num_of_loops:                       215
% 4.07/1.00  sup_fw_superposition:                   706
% 4.07/1.00  sup_bw_superposition:                   203
% 4.07/1.00  sup_immediate_simplified:               301
% 4.07/1.00  sup_given_eliminated:                   0
% 4.07/1.00  comparisons_done:                       0
% 4.07/1.00  comparisons_avoided:                    0
% 4.07/1.00  
% 4.07/1.00  ------ Simplifications
% 4.07/1.00  
% 4.07/1.00  
% 4.07/1.00  sim_fw_subset_subsumed:                 35
% 4.07/1.00  sim_bw_subset_subsumed:                 0
% 4.07/1.00  sim_fw_subsumed:                        93
% 4.07/1.00  sim_bw_subsumed:                        2
% 4.07/1.00  sim_fw_subsumption_res:                 0
% 4.07/1.00  sim_bw_subsumption_res:                 0
% 4.07/1.00  sim_tautology_del:                      77
% 4.07/1.00  sim_eq_tautology_del:                   151
% 4.07/1.00  sim_eq_res_simp:                        0
% 4.07/1.00  sim_fw_demodulated:                     51
% 4.07/1.00  sim_bw_demodulated:                     0
% 4.07/1.00  sim_light_normalised:                   188
% 4.07/1.00  sim_joinable_taut:                      0
% 4.07/1.00  sim_joinable_simp:                      0
% 4.07/1.00  sim_ac_normalised:                      0
% 4.07/1.00  sim_smt_subsumption:                    0
% 4.07/1.00  
%------------------------------------------------------------------------------
