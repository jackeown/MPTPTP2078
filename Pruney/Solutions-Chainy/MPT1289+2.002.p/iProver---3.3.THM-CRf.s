%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:15:58 EST 2020

% Result     : Theorem 8.14s
% Output     : CNFRefutation 8.14s
% Verified   : 
% Statistics : Number of formulae       :  241 (5260 expanded)
%              Number of clauses        :  182 (1788 expanded)
%              Number of leaves         :   14 (1112 expanded)
%              Depth                    :   28
%              Number of atoms          :  756 (20728 expanded)
%              Number of equality atoms :  381 (3004 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_tops_1(X1,X0)
           => ( v4_tops_1(k2_pre_topc(X0,X1),X0)
              & v4_tops_1(k1_tops_1(X0,X1),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_tops_1(X1,X0)
             => ( v4_tops_1(k2_pre_topc(X0,X1),X0)
                & v4_tops_1(k1_tops_1(X0,X1),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v4_tops_1(k2_pre_topc(X0,X1),X0)
            | ~ v4_tops_1(k1_tops_1(X0,X1),X0) )
          & v4_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v4_tops_1(k2_pre_topc(X0,X1),X0)
            | ~ v4_tops_1(k1_tops_1(X0,X1),X0) )
          & v4_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ v4_tops_1(k2_pre_topc(X0,X1),X0)
            | ~ v4_tops_1(k1_tops_1(X0,X1),X0) )
          & v4_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ~ v4_tops_1(k2_pre_topc(X0,sK1),X0)
          | ~ v4_tops_1(k1_tops_1(X0,sK1),X0) )
        & v4_tops_1(sK1,X0)
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v4_tops_1(k2_pre_topc(X0,X1),X0)
              | ~ v4_tops_1(k1_tops_1(X0,X1),X0) )
            & v4_tops_1(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ~ v4_tops_1(k2_pre_topc(sK0,X1),sK0)
            | ~ v4_tops_1(k1_tops_1(sK0,X1),sK0) )
          & v4_tops_1(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ( ~ v4_tops_1(k2_pre_topc(sK0,sK1),sK0)
      | ~ v4_tops_1(k1_tops_1(sK0,sK1),sK0) )
    & v4_tops_1(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f31,f38,f37])).

fof(f57,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f39])).

fof(f4,axiom,(
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
    inference(ennf_transformation,[],[f4])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f56,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f32])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f60,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f41])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_tops_1(X1,X0)
          <=> ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_tops_1(X1,X0)
          <=> ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_tops_1(X1,X0)
              | ~ r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              | ~ r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) )
            & ( ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
                & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) )
              | ~ v4_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_tops_1(X1,X0)
              | ~ r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              | ~ r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) )
            & ( ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
                & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) )
              | ~ v4_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)
      | ~ v4_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f58,plain,(
    v4_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f42,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
      | ~ v4_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v4_tops_1(X1,X0)
      | ~ r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
      | ~ r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f59,plain,
    ( ~ v4_tops_1(k2_pre_topc(sK0,sK1),sK0)
    | ~ v4_tops_1(k1_tops_1(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_777,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_789,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_790,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2690,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(k2_pre_topc(X1,X0),u1_struct_0(X1)) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_789,c_790])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_792,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_7810,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(k2_pre_topc(X1,X0),X2) = iProver_top
    | r1_tarski(u1_struct_0(X1),X2) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2690,c_792])).

cnf(c_33479,plain,
    ( r1_tarski(k2_pre_topc(sK0,sK1),X0) = iProver_top
    | r1_tarski(u1_struct_0(sK0),X0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_777,c_7810])).

cnf(c_19,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_20,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_21,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_962,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_963,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_962])).

cnf(c_1412,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,u1_struct_0(X1)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2997,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k2_pre_topc(sK0,sK1),u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1412])).

cnf(c_2998,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,sK1),u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2997])).

cnf(c_7490,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(k2_pre_topc(sK0,sK1),X0)
    | r1_tarski(k2_pre_topc(sK0,sK1),X1) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_21871,plain,
    ( r1_tarski(k2_pre_topc(sK0,sK1),X0)
    | ~ r1_tarski(k2_pre_topc(sK0,sK1),u1_struct_0(sK0))
    | ~ r1_tarski(u1_struct_0(sK0),X0) ),
    inference(instantiation,[status(thm)],[c_7490])).

cnf(c_21872,plain,
    ( r1_tarski(k2_pre_topc(sK0,sK1),X0) = iProver_top
    | r1_tarski(k2_pre_topc(sK0,sK1),u1_struct_0(sK0)) != iProver_top
    | r1_tarski(u1_struct_0(sK0),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21871])).

cnf(c_34047,plain,
    ( r1_tarski(u1_struct_0(sK0),X0) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,sK1),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_33479,c_20,c_21,c_963,c_2998,c_21872])).

cnf(c_34048,plain,
    ( r1_tarski(k2_pre_topc(sK0,sK1),X0) = iProver_top
    | r1_tarski(u1_struct_0(sK0),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_34047])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_782,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k2_pre_topc(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_788,plain,
    ( k2_pre_topc(X0,k2_pre_topc(X0,X1)) = k2_pre_topc(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2661,plain,
    ( k2_pre_topc(X0,k2_pre_topc(X0,k1_tops_1(X0,X1))) = k2_pre_topc(X0,k1_tops_1(X0,X1))
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_782,c_788])).

cnf(c_12488,plain,
    ( k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = k2_pre_topc(sK0,k1_tops_1(sK0,sK1))
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_777,c_2661])).

cnf(c_994,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1126,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_12522,plain,
    ( k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12488,c_19,c_18,c_994,c_1126])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k2_pre_topc(X1,X0),k2_pre_topc(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_786,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(k2_pre_topc(X1,X0),k2_pre_topc(X1,X2)) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_12527,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),X0) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k2_pre_topc(sK0,X0)) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_12522,c_786])).

cnf(c_995,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_994])).

cnf(c_1129,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1130,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1129])).

cnf(c_13384,plain,
    ( r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k2_pre_topc(sK0,X0)) = iProver_top
    | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12527,c_20,c_21,c_995,c_1130])).

cnf(c_13385,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),X0) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k2_pre_topc(sK0,X0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_13384])).

cnf(c_776,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_793,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_4,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_791,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2660,plain,
    ( k2_pre_topc(X0,k2_pre_topc(X0,X1)) = k2_pre_topc(X0,X1)
    | r1_tarski(X1,u1_struct_0(X0)) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_791,c_788])).

cnf(c_6068,plain,
    ( k2_pre_topc(X0,k2_pre_topc(X0,u1_struct_0(X0))) = k2_pre_topc(X0,u1_struct_0(X0))
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_793,c_2660])).

cnf(c_7337,plain,
    ( k2_pre_topc(sK0,k2_pre_topc(sK0,u1_struct_0(sK0))) = k2_pre_topc(sK0,u1_struct_0(sK0)) ),
    inference(superposition,[status(thm)],[c_776,c_6068])).

cnf(c_7570,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK0,u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,u1_struct_0(sK0))) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7337,c_786])).

cnf(c_957,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,u1_struct_0(X1)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1417,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X0)) ),
    inference(instantiation,[status(thm)],[c_957])).

cnf(c_1419,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1417])).

cnf(c_1421,plain,
    ( m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1419])).

cnf(c_1418,plain,
    ( r1_tarski(u1_struct_0(X0),u1_struct_0(X0)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1423,plain,
    ( r1_tarski(u1_struct_0(X0),u1_struct_0(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1418])).

cnf(c_1425,plain,
    ( r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1423])).

cnf(c_3044,plain,
    ( m1_subset_1(k2_pre_topc(X0,u1_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_3045,plain,
    ( m1_subset_1(k2_pre_topc(X0,u1_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3044])).

cnf(c_3047,plain,
    ( m1_subset_1(k2_pre_topc(sK0,u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3045])).

cnf(c_8362,plain,
    ( r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,u1_struct_0(sK0))) = iProver_top
    | r1_tarski(X0,k2_pre_topc(sK0,u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7570,c_20,c_1421,c_1425,c_3047])).

cnf(c_8363,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK0,u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,u1_struct_0(sK0))) = iProver_top ),
    inference(renaming,[status(thm)],[c_8362])).

cnf(c_8373,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK0,u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,X0),X1) = iProver_top
    | r1_tarski(k2_pre_topc(sK0,u1_struct_0(sK0)),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_8363,c_792])).

cnf(c_29510,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),u1_struct_0(sK0)) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))),X0) = iProver_top
    | r1_tarski(k2_pre_topc(sK0,u1_struct_0(sK0)),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_13385,c_8373])).

cnf(c_29528,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),X0) = iProver_top
    | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),u1_struct_0(sK0)) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,u1_struct_0(sK0)),X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_29510,c_12522])).

cnf(c_12,plain,
    ( ~ v4_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_783,plain,
    ( v4_tops_1(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_7568,plain,
    ( v4_tops_1(k2_pre_topc(sK0,u1_struct_0(sK0)),sK0) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,u1_struct_0(sK0))),k2_pre_topc(sK0,u1_struct_0(sK0))) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7337,c_783])).

cnf(c_7844,plain,
    ( r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,u1_struct_0(sK0))),k2_pre_topc(sK0,u1_struct_0(sK0))) = iProver_top
    | v4_tops_1(k2_pre_topc(sK0,u1_struct_0(sK0)),sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7568,c_20,c_1421,c_1425,c_3047])).

cnf(c_7845,plain,
    ( v4_tops_1(k2_pre_topc(sK0,u1_struct_0(sK0)),sK0) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,u1_struct_0(sK0))),k2_pre_topc(sK0,u1_struct_0(sK0))) = iProver_top ),
    inference(renaming,[status(thm)],[c_7844])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_780,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2)) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1501,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(k1_tops_1(X1,X2),X3) != iProver_top
    | r1_tarski(k1_tops_1(X1,X0),X3) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_780,c_792])).

cnf(c_5590,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),X1) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),X1) = iProver_top
    | r1_tarski(sK1,X0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_777,c_1501])).

cnf(c_6103,plain,
    ( r1_tarski(sK1,X0) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),X1) = iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5590,c_20])).

cnf(c_6104,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),X1) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),X1) = iProver_top
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_6103])).

cnf(c_6114,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),X1) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),X1) = iProver_top
    | r1_tarski(sK1,k2_pre_topc(sK0,X0)) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_789,c_6104])).

cnf(c_6646,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,X0)) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),X1) = iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6114,c_20])).

cnf(c_6647,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),X1) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),X1) = iProver_top
    | r1_tarski(sK1,k2_pre_topc(sK0,X0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_6646])).

cnf(c_6656,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,X0))) = iProver_top
    | r1_tarski(sK1,k2_pre_topc(sK0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_793,c_6647])).

cnf(c_9687,plain,
    ( m1_subset_1(k2_pre_topc(sK0,u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,u1_struct_0(sK0)))) = iProver_top
    | r1_tarski(sK1,k2_pre_topc(sK0,k2_pre_topc(sK0,u1_struct_0(sK0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7337,c_6656])).

cnf(c_9713,plain,
    ( m1_subset_1(k2_pre_topc(sK0,u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,u1_struct_0(sK0)))) = iProver_top
    | r1_tarski(sK1,k2_pre_topc(sK0,u1_struct_0(sK0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9687,c_7337])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_787,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(X1,X0)) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1527,plain,
    ( r1_tarski(X0,k2_pre_topc(X1,X0)) = iProver_top
    | r1_tarski(X0,u1_struct_0(X1)) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_791,c_787])).

cnf(c_1075,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_777,c_790])).

cnf(c_1502,plain,
    ( r1_tarski(u1_struct_0(sK0),X0) != iProver_top
    | r1_tarski(sK1,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1075,c_792])).

cnf(c_4300,plain,
    ( r1_tarski(u1_struct_0(sK0),u1_struct_0(X0)) != iProver_top
    | r1_tarski(sK1,k2_pre_topc(X0,u1_struct_0(sK0))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1527,c_1502])).

cnf(c_4338,plain,
    ( r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0)) != iProver_top
    | r1_tarski(sK1,k2_pre_topc(sK0,u1_struct_0(sK0))) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4300])).

cnf(c_9929,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,u1_struct_0(sK0)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9713,c_20,c_1421,c_1425,c_3047,c_4338])).

cnf(c_9934,plain,
    ( r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,u1_struct_0(sK0))),X0) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_9929,c_792])).

cnf(c_10190,plain,
    ( v4_tops_1(k2_pre_topc(sK0,u1_struct_0(sK0)),sK0) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,u1_struct_0(sK0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_7845,c_9934])).

cnf(c_2662,plain,
    ( k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)) = k2_pre_topc(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_777,c_788])).

cnf(c_998,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_3123,plain,
    ( k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2662,c_19,c_18,c_998])).

cnf(c_3126,plain,
    ( v4_tops_1(k2_pre_topc(sK0,sK1),sK0) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_pre_topc(sK0,sK1)) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3123,c_783])).

cnf(c_17,negated_conjecture,
    ( v4_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_22,plain,
    ( v4_tops_1(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_990,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_991,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK1,k2_pre_topc(sK0,sK1)) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_990])).

cnf(c_1019,plain,
    ( ~ v4_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1020,plain,
    ( v4_tops_1(sK1,sK0) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1019])).

cnf(c_1401,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,k2_pre_topc(sK0,sK1))
    | r1_tarski(X0,k2_pre_topc(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2520,plain,
    ( r1_tarski(X0,k2_pre_topc(sK0,sK1))
    | ~ r1_tarski(X0,sK1)
    | ~ r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_1401])).

cnf(c_2787,plain,
    ( r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_pre_topc(sK0,sK1))
    | ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK1)
    | ~ r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_2520])).

cnf(c_2788,plain,
    ( r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_pre_topc(sK0,sK1)) = iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK1) != iProver_top
    | r1_tarski(sK1,k2_pre_topc(sK0,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2787])).

cnf(c_3138,plain,
    ( r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_pre_topc(sK0,sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3126,c_20,c_21,c_22,c_991,c_1020,c_2788])).

cnf(c_6663,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1)) = iProver_top
    | r1_tarski(sK1,k2_pre_topc(sK0,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3138,c_6647])).

cnf(c_1114,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,k2_pre_topc(sK0,sK1))
    | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1409,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))
    | ~ r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_1114])).

cnf(c_1410,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) = iProver_top
    | r1_tarski(sK1,k2_pre_topc(sK0,sK1)) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1409])).

cnf(c_1446,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,sK1)
    | r1_tarski(X0,sK1) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1765,plain,
    ( ~ r1_tarski(X0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))
    | r1_tarski(X0,sK1)
    | ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK1) ),
    inference(instantiation,[status(thm)],[c_1446])).

cnf(c_2780,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK1)
    | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))
    | r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(instantiation,[status(thm)],[c_1765])).

cnf(c_2781,plain,
    ( r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK1) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2780])).

cnf(c_5499,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_2520])).

cnf(c_5512,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1)) = iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),sK1) != iProver_top
    | r1_tarski(sK1,k2_pre_topc(sK0,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5499])).

cnf(c_8870,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6663,c_20,c_21,c_22,c_963,c_991,c_1020,c_1410,c_2781,c_5512])).

cnf(c_8875,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),X0) = iProver_top
    | r1_tarski(k2_pre_topc(sK0,sK1),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8870,c_792])).

cnf(c_9060,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,u1_struct_0(sK0))) = iProver_top
    | r1_tarski(sK1,k2_pre_topc(sK0,u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8363,c_8875])).

cnf(c_10939,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,u1_struct_0(sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10190,c_20,c_21,c_1425,c_4338,c_9060])).

cnf(c_29509,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),X0) = iProver_top
    | r1_tarski(k2_pre_topc(sK0,u1_struct_0(sK0)),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_10939,c_8373])).

cnf(c_29971,plain,
    ( r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),X0) = iProver_top
    | r1_tarski(k2_pre_topc(sK0,u1_struct_0(sK0)),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_29528,c_20,c_21,c_995,c_29509])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_794,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_29981,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = X0
    | r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,u1_struct_0(sK0)),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_29971,c_794])).

cnf(c_34062,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
    | r1_tarski(k2_pre_topc(sK0,u1_struct_0(sK0)),k2_pre_topc(sK0,sK1)) != iProver_top
    | r1_tarski(u1_struct_0(sK0),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_34048,c_29981])).

cnf(c_11,plain,
    ( ~ v4_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1016,plain,
    ( ~ v4_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK1,k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1017,plain,
    ( v4_tops_1(sK1,sK0) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK1,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1016])).

cnf(c_1101,plain,
    ( m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1108,plain,
    ( m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1101])).

cnf(c_1046,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,sK1)
    | r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1454,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK1)
    | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))),k2_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_1046])).

cnf(c_1455,plain,
    ( m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK1) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))),k2_pre_topc(sK0,sK1)) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1454])).

cnf(c_1229,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))
    | r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2279,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))
    | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_1229])).

cnf(c_2280,plain,
    ( m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2279])).

cnf(c_2524,plain,
    ( ~ r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))))
    | r1_tarski(X0,k2_pre_topc(sK0,sK1))
    | ~ r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))),k2_pre_topc(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_1401])).

cnf(c_3119,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))),k2_pre_topc(sK0,sK1))
    | ~ r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))))
    | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k2_pre_topc(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_2524])).

cnf(c_3120,plain,
    ( r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))),k2_pre_topc(sK0,sK1)) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k2_pre_topc(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3119])).

cnf(c_7238,plain,
    ( ~ r1_tarski(X0,k2_pre_topc(X1,X2))
    | ~ r1_tarski(k2_pre_topc(X1,X2),X0)
    | k2_pre_topc(X1,X2) = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_14809,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k2_pre_topc(sK0,sK1))
    | ~ r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))
    | k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_7238])).

cnf(c_14810,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
    | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k2_pre_topc(sK0,sK1)) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14809])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,k1_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_781,plain,
    ( k1_tops_1(X0,k1_tops_1(X0,X1)) = k1_tops_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2692,plain,
    ( k1_tops_1(X0,k1_tops_1(X0,k2_pre_topc(X0,X1))) = k1_tops_1(X0,k2_pre_topc(X0,X1))
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_789,c_781])).

cnf(c_15583,plain,
    ( k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) = k1_tops_1(sK0,k2_pre_topc(sK0,sK1))
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_777,c_2692])).

cnf(c_1099,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) = k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_15889,plain,
    ( k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) = k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_15583,c_19,c_18,c_962,c_1099])).

cnf(c_15897,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),X0) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,X0)) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_15889,c_780])).

cnf(c_16104,plain,
    ( r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,X0)) = iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15897,c_20,c_21,c_963,c_1108])).

cnf(c_16105,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),X0) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,X0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_16104])).

cnf(c_9686,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) = iProver_top
    | r1_tarski(sK1,k2_pre_topc(sK0,k2_pre_topc(sK0,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3123,c_6656])).

cnf(c_9720,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) = iProver_top
    | r1_tarski(sK1,k2_pre_topc(sK0,sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9686,c_3123])).

cnf(c_9900,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9720,c_20,c_21,c_963,c_991,c_1410])).

cnf(c_9906,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,sK1)
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9900,c_794])).

cnf(c_16123,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,sK1)
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_16105,c_9906])).

cnf(c_16645,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_16123,c_20,c_21,c_22,c_1020])).

cnf(c_784,plain,
    ( v4_tops_1(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_16692,plain,
    ( v4_tops_1(k2_pre_topc(sK0,sK1),sK0) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_16645,c_784])).

cnf(c_12531,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_12522,c_786])).

cnf(c_13517,plain,
    ( r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = iProver_top
    | r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12531,c_20,c_21,c_995,c_1130])).

cnf(c_13518,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = iProver_top ),
    inference(renaming,[status(thm)],[c_13517])).

cnf(c_10,plain,
    ( v4_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
    | ~ r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_785,plain,
    ( v4_tops_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0))) != iProver_top
    | r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3968,plain,
    ( v4_tops_1(k2_pre_topc(sK0,sK1),sK0) = iProver_top
    | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_pre_topc(sK0,sK1)) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3123,c_785])).

cnf(c_4711,plain,
    ( r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))) != iProver_top
    | v4_tops_1(k2_pre_topc(sK0,sK1),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3968,c_20,c_21,c_22,c_963,c_991,c_1020,c_2788])).

cnf(c_4712,plain,
    ( v4_tops_1(k2_pre_topc(sK0,sK1),sK0) = iProver_top
    | r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_4711])).

cnf(c_16658,plain,
    ( v4_tops_1(k2_pre_topc(sK0,sK1),sK0) = iProver_top
    | r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_16645,c_4712])).

cnf(c_16821,plain,
    ( v4_tops_1(k2_pre_topc(sK0,sK1),sK0) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK1,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_13518,c_16658])).

cnf(c_37013,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_34062,c_20,c_21,c_22,c_963,c_991,c_995,c_1017,c_1020,c_1108,c_1410,c_1455,c_2280,c_3120,c_14810,c_16692,c_16821])).

cnf(c_37111,plain,
    ( v4_tops_1(k1_tops_1(sK0,sK1),sK0) = iProver_top
    | m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,sK1)) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,k1_tops_1(sK0,sK1)))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_37013,c_785])).

cnf(c_1700,plain,
    ( k1_tops_1(sK0,k1_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_777,c_781])).

cnf(c_1002,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k1_tops_1(sK0,k1_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1856,plain,
    ( k1_tops_1(sK0,k1_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1700,c_19,c_18,c_1002])).

cnf(c_37203,plain,
    ( v4_tops_1(k1_tops_1(sK0,sK1),sK0) = iProver_top
    | m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1)) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_37111,c_1856,c_16645,c_37013])).

cnf(c_1471,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1474,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1471])).

cnf(c_16,negated_conjecture,
    ( ~ v4_tops_1(k1_tops_1(sK0,sK1),sK0)
    | ~ v4_tops_1(k2_pre_topc(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_23,plain,
    ( v4_tops_1(k1_tops_1(sK0,sK1),sK0) != iProver_top
    | v4_tops_1(k2_pre_topc(sK0,sK1),sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_37203,c_16821,c_5512,c_2781,c_1474,c_1410,c_1020,c_1017,c_995,c_991,c_963,c_23,c_22,c_21,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:39:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 8.14/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.14/1.49  
% 8.14/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 8.14/1.49  
% 8.14/1.49  ------  iProver source info
% 8.14/1.49  
% 8.14/1.49  git: date: 2020-06-30 10:37:57 +0100
% 8.14/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 8.14/1.49  git: non_committed_changes: false
% 8.14/1.49  git: last_make_outside_of_git: false
% 8.14/1.49  
% 8.14/1.49  ------ 
% 8.14/1.49  ------ Parsing...
% 8.14/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 8.14/1.49  
% 8.14/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 8.14/1.49  
% 8.14/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 8.14/1.49  
% 8.14/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.14/1.49  ------ Proving...
% 8.14/1.49  ------ Problem Properties 
% 8.14/1.49  
% 8.14/1.49  
% 8.14/1.49  clauses                                 19
% 8.14/1.49  conjectures                             4
% 8.14/1.49  EPR                                     5
% 8.14/1.49  Horn                                    19
% 8.14/1.49  unary                                   4
% 8.14/1.49  binary                                  3
% 8.14/1.49  lits                                    54
% 8.14/1.49  lits eq                                 3
% 8.14/1.49  fd_pure                                 0
% 8.14/1.49  fd_pseudo                               0
% 8.14/1.49  fd_cond                                 0
% 8.14/1.49  fd_pseudo_cond                          1
% 8.14/1.49  AC symbols                              0
% 8.14/1.49  
% 8.14/1.49  ------ Input Options Time Limit: Unbounded
% 8.14/1.49  
% 8.14/1.49  
% 8.14/1.49  ------ 
% 8.14/1.49  Current options:
% 8.14/1.49  ------ 
% 8.14/1.49  
% 8.14/1.49  
% 8.14/1.49  
% 8.14/1.49  
% 8.14/1.49  ------ Proving...
% 8.14/1.49  
% 8.14/1.49  
% 8.14/1.49  % SZS status Theorem for theBenchmark.p
% 8.14/1.49  
% 8.14/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 8.14/1.49  
% 8.14/1.49  fof(f12,conjecture,(
% 8.14/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_tops_1(X1,X0) => (v4_tops_1(k2_pre_topc(X0,X1),X0) & v4_tops_1(k1_tops_1(X0,X1),X0)))))),
% 8.14/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.14/1.49  
% 8.14/1.49  fof(f13,negated_conjecture,(
% 8.14/1.49    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_tops_1(X1,X0) => (v4_tops_1(k2_pre_topc(X0,X1),X0) & v4_tops_1(k1_tops_1(X0,X1),X0)))))),
% 8.14/1.49    inference(negated_conjecture,[],[f12])).
% 8.14/1.49  
% 8.14/1.49  fof(f30,plain,(
% 8.14/1.49    ? [X0] : (? [X1] : (((~v4_tops_1(k2_pre_topc(X0,X1),X0) | ~v4_tops_1(k1_tops_1(X0,X1),X0)) & v4_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 8.14/1.49    inference(ennf_transformation,[],[f13])).
% 8.14/1.49  
% 8.14/1.49  fof(f31,plain,(
% 8.14/1.49    ? [X0] : (? [X1] : ((~v4_tops_1(k2_pre_topc(X0,X1),X0) | ~v4_tops_1(k1_tops_1(X0,X1),X0)) & v4_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 8.14/1.49    inference(flattening,[],[f30])).
% 8.14/1.49  
% 8.14/1.49  fof(f38,plain,(
% 8.14/1.49    ( ! [X0] : (? [X1] : ((~v4_tops_1(k2_pre_topc(X0,X1),X0) | ~v4_tops_1(k1_tops_1(X0,X1),X0)) & v4_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((~v4_tops_1(k2_pre_topc(X0,sK1),X0) | ~v4_tops_1(k1_tops_1(X0,sK1),X0)) & v4_tops_1(sK1,X0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 8.14/1.49    introduced(choice_axiom,[])).
% 8.14/1.49  
% 8.14/1.49  fof(f37,plain,(
% 8.14/1.49    ? [X0] : (? [X1] : ((~v4_tops_1(k2_pre_topc(X0,X1),X0) | ~v4_tops_1(k1_tops_1(X0,X1),X0)) & v4_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((~v4_tops_1(k2_pre_topc(sK0,X1),sK0) | ~v4_tops_1(k1_tops_1(sK0,X1),sK0)) & v4_tops_1(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 8.14/1.49    introduced(choice_axiom,[])).
% 8.14/1.49  
% 8.14/1.49  fof(f39,plain,(
% 8.14/1.49    ((~v4_tops_1(k2_pre_topc(sK0,sK1),sK0) | ~v4_tops_1(k1_tops_1(sK0,sK1),sK0)) & v4_tops_1(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 8.14/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f31,f38,f37])).
% 8.14/1.49  
% 8.14/1.49  fof(f57,plain,(
% 8.14/1.49    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 8.14/1.49    inference(cnf_transformation,[],[f39])).
% 8.14/1.49  
% 8.14/1.49  fof(f4,axiom,(
% 8.14/1.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 8.14/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.14/1.49  
% 8.14/1.49  fof(f16,plain,(
% 8.14/1.49    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 8.14/1.49    inference(ennf_transformation,[],[f4])).
% 8.14/1.49  
% 8.14/1.49  fof(f17,plain,(
% 8.14/1.49    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 8.14/1.49    inference(flattening,[],[f16])).
% 8.14/1.49  
% 8.14/1.49  fof(f46,plain,(
% 8.14/1.49    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 8.14/1.49    inference(cnf_transformation,[],[f17])).
% 8.14/1.49  
% 8.14/1.49  fof(f3,axiom,(
% 8.14/1.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 8.14/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.14/1.49  
% 8.14/1.49  fof(f34,plain,(
% 8.14/1.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 8.14/1.49    inference(nnf_transformation,[],[f3])).
% 8.14/1.49  
% 8.14/1.49  fof(f44,plain,(
% 8.14/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 8.14/1.49    inference(cnf_transformation,[],[f34])).
% 8.14/1.49  
% 8.14/1.49  fof(f2,axiom,(
% 8.14/1.49    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 8.14/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.14/1.49  
% 8.14/1.49  fof(f14,plain,(
% 8.14/1.49    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 8.14/1.49    inference(ennf_transformation,[],[f2])).
% 8.14/1.49  
% 8.14/1.49  fof(f15,plain,(
% 8.14/1.49    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 8.14/1.49    inference(flattening,[],[f14])).
% 8.14/1.49  
% 8.14/1.49  fof(f43,plain,(
% 8.14/1.49    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 8.14/1.49    inference(cnf_transformation,[],[f15])).
% 8.14/1.49  
% 8.14/1.49  fof(f56,plain,(
% 8.14/1.49    l1_pre_topc(sK0)),
% 8.14/1.49    inference(cnf_transformation,[],[f39])).
% 8.14/1.49  
% 8.14/1.49  fof(f9,axiom,(
% 8.14/1.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 8.14/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.14/1.49  
% 8.14/1.49  fof(f24,plain,(
% 8.14/1.49    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 8.14/1.49    inference(ennf_transformation,[],[f9])).
% 8.14/1.49  
% 8.14/1.49  fof(f25,plain,(
% 8.14/1.49    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 8.14/1.49    inference(flattening,[],[f24])).
% 8.14/1.49  
% 8.14/1.49  fof(f53,plain,(
% 8.14/1.49    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 8.14/1.49    inference(cnf_transformation,[],[f25])).
% 8.14/1.49  
% 8.14/1.49  fof(f5,axiom,(
% 8.14/1.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)))),
% 8.14/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.14/1.49  
% 8.14/1.49  fof(f18,plain,(
% 8.14/1.49    ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 8.14/1.49    inference(ennf_transformation,[],[f5])).
% 8.14/1.49  
% 8.14/1.49  fof(f19,plain,(
% 8.14/1.49    ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 8.14/1.49    inference(flattening,[],[f18])).
% 8.14/1.49  
% 8.14/1.49  fof(f47,plain,(
% 8.14/1.49    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 8.14/1.49    inference(cnf_transformation,[],[f19])).
% 8.14/1.49  
% 8.14/1.49  fof(f7,axiom,(
% 8.14/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))))))),
% 8.14/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.14/1.49  
% 8.14/1.49  fof(f21,plain,(
% 8.14/1.49    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 8.14/1.49    inference(ennf_transformation,[],[f7])).
% 8.14/1.49  
% 8.14/1.49  fof(f22,plain,(
% 8.14/1.49    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 8.14/1.49    inference(flattening,[],[f21])).
% 8.14/1.49  
% 8.14/1.49  fof(f49,plain,(
% 8.14/1.49    ( ! [X2,X0,X1] : (r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 8.14/1.49    inference(cnf_transformation,[],[f22])).
% 8.14/1.49  
% 8.14/1.49  fof(f1,axiom,(
% 8.14/1.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 8.14/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.14/1.49  
% 8.14/1.49  fof(f32,plain,(
% 8.14/1.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 8.14/1.49    inference(nnf_transformation,[],[f1])).
% 8.14/1.49  
% 8.14/1.49  fof(f33,plain,(
% 8.14/1.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 8.14/1.49    inference(flattening,[],[f32])).
% 8.14/1.49  
% 8.14/1.49  fof(f41,plain,(
% 8.14/1.49    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 8.14/1.49    inference(cnf_transformation,[],[f33])).
% 8.14/1.49  
% 8.14/1.49  fof(f60,plain,(
% 8.14/1.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 8.14/1.49    inference(equality_resolution,[],[f41])).
% 8.14/1.49  
% 8.14/1.49  fof(f45,plain,(
% 8.14/1.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 8.14/1.49    inference(cnf_transformation,[],[f34])).
% 8.14/1.49  
% 8.14/1.49  fof(f8,axiom,(
% 8.14/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_tops_1(X1,X0) <=> (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)))))),
% 8.14/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.14/1.49  
% 8.14/1.49  fof(f23,plain,(
% 8.14/1.49    ! [X0] : (! [X1] : ((v4_tops_1(X1,X0) <=> (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 8.14/1.49    inference(ennf_transformation,[],[f8])).
% 8.14/1.49  
% 8.14/1.49  fof(f35,plain,(
% 8.14/1.49    ! [X0] : (! [X1] : (((v4_tops_1(X1,X0) | (~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1))) & ((r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) | ~v4_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 8.14/1.49    inference(nnf_transformation,[],[f23])).
% 8.14/1.49  
% 8.14/1.49  fof(f36,plain,(
% 8.14/1.49    ! [X0] : (! [X1] : (((v4_tops_1(X1,X0) | ~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) & ((r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) | ~v4_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 8.14/1.49    inference(flattening,[],[f35])).
% 8.14/1.49  
% 8.14/1.49  fof(f50,plain,(
% 8.14/1.49    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) | ~v4_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 8.14/1.49    inference(cnf_transformation,[],[f36])).
% 8.14/1.49  
% 8.14/1.49  fof(f11,axiom,(
% 8.14/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 8.14/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.14/1.49  
% 8.14/1.49  fof(f28,plain,(
% 8.14/1.49    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 8.14/1.49    inference(ennf_transformation,[],[f11])).
% 8.14/1.49  
% 8.14/1.49  fof(f29,plain,(
% 8.14/1.49    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 8.14/1.49    inference(flattening,[],[f28])).
% 8.14/1.49  
% 8.14/1.49  fof(f55,plain,(
% 8.14/1.49    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 8.14/1.49    inference(cnf_transformation,[],[f29])).
% 8.14/1.49  
% 8.14/1.49  fof(f6,axiom,(
% 8.14/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 8.14/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.14/1.49  
% 8.14/1.49  fof(f20,plain,(
% 8.14/1.49    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 8.14/1.49    inference(ennf_transformation,[],[f6])).
% 8.14/1.49  
% 8.14/1.49  fof(f48,plain,(
% 8.14/1.49    ( ! [X0,X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 8.14/1.49    inference(cnf_transformation,[],[f20])).
% 8.14/1.49  
% 8.14/1.49  fof(f58,plain,(
% 8.14/1.49    v4_tops_1(sK1,sK0)),
% 8.14/1.49    inference(cnf_transformation,[],[f39])).
% 8.14/1.49  
% 8.14/1.49  fof(f42,plain,(
% 8.14/1.49    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 8.14/1.49    inference(cnf_transformation,[],[f33])).
% 8.14/1.49  
% 8.14/1.49  fof(f51,plain,(
% 8.14/1.49    ( ! [X0,X1] : (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~v4_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 8.14/1.49    inference(cnf_transformation,[],[f36])).
% 8.14/1.49  
% 8.14/1.49  fof(f10,axiom,(
% 8.14/1.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)))),
% 8.14/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.14/1.49  
% 8.14/1.49  fof(f26,plain,(
% 8.14/1.49    ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 8.14/1.49    inference(ennf_transformation,[],[f10])).
% 8.14/1.49  
% 8.14/1.49  fof(f27,plain,(
% 8.14/1.49    ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 8.14/1.49    inference(flattening,[],[f26])).
% 8.14/1.49  
% 8.14/1.49  fof(f54,plain,(
% 8.14/1.49    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 8.14/1.49    inference(cnf_transformation,[],[f27])).
% 8.14/1.49  
% 8.14/1.49  fof(f52,plain,(
% 8.14/1.49    ( ! [X0,X1] : (v4_tops_1(X1,X0) | ~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 8.14/1.49    inference(cnf_transformation,[],[f36])).
% 8.14/1.49  
% 8.14/1.49  fof(f59,plain,(
% 8.14/1.49    ~v4_tops_1(k2_pre_topc(sK0,sK1),sK0) | ~v4_tops_1(k1_tops_1(sK0,sK1),sK0)),
% 8.14/1.49    inference(cnf_transformation,[],[f39])).
% 8.14/1.49  
% 8.14/1.49  cnf(c_18,negated_conjecture,
% 8.14/1.49      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 8.14/1.49      inference(cnf_transformation,[],[f57]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_777,plain,
% 8.14/1.49      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 8.14/1.49      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_6,plain,
% 8.14/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 8.14/1.49      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 8.14/1.49      | ~ l1_pre_topc(X1) ),
% 8.14/1.49      inference(cnf_transformation,[],[f46]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_789,plain,
% 8.14/1.49      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 8.14/1.49      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 8.14/1.49      | l1_pre_topc(X1) != iProver_top ),
% 8.14/1.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_5,plain,
% 8.14/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 8.14/1.49      inference(cnf_transformation,[],[f44]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_790,plain,
% 8.14/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 8.14/1.49      | r1_tarski(X0,X1) = iProver_top ),
% 8.14/1.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_2690,plain,
% 8.14/1.49      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 8.14/1.49      | r1_tarski(k2_pre_topc(X1,X0),u1_struct_0(X1)) = iProver_top
% 8.14/1.49      | l1_pre_topc(X1) != iProver_top ),
% 8.14/1.49      inference(superposition,[status(thm)],[c_789,c_790]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_3,plain,
% 8.14/1.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 8.14/1.49      inference(cnf_transformation,[],[f43]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_792,plain,
% 8.14/1.49      ( r1_tarski(X0,X1) != iProver_top
% 8.14/1.49      | r1_tarski(X1,X2) != iProver_top
% 8.14/1.49      | r1_tarski(X0,X2) = iProver_top ),
% 8.14/1.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_7810,plain,
% 8.14/1.49      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 8.14/1.49      | r1_tarski(k2_pre_topc(X1,X0),X2) = iProver_top
% 8.14/1.49      | r1_tarski(u1_struct_0(X1),X2) != iProver_top
% 8.14/1.49      | l1_pre_topc(X1) != iProver_top ),
% 8.14/1.49      inference(superposition,[status(thm)],[c_2690,c_792]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_33479,plain,
% 8.14/1.49      ( r1_tarski(k2_pre_topc(sK0,sK1),X0) = iProver_top
% 8.14/1.49      | r1_tarski(u1_struct_0(sK0),X0) != iProver_top
% 8.14/1.49      | l1_pre_topc(sK0) != iProver_top ),
% 8.14/1.49      inference(superposition,[status(thm)],[c_777,c_7810]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_19,negated_conjecture,
% 8.14/1.49      ( l1_pre_topc(sK0) ),
% 8.14/1.49      inference(cnf_transformation,[],[f56]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_20,plain,
% 8.14/1.49      ( l1_pre_topc(sK0) = iProver_top ),
% 8.14/1.49      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_21,plain,
% 8.14/1.49      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 8.14/1.49      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_962,plain,
% 8.14/1.49      ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 8.14/1.49      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 8.14/1.49      | ~ l1_pre_topc(sK0) ),
% 8.14/1.49      inference(instantiation,[status(thm)],[c_6]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_963,plain,
% 8.14/1.49      ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 8.14/1.49      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.14/1.49      | l1_pre_topc(sK0) != iProver_top ),
% 8.14/1.49      inference(predicate_to_equality,[status(thm)],[c_962]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_1412,plain,
% 8.14/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 8.14/1.49      | r1_tarski(X0,u1_struct_0(X1)) ),
% 8.14/1.49      inference(instantiation,[status(thm)],[c_5]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_2997,plain,
% 8.14/1.49      ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 8.14/1.49      | r1_tarski(k2_pre_topc(sK0,sK1),u1_struct_0(sK0)) ),
% 8.14/1.49      inference(instantiation,[status(thm)],[c_1412]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_2998,plain,
% 8.14/1.49      ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.14/1.49      | r1_tarski(k2_pre_topc(sK0,sK1),u1_struct_0(sK0)) = iProver_top ),
% 8.14/1.49      inference(predicate_to_equality,[status(thm)],[c_2997]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_7490,plain,
% 8.14/1.49      ( ~ r1_tarski(X0,X1)
% 8.14/1.49      | ~ r1_tarski(k2_pre_topc(sK0,sK1),X0)
% 8.14/1.49      | r1_tarski(k2_pre_topc(sK0,sK1),X1) ),
% 8.14/1.49      inference(instantiation,[status(thm)],[c_3]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_21871,plain,
% 8.14/1.49      ( r1_tarski(k2_pre_topc(sK0,sK1),X0)
% 8.14/1.49      | ~ r1_tarski(k2_pre_topc(sK0,sK1),u1_struct_0(sK0))
% 8.14/1.49      | ~ r1_tarski(u1_struct_0(sK0),X0) ),
% 8.14/1.49      inference(instantiation,[status(thm)],[c_7490]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_21872,plain,
% 8.14/1.49      ( r1_tarski(k2_pre_topc(sK0,sK1),X0) = iProver_top
% 8.14/1.49      | r1_tarski(k2_pre_topc(sK0,sK1),u1_struct_0(sK0)) != iProver_top
% 8.14/1.49      | r1_tarski(u1_struct_0(sK0),X0) != iProver_top ),
% 8.14/1.49      inference(predicate_to_equality,[status(thm)],[c_21871]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_34047,plain,
% 8.14/1.49      ( r1_tarski(u1_struct_0(sK0),X0) != iProver_top
% 8.14/1.49      | r1_tarski(k2_pre_topc(sK0,sK1),X0) = iProver_top ),
% 8.14/1.49      inference(global_propositional_subsumption,
% 8.14/1.49                [status(thm)],
% 8.14/1.49                [c_33479,c_20,c_21,c_963,c_2998,c_21872]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_34048,plain,
% 8.14/1.49      ( r1_tarski(k2_pre_topc(sK0,sK1),X0) = iProver_top
% 8.14/1.49      | r1_tarski(u1_struct_0(sK0),X0) != iProver_top ),
% 8.14/1.49      inference(renaming,[status(thm)],[c_34047]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_13,plain,
% 8.14/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 8.14/1.49      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 8.14/1.49      | ~ l1_pre_topc(X1) ),
% 8.14/1.49      inference(cnf_transformation,[],[f53]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_782,plain,
% 8.14/1.49      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 8.14/1.49      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 8.14/1.49      | l1_pre_topc(X1) != iProver_top ),
% 8.14/1.49      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_7,plain,
% 8.14/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 8.14/1.49      | ~ l1_pre_topc(X1)
% 8.14/1.49      | k2_pre_topc(X1,k2_pre_topc(X1,X0)) = k2_pre_topc(X1,X0) ),
% 8.14/1.49      inference(cnf_transformation,[],[f47]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_788,plain,
% 8.14/1.49      ( k2_pre_topc(X0,k2_pre_topc(X0,X1)) = k2_pre_topc(X0,X1)
% 8.14/1.49      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 8.14/1.49      | l1_pre_topc(X0) != iProver_top ),
% 8.14/1.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_2661,plain,
% 8.14/1.49      ( k2_pre_topc(X0,k2_pre_topc(X0,k1_tops_1(X0,X1))) = k2_pre_topc(X0,k1_tops_1(X0,X1))
% 8.14/1.49      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 8.14/1.49      | l1_pre_topc(X0) != iProver_top ),
% 8.14/1.49      inference(superposition,[status(thm)],[c_782,c_788]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_12488,plain,
% 8.14/1.49      ( k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = k2_pre_topc(sK0,k1_tops_1(sK0,sK1))
% 8.14/1.49      | l1_pre_topc(sK0) != iProver_top ),
% 8.14/1.49      inference(superposition,[status(thm)],[c_777,c_2661]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_994,plain,
% 8.14/1.49      ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 8.14/1.49      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 8.14/1.49      | ~ l1_pre_topc(sK0) ),
% 8.14/1.49      inference(instantiation,[status(thm)],[c_13]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_1126,plain,
% 8.14/1.49      ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 8.14/1.49      | ~ l1_pre_topc(sK0)
% 8.14/1.49      | k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) ),
% 8.14/1.49      inference(instantiation,[status(thm)],[c_7]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_12522,plain,
% 8.14/1.49      ( k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) ),
% 8.14/1.49      inference(global_propositional_subsumption,
% 8.14/1.49                [status(thm)],
% 8.14/1.49                [c_12488,c_19,c_18,c_994,c_1126]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_9,plain,
% 8.14/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 8.14/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 8.14/1.49      | ~ r1_tarski(X0,X2)
% 8.14/1.49      | r1_tarski(k2_pre_topc(X1,X0),k2_pre_topc(X1,X2))
% 8.14/1.49      | ~ l1_pre_topc(X1) ),
% 8.14/1.49      inference(cnf_transformation,[],[f49]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_786,plain,
% 8.14/1.49      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 8.14/1.49      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 8.14/1.49      | r1_tarski(X0,X2) != iProver_top
% 8.14/1.49      | r1_tarski(k2_pre_topc(X1,X0),k2_pre_topc(X1,X2)) = iProver_top
% 8.14/1.49      | l1_pre_topc(X1) != iProver_top ),
% 8.14/1.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_12527,plain,
% 8.14/1.49      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.14/1.49      | m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.14/1.49      | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),X0) != iProver_top
% 8.14/1.49      | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k2_pre_topc(sK0,X0)) = iProver_top
% 8.14/1.49      | l1_pre_topc(sK0) != iProver_top ),
% 8.14/1.49      inference(superposition,[status(thm)],[c_12522,c_786]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_995,plain,
% 8.14/1.49      ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 8.14/1.49      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.14/1.49      | l1_pre_topc(sK0) != iProver_top ),
% 8.14/1.49      inference(predicate_to_equality,[status(thm)],[c_994]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_1129,plain,
% 8.14/1.49      ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 8.14/1.49      | m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
% 8.14/1.49      | ~ l1_pre_topc(sK0) ),
% 8.14/1.49      inference(instantiation,[status(thm)],[c_6]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_1130,plain,
% 8.14/1.49      ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.14/1.49      | m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 8.14/1.49      | l1_pre_topc(sK0) != iProver_top ),
% 8.14/1.49      inference(predicate_to_equality,[status(thm)],[c_1129]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_13384,plain,
% 8.14/1.49      ( r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k2_pre_topc(sK0,X0)) = iProver_top
% 8.14/1.49      | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),X0) != iProver_top
% 8.14/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 8.14/1.49      inference(global_propositional_subsumption,
% 8.14/1.49                [status(thm)],
% 8.14/1.49                [c_12527,c_20,c_21,c_995,c_1130]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_13385,plain,
% 8.14/1.49      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.14/1.49      | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),X0) != iProver_top
% 8.14/1.49      | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k2_pre_topc(sK0,X0)) = iProver_top ),
% 8.14/1.49      inference(renaming,[status(thm)],[c_13384]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_776,plain,
% 8.14/1.49      ( l1_pre_topc(sK0) = iProver_top ),
% 8.14/1.49      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_1,plain,
% 8.14/1.49      ( r1_tarski(X0,X0) ),
% 8.14/1.49      inference(cnf_transformation,[],[f60]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_793,plain,
% 8.14/1.49      ( r1_tarski(X0,X0) = iProver_top ),
% 8.14/1.49      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_4,plain,
% 8.14/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 8.14/1.49      inference(cnf_transformation,[],[f45]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_791,plain,
% 8.14/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 8.14/1.49      | r1_tarski(X0,X1) != iProver_top ),
% 8.14/1.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_2660,plain,
% 8.14/1.49      ( k2_pre_topc(X0,k2_pre_topc(X0,X1)) = k2_pre_topc(X0,X1)
% 8.14/1.49      | r1_tarski(X1,u1_struct_0(X0)) != iProver_top
% 8.14/1.49      | l1_pre_topc(X0) != iProver_top ),
% 8.14/1.49      inference(superposition,[status(thm)],[c_791,c_788]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_6068,plain,
% 8.14/1.49      ( k2_pre_topc(X0,k2_pre_topc(X0,u1_struct_0(X0))) = k2_pre_topc(X0,u1_struct_0(X0))
% 8.14/1.49      | l1_pre_topc(X0) != iProver_top ),
% 8.14/1.49      inference(superposition,[status(thm)],[c_793,c_2660]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_7337,plain,
% 8.14/1.49      ( k2_pre_topc(sK0,k2_pre_topc(sK0,u1_struct_0(sK0))) = k2_pre_topc(sK0,u1_struct_0(sK0)) ),
% 8.14/1.49      inference(superposition,[status(thm)],[c_776,c_6068]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_7570,plain,
% 8.14/1.49      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.14/1.49      | m1_subset_1(k2_pre_topc(sK0,u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.14/1.49      | r1_tarski(X0,k2_pre_topc(sK0,u1_struct_0(sK0))) != iProver_top
% 8.14/1.49      | r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,u1_struct_0(sK0))) = iProver_top
% 8.14/1.49      | l1_pre_topc(sK0) != iProver_top ),
% 8.14/1.49      inference(superposition,[status(thm)],[c_7337,c_786]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_957,plain,
% 8.14/1.49      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 8.14/1.49      | ~ r1_tarski(X0,u1_struct_0(X1)) ),
% 8.14/1.49      inference(instantiation,[status(thm)],[c_4]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_1417,plain,
% 8.14/1.49      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 8.14/1.49      | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X0)) ),
% 8.14/1.49      inference(instantiation,[status(thm)],[c_957]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_1419,plain,
% 8.14/1.49      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 8.14/1.49      | r1_tarski(u1_struct_0(X0),u1_struct_0(X0)) != iProver_top ),
% 8.14/1.49      inference(predicate_to_equality,[status(thm)],[c_1417]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_1421,plain,
% 8.14/1.49      ( m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 8.14/1.49      | r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0)) != iProver_top ),
% 8.14/1.49      inference(instantiation,[status(thm)],[c_1419]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_1418,plain,
% 8.14/1.49      ( r1_tarski(u1_struct_0(X0),u1_struct_0(X0)) ),
% 8.14/1.49      inference(instantiation,[status(thm)],[c_1]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_1423,plain,
% 8.14/1.49      ( r1_tarski(u1_struct_0(X0),u1_struct_0(X0)) = iProver_top ),
% 8.14/1.49      inference(predicate_to_equality,[status(thm)],[c_1418]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_1425,plain,
% 8.14/1.49      ( r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0)) = iProver_top ),
% 8.14/1.49      inference(instantiation,[status(thm)],[c_1423]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_3044,plain,
% 8.14/1.49      ( m1_subset_1(k2_pre_topc(X0,u1_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0)))
% 8.14/1.49      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 8.14/1.49      | ~ l1_pre_topc(X0) ),
% 8.14/1.49      inference(instantiation,[status(thm)],[c_6]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_3045,plain,
% 8.14/1.49      ( m1_subset_1(k2_pre_topc(X0,u1_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 8.14/1.49      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 8.14/1.49      | l1_pre_topc(X0) != iProver_top ),
% 8.14/1.49      inference(predicate_to_equality,[status(thm)],[c_3044]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_3047,plain,
% 8.14/1.49      ( m1_subset_1(k2_pre_topc(sK0,u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 8.14/1.49      | m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.14/1.49      | l1_pre_topc(sK0) != iProver_top ),
% 8.14/1.49      inference(instantiation,[status(thm)],[c_3045]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_8362,plain,
% 8.14/1.49      ( r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,u1_struct_0(sK0))) = iProver_top
% 8.14/1.49      | r1_tarski(X0,k2_pre_topc(sK0,u1_struct_0(sK0))) != iProver_top
% 8.14/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 8.14/1.49      inference(global_propositional_subsumption,
% 8.14/1.49                [status(thm)],
% 8.14/1.49                [c_7570,c_20,c_1421,c_1425,c_3047]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_8363,plain,
% 8.14/1.49      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.14/1.49      | r1_tarski(X0,k2_pre_topc(sK0,u1_struct_0(sK0))) != iProver_top
% 8.14/1.49      | r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,u1_struct_0(sK0))) = iProver_top ),
% 8.14/1.49      inference(renaming,[status(thm)],[c_8362]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_8373,plain,
% 8.14/1.49      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.14/1.49      | r1_tarski(X0,k2_pre_topc(sK0,u1_struct_0(sK0))) != iProver_top
% 8.14/1.49      | r1_tarski(k2_pre_topc(sK0,X0),X1) = iProver_top
% 8.14/1.49      | r1_tarski(k2_pre_topc(sK0,u1_struct_0(sK0)),X1) != iProver_top ),
% 8.14/1.49      inference(superposition,[status(thm)],[c_8363,c_792]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_29510,plain,
% 8.14/1.49      ( m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.14/1.49      | m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.14/1.49      | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),u1_struct_0(sK0)) != iProver_top
% 8.14/1.49      | r1_tarski(k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))),X0) = iProver_top
% 8.14/1.49      | r1_tarski(k2_pre_topc(sK0,u1_struct_0(sK0)),X0) != iProver_top ),
% 8.14/1.49      inference(superposition,[status(thm)],[c_13385,c_8373]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_29528,plain,
% 8.14/1.49      ( m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.14/1.49      | m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.14/1.49      | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),X0) = iProver_top
% 8.14/1.49      | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),u1_struct_0(sK0)) != iProver_top
% 8.14/1.49      | r1_tarski(k2_pre_topc(sK0,u1_struct_0(sK0)),X0) != iProver_top ),
% 8.14/1.49      inference(light_normalisation,[status(thm)],[c_29510,c_12522]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_12,plain,
% 8.14/1.49      ( ~ v4_tops_1(X0,X1)
% 8.14/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 8.14/1.49      | r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
% 8.14/1.49      | ~ l1_pre_topc(X1) ),
% 8.14/1.49      inference(cnf_transformation,[],[f50]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_783,plain,
% 8.14/1.49      ( v4_tops_1(X0,X1) != iProver_top
% 8.14/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 8.14/1.49      | r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0) = iProver_top
% 8.14/1.49      | l1_pre_topc(X1) != iProver_top ),
% 8.14/1.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_7568,plain,
% 8.14/1.49      ( v4_tops_1(k2_pre_topc(sK0,u1_struct_0(sK0)),sK0) != iProver_top
% 8.14/1.49      | m1_subset_1(k2_pre_topc(sK0,u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.14/1.49      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,u1_struct_0(sK0))),k2_pre_topc(sK0,u1_struct_0(sK0))) = iProver_top
% 8.14/1.49      | l1_pre_topc(sK0) != iProver_top ),
% 8.14/1.49      inference(superposition,[status(thm)],[c_7337,c_783]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_7844,plain,
% 8.14/1.49      ( r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,u1_struct_0(sK0))),k2_pre_topc(sK0,u1_struct_0(sK0))) = iProver_top
% 8.14/1.49      | v4_tops_1(k2_pre_topc(sK0,u1_struct_0(sK0)),sK0) != iProver_top ),
% 8.14/1.49      inference(global_propositional_subsumption,
% 8.14/1.49                [status(thm)],
% 8.14/1.49                [c_7568,c_20,c_1421,c_1425,c_3047]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_7845,plain,
% 8.14/1.49      ( v4_tops_1(k2_pre_topc(sK0,u1_struct_0(sK0)),sK0) != iProver_top
% 8.14/1.49      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,u1_struct_0(sK0))),k2_pre_topc(sK0,u1_struct_0(sK0))) = iProver_top ),
% 8.14/1.49      inference(renaming,[status(thm)],[c_7844]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_15,plain,
% 8.14/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 8.14/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 8.14/1.49      | ~ r1_tarski(X0,X2)
% 8.14/1.49      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 8.14/1.49      | ~ l1_pre_topc(X1) ),
% 8.14/1.49      inference(cnf_transformation,[],[f55]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_780,plain,
% 8.14/1.49      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 8.14/1.49      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 8.14/1.49      | r1_tarski(X0,X2) != iProver_top
% 8.14/1.49      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2)) = iProver_top
% 8.14/1.49      | l1_pre_topc(X1) != iProver_top ),
% 8.14/1.49      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_1501,plain,
% 8.14/1.49      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 8.14/1.49      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 8.14/1.49      | r1_tarski(X0,X2) != iProver_top
% 8.14/1.49      | r1_tarski(k1_tops_1(X1,X2),X3) != iProver_top
% 8.14/1.49      | r1_tarski(k1_tops_1(X1,X0),X3) = iProver_top
% 8.14/1.49      | l1_pre_topc(X1) != iProver_top ),
% 8.14/1.49      inference(superposition,[status(thm)],[c_780,c_792]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_5590,plain,
% 8.14/1.49      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.14/1.49      | r1_tarski(k1_tops_1(sK0,X0),X1) != iProver_top
% 8.14/1.49      | r1_tarski(k1_tops_1(sK0,sK1),X1) = iProver_top
% 8.14/1.49      | r1_tarski(sK1,X0) != iProver_top
% 8.14/1.49      | l1_pre_topc(sK0) != iProver_top ),
% 8.14/1.49      inference(superposition,[status(thm)],[c_777,c_1501]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_6103,plain,
% 8.14/1.49      ( r1_tarski(sK1,X0) != iProver_top
% 8.14/1.49      | r1_tarski(k1_tops_1(sK0,sK1),X1) = iProver_top
% 8.14/1.49      | r1_tarski(k1_tops_1(sK0,X0),X1) != iProver_top
% 8.14/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 8.14/1.49      inference(global_propositional_subsumption,
% 8.14/1.49                [status(thm)],
% 8.14/1.49                [c_5590,c_20]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_6104,plain,
% 8.14/1.49      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.14/1.49      | r1_tarski(k1_tops_1(sK0,X0),X1) != iProver_top
% 8.14/1.49      | r1_tarski(k1_tops_1(sK0,sK1),X1) = iProver_top
% 8.14/1.49      | r1_tarski(sK1,X0) != iProver_top ),
% 8.14/1.49      inference(renaming,[status(thm)],[c_6103]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_6114,plain,
% 8.14/1.49      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.14/1.49      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),X1) != iProver_top
% 8.14/1.49      | r1_tarski(k1_tops_1(sK0,sK1),X1) = iProver_top
% 8.14/1.49      | r1_tarski(sK1,k2_pre_topc(sK0,X0)) != iProver_top
% 8.14/1.49      | l1_pre_topc(sK0) != iProver_top ),
% 8.14/1.49      inference(superposition,[status(thm)],[c_789,c_6104]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_6646,plain,
% 8.14/1.49      ( r1_tarski(sK1,k2_pre_topc(sK0,X0)) != iProver_top
% 8.14/1.49      | r1_tarski(k1_tops_1(sK0,sK1),X1) = iProver_top
% 8.14/1.49      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),X1) != iProver_top
% 8.14/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 8.14/1.49      inference(global_propositional_subsumption,
% 8.14/1.49                [status(thm)],
% 8.14/1.49                [c_6114,c_20]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_6647,plain,
% 8.14/1.49      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.14/1.49      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),X1) != iProver_top
% 8.14/1.49      | r1_tarski(k1_tops_1(sK0,sK1),X1) = iProver_top
% 8.14/1.49      | r1_tarski(sK1,k2_pre_topc(sK0,X0)) != iProver_top ),
% 8.14/1.49      inference(renaming,[status(thm)],[c_6646]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_6656,plain,
% 8.14/1.49      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.14/1.49      | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,X0))) = iProver_top
% 8.14/1.49      | r1_tarski(sK1,k2_pre_topc(sK0,X0)) != iProver_top ),
% 8.14/1.49      inference(superposition,[status(thm)],[c_793,c_6647]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_9687,plain,
% 8.14/1.49      ( m1_subset_1(k2_pre_topc(sK0,u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.14/1.49      | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,u1_struct_0(sK0)))) = iProver_top
% 8.14/1.49      | r1_tarski(sK1,k2_pre_topc(sK0,k2_pre_topc(sK0,u1_struct_0(sK0)))) != iProver_top ),
% 8.14/1.49      inference(superposition,[status(thm)],[c_7337,c_6656]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_9713,plain,
% 8.14/1.49      ( m1_subset_1(k2_pre_topc(sK0,u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.14/1.49      | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,u1_struct_0(sK0)))) = iProver_top
% 8.14/1.49      | r1_tarski(sK1,k2_pre_topc(sK0,u1_struct_0(sK0))) != iProver_top ),
% 8.14/1.49      inference(light_normalisation,[status(thm)],[c_9687,c_7337]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_8,plain,
% 8.14/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 8.14/1.49      | r1_tarski(X0,k2_pre_topc(X1,X0))
% 8.14/1.49      | ~ l1_pre_topc(X1) ),
% 8.14/1.49      inference(cnf_transformation,[],[f48]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_787,plain,
% 8.14/1.49      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 8.14/1.49      | r1_tarski(X0,k2_pre_topc(X1,X0)) = iProver_top
% 8.14/1.49      | l1_pre_topc(X1) != iProver_top ),
% 8.14/1.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_1527,plain,
% 8.14/1.49      ( r1_tarski(X0,k2_pre_topc(X1,X0)) = iProver_top
% 8.14/1.49      | r1_tarski(X0,u1_struct_0(X1)) != iProver_top
% 8.14/1.49      | l1_pre_topc(X1) != iProver_top ),
% 8.14/1.49      inference(superposition,[status(thm)],[c_791,c_787]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_1075,plain,
% 8.14/1.49      ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
% 8.14/1.49      inference(superposition,[status(thm)],[c_777,c_790]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_1502,plain,
% 8.14/1.49      ( r1_tarski(u1_struct_0(sK0),X0) != iProver_top
% 8.14/1.49      | r1_tarski(sK1,X0) = iProver_top ),
% 8.14/1.49      inference(superposition,[status(thm)],[c_1075,c_792]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_4300,plain,
% 8.14/1.49      ( r1_tarski(u1_struct_0(sK0),u1_struct_0(X0)) != iProver_top
% 8.14/1.49      | r1_tarski(sK1,k2_pre_topc(X0,u1_struct_0(sK0))) = iProver_top
% 8.14/1.49      | l1_pre_topc(X0) != iProver_top ),
% 8.14/1.49      inference(superposition,[status(thm)],[c_1527,c_1502]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_4338,plain,
% 8.14/1.49      ( r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0)) != iProver_top
% 8.14/1.49      | r1_tarski(sK1,k2_pre_topc(sK0,u1_struct_0(sK0))) = iProver_top
% 8.14/1.49      | l1_pre_topc(sK0) != iProver_top ),
% 8.14/1.49      inference(instantiation,[status(thm)],[c_4300]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_9929,plain,
% 8.14/1.49      ( r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,u1_struct_0(sK0)))) = iProver_top ),
% 8.14/1.49      inference(global_propositional_subsumption,
% 8.14/1.49                [status(thm)],
% 8.14/1.49                [c_9713,c_20,c_1421,c_1425,c_3047,c_4338]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_9934,plain,
% 8.14/1.49      ( r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,u1_struct_0(sK0))),X0) != iProver_top
% 8.14/1.49      | r1_tarski(k1_tops_1(sK0,sK1),X0) = iProver_top ),
% 8.14/1.49      inference(superposition,[status(thm)],[c_9929,c_792]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_10190,plain,
% 8.14/1.49      ( v4_tops_1(k2_pre_topc(sK0,u1_struct_0(sK0)),sK0) != iProver_top
% 8.14/1.49      | r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,u1_struct_0(sK0))) = iProver_top ),
% 8.14/1.49      inference(superposition,[status(thm)],[c_7845,c_9934]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_2662,plain,
% 8.14/1.49      ( k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)) = k2_pre_topc(sK0,sK1)
% 8.14/1.49      | l1_pre_topc(sK0) != iProver_top ),
% 8.14/1.49      inference(superposition,[status(thm)],[c_777,c_788]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_998,plain,
% 8.14/1.49      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 8.14/1.49      | ~ l1_pre_topc(sK0)
% 8.14/1.49      | k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 8.14/1.49      inference(instantiation,[status(thm)],[c_7]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_3123,plain,
% 8.14/1.49      ( k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 8.14/1.49      inference(global_propositional_subsumption,
% 8.14/1.49                [status(thm)],
% 8.14/1.49                [c_2662,c_19,c_18,c_998]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_3126,plain,
% 8.14/1.49      ( v4_tops_1(k2_pre_topc(sK0,sK1),sK0) != iProver_top
% 8.14/1.49      | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.14/1.49      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_pre_topc(sK0,sK1)) = iProver_top
% 8.14/1.49      | l1_pre_topc(sK0) != iProver_top ),
% 8.14/1.49      inference(superposition,[status(thm)],[c_3123,c_783]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_17,negated_conjecture,
% 8.14/1.49      ( v4_tops_1(sK1,sK0) ),
% 8.14/1.49      inference(cnf_transformation,[],[f58]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_22,plain,
% 8.14/1.49      ( v4_tops_1(sK1,sK0) = iProver_top ),
% 8.14/1.49      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_990,plain,
% 8.14/1.49      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 8.14/1.49      | r1_tarski(sK1,k2_pre_topc(sK0,sK1))
% 8.14/1.49      | ~ l1_pre_topc(sK0) ),
% 8.14/1.49      inference(instantiation,[status(thm)],[c_8]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_991,plain,
% 8.14/1.49      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.14/1.49      | r1_tarski(sK1,k2_pre_topc(sK0,sK1)) = iProver_top
% 8.14/1.49      | l1_pre_topc(sK0) != iProver_top ),
% 8.14/1.49      inference(predicate_to_equality,[status(thm)],[c_990]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_1019,plain,
% 8.14/1.49      ( ~ v4_tops_1(sK1,sK0)
% 8.14/1.49      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 8.14/1.49      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK1)
% 8.14/1.49      | ~ l1_pre_topc(sK0) ),
% 8.14/1.49      inference(instantiation,[status(thm)],[c_12]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_1020,plain,
% 8.14/1.49      ( v4_tops_1(sK1,sK0) != iProver_top
% 8.14/1.49      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.14/1.49      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK1) = iProver_top
% 8.14/1.49      | l1_pre_topc(sK0) != iProver_top ),
% 8.14/1.49      inference(predicate_to_equality,[status(thm)],[c_1019]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_1401,plain,
% 8.14/1.49      ( ~ r1_tarski(X0,X1)
% 8.14/1.49      | ~ r1_tarski(X1,k2_pre_topc(sK0,sK1))
% 8.14/1.49      | r1_tarski(X0,k2_pre_topc(sK0,sK1)) ),
% 8.14/1.49      inference(instantiation,[status(thm)],[c_3]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_2520,plain,
% 8.14/1.49      ( r1_tarski(X0,k2_pre_topc(sK0,sK1))
% 8.14/1.49      | ~ r1_tarski(X0,sK1)
% 8.14/1.49      | ~ r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
% 8.14/1.49      inference(instantiation,[status(thm)],[c_1401]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_2787,plain,
% 8.14/1.49      ( r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_pre_topc(sK0,sK1))
% 8.14/1.49      | ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK1)
% 8.14/1.49      | ~ r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
% 8.14/1.49      inference(instantiation,[status(thm)],[c_2520]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_2788,plain,
% 8.14/1.49      ( r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_pre_topc(sK0,sK1)) = iProver_top
% 8.14/1.49      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK1) != iProver_top
% 8.14/1.49      | r1_tarski(sK1,k2_pre_topc(sK0,sK1)) != iProver_top ),
% 8.14/1.49      inference(predicate_to_equality,[status(thm)],[c_2787]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_3138,plain,
% 8.14/1.49      ( r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_pre_topc(sK0,sK1)) = iProver_top ),
% 8.14/1.49      inference(global_propositional_subsumption,
% 8.14/1.49                [status(thm)],
% 8.14/1.49                [c_3126,c_20,c_21,c_22,c_991,c_1020,c_2788]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_6663,plain,
% 8.14/1.49      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.14/1.49      | r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1)) = iProver_top
% 8.14/1.49      | r1_tarski(sK1,k2_pre_topc(sK0,sK1)) != iProver_top ),
% 8.14/1.49      inference(superposition,[status(thm)],[c_3138,c_6647]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_1114,plain,
% 8.14/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 8.14/1.49      | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 8.14/1.49      | ~ r1_tarski(X0,k2_pre_topc(sK0,sK1))
% 8.14/1.49      | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))
% 8.14/1.49      | ~ l1_pre_topc(sK0) ),
% 8.14/1.49      inference(instantiation,[status(thm)],[c_15]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_1409,plain,
% 8.14/1.49      ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 8.14/1.49      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 8.14/1.49      | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))
% 8.14/1.49      | ~ r1_tarski(sK1,k2_pre_topc(sK0,sK1))
% 8.14/1.49      | ~ l1_pre_topc(sK0) ),
% 8.14/1.49      inference(instantiation,[status(thm)],[c_1114]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_1410,plain,
% 8.14/1.49      ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.14/1.49      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.14/1.49      | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) = iProver_top
% 8.14/1.49      | r1_tarski(sK1,k2_pre_topc(sK0,sK1)) != iProver_top
% 8.14/1.49      | l1_pre_topc(sK0) != iProver_top ),
% 8.14/1.49      inference(predicate_to_equality,[status(thm)],[c_1409]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_1446,plain,
% 8.14/1.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,sK1) | r1_tarski(X0,sK1) ),
% 8.14/1.49      inference(instantiation,[status(thm)],[c_3]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_1765,plain,
% 8.14/1.49      ( ~ r1_tarski(X0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))
% 8.14/1.49      | r1_tarski(X0,sK1)
% 8.14/1.49      | ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK1) ),
% 8.14/1.49      inference(instantiation,[status(thm)],[c_1446]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_2780,plain,
% 8.14/1.49      ( ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK1)
% 8.14/1.49      | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))
% 8.14/1.49      | r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
% 8.14/1.49      inference(instantiation,[status(thm)],[c_1765]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_2781,plain,
% 8.14/1.49      ( r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK1) != iProver_top
% 8.14/1.49      | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) != iProver_top
% 8.14/1.49      | r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
% 8.14/1.49      inference(predicate_to_equality,[status(thm)],[c_2780]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_5499,plain,
% 8.14/1.49      ( r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1))
% 8.14/1.49      | ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
% 8.14/1.49      | ~ r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
% 8.14/1.49      inference(instantiation,[status(thm)],[c_2520]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_5512,plain,
% 8.14/1.49      ( r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1)) = iProver_top
% 8.14/1.49      | r1_tarski(k1_tops_1(sK0,sK1),sK1) != iProver_top
% 8.14/1.49      | r1_tarski(sK1,k2_pre_topc(sK0,sK1)) != iProver_top ),
% 8.14/1.49      inference(predicate_to_equality,[status(thm)],[c_5499]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_8870,plain,
% 8.14/1.49      ( r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1)) = iProver_top ),
% 8.14/1.49      inference(global_propositional_subsumption,
% 8.14/1.49                [status(thm)],
% 8.14/1.49                [c_6663,c_20,c_21,c_22,c_963,c_991,c_1020,c_1410,c_2781,
% 8.14/1.49                 c_5512]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_8875,plain,
% 8.14/1.49      ( r1_tarski(k1_tops_1(sK0,sK1),X0) = iProver_top
% 8.14/1.49      | r1_tarski(k2_pre_topc(sK0,sK1),X0) != iProver_top ),
% 8.14/1.49      inference(superposition,[status(thm)],[c_8870,c_792]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_9060,plain,
% 8.14/1.49      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.14/1.49      | r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,u1_struct_0(sK0))) = iProver_top
% 8.14/1.49      | r1_tarski(sK1,k2_pre_topc(sK0,u1_struct_0(sK0))) != iProver_top ),
% 8.14/1.49      inference(superposition,[status(thm)],[c_8363,c_8875]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_10939,plain,
% 8.14/1.49      ( r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,u1_struct_0(sK0))) = iProver_top ),
% 8.14/1.49      inference(global_propositional_subsumption,
% 8.14/1.49                [status(thm)],
% 8.14/1.49                [c_10190,c_20,c_21,c_1425,c_4338,c_9060]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_29509,plain,
% 8.14/1.49      ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.14/1.49      | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),X0) = iProver_top
% 8.14/1.49      | r1_tarski(k2_pre_topc(sK0,u1_struct_0(sK0)),X0) != iProver_top ),
% 8.14/1.49      inference(superposition,[status(thm)],[c_10939,c_8373]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_29971,plain,
% 8.14/1.49      ( r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),X0) = iProver_top
% 8.14/1.49      | r1_tarski(k2_pre_topc(sK0,u1_struct_0(sK0)),X0) != iProver_top ),
% 8.14/1.49      inference(global_propositional_subsumption,
% 8.14/1.49                [status(thm)],
% 8.14/1.49                [c_29528,c_20,c_21,c_995,c_29509]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_0,plain,
% 8.14/1.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 8.14/1.49      inference(cnf_transformation,[],[f42]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_794,plain,
% 8.14/1.49      ( X0 = X1
% 8.14/1.49      | r1_tarski(X0,X1) != iProver_top
% 8.14/1.49      | r1_tarski(X1,X0) != iProver_top ),
% 8.14/1.49      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_29981,plain,
% 8.14/1.49      ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = X0
% 8.14/1.49      | r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != iProver_top
% 8.14/1.49      | r1_tarski(k2_pre_topc(sK0,u1_struct_0(sK0)),X0) != iProver_top ),
% 8.14/1.49      inference(superposition,[status(thm)],[c_29971,c_794]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_34062,plain,
% 8.14/1.49      ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
% 8.14/1.49      | r1_tarski(k2_pre_topc(sK0,u1_struct_0(sK0)),k2_pre_topc(sK0,sK1)) != iProver_top
% 8.14/1.49      | r1_tarski(u1_struct_0(sK0),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != iProver_top ),
% 8.14/1.49      inference(superposition,[status(thm)],[c_34048,c_29981]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_11,plain,
% 8.14/1.49      ( ~ v4_tops_1(X0,X1)
% 8.14/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 8.14/1.49      | r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
% 8.14/1.49      | ~ l1_pre_topc(X1) ),
% 8.14/1.49      inference(cnf_transformation,[],[f51]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_1016,plain,
% 8.14/1.49      ( ~ v4_tops_1(sK1,sK0)
% 8.14/1.49      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 8.14/1.49      | r1_tarski(sK1,k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))
% 8.14/1.49      | ~ l1_pre_topc(sK0) ),
% 8.14/1.49      inference(instantiation,[status(thm)],[c_11]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_1017,plain,
% 8.14/1.49      ( v4_tops_1(sK1,sK0) != iProver_top
% 8.14/1.49      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.14/1.49      | r1_tarski(sK1,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = iProver_top
% 8.14/1.49      | l1_pre_topc(sK0) != iProver_top ),
% 8.14/1.49      inference(predicate_to_equality,[status(thm)],[c_1016]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_1101,plain,
% 8.14/1.49      ( m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
% 8.14/1.49      | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 8.14/1.49      | ~ l1_pre_topc(sK0) ),
% 8.14/1.49      inference(instantiation,[status(thm)],[c_13]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_1108,plain,
% 8.14/1.49      ( m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 8.14/1.49      | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.14/1.49      | l1_pre_topc(sK0) != iProver_top ),
% 8.14/1.49      inference(predicate_to_equality,[status(thm)],[c_1101]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_1046,plain,
% 8.14/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 8.14/1.49      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 8.14/1.49      | ~ r1_tarski(X0,sK1)
% 8.14/1.49      | r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,sK1))
% 8.14/1.49      | ~ l1_pre_topc(sK0) ),
% 8.14/1.49      inference(instantiation,[status(thm)],[c_9]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_1454,plain,
% 8.14/1.49      ( ~ m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
% 8.14/1.49      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 8.14/1.49      | ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK1)
% 8.14/1.49      | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))),k2_pre_topc(sK0,sK1))
% 8.14/1.49      | ~ l1_pre_topc(sK0) ),
% 8.14/1.49      inference(instantiation,[status(thm)],[c_1046]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_1455,plain,
% 8.14/1.49      ( m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.14/1.49      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.14/1.49      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK1) != iProver_top
% 8.14/1.49      | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))),k2_pre_topc(sK0,sK1)) = iProver_top
% 8.14/1.49      | l1_pre_topc(sK0) != iProver_top ),
% 8.14/1.49      inference(predicate_to_equality,[status(thm)],[c_1454]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_1229,plain,
% 8.14/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 8.14/1.49      | ~ m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
% 8.14/1.49      | ~ r1_tarski(X0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))
% 8.14/1.49      | r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))))
% 8.14/1.49      | ~ l1_pre_topc(sK0) ),
% 8.14/1.49      inference(instantiation,[status(thm)],[c_9]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_2279,plain,
% 8.14/1.49      ( ~ m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
% 8.14/1.49      | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 8.14/1.49      | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))
% 8.14/1.49      | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))))
% 8.14/1.49      | ~ l1_pre_topc(sK0) ),
% 8.14/1.49      inference(instantiation,[status(thm)],[c_1229]) ).
% 8.14/1.49  
% 8.14/1.49  cnf(c_2280,plain,
% 8.14/1.49      ( m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.14/1.49      | m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.14/1.50      | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) != iProver_top
% 8.14/1.50      | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))) = iProver_top
% 8.14/1.50      | l1_pre_topc(sK0) != iProver_top ),
% 8.14/1.50      inference(predicate_to_equality,[status(thm)],[c_2279]) ).
% 8.14/1.50  
% 8.14/1.50  cnf(c_2524,plain,
% 8.14/1.50      ( ~ r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))))
% 8.14/1.50      | r1_tarski(X0,k2_pre_topc(sK0,sK1))
% 8.14/1.50      | ~ r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))),k2_pre_topc(sK0,sK1)) ),
% 8.14/1.50      inference(instantiation,[status(thm)],[c_1401]) ).
% 8.14/1.50  
% 8.14/1.50  cnf(c_3119,plain,
% 8.14/1.50      ( ~ r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))),k2_pre_topc(sK0,sK1))
% 8.14/1.50      | ~ r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))))
% 8.14/1.50      | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k2_pre_topc(sK0,sK1)) ),
% 8.14/1.50      inference(instantiation,[status(thm)],[c_2524]) ).
% 8.14/1.50  
% 8.14/1.50  cnf(c_3120,plain,
% 8.14/1.50      ( r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))),k2_pre_topc(sK0,sK1)) != iProver_top
% 8.14/1.50      | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))) != iProver_top
% 8.14/1.50      | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k2_pre_topc(sK0,sK1)) = iProver_top ),
% 8.14/1.50      inference(predicate_to_equality,[status(thm)],[c_3119]) ).
% 8.14/1.50  
% 8.14/1.50  cnf(c_7238,plain,
% 8.14/1.50      ( ~ r1_tarski(X0,k2_pre_topc(X1,X2))
% 8.14/1.50      | ~ r1_tarski(k2_pre_topc(X1,X2),X0)
% 8.14/1.50      | k2_pre_topc(X1,X2) = X0 ),
% 8.14/1.50      inference(instantiation,[status(thm)],[c_0]) ).
% 8.14/1.50  
% 8.14/1.50  cnf(c_14809,plain,
% 8.14/1.50      ( ~ r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k2_pre_topc(sK0,sK1))
% 8.14/1.50      | ~ r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))
% 8.14/1.50      | k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 8.14/1.50      inference(instantiation,[status(thm)],[c_7238]) ).
% 8.14/1.50  
% 8.14/1.50  cnf(c_14810,plain,
% 8.14/1.50      ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
% 8.14/1.50      | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k2_pre_topc(sK0,sK1)) != iProver_top
% 8.14/1.50      | r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != iProver_top ),
% 8.14/1.50      inference(predicate_to_equality,[status(thm)],[c_14809]) ).
% 8.14/1.50  
% 8.14/1.50  cnf(c_14,plain,
% 8.14/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 8.14/1.50      | ~ l1_pre_topc(X1)
% 8.14/1.50      | k1_tops_1(X1,k1_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
% 8.14/1.50      inference(cnf_transformation,[],[f54]) ).
% 8.14/1.50  
% 8.14/1.50  cnf(c_781,plain,
% 8.14/1.50      ( k1_tops_1(X0,k1_tops_1(X0,X1)) = k1_tops_1(X0,X1)
% 8.14/1.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 8.14/1.50      | l1_pre_topc(X0) != iProver_top ),
% 8.14/1.50      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 8.14/1.50  
% 8.14/1.50  cnf(c_2692,plain,
% 8.14/1.50      ( k1_tops_1(X0,k1_tops_1(X0,k2_pre_topc(X0,X1))) = k1_tops_1(X0,k2_pre_topc(X0,X1))
% 8.14/1.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 8.14/1.50      | l1_pre_topc(X0) != iProver_top ),
% 8.14/1.50      inference(superposition,[status(thm)],[c_789,c_781]) ).
% 8.14/1.50  
% 8.14/1.50  cnf(c_15583,plain,
% 8.14/1.50      ( k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) = k1_tops_1(sK0,k2_pre_topc(sK0,sK1))
% 8.14/1.50      | l1_pre_topc(sK0) != iProver_top ),
% 8.14/1.50      inference(superposition,[status(thm)],[c_777,c_2692]) ).
% 8.14/1.50  
% 8.14/1.50  cnf(c_1099,plain,
% 8.14/1.50      ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 8.14/1.50      | ~ l1_pre_topc(sK0)
% 8.14/1.50      | k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) = k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) ),
% 8.14/1.50      inference(instantiation,[status(thm)],[c_14]) ).
% 8.14/1.50  
% 8.14/1.50  cnf(c_15889,plain,
% 8.14/1.50      ( k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) = k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) ),
% 8.14/1.50      inference(global_propositional_subsumption,
% 8.14/1.50                [status(thm)],
% 8.14/1.50                [c_15583,c_19,c_18,c_962,c_1099]) ).
% 8.14/1.50  
% 8.14/1.50  cnf(c_15897,plain,
% 8.14/1.50      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.14/1.50      | m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.14/1.50      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),X0) != iProver_top
% 8.14/1.50      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,X0)) = iProver_top
% 8.14/1.50      | l1_pre_topc(sK0) != iProver_top ),
% 8.14/1.50      inference(superposition,[status(thm)],[c_15889,c_780]) ).
% 8.14/1.50  
% 8.14/1.50  cnf(c_16104,plain,
% 8.14/1.50      ( r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,X0)) = iProver_top
% 8.14/1.50      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),X0) != iProver_top
% 8.14/1.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 8.14/1.50      inference(global_propositional_subsumption,
% 8.14/1.50                [status(thm)],
% 8.14/1.50                [c_15897,c_20,c_21,c_963,c_1108]) ).
% 8.14/1.50  
% 8.14/1.50  cnf(c_16105,plain,
% 8.14/1.50      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.14/1.50      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),X0) != iProver_top
% 8.14/1.50      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,X0)) = iProver_top ),
% 8.14/1.50      inference(renaming,[status(thm)],[c_16104]) ).
% 8.14/1.50  
% 8.14/1.50  cnf(c_9686,plain,
% 8.14/1.50      ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.14/1.50      | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) = iProver_top
% 8.14/1.50      | r1_tarski(sK1,k2_pre_topc(sK0,k2_pre_topc(sK0,sK1))) != iProver_top ),
% 8.14/1.50      inference(superposition,[status(thm)],[c_3123,c_6656]) ).
% 8.14/1.50  
% 8.14/1.50  cnf(c_9720,plain,
% 8.14/1.50      ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.14/1.50      | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) = iProver_top
% 8.14/1.50      | r1_tarski(sK1,k2_pre_topc(sK0,sK1)) != iProver_top ),
% 8.14/1.50      inference(light_normalisation,[status(thm)],[c_9686,c_3123]) ).
% 8.14/1.50  
% 8.14/1.50  cnf(c_9900,plain,
% 8.14/1.50      ( r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) = iProver_top ),
% 8.14/1.50      inference(global_propositional_subsumption,
% 8.14/1.50                [status(thm)],
% 8.14/1.50                [c_9720,c_20,c_21,c_963,c_991,c_1410]) ).
% 8.14/1.50  
% 8.14/1.50  cnf(c_9906,plain,
% 8.14/1.50      ( k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,sK1)
% 8.14/1.50      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,sK1)) != iProver_top ),
% 8.14/1.50      inference(superposition,[status(thm)],[c_9900,c_794]) ).
% 8.14/1.50  
% 8.14/1.50  cnf(c_16123,plain,
% 8.14/1.50      ( k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,sK1)
% 8.14/1.50      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.14/1.50      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK1) != iProver_top ),
% 8.14/1.50      inference(superposition,[status(thm)],[c_16105,c_9906]) ).
% 8.14/1.50  
% 8.14/1.50  cnf(c_16645,plain,
% 8.14/1.50      ( k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
% 8.14/1.50      inference(global_propositional_subsumption,
% 8.14/1.50                [status(thm)],
% 8.14/1.50                [c_16123,c_20,c_21,c_22,c_1020]) ).
% 8.14/1.50  
% 8.14/1.50  cnf(c_784,plain,
% 8.14/1.50      ( v4_tops_1(X0,X1) != iProver_top
% 8.14/1.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 8.14/1.50      | r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0))) = iProver_top
% 8.14/1.50      | l1_pre_topc(X1) != iProver_top ),
% 8.14/1.50      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 8.14/1.50  
% 8.14/1.50  cnf(c_16692,plain,
% 8.14/1.50      ( v4_tops_1(k2_pre_topc(sK0,sK1),sK0) != iProver_top
% 8.14/1.50      | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.14/1.50      | r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = iProver_top
% 8.14/1.50      | l1_pre_topc(sK0) != iProver_top ),
% 8.14/1.50      inference(superposition,[status(thm)],[c_16645,c_784]) ).
% 8.14/1.50  
% 8.14/1.50  cnf(c_12531,plain,
% 8.14/1.50      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.14/1.50      | m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.14/1.50      | r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != iProver_top
% 8.14/1.50      | r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = iProver_top
% 8.14/1.50      | l1_pre_topc(sK0) != iProver_top ),
% 8.14/1.50      inference(superposition,[status(thm)],[c_12522,c_786]) ).
% 8.14/1.50  
% 8.14/1.50  cnf(c_13517,plain,
% 8.14/1.50      ( r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = iProver_top
% 8.14/1.50      | r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != iProver_top
% 8.14/1.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 8.14/1.50      inference(global_propositional_subsumption,
% 8.14/1.50                [status(thm)],
% 8.14/1.50                [c_12531,c_20,c_21,c_995,c_1130]) ).
% 8.14/1.50  
% 8.14/1.50  cnf(c_13518,plain,
% 8.14/1.50      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.14/1.50      | r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != iProver_top
% 8.14/1.50      | r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = iProver_top ),
% 8.14/1.50      inference(renaming,[status(thm)],[c_13517]) ).
% 8.14/1.50  
% 8.14/1.50  cnf(c_10,plain,
% 8.14/1.50      ( v4_tops_1(X0,X1)
% 8.14/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 8.14/1.50      | ~ r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
% 8.14/1.50      | ~ r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
% 8.14/1.50      | ~ l1_pre_topc(X1) ),
% 8.14/1.50      inference(cnf_transformation,[],[f52]) ).
% 8.14/1.50  
% 8.14/1.50  cnf(c_785,plain,
% 8.14/1.50      ( v4_tops_1(X0,X1) = iProver_top
% 8.14/1.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 8.14/1.50      | r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0))) != iProver_top
% 8.14/1.50      | r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0) != iProver_top
% 8.14/1.50      | l1_pre_topc(X1) != iProver_top ),
% 8.14/1.50      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 8.14/1.50  
% 8.14/1.50  cnf(c_3968,plain,
% 8.14/1.50      ( v4_tops_1(k2_pre_topc(sK0,sK1),sK0) = iProver_top
% 8.14/1.50      | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.14/1.50      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_pre_topc(sK0,sK1)) != iProver_top
% 8.14/1.50      | r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))) != iProver_top
% 8.14/1.50      | l1_pre_topc(sK0) != iProver_top ),
% 8.14/1.50      inference(superposition,[status(thm)],[c_3123,c_785]) ).
% 8.14/1.50  
% 8.14/1.50  cnf(c_4711,plain,
% 8.14/1.50      ( r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))) != iProver_top
% 8.14/1.50      | v4_tops_1(k2_pre_topc(sK0,sK1),sK0) = iProver_top ),
% 8.14/1.50      inference(global_propositional_subsumption,
% 8.14/1.50                [status(thm)],
% 8.14/1.50                [c_3968,c_20,c_21,c_22,c_963,c_991,c_1020,c_2788]) ).
% 8.14/1.50  
% 8.14/1.50  cnf(c_4712,plain,
% 8.14/1.50      ( v4_tops_1(k2_pre_topc(sK0,sK1),sK0) = iProver_top
% 8.14/1.50      | r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))) != iProver_top ),
% 8.14/1.50      inference(renaming,[status(thm)],[c_4711]) ).
% 8.14/1.50  
% 8.14/1.50  cnf(c_16658,plain,
% 8.14/1.50      ( v4_tops_1(k2_pre_topc(sK0,sK1),sK0) = iProver_top
% 8.14/1.50      | r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != iProver_top ),
% 8.14/1.50      inference(demodulation,[status(thm)],[c_16645,c_4712]) ).
% 8.14/1.50  
% 8.14/1.50  cnf(c_16821,plain,
% 8.14/1.50      ( v4_tops_1(k2_pre_topc(sK0,sK1),sK0) = iProver_top
% 8.14/1.50      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.14/1.50      | r1_tarski(sK1,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != iProver_top ),
% 8.14/1.50      inference(superposition,[status(thm)],[c_13518,c_16658]) ).
% 8.14/1.50  
% 8.14/1.50  cnf(c_37013,plain,
% 8.14/1.50      ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 8.14/1.50      inference(global_propositional_subsumption,
% 8.14/1.50                [status(thm)],
% 8.14/1.50                [c_34062,c_20,c_21,c_22,c_963,c_991,c_995,c_1017,c_1020,
% 8.14/1.50                 c_1108,c_1410,c_1455,c_2280,c_3120,c_14810,c_16692,
% 8.14/1.50                 c_16821]) ).
% 8.14/1.50  
% 8.14/1.50  cnf(c_37111,plain,
% 8.14/1.50      ( v4_tops_1(k1_tops_1(sK0,sK1),sK0) = iProver_top
% 8.14/1.50      | m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.14/1.50      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,sK1)) != iProver_top
% 8.14/1.50      | r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,k1_tops_1(sK0,sK1)))) != iProver_top
% 8.14/1.50      | l1_pre_topc(sK0) != iProver_top ),
% 8.14/1.50      inference(superposition,[status(thm)],[c_37013,c_785]) ).
% 8.14/1.50  
% 8.14/1.50  cnf(c_1700,plain,
% 8.14/1.50      ( k1_tops_1(sK0,k1_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1)
% 8.14/1.50      | l1_pre_topc(sK0) != iProver_top ),
% 8.14/1.50      inference(superposition,[status(thm)],[c_777,c_781]) ).
% 8.14/1.50  
% 8.14/1.50  cnf(c_1002,plain,
% 8.14/1.50      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 8.14/1.50      | ~ l1_pre_topc(sK0)
% 8.14/1.50      | k1_tops_1(sK0,k1_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
% 8.14/1.50      inference(instantiation,[status(thm)],[c_14]) ).
% 8.14/1.50  
% 8.14/1.50  cnf(c_1856,plain,
% 8.14/1.50      ( k1_tops_1(sK0,k1_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
% 8.14/1.50      inference(global_propositional_subsumption,
% 8.14/1.50                [status(thm)],
% 8.14/1.50                [c_1700,c_19,c_18,c_1002]) ).
% 8.14/1.50  
% 8.14/1.50  cnf(c_37203,plain,
% 8.14/1.50      ( v4_tops_1(k1_tops_1(sK0,sK1),sK0) = iProver_top
% 8.14/1.50      | m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.14/1.50      | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) != iProver_top
% 8.14/1.50      | r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1)) != iProver_top
% 8.14/1.50      | l1_pre_topc(sK0) != iProver_top ),
% 8.14/1.50      inference(light_normalisation,
% 8.14/1.50                [status(thm)],
% 8.14/1.50                [c_37111,c_1856,c_16645,c_37013]) ).
% 8.14/1.50  
% 8.14/1.50  cnf(c_1471,plain,
% 8.14/1.50      ( r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) ),
% 8.14/1.50      inference(instantiation,[status(thm)],[c_1]) ).
% 8.14/1.50  
% 8.14/1.50  cnf(c_1474,plain,
% 8.14/1.50      ( r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) = iProver_top ),
% 8.14/1.50      inference(predicate_to_equality,[status(thm)],[c_1471]) ).
% 8.14/1.50  
% 8.14/1.50  cnf(c_16,negated_conjecture,
% 8.14/1.50      ( ~ v4_tops_1(k1_tops_1(sK0,sK1),sK0)
% 8.14/1.50      | ~ v4_tops_1(k2_pre_topc(sK0,sK1),sK0) ),
% 8.14/1.50      inference(cnf_transformation,[],[f59]) ).
% 8.14/1.50  
% 8.14/1.50  cnf(c_23,plain,
% 8.14/1.50      ( v4_tops_1(k1_tops_1(sK0,sK1),sK0) != iProver_top
% 8.14/1.50      | v4_tops_1(k2_pre_topc(sK0,sK1),sK0) != iProver_top ),
% 8.14/1.50      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 8.14/1.50  
% 8.14/1.50  cnf(contradiction,plain,
% 8.14/1.50      ( $false ),
% 8.14/1.50      inference(minisat,
% 8.14/1.50                [status(thm)],
% 8.14/1.50                [c_37203,c_16821,c_5512,c_2781,c_1474,c_1410,c_1020,
% 8.14/1.50                 c_1017,c_995,c_991,c_963,c_23,c_22,c_21,c_20]) ).
% 8.14/1.50  
% 8.14/1.50  
% 8.14/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 8.14/1.50  
% 8.14/1.50  ------                               Statistics
% 8.14/1.50  
% 8.14/1.50  ------ Selected
% 8.14/1.50  
% 8.14/1.50  total_time:                             1.014
% 8.14/1.50  
%------------------------------------------------------------------------------
