%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:15:58 EST 2020

% Result     : Theorem 3.93s
% Output     : CNFRefutation 3.93s
% Verified   : 
% Statistics : Number of formulae       :  153 (1381 expanded)
%              Number of clauses        :  101 ( 439 expanded)
%              Number of leaves         :   13 ( 322 expanded)
%              Depth                    :   23
%              Number of atoms          :  494 (5878 expanded)
%              Number of equality atoms :  158 ( 490 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal clause size      :   10 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_tops_1(X1,X0)
           => ( v4_tops_1(k2_pre_topc(X0,X1),X0)
              & v4_tops_1(k1_tops_1(X0,X1),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_tops_1(X1,X0)
             => ( v4_tops_1(k2_pre_topc(X0,X1),X0)
                & v4_tops_1(k1_tops_1(X0,X1),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v4_tops_1(k2_pre_topc(X0,X1),X0)
            | ~ v4_tops_1(k1_tops_1(X0,X1),X0) )
          & v4_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v4_tops_1(k2_pre_topc(X0,X1),X0)
            | ~ v4_tops_1(k1_tops_1(X0,X1),X0) )
          & v4_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f35,plain,(
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

fof(f34,plain,
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

fof(f36,plain,
    ( ( ~ v4_tops_1(k2_pre_topc(sK0,sK1),sK0)
      | ~ v4_tops_1(k1_tops_1(sK0,sK1),sK0) )
    & v4_tops_1(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f29,f35,f34])).

fof(f52,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f36])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f51,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_tops_1(X1,X0)
          <=> ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_tops_1(X1,X0)
          <=> ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
      | ~ v4_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f3,axiom,(
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
    inference(ennf_transformation,[],[f3])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

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

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f30])).

fof(f39,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f53,plain,(
    v4_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v4_tops_1(X1,X0)
      | ~ r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
      | ~ r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f54,plain,
    ( ~ v4_tops_1(k2_pre_topc(sK0,sK1),sK0)
    | ~ v4_tops_1(k1_tops_1(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f4,axiom,(
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
    inference(ennf_transformation,[],[f4])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)
      | ~ v4_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_813,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_17,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_340,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_17])).

cnf(c_341,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_340])).

cnf(c_802,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_341])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,k1_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_226,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,k1_tops_1(X1,X0)) = k1_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_17])).

cnf(c_227,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,k1_tops_1(sK0,X0)) = k1_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_226])).

cnf(c_810,plain,
    ( k1_tops_1(sK0,k1_tops_1(sK0,X0)) = k1_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_227])).

cnf(c_1699,plain,
    ( k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,X0))) = k1_tops_1(sK0,k2_pre_topc(sK0,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_802,c_810])).

cnf(c_4100,plain,
    ( k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) = k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_813,c_1699])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_196,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_17])).

cnf(c_197,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X1,X0)
    | r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_196])).

cnf(c_812,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_197])).

cnf(c_4290,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),X0) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4100,c_812])).

cnf(c_19,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_932,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_341])).

cnf(c_933,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_932])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_238,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_17])).

cnf(c_239,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_238])).

cnf(c_1050,plain,
    ( m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_239])).

cnf(c_1051,plain,
    ( m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1050])).

cnf(c_11994,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),X0) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4290,c_19,c_933,c_1051])).

cnf(c_8,plain,
    ( ~ v4_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_265,plain,
    ( ~ v4_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_17])).

cnf(c_266,plain,
    ( ~ v4_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,X0))) ),
    inference(unflattening,[status(thm)],[c_265])).

cnf(c_807,plain,
    ( v4_tops_1(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_266])).

cnf(c_809,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_239])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k2_pre_topc(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_328,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,k2_pre_topc(X1,X0)) = k2_pre_topc(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_17])).

cnf(c_329,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k2_pre_topc(sK0,X0)) = k2_pre_topc(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_328])).

cnf(c_803,plain,
    ( k2_pre_topc(sK0,k2_pre_topc(sK0,X0)) = k2_pre_topc(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_329])).

cnf(c_1497,plain,
    ( k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,X0))) = k2_pre_topc(sK0,k1_tops_1(sK0,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_809,c_803])).

cnf(c_3125,plain,
    ( k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_813,c_1497])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k2_pre_topc(X1,X0),k2_pre_topc(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_298,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k2_pre_topc(X1,X0),k2_pre_topc(X1,X2))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_17])).

cnf(c_299,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X1,X0)
    | r1_tarski(k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_298])).

cnf(c_805,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_299])).

cnf(c_3153,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3125,c_805])).

cnf(c_929,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_239])).

cnf(c_930,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_929])).

cnf(c_1013,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_341])).

cnf(c_1017,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1013])).

cnf(c_9594,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3153,c_19,c_930,c_1017])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_817,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1970,plain,
    ( k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_805,c_817])).

cnf(c_9609,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k2_pre_topc(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9594,c_1970])).

cnf(c_12511,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k2_pre_topc(sK0,X0)
    | r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9609,c_19,c_930])).

cnf(c_12512,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k2_pre_topc(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_12511])).

cnf(c_12523,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
    | v4_tops_1(sK1,sK0) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_807,c_12512])).

cnf(c_15,negated_conjecture,
    ( v4_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_20,plain,
    ( v4_tops_1(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_214,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_17])).

cnf(c_215,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,X0),X0) ),
    inference(unflattening,[status(thm)],[c_214])).

cnf(c_935,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(instantiation,[status(thm)],[c_215])).

cnf(c_936,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_935])).

cnf(c_12595,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12523,c_19,c_20,c_936])).

cnf(c_7,plain,
    ( v4_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
    | ~ r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_280,plain,
    ( v4_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
    | ~ r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_17])).

cnf(c_281,plain,
    ( v4_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,X0)))
    | ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),X0) ),
    inference(unflattening,[status(thm)],[c_280])).

cnf(c_806,plain,
    ( v4_tops_1(X0,sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,X0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_281])).

cnf(c_12643,plain,
    ( v4_tops_1(k1_tops_1(sK0,sK1),sK0) = iProver_top
    | m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,sK1)) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,k1_tops_1(sK0,sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_12595,c_806])).

cnf(c_1697,plain,
    ( k1_tops_1(sK0,k1_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_813,c_810])).

cnf(c_12722,plain,
    ( v4_tops_1(k1_tops_1(sK0,sK1),sK0) = iProver_top
    | m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,sK1)) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_12643,c_1697,c_12595])).

cnf(c_14,negated_conjecture,
    ( ~ v4_tops_1(k1_tops_1(sK0,sK1),sK0)
    | ~ v4_tops_1(k2_pre_topc(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_21,plain,
    ( v4_tops_1(k1_tops_1(sK0,sK1),sK0) != iProver_top
    | v4_tops_1(k2_pre_topc(sK0,sK1),sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3152,plain,
    ( v4_tops_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),sK0) = iProver_top
    | m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3125,c_806])).

cnf(c_954,plain,
    ( ~ v4_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK1,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
    inference(instantiation,[status(thm)],[c_266])).

cnf(c_955,plain,
    ( v4_tops_1(sK1,sK0) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK1,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_954])).

cnf(c_1173,plain,
    ( m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_239])).

cnf(c_1174,plain,
    ( m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1173])).

cnf(c_1171,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
    inference(instantiation,[status(thm)],[c_215])).

cnf(c_1178,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1171])).

cnf(c_1167,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))
    | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))) ),
    inference(instantiation,[status(thm)],[c_197])).

cnf(c_5381,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))))
    | ~ r1_tarski(sK1,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
    inference(instantiation,[status(thm)],[c_1167])).

cnf(c_5382,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))) = iProver_top
    | r1_tarski(sK1,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5381])).

cnf(c_4423,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,k1_tops_1(sK0,k2_pre_topc(sK0,X0)))
    | r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,X0)))) ),
    inference(instantiation,[status(thm)],[c_299])).

cnf(c_9176,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))))
    | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))))) ),
    inference(instantiation,[status(thm)],[c_4423])).

cnf(c_9179,plain,
    ( m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9176])).

cnf(c_11204,plain,
    ( v4_tops_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3152,c_19,c_20,c_930,c_955,c_1017,c_1174,c_1178,c_5382,c_9179])).

cnf(c_12601,plain,
    ( v4_tops_1(k2_pre_topc(sK0,sK1),sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_12595,c_11204])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_316,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,X0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_17])).

cnf(c_317,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(X0,k2_pre_topc(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_316])).

cnf(c_804,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_317])).

cnf(c_1499,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),k2_pre_topc(sK0,k1_tops_1(sK0,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_809,c_804])).

cnf(c_12649,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_12595,c_1499])).

cnf(c_13231,plain,
    ( r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12722,c_19,c_21,c_930,c_12601,c_12649])).

cnf(c_13238,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_11994,c_13231])).

cnf(c_9,plain,
    ( ~ v4_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_250,plain,
    ( ~ v4_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_17])).

cnf(c_251,plain,
    ( ~ v4_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),X0) ),
    inference(unflattening,[status(thm)],[c_250])).

cnf(c_947,plain,
    ( ~ v4_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK1) ),
    inference(instantiation,[status(thm)],[c_251])).

cnf(c_948,plain,
    ( v4_tops_1(sK1,sK0) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_947])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13238,c_948,c_20,c_19])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 21:01:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.93/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.93/0.99  
% 3.93/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.93/0.99  
% 3.93/0.99  ------  iProver source info
% 3.93/0.99  
% 3.93/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.93/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.93/0.99  git: non_committed_changes: false
% 3.93/0.99  git: last_make_outside_of_git: false
% 3.93/0.99  
% 3.93/0.99  ------ 
% 3.93/0.99  
% 3.93/0.99  ------ Input Options
% 3.93/0.99  
% 3.93/0.99  --out_options                           all
% 3.93/0.99  --tptp_safe_out                         true
% 3.93/0.99  --problem_path                          ""
% 3.93/0.99  --include_path                          ""
% 3.93/0.99  --clausifier                            res/vclausify_rel
% 3.93/0.99  --clausifier_options                    --mode clausify
% 3.93/0.99  --stdin                                 false
% 3.93/0.99  --stats_out                             all
% 3.93/0.99  
% 3.93/0.99  ------ General Options
% 3.93/0.99  
% 3.93/0.99  --fof                                   false
% 3.93/0.99  --time_out_real                         305.
% 3.93/0.99  --time_out_virtual                      -1.
% 3.93/0.99  --symbol_type_check                     false
% 3.93/0.99  --clausify_out                          false
% 3.93/0.99  --sig_cnt_out                           false
% 3.93/0.99  --trig_cnt_out                          false
% 3.93/0.99  --trig_cnt_out_tolerance                1.
% 3.93/0.99  --trig_cnt_out_sk_spl                   false
% 3.93/0.99  --abstr_cl_out                          false
% 3.93/0.99  
% 3.93/0.99  ------ Global Options
% 3.93/0.99  
% 3.93/0.99  --schedule                              default
% 3.93/0.99  --add_important_lit                     false
% 3.93/0.99  --prop_solver_per_cl                    1000
% 3.93/0.99  --min_unsat_core                        false
% 3.93/0.99  --soft_assumptions                      false
% 3.93/0.99  --soft_lemma_size                       3
% 3.93/0.99  --prop_impl_unit_size                   0
% 3.93/0.99  --prop_impl_unit                        []
% 3.93/0.99  --share_sel_clauses                     true
% 3.93/0.99  --reset_solvers                         false
% 3.93/0.99  --bc_imp_inh                            [conj_cone]
% 3.93/0.99  --conj_cone_tolerance                   3.
% 3.93/0.99  --extra_neg_conj                        none
% 3.93/0.99  --large_theory_mode                     true
% 3.93/0.99  --prolific_symb_bound                   200
% 3.93/0.99  --lt_threshold                          2000
% 3.93/0.99  --clause_weak_htbl                      true
% 3.93/0.99  --gc_record_bc_elim                     false
% 3.93/0.99  
% 3.93/0.99  ------ Preprocessing Options
% 3.93/0.99  
% 3.93/0.99  --preprocessing_flag                    true
% 3.93/0.99  --time_out_prep_mult                    0.1
% 3.93/0.99  --splitting_mode                        input
% 3.93/0.99  --splitting_grd                         true
% 3.93/0.99  --splitting_cvd                         false
% 3.93/0.99  --splitting_cvd_svl                     false
% 3.93/0.99  --splitting_nvd                         32
% 3.93/0.99  --sub_typing                            true
% 3.93/0.99  --prep_gs_sim                           true
% 3.93/0.99  --prep_unflatten                        true
% 3.93/0.99  --prep_res_sim                          true
% 3.93/0.99  --prep_upred                            true
% 3.93/0.99  --prep_sem_filter                       exhaustive
% 3.93/0.99  --prep_sem_filter_out                   false
% 3.93/0.99  --pred_elim                             true
% 3.93/0.99  --res_sim_input                         true
% 3.93/0.99  --eq_ax_congr_red                       true
% 3.93/0.99  --pure_diseq_elim                       true
% 3.93/0.99  --brand_transform                       false
% 3.93/0.99  --non_eq_to_eq                          false
% 3.93/0.99  --prep_def_merge                        true
% 3.93/0.99  --prep_def_merge_prop_impl              false
% 3.93/0.99  --prep_def_merge_mbd                    true
% 3.93/0.99  --prep_def_merge_tr_red                 false
% 3.93/0.99  --prep_def_merge_tr_cl                  false
% 3.93/0.99  --smt_preprocessing                     true
% 3.93/0.99  --smt_ac_axioms                         fast
% 3.93/0.99  --preprocessed_out                      false
% 3.93/0.99  --preprocessed_stats                    false
% 3.93/0.99  
% 3.93/0.99  ------ Abstraction refinement Options
% 3.93/0.99  
% 3.93/0.99  --abstr_ref                             []
% 3.93/0.99  --abstr_ref_prep                        false
% 3.93/0.99  --abstr_ref_until_sat                   false
% 3.93/0.99  --abstr_ref_sig_restrict                funpre
% 3.93/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.93/0.99  --abstr_ref_under                       []
% 3.93/0.99  
% 3.93/0.99  ------ SAT Options
% 3.93/0.99  
% 3.93/0.99  --sat_mode                              false
% 3.93/0.99  --sat_fm_restart_options                ""
% 3.93/0.99  --sat_gr_def                            false
% 3.93/0.99  --sat_epr_types                         true
% 3.93/0.99  --sat_non_cyclic_types                  false
% 3.93/0.99  --sat_finite_models                     false
% 3.93/0.99  --sat_fm_lemmas                         false
% 3.93/0.99  --sat_fm_prep                           false
% 3.93/0.99  --sat_fm_uc_incr                        true
% 3.93/0.99  --sat_out_model                         small
% 3.93/0.99  --sat_out_clauses                       false
% 3.93/0.99  
% 3.93/0.99  ------ QBF Options
% 3.93/0.99  
% 3.93/0.99  --qbf_mode                              false
% 3.93/0.99  --qbf_elim_univ                         false
% 3.93/0.99  --qbf_dom_inst                          none
% 3.93/0.99  --qbf_dom_pre_inst                      false
% 3.93/0.99  --qbf_sk_in                             false
% 3.93/0.99  --qbf_pred_elim                         true
% 3.93/0.99  --qbf_split                             512
% 3.93/0.99  
% 3.93/0.99  ------ BMC1 Options
% 3.93/0.99  
% 3.93/0.99  --bmc1_incremental                      false
% 3.93/0.99  --bmc1_axioms                           reachable_all
% 3.93/0.99  --bmc1_min_bound                        0
% 3.93/0.99  --bmc1_max_bound                        -1
% 3.93/0.99  --bmc1_max_bound_default                -1
% 3.93/0.99  --bmc1_symbol_reachability              true
% 3.93/0.99  --bmc1_property_lemmas                  false
% 3.93/0.99  --bmc1_k_induction                      false
% 3.93/0.99  --bmc1_non_equiv_states                 false
% 3.93/0.99  --bmc1_deadlock                         false
% 3.93/0.99  --bmc1_ucm                              false
% 3.93/0.99  --bmc1_add_unsat_core                   none
% 3.93/0.99  --bmc1_unsat_core_children              false
% 3.93/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.93/0.99  --bmc1_out_stat                         full
% 3.93/0.99  --bmc1_ground_init                      false
% 3.93/0.99  --bmc1_pre_inst_next_state              false
% 3.93/0.99  --bmc1_pre_inst_state                   false
% 3.93/0.99  --bmc1_pre_inst_reach_state             false
% 3.93/0.99  --bmc1_out_unsat_core                   false
% 3.93/0.99  --bmc1_aig_witness_out                  false
% 3.93/0.99  --bmc1_verbose                          false
% 3.93/0.99  --bmc1_dump_clauses_tptp                false
% 3.93/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.93/0.99  --bmc1_dump_file                        -
% 3.93/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.93/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.93/0.99  --bmc1_ucm_extend_mode                  1
% 3.93/0.99  --bmc1_ucm_init_mode                    2
% 3.93/0.99  --bmc1_ucm_cone_mode                    none
% 3.93/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.93/0.99  --bmc1_ucm_relax_model                  4
% 3.93/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.93/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.93/0.99  --bmc1_ucm_layered_model                none
% 3.93/0.99  --bmc1_ucm_max_lemma_size               10
% 3.93/0.99  
% 3.93/0.99  ------ AIG Options
% 3.93/0.99  
% 3.93/0.99  --aig_mode                              false
% 3.93/0.99  
% 3.93/0.99  ------ Instantiation Options
% 3.93/0.99  
% 3.93/0.99  --instantiation_flag                    true
% 3.93/0.99  --inst_sos_flag                         false
% 3.93/0.99  --inst_sos_phase                        true
% 3.93/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.93/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.93/0.99  --inst_lit_sel_side                     num_symb
% 3.93/0.99  --inst_solver_per_active                1400
% 3.93/0.99  --inst_solver_calls_frac                1.
% 3.93/0.99  --inst_passive_queue_type               priority_queues
% 3.93/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.93/0.99  --inst_passive_queues_freq              [25;2]
% 3.93/0.99  --inst_dismatching                      true
% 3.93/0.99  --inst_eager_unprocessed_to_passive     true
% 3.93/0.99  --inst_prop_sim_given                   true
% 3.93/0.99  --inst_prop_sim_new                     false
% 3.93/0.99  --inst_subs_new                         false
% 3.93/0.99  --inst_eq_res_simp                      false
% 3.93/0.99  --inst_subs_given                       false
% 3.93/0.99  --inst_orphan_elimination               true
% 3.93/0.99  --inst_learning_loop_flag               true
% 3.93/0.99  --inst_learning_start                   3000
% 3.93/0.99  --inst_learning_factor                  2
% 3.93/0.99  --inst_start_prop_sim_after_learn       3
% 3.93/0.99  --inst_sel_renew                        solver
% 3.93/0.99  --inst_lit_activity_flag                true
% 3.93/0.99  --inst_restr_to_given                   false
% 3.93/0.99  --inst_activity_threshold               500
% 3.93/0.99  --inst_out_proof                        true
% 3.93/0.99  
% 3.93/0.99  ------ Resolution Options
% 3.93/0.99  
% 3.93/0.99  --resolution_flag                       true
% 3.93/0.99  --res_lit_sel                           adaptive
% 3.93/0.99  --res_lit_sel_side                      none
% 3.93/0.99  --res_ordering                          kbo
% 3.93/0.99  --res_to_prop_solver                    active
% 3.93/0.99  --res_prop_simpl_new                    false
% 3.93/0.99  --res_prop_simpl_given                  true
% 3.93/0.99  --res_passive_queue_type                priority_queues
% 3.93/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.93/0.99  --res_passive_queues_freq               [15;5]
% 3.93/0.99  --res_forward_subs                      full
% 3.93/0.99  --res_backward_subs                     full
% 3.93/0.99  --res_forward_subs_resolution           true
% 3.93/0.99  --res_backward_subs_resolution          true
% 3.93/0.99  --res_orphan_elimination                true
% 3.93/0.99  --res_time_limit                        2.
% 3.93/0.99  --res_out_proof                         true
% 3.93/0.99  
% 3.93/0.99  ------ Superposition Options
% 3.93/0.99  
% 3.93/0.99  --superposition_flag                    true
% 3.93/0.99  --sup_passive_queue_type                priority_queues
% 3.93/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.93/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.93/0.99  --demod_completeness_check              fast
% 3.93/0.99  --demod_use_ground                      true
% 3.93/0.99  --sup_to_prop_solver                    passive
% 3.93/0.99  --sup_prop_simpl_new                    true
% 3.93/0.99  --sup_prop_simpl_given                  true
% 3.93/0.99  --sup_fun_splitting                     false
% 3.93/0.99  --sup_smt_interval                      50000
% 3.93/0.99  
% 3.93/0.99  ------ Superposition Simplification Setup
% 3.93/0.99  
% 3.93/0.99  --sup_indices_passive                   []
% 3.93/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.93/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.93/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.93/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.93/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.93/0.99  --sup_full_bw                           [BwDemod]
% 3.93/0.99  --sup_immed_triv                        [TrivRules]
% 3.93/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.93/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.93/0.99  --sup_immed_bw_main                     []
% 3.93/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.93/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.93/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.93/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.93/0.99  
% 3.93/0.99  ------ Combination Options
% 3.93/0.99  
% 3.93/0.99  --comb_res_mult                         3
% 3.93/0.99  --comb_sup_mult                         2
% 3.93/0.99  --comb_inst_mult                        10
% 3.93/0.99  
% 3.93/0.99  ------ Debug Options
% 3.93/0.99  
% 3.93/0.99  --dbg_backtrace                         false
% 3.93/0.99  --dbg_dump_prop_clauses                 false
% 3.93/0.99  --dbg_dump_prop_clauses_file            -
% 3.93/0.99  --dbg_out_stat                          false
% 3.93/0.99  ------ Parsing...
% 3.93/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.93/0.99  
% 3.93/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.93/0.99  
% 3.93/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.93/0.99  
% 3.93/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.93/0.99  ------ Proving...
% 3.93/0.99  ------ Problem Properties 
% 3.93/0.99  
% 3.93/0.99  
% 3.93/0.99  clauses                                 16
% 3.93/0.99  conjectures                             3
% 3.93/0.99  EPR                                     3
% 3.93/0.99  Horn                                    16
% 3.93/0.99  unary                                   3
% 3.93/0.99  binary                                  7
% 3.93/0.99  lits                                    38
% 3.93/0.99  lits eq                                 3
% 3.93/0.99  fd_pure                                 0
% 3.93/0.99  fd_pseudo                               0
% 3.93/0.99  fd_cond                                 0
% 3.93/0.99  fd_pseudo_cond                          1
% 3.93/0.99  AC symbols                              0
% 3.93/0.99  
% 3.93/0.99  ------ Schedule dynamic 5 is on 
% 3.93/0.99  
% 3.93/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.93/0.99  
% 3.93/0.99  
% 3.93/0.99  ------ 
% 3.93/0.99  Current options:
% 3.93/0.99  ------ 
% 3.93/0.99  
% 3.93/0.99  ------ Input Options
% 3.93/0.99  
% 3.93/0.99  --out_options                           all
% 3.93/0.99  --tptp_safe_out                         true
% 3.93/0.99  --problem_path                          ""
% 3.93/0.99  --include_path                          ""
% 3.93/0.99  --clausifier                            res/vclausify_rel
% 3.93/0.99  --clausifier_options                    --mode clausify
% 3.93/0.99  --stdin                                 false
% 3.93/0.99  --stats_out                             all
% 3.93/0.99  
% 3.93/0.99  ------ General Options
% 3.93/0.99  
% 3.93/0.99  --fof                                   false
% 3.93/0.99  --time_out_real                         305.
% 3.93/0.99  --time_out_virtual                      -1.
% 3.93/0.99  --symbol_type_check                     false
% 3.93/0.99  --clausify_out                          false
% 3.93/0.99  --sig_cnt_out                           false
% 3.93/0.99  --trig_cnt_out                          false
% 3.93/0.99  --trig_cnt_out_tolerance                1.
% 3.93/0.99  --trig_cnt_out_sk_spl                   false
% 3.93/0.99  --abstr_cl_out                          false
% 3.93/0.99  
% 3.93/0.99  ------ Global Options
% 3.93/0.99  
% 3.93/0.99  --schedule                              default
% 3.93/0.99  --add_important_lit                     false
% 3.93/0.99  --prop_solver_per_cl                    1000
% 3.93/0.99  --min_unsat_core                        false
% 3.93/0.99  --soft_assumptions                      false
% 3.93/0.99  --soft_lemma_size                       3
% 3.93/0.99  --prop_impl_unit_size                   0
% 3.93/0.99  --prop_impl_unit                        []
% 3.93/0.99  --share_sel_clauses                     true
% 3.93/0.99  --reset_solvers                         false
% 3.93/0.99  --bc_imp_inh                            [conj_cone]
% 3.93/0.99  --conj_cone_tolerance                   3.
% 3.93/0.99  --extra_neg_conj                        none
% 3.93/0.99  --large_theory_mode                     true
% 3.93/0.99  --prolific_symb_bound                   200
% 3.93/0.99  --lt_threshold                          2000
% 3.93/0.99  --clause_weak_htbl                      true
% 3.93/0.99  --gc_record_bc_elim                     false
% 3.93/0.99  
% 3.93/0.99  ------ Preprocessing Options
% 3.93/0.99  
% 3.93/0.99  --preprocessing_flag                    true
% 3.93/0.99  --time_out_prep_mult                    0.1
% 3.93/0.99  --splitting_mode                        input
% 3.93/0.99  --splitting_grd                         true
% 3.93/0.99  --splitting_cvd                         false
% 3.93/0.99  --splitting_cvd_svl                     false
% 3.93/0.99  --splitting_nvd                         32
% 3.93/0.99  --sub_typing                            true
% 3.93/0.99  --prep_gs_sim                           true
% 3.93/0.99  --prep_unflatten                        true
% 3.93/0.99  --prep_res_sim                          true
% 3.93/0.99  --prep_upred                            true
% 3.93/0.99  --prep_sem_filter                       exhaustive
% 3.93/0.99  --prep_sem_filter_out                   false
% 3.93/0.99  --pred_elim                             true
% 3.93/0.99  --res_sim_input                         true
% 3.93/0.99  --eq_ax_congr_red                       true
% 3.93/0.99  --pure_diseq_elim                       true
% 3.93/0.99  --brand_transform                       false
% 3.93/0.99  --non_eq_to_eq                          false
% 3.93/0.99  --prep_def_merge                        true
% 3.93/0.99  --prep_def_merge_prop_impl              false
% 3.93/0.99  --prep_def_merge_mbd                    true
% 3.93/0.99  --prep_def_merge_tr_red                 false
% 3.93/0.99  --prep_def_merge_tr_cl                  false
% 3.93/0.99  --smt_preprocessing                     true
% 3.93/0.99  --smt_ac_axioms                         fast
% 3.93/0.99  --preprocessed_out                      false
% 3.93/0.99  --preprocessed_stats                    false
% 3.93/0.99  
% 3.93/0.99  ------ Abstraction refinement Options
% 3.93/0.99  
% 3.93/0.99  --abstr_ref                             []
% 3.93/0.99  --abstr_ref_prep                        false
% 3.93/0.99  --abstr_ref_until_sat                   false
% 3.93/0.99  --abstr_ref_sig_restrict                funpre
% 3.93/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.93/0.99  --abstr_ref_under                       []
% 3.93/0.99  
% 3.93/0.99  ------ SAT Options
% 3.93/0.99  
% 3.93/0.99  --sat_mode                              false
% 3.93/0.99  --sat_fm_restart_options                ""
% 3.93/0.99  --sat_gr_def                            false
% 3.93/0.99  --sat_epr_types                         true
% 3.93/0.99  --sat_non_cyclic_types                  false
% 3.93/0.99  --sat_finite_models                     false
% 3.93/0.99  --sat_fm_lemmas                         false
% 3.93/0.99  --sat_fm_prep                           false
% 3.93/0.99  --sat_fm_uc_incr                        true
% 3.93/0.99  --sat_out_model                         small
% 3.93/0.99  --sat_out_clauses                       false
% 3.93/0.99  
% 3.93/0.99  ------ QBF Options
% 3.93/0.99  
% 3.93/0.99  --qbf_mode                              false
% 3.93/0.99  --qbf_elim_univ                         false
% 3.93/0.99  --qbf_dom_inst                          none
% 3.93/0.99  --qbf_dom_pre_inst                      false
% 3.93/0.99  --qbf_sk_in                             false
% 3.93/0.99  --qbf_pred_elim                         true
% 3.93/0.99  --qbf_split                             512
% 3.93/0.99  
% 3.93/0.99  ------ BMC1 Options
% 3.93/0.99  
% 3.93/0.99  --bmc1_incremental                      false
% 3.93/0.99  --bmc1_axioms                           reachable_all
% 3.93/0.99  --bmc1_min_bound                        0
% 3.93/0.99  --bmc1_max_bound                        -1
% 3.93/0.99  --bmc1_max_bound_default                -1
% 3.93/0.99  --bmc1_symbol_reachability              true
% 3.93/0.99  --bmc1_property_lemmas                  false
% 3.93/0.99  --bmc1_k_induction                      false
% 3.93/0.99  --bmc1_non_equiv_states                 false
% 3.93/0.99  --bmc1_deadlock                         false
% 3.93/0.99  --bmc1_ucm                              false
% 3.93/0.99  --bmc1_add_unsat_core                   none
% 3.93/0.99  --bmc1_unsat_core_children              false
% 3.93/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.93/0.99  --bmc1_out_stat                         full
% 3.93/0.99  --bmc1_ground_init                      false
% 3.93/0.99  --bmc1_pre_inst_next_state              false
% 3.93/0.99  --bmc1_pre_inst_state                   false
% 3.93/0.99  --bmc1_pre_inst_reach_state             false
% 3.93/0.99  --bmc1_out_unsat_core                   false
% 3.93/0.99  --bmc1_aig_witness_out                  false
% 3.93/0.99  --bmc1_verbose                          false
% 3.93/0.99  --bmc1_dump_clauses_tptp                false
% 3.93/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.93/0.99  --bmc1_dump_file                        -
% 3.93/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.93/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.93/0.99  --bmc1_ucm_extend_mode                  1
% 3.93/0.99  --bmc1_ucm_init_mode                    2
% 3.93/0.99  --bmc1_ucm_cone_mode                    none
% 3.93/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.93/0.99  --bmc1_ucm_relax_model                  4
% 3.93/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.93/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.93/0.99  --bmc1_ucm_layered_model                none
% 3.93/0.99  --bmc1_ucm_max_lemma_size               10
% 3.93/0.99  
% 3.93/0.99  ------ AIG Options
% 3.93/0.99  
% 3.93/0.99  --aig_mode                              false
% 3.93/0.99  
% 3.93/0.99  ------ Instantiation Options
% 3.93/0.99  
% 3.93/0.99  --instantiation_flag                    true
% 3.93/0.99  --inst_sos_flag                         false
% 3.93/0.99  --inst_sos_phase                        true
% 3.93/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.93/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.93/0.99  --inst_lit_sel_side                     none
% 3.93/0.99  --inst_solver_per_active                1400
% 3.93/0.99  --inst_solver_calls_frac                1.
% 3.93/0.99  --inst_passive_queue_type               priority_queues
% 3.93/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.93/0.99  --inst_passive_queues_freq              [25;2]
% 3.93/0.99  --inst_dismatching                      true
% 3.93/0.99  --inst_eager_unprocessed_to_passive     true
% 3.93/0.99  --inst_prop_sim_given                   true
% 3.93/0.99  --inst_prop_sim_new                     false
% 3.93/0.99  --inst_subs_new                         false
% 3.93/0.99  --inst_eq_res_simp                      false
% 3.93/0.99  --inst_subs_given                       false
% 3.93/0.99  --inst_orphan_elimination               true
% 3.93/0.99  --inst_learning_loop_flag               true
% 3.93/0.99  --inst_learning_start                   3000
% 3.93/0.99  --inst_learning_factor                  2
% 3.93/0.99  --inst_start_prop_sim_after_learn       3
% 3.93/0.99  --inst_sel_renew                        solver
% 3.93/0.99  --inst_lit_activity_flag                true
% 3.93/0.99  --inst_restr_to_given                   false
% 3.93/0.99  --inst_activity_threshold               500
% 3.93/0.99  --inst_out_proof                        true
% 3.93/0.99  
% 3.93/0.99  ------ Resolution Options
% 3.93/0.99  
% 3.93/0.99  --resolution_flag                       false
% 3.93/0.99  --res_lit_sel                           adaptive
% 3.93/0.99  --res_lit_sel_side                      none
% 3.93/0.99  --res_ordering                          kbo
% 3.93/0.99  --res_to_prop_solver                    active
% 3.93/0.99  --res_prop_simpl_new                    false
% 3.93/0.99  --res_prop_simpl_given                  true
% 3.93/0.99  --res_passive_queue_type                priority_queues
% 3.93/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.93/0.99  --res_passive_queues_freq               [15;5]
% 3.93/0.99  --res_forward_subs                      full
% 3.93/0.99  --res_backward_subs                     full
% 3.93/0.99  --res_forward_subs_resolution           true
% 3.93/0.99  --res_backward_subs_resolution          true
% 3.93/0.99  --res_orphan_elimination                true
% 3.93/0.99  --res_time_limit                        2.
% 3.93/0.99  --res_out_proof                         true
% 3.93/0.99  
% 3.93/0.99  ------ Superposition Options
% 3.93/0.99  
% 3.93/0.99  --superposition_flag                    true
% 3.93/0.99  --sup_passive_queue_type                priority_queues
% 3.93/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.93/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.93/0.99  --demod_completeness_check              fast
% 3.93/0.99  --demod_use_ground                      true
% 3.93/0.99  --sup_to_prop_solver                    passive
% 3.93/0.99  --sup_prop_simpl_new                    true
% 3.93/0.99  --sup_prop_simpl_given                  true
% 3.93/0.99  --sup_fun_splitting                     false
% 3.93/0.99  --sup_smt_interval                      50000
% 3.93/0.99  
% 3.93/0.99  ------ Superposition Simplification Setup
% 3.93/0.99  
% 3.93/0.99  --sup_indices_passive                   []
% 3.93/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.93/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.93/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.93/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.93/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.93/0.99  --sup_full_bw                           [BwDemod]
% 3.93/0.99  --sup_immed_triv                        [TrivRules]
% 3.93/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.93/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.93/0.99  --sup_immed_bw_main                     []
% 3.93/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.93/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.93/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.93/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.93/0.99  
% 3.93/0.99  ------ Combination Options
% 3.93/0.99  
% 3.93/0.99  --comb_res_mult                         3
% 3.93/0.99  --comb_sup_mult                         2
% 3.93/0.99  --comb_inst_mult                        10
% 3.93/0.99  
% 3.93/0.99  ------ Debug Options
% 3.93/0.99  
% 3.93/0.99  --dbg_backtrace                         false
% 3.93/0.99  --dbg_dump_prop_clauses                 false
% 3.93/0.99  --dbg_dump_prop_clauses_file            -
% 3.93/0.99  --dbg_out_stat                          false
% 3.93/0.99  
% 3.93/0.99  
% 3.93/0.99  
% 3.93/0.99  
% 3.93/0.99  ------ Proving...
% 3.93/0.99  
% 3.93/0.99  
% 3.93/0.99  % SZS status Theorem for theBenchmark.p
% 3.93/0.99  
% 3.93/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.93/0.99  
% 3.93/0.99  fof(f11,conjecture,(
% 3.93/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_tops_1(X1,X0) => (v4_tops_1(k2_pre_topc(X0,X1),X0) & v4_tops_1(k1_tops_1(X0,X1),X0)))))),
% 3.93/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.93/0.99  
% 3.93/0.99  fof(f12,negated_conjecture,(
% 3.93/0.99    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_tops_1(X1,X0) => (v4_tops_1(k2_pre_topc(X0,X1),X0) & v4_tops_1(k1_tops_1(X0,X1),X0)))))),
% 3.93/0.99    inference(negated_conjecture,[],[f11])).
% 3.93/0.99  
% 3.93/0.99  fof(f28,plain,(
% 3.93/0.99    ? [X0] : (? [X1] : (((~v4_tops_1(k2_pre_topc(X0,X1),X0) | ~v4_tops_1(k1_tops_1(X0,X1),X0)) & v4_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.93/0.99    inference(ennf_transformation,[],[f12])).
% 3.93/0.99  
% 3.93/0.99  fof(f29,plain,(
% 3.93/0.99    ? [X0] : (? [X1] : ((~v4_tops_1(k2_pre_topc(X0,X1),X0) | ~v4_tops_1(k1_tops_1(X0,X1),X0)) & v4_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.93/0.99    inference(flattening,[],[f28])).
% 3.93/0.99  
% 3.93/0.99  fof(f35,plain,(
% 3.93/0.99    ( ! [X0] : (? [X1] : ((~v4_tops_1(k2_pre_topc(X0,X1),X0) | ~v4_tops_1(k1_tops_1(X0,X1),X0)) & v4_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((~v4_tops_1(k2_pre_topc(X0,sK1),X0) | ~v4_tops_1(k1_tops_1(X0,sK1),X0)) & v4_tops_1(sK1,X0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.93/0.99    introduced(choice_axiom,[])).
% 3.93/0.99  
% 3.93/0.99  fof(f34,plain,(
% 3.93/0.99    ? [X0] : (? [X1] : ((~v4_tops_1(k2_pre_topc(X0,X1),X0) | ~v4_tops_1(k1_tops_1(X0,X1),X0)) & v4_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((~v4_tops_1(k2_pre_topc(sK0,X1),sK0) | ~v4_tops_1(k1_tops_1(sK0,X1),sK0)) & v4_tops_1(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 3.93/0.99    introduced(choice_axiom,[])).
% 3.93/0.99  
% 3.93/0.99  fof(f36,plain,(
% 3.93/0.99    ((~v4_tops_1(k2_pre_topc(sK0,sK1),sK0) | ~v4_tops_1(k1_tops_1(sK0,sK1),sK0)) & v4_tops_1(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 3.93/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f29,f35,f34])).
% 3.93/0.99  
% 3.93/0.99  fof(f52,plain,(
% 3.93/0.99    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.93/0.99    inference(cnf_transformation,[],[f36])).
% 3.93/0.99  
% 3.93/0.99  fof(f2,axiom,(
% 3.93/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.93/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.93/0.99  
% 3.93/0.99  fof(f13,plain,(
% 3.93/0.99    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.93/0.99    inference(ennf_transformation,[],[f2])).
% 3.93/0.99  
% 3.93/0.99  fof(f14,plain,(
% 3.93/0.99    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.93/0.99    inference(flattening,[],[f13])).
% 3.93/0.99  
% 3.93/0.99  fof(f40,plain,(
% 3.93/0.99    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.93/0.99    inference(cnf_transformation,[],[f14])).
% 3.93/0.99  
% 3.93/0.99  fof(f51,plain,(
% 3.93/0.99    l1_pre_topc(sK0)),
% 3.93/0.99    inference(cnf_transformation,[],[f36])).
% 3.93/0.99  
% 3.93/0.99  fof(f8,axiom,(
% 3.93/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)))),
% 3.93/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.93/0.99  
% 3.93/0.99  fof(f23,plain,(
% 3.93/0.99    ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.93/0.99    inference(ennf_transformation,[],[f8])).
% 3.93/0.99  
% 3.93/0.99  fof(f24,plain,(
% 3.93/0.99    ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.93/0.99    inference(flattening,[],[f23])).
% 3.93/0.99  
% 3.93/0.99  fof(f48,plain,(
% 3.93/0.99    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.93/0.99    inference(cnf_transformation,[],[f24])).
% 3.93/0.99  
% 3.93/0.99  fof(f10,axiom,(
% 3.93/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 3.93/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.93/0.99  
% 3.93/0.99  fof(f26,plain,(
% 3.93/0.99    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.93/0.99    inference(ennf_transformation,[],[f10])).
% 3.93/0.99  
% 3.93/0.99  fof(f27,plain,(
% 3.93/0.99    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.93/0.99    inference(flattening,[],[f26])).
% 3.93/0.99  
% 3.93/0.99  fof(f50,plain,(
% 3.93/0.99    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.93/0.99    inference(cnf_transformation,[],[f27])).
% 3.93/0.99  
% 3.93/0.99  fof(f7,axiom,(
% 3.93/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.93/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.93/0.99  
% 3.93/0.99  fof(f21,plain,(
% 3.93/0.99    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.93/0.99    inference(ennf_transformation,[],[f7])).
% 3.93/0.99  
% 3.93/0.99  fof(f22,plain,(
% 3.93/0.99    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.93/0.99    inference(flattening,[],[f21])).
% 3.93/0.99  
% 3.93/0.99  fof(f47,plain,(
% 3.93/0.99    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.93/0.99    inference(cnf_transformation,[],[f22])).
% 3.93/0.99  
% 3.93/0.99  fof(f6,axiom,(
% 3.93/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_tops_1(X1,X0) <=> (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)))))),
% 3.93/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.93/0.99  
% 3.93/0.99  fof(f20,plain,(
% 3.93/0.99    ! [X0] : (! [X1] : ((v4_tops_1(X1,X0) <=> (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.93/0.99    inference(ennf_transformation,[],[f6])).
% 3.93/0.99  
% 3.93/0.99  fof(f32,plain,(
% 3.93/0.99    ! [X0] : (! [X1] : (((v4_tops_1(X1,X0) | (~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1))) & ((r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) | ~v4_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.93/0.99    inference(nnf_transformation,[],[f20])).
% 3.93/0.99  
% 3.93/0.99  fof(f33,plain,(
% 3.93/0.99    ! [X0] : (! [X1] : (((v4_tops_1(X1,X0) | ~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) & ((r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) | ~v4_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.93/0.99    inference(flattening,[],[f32])).
% 3.93/0.99  
% 3.93/0.99  fof(f45,plain,(
% 3.93/0.99    ( ! [X0,X1] : (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~v4_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.93/0.99    inference(cnf_transformation,[],[f33])).
% 3.93/0.99  
% 3.93/0.99  fof(f3,axiom,(
% 3.93/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)))),
% 3.93/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.93/0.99  
% 3.93/0.99  fof(f15,plain,(
% 3.93/0.99    ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.93/0.99    inference(ennf_transformation,[],[f3])).
% 3.93/0.99  
% 3.93/0.99  fof(f16,plain,(
% 3.93/0.99    ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.93/0.99    inference(flattening,[],[f15])).
% 3.93/0.99  
% 3.93/0.99  fof(f41,plain,(
% 3.93/0.99    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.93/0.99    inference(cnf_transformation,[],[f16])).
% 3.93/0.99  
% 3.93/0.99  fof(f5,axiom,(
% 3.93/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))))))),
% 3.93/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.93/0.99  
% 3.93/0.99  fof(f18,plain,(
% 3.93/0.99    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.93/0.99    inference(ennf_transformation,[],[f5])).
% 3.93/0.99  
% 3.93/0.99  fof(f19,plain,(
% 3.93/0.99    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.93/0.99    inference(flattening,[],[f18])).
% 3.93/0.99  
% 3.93/0.99  fof(f43,plain,(
% 3.93/0.99    ( ! [X2,X0,X1] : (r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.93/0.99    inference(cnf_transformation,[],[f19])).
% 3.93/0.99  
% 3.93/0.99  fof(f1,axiom,(
% 3.93/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.93/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.93/0.99  
% 3.93/0.99  fof(f30,plain,(
% 3.93/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.93/0.99    inference(nnf_transformation,[],[f1])).
% 3.93/0.99  
% 3.93/0.99  fof(f31,plain,(
% 3.93/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.93/0.99    inference(flattening,[],[f30])).
% 3.93/0.99  
% 3.93/0.99  fof(f39,plain,(
% 3.93/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.93/0.99    inference(cnf_transformation,[],[f31])).
% 3.93/0.99  
% 3.93/0.99  fof(f53,plain,(
% 3.93/0.99    v4_tops_1(sK1,sK0)),
% 3.93/0.99    inference(cnf_transformation,[],[f36])).
% 3.93/0.99  
% 3.93/0.99  fof(f9,axiom,(
% 3.93/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 3.93/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.93/0.99  
% 3.93/0.99  fof(f25,plain,(
% 3.93/0.99    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.93/0.99    inference(ennf_transformation,[],[f9])).
% 3.93/0.99  
% 3.93/0.99  fof(f49,plain,(
% 3.93/0.99    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.93/0.99    inference(cnf_transformation,[],[f25])).
% 3.93/0.99  
% 3.93/0.99  fof(f46,plain,(
% 3.93/0.99    ( ! [X0,X1] : (v4_tops_1(X1,X0) | ~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.93/0.99    inference(cnf_transformation,[],[f33])).
% 3.93/0.99  
% 3.93/0.99  fof(f54,plain,(
% 3.93/0.99    ~v4_tops_1(k2_pre_topc(sK0,sK1),sK0) | ~v4_tops_1(k1_tops_1(sK0,sK1),sK0)),
% 3.93/0.99    inference(cnf_transformation,[],[f36])).
% 3.93/0.99  
% 3.93/0.99  fof(f4,axiom,(
% 3.93/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 3.93/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.93/0.99  
% 3.93/0.99  fof(f17,plain,(
% 3.93/0.99    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.93/0.99    inference(ennf_transformation,[],[f4])).
% 3.93/0.99  
% 3.93/0.99  fof(f42,plain,(
% 3.93/0.99    ( ! [X0,X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.93/0.99    inference(cnf_transformation,[],[f17])).
% 3.93/0.99  
% 3.93/0.99  fof(f44,plain,(
% 3.93/0.99    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) | ~v4_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.93/0.99    inference(cnf_transformation,[],[f33])).
% 3.93/0.99  
% 3.93/0.99  cnf(c_16,negated_conjecture,
% 3.93/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.93/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_813,plain,
% 3.93/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.93/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_3,plain,
% 3.93/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.93/0.99      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.93/0.99      | ~ l1_pre_topc(X1) ),
% 3.93/0.99      inference(cnf_transformation,[],[f40]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_17,negated_conjecture,
% 3.93/0.99      ( l1_pre_topc(sK0) ),
% 3.93/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_340,plain,
% 3.93/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.93/0.99      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.93/0.99      | sK0 != X1 ),
% 3.93/0.99      inference(resolution_lifted,[status(thm)],[c_3,c_17]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_341,plain,
% 3.93/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.93/0.99      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.93/0.99      inference(unflattening,[status(thm)],[c_340]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_802,plain,
% 3.93/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.93/0.99      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.93/0.99      inference(predicate_to_equality,[status(thm)],[c_341]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_11,plain,
% 3.93/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.93/0.99      | ~ l1_pre_topc(X1)
% 3.93/0.99      | k1_tops_1(X1,k1_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
% 3.93/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_226,plain,
% 3.93/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.93/0.99      | k1_tops_1(X1,k1_tops_1(X1,X0)) = k1_tops_1(X1,X0)
% 3.93/0.99      | sK0 != X1 ),
% 3.93/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_17]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_227,plain,
% 3.93/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.93/0.99      | k1_tops_1(sK0,k1_tops_1(sK0,X0)) = k1_tops_1(sK0,X0) ),
% 3.93/0.99      inference(unflattening,[status(thm)],[c_226]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_810,plain,
% 3.93/0.99      ( k1_tops_1(sK0,k1_tops_1(sK0,X0)) = k1_tops_1(sK0,X0)
% 3.93/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.93/0.99      inference(predicate_to_equality,[status(thm)],[c_227]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_1699,plain,
% 3.93/0.99      ( k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,X0))) = k1_tops_1(sK0,k2_pre_topc(sK0,X0))
% 3.93/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.93/0.99      inference(superposition,[status(thm)],[c_802,c_810]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_4100,plain,
% 3.93/0.99      ( k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) = k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) ),
% 3.93/0.99      inference(superposition,[status(thm)],[c_813,c_1699]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_13,plain,
% 3.93/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.93/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.93/0.99      | ~ r1_tarski(X0,X2)
% 3.93/0.99      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 3.93/0.99      | ~ l1_pre_topc(X1) ),
% 3.93/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_196,plain,
% 3.93/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.93/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.93/0.99      | ~ r1_tarski(X0,X2)
% 3.93/0.99      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 3.93/0.99      | sK0 != X1 ),
% 3.93/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_17]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_197,plain,
% 3.93/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.93/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.93/0.99      | ~ r1_tarski(X1,X0)
% 3.93/0.99      | r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,X0)) ),
% 3.93/0.99      inference(unflattening,[status(thm)],[c_196]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_812,plain,
% 3.93/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.93/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.93/0.99      | r1_tarski(X1,X0) != iProver_top
% 3.93/0.99      | r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,X0)) = iProver_top ),
% 3.93/0.99      inference(predicate_to_equality,[status(thm)],[c_197]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_4290,plain,
% 3.93/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.93/0.99      | m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.93/0.99      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),X0) != iProver_top
% 3.93/0.99      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,X0)) = iProver_top ),
% 3.93/0.99      inference(superposition,[status(thm)],[c_4100,c_812]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_19,plain,
% 3.93/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.93/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_932,plain,
% 3.93/0.99      ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.93/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.93/0.99      inference(instantiation,[status(thm)],[c_341]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_933,plain,
% 3.93/0.99      ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 3.93/0.99      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.93/0.99      inference(predicate_to_equality,[status(thm)],[c_932]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_10,plain,
% 3.93/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.93/0.99      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.93/0.99      | ~ l1_pre_topc(X1) ),
% 3.93/0.99      inference(cnf_transformation,[],[f47]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_238,plain,
% 3.93/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.93/0.99      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.93/0.99      | sK0 != X1 ),
% 3.93/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_17]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_239,plain,
% 3.93/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.93/0.99      | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.93/0.99      inference(unflattening,[status(thm)],[c_238]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_1050,plain,
% 3.93/0.99      ( m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.93/0.99      | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.93/0.99      inference(instantiation,[status(thm)],[c_239]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_1051,plain,
% 3.93/0.99      ( m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 3.93/0.99      | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.93/0.99      inference(predicate_to_equality,[status(thm)],[c_1050]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_11994,plain,
% 3.93/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.93/0.99      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),X0) != iProver_top
% 3.93/0.99      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,X0)) = iProver_top ),
% 3.93/0.99      inference(global_propositional_subsumption,
% 3.93/0.99                [status(thm)],
% 3.93/0.99                [c_4290,c_19,c_933,c_1051]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_8,plain,
% 3.93/0.99      ( ~ v4_tops_1(X0,X1)
% 3.93/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.93/0.99      | r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
% 3.93/0.99      | ~ l1_pre_topc(X1) ),
% 3.93/0.99      inference(cnf_transformation,[],[f45]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_265,plain,
% 3.93/0.99      ( ~ v4_tops_1(X0,X1)
% 3.93/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.93/0.99      | r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
% 3.93/0.99      | sK0 != X1 ),
% 3.93/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_17]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_266,plain,
% 3.93/0.99      ( ~ v4_tops_1(X0,sK0)
% 3.93/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.93/0.99      | r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,X0))) ),
% 3.93/0.99      inference(unflattening,[status(thm)],[c_265]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_807,plain,
% 3.93/0.99      ( v4_tops_1(X0,sK0) != iProver_top
% 3.93/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.93/0.99      | r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,X0))) = iProver_top ),
% 3.93/0.99      inference(predicate_to_equality,[status(thm)],[c_266]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_809,plain,
% 3.93/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.93/0.99      | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.93/0.99      inference(predicate_to_equality,[status(thm)],[c_239]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_4,plain,
% 3.93/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.93/0.99      | ~ l1_pre_topc(X1)
% 3.93/0.99      | k2_pre_topc(X1,k2_pre_topc(X1,X0)) = k2_pre_topc(X1,X0) ),
% 3.93/0.99      inference(cnf_transformation,[],[f41]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_328,plain,
% 3.93/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.93/0.99      | k2_pre_topc(X1,k2_pre_topc(X1,X0)) = k2_pre_topc(X1,X0)
% 3.93/0.99      | sK0 != X1 ),
% 3.93/0.99      inference(resolution_lifted,[status(thm)],[c_4,c_17]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_329,plain,
% 3.93/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.93/0.99      | k2_pre_topc(sK0,k2_pre_topc(sK0,X0)) = k2_pre_topc(sK0,X0) ),
% 3.93/0.99      inference(unflattening,[status(thm)],[c_328]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_803,plain,
% 3.93/0.99      ( k2_pre_topc(sK0,k2_pre_topc(sK0,X0)) = k2_pre_topc(sK0,X0)
% 3.93/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.93/0.99      inference(predicate_to_equality,[status(thm)],[c_329]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_1497,plain,
% 3.93/0.99      ( k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,X0))) = k2_pre_topc(sK0,k1_tops_1(sK0,X0))
% 3.93/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.93/0.99      inference(superposition,[status(thm)],[c_809,c_803]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_3125,plain,
% 3.93/0.99      ( k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) ),
% 3.93/0.99      inference(superposition,[status(thm)],[c_813,c_1497]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_6,plain,
% 3.93/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.93/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.93/0.99      | ~ r1_tarski(X0,X2)
% 3.93/0.99      | r1_tarski(k2_pre_topc(X1,X0),k2_pre_topc(X1,X2))
% 3.93/0.99      | ~ l1_pre_topc(X1) ),
% 3.93/0.99      inference(cnf_transformation,[],[f43]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_298,plain,
% 3.93/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.93/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.93/0.99      | ~ r1_tarski(X0,X2)
% 3.93/0.99      | r1_tarski(k2_pre_topc(X1,X0),k2_pre_topc(X1,X2))
% 3.93/0.99      | sK0 != X1 ),
% 3.93/0.99      inference(resolution_lifted,[status(thm)],[c_6,c_17]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_299,plain,
% 3.93/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.93/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.93/0.99      | ~ r1_tarski(X1,X0)
% 3.93/0.99      | r1_tarski(k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X0)) ),
% 3.93/0.99      inference(unflattening,[status(thm)],[c_298]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_805,plain,
% 3.93/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.93/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.93/0.99      | r1_tarski(X1,X0) != iProver_top
% 3.93/0.99      | r1_tarski(k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X0)) = iProver_top ),
% 3.93/0.99      inference(predicate_to_equality,[status(thm)],[c_299]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_3153,plain,
% 3.93/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.93/0.99      | m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.93/0.99      | r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != iProver_top
% 3.93/0.99      | r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = iProver_top ),
% 3.93/0.99      inference(superposition,[status(thm)],[c_3125,c_805]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_929,plain,
% 3.93/0.99      ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.93/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.93/0.99      inference(instantiation,[status(thm)],[c_239]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_930,plain,
% 3.93/0.99      ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 3.93/0.99      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.93/0.99      inference(predicate_to_equality,[status(thm)],[c_929]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_1013,plain,
% 3.93/0.99      ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.93/0.99      | m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.93/0.99      inference(instantiation,[status(thm)],[c_341]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_1017,plain,
% 3.93/0.99      ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.93/0.99      | m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.93/0.99      inference(predicate_to_equality,[status(thm)],[c_1013]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_9594,plain,
% 3.93/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.93/0.99      | r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != iProver_top
% 3.93/0.99      | r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = iProver_top ),
% 3.93/0.99      inference(global_propositional_subsumption,
% 3.93/0.99                [status(thm)],
% 3.93/0.99                [c_3153,c_19,c_930,c_1017]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_0,plain,
% 3.93/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.93/0.99      inference(cnf_transformation,[],[f39]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_817,plain,
% 3.93/0.99      ( X0 = X1
% 3.93/0.99      | r1_tarski(X0,X1) != iProver_top
% 3.93/0.99      | r1_tarski(X1,X0) != iProver_top ),
% 3.93/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_1970,plain,
% 3.93/0.99      ( k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,X1)
% 3.93/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.93/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.93/0.99      | r1_tarski(X0,X1) != iProver_top
% 3.93/0.99      | r1_tarski(k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X0)) != iProver_top ),
% 3.93/0.99      inference(superposition,[status(thm)],[c_805,c_817]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_9609,plain,
% 3.93/0.99      ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k2_pre_topc(sK0,X0)
% 3.93/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.93/0.99      | m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.93/0.99      | r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != iProver_top
% 3.93/0.99      | r1_tarski(k1_tops_1(sK0,sK1),X0) != iProver_top ),
% 3.93/0.99      inference(superposition,[status(thm)],[c_9594,c_1970]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_12511,plain,
% 3.93/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.93/0.99      | k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k2_pre_topc(sK0,X0)
% 3.93/0.99      | r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != iProver_top
% 3.93/0.99      | r1_tarski(k1_tops_1(sK0,sK1),X0) != iProver_top ),
% 3.93/0.99      inference(global_propositional_subsumption,
% 3.93/0.99                [status(thm)],
% 3.93/0.99                [c_9609,c_19,c_930]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_12512,plain,
% 3.93/0.99      ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k2_pre_topc(sK0,X0)
% 3.93/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.93/0.99      | r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != iProver_top
% 3.93/0.99      | r1_tarski(k1_tops_1(sK0,sK1),X0) != iProver_top ),
% 3.93/0.99      inference(renaming,[status(thm)],[c_12511]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_12523,plain,
% 3.93/0.99      ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
% 3.93/0.99      | v4_tops_1(sK1,sK0) != iProver_top
% 3.93/0.99      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.93/0.99      | r1_tarski(k1_tops_1(sK0,sK1),sK1) != iProver_top ),
% 3.93/0.99      inference(superposition,[status(thm)],[c_807,c_12512]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_15,negated_conjecture,
% 3.93/0.99      ( v4_tops_1(sK1,sK0) ),
% 3.93/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_20,plain,
% 3.93/0.99      ( v4_tops_1(sK1,sK0) = iProver_top ),
% 3.93/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_12,plain,
% 3.93/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.93/0.99      | r1_tarski(k1_tops_1(X1,X0),X0)
% 3.93/0.99      | ~ l1_pre_topc(X1) ),
% 3.93/0.99      inference(cnf_transformation,[],[f49]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_214,plain,
% 3.93/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.93/0.99      | r1_tarski(k1_tops_1(X1,X0),X0)
% 3.93/0.99      | sK0 != X1 ),
% 3.93/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_17]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_215,plain,
% 3.93/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.93/0.99      | r1_tarski(k1_tops_1(sK0,X0),X0) ),
% 3.93/0.99      inference(unflattening,[status(thm)],[c_214]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_935,plain,
% 3.93/0.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.93/0.99      | r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
% 3.93/0.99      inference(instantiation,[status(thm)],[c_215]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_936,plain,
% 3.93/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.93/0.99      | r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
% 3.93/0.99      inference(predicate_to_equality,[status(thm)],[c_935]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_12595,plain,
% 3.93/0.99      ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 3.93/0.99      inference(global_propositional_subsumption,
% 3.93/0.99                [status(thm)],
% 3.93/0.99                [c_12523,c_19,c_20,c_936]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_7,plain,
% 3.93/0.99      ( v4_tops_1(X0,X1)
% 3.93/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.93/0.99      | ~ r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
% 3.93/0.99      | ~ r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
% 3.93/0.99      | ~ l1_pre_topc(X1) ),
% 3.93/0.99      inference(cnf_transformation,[],[f46]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_280,plain,
% 3.93/0.99      ( v4_tops_1(X0,X1)
% 3.93/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.93/0.99      | ~ r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
% 3.93/0.99      | ~ r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
% 3.93/0.99      | sK0 != X1 ),
% 3.93/0.99      inference(resolution_lifted,[status(thm)],[c_7,c_17]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_281,plain,
% 3.93/0.99      ( v4_tops_1(X0,sK0)
% 3.93/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.93/0.99      | ~ r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,X0)))
% 3.93/0.99      | ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),X0) ),
% 3.93/0.99      inference(unflattening,[status(thm)],[c_280]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_806,plain,
% 3.93/0.99      ( v4_tops_1(X0,sK0) = iProver_top
% 3.93/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.93/0.99      | r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,X0))) != iProver_top
% 3.93/0.99      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),X0) != iProver_top ),
% 3.93/0.99      inference(predicate_to_equality,[status(thm)],[c_281]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_12643,plain,
% 3.93/0.99      ( v4_tops_1(k1_tops_1(sK0,sK1),sK0) = iProver_top
% 3.93/0.99      | m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.93/0.99      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,sK1)) != iProver_top
% 3.93/0.99      | r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,k1_tops_1(sK0,sK1)))) != iProver_top ),
% 3.93/0.99      inference(superposition,[status(thm)],[c_12595,c_806]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_1697,plain,
% 3.93/0.99      ( k1_tops_1(sK0,k1_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
% 3.93/0.99      inference(superposition,[status(thm)],[c_813,c_810]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_12722,plain,
% 3.93/0.99      ( v4_tops_1(k1_tops_1(sK0,sK1),sK0) = iProver_top
% 3.93/0.99      | m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.93/0.99      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,sK1)) != iProver_top
% 3.93/0.99      | r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1)) != iProver_top ),
% 3.93/0.99      inference(light_normalisation,
% 3.93/0.99                [status(thm)],
% 3.93/0.99                [c_12643,c_1697,c_12595]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_14,negated_conjecture,
% 3.93/0.99      ( ~ v4_tops_1(k1_tops_1(sK0,sK1),sK0)
% 3.93/0.99      | ~ v4_tops_1(k2_pre_topc(sK0,sK1),sK0) ),
% 3.93/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_21,plain,
% 3.93/0.99      ( v4_tops_1(k1_tops_1(sK0,sK1),sK0) != iProver_top
% 3.93/0.99      | v4_tops_1(k2_pre_topc(sK0,sK1),sK0) != iProver_top ),
% 3.93/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_3152,plain,
% 3.93/0.99      ( v4_tops_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),sK0) = iProver_top
% 3.93/0.99      | m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.93/0.99      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != iProver_top
% 3.93/0.99      | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))))) != iProver_top ),
% 3.93/0.99      inference(superposition,[status(thm)],[c_3125,c_806]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_954,plain,
% 3.93/0.99      ( ~ v4_tops_1(sK1,sK0)
% 3.93/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.93/0.99      | r1_tarski(sK1,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
% 3.93/0.99      inference(instantiation,[status(thm)],[c_266]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_955,plain,
% 3.93/0.99      ( v4_tops_1(sK1,sK0) != iProver_top
% 3.93/0.99      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.93/0.99      | r1_tarski(sK1,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = iProver_top ),
% 3.93/0.99      inference(predicate_to_equality,[status(thm)],[c_954]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_1173,plain,
% 3.93/0.99      ( m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.93/0.99      | ~ m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.93/0.99      inference(instantiation,[status(thm)],[c_239]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_1174,plain,
% 3.93/0.99      ( m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 3.93/0.99      | m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.93/0.99      inference(predicate_to_equality,[status(thm)],[c_1173]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_1171,plain,
% 3.93/0.99      ( ~ m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.93/0.99      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
% 3.93/0.99      inference(instantiation,[status(thm)],[c_215]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_1178,plain,
% 3.93/0.99      ( m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.93/0.99      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = iProver_top ),
% 3.93/0.99      inference(predicate_to_equality,[status(thm)],[c_1171]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_1167,plain,
% 3.93/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.93/0.99      | ~ m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.93/0.99      | ~ r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))
% 3.93/0.99      | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))) ),
% 3.93/0.99      inference(instantiation,[status(thm)],[c_197]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_5381,plain,
% 3.93/0.99      ( ~ m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.93/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.93/0.99      | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))))
% 3.93/0.99      | ~ r1_tarski(sK1,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
% 3.93/0.99      inference(instantiation,[status(thm)],[c_1167]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_5382,plain,
% 3.93/0.99      ( m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.93/0.99      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.93/0.99      | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))) = iProver_top
% 3.93/0.99      | r1_tarski(sK1,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != iProver_top ),
% 3.93/0.99      inference(predicate_to_equality,[status(thm)],[c_5381]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_4423,plain,
% 3.93/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.93/0.99      | ~ m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.93/0.99      | ~ r1_tarski(X0,k1_tops_1(sK0,k2_pre_topc(sK0,X0)))
% 3.93/0.99      | r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,X0)))) ),
% 3.93/0.99      inference(instantiation,[status(thm)],[c_299]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_9176,plain,
% 3.93/0.99      ( ~ m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.93/0.99      | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.93/0.99      | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))))
% 3.93/0.99      | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))))) ),
% 3.93/0.99      inference(instantiation,[status(thm)],[c_4423]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_9179,plain,
% 3.93/0.99      ( m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.93/0.99      | m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.93/0.99      | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))) != iProver_top
% 3.93/0.99      | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))))) = iProver_top ),
% 3.93/0.99      inference(predicate_to_equality,[status(thm)],[c_9176]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_11204,plain,
% 3.93/0.99      ( v4_tops_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),sK0) = iProver_top ),
% 3.93/0.99      inference(global_propositional_subsumption,
% 3.93/0.99                [status(thm)],
% 3.93/0.99                [c_3152,c_19,c_20,c_930,c_955,c_1017,c_1174,c_1178,
% 3.93/0.99                 c_5382,c_9179]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_12601,plain,
% 3.93/0.99      ( v4_tops_1(k2_pre_topc(sK0,sK1),sK0) = iProver_top ),
% 3.93/0.99      inference(demodulation,[status(thm)],[c_12595,c_11204]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_5,plain,
% 3.93/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.93/0.99      | r1_tarski(X0,k2_pre_topc(X1,X0))
% 3.93/0.99      | ~ l1_pre_topc(X1) ),
% 3.93/0.99      inference(cnf_transformation,[],[f42]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_316,plain,
% 3.93/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.93/0.99      | r1_tarski(X0,k2_pre_topc(X1,X0))
% 3.93/0.99      | sK0 != X1 ),
% 3.93/0.99      inference(resolution_lifted,[status(thm)],[c_5,c_17]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_317,plain,
% 3.93/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.93/0.99      | r1_tarski(X0,k2_pre_topc(sK0,X0)) ),
% 3.93/0.99      inference(unflattening,[status(thm)],[c_316]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_804,plain,
% 3.93/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.93/0.99      | r1_tarski(X0,k2_pre_topc(sK0,X0)) = iProver_top ),
% 3.93/0.99      inference(predicate_to_equality,[status(thm)],[c_317]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_1499,plain,
% 3.93/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.93/0.99      | r1_tarski(k1_tops_1(sK0,X0),k2_pre_topc(sK0,k1_tops_1(sK0,X0))) = iProver_top ),
% 3.93/0.99      inference(superposition,[status(thm)],[c_809,c_804]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_12649,plain,
% 3.93/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.93/0.99      | r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1)) = iProver_top ),
% 3.93/0.99      inference(superposition,[status(thm)],[c_12595,c_1499]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_13231,plain,
% 3.93/0.99      ( r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,sK1)) != iProver_top ),
% 3.93/0.99      inference(global_propositional_subsumption,
% 3.93/0.99                [status(thm)],
% 3.93/0.99                [c_12722,c_19,c_21,c_930,c_12601,c_12649]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_13238,plain,
% 3.93/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.93/0.99      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK1) != iProver_top ),
% 3.93/0.99      inference(superposition,[status(thm)],[c_11994,c_13231]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_9,plain,
% 3.93/1.00      ( ~ v4_tops_1(X0,X1)
% 3.93/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.93/1.00      | r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
% 3.93/1.00      | ~ l1_pre_topc(X1) ),
% 3.93/1.00      inference(cnf_transformation,[],[f44]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_250,plain,
% 3.93/1.00      ( ~ v4_tops_1(X0,X1)
% 3.93/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.93/1.00      | r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
% 3.93/1.00      | sK0 != X1 ),
% 3.93/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_17]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_251,plain,
% 3.93/1.00      ( ~ v4_tops_1(X0,sK0)
% 3.93/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.93/1.00      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),X0) ),
% 3.93/1.00      inference(unflattening,[status(thm)],[c_250]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_947,plain,
% 3.93/1.00      ( ~ v4_tops_1(sK1,sK0)
% 3.93/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.93/1.00      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK1) ),
% 3.93/1.00      inference(instantiation,[status(thm)],[c_251]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(c_948,plain,
% 3.93/1.00      ( v4_tops_1(sK1,sK0) != iProver_top
% 3.93/1.00      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.93/1.00      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK1) = iProver_top ),
% 3.93/1.00      inference(predicate_to_equality,[status(thm)],[c_947]) ).
% 3.93/1.00  
% 3.93/1.00  cnf(contradiction,plain,
% 3.93/1.00      ( $false ),
% 3.93/1.00      inference(minisat,[status(thm)],[c_13238,c_948,c_20,c_19]) ).
% 3.93/1.00  
% 3.93/1.00  
% 3.93/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.93/1.00  
% 3.93/1.00  ------                               Statistics
% 3.93/1.00  
% 3.93/1.00  ------ General
% 3.93/1.00  
% 3.93/1.00  abstr_ref_over_cycles:                  0
% 3.93/1.00  abstr_ref_under_cycles:                 0
% 3.93/1.00  gc_basic_clause_elim:                   0
% 3.93/1.00  forced_gc_time:                         0
% 3.93/1.00  parsing_time:                           0.009
% 3.93/1.00  unif_index_cands_time:                  0.
% 3.93/1.00  unif_index_add_time:                    0.
% 3.93/1.00  orderings_time:                         0.
% 3.93/1.00  out_proof_time:                         0.012
% 3.93/1.00  total_time:                             0.407
% 3.93/1.00  num_of_symbols:                         41
% 3.93/1.00  num_of_terms:                           10485
% 3.93/1.00  
% 3.93/1.00  ------ Preprocessing
% 3.93/1.00  
% 3.93/1.00  num_of_splits:                          0
% 3.93/1.00  num_of_split_atoms:                     0
% 3.93/1.00  num_of_reused_defs:                     0
% 3.93/1.00  num_eq_ax_congr_red:                    0
% 3.93/1.00  num_of_sem_filtered_clauses:            1
% 3.93/1.00  num_of_subtypes:                        0
% 3.93/1.00  monotx_restored_types:                  0
% 3.93/1.00  sat_num_of_epr_types:                   0
% 3.93/1.00  sat_num_of_non_cyclic_types:            0
% 3.93/1.00  sat_guarded_non_collapsed_types:        0
% 3.93/1.00  num_pure_diseq_elim:                    0
% 3.93/1.00  simp_replaced_by:                       0
% 3.93/1.00  res_preprocessed:                       84
% 3.93/1.00  prep_upred:                             0
% 3.93/1.00  prep_unflattend:                        11
% 3.93/1.00  smt_new_axioms:                         0
% 3.93/1.00  pred_elim_cands:                        3
% 3.93/1.00  pred_elim:                              1
% 3.93/1.00  pred_elim_cl:                           1
% 3.93/1.00  pred_elim_cycles:                       3
% 3.93/1.00  merged_defs:                            0
% 3.93/1.00  merged_defs_ncl:                        0
% 3.93/1.00  bin_hyper_res:                          0
% 3.93/1.00  prep_cycles:                            4
% 3.93/1.00  pred_elim_time:                         0.004
% 3.93/1.00  splitting_time:                         0.
% 3.93/1.00  sem_filter_time:                        0.
% 3.93/1.00  monotx_time:                            0.
% 3.93/1.00  subtype_inf_time:                       0.
% 3.93/1.00  
% 3.93/1.00  ------ Problem properties
% 3.93/1.00  
% 3.93/1.00  clauses:                                16
% 3.93/1.00  conjectures:                            3
% 3.93/1.00  epr:                                    3
% 3.93/1.00  horn:                                   16
% 3.93/1.00  ground:                                 3
% 3.93/1.00  unary:                                  3
% 3.93/1.00  binary:                                 7
% 3.93/1.00  lits:                                   38
% 3.93/1.00  lits_eq:                                3
% 3.93/1.00  fd_pure:                                0
% 3.93/1.00  fd_pseudo:                              0
% 3.93/1.00  fd_cond:                                0
% 3.93/1.00  fd_pseudo_cond:                         1
% 3.93/1.00  ac_symbols:                             0
% 3.93/1.00  
% 3.93/1.00  ------ Propositional Solver
% 3.93/1.00  
% 3.93/1.00  prop_solver_calls:                      30
% 3.93/1.00  prop_fast_solver_calls:                 1063
% 3.93/1.00  smt_solver_calls:                       0
% 3.93/1.00  smt_fast_solver_calls:                  0
% 3.93/1.00  prop_num_of_clauses:                    4606
% 3.93/1.00  prop_preprocess_simplified:             8033
% 3.93/1.00  prop_fo_subsumed:                       51
% 3.93/1.00  prop_solver_time:                       0.
% 3.93/1.00  smt_solver_time:                        0.
% 3.93/1.00  smt_fast_solver_time:                   0.
% 3.93/1.00  prop_fast_solver_time:                  0.
% 3.93/1.00  prop_unsat_core_time:                   0.
% 3.93/1.00  
% 3.93/1.00  ------ QBF
% 3.93/1.00  
% 3.93/1.00  qbf_q_res:                              0
% 3.93/1.00  qbf_num_tautologies:                    0
% 3.93/1.00  qbf_prep_cycles:                        0
% 3.93/1.00  
% 3.93/1.00  ------ BMC1
% 3.93/1.00  
% 3.93/1.00  bmc1_current_bound:                     -1
% 3.93/1.00  bmc1_last_solved_bound:                 -1
% 3.93/1.00  bmc1_unsat_core_size:                   -1
% 3.93/1.00  bmc1_unsat_core_parents_size:           -1
% 3.93/1.00  bmc1_merge_next_fun:                    0
% 3.93/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.93/1.00  
% 3.93/1.00  ------ Instantiation
% 3.93/1.00  
% 3.93/1.00  inst_num_of_clauses:                    1275
% 3.93/1.00  inst_num_in_passive:                    284
% 3.93/1.00  inst_num_in_active:                     817
% 3.93/1.00  inst_num_in_unprocessed:                174
% 3.93/1.00  inst_num_of_loops:                      840
% 3.93/1.00  inst_num_of_learning_restarts:          0
% 3.93/1.00  inst_num_moves_active_passive:          20
% 3.93/1.00  inst_lit_activity:                      0
% 3.93/1.00  inst_lit_activity_moves:                1
% 3.93/1.00  inst_num_tautologies:                   0
% 3.93/1.00  inst_num_prop_implied:                  0
% 3.93/1.00  inst_num_existing_simplified:           0
% 3.93/1.00  inst_num_eq_res_simplified:             0
% 3.93/1.00  inst_num_child_elim:                    0
% 3.93/1.00  inst_num_of_dismatching_blockings:      1084
% 3.93/1.00  inst_num_of_non_proper_insts:           1158
% 3.93/1.00  inst_num_of_duplicates:                 0
% 3.93/1.00  inst_inst_num_from_inst_to_res:         0
% 3.93/1.00  inst_dismatching_checking_time:         0.
% 3.93/1.00  
% 3.93/1.00  ------ Resolution
% 3.93/1.00  
% 3.93/1.00  res_num_of_clauses:                     0
% 3.93/1.00  res_num_in_passive:                     0
% 3.93/1.00  res_num_in_active:                      0
% 3.93/1.00  res_num_of_loops:                       88
% 3.93/1.00  res_forward_subset_subsumed:            46
% 3.93/1.00  res_backward_subset_subsumed:           2
% 3.93/1.00  res_forward_subsumed:                   0
% 3.93/1.00  res_backward_subsumed:                  0
% 3.93/1.00  res_forward_subsumption_resolution:     0
% 3.93/1.00  res_backward_subsumption_resolution:    0
% 3.93/1.00  res_clause_to_clause_subsumption:       2861
% 3.93/1.00  res_orphan_elimination:                 0
% 3.93/1.00  res_tautology_del:                      19
% 3.93/1.00  res_num_eq_res_simplified:              0
% 3.93/1.00  res_num_sel_changes:                    0
% 3.93/1.00  res_moves_from_active_to_pass:          0
% 3.93/1.00  
% 3.93/1.00  ------ Superposition
% 3.93/1.00  
% 3.93/1.00  sup_time_total:                         0.
% 3.93/1.00  sup_time_generating:                    0.
% 3.93/1.00  sup_time_sim_full:                      0.
% 3.93/1.00  sup_time_sim_immed:                     0.
% 3.93/1.00  
% 3.93/1.00  sup_num_of_clauses:                     355
% 3.93/1.00  sup_num_in_active:                      151
% 3.93/1.00  sup_num_in_passive:                     204
% 3.93/1.00  sup_num_of_loops:                       167
% 3.93/1.00  sup_fw_superposition:                   486
% 3.93/1.00  sup_bw_superposition:                   300
% 3.93/1.00  sup_immediate_simplified:               277
% 3.93/1.00  sup_given_eliminated:                   0
% 3.93/1.00  comparisons_done:                       0
% 3.93/1.00  comparisons_avoided:                    0
% 3.93/1.00  
% 3.93/1.00  ------ Simplifications
% 3.93/1.00  
% 3.93/1.00  
% 3.93/1.00  sim_fw_subset_subsumed:                 25
% 3.93/1.00  sim_bw_subset_subsumed:                 8
% 3.93/1.00  sim_fw_subsumed:                        68
% 3.93/1.00  sim_bw_subsumed:                        4
% 3.93/1.00  sim_fw_subsumption_res:                 0
% 3.93/1.00  sim_bw_subsumption_res:                 0
% 3.93/1.00  sim_tautology_del:                      53
% 3.93/1.00  sim_eq_tautology_del:                   141
% 3.93/1.00  sim_eq_res_simp:                        0
% 3.93/1.00  sim_fw_demodulated:                     40
% 3.93/1.00  sim_bw_demodulated:                     13
% 3.93/1.00  sim_light_normalised:                   175
% 3.93/1.00  sim_joinable_taut:                      0
% 3.93/1.00  sim_joinable_simp:                      0
% 3.93/1.00  sim_ac_normalised:                      0
% 3.93/1.00  sim_smt_subsumption:                    0
% 3.93/1.00  
%------------------------------------------------------------------------------
