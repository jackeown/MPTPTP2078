%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:15:58 EST 2020

% Result     : Theorem 11.81s
% Output     : CNFRefutation 11.81s
% Verified   : 
% Statistics : Number of formulae       :  214 (1926 expanded)
%              Number of clauses        :  155 ( 636 expanded)
%              Number of leaves         :   17 ( 435 expanded)
%              Depth                    :   22
%              Number of atoms          :  672 (8010 expanded)
%              Number of equality atoms :  244 ( 730 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f56,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f42,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f58,plain,(
    v4_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_tops_1(X1,X0)
          <=> ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_tops_1(X1,X0)
          <=> ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

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
    inference(nnf_transformation,[],[f22])).

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
      ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
      | ~ v4_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)
      | ~ v4_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v4_tops_1(X1,X0)
      | ~ r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
      | ~ r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f59,plain,
    ( ~ v4_tops_1(k2_pre_topc(sK0,sK1),sK0)
    | ~ v4_tops_1(k1_tops_1(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_600,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_4994,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))
    | k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) != X1
    | k2_pre_topc(sK0,sK1) != X0 ),
    inference(instantiation,[status(thm)],[c_600])).

cnf(c_17242,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,sK1),X0)
    | r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))
    | k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) != X0
    | k2_pre_topc(sK0,sK1) != k2_pre_topc(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_4994])).

cnf(c_39153,plain,
    ( r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))
    | ~ r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))))
    | k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) != k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))
    | k2_pre_topc(sK0,sK1) != k2_pre_topc(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_17242])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1026,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_19,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_387,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_19])).

cnf(c_388,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_387])).

cnf(c_1016,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_388])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,k1_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_285,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,k1_tops_1(X1,X0)) = k1_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_19])).

cnf(c_286,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,k1_tops_1(sK0,X0)) = k1_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_285])).

cnf(c_1023,plain,
    ( k1_tops_1(sK0,k1_tops_1(sK0,X0)) = k1_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_286])).

cnf(c_2086,plain,
    ( k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,X0))) = k1_tops_1(sK0,k2_pre_topc(sK0,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1016,c_1023])).

cnf(c_4394,plain,
    ( k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) = k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_1026,c_2086])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_255,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_19])).

cnf(c_256,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X1,X0)
    | r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_255])).

cnf(c_1025,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_256])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_273,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_19])).

cnf(c_274,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,X0),X0) ),
    inference(unflattening,[status(thm)],[c_273])).

cnf(c_1024,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_274])).

cnf(c_1198,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1026,c_1024])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1031,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2785,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),X0) = iProver_top
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1198,c_1031])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1033,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3131,plain,
    ( k1_tops_1(sK0,sK1) = X0
    | r1_tarski(X0,k1_tops_1(sK0,sK1)) != iProver_top
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2785,c_1033])).

cnf(c_4289,plain,
    ( k1_tops_1(sK0,X0) = k1_tops_1(sK0,sK1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(sK1,k1_tops_1(sK0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1025,c_3131])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1029,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1763,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1026,c_1029])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1032,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_4,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1030,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2781,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),X2) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X1),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1025,c_1031])).

cnf(c_13873,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),X1) = iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1026,c_2781])).

cnf(c_14167,plain,
    ( r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),X1) = iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1030,c_13873])).

cnf(c_14179,plain,
    ( r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1032,c_14167])).

cnf(c_14753,plain,
    ( k1_tops_1(sK0,X0) = k1_tops_1(sK0,sK1)
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(sK1,k1_tops_1(sK0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_14179,c_3131])).

cnf(c_1269,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,u1_struct_0(sK0))
    | r1_tarski(X0,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_16869,plain,
    ( r1_tarski(X0,u1_struct_0(sK0))
    | ~ r1_tarski(X0,sK1)
    | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1269])).

cnf(c_16870,plain,
    ( r1_tarski(X0,u1_struct_0(sK0)) = iProver_top
    | r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(sK1,u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16869])).

cnf(c_37379,plain,
    ( k1_tops_1(sK0,X0) = k1_tops_1(sK0,sK1)
    | r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(sK1,k1_tops_1(sK0,X0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4289,c_1763,c_14753,c_16870])).

cnf(c_37386,plain,
    ( k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) = k1_tops_1(sK0,sK1)
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK1) != iProver_top
    | r1_tarski(sK1,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4394,c_37379])).

cnf(c_37403,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,sK1)
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK1) != iProver_top
    | r1_tarski(sK1,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_37386,c_4394])).

cnf(c_17,negated_conjecture,
    ( v4_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_297,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_19])).

cnf(c_298,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_297])).

cnf(c_1070,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_298])).

cnf(c_1083,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_388])).

cnf(c_1088,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(instantiation,[status(thm)],[c_274])).

cnf(c_10,plain,
    ( ~ v4_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_324,plain,
    ( ~ v4_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_19])).

cnf(c_325,plain,
    ( ~ v4_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,X0))) ),
    inference(unflattening,[status(thm)],[c_324])).

cnf(c_1109,plain,
    ( ~ v4_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK1,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
    inference(instantiation,[status(thm)],[c_325])).

cnf(c_1175,plain,
    ( m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_298])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k2_pre_topc(X1,X0),k2_pre_topc(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_357,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k2_pre_topc(X1,X0),k2_pre_topc(X1,X2))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_19])).

cnf(c_358,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X1,X0)
    | r1_tarski(k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_357])).

cnf(c_1125,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,sK1)
    | r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_358])).

cnf(c_1222,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k2_pre_topc(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_1125])).

cnf(c_1782,plain,
    ( ~ r1_tarski(X0,k2_pre_topc(sK0,sK1))
    | ~ r1_tarski(sK1,X0)
    | r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_3718,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k2_pre_topc(sK0,sK1))
    | ~ r1_tarski(sK1,k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))
    | r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_1782])).

cnf(c_14740,plain,
    ( r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,sK1)) = iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),u1_struct_0(sK0)) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4394,c_14179])).

cnf(c_21,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_22,plain,
    ( v4_tops_1(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_11,plain,
    ( ~ v4_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_309,plain,
    ( ~ v4_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_19])).

cnf(c_310,plain,
    ( ~ v4_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),X0) ),
    inference(unflattening,[status(thm)],[c_309])).

cnf(c_1103,plain,
    ( ~ v4_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK1) ),
    inference(instantiation,[status(thm)],[c_310])).

cnf(c_1104,plain,
    ( v4_tops_1(sK1,sK0) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1103])).

cnf(c_15108,plain,
    ( r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),u1_struct_0(sK0)) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14740,c_21,c_22,c_1104])).

cnf(c_15109,plain,
    ( r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,sK1)) = iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),u1_struct_0(sK0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_15108])).

cnf(c_2311,plain,
    ( k1_tops_1(sK0,X0) = k1_tops_1(sK0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1025,c_1033])).

cnf(c_15115,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,sK1)
    | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),u1_struct_0(sK0)) != iProver_top
    | r1_tarski(sK1,k2_pre_topc(sK0,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_15109,c_2311])).

cnf(c_15122,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),u1_struct_0(sK0))
    | ~ r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_15115])).

cnf(c_1261,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(X0,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_15148,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,X0),u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1261])).

cnf(c_24292,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_15148])).

cnf(c_38057,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_37403,c_18,c_17,c_1070,c_1083,c_1088,c_1109,c_1175,c_1222,c_3718,c_15122,c_24292])).

cnf(c_9,plain,
    ( v4_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
    | ~ r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_339,plain,
    ( v4_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
    | ~ r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_19])).

cnf(c_340,plain,
    ( v4_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,X0)))
    | ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),X0) ),
    inference(unflattening,[status(thm)],[c_339])).

cnf(c_1019,plain,
    ( v4_tops_1(X0,sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,X0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_340])).

cnf(c_2591,plain,
    ( v4_tops_1(k1_tops_1(sK0,X0),sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,X0)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),k2_pre_topc(sK0,k1_tops_1(sK0,k1_tops_1(sK0,X0)))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,X0)),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1025,c_1019])).

cnf(c_299,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_298])).

cnf(c_11380,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,X0)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_388])).

cnf(c_11381,plain,
    ( m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,X0)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11380])).

cnf(c_11800,plain,
    ( v4_tops_1(k1_tops_1(sK0,X0),sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),k2_pre_topc(sK0,k1_tops_1(sK0,k1_tops_1(sK0,X0)))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,X0)),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2591,c_299,c_11381])).

cnf(c_38155,plain,
    ( v4_tops_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK0) = iProver_top
    | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,k1_tops_1(sK0,sK1)))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))),k2_pre_topc(sK0,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_38057,c_11800])).

cnf(c_2084,plain,
    ( k1_tops_1(sK0,k1_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_1026,c_1023])).

cnf(c_38194,plain,
    ( v4_tops_1(k1_tops_1(sK0,sK1),sK0) = iProver_top
    | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k2_pre_topc(sK0,sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_38155,c_2084,c_38057])).

cnf(c_599,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_9150,plain,
    ( X0 != X1
    | k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) != X1
    | k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = X0 ),
    inference(instantiation,[status(thm)],[c_599])).

cnf(c_22081,plain,
    ( X0 != k2_pre_topc(sK0,k1_tops_1(sK0,sK1))
    | k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = X0
    | k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) != k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_9150])).

cnf(c_33165,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) != k2_pre_topc(sK0,k1_tops_1(sK0,sK1))
    | k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))
    | k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_22081])).

cnf(c_8021,plain,
    ( ~ r1_tarski(X0,k2_pre_topc(sK0,sK1))
    | ~ r1_tarski(k2_pre_topc(sK0,sK1),X0)
    | k2_pre_topc(sK0,sK1) = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_21001,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k2_pre_topc(sK0,sK1))
    | ~ r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))
    | k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_8021])).

cnf(c_10852,plain,
    ( ~ r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,X1)))
    | ~ r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,X1)),X0)
    | k2_pre_topc(sK0,k1_tops_1(sK0,X1)) = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_19849,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))))
    | k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) = k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) ),
    inference(instantiation,[status(thm)],[c_10852])).

cnf(c_598,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_14502,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_598])).

cnf(c_13706,plain,
    ( k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_598])).

cnf(c_4312,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,k2_pre_topc(sK0,k1_tops_1(sK0,X2)))
    | X2 != X0
    | k2_pre_topc(sK0,k1_tops_1(sK0,X2)) != X1 ),
    inference(instantiation,[status(thm)],[c_600])).

cnf(c_10857,plain,
    ( ~ r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,X1)))
    | r1_tarski(X1,k2_pre_topc(sK0,k1_tops_1(sK0,X1)))
    | X1 != X0
    | k2_pre_topc(sK0,k1_tops_1(sK0,X1)) != k2_pre_topc(sK0,k1_tops_1(sK0,X1)) ),
    inference(instantiation,[status(thm)],[c_4312])).

cnf(c_13408,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))))
    | r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))))
    | k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) != k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))
    | k2_pre_topc(sK0,sK1) != k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_10857])).

cnf(c_13409,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) != k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))
    | k2_pre_topc(sK0,sK1) != k2_pre_topc(sK0,k1_tops_1(sK0,sK1))
    | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13408])).

cnf(c_1020,plain,
    ( v4_tops_1(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_325])).

cnf(c_2193,plain,
    ( v4_tops_1(k1_tops_1(sK0,sK1),sK0) != iProver_top
    | m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2084,c_1020])).

cnf(c_1071,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1070])).

cnf(c_6868,plain,
    ( v4_tops_1(k1_tops_1(sK0,sK1),sK0) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2193,c_21,c_1071])).

cnf(c_6873,plain,
    ( v4_tops_1(k1_tops_1(sK0,sK1),sK0) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),X0) = iProver_top
    | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6868,c_1031])).

cnf(c_1110,plain,
    ( v4_tops_1(sK1,sK0) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK1,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1109])).

cnf(c_3710,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(sK1,X0)
    | r1_tarski(sK1,X1) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_9630,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),X0)
    | r1_tarski(sK1,X0)
    | ~ r1_tarski(sK1,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
    inference(instantiation,[status(thm)],[c_3710])).

cnf(c_9631,plain,
    ( r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),X0) != iProver_top
    | r1_tarski(sK1,X0) = iProver_top
    | r1_tarski(sK1,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9630])).

cnf(c_12816,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),X0) = iProver_top
    | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6873,c_21,c_22,c_1110,c_2785,c_9631])).

cnf(c_12822,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1032,c_12816])).

cnf(c_1432,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))
    | r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))) ),
    inference(instantiation,[status(thm)],[c_358])).

cnf(c_5257,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))
    | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))) ),
    inference(instantiation,[status(thm)],[c_1432])).

cnf(c_5254,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))
    | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))) ),
    inference(instantiation,[status(thm)],[c_1432])).

cnf(c_5255,plain,
    ( m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5254])).

cnf(c_1290,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))
    | r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))) ),
    inference(instantiation,[status(thm)],[c_358])).

cnf(c_3726,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))))
    | ~ r1_tarski(sK1,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
    inference(instantiation,[status(thm)],[c_1290])).

cnf(c_3719,plain,
    ( r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k2_pre_topc(sK0,sK1)) != iProver_top
    | r1_tarski(sK1,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != iProver_top
    | r1_tarski(sK1,k2_pre_topc(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3718])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k2_pre_topc(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_375,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,k2_pre_topc(X1,X0)) = k2_pre_topc(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_19])).

cnf(c_376,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k2_pre_topc(sK0,X0)) = k2_pre_topc(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_375])).

cnf(c_1017,plain,
    ( k2_pre_topc(sK0,k2_pre_topc(sK0,X0)) = k2_pre_topc(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_376])).

cnf(c_1461,plain,
    ( k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_1026,c_1017])).

cnf(c_2593,plain,
    ( v4_tops_1(k2_pre_topc(sK0,sK1),sK0) = iProver_top
    | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_pre_topc(sK0,sK1)) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1461,c_1019])).

cnf(c_1170,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,k2_pre_topc(sK0,sK1))
    | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) ),
    inference(instantiation,[status(thm)],[c_256])).

cnf(c_2340,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))
    | ~ r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_1170])).

cnf(c_2334,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))
    | ~ r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_1170])).

cnf(c_2335,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) = iProver_top
    | r1_tarski(sK1,k2_pre_topc(sK0,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2334])).

cnf(c_1469,plain,
    ( r1_tarski(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1229,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK1))
    | ~ r1_tarski(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_1125])).

cnf(c_1223,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),sK1) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k2_pre_topc(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1222])).

cnf(c_1173,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_pre_topc(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_274])).

cnf(c_1180,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_pre_topc(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1173])).

cnf(c_1176,plain,
    ( m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1175])).

cnf(c_1135,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_376])).

cnf(c_1138,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_388])).

cnf(c_1089,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1088])).

cnf(c_1084,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1083])).

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
    inference(minisat,[status(thm)],[c_39153,c_38194,c_33165,c_21001,c_19849,c_14502,c_13706,c_13409,c_12822,c_5257,c_5255,c_3726,c_3719,c_2593,c_2340,c_2335,c_1469,c_1229,c_1223,c_1222,c_1180,c_1176,c_1175,c_1135,c_1138,c_1110,c_1109,c_1089,c_1088,c_1084,c_1083,c_1071,c_1070,c_23,c_22,c_17,c_21,c_18])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:49:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 11.81/2.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.81/2.00  
% 11.81/2.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.81/2.00  
% 11.81/2.00  ------  iProver source info
% 11.81/2.00  
% 11.81/2.00  git: date: 2020-06-30 10:37:57 +0100
% 11.81/2.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.81/2.00  git: non_committed_changes: false
% 11.81/2.00  git: last_make_outside_of_git: false
% 11.81/2.00  
% 11.81/2.00  ------ 
% 11.81/2.00  
% 11.81/2.00  ------ Input Options
% 11.81/2.00  
% 11.81/2.00  --out_options                           all
% 11.81/2.00  --tptp_safe_out                         true
% 11.81/2.00  --problem_path                          ""
% 11.81/2.00  --include_path                          ""
% 11.81/2.00  --clausifier                            res/vclausify_rel
% 11.81/2.00  --clausifier_options                    ""
% 11.81/2.00  --stdin                                 false
% 11.81/2.00  --stats_out                             all
% 11.81/2.00  
% 11.81/2.00  ------ General Options
% 11.81/2.00  
% 11.81/2.00  --fof                                   false
% 11.81/2.00  --time_out_real                         305.
% 11.81/2.00  --time_out_virtual                      -1.
% 11.81/2.00  --symbol_type_check                     false
% 11.81/2.00  --clausify_out                          false
% 11.81/2.00  --sig_cnt_out                           false
% 11.81/2.00  --trig_cnt_out                          false
% 11.81/2.00  --trig_cnt_out_tolerance                1.
% 11.81/2.00  --trig_cnt_out_sk_spl                   false
% 11.81/2.00  --abstr_cl_out                          false
% 11.81/2.00  
% 11.81/2.00  ------ Global Options
% 11.81/2.00  
% 11.81/2.00  --schedule                              default
% 11.81/2.00  --add_important_lit                     false
% 11.81/2.00  --prop_solver_per_cl                    1000
% 11.81/2.00  --min_unsat_core                        false
% 11.81/2.00  --soft_assumptions                      false
% 11.81/2.00  --soft_lemma_size                       3
% 11.81/2.00  --prop_impl_unit_size                   0
% 11.81/2.00  --prop_impl_unit                        []
% 11.81/2.00  --share_sel_clauses                     true
% 11.81/2.00  --reset_solvers                         false
% 11.81/2.00  --bc_imp_inh                            [conj_cone]
% 11.81/2.00  --conj_cone_tolerance                   3.
% 11.81/2.00  --extra_neg_conj                        none
% 11.81/2.00  --large_theory_mode                     true
% 11.81/2.00  --prolific_symb_bound                   200
% 11.81/2.00  --lt_threshold                          2000
% 11.81/2.00  --clause_weak_htbl                      true
% 11.81/2.00  --gc_record_bc_elim                     false
% 11.81/2.00  
% 11.81/2.00  ------ Preprocessing Options
% 11.81/2.00  
% 11.81/2.00  --preprocessing_flag                    true
% 11.81/2.00  --time_out_prep_mult                    0.1
% 11.81/2.00  --splitting_mode                        input
% 11.81/2.00  --splitting_grd                         true
% 11.81/2.00  --splitting_cvd                         false
% 11.81/2.00  --splitting_cvd_svl                     false
% 11.81/2.00  --splitting_nvd                         32
% 11.81/2.00  --sub_typing                            true
% 11.81/2.00  --prep_gs_sim                           true
% 11.81/2.00  --prep_unflatten                        true
% 11.81/2.00  --prep_res_sim                          true
% 11.81/2.00  --prep_upred                            true
% 11.81/2.00  --prep_sem_filter                       exhaustive
% 11.81/2.00  --prep_sem_filter_out                   false
% 11.81/2.00  --pred_elim                             true
% 11.81/2.00  --res_sim_input                         true
% 11.81/2.00  --eq_ax_congr_red                       true
% 11.81/2.00  --pure_diseq_elim                       true
% 11.81/2.00  --brand_transform                       false
% 11.81/2.00  --non_eq_to_eq                          false
% 11.81/2.00  --prep_def_merge                        true
% 11.81/2.00  --prep_def_merge_prop_impl              false
% 11.81/2.00  --prep_def_merge_mbd                    true
% 11.81/2.00  --prep_def_merge_tr_red                 false
% 11.81/2.00  --prep_def_merge_tr_cl                  false
% 11.81/2.00  --smt_preprocessing                     true
% 11.81/2.00  --smt_ac_axioms                         fast
% 11.81/2.00  --preprocessed_out                      false
% 11.81/2.00  --preprocessed_stats                    false
% 11.81/2.00  
% 11.81/2.00  ------ Abstraction refinement Options
% 11.81/2.00  
% 11.81/2.00  --abstr_ref                             []
% 11.81/2.00  --abstr_ref_prep                        false
% 11.81/2.00  --abstr_ref_until_sat                   false
% 11.81/2.00  --abstr_ref_sig_restrict                funpre
% 11.81/2.00  --abstr_ref_af_restrict_to_split_sk     false
% 11.81/2.00  --abstr_ref_under                       []
% 11.81/2.00  
% 11.81/2.00  ------ SAT Options
% 11.81/2.00  
% 11.81/2.00  --sat_mode                              false
% 11.81/2.00  --sat_fm_restart_options                ""
% 11.81/2.00  --sat_gr_def                            false
% 11.81/2.00  --sat_epr_types                         true
% 11.81/2.00  --sat_non_cyclic_types                  false
% 11.81/2.00  --sat_finite_models                     false
% 11.81/2.00  --sat_fm_lemmas                         false
% 11.81/2.00  --sat_fm_prep                           false
% 11.81/2.00  --sat_fm_uc_incr                        true
% 11.81/2.00  --sat_out_model                         small
% 11.81/2.00  --sat_out_clauses                       false
% 11.81/2.00  
% 11.81/2.00  ------ QBF Options
% 11.81/2.00  
% 11.81/2.00  --qbf_mode                              false
% 11.81/2.00  --qbf_elim_univ                         false
% 11.81/2.00  --qbf_dom_inst                          none
% 11.81/2.00  --qbf_dom_pre_inst                      false
% 11.81/2.00  --qbf_sk_in                             false
% 11.81/2.00  --qbf_pred_elim                         true
% 11.81/2.00  --qbf_split                             512
% 11.81/2.00  
% 11.81/2.00  ------ BMC1 Options
% 11.81/2.00  
% 11.81/2.00  --bmc1_incremental                      false
% 11.81/2.00  --bmc1_axioms                           reachable_all
% 11.81/2.00  --bmc1_min_bound                        0
% 11.81/2.00  --bmc1_max_bound                        -1
% 11.81/2.00  --bmc1_max_bound_default                -1
% 11.81/2.00  --bmc1_symbol_reachability              true
% 11.81/2.00  --bmc1_property_lemmas                  false
% 11.81/2.00  --bmc1_k_induction                      false
% 11.81/2.00  --bmc1_non_equiv_states                 false
% 11.81/2.00  --bmc1_deadlock                         false
% 11.81/2.00  --bmc1_ucm                              false
% 11.81/2.00  --bmc1_add_unsat_core                   none
% 11.81/2.00  --bmc1_unsat_core_children              false
% 11.81/2.00  --bmc1_unsat_core_extrapolate_axioms    false
% 11.81/2.00  --bmc1_out_stat                         full
% 11.81/2.00  --bmc1_ground_init                      false
% 11.81/2.00  --bmc1_pre_inst_next_state              false
% 11.81/2.00  --bmc1_pre_inst_state                   false
% 11.81/2.00  --bmc1_pre_inst_reach_state             false
% 11.81/2.00  --bmc1_out_unsat_core                   false
% 11.81/2.00  --bmc1_aig_witness_out                  false
% 11.81/2.00  --bmc1_verbose                          false
% 11.81/2.00  --bmc1_dump_clauses_tptp                false
% 11.81/2.00  --bmc1_dump_unsat_core_tptp             false
% 11.81/2.00  --bmc1_dump_file                        -
% 11.81/2.00  --bmc1_ucm_expand_uc_limit              128
% 11.81/2.00  --bmc1_ucm_n_expand_iterations          6
% 11.81/2.00  --bmc1_ucm_extend_mode                  1
% 11.81/2.00  --bmc1_ucm_init_mode                    2
% 11.81/2.00  --bmc1_ucm_cone_mode                    none
% 11.81/2.00  --bmc1_ucm_reduced_relation_type        0
% 11.81/2.00  --bmc1_ucm_relax_model                  4
% 11.81/2.00  --bmc1_ucm_full_tr_after_sat            true
% 11.81/2.00  --bmc1_ucm_expand_neg_assumptions       false
% 11.81/2.00  --bmc1_ucm_layered_model                none
% 11.81/2.00  --bmc1_ucm_max_lemma_size               10
% 11.81/2.00  
% 11.81/2.00  ------ AIG Options
% 11.81/2.00  
% 11.81/2.00  --aig_mode                              false
% 11.81/2.00  
% 11.81/2.00  ------ Instantiation Options
% 11.81/2.00  
% 11.81/2.00  --instantiation_flag                    true
% 11.81/2.00  --inst_sos_flag                         true
% 11.81/2.00  --inst_sos_phase                        true
% 11.81/2.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.81/2.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.81/2.00  --inst_lit_sel_side                     num_symb
% 11.81/2.00  --inst_solver_per_active                1400
% 11.81/2.00  --inst_solver_calls_frac                1.
% 11.81/2.00  --inst_passive_queue_type               priority_queues
% 11.81/2.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.81/2.00  --inst_passive_queues_freq              [25;2]
% 11.81/2.00  --inst_dismatching                      true
% 11.81/2.00  --inst_eager_unprocessed_to_passive     true
% 11.81/2.00  --inst_prop_sim_given                   true
% 11.81/2.00  --inst_prop_sim_new                     false
% 11.81/2.00  --inst_subs_new                         false
% 11.81/2.00  --inst_eq_res_simp                      false
% 11.81/2.00  --inst_subs_given                       false
% 11.81/2.00  --inst_orphan_elimination               true
% 11.81/2.00  --inst_learning_loop_flag               true
% 11.81/2.00  --inst_learning_start                   3000
% 11.81/2.00  --inst_learning_factor                  2
% 11.81/2.00  --inst_start_prop_sim_after_learn       3
% 11.81/2.00  --inst_sel_renew                        solver
% 11.81/2.00  --inst_lit_activity_flag                true
% 11.81/2.00  --inst_restr_to_given                   false
% 11.81/2.00  --inst_activity_threshold               500
% 11.81/2.00  --inst_out_proof                        true
% 11.81/2.00  
% 11.81/2.00  ------ Resolution Options
% 11.81/2.00  
% 11.81/2.00  --resolution_flag                       true
% 11.81/2.00  --res_lit_sel                           adaptive
% 11.81/2.00  --res_lit_sel_side                      none
% 11.81/2.00  --res_ordering                          kbo
% 11.81/2.00  --res_to_prop_solver                    active
% 11.81/2.00  --res_prop_simpl_new                    false
% 11.81/2.00  --res_prop_simpl_given                  true
% 11.81/2.00  --res_passive_queue_type                priority_queues
% 11.81/2.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.81/2.00  --res_passive_queues_freq               [15;5]
% 11.81/2.00  --res_forward_subs                      full
% 11.81/2.00  --res_backward_subs                     full
% 11.81/2.00  --res_forward_subs_resolution           true
% 11.81/2.00  --res_backward_subs_resolution          true
% 11.81/2.00  --res_orphan_elimination                true
% 11.81/2.00  --res_time_limit                        2.
% 11.81/2.00  --res_out_proof                         true
% 11.81/2.00  
% 11.81/2.00  ------ Superposition Options
% 11.81/2.00  
% 11.81/2.00  --superposition_flag                    true
% 11.81/2.00  --sup_passive_queue_type                priority_queues
% 11.81/2.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.81/2.00  --sup_passive_queues_freq               [8;1;4]
% 11.81/2.00  --demod_completeness_check              fast
% 11.81/2.00  --demod_use_ground                      true
% 11.81/2.00  --sup_to_prop_solver                    passive
% 11.81/2.00  --sup_prop_simpl_new                    true
% 11.81/2.00  --sup_prop_simpl_given                  true
% 11.81/2.00  --sup_fun_splitting                     true
% 11.81/2.00  --sup_smt_interval                      50000
% 11.81/2.00  
% 11.81/2.00  ------ Superposition Simplification Setup
% 11.81/2.00  
% 11.81/2.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.81/2.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.81/2.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.81/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.81/2.00  --sup_full_triv                         [TrivRules;PropSubs]
% 11.81/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.81/2.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.81/2.00  --sup_immed_triv                        [TrivRules]
% 11.81/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.81/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.81/2.00  --sup_immed_bw_main                     []
% 11.81/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.81/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 11.81/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.81/2.00  --sup_input_bw                          []
% 11.81/2.00  
% 11.81/2.00  ------ Combination Options
% 11.81/2.00  
% 11.81/2.00  --comb_res_mult                         3
% 11.81/2.00  --comb_sup_mult                         2
% 11.81/2.00  --comb_inst_mult                        10
% 11.81/2.00  
% 11.81/2.00  ------ Debug Options
% 11.81/2.00  
% 11.81/2.00  --dbg_backtrace                         false
% 11.81/2.00  --dbg_dump_prop_clauses                 false
% 11.81/2.00  --dbg_dump_prop_clauses_file            -
% 11.81/2.00  --dbg_out_stat                          false
% 11.81/2.00  ------ Parsing...
% 11.81/2.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.81/2.00  
% 11.81/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 11.81/2.00  
% 11.81/2.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.81/2.00  
% 11.81/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.81/2.00  ------ Proving...
% 11.81/2.00  ------ Problem Properties 
% 11.81/2.00  
% 11.81/2.00  
% 11.81/2.00  clauses                                 18
% 11.81/2.00  conjectures                             3
% 11.81/2.00  EPR                                     4
% 11.81/2.00  Horn                                    18
% 11.81/2.00  unary                                   3
% 11.81/2.00  binary                                  8
% 11.81/2.00  lits                                    43
% 11.81/2.00  lits eq                                 3
% 11.81/2.00  fd_pure                                 0
% 11.81/2.00  fd_pseudo                               0
% 11.81/2.00  fd_cond                                 0
% 11.81/2.00  fd_pseudo_cond                          1
% 11.81/2.00  AC symbols                              0
% 11.81/2.00  
% 11.81/2.00  ------ Schedule dynamic 5 is on 
% 11.81/2.00  
% 11.81/2.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.81/2.00  
% 11.81/2.00  
% 11.81/2.00  ------ 
% 11.81/2.00  Current options:
% 11.81/2.00  ------ 
% 11.81/2.00  
% 11.81/2.00  ------ Input Options
% 11.81/2.00  
% 11.81/2.00  --out_options                           all
% 11.81/2.00  --tptp_safe_out                         true
% 11.81/2.00  --problem_path                          ""
% 11.81/2.00  --include_path                          ""
% 11.81/2.00  --clausifier                            res/vclausify_rel
% 11.81/2.00  --clausifier_options                    ""
% 11.81/2.00  --stdin                                 false
% 11.81/2.00  --stats_out                             all
% 11.81/2.00  
% 11.81/2.00  ------ General Options
% 11.81/2.00  
% 11.81/2.00  --fof                                   false
% 11.81/2.00  --time_out_real                         305.
% 11.81/2.00  --time_out_virtual                      -1.
% 11.81/2.00  --symbol_type_check                     false
% 11.81/2.00  --clausify_out                          false
% 11.81/2.00  --sig_cnt_out                           false
% 11.81/2.00  --trig_cnt_out                          false
% 11.81/2.00  --trig_cnt_out_tolerance                1.
% 11.81/2.00  --trig_cnt_out_sk_spl                   false
% 11.81/2.00  --abstr_cl_out                          false
% 11.81/2.00  
% 11.81/2.00  ------ Global Options
% 11.81/2.00  
% 11.81/2.00  --schedule                              default
% 11.81/2.00  --add_important_lit                     false
% 11.81/2.00  --prop_solver_per_cl                    1000
% 11.81/2.00  --min_unsat_core                        false
% 11.81/2.00  --soft_assumptions                      false
% 11.81/2.00  --soft_lemma_size                       3
% 11.81/2.00  --prop_impl_unit_size                   0
% 11.81/2.00  --prop_impl_unit                        []
% 11.81/2.00  --share_sel_clauses                     true
% 11.81/2.00  --reset_solvers                         false
% 11.81/2.00  --bc_imp_inh                            [conj_cone]
% 11.81/2.00  --conj_cone_tolerance                   3.
% 11.81/2.00  --extra_neg_conj                        none
% 11.81/2.00  --large_theory_mode                     true
% 11.81/2.00  --prolific_symb_bound                   200
% 11.81/2.00  --lt_threshold                          2000
% 11.81/2.00  --clause_weak_htbl                      true
% 11.81/2.00  --gc_record_bc_elim                     false
% 11.81/2.00  
% 11.81/2.00  ------ Preprocessing Options
% 11.81/2.00  
% 11.81/2.00  --preprocessing_flag                    true
% 11.81/2.00  --time_out_prep_mult                    0.1
% 11.81/2.00  --splitting_mode                        input
% 11.81/2.00  --splitting_grd                         true
% 11.81/2.00  --splitting_cvd                         false
% 11.81/2.00  --splitting_cvd_svl                     false
% 11.81/2.00  --splitting_nvd                         32
% 11.81/2.00  --sub_typing                            true
% 11.81/2.00  --prep_gs_sim                           true
% 11.81/2.00  --prep_unflatten                        true
% 11.81/2.00  --prep_res_sim                          true
% 11.81/2.00  --prep_upred                            true
% 11.81/2.00  --prep_sem_filter                       exhaustive
% 11.81/2.00  --prep_sem_filter_out                   false
% 11.81/2.00  --pred_elim                             true
% 11.81/2.00  --res_sim_input                         true
% 11.81/2.00  --eq_ax_congr_red                       true
% 11.81/2.00  --pure_diseq_elim                       true
% 11.81/2.00  --brand_transform                       false
% 11.81/2.00  --non_eq_to_eq                          false
% 11.81/2.00  --prep_def_merge                        true
% 11.81/2.00  --prep_def_merge_prop_impl              false
% 11.81/2.00  --prep_def_merge_mbd                    true
% 11.81/2.00  --prep_def_merge_tr_red                 false
% 11.81/2.00  --prep_def_merge_tr_cl                  false
% 11.81/2.00  --smt_preprocessing                     true
% 11.81/2.00  --smt_ac_axioms                         fast
% 11.81/2.00  --preprocessed_out                      false
% 11.81/2.00  --preprocessed_stats                    false
% 11.81/2.00  
% 11.81/2.00  ------ Abstraction refinement Options
% 11.81/2.00  
% 11.81/2.00  --abstr_ref                             []
% 11.81/2.00  --abstr_ref_prep                        false
% 11.81/2.00  --abstr_ref_until_sat                   false
% 11.81/2.00  --abstr_ref_sig_restrict                funpre
% 11.81/2.00  --abstr_ref_af_restrict_to_split_sk     false
% 11.81/2.00  --abstr_ref_under                       []
% 11.81/2.00  
% 11.81/2.00  ------ SAT Options
% 11.81/2.00  
% 11.81/2.00  --sat_mode                              false
% 11.81/2.00  --sat_fm_restart_options                ""
% 11.81/2.00  --sat_gr_def                            false
% 11.81/2.00  --sat_epr_types                         true
% 11.81/2.00  --sat_non_cyclic_types                  false
% 11.81/2.00  --sat_finite_models                     false
% 11.81/2.00  --sat_fm_lemmas                         false
% 11.81/2.00  --sat_fm_prep                           false
% 11.81/2.00  --sat_fm_uc_incr                        true
% 11.81/2.00  --sat_out_model                         small
% 11.81/2.00  --sat_out_clauses                       false
% 11.81/2.00  
% 11.81/2.00  ------ QBF Options
% 11.81/2.00  
% 11.81/2.00  --qbf_mode                              false
% 11.81/2.00  --qbf_elim_univ                         false
% 11.81/2.00  --qbf_dom_inst                          none
% 11.81/2.00  --qbf_dom_pre_inst                      false
% 11.81/2.00  --qbf_sk_in                             false
% 11.81/2.00  --qbf_pred_elim                         true
% 11.81/2.00  --qbf_split                             512
% 11.81/2.00  
% 11.81/2.00  ------ BMC1 Options
% 11.81/2.00  
% 11.81/2.00  --bmc1_incremental                      false
% 11.81/2.00  --bmc1_axioms                           reachable_all
% 11.81/2.00  --bmc1_min_bound                        0
% 11.81/2.00  --bmc1_max_bound                        -1
% 11.81/2.00  --bmc1_max_bound_default                -1
% 11.81/2.00  --bmc1_symbol_reachability              true
% 11.81/2.00  --bmc1_property_lemmas                  false
% 11.81/2.00  --bmc1_k_induction                      false
% 11.81/2.00  --bmc1_non_equiv_states                 false
% 11.81/2.00  --bmc1_deadlock                         false
% 11.81/2.00  --bmc1_ucm                              false
% 11.81/2.00  --bmc1_add_unsat_core                   none
% 11.81/2.00  --bmc1_unsat_core_children              false
% 11.81/2.00  --bmc1_unsat_core_extrapolate_axioms    false
% 11.81/2.00  --bmc1_out_stat                         full
% 11.81/2.00  --bmc1_ground_init                      false
% 11.81/2.00  --bmc1_pre_inst_next_state              false
% 11.81/2.00  --bmc1_pre_inst_state                   false
% 11.81/2.00  --bmc1_pre_inst_reach_state             false
% 11.81/2.00  --bmc1_out_unsat_core                   false
% 11.81/2.00  --bmc1_aig_witness_out                  false
% 11.81/2.00  --bmc1_verbose                          false
% 11.81/2.00  --bmc1_dump_clauses_tptp                false
% 11.81/2.00  --bmc1_dump_unsat_core_tptp             false
% 11.81/2.00  --bmc1_dump_file                        -
% 11.81/2.00  --bmc1_ucm_expand_uc_limit              128
% 11.81/2.00  --bmc1_ucm_n_expand_iterations          6
% 11.81/2.00  --bmc1_ucm_extend_mode                  1
% 11.81/2.00  --bmc1_ucm_init_mode                    2
% 11.81/2.00  --bmc1_ucm_cone_mode                    none
% 11.81/2.00  --bmc1_ucm_reduced_relation_type        0
% 11.81/2.00  --bmc1_ucm_relax_model                  4
% 11.81/2.00  --bmc1_ucm_full_tr_after_sat            true
% 11.81/2.00  --bmc1_ucm_expand_neg_assumptions       false
% 11.81/2.00  --bmc1_ucm_layered_model                none
% 11.81/2.00  --bmc1_ucm_max_lemma_size               10
% 11.81/2.00  
% 11.81/2.00  ------ AIG Options
% 11.81/2.00  
% 11.81/2.00  --aig_mode                              false
% 11.81/2.00  
% 11.81/2.00  ------ Instantiation Options
% 11.81/2.00  
% 11.81/2.00  --instantiation_flag                    true
% 11.81/2.00  --inst_sos_flag                         true
% 11.81/2.00  --inst_sos_phase                        true
% 11.81/2.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.81/2.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.81/2.00  --inst_lit_sel_side                     none
% 11.81/2.00  --inst_solver_per_active                1400
% 11.81/2.00  --inst_solver_calls_frac                1.
% 11.81/2.00  --inst_passive_queue_type               priority_queues
% 11.81/2.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.81/2.00  --inst_passive_queues_freq              [25;2]
% 11.81/2.00  --inst_dismatching                      true
% 11.81/2.00  --inst_eager_unprocessed_to_passive     true
% 11.81/2.00  --inst_prop_sim_given                   true
% 11.81/2.00  --inst_prop_sim_new                     false
% 11.81/2.00  --inst_subs_new                         false
% 11.81/2.00  --inst_eq_res_simp                      false
% 11.81/2.00  --inst_subs_given                       false
% 11.81/2.00  --inst_orphan_elimination               true
% 11.81/2.00  --inst_learning_loop_flag               true
% 11.81/2.00  --inst_learning_start                   3000
% 11.81/2.00  --inst_learning_factor                  2
% 11.81/2.00  --inst_start_prop_sim_after_learn       3
% 11.81/2.00  --inst_sel_renew                        solver
% 11.81/2.00  --inst_lit_activity_flag                true
% 11.81/2.00  --inst_restr_to_given                   false
% 11.81/2.00  --inst_activity_threshold               500
% 11.81/2.00  --inst_out_proof                        true
% 11.81/2.00  
% 11.81/2.00  ------ Resolution Options
% 11.81/2.00  
% 11.81/2.00  --resolution_flag                       false
% 11.81/2.00  --res_lit_sel                           adaptive
% 11.81/2.00  --res_lit_sel_side                      none
% 11.81/2.00  --res_ordering                          kbo
% 11.81/2.00  --res_to_prop_solver                    active
% 11.81/2.00  --res_prop_simpl_new                    false
% 11.81/2.00  --res_prop_simpl_given                  true
% 11.81/2.00  --res_passive_queue_type                priority_queues
% 11.81/2.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.81/2.00  --res_passive_queues_freq               [15;5]
% 11.81/2.00  --res_forward_subs                      full
% 11.81/2.00  --res_backward_subs                     full
% 11.81/2.00  --res_forward_subs_resolution           true
% 11.81/2.00  --res_backward_subs_resolution          true
% 11.81/2.00  --res_orphan_elimination                true
% 11.81/2.00  --res_time_limit                        2.
% 11.81/2.00  --res_out_proof                         true
% 11.81/2.00  
% 11.81/2.00  ------ Superposition Options
% 11.81/2.00  
% 11.81/2.00  --superposition_flag                    true
% 11.81/2.00  --sup_passive_queue_type                priority_queues
% 11.81/2.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.81/2.00  --sup_passive_queues_freq               [8;1;4]
% 11.81/2.00  --demod_completeness_check              fast
% 11.81/2.00  --demod_use_ground                      true
% 11.81/2.00  --sup_to_prop_solver                    passive
% 11.81/2.00  --sup_prop_simpl_new                    true
% 11.81/2.00  --sup_prop_simpl_given                  true
% 11.81/2.00  --sup_fun_splitting                     true
% 11.81/2.00  --sup_smt_interval                      50000
% 11.81/2.00  
% 11.81/2.00  ------ Superposition Simplification Setup
% 11.81/2.00  
% 11.81/2.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.81/2.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.81/2.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.81/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.81/2.00  --sup_full_triv                         [TrivRules;PropSubs]
% 11.81/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.81/2.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.81/2.00  --sup_immed_triv                        [TrivRules]
% 11.81/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.81/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.81/2.00  --sup_immed_bw_main                     []
% 11.81/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.81/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 11.81/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.81/2.00  --sup_input_bw                          []
% 11.81/2.00  
% 11.81/2.00  ------ Combination Options
% 11.81/2.00  
% 11.81/2.00  --comb_res_mult                         3
% 11.81/2.00  --comb_sup_mult                         2
% 11.81/2.00  --comb_inst_mult                        10
% 11.81/2.00  
% 11.81/2.00  ------ Debug Options
% 11.81/2.00  
% 11.81/2.00  --dbg_backtrace                         false
% 11.81/2.00  --dbg_dump_prop_clauses                 false
% 11.81/2.00  --dbg_dump_prop_clauses_file            -
% 11.81/2.00  --dbg_out_stat                          false
% 11.81/2.00  
% 11.81/2.00  
% 11.81/2.00  
% 11.81/2.00  
% 11.81/2.00  ------ Proving...
% 11.81/2.00  
% 11.81/2.00  
% 11.81/2.00  % SZS status Theorem for theBenchmark.p
% 11.81/2.00  
% 11.81/2.00  % SZS output start CNFRefutation for theBenchmark.p
% 11.81/2.00  
% 11.81/2.00  fof(f12,conjecture,(
% 11.81/2.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_tops_1(X1,X0) => (v4_tops_1(k2_pre_topc(X0,X1),X0) & v4_tops_1(k1_tops_1(X0,X1),X0)))))),
% 11.81/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.81/2.00  
% 11.81/2.00  fof(f13,negated_conjecture,(
% 11.81/2.00    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_tops_1(X1,X0) => (v4_tops_1(k2_pre_topc(X0,X1),X0) & v4_tops_1(k1_tops_1(X0,X1),X0)))))),
% 11.81/2.00    inference(negated_conjecture,[],[f12])).
% 11.81/2.00  
% 11.81/2.00  fof(f30,plain,(
% 11.81/2.00    ? [X0] : (? [X1] : (((~v4_tops_1(k2_pre_topc(X0,X1),X0) | ~v4_tops_1(k1_tops_1(X0,X1),X0)) & v4_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 11.81/2.00    inference(ennf_transformation,[],[f13])).
% 11.81/2.00  
% 11.81/2.00  fof(f31,plain,(
% 11.81/2.00    ? [X0] : (? [X1] : ((~v4_tops_1(k2_pre_topc(X0,X1),X0) | ~v4_tops_1(k1_tops_1(X0,X1),X0)) & v4_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 11.81/2.00    inference(flattening,[],[f30])).
% 11.81/2.00  
% 11.81/2.00  fof(f38,plain,(
% 11.81/2.00    ( ! [X0] : (? [X1] : ((~v4_tops_1(k2_pre_topc(X0,X1),X0) | ~v4_tops_1(k1_tops_1(X0,X1),X0)) & v4_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((~v4_tops_1(k2_pre_topc(X0,sK1),X0) | ~v4_tops_1(k1_tops_1(X0,sK1),X0)) & v4_tops_1(sK1,X0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 11.81/2.00    introduced(choice_axiom,[])).
% 11.81/2.00  
% 11.81/2.00  fof(f37,plain,(
% 11.81/2.00    ? [X0] : (? [X1] : ((~v4_tops_1(k2_pre_topc(X0,X1),X0) | ~v4_tops_1(k1_tops_1(X0,X1),X0)) & v4_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((~v4_tops_1(k2_pre_topc(sK0,X1),sK0) | ~v4_tops_1(k1_tops_1(sK0,X1),sK0)) & v4_tops_1(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 11.81/2.00    introduced(choice_axiom,[])).
% 11.81/2.00  
% 11.81/2.00  fof(f39,plain,(
% 11.81/2.00    ((~v4_tops_1(k2_pre_topc(sK0,sK1),sK0) | ~v4_tops_1(k1_tops_1(sK0,sK1),sK0)) & v4_tops_1(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 11.81/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f31,f38,f37])).
% 11.81/2.00  
% 11.81/2.00  fof(f57,plain,(
% 11.81/2.00    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 11.81/2.00    inference(cnf_transformation,[],[f39])).
% 11.81/2.00  
% 11.81/2.00  fof(f4,axiom,(
% 11.81/2.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 11.81/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.81/2.00  
% 11.81/2.00  fof(f16,plain,(
% 11.81/2.00    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 11.81/2.00    inference(ennf_transformation,[],[f4])).
% 11.81/2.00  
% 11.81/2.00  fof(f17,plain,(
% 11.81/2.00    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 11.81/2.00    inference(flattening,[],[f16])).
% 11.81/2.00  
% 11.81/2.00  fof(f46,plain,(
% 11.81/2.00    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.81/2.00    inference(cnf_transformation,[],[f17])).
% 11.81/2.00  
% 11.81/2.00  fof(f56,plain,(
% 11.81/2.00    l1_pre_topc(sK0)),
% 11.81/2.00    inference(cnf_transformation,[],[f39])).
% 11.81/2.00  
% 11.81/2.00  fof(f9,axiom,(
% 11.81/2.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)))),
% 11.81/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.81/2.00  
% 11.81/2.00  fof(f25,plain,(
% 11.81/2.00    ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 11.81/2.00    inference(ennf_transformation,[],[f9])).
% 11.81/2.00  
% 11.81/2.00  fof(f26,plain,(
% 11.81/2.00    ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 11.81/2.00    inference(flattening,[],[f25])).
% 11.81/2.00  
% 11.81/2.00  fof(f53,plain,(
% 11.81/2.00    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.81/2.00    inference(cnf_transformation,[],[f26])).
% 11.81/2.00  
% 11.81/2.00  fof(f11,axiom,(
% 11.81/2.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 11.81/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.81/2.00  
% 11.81/2.00  fof(f28,plain,(
% 11.81/2.00    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.81/2.00    inference(ennf_transformation,[],[f11])).
% 11.81/2.00  
% 11.81/2.00  fof(f29,plain,(
% 11.81/2.00    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.81/2.00    inference(flattening,[],[f28])).
% 11.81/2.00  
% 11.81/2.00  fof(f55,plain,(
% 11.81/2.00    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.81/2.00    inference(cnf_transformation,[],[f29])).
% 11.81/2.00  
% 11.81/2.00  fof(f10,axiom,(
% 11.81/2.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 11.81/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.81/2.00  
% 11.81/2.00  fof(f27,plain,(
% 11.81/2.00    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.81/2.00    inference(ennf_transformation,[],[f10])).
% 11.81/2.00  
% 11.81/2.00  fof(f54,plain,(
% 11.81/2.00    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.81/2.00    inference(cnf_transformation,[],[f27])).
% 11.81/2.00  
% 11.81/2.00  fof(f2,axiom,(
% 11.81/2.00    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 11.81/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.81/2.00  
% 11.81/2.00  fof(f14,plain,(
% 11.81/2.00    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 11.81/2.00    inference(ennf_transformation,[],[f2])).
% 11.81/2.00  
% 11.81/2.00  fof(f15,plain,(
% 11.81/2.00    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 11.81/2.00    inference(flattening,[],[f14])).
% 11.81/2.00  
% 11.81/2.00  fof(f43,plain,(
% 11.81/2.00    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 11.81/2.00    inference(cnf_transformation,[],[f15])).
% 11.81/2.00  
% 11.81/2.00  fof(f1,axiom,(
% 11.81/2.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 11.81/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.81/2.00  
% 11.81/2.00  fof(f32,plain,(
% 11.81/2.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.81/2.00    inference(nnf_transformation,[],[f1])).
% 11.81/2.00  
% 11.81/2.00  fof(f33,plain,(
% 11.81/2.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.81/2.00    inference(flattening,[],[f32])).
% 11.81/2.00  
% 11.81/2.00  fof(f42,plain,(
% 11.81/2.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 11.81/2.00    inference(cnf_transformation,[],[f33])).
% 11.81/2.00  
% 11.81/2.00  fof(f3,axiom,(
% 11.81/2.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 11.81/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.81/2.00  
% 11.81/2.00  fof(f34,plain,(
% 11.81/2.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 11.81/2.00    inference(nnf_transformation,[],[f3])).
% 11.81/2.00  
% 11.81/2.00  fof(f44,plain,(
% 11.81/2.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 11.81/2.00    inference(cnf_transformation,[],[f34])).
% 11.81/2.00  
% 11.81/2.00  fof(f41,plain,(
% 11.81/2.00    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 11.81/2.00    inference(cnf_transformation,[],[f33])).
% 11.81/2.00  
% 11.81/2.00  fof(f60,plain,(
% 11.81/2.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 11.81/2.00    inference(equality_resolution,[],[f41])).
% 11.81/2.00  
% 11.81/2.00  fof(f45,plain,(
% 11.81/2.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 11.81/2.00    inference(cnf_transformation,[],[f34])).
% 11.81/2.00  
% 11.81/2.00  fof(f58,plain,(
% 11.81/2.00    v4_tops_1(sK1,sK0)),
% 11.81/2.00    inference(cnf_transformation,[],[f39])).
% 11.81/2.00  
% 11.81/2.00  fof(f8,axiom,(
% 11.81/2.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 11.81/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.81/2.00  
% 11.81/2.00  fof(f23,plain,(
% 11.81/2.00    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 11.81/2.00    inference(ennf_transformation,[],[f8])).
% 11.81/2.00  
% 11.81/2.00  fof(f24,plain,(
% 11.81/2.00    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 11.81/2.00    inference(flattening,[],[f23])).
% 11.81/2.00  
% 11.81/2.00  fof(f52,plain,(
% 11.81/2.00    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.81/2.00    inference(cnf_transformation,[],[f24])).
% 11.81/2.00  
% 11.81/2.00  fof(f7,axiom,(
% 11.81/2.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_tops_1(X1,X0) <=> (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)))))),
% 11.81/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.81/2.00  
% 11.81/2.00  fof(f22,plain,(
% 11.81/2.00    ! [X0] : (! [X1] : ((v4_tops_1(X1,X0) <=> (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.81/2.00    inference(ennf_transformation,[],[f7])).
% 11.81/2.00  
% 11.81/2.00  fof(f35,plain,(
% 11.81/2.00    ! [X0] : (! [X1] : (((v4_tops_1(X1,X0) | (~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1))) & ((r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) | ~v4_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.81/2.00    inference(nnf_transformation,[],[f22])).
% 11.81/2.00  
% 11.81/2.00  fof(f36,plain,(
% 11.81/2.00    ! [X0] : (! [X1] : (((v4_tops_1(X1,X0) | ~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) & ((r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) | ~v4_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.81/2.00    inference(flattening,[],[f35])).
% 11.81/2.00  
% 11.81/2.00  fof(f50,plain,(
% 11.81/2.00    ( ! [X0,X1] : (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~v4_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.81/2.00    inference(cnf_transformation,[],[f36])).
% 11.81/2.00  
% 11.81/2.00  fof(f6,axiom,(
% 11.81/2.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))))))),
% 11.81/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.81/2.00  
% 11.81/2.00  fof(f20,plain,(
% 11.81/2.00    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.81/2.00    inference(ennf_transformation,[],[f6])).
% 11.81/2.00  
% 11.81/2.00  fof(f21,plain,(
% 11.81/2.00    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.81/2.00    inference(flattening,[],[f20])).
% 11.81/2.00  
% 11.81/2.00  fof(f48,plain,(
% 11.81/2.00    ( ! [X2,X0,X1] : (r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.81/2.00    inference(cnf_transformation,[],[f21])).
% 11.81/2.00  
% 11.81/2.00  fof(f49,plain,(
% 11.81/2.00    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) | ~v4_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.81/2.00    inference(cnf_transformation,[],[f36])).
% 11.81/2.00  
% 11.81/2.00  fof(f51,plain,(
% 11.81/2.00    ( ! [X0,X1] : (v4_tops_1(X1,X0) | ~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.81/2.00    inference(cnf_transformation,[],[f36])).
% 11.81/2.00  
% 11.81/2.00  fof(f5,axiom,(
% 11.81/2.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)))),
% 11.81/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.81/2.00  
% 11.81/2.00  fof(f18,plain,(
% 11.81/2.00    ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 11.81/2.00    inference(ennf_transformation,[],[f5])).
% 11.81/2.00  
% 11.81/2.00  fof(f19,plain,(
% 11.81/2.00    ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 11.81/2.00    inference(flattening,[],[f18])).
% 11.81/2.00  
% 11.81/2.00  fof(f47,plain,(
% 11.81/2.00    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.81/2.00    inference(cnf_transformation,[],[f19])).
% 11.81/2.00  
% 11.81/2.00  fof(f59,plain,(
% 11.81/2.00    ~v4_tops_1(k2_pre_topc(sK0,sK1),sK0) | ~v4_tops_1(k1_tops_1(sK0,sK1),sK0)),
% 11.81/2.00    inference(cnf_transformation,[],[f39])).
% 11.81/2.00  
% 11.81/2.00  cnf(c_600,plain,
% 11.81/2.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 11.81/2.00      theory(equality) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_4994,plain,
% 11.81/2.00      ( ~ r1_tarski(X0,X1)
% 11.81/2.00      | r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))
% 11.81/2.00      | k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) != X1
% 11.81/2.00      | k2_pre_topc(sK0,sK1) != X0 ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_600]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_17242,plain,
% 11.81/2.00      ( ~ r1_tarski(k2_pre_topc(sK0,sK1),X0)
% 11.81/2.00      | r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))
% 11.81/2.00      | k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) != X0
% 11.81/2.00      | k2_pre_topc(sK0,sK1) != k2_pre_topc(sK0,sK1) ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_4994]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_39153,plain,
% 11.81/2.00      ( r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))
% 11.81/2.00      | ~ r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))))
% 11.81/2.00      | k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) != k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))
% 11.81/2.00      | k2_pre_topc(sK0,sK1) != k2_pre_topc(sK0,sK1) ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_17242]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_18,negated_conjecture,
% 11.81/2.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 11.81/2.00      inference(cnf_transformation,[],[f57]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_1026,plain,
% 11.81/2.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 11.81/2.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_6,plain,
% 11.81/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.81/2.00      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 11.81/2.00      | ~ l1_pre_topc(X1) ),
% 11.81/2.00      inference(cnf_transformation,[],[f46]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_19,negated_conjecture,
% 11.81/2.00      ( l1_pre_topc(sK0) ),
% 11.81/2.00      inference(cnf_transformation,[],[f56]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_387,plain,
% 11.81/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.81/2.00      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 11.81/2.00      | sK0 != X1 ),
% 11.81/2.00      inference(resolution_lifted,[status(thm)],[c_6,c_19]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_388,plain,
% 11.81/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.81/2.00      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 11.81/2.00      inference(unflattening,[status(thm)],[c_387]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_1016,plain,
% 11.81/2.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.81/2.00      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 11.81/2.00      inference(predicate_to_equality,[status(thm)],[c_388]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_13,plain,
% 11.81/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.81/2.00      | ~ l1_pre_topc(X1)
% 11.81/2.00      | k1_tops_1(X1,k1_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
% 11.81/2.00      inference(cnf_transformation,[],[f53]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_285,plain,
% 11.81/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.81/2.00      | k1_tops_1(X1,k1_tops_1(X1,X0)) = k1_tops_1(X1,X0)
% 11.81/2.00      | sK0 != X1 ),
% 11.81/2.00      inference(resolution_lifted,[status(thm)],[c_13,c_19]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_286,plain,
% 11.81/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.81/2.00      | k1_tops_1(sK0,k1_tops_1(sK0,X0)) = k1_tops_1(sK0,X0) ),
% 11.81/2.00      inference(unflattening,[status(thm)],[c_285]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_1023,plain,
% 11.81/2.00      ( k1_tops_1(sK0,k1_tops_1(sK0,X0)) = k1_tops_1(sK0,X0)
% 11.81/2.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 11.81/2.00      inference(predicate_to_equality,[status(thm)],[c_286]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_2086,plain,
% 11.81/2.00      ( k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,X0))) = k1_tops_1(sK0,k2_pre_topc(sK0,X0))
% 11.81/2.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 11.81/2.00      inference(superposition,[status(thm)],[c_1016,c_1023]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_4394,plain,
% 11.81/2.00      ( k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) = k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) ),
% 11.81/2.00      inference(superposition,[status(thm)],[c_1026,c_2086]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_15,plain,
% 11.81/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.81/2.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 11.81/2.00      | ~ r1_tarski(X0,X2)
% 11.81/2.00      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 11.81/2.00      | ~ l1_pre_topc(X1) ),
% 11.81/2.00      inference(cnf_transformation,[],[f55]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_255,plain,
% 11.81/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.81/2.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 11.81/2.00      | ~ r1_tarski(X0,X2)
% 11.81/2.00      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 11.81/2.00      | sK0 != X1 ),
% 11.81/2.00      inference(resolution_lifted,[status(thm)],[c_15,c_19]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_256,plain,
% 11.81/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.81/2.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.81/2.00      | ~ r1_tarski(X1,X0)
% 11.81/2.00      | r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,X0)) ),
% 11.81/2.00      inference(unflattening,[status(thm)],[c_255]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_1025,plain,
% 11.81/2.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.81/2.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.81/2.00      | r1_tarski(X1,X0) != iProver_top
% 11.81/2.00      | r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,X0)) = iProver_top ),
% 11.81/2.00      inference(predicate_to_equality,[status(thm)],[c_256]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_14,plain,
% 11.81/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.81/2.00      | r1_tarski(k1_tops_1(X1,X0),X0)
% 11.81/2.00      | ~ l1_pre_topc(X1) ),
% 11.81/2.00      inference(cnf_transformation,[],[f54]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_273,plain,
% 11.81/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.81/2.00      | r1_tarski(k1_tops_1(X1,X0),X0)
% 11.81/2.00      | sK0 != X1 ),
% 11.81/2.00      inference(resolution_lifted,[status(thm)],[c_14,c_19]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_274,plain,
% 11.81/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.81/2.00      | r1_tarski(k1_tops_1(sK0,X0),X0) ),
% 11.81/2.00      inference(unflattening,[status(thm)],[c_273]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_1024,plain,
% 11.81/2.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.81/2.00      | r1_tarski(k1_tops_1(sK0,X0),X0) = iProver_top ),
% 11.81/2.00      inference(predicate_to_equality,[status(thm)],[c_274]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_1198,plain,
% 11.81/2.00      ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
% 11.81/2.00      inference(superposition,[status(thm)],[c_1026,c_1024]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_3,plain,
% 11.81/2.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 11.81/2.00      inference(cnf_transformation,[],[f43]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_1031,plain,
% 11.81/2.00      ( r1_tarski(X0,X1) != iProver_top
% 11.81/2.00      | r1_tarski(X1,X2) != iProver_top
% 11.81/2.00      | r1_tarski(X0,X2) = iProver_top ),
% 11.81/2.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_2785,plain,
% 11.81/2.00      ( r1_tarski(k1_tops_1(sK0,sK1),X0) = iProver_top
% 11.81/2.00      | r1_tarski(sK1,X0) != iProver_top ),
% 11.81/2.00      inference(superposition,[status(thm)],[c_1198,c_1031]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_0,plain,
% 11.81/2.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 11.81/2.00      inference(cnf_transformation,[],[f42]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_1033,plain,
% 11.81/2.00      ( X0 = X1
% 11.81/2.00      | r1_tarski(X0,X1) != iProver_top
% 11.81/2.00      | r1_tarski(X1,X0) != iProver_top ),
% 11.81/2.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_3131,plain,
% 11.81/2.00      ( k1_tops_1(sK0,sK1) = X0
% 11.81/2.00      | r1_tarski(X0,k1_tops_1(sK0,sK1)) != iProver_top
% 11.81/2.00      | r1_tarski(sK1,X0) != iProver_top ),
% 11.81/2.00      inference(superposition,[status(thm)],[c_2785,c_1033]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_4289,plain,
% 11.81/2.00      ( k1_tops_1(sK0,X0) = k1_tops_1(sK0,sK1)
% 11.81/2.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.81/2.00      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.81/2.00      | r1_tarski(X0,sK1) != iProver_top
% 11.81/2.00      | r1_tarski(sK1,k1_tops_1(sK0,X0)) != iProver_top ),
% 11.81/2.00      inference(superposition,[status(thm)],[c_1025,c_3131]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_5,plain,
% 11.81/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 11.81/2.00      inference(cnf_transformation,[],[f44]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_1029,plain,
% 11.81/2.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 11.81/2.00      | r1_tarski(X0,X1) = iProver_top ),
% 11.81/2.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_1763,plain,
% 11.81/2.00      ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
% 11.81/2.00      inference(superposition,[status(thm)],[c_1026,c_1029]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_1,plain,
% 11.81/2.00      ( r1_tarski(X0,X0) ),
% 11.81/2.00      inference(cnf_transformation,[],[f60]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_1032,plain,
% 11.81/2.00      ( r1_tarski(X0,X0) = iProver_top ),
% 11.81/2.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_4,plain,
% 11.81/2.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 11.81/2.00      inference(cnf_transformation,[],[f45]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_1030,plain,
% 11.81/2.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 11.81/2.00      | r1_tarski(X0,X1) != iProver_top ),
% 11.81/2.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_2781,plain,
% 11.81/2.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.81/2.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.81/2.00      | r1_tarski(X1,X0) != iProver_top
% 11.81/2.00      | r1_tarski(k1_tops_1(sK0,X0),X2) != iProver_top
% 11.81/2.00      | r1_tarski(k1_tops_1(sK0,X1),X2) = iProver_top ),
% 11.81/2.00      inference(superposition,[status(thm)],[c_1025,c_1031]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_13873,plain,
% 11.81/2.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.81/2.00      | r1_tarski(X0,sK1) != iProver_top
% 11.81/2.00      | r1_tarski(k1_tops_1(sK0,X0),X1) = iProver_top
% 11.81/2.00      | r1_tarski(k1_tops_1(sK0,sK1),X1) != iProver_top ),
% 11.81/2.00      inference(superposition,[status(thm)],[c_1026,c_2781]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_14167,plain,
% 11.81/2.00      ( r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
% 11.81/2.00      | r1_tarski(X0,sK1) != iProver_top
% 11.81/2.00      | r1_tarski(k1_tops_1(sK0,X0),X1) = iProver_top
% 11.81/2.00      | r1_tarski(k1_tops_1(sK0,sK1),X1) != iProver_top ),
% 11.81/2.00      inference(superposition,[status(thm)],[c_1030,c_13873]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_14179,plain,
% 11.81/2.00      ( r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
% 11.81/2.00      | r1_tarski(X0,sK1) != iProver_top
% 11.81/2.00      | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK1)) = iProver_top ),
% 11.81/2.00      inference(superposition,[status(thm)],[c_1032,c_14167]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_14753,plain,
% 11.81/2.00      ( k1_tops_1(sK0,X0) = k1_tops_1(sK0,sK1)
% 11.81/2.00      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
% 11.81/2.00      | r1_tarski(X0,sK1) != iProver_top
% 11.81/2.00      | r1_tarski(sK1,k1_tops_1(sK0,X0)) != iProver_top ),
% 11.81/2.00      inference(superposition,[status(thm)],[c_14179,c_3131]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_1269,plain,
% 11.81/2.00      ( ~ r1_tarski(X0,X1)
% 11.81/2.00      | ~ r1_tarski(X1,u1_struct_0(sK0))
% 11.81/2.00      | r1_tarski(X0,u1_struct_0(sK0)) ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_3]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_16869,plain,
% 11.81/2.00      ( r1_tarski(X0,u1_struct_0(sK0))
% 11.81/2.00      | ~ r1_tarski(X0,sK1)
% 11.81/2.00      | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_1269]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_16870,plain,
% 11.81/2.00      ( r1_tarski(X0,u1_struct_0(sK0)) = iProver_top
% 11.81/2.00      | r1_tarski(X0,sK1) != iProver_top
% 11.81/2.00      | r1_tarski(sK1,u1_struct_0(sK0)) != iProver_top ),
% 11.81/2.00      inference(predicate_to_equality,[status(thm)],[c_16869]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_37379,plain,
% 11.81/2.00      ( k1_tops_1(sK0,X0) = k1_tops_1(sK0,sK1)
% 11.81/2.00      | r1_tarski(X0,sK1) != iProver_top
% 11.81/2.00      | r1_tarski(sK1,k1_tops_1(sK0,X0)) != iProver_top ),
% 11.81/2.00      inference(global_propositional_subsumption,
% 11.81/2.00                [status(thm)],
% 11.81/2.00                [c_4289,c_1763,c_14753,c_16870]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_37386,plain,
% 11.81/2.00      ( k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) = k1_tops_1(sK0,sK1)
% 11.81/2.00      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK1) != iProver_top
% 11.81/2.00      | r1_tarski(sK1,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) != iProver_top ),
% 11.81/2.00      inference(superposition,[status(thm)],[c_4394,c_37379]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_37403,plain,
% 11.81/2.00      ( k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,sK1)
% 11.81/2.00      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK1) != iProver_top
% 11.81/2.00      | r1_tarski(sK1,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) != iProver_top ),
% 11.81/2.00      inference(demodulation,[status(thm)],[c_37386,c_4394]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_17,negated_conjecture,
% 11.81/2.00      ( v4_tops_1(sK1,sK0) ),
% 11.81/2.00      inference(cnf_transformation,[],[f58]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_12,plain,
% 11.81/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.81/2.00      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 11.81/2.00      | ~ l1_pre_topc(X1) ),
% 11.81/2.00      inference(cnf_transformation,[],[f52]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_297,plain,
% 11.81/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.81/2.00      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 11.81/2.00      | sK0 != X1 ),
% 11.81/2.00      inference(resolution_lifted,[status(thm)],[c_12,c_19]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_298,plain,
% 11.81/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.81/2.00      | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 11.81/2.00      inference(unflattening,[status(thm)],[c_297]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_1070,plain,
% 11.81/2.00      ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 11.81/2.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_298]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_1083,plain,
% 11.81/2.00      ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 11.81/2.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_388]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_1088,plain,
% 11.81/2.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.81/2.00      | r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_274]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_10,plain,
% 11.81/2.00      ( ~ v4_tops_1(X0,X1)
% 11.81/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.81/2.00      | r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
% 11.81/2.00      | ~ l1_pre_topc(X1) ),
% 11.81/2.00      inference(cnf_transformation,[],[f50]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_324,plain,
% 11.81/2.00      ( ~ v4_tops_1(X0,X1)
% 11.81/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.81/2.00      | r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
% 11.81/2.00      | sK0 != X1 ),
% 11.81/2.00      inference(resolution_lifted,[status(thm)],[c_10,c_19]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_325,plain,
% 11.81/2.00      ( ~ v4_tops_1(X0,sK0)
% 11.81/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.81/2.00      | r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,X0))) ),
% 11.81/2.00      inference(unflattening,[status(thm)],[c_324]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_1109,plain,
% 11.81/2.00      ( ~ v4_tops_1(sK1,sK0)
% 11.81/2.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.81/2.00      | r1_tarski(sK1,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_325]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_1175,plain,
% 11.81/2.00      ( m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
% 11.81/2.00      | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_298]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_8,plain,
% 11.81/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.81/2.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 11.81/2.00      | ~ r1_tarski(X0,X2)
% 11.81/2.00      | r1_tarski(k2_pre_topc(X1,X0),k2_pre_topc(X1,X2))
% 11.81/2.00      | ~ l1_pre_topc(X1) ),
% 11.81/2.00      inference(cnf_transformation,[],[f48]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_357,plain,
% 11.81/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.81/2.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 11.81/2.00      | ~ r1_tarski(X0,X2)
% 11.81/2.00      | r1_tarski(k2_pre_topc(X1,X0),k2_pre_topc(X1,X2))
% 11.81/2.00      | sK0 != X1 ),
% 11.81/2.00      inference(resolution_lifted,[status(thm)],[c_8,c_19]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_358,plain,
% 11.81/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.81/2.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.81/2.00      | ~ r1_tarski(X1,X0)
% 11.81/2.00      | r1_tarski(k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X0)) ),
% 11.81/2.00      inference(unflattening,[status(thm)],[c_357]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_1125,plain,
% 11.81/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.81/2.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.81/2.00      | ~ r1_tarski(X0,sK1)
% 11.81/2.00      | r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,sK1)) ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_358]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_1222,plain,
% 11.81/2.00      ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 11.81/2.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.81/2.00      | ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
% 11.81/2.00      | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k2_pre_topc(sK0,sK1)) ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_1125]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_1782,plain,
% 11.81/2.00      ( ~ r1_tarski(X0,k2_pre_topc(sK0,sK1))
% 11.81/2.00      | ~ r1_tarski(sK1,X0)
% 11.81/2.00      | r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_3]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_3718,plain,
% 11.81/2.00      ( ~ r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k2_pre_topc(sK0,sK1))
% 11.81/2.00      | ~ r1_tarski(sK1,k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))
% 11.81/2.00      | r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_1782]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_14740,plain,
% 11.81/2.00      ( r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,sK1)) = iProver_top
% 11.81/2.00      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),u1_struct_0(sK0)) != iProver_top
% 11.81/2.00      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK1) != iProver_top ),
% 11.81/2.00      inference(superposition,[status(thm)],[c_4394,c_14179]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_21,plain,
% 11.81/2.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 11.81/2.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_22,plain,
% 11.81/2.00      ( v4_tops_1(sK1,sK0) = iProver_top ),
% 11.81/2.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_11,plain,
% 11.81/2.00      ( ~ v4_tops_1(X0,X1)
% 11.81/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.81/2.00      | r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
% 11.81/2.00      | ~ l1_pre_topc(X1) ),
% 11.81/2.00      inference(cnf_transformation,[],[f49]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_309,plain,
% 11.81/2.00      ( ~ v4_tops_1(X0,X1)
% 11.81/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.81/2.00      | r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
% 11.81/2.00      | sK0 != X1 ),
% 11.81/2.00      inference(resolution_lifted,[status(thm)],[c_11,c_19]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_310,plain,
% 11.81/2.00      ( ~ v4_tops_1(X0,sK0)
% 11.81/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.81/2.00      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),X0) ),
% 11.81/2.00      inference(unflattening,[status(thm)],[c_309]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_1103,plain,
% 11.81/2.00      ( ~ v4_tops_1(sK1,sK0)
% 11.81/2.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.81/2.00      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK1) ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_310]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_1104,plain,
% 11.81/2.00      ( v4_tops_1(sK1,sK0) != iProver_top
% 11.81/2.00      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.81/2.00      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK1) = iProver_top ),
% 11.81/2.00      inference(predicate_to_equality,[status(thm)],[c_1103]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_15108,plain,
% 11.81/2.00      ( r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),u1_struct_0(sK0)) != iProver_top
% 11.81/2.00      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,sK1)) = iProver_top ),
% 11.81/2.00      inference(global_propositional_subsumption,
% 11.81/2.00                [status(thm)],
% 11.81/2.00                [c_14740,c_21,c_22,c_1104]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_15109,plain,
% 11.81/2.00      ( r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,sK1)) = iProver_top
% 11.81/2.00      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),u1_struct_0(sK0)) != iProver_top ),
% 11.81/2.00      inference(renaming,[status(thm)],[c_15108]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_2311,plain,
% 11.81/2.00      ( k1_tops_1(sK0,X0) = k1_tops_1(sK0,X1)
% 11.81/2.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.81/2.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.81/2.00      | r1_tarski(X0,X1) != iProver_top
% 11.81/2.00      | r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,X0)) != iProver_top ),
% 11.81/2.00      inference(superposition,[status(thm)],[c_1025,c_1033]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_15115,plain,
% 11.81/2.00      ( k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,sK1)
% 11.81/2.00      | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.81/2.00      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.81/2.00      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),u1_struct_0(sK0)) != iProver_top
% 11.81/2.00      | r1_tarski(sK1,k2_pre_topc(sK0,sK1)) != iProver_top ),
% 11.81/2.00      inference(superposition,[status(thm)],[c_15109,c_2311]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_15122,plain,
% 11.81/2.00      ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 11.81/2.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.81/2.00      | ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),u1_struct_0(sK0))
% 11.81/2.00      | ~ r1_tarski(sK1,k2_pre_topc(sK0,sK1))
% 11.81/2.00      | k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
% 11.81/2.00      inference(predicate_to_equality_rev,[status(thm)],[c_15115]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_1261,plain,
% 11.81/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.81/2.00      | r1_tarski(X0,u1_struct_0(sK0)) ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_5]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_15148,plain,
% 11.81/2.00      ( ~ m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
% 11.81/2.00      | r1_tarski(k1_tops_1(sK0,X0),u1_struct_0(sK0)) ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_1261]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_24292,plain,
% 11.81/2.00      ( ~ m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
% 11.81/2.00      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),u1_struct_0(sK0)) ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_15148]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_38057,plain,
% 11.81/2.00      ( k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
% 11.81/2.00      inference(global_propositional_subsumption,
% 11.81/2.00                [status(thm)],
% 11.81/2.00                [c_37403,c_18,c_17,c_1070,c_1083,c_1088,c_1109,c_1175,
% 11.81/2.00                 c_1222,c_3718,c_15122,c_24292]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_9,plain,
% 11.81/2.00      ( v4_tops_1(X0,X1)
% 11.81/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.81/2.00      | ~ r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
% 11.81/2.00      | ~ r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
% 11.81/2.00      | ~ l1_pre_topc(X1) ),
% 11.81/2.00      inference(cnf_transformation,[],[f51]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_339,plain,
% 11.81/2.00      ( v4_tops_1(X0,X1)
% 11.81/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.81/2.00      | ~ r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
% 11.81/2.00      | ~ r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
% 11.81/2.00      | sK0 != X1 ),
% 11.81/2.00      inference(resolution_lifted,[status(thm)],[c_9,c_19]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_340,plain,
% 11.81/2.00      ( v4_tops_1(X0,sK0)
% 11.81/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.81/2.00      | ~ r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,X0)))
% 11.81/2.00      | ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),X0) ),
% 11.81/2.00      inference(unflattening,[status(thm)],[c_339]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_1019,plain,
% 11.81/2.00      ( v4_tops_1(X0,sK0) = iProver_top
% 11.81/2.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.81/2.00      | r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,X0))) != iProver_top
% 11.81/2.00      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),X0) != iProver_top ),
% 11.81/2.00      inference(predicate_to_equality,[status(thm)],[c_340]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_2591,plain,
% 11.81/2.00      ( v4_tops_1(k1_tops_1(sK0,X0),sK0) = iProver_top
% 11.81/2.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.81/2.00      | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.81/2.00      | m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,X0)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.81/2.00      | r1_tarski(k1_tops_1(sK0,X0),k2_pre_topc(sK0,k1_tops_1(sK0,k1_tops_1(sK0,X0)))) != iProver_top
% 11.81/2.00      | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,X0)),X0) != iProver_top ),
% 11.81/2.00      inference(superposition,[status(thm)],[c_1025,c_1019]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_299,plain,
% 11.81/2.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.81/2.00      | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 11.81/2.00      inference(predicate_to_equality,[status(thm)],[c_298]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_11380,plain,
% 11.81/2.00      ( ~ m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
% 11.81/2.00      | m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,X0)),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_388]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_11381,plain,
% 11.81/2.00      ( m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.81/2.00      | m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,X0)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 11.81/2.00      inference(predicate_to_equality,[status(thm)],[c_11380]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_11800,plain,
% 11.81/2.00      ( v4_tops_1(k1_tops_1(sK0,X0),sK0) = iProver_top
% 11.81/2.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.81/2.00      | r1_tarski(k1_tops_1(sK0,X0),k2_pre_topc(sK0,k1_tops_1(sK0,k1_tops_1(sK0,X0)))) != iProver_top
% 11.81/2.00      | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,X0)),X0) != iProver_top ),
% 11.81/2.00      inference(global_propositional_subsumption,
% 11.81/2.00                [status(thm)],
% 11.81/2.00                [c_2591,c_299,c_11381]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_38155,plain,
% 11.81/2.00      ( v4_tops_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK0) = iProver_top
% 11.81/2.00      | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.81/2.00      | r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,k1_tops_1(sK0,sK1)))) != iProver_top
% 11.81/2.00      | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))),k2_pre_topc(sK0,sK1)) != iProver_top ),
% 11.81/2.00      inference(superposition,[status(thm)],[c_38057,c_11800]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_2084,plain,
% 11.81/2.00      ( k1_tops_1(sK0,k1_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
% 11.81/2.00      inference(superposition,[status(thm)],[c_1026,c_1023]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_38194,plain,
% 11.81/2.00      ( v4_tops_1(k1_tops_1(sK0,sK1),sK0) = iProver_top
% 11.81/2.00      | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.81/2.00      | r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != iProver_top
% 11.81/2.00      | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k2_pre_topc(sK0,sK1)) != iProver_top ),
% 11.81/2.00      inference(light_normalisation,
% 11.81/2.00                [status(thm)],
% 11.81/2.00                [c_38155,c_2084,c_38057]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_599,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_9150,plain,
% 11.81/2.00      ( X0 != X1
% 11.81/2.00      | k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) != X1
% 11.81/2.00      | k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = X0 ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_599]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_22081,plain,
% 11.81/2.00      ( X0 != k2_pre_topc(sK0,k1_tops_1(sK0,sK1))
% 11.81/2.00      | k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = X0
% 11.81/2.00      | k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) != k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_9150]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_33165,plain,
% 11.81/2.00      ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) != k2_pre_topc(sK0,k1_tops_1(sK0,sK1))
% 11.81/2.00      | k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))
% 11.81/2.00      | k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_22081]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_8021,plain,
% 11.81/2.00      ( ~ r1_tarski(X0,k2_pre_topc(sK0,sK1))
% 11.81/2.00      | ~ r1_tarski(k2_pre_topc(sK0,sK1),X0)
% 11.81/2.00      | k2_pre_topc(sK0,sK1) = X0 ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_0]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_21001,plain,
% 11.81/2.00      ( ~ r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k2_pre_topc(sK0,sK1))
% 11.81/2.00      | ~ r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))
% 11.81/2.00      | k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_8021]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_10852,plain,
% 11.81/2.00      ( ~ r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,X1)))
% 11.81/2.00      | ~ r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,X1)),X0)
% 11.81/2.00      | k2_pre_topc(sK0,k1_tops_1(sK0,X1)) = X0 ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_0]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_19849,plain,
% 11.81/2.00      ( ~ r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))))
% 11.81/2.00      | k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) = k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_10852]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_598,plain,( X0 = X0 ),theory(equality) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_14502,plain,
% 11.81/2.00      ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_598]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_13706,plain,
% 11.81/2.00      ( k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,sK1) ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_598]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_4312,plain,
% 11.81/2.00      ( ~ r1_tarski(X0,X1)
% 11.81/2.00      | r1_tarski(X2,k2_pre_topc(sK0,k1_tops_1(sK0,X2)))
% 11.81/2.00      | X2 != X0
% 11.81/2.00      | k2_pre_topc(sK0,k1_tops_1(sK0,X2)) != X1 ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_600]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_10857,plain,
% 11.81/2.00      ( ~ r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,X1)))
% 11.81/2.00      | r1_tarski(X1,k2_pre_topc(sK0,k1_tops_1(sK0,X1)))
% 11.81/2.00      | X1 != X0
% 11.81/2.00      | k2_pre_topc(sK0,k1_tops_1(sK0,X1)) != k2_pre_topc(sK0,k1_tops_1(sK0,X1)) ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_4312]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_13408,plain,
% 11.81/2.00      ( ~ r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))))
% 11.81/2.00      | r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))))
% 11.81/2.00      | k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) != k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))
% 11.81/2.00      | k2_pre_topc(sK0,sK1) != k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_10857]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_13409,plain,
% 11.81/2.00      ( k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) != k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))
% 11.81/2.00      | k2_pre_topc(sK0,sK1) != k2_pre_topc(sK0,k1_tops_1(sK0,sK1))
% 11.81/2.00      | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))) != iProver_top
% 11.81/2.00      | r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))) = iProver_top ),
% 11.81/2.00      inference(predicate_to_equality,[status(thm)],[c_13408]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_1020,plain,
% 11.81/2.00      ( v4_tops_1(X0,sK0) != iProver_top
% 11.81/2.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.81/2.00      | r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,X0))) = iProver_top ),
% 11.81/2.00      inference(predicate_to_equality,[status(thm)],[c_325]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_2193,plain,
% 11.81/2.00      ( v4_tops_1(k1_tops_1(sK0,sK1),sK0) != iProver_top
% 11.81/2.00      | m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.81/2.00      | r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = iProver_top ),
% 11.81/2.00      inference(superposition,[status(thm)],[c_2084,c_1020]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_1071,plain,
% 11.81/2.00      ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 11.81/2.00      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 11.81/2.00      inference(predicate_to_equality,[status(thm)],[c_1070]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_6868,plain,
% 11.81/2.00      ( v4_tops_1(k1_tops_1(sK0,sK1),sK0) != iProver_top
% 11.81/2.00      | r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = iProver_top ),
% 11.81/2.00      inference(global_propositional_subsumption,
% 11.81/2.00                [status(thm)],
% 11.81/2.00                [c_2193,c_21,c_1071]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_6873,plain,
% 11.81/2.00      ( v4_tops_1(k1_tops_1(sK0,sK1),sK0) != iProver_top
% 11.81/2.00      | r1_tarski(k1_tops_1(sK0,sK1),X0) = iProver_top
% 11.81/2.00      | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),X0) != iProver_top ),
% 11.81/2.00      inference(superposition,[status(thm)],[c_6868,c_1031]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_1110,plain,
% 11.81/2.00      ( v4_tops_1(sK1,sK0) != iProver_top
% 11.81/2.00      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.81/2.00      | r1_tarski(sK1,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = iProver_top ),
% 11.81/2.00      inference(predicate_to_equality,[status(thm)],[c_1109]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_3710,plain,
% 11.81/2.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(sK1,X0) | r1_tarski(sK1,X1) ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_3]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_9630,plain,
% 11.81/2.00      ( ~ r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),X0)
% 11.81/2.00      | r1_tarski(sK1,X0)
% 11.81/2.00      | ~ r1_tarski(sK1,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_3710]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_9631,plain,
% 11.81/2.00      ( r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),X0) != iProver_top
% 11.81/2.00      | r1_tarski(sK1,X0) = iProver_top
% 11.81/2.00      | r1_tarski(sK1,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != iProver_top ),
% 11.81/2.00      inference(predicate_to_equality,[status(thm)],[c_9630]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_12816,plain,
% 11.81/2.00      ( r1_tarski(k1_tops_1(sK0,sK1),X0) = iProver_top
% 11.81/2.00      | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),X0) != iProver_top ),
% 11.81/2.00      inference(global_propositional_subsumption,
% 11.81/2.00                [status(thm)],
% 11.81/2.00                [c_6873,c_21,c_22,c_1110,c_2785,c_9631]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_12822,plain,
% 11.81/2.00      ( r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = iProver_top ),
% 11.81/2.00      inference(superposition,[status(thm)],[c_1032,c_12816]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_1432,plain,
% 11.81/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.81/2.00      | ~ m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
% 11.81/2.00      | ~ r1_tarski(X0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))
% 11.81/2.00      | r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))) ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_358]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_5257,plain,
% 11.81/2.00      ( ~ m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
% 11.81/2.00      | ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))
% 11.81/2.00      | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))) ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_1432]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_5254,plain,
% 11.81/2.00      ( ~ m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
% 11.81/2.00      | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 11.81/2.00      | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))
% 11.81/2.00      | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))) ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_1432]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_5255,plain,
% 11.81/2.00      ( m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.81/2.00      | m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.81/2.00      | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) != iProver_top
% 11.81/2.00      | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))) = iProver_top ),
% 11.81/2.00      inference(predicate_to_equality,[status(thm)],[c_5254]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_1290,plain,
% 11.81/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.81/2.00      | ~ m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
% 11.81/2.00      | ~ r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))
% 11.81/2.00      | r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))) ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_358]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_3726,plain,
% 11.81/2.00      ( ~ m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
% 11.81/2.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.81/2.00      | r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))))
% 11.81/2.00      | ~ r1_tarski(sK1,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_1290]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_3719,plain,
% 11.81/2.00      ( r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k2_pre_topc(sK0,sK1)) != iProver_top
% 11.81/2.00      | r1_tarski(sK1,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != iProver_top
% 11.81/2.00      | r1_tarski(sK1,k2_pre_topc(sK0,sK1)) = iProver_top ),
% 11.81/2.00      inference(predicate_to_equality,[status(thm)],[c_3718]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_7,plain,
% 11.81/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.81/2.00      | ~ l1_pre_topc(X1)
% 11.81/2.00      | k2_pre_topc(X1,k2_pre_topc(X1,X0)) = k2_pre_topc(X1,X0) ),
% 11.81/2.00      inference(cnf_transformation,[],[f47]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_375,plain,
% 11.81/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.81/2.00      | k2_pre_topc(X1,k2_pre_topc(X1,X0)) = k2_pre_topc(X1,X0)
% 11.81/2.00      | sK0 != X1 ),
% 11.81/2.00      inference(resolution_lifted,[status(thm)],[c_7,c_19]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_376,plain,
% 11.81/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.81/2.00      | k2_pre_topc(sK0,k2_pre_topc(sK0,X0)) = k2_pre_topc(sK0,X0) ),
% 11.81/2.00      inference(unflattening,[status(thm)],[c_375]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_1017,plain,
% 11.81/2.00      ( k2_pre_topc(sK0,k2_pre_topc(sK0,X0)) = k2_pre_topc(sK0,X0)
% 11.81/2.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 11.81/2.00      inference(predicate_to_equality,[status(thm)],[c_376]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_1461,plain,
% 11.81/2.00      ( k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 11.81/2.00      inference(superposition,[status(thm)],[c_1026,c_1017]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_2593,plain,
% 11.81/2.00      ( v4_tops_1(k2_pre_topc(sK0,sK1),sK0) = iProver_top
% 11.81/2.00      | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.81/2.00      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_pre_topc(sK0,sK1)) != iProver_top
% 11.81/2.00      | r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))) != iProver_top ),
% 11.81/2.00      inference(superposition,[status(thm)],[c_1461,c_1019]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_1170,plain,
% 11.81/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.81/2.00      | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 11.81/2.00      | ~ r1_tarski(X0,k2_pre_topc(sK0,sK1))
% 11.81/2.00      | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_256]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_2340,plain,
% 11.81/2.00      ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 11.81/2.00      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))
% 11.81/2.00      | ~ r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK1)) ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_1170]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_2334,plain,
% 11.81/2.00      ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 11.81/2.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.81/2.00      | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))
% 11.81/2.00      | ~ r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_1170]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_2335,plain,
% 11.81/2.00      ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.81/2.00      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.81/2.00      | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) = iProver_top
% 11.81/2.00      | r1_tarski(sK1,k2_pre_topc(sK0,sK1)) != iProver_top ),
% 11.81/2.00      inference(predicate_to_equality,[status(thm)],[c_2334]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_1469,plain,
% 11.81/2.00      ( r1_tarski(sK1,sK1) ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_1]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_1229,plain,
% 11.81/2.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.81/2.00      | r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK1))
% 11.81/2.00      | ~ r1_tarski(sK1,sK1) ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_1125]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_1223,plain,
% 11.81/2.00      ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.81/2.00      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.81/2.00      | r1_tarski(k1_tops_1(sK0,sK1),sK1) != iProver_top
% 11.81/2.00      | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k2_pre_topc(sK0,sK1)) = iProver_top ),
% 11.81/2.00      inference(predicate_to_equality,[status(thm)],[c_1222]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_1173,plain,
% 11.81/2.00      ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 11.81/2.00      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_pre_topc(sK0,sK1)) ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_274]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_1180,plain,
% 11.81/2.00      ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.81/2.00      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_pre_topc(sK0,sK1)) = iProver_top ),
% 11.81/2.00      inference(predicate_to_equality,[status(thm)],[c_1173]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_1176,plain,
% 11.81/2.00      ( m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 11.81/2.00      | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 11.81/2.00      inference(predicate_to_equality,[status(thm)],[c_1175]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_1135,plain,
% 11.81/2.00      ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 11.81/2.00      | k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_376]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_1138,plain,
% 11.81/2.00      ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 11.81/2.00      | m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 11.81/2.00      inference(instantiation,[status(thm)],[c_388]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_1089,plain,
% 11.81/2.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.81/2.00      | r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
% 11.81/2.00      inference(predicate_to_equality,[status(thm)],[c_1088]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_1084,plain,
% 11.81/2.00      ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 11.81/2.00      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 11.81/2.00      inference(predicate_to_equality,[status(thm)],[c_1083]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_16,negated_conjecture,
% 11.81/2.00      ( ~ v4_tops_1(k1_tops_1(sK0,sK1),sK0)
% 11.81/2.00      | ~ v4_tops_1(k2_pre_topc(sK0,sK1),sK0) ),
% 11.81/2.00      inference(cnf_transformation,[],[f59]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(c_23,plain,
% 11.81/2.00      ( v4_tops_1(k1_tops_1(sK0,sK1),sK0) != iProver_top
% 11.81/2.00      | v4_tops_1(k2_pre_topc(sK0,sK1),sK0) != iProver_top ),
% 11.81/2.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 11.81/2.00  
% 11.81/2.00  cnf(contradiction,plain,
% 11.81/2.00      ( $false ),
% 11.81/2.00      inference(minisat,
% 11.81/2.00                [status(thm)],
% 11.81/2.00                [c_39153,c_38194,c_33165,c_21001,c_19849,c_14502,c_13706,
% 11.81/2.00                 c_13409,c_12822,c_5257,c_5255,c_3726,c_3719,c_2593,
% 11.81/2.00                 c_2340,c_2335,c_1469,c_1229,c_1223,c_1222,c_1180,c_1176,
% 11.81/2.00                 c_1175,c_1135,c_1138,c_1110,c_1109,c_1089,c_1088,c_1084,
% 11.81/2.00                 c_1083,c_1071,c_1070,c_23,c_22,c_17,c_21,c_18]) ).
% 11.81/2.00  
% 11.81/2.00  
% 11.81/2.00  % SZS output end CNFRefutation for theBenchmark.p
% 11.81/2.00  
% 11.81/2.00  ------                               Statistics
% 11.81/2.00  
% 11.81/2.00  ------ General
% 11.81/2.00  
% 11.81/2.00  abstr_ref_over_cycles:                  0
% 11.81/2.00  abstr_ref_under_cycles:                 0
% 11.81/2.00  gc_basic_clause_elim:                   0
% 11.81/2.00  forced_gc_time:                         0
% 11.81/2.00  parsing_time:                           0.011
% 11.81/2.00  unif_index_cands_time:                  0.
% 11.81/2.00  unif_index_add_time:                    0.
% 11.81/2.00  orderings_time:                         0.
% 11.81/2.00  out_proof_time:                         0.031
% 11.81/2.00  total_time:                             1.334
% 11.81/2.00  num_of_symbols:                         41
% 11.81/2.00  num_of_terms:                           28307
% 11.81/2.00  
% 11.81/2.00  ------ Preprocessing
% 11.81/2.00  
% 11.81/2.00  num_of_splits:                          0
% 11.81/2.00  num_of_split_atoms:                     0
% 11.81/2.00  num_of_reused_defs:                     0
% 11.81/2.00  num_eq_ax_congr_red:                    0
% 11.81/2.00  num_of_sem_filtered_clauses:            1
% 11.81/2.00  num_of_subtypes:                        0
% 11.81/2.00  monotx_restored_types:                  0
% 11.81/2.00  sat_num_of_epr_types:                   0
% 11.81/2.00  sat_num_of_non_cyclic_types:            0
% 11.81/2.00  sat_guarded_non_collapsed_types:        0
% 11.81/2.00  num_pure_diseq_elim:                    0
% 11.81/2.00  simp_replaced_by:                       0
% 11.81/2.00  res_preprocessed:                       92
% 11.81/2.00  prep_upred:                             0
% 11.81/2.00  prep_unflattend:                        10
% 11.81/2.00  smt_new_axioms:                         0
% 11.81/2.00  pred_elim_cands:                        3
% 11.81/2.00  pred_elim:                              1
% 11.81/2.00  pred_elim_cl:                           1
% 11.81/2.00  pred_elim_cycles:                       3
% 11.81/2.00  merged_defs:                            8
% 11.81/2.00  merged_defs_ncl:                        0
% 11.81/2.00  bin_hyper_res:                          8
% 11.81/2.00  prep_cycles:                            4
% 11.81/2.00  pred_elim_time:                         0.003
% 11.81/2.00  splitting_time:                         0.
% 11.81/2.00  sem_filter_time:                        0.
% 11.81/2.00  monotx_time:                            0.001
% 11.81/2.00  subtype_inf_time:                       0.
% 11.81/2.00  
% 11.81/2.00  ------ Problem properties
% 11.81/2.00  
% 11.81/2.00  clauses:                                18
% 11.81/2.00  conjectures:                            3
% 11.81/2.00  epr:                                    4
% 11.81/2.00  horn:                                   18
% 11.81/2.00  ground:                                 3
% 11.81/2.00  unary:                                  3
% 11.81/2.00  binary:                                 8
% 11.81/2.00  lits:                                   43
% 11.81/2.00  lits_eq:                                3
% 11.81/2.00  fd_pure:                                0
% 11.81/2.00  fd_pseudo:                              0
% 11.81/2.00  fd_cond:                                0
% 11.81/2.00  fd_pseudo_cond:                         1
% 11.81/2.00  ac_symbols:                             0
% 11.81/2.00  
% 11.81/2.00  ------ Propositional Solver
% 11.81/2.00  
% 11.81/2.00  prop_solver_calls:                      32
% 11.81/2.00  prop_fast_solver_calls:                 1774
% 11.81/2.00  smt_solver_calls:                       0
% 11.81/2.00  smt_fast_solver_calls:                  0
% 11.81/2.00  prop_num_of_clauses:                    19491
% 11.81/2.00  prop_preprocess_simplified:             19914
% 11.81/2.00  prop_fo_subsumed:                       124
% 11.81/2.00  prop_solver_time:                       0.
% 11.81/2.00  smt_solver_time:                        0.
% 11.81/2.00  smt_fast_solver_time:                   0.
% 11.81/2.00  prop_fast_solver_time:                  0.
% 11.81/2.00  prop_unsat_core_time:                   0.002
% 11.81/2.00  
% 11.81/2.00  ------ QBF
% 11.81/2.00  
% 11.81/2.00  qbf_q_res:                              0
% 11.81/2.00  qbf_num_tautologies:                    0
% 11.81/2.00  qbf_prep_cycles:                        0
% 11.81/2.00  
% 11.81/2.00  ------ BMC1
% 11.81/2.00  
% 11.81/2.00  bmc1_current_bound:                     -1
% 11.81/2.00  bmc1_last_solved_bound:                 -1
% 11.81/2.00  bmc1_unsat_core_size:                   -1
% 11.81/2.00  bmc1_unsat_core_parents_size:           -1
% 11.81/2.00  bmc1_merge_next_fun:                    0
% 11.81/2.00  bmc1_unsat_core_clauses_time:           0.
% 11.81/2.00  
% 11.81/2.00  ------ Instantiation
% 11.81/2.00  
% 11.81/2.00  inst_num_of_clauses:                    4639
% 11.81/2.00  inst_num_in_passive:                    670
% 11.81/2.00  inst_num_in_active:                     1939
% 11.81/2.00  inst_num_in_unprocessed:                2029
% 11.81/2.00  inst_num_of_loops:                      2001
% 11.81/2.00  inst_num_of_learning_restarts:          0
% 11.81/2.00  inst_num_moves_active_passive:          58
% 11.81/2.00  inst_lit_activity:                      0
% 11.81/2.00  inst_lit_activity_moves:                1
% 11.81/2.00  inst_num_tautologies:                   0
% 11.81/2.00  inst_num_prop_implied:                  0
% 11.81/2.00  inst_num_existing_simplified:           0
% 11.81/2.00  inst_num_eq_res_simplified:             0
% 11.81/2.00  inst_num_child_elim:                    0
% 11.81/2.00  inst_num_of_dismatching_blockings:      3743
% 11.81/2.00  inst_num_of_non_proper_insts:           6888
% 11.81/2.00  inst_num_of_duplicates:                 0
% 11.81/2.00  inst_inst_num_from_inst_to_res:         0
% 11.81/2.00  inst_dismatching_checking_time:         0.
% 11.81/2.00  
% 11.81/2.00  ------ Resolution
% 11.81/2.00  
% 11.81/2.00  res_num_of_clauses:                     0
% 11.81/2.00  res_num_in_passive:                     0
% 11.81/2.00  res_num_in_active:                      0
% 11.81/2.00  res_num_of_loops:                       96
% 11.81/2.00  res_forward_subset_subsumed:            141
% 11.81/2.00  res_backward_subset_subsumed:           0
% 11.81/2.00  res_forward_subsumed:                   0
% 11.81/2.00  res_backward_subsumed:                  0
% 11.81/2.00  res_forward_subsumption_resolution:     0
% 11.81/2.00  res_backward_subsumption_resolution:    0
% 11.81/2.00  res_clause_to_clause_subsumption:       15454
% 11.81/2.00  res_orphan_elimination:                 0
% 11.81/2.00  res_tautology_del:                      658
% 11.81/2.00  res_num_eq_res_simplified:              0
% 11.81/2.00  res_num_sel_changes:                    0
% 11.81/2.00  res_moves_from_active_to_pass:          0
% 11.81/2.00  
% 11.81/2.00  ------ Superposition
% 11.81/2.00  
% 11.81/2.00  sup_time_total:                         0.
% 11.81/2.00  sup_time_generating:                    0.
% 11.81/2.00  sup_time_sim_full:                      0.
% 11.81/2.00  sup_time_sim_immed:                     0.
% 11.81/2.00  
% 11.81/2.00  sup_num_of_clauses:                     1876
% 11.81/2.00  sup_num_in_active:                      329
% 11.81/2.00  sup_num_in_passive:                     1547
% 11.81/2.00  sup_num_of_loops:                       400
% 11.81/2.00  sup_fw_superposition:                   2974
% 11.81/2.00  sup_bw_superposition:                   1677
% 11.81/2.00  sup_immediate_simplified:               2166
% 11.81/2.00  sup_given_eliminated:                   0
% 11.81/2.00  comparisons_done:                       0
% 11.81/2.00  comparisons_avoided:                    0
% 11.81/2.00  
% 11.81/2.00  ------ Simplifications
% 11.81/2.00  
% 11.81/2.00  
% 11.81/2.00  sim_fw_subset_subsumed:                 797
% 11.81/2.00  sim_bw_subset_subsumed:                 95
% 11.81/2.00  sim_fw_subsumed:                        450
% 11.81/2.00  sim_bw_subsumed:                        22
% 11.81/2.00  sim_fw_subsumption_res:                 0
% 11.81/2.00  sim_bw_subsumption_res:                 0
% 11.81/2.00  sim_tautology_del:                      166
% 11.81/2.00  sim_eq_tautology_del:                   562
% 11.81/2.00  sim_eq_res_simp:                        0
% 11.81/2.00  sim_fw_demodulated:                     151
% 11.81/2.00  sim_bw_demodulated:                     64
% 11.81/2.00  sim_light_normalised:                   907
% 11.81/2.00  sim_joinable_taut:                      0
% 11.81/2.00  sim_joinable_simp:                      0
% 11.81/2.00  sim_ac_normalised:                      0
% 11.81/2.00  sim_smt_subsumption:                    0
% 11.81/2.00  
%------------------------------------------------------------------------------
