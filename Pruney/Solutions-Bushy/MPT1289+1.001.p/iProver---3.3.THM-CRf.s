%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1289+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:21 EST 2020

% Result     : Theorem 3.65s
% Output     : CNFRefutation 3.65s
% Verified   : 
% Statistics : Number of formulae       :  189 ( 620 expanded)
%              Number of clauses        :  137 ( 239 expanded)
%              Number of leaves         :   16 ( 131 expanded)
%              Depth                    :   16
%              Number of atoms          :  594 (2549 expanded)
%              Number of equality atoms :  210 ( 249 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   3 average)
%              Maximal term depth       :    5 (   2 average)

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

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v4_tops_1(k2_pre_topc(X0,X1),X0)
            | ~ v4_tops_1(k1_tops_1(X0,X1),X0) )
          & v4_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v4_tops_1(k2_pre_topc(X0,X1),X0)
            | ~ v4_tops_1(k1_tops_1(X0,X1),X0) )
          & v4_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f31,f35,f34])).

fof(f50,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f36])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f49,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f3,axiom,(
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
    inference(ennf_transformation,[],[f3])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

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

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

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

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

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

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_tops_1(X1,X0)
          <=> ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_tops_1(X1,X0)
          <=> ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

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
    inference(nnf_transformation,[],[f13])).

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

fof(f39,plain,(
    ! [X0,X1] :
      ( v4_tops_1(X1,X0)
      | ~ r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
      | ~ r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
      | ~ v4_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)
      | ~ v4_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f52,plain,
    ( ~ v4_tops_1(k2_pre_topc(sK0,sK1),sK0)
    | ~ v4_tops_1(k1_tops_1(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f51,plain,(
    v4_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_493,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_798,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_493])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_15,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_274,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_15])).

cnf(c_275,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_274])).

cnf(c_485,plain,
    ( ~ m1_subset_1(X0_38,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k1_tops_1(sK0,X0_38),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_275])).

cnf(c_806,plain,
    ( m1_subset_1(X0_38,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k1_tops_1(sK0,X0_38),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_485])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_262,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_15])).

cnf(c_263,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_262])).

cnf(c_486,plain,
    ( ~ m1_subset_1(X0_38,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_pre_topc(sK0,X0_38),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_263])).

cnf(c_805,plain,
    ( m1_subset_1(X0_38,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,X0_38),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_486])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,k1_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_250,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,k1_tops_1(X1,X0)) = k1_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_15])).

cnf(c_251,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,k1_tops_1(sK0,X0)) = k1_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_250])).

cnf(c_487,plain,
    ( ~ m1_subset_1(X0_38,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,k1_tops_1(sK0,X0_38)) = k1_tops_1(sK0,X0_38) ),
    inference(subtyping,[status(esa)],[c_251])).

cnf(c_804,plain,
    ( k1_tops_1(sK0,k1_tops_1(sK0,X0_38)) = k1_tops_1(sK0,X0_38)
    | m1_subset_1(X0_38,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_487])).

cnf(c_1796,plain,
    ( k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,X0_38))) = k1_tops_1(sK0,k2_pre_topc(sK0,X0_38))
    | m1_subset_1(X0_38,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_805,c_804])).

cnf(c_4512,plain,
    ( k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,X0_38)))) = k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,X0_38)))
    | m1_subset_1(X0_38,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_806,c_1796])).

cnf(c_6079,plain,
    ( k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))) = k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
    inference(superposition,[status(thm)],[c_798,c_4512])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_196,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_15])).

cnf(c_197,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X1,X0)
    | r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_196])).

cnf(c_491,plain,
    ( ~ m1_subset_1(X0_38,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1_38,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X1_38,X0_38)
    | r1_tarski(k1_tops_1(sK0,X1_38),k1_tops_1(sK0,X0_38)) ),
    inference(subtyping,[status(esa)],[c_197])).

cnf(c_800,plain,
    ( m1_subset_1(X0_38,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1_38,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X1_38,X0_38) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X1_38),k1_tops_1(sK0,X0_38)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_491])).

cnf(c_6182,plain,
    ( m1_subset_1(X0_38,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))),X0_38) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))),k1_tops_1(sK0,X0_38)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6079,c_800])).

cnf(c_6233,plain,
    ( m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))),k1_tops_1(sK0,sK1)) = iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))),sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6182])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k2_pre_topc(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_238,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,k2_pre_topc(X1,X0)) = k2_pre_topc(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_15])).

cnf(c_239,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k2_pre_topc(sK0,X0)) = k2_pre_topc(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_238])).

cnf(c_488,plain,
    ( ~ m1_subset_1(X0_38,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k2_pre_topc(sK0,X0_38)) = k2_pre_topc(sK0,X0_38) ),
    inference(subtyping,[status(esa)],[c_239])).

cnf(c_803,plain,
    ( k2_pre_topc(sK0,k2_pre_topc(sK0,X0_38)) = k2_pre_topc(sK0,X0_38)
    | m1_subset_1(X0_38,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_488])).

cnf(c_1881,plain,
    ( k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,X0_38))) = k2_pre_topc(sK0,k1_tops_1(sK0,X0_38))
    | m1_subset_1(X0_38,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_806,c_803])).

cnf(c_5070,plain,
    ( k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_798,c_1881])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k2_pre_topc(X1,X0),k2_pre_topc(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_178,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k2_pre_topc(X1,X0),k2_pre_topc(X1,X2))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_15])).

cnf(c_179,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X1,X0)
    | r1_tarski(k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_178])).

cnf(c_492,plain,
    ( ~ m1_subset_1(X0_38,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1_38,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X1_38,X0_38)
    | r1_tarski(k2_pre_topc(sK0,X1_38),k2_pre_topc(sK0,X0_38)) ),
    inference(subtyping,[status(esa)],[c_179])).

cnf(c_799,plain,
    ( m1_subset_1(X0_38,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1_38,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X1_38,X0_38) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,X1_38),k2_pre_topc(sK0,X0_38)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_492])).

cnf(c_5101,plain,
    ( m1_subset_1(X0_38,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0_38,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,X0_38),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_5070,c_799])).

cnf(c_5160,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = iProver_top
    | r1_tarski(sK1,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5101])).

cnf(c_503,plain,
    ( ~ r1_tarski(X0_38,X1_38)
    | r1_tarski(X2_38,X3_38)
    | X2_38 != X0_38
    | X3_38 != X1_38 ),
    theory(equality)).

cnf(c_1167,plain,
    ( r1_tarski(X0_38,X1_38)
    | ~ r1_tarski(X2_38,k2_pre_topc(sK0,k1_tops_1(sK0,X3_38)))
    | X0_38 != X2_38
    | X1_38 != k2_pre_topc(sK0,k1_tops_1(sK0,X3_38)) ),
    inference(instantiation,[status(thm)],[c_503])).

cnf(c_4971,plain,
    ( ~ r1_tarski(X0_38,k2_pre_topc(sK0,k1_tops_1(sK0,X1_38)))
    | r1_tarski(X2_38,k2_pre_topc(sK0,k1_tops_1(sK0,k1_tops_1(sK0,X1_38))))
    | X2_38 != X0_38
    | k2_pre_topc(sK0,k1_tops_1(sK0,k1_tops_1(sK0,X1_38))) != k2_pre_topc(sK0,k1_tops_1(sK0,X1_38)) ),
    inference(instantiation,[status(thm)],[c_1167])).

cnf(c_4972,plain,
    ( X0_38 != X1_38
    | k2_pre_topc(sK0,k1_tops_1(sK0,k1_tops_1(sK0,X2_38))) != k2_pre_topc(sK0,k1_tops_1(sK0,X2_38))
    | r1_tarski(X1_38,k2_pre_topc(sK0,k1_tops_1(sK0,X2_38))) != iProver_top
    | r1_tarski(X0_38,k2_pre_topc(sK0,k1_tops_1(sK0,k1_tops_1(sK0,X2_38)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4971])).

cnf(c_4974,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,k1_tops_1(sK0,sK1))) != k2_pre_topc(sK0,k1_tops_1(sK0,sK1))
    | sK1 != sK1
    | r1_tarski(sK1,k2_pre_topc(sK0,k1_tops_1(sK0,k1_tops_1(sK0,sK1)))) = iProver_top
    | r1_tarski(sK1,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4972])).

cnf(c_1096,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,X0_38),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,X0_38)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_485])).

cnf(c_2489,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,X0_38)),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,X0_38))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_1096])).

cnf(c_2493,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,X0_38)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,X0_38))),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2489])).

cnf(c_2495,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2493])).

cnf(c_1160,plain,
    ( k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_798,c_803])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
    | ~ r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
    | v4_tops_1(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_316,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
    | ~ r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
    | v4_tops_1(X0,X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_15])).

cnf(c_317,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,X0)))
    | ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),X0)
    | v4_tops_1(X0,sK0) ),
    inference(unflattening,[status(thm)],[c_316])).

cnf(c_482,plain,
    ( ~ m1_subset_1(X0_38,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0_38,k2_pre_topc(sK0,k1_tops_1(sK0,X0_38)))
    | ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,X0_38)),X0_38)
    | v4_tops_1(X0_38,sK0) ),
    inference(subtyping,[status(esa)],[c_317])).

cnf(c_809,plain,
    ( m1_subset_1(X0_38,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0_38,k2_pre_topc(sK0,k1_tops_1(sK0,X0_38))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,X0_38)),X0_38) != iProver_top
    | v4_tops_1(X0_38,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_482])).

cnf(c_2401,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_pre_topc(sK0,sK1)) != iProver_top
    | v4_tops_1(k2_pre_topc(sK0,sK1),sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1160,c_809])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_496,plain,
    ( ~ r1_tarski(X0_38,X1_38)
    | ~ r1_tarski(X2_38,X0_38)
    | r1_tarski(X2_38,X1_38) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1168,plain,
    ( ~ r1_tarski(X0_38,X1_38)
    | ~ r1_tarski(X1_38,k2_pre_topc(sK0,k1_tops_1(sK0,X2_38)))
    | r1_tarski(X0_38,k2_pre_topc(sK0,k1_tops_1(sK0,X2_38))) ),
    inference(instantiation,[status(thm)],[c_496])).

cnf(c_2378,plain,
    ( ~ r1_tarski(X0_38,k2_pre_topc(sK0,k1_tops_1(sK0,k1_tops_1(sK0,X1_38))))
    | ~ r1_tarski(k1_tops_1(sK0,X1_38),X0_38)
    | r1_tarski(k1_tops_1(sK0,X1_38),k2_pre_topc(sK0,k1_tops_1(sK0,k1_tops_1(sK0,X1_38)))) ),
    inference(instantiation,[status(thm)],[c_1168])).

cnf(c_2379,plain,
    ( r1_tarski(X0_38,k2_pre_topc(sK0,k1_tops_1(sK0,k1_tops_1(sK0,X1_38)))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X1_38),X0_38) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X1_38),k2_pre_topc(sK0,k1_tops_1(sK0,k1_tops_1(sK0,X1_38)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2378])).

cnf(c_2381,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,k1_tops_1(sK0,sK1)))) = iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),sK1) != iProver_top
    | r1_tarski(sK1,k2_pre_topc(sK0,k1_tops_1(sK0,k1_tops_1(sK0,sK1)))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2379])).

cnf(c_2011,plain,
    ( ~ r1_tarski(X0_38,k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))))
    | ~ r1_tarski(k2_pre_topc(sK0,sK1),X0_38)
    | r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))) ),
    inference(instantiation,[status(thm)],[c_1168])).

cnf(c_2203,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,X0_38)),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))))
    | ~ r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,X0_38)))
    | r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))) ),
    inference(instantiation,[status(thm)],[c_2011])).

cnf(c_2205,plain,
    ( r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,X0_38)),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,X0_38))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2203])).

cnf(c_2207,plain,
    ( r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))) = iProver_top
    | r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2205])).

cnf(c_502,plain,
    ( X0_38 != X1_38
    | k2_pre_topc(X0_41,X0_38) = k2_pre_topc(X0_41,X1_38) ),
    theory(equality)).

cnf(c_1257,plain,
    ( X0_38 != k1_tops_1(sK0,X1_38)
    | k2_pre_topc(sK0,X0_38) = k2_pre_topc(sK0,k1_tops_1(sK0,X1_38)) ),
    inference(instantiation,[status(thm)],[c_502])).

cnf(c_1868,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,k1_tops_1(sK0,X0_38))) = k2_pre_topc(sK0,k1_tops_1(sK0,X0_38))
    | k1_tops_1(sK0,k1_tops_1(sK0,X0_38)) != k1_tops_1(sK0,X0_38) ),
    inference(instantiation,[status(thm)],[c_1257])).

cnf(c_1869,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,k1_tops_1(sK0,sK1))) = k2_pre_topc(sK0,k1_tops_1(sK0,sK1))
    | k1_tops_1(sK0,k1_tops_1(sK0,sK1)) != k1_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_1868])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_226,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_15])).

cnf(c_227,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,X0),X0) ),
    inference(unflattening,[status(thm)],[c_226])).

cnf(c_489,plain,
    ( ~ m1_subset_1(X0_38,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,X0_38),X0_38) ),
    inference(subtyping,[status(esa)],[c_227])).

cnf(c_802,plain,
    ( m1_subset_1(X0_38,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0_38),X0_38) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_489])).

cnf(c_1798,plain,
    ( m1_subset_1(X0_38,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,X0_38)),k2_pre_topc(sK0,X0_38)) = iProver_top ),
    inference(superposition,[status(thm)],[c_805,c_802])).

cnf(c_1823,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k2_pre_topc(sK0,sK1)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1798])).

cnf(c_981,plain,
    ( r1_tarski(X0_38,X1_38)
    | ~ r1_tarski(X0_38,k1_tops_1(sK0,k2_pre_topc(sK0,X1_38)))
    | ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,X1_38)),X1_38) ),
    inference(instantiation,[status(thm)],[c_496])).

cnf(c_1569,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,X0_38)),X0_38)
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,X0_38))),X0_38)
    | ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,X0_38))),k1_tops_1(sK0,k2_pre_topc(sK0,X0_38))) ),
    inference(instantiation,[status(thm)],[c_981])).

cnf(c_1570,plain,
    ( r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,X0_38)),X0_38) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,X0_38))),X0_38) = iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,X0_38))),k1_tops_1(sK0,k2_pre_topc(sK0,X0_38))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1569])).

cnf(c_1572,plain,
    ( r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))),k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))),sK1) = iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1570])).

cnf(c_1396,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,X0_38),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k1_tops_1(sK0,X0_38),k2_pre_topc(sK0,k1_tops_1(sK0,k1_tops_1(sK0,X0_38))))
    | ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,X0_38))),k1_tops_1(sK0,X0_38))
    | v4_tops_1(k1_tops_1(sK0,X0_38),sK0) ),
    inference(instantiation,[status(thm)],[c_482])).

cnf(c_1397,plain,
    ( m1_subset_1(k1_tops_1(sK0,X0_38),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0_38),k2_pre_topc(sK0,k1_tops_1(sK0,k1_tops_1(sK0,X0_38)))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,X0_38))),k1_tops_1(sK0,X0_38)) != iProver_top
    | v4_tops_1(k1_tops_1(sK0,X0_38),sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1396])).

cnf(c_1399,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))),k1_tops_1(sK0,sK1)) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,k1_tops_1(sK0,sK1)))) != iProver_top
    | v4_tops_1(k1_tops_1(sK0,sK1),sK0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1397])).

cnf(c_1134,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,X0_38),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,X0_38)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,X0_38)),k2_pre_topc(sK0,X0_38))
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,X0_38))),k1_tops_1(sK0,k2_pre_topc(sK0,X0_38))) ),
    inference(instantiation,[status(thm)],[c_491])).

cnf(c_1135,plain,
    ( m1_subset_1(k2_pre_topc(sK0,X0_38),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,X0_38)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,X0_38)),k2_pre_topc(sK0,X0_38)) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,X0_38))),k1_tops_1(sK0,k2_pre_topc(sK0,X0_38))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1134])).

cnf(c_1137,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k2_pre_topc(sK0,sK1)) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))),k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1135])).

cnf(c_1105,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,X0_38),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,X0_38)),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,X0_38)),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,X0_38))))
    | ~ r1_tarski(k1_tops_1(sK0,X0_38),k1_tops_1(sK0,k2_pre_topc(sK0,X0_38))) ),
    inference(instantiation,[status(thm)],[c_492])).

cnf(c_1111,plain,
    ( m1_subset_1(k1_tops_1(sK0,X0_38),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,X0_38)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,X0_38)),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,X0_38)))) = iProver_top
    | r1_tarski(k1_tops_1(sK0,X0_38),k1_tops_1(sK0,k2_pre_topc(sK0,X0_38))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1105])).

cnf(c_1113,plain,
    ( m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))) = iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1111])).

cnf(c_1097,plain,
    ( m1_subset_1(k2_pre_topc(sK0,X0_38),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,X0_38)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1096])).

cnf(c_1099,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1097])).

cnf(c_1076,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,X0_38)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_tops_1(sK0,X0_38),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_486])).

cnf(c_1077,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,X0_38)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(k1_tops_1(sK0,X0_38),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1076])).

cnf(c_1079,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1077])).

cnf(c_954,plain,
    ( ~ m1_subset_1(X0_38,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_tops_1(sK0,X0_38),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,X0_38)),k2_pre_topc(sK0,X0_38))
    | ~ r1_tarski(k1_tops_1(sK0,X0_38),X0_38) ),
    inference(instantiation,[status(thm)],[c_492])).

cnf(c_955,plain,
    ( m1_subset_1(X0_38,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k1_tops_1(sK0,X0_38),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,X0_38)),k2_pre_topc(sK0,X0_38)) = iProver_top
    | r1_tarski(k1_tops_1(sK0,X0_38),X0_38) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_954])).

cnf(c_957,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k2_pre_topc(sK0,sK1)) = iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_955])).

cnf(c_939,plain,
    ( ~ m1_subset_1(X0_38,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_pre_topc(sK0,X0_38),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0_38,k2_pre_topc(sK0,X0_38))
    | r1_tarski(k1_tops_1(sK0,X0_38),k1_tops_1(sK0,k2_pre_topc(sK0,X0_38))) ),
    inference(instantiation,[status(thm)],[c_491])).

cnf(c_940,plain,
    ( m1_subset_1(X0_38,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,X0_38),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0_38,k2_pre_topc(sK0,X0_38)) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0_38),k1_tops_1(sK0,k2_pre_topc(sK0,X0_38))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_939])).

cnf(c_942,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) = iProver_top
    | r1_tarski(sK1,k2_pre_topc(sK0,sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_940])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
    | ~ v4_tops_1(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_301,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
    | ~ v4_tops_1(X0,X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_15])).

cnf(c_302,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,X0)))
    | ~ v4_tops_1(X0,sK0) ),
    inference(unflattening,[status(thm)],[c_301])).

cnf(c_483,plain,
    ( ~ m1_subset_1(X0_38,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(X0_38,k2_pre_topc(sK0,k1_tops_1(sK0,X0_38)))
    | ~ v4_tops_1(X0_38,sK0) ),
    inference(subtyping,[status(esa)],[c_302])).

cnf(c_543,plain,
    ( m1_subset_1(X0_38,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0_38,k2_pre_topc(sK0,k1_tops_1(sK0,X0_38))) = iProver_top
    | v4_tops_1(X0_38,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_483])).

cnf(c_545,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK1,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = iProver_top
    | v4_tops_1(sK1,sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_543])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
    | ~ v4_tops_1(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_286,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
    | ~ v4_tops_1(X0,X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_15])).

cnf(c_287,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),X0)
    | ~ v4_tops_1(X0,sK0) ),
    inference(unflattening,[status(thm)],[c_286])).

cnf(c_484,plain,
    ( ~ m1_subset_1(X0_38,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,X0_38)),X0_38)
    | ~ v4_tops_1(X0_38,sK0) ),
    inference(subtyping,[status(esa)],[c_287])).

cnf(c_540,plain,
    ( m1_subset_1(X0_38,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,X0_38)),X0_38) = iProver_top
    | v4_tops_1(X0_38,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_484])).

cnf(c_542,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK1) = iProver_top
    | v4_tops_1(sK1,sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_540])).

cnf(c_537,plain,
    ( m1_subset_1(X0_38,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k1_tops_1(sK0,X0_38),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_485])).

cnf(c_539,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_537])).

cnf(c_534,plain,
    ( m1_subset_1(X0_38,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,X0_38),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_486])).

cnf(c_536,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_534])).

cnf(c_532,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,k1_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_487])).

cnf(c_525,plain,
    ( m1_subset_1(X0_38,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0_38),X0_38) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_489])).

cnf(c_527,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_525])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_214,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,X0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_15])).

cnf(c_215,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(X0,k2_pre_topc(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_214])).

cnf(c_490,plain,
    ( ~ m1_subset_1(X0_38,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(X0_38,k2_pre_topc(sK0,X0_38)) ),
    inference(subtyping,[status(esa)],[c_215])).

cnf(c_522,plain,
    ( m1_subset_1(X0_38,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0_38,k2_pre_topc(sK0,X0_38)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_490])).

cnf(c_524,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK1,k2_pre_topc(sK0,sK1)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_522])).

cnf(c_498,plain,
    ( X0_38 = X0_38 ),
    theory(equality)).

cnf(c_511,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_498])).

cnf(c_12,negated_conjecture,
    ( ~ v4_tops_1(k2_pre_topc(sK0,sK1),sK0)
    | ~ v4_tops_1(k1_tops_1(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_19,plain,
    ( v4_tops_1(k2_pre_topc(sK0,sK1),sK0) != iProver_top
    | v4_tops_1(k1_tops_1(sK0,sK1),sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_13,negated_conjecture,
    ( v4_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_18,plain,
    ( v4_tops_1(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_17,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6233,c_5160,c_4974,c_2495,c_2401,c_2381,c_2207,c_1869,c_1823,c_1572,c_1399,c_1137,c_1113,c_1099,c_1079,c_957,c_942,c_545,c_542,c_539,c_536,c_532,c_527,c_524,c_511,c_19,c_18,c_17,c_14])).


%------------------------------------------------------------------------------
