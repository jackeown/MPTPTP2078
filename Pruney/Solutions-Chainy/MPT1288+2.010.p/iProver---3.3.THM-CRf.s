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
% DateTime   : Thu Dec  3 12:15:58 EST 2020

% Result     : Theorem 11.75s
% Output     : CNFRefutation 11.75s
% Verified   : 
% Statistics : Number of formulae       :  177 ( 898 expanded)
%              Number of clauses        :  109 ( 269 expanded)
%              Number of leaves         :   19 ( 208 expanded)
%              Depth                    :   25
%              Number of atoms          :  581 (3547 expanded)
%              Number of equality atoms :  239 ( 859 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal clause size      :   10 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_tops_1(X1,X0)
           => k1_tops_1(X0,k2_tops_1(X0,X1)) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_tops_1(X1,X0)
             => k1_tops_1(X0,k2_tops_1(X0,X1)) = k1_xboole_0 ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_tops_1(X0,k2_tops_1(X0,X1)) != k1_xboole_0
          & v4_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_tops_1(X0,k2_tops_1(X0,X1)) != k1_xboole_0
          & v4_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f39])).

fof(f47,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k1_tops_1(X0,k2_tops_1(X0,X1)) != k1_xboole_0
          & v4_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k1_tops_1(X0,k2_tops_1(X0,sK1)) != k1_xboole_0
        & v4_tops_1(sK1,X0)
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k1_tops_1(X0,k2_tops_1(X0,X1)) != k1_xboole_0
            & v4_tops_1(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( k1_tops_1(sK0,k2_tops_1(sK0,X1)) != k1_xboole_0
          & v4_tops_1(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( k1_tops_1(sK0,k2_tops_1(sK0,sK1)) != k1_xboole_0
    & v4_tops_1(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f40,f47,f46])).

fof(f70,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f48])).

fof(f6,axiom,(
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
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f3,axiom,(
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
    inference(ennf_transformation,[],[f3])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f69,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f4,axiom,(
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
    inference(ennf_transformation,[],[f4])).

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

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f41])).

fof(f51,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f71,plain,(
    v4_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f5,axiom,(
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
    inference(ennf_transformation,[],[f5])).

fof(f43,plain,(
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

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
      | ~ v4_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_tops_1(X0,X1) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> k1_tops_1(X0,X1) = k1_xboole_0 )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | k1_tops_1(X0,X1) != k1_xboole_0 )
            & ( k1_tops_1(X0,X1) = k1_xboole_0
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v2_tops_1(X1,X0)
      | k1_tops_1(X0,X1) != k1_xboole_0
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f68,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
           => v3_tops_1(k2_tops_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tops_1(k2_tops_1(X0,X1),X0)
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tops_1(k2_tops_1(X0,X1),X0)
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f37])).

fof(f67,plain,(
    ! [X0,X1] :
      ( v3_tops_1(k2_tops_1(X0,X1),X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tops_1(X1,X0)
           => v2_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tops_1(X1,X0)
          | ~ v3_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tops_1(X1,X0)
          | ~ v3_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f66,plain,(
    ! [X0,X1] :
      ( v2_tops_1(X1,X0)
      | ~ v3_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_xboole_0
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f72,plain,(
    k1_tops_1(sK0,k2_tops_1(sK0,sK1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_718,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_729,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k2_pre_topc(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_734,plain,
    ( k2_pre_topc(X0,k2_pre_topc(X0,X1)) = k2_pre_topc(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2063,plain,
    ( k2_pre_topc(X0,k2_pre_topc(X0,k1_tops_1(X0,X1))) = k2_pre_topc(X0,k1_tops_1(X0,X1))
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_729,c_734])).

cnf(c_5541,plain,
    ( k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = k2_pre_topc(sK0,k1_tops_1(sK0,sK1))
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_718,c_2063])).

cnf(c_22,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_956,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1145,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_5651,plain,
    ( k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5541,c_22,c_21,c_956,c_1145])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k2_pre_topc(X1,X0),k2_pre_topc(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_733,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(k2_pre_topc(X1,X0),k2_pre_topc(X1,X2)) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_5660,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5651,c_733])).

cnf(c_25,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_26,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_957,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_956])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1150,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1151,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1150])).

cnf(c_6138,plain,
    ( r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = iProver_top
    | r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5660,c_25,c_26,c_957,c_1151])).

cnf(c_6139,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = iProver_top ),
    inference(renaming,[status(thm)],[c_6138])).

cnf(c_2065,plain,
    ( k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)) = k2_pre_topc(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_718,c_734])).

cnf(c_997,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2090,plain,
    ( k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2065,c_22,c_21,c_997])).

cnf(c_3874,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK0,sK1)) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,sK1)) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2090,c_733])).

cnf(c_953,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_954,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_953])).

cnf(c_4572,plain,
    ( r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,sK1)) = iProver_top
    | r1_tarski(X0,k2_pre_topc(sK0,sK1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3874,c_25,c_26,c_954])).

cnf(c_4573,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK0,sK1)) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,sK1)) = iProver_top ),
    inference(renaming,[status(thm)],[c_4572])).

cnf(c_3873,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,sK1),X0) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X0)) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2090,c_733])).

cnf(c_4321,plain,
    ( r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X0)) = iProver_top
    | r1_tarski(k2_pre_topc(sK0,sK1),X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3873,c_25,c_26,c_954])).

cnf(c_4322,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,sK1),X0) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_4321])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_737,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4331,plain,
    ( k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,sK1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,sK1)) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,sK1),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4322,c_737])).

cnf(c_6653,plain,
    ( k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,sK1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK0,sK1)) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,sK1),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4573,c_4331])).

cnf(c_322,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1134,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | X0 != k2_pre_topc(sK0,sK1)
    | X1 != k1_zfmisc_1(u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_322])).

cnf(c_2357,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | X0 != k2_pre_topc(sK0,sK1)
    | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1134])).

cnf(c_2359,plain,
    ( X0 != k2_pre_topc(sK0,sK1)
    | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(u1_struct_0(sK0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2357])).

cnf(c_316,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2358,plain,
    ( k1_zfmisc_1(u1_struct_0(sK0)) = k1_zfmisc_1(u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_316])).

cnf(c_6105,plain,
    ( ~ r1_tarski(X0,k2_pre_topc(sK0,sK1))
    | ~ r1_tarski(k2_pre_topc(sK0,sK1),X0)
    | X0 = k2_pre_topc(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_6106,plain,
    ( X0 = k2_pre_topc(sK0,sK1)
    | r1_tarski(X0,k2_pre_topc(sK0,sK1)) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,sK1),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6105])).

cnf(c_7778,plain,
    ( k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,sK1)
    | r1_tarski(X0,k2_pre_topc(sK0,sK1)) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,sK1),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6653,c_25,c_26,c_954,c_2359,c_2358,c_6106])).

cnf(c_7788,plain,
    ( k2_pre_topc(sK0,k2_pre_topc(sK0,X0)) = k2_pre_topc(sK0,sK1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X0)) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_733,c_7778])).

cnf(c_33691,plain,
    ( r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X0)) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top
    | k2_pre_topc(sK0,k2_pre_topc(sK0,X0)) = k2_pre_topc(sK0,sK1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7788,c_25,c_26])).

cnf(c_33692,plain,
    ( k2_pre_topc(sK0,k2_pre_topc(sK0,X0)) = k2_pre_topc(sK0,sK1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_33691])).

cnf(c_33705,plain,
    ( k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = k2_pre_topc(sK0,sK1)
    | m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),sK1) != iProver_top
    | r1_tarski(sK1,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6139,c_33692])).

cnf(c_33892,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
    | m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),sK1) != iProver_top
    | r1_tarski(sK1,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_33705,c_5651])).

cnf(c_20,negated_conjecture,
    ( v4_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_27,plain,
    ( v4_tops_1(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_962,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_963,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_962])).

cnf(c_7,plain,
    ( ~ v4_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1041,plain,
    ( ~ v4_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK1,k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1042,plain,
    ( v4_tops_1(sK1,sK0) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK1,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1041])).

cnf(c_35513,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_33892,c_25,c_26,c_27,c_957,c_963,c_1042])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_726,plain,
    ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2601,plain,
    ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k1_tops_1(X0,X1)),k1_tops_1(X0,k1_tops_1(X0,X1))) = k2_tops_1(X0,k1_tops_1(X0,X1))
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_729,c_726])).

cnf(c_11632,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,k1_tops_1(sK0,sK1))) = k2_tops_1(sK0,k1_tops_1(sK0,sK1))
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_718,c_2601])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,k1_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_725,plain,
    ( k1_tops_1(X0,k1_tops_1(X0,X1)) = k1_tops_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1265,plain,
    ( k1_tops_1(sK0,k1_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_718,c_725])).

cnf(c_1000,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k1_tops_1(sK0,k1_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1605,plain,
    ( k1_tops_1(sK0,k1_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1265,c_22,c_21,c_1000])).

cnf(c_11635,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,k1_tops_1(sK0,sK1))
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11632,c_1605])).

cnf(c_12188,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,k1_tops_1(sK0,sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11635,c_25])).

cnf(c_35537,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,k1_tops_1(sK0,sK1)) ),
    inference(demodulation,[status(thm)],[c_35513,c_12188])).

cnf(c_2603,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_718,c_726])).

cnf(c_1047,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_3084,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2603,c_22,c_21,c_1047])).

cnf(c_35558,plain,
    ( k2_tops_1(sK0,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_35537,c_3084])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_728,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1343,plain,
    ( k1_tops_1(X0,k1_tops_1(X0,k2_tops_1(X0,X1))) = k1_tops_1(X0,k2_tops_1(X0,X1))
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_728,c_725])).

cnf(c_4070,plain,
    ( k1_tops_1(X0,k1_tops_1(X0,k2_tops_1(X0,k1_tops_1(X0,X1)))) = k1_tops_1(X0,k2_tops_1(X0,k1_tops_1(X0,X1)))
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_729,c_1343])).

cnf(c_10276,plain,
    ( k1_tops_1(sK0,k1_tops_1(sK0,k2_tops_1(sK0,k1_tops_1(sK0,sK1)))) = k1_tops_1(sK0,k2_tops_1(sK0,k1_tops_1(sK0,sK1)))
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_718,c_4070])).

cnf(c_1148,plain,
    ( m1_subset_1(k2_tops_1(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1639,plain,
    ( ~ m1_subset_1(k2_tops_1(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k1_tops_1(sK0,k1_tops_1(sK0,k2_tops_1(sK0,k1_tops_1(sK0,sK1)))) = k1_tops_1(sK0,k2_tops_1(sK0,k1_tops_1(sK0,sK1))) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_10428,plain,
    ( k1_tops_1(sK0,k1_tops_1(sK0,k2_tops_1(sK0,k1_tops_1(sK0,sK1)))) = k1_tops_1(sK0,k2_tops_1(sK0,k1_tops_1(sK0,sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10276,c_22,c_21,c_956,c_1148,c_1639])).

cnf(c_15,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_723,plain,
    ( k1_tops_1(X0,X1) != k1_xboole_0
    | v2_tops_1(X1,X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_10434,plain,
    ( k1_tops_1(sK0,k2_tops_1(sK0,k1_tops_1(sK0,sK1))) != k1_xboole_0
    | v2_tops_1(k1_tops_1(sK0,k2_tops_1(sK0,k1_tops_1(sK0,sK1))),sK0) = iProver_top
    | m1_subset_1(k1_tops_1(sK0,k2_tops_1(sK0,k1_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_10428,c_723])).

cnf(c_23,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_11,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_967,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1155,plain,
    ( m1_subset_1(k2_tops_1(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1148])).

cnf(c_18,plain,
    ( v3_tops_1(k2_tops_1(X0,X1),X0)
    | ~ v3_pre_topc(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1242,plain,
    ( v3_tops_1(k2_tops_1(sK0,k1_tops_1(sK0,sK1)),sK0)
    | ~ v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_1644,plain,
    ( ~ m1_subset_1(k2_tops_1(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k1_tops_1(sK0,k2_tops_1(sK0,k1_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1648,plain,
    ( m1_subset_1(k2_tops_1(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k1_tops_1(sK0,k2_tops_1(sK0,k1_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1644])).

cnf(c_17,plain,
    ( ~ v3_tops_1(X0,X1)
    | v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2045,plain,
    ( ~ v3_tops_1(k2_tops_1(sK0,k1_tops_1(sK0,sK1)),sK0)
    | v2_tops_1(k2_tops_1(sK0,k1_tops_1(sK0,sK1)),sK0)
    | ~ m1_subset_1(k2_tops_1(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_16,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_3501,plain,
    ( ~ v2_tops_1(k2_tops_1(sK0,k1_tops_1(sK0,sK1)),sK0)
    | ~ m1_subset_1(k2_tops_1(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k1_tops_1(sK0,k2_tops_1(sK0,k1_tops_1(sK0,sK1))) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_11469,plain,
    ( v2_tops_1(k1_tops_1(sK0,k2_tops_1(sK0,k1_tops_1(sK0,sK1))),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10434,c_23,c_22,c_25,c_21,c_26,c_956,c_957,c_967,c_1148,c_1155,c_1242,c_1648,c_2045,c_3501])).

cnf(c_722,plain,
    ( k1_tops_1(X0,X1) = k1_xboole_0
    | v2_tops_1(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2410,plain,
    ( k1_tops_1(X0,k1_tops_1(X0,X1)) = k1_xboole_0
    | v2_tops_1(k1_tops_1(X0,X1),X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_729,c_722])).

cnf(c_11474,plain,
    ( k1_tops_1(sK0,k1_tops_1(sK0,k2_tops_1(sK0,k1_tops_1(sK0,sK1)))) = k1_xboole_0
    | m1_subset_1(k2_tops_1(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_11469,c_2410])).

cnf(c_11475,plain,
    ( k1_tops_1(sK0,k2_tops_1(sK0,k1_tops_1(sK0,sK1))) = k1_xboole_0
    | m1_subset_1(k2_tops_1(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11474,c_10428])).

cnf(c_11478,plain,
    ( k1_tops_1(sK0,k2_tops_1(sK0,k1_tops_1(sK0,sK1))) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_11475,c_23,c_22,c_21,c_956,c_967,c_1148,c_1242,c_2045,c_3501])).

cnf(c_35942,plain,
    ( k1_tops_1(sK0,k2_tops_1(sK0,sK1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_35558,c_11478])).

cnf(c_19,negated_conjecture,
    ( k1_tops_1(sK0,k2_tops_1(sK0,sK1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f72])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_35942,c_19])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:46:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 11.75/1.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.75/1.99  
% 11.75/1.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.75/1.99  
% 11.75/1.99  ------  iProver source info
% 11.75/1.99  
% 11.75/1.99  git: date: 2020-06-30 10:37:57 +0100
% 11.75/1.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.75/1.99  git: non_committed_changes: false
% 11.75/1.99  git: last_make_outside_of_git: false
% 11.75/1.99  
% 11.75/1.99  ------ 
% 11.75/1.99  ------ Parsing...
% 11.75/1.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.75/1.99  
% 11.75/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 11.75/1.99  
% 11.75/1.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.75/1.99  
% 11.75/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.75/1.99  ------ Proving...
% 11.75/1.99  ------ Problem Properties 
% 11.75/1.99  
% 11.75/1.99  
% 11.75/1.99  clauses                                 23
% 11.75/1.99  conjectures                             5
% 11.75/1.99  EPR                                     5
% 11.75/1.99  Horn                                    23
% 11.75/1.99  unary                                   6
% 11.75/1.99  binary                                  0
% 11.75/1.99  lits                                    69
% 11.75/1.99  lits eq                                 7
% 11.75/1.99  fd_pure                                 0
% 11.75/1.99  fd_pseudo                               0
% 11.75/1.99  fd_cond                                 0
% 11.75/1.99  fd_pseudo_cond                          1
% 11.75/1.99  AC symbols                              0
% 11.75/1.99  
% 11.75/1.99  ------ Input Options Time Limit: Unbounded
% 11.75/1.99  
% 11.75/1.99  
% 11.75/1.99  ------ 
% 11.75/1.99  Current options:
% 11.75/1.99  ------ 
% 11.75/1.99  
% 11.75/1.99  
% 11.75/1.99  
% 11.75/1.99  
% 11.75/1.99  ------ Proving...
% 11.75/1.99  
% 11.75/1.99  
% 11.75/1.99  % SZS status Theorem for theBenchmark.p
% 11.75/1.99  
% 11.75/1.99  % SZS output start CNFRefutation for theBenchmark.p
% 11.75/1.99  
% 11.75/1.99  fof(f15,conjecture,(
% 11.75/1.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_tops_1(X1,X0) => k1_tops_1(X0,k2_tops_1(X0,X1)) = k1_xboole_0)))),
% 11.75/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.75/1.99  
% 11.75/1.99  fof(f16,negated_conjecture,(
% 11.75/1.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_tops_1(X1,X0) => k1_tops_1(X0,k2_tops_1(X0,X1)) = k1_xboole_0)))),
% 11.75/1.99    inference(negated_conjecture,[],[f15])).
% 11.75/1.99  
% 11.75/1.99  fof(f39,plain,(
% 11.75/1.99    ? [X0] : (? [X1] : ((k1_tops_1(X0,k2_tops_1(X0,X1)) != k1_xboole_0 & v4_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 11.75/1.99    inference(ennf_transformation,[],[f16])).
% 11.75/1.99  
% 11.75/1.99  fof(f40,plain,(
% 11.75/1.99    ? [X0] : (? [X1] : (k1_tops_1(X0,k2_tops_1(X0,X1)) != k1_xboole_0 & v4_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 11.75/1.99    inference(flattening,[],[f39])).
% 11.75/1.99  
% 11.75/1.99  fof(f47,plain,(
% 11.75/1.99    ( ! [X0] : (? [X1] : (k1_tops_1(X0,k2_tops_1(X0,X1)) != k1_xboole_0 & v4_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (k1_tops_1(X0,k2_tops_1(X0,sK1)) != k1_xboole_0 & v4_tops_1(sK1,X0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 11.75/1.99    introduced(choice_axiom,[])).
% 11.75/1.99  
% 11.75/1.99  fof(f46,plain,(
% 11.75/1.99    ? [X0] : (? [X1] : (k1_tops_1(X0,k2_tops_1(X0,X1)) != k1_xboole_0 & v4_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (k1_tops_1(sK0,k2_tops_1(sK0,X1)) != k1_xboole_0 & v4_tops_1(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 11.75/1.99    introduced(choice_axiom,[])).
% 11.75/1.99  
% 11.75/1.99  fof(f48,plain,(
% 11.75/1.99    (k1_tops_1(sK0,k2_tops_1(sK0,sK1)) != k1_xboole_0 & v4_tops_1(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 11.75/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f40,f47,f46])).
% 11.75/1.99  
% 11.75/1.99  fof(f70,plain,(
% 11.75/1.99    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 11.75/1.99    inference(cnf_transformation,[],[f48])).
% 11.75/1.99  
% 11.75/1.99  fof(f6,axiom,(
% 11.75/1.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 11.75/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.75/1.99  
% 11.75/1.99  fof(f24,plain,(
% 11.75/1.99    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 11.75/1.99    inference(ennf_transformation,[],[f6])).
% 11.75/1.99  
% 11.75/1.99  fof(f25,plain,(
% 11.75/1.99    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 11.75/1.99    inference(flattening,[],[f24])).
% 11.75/1.99  
% 11.75/1.99  fof(f58,plain,(
% 11.75/1.99    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.75/1.99    inference(cnf_transformation,[],[f25])).
% 11.75/1.99  
% 11.75/1.99  fof(f3,axiom,(
% 11.75/1.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)))),
% 11.75/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.75/1.99  
% 11.75/1.99  fof(f19,plain,(
% 11.75/1.99    ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 11.75/1.99    inference(ennf_transformation,[],[f3])).
% 11.75/1.99  
% 11.75/1.99  fof(f20,plain,(
% 11.75/1.99    ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 11.75/1.99    inference(flattening,[],[f19])).
% 11.75/1.99  
% 11.75/1.99  fof(f53,plain,(
% 11.75/1.99    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.75/1.99    inference(cnf_transformation,[],[f20])).
% 11.75/1.99  
% 11.75/1.99  fof(f69,plain,(
% 11.75/1.99    l1_pre_topc(sK0)),
% 11.75/1.99    inference(cnf_transformation,[],[f48])).
% 11.75/1.99  
% 11.75/1.99  fof(f4,axiom,(
% 11.75/1.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))))))),
% 11.75/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.75/1.99  
% 11.75/1.99  fof(f21,plain,(
% 11.75/1.99    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.75/1.99    inference(ennf_transformation,[],[f4])).
% 11.75/1.99  
% 11.75/1.99  fof(f22,plain,(
% 11.75/1.99    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.75/1.99    inference(flattening,[],[f21])).
% 11.75/1.99  
% 11.75/1.99  fof(f54,plain,(
% 11.75/1.99    ( ! [X2,X0,X1] : (r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.75/1.99    inference(cnf_transformation,[],[f22])).
% 11.75/1.99  
% 11.75/1.99  fof(f2,axiom,(
% 11.75/1.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 11.75/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.75/1.99  
% 11.75/1.99  fof(f17,plain,(
% 11.75/1.99    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 11.75/1.99    inference(ennf_transformation,[],[f2])).
% 11.75/1.99  
% 11.75/1.99  fof(f18,plain,(
% 11.75/1.99    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 11.75/1.99    inference(flattening,[],[f17])).
% 11.75/1.99  
% 11.75/1.99  fof(f52,plain,(
% 11.75/1.99    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.75/1.99    inference(cnf_transformation,[],[f18])).
% 11.75/1.99  
% 11.75/1.99  fof(f1,axiom,(
% 11.75/1.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 11.75/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.75/1.99  
% 11.75/1.99  fof(f41,plain,(
% 11.75/1.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.75/1.99    inference(nnf_transformation,[],[f1])).
% 11.75/1.99  
% 11.75/1.99  fof(f42,plain,(
% 11.75/1.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.75/1.99    inference(flattening,[],[f41])).
% 11.75/1.99  
% 11.75/1.99  fof(f51,plain,(
% 11.75/1.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 11.75/1.99    inference(cnf_transformation,[],[f42])).
% 11.75/1.99  
% 11.75/1.99  fof(f71,plain,(
% 11.75/1.99    v4_tops_1(sK1,sK0)),
% 11.75/1.99    inference(cnf_transformation,[],[f48])).
% 11.75/1.99  
% 11.75/1.99  fof(f11,axiom,(
% 11.75/1.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 11.75/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.75/1.99  
% 11.75/1.99  fof(f33,plain,(
% 11.75/1.99    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.75/1.99    inference(ennf_transformation,[],[f11])).
% 11.75/1.99  
% 11.75/1.99  fof(f63,plain,(
% 11.75/1.99    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.75/1.99    inference(cnf_transformation,[],[f33])).
% 11.75/1.99  
% 11.75/1.99  fof(f5,axiom,(
% 11.75/1.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_tops_1(X1,X0) <=> (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)))))),
% 11.75/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.75/1.99  
% 11.75/1.99  fof(f23,plain,(
% 11.75/1.99    ! [X0] : (! [X1] : ((v4_tops_1(X1,X0) <=> (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.75/1.99    inference(ennf_transformation,[],[f5])).
% 11.75/1.99  
% 11.75/1.99  fof(f43,plain,(
% 11.75/1.99    ! [X0] : (! [X1] : (((v4_tops_1(X1,X0) | (~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1))) & ((r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) | ~v4_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.75/1.99    inference(nnf_transformation,[],[f23])).
% 11.75/1.99  
% 11.75/1.99  fof(f44,plain,(
% 11.75/1.99    ! [X0] : (! [X1] : (((v4_tops_1(X1,X0) | ~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) & ((r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) | ~v4_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.75/1.99    inference(flattening,[],[f43])).
% 11.75/1.99  
% 11.75/1.99  fof(f56,plain,(
% 11.75/1.99    ( ! [X0,X1] : (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~v4_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.75/1.99    inference(cnf_transformation,[],[f44])).
% 11.75/1.99  
% 11.75/1.99  fof(f9,axiom,(
% 11.75/1.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 11.75/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.75/1.99  
% 11.75/1.99  fof(f30,plain,(
% 11.75/1.99    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.75/1.99    inference(ennf_transformation,[],[f9])).
% 11.75/1.99  
% 11.75/1.99  fof(f61,plain,(
% 11.75/1.99    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.75/1.99    inference(cnf_transformation,[],[f30])).
% 11.75/1.99  
% 11.75/1.99  fof(f10,axiom,(
% 11.75/1.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)))),
% 11.75/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.75/1.99  
% 11.75/1.99  fof(f31,plain,(
% 11.75/1.99    ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 11.75/1.99    inference(ennf_transformation,[],[f10])).
% 11.75/1.99  
% 11.75/1.99  fof(f32,plain,(
% 11.75/1.99    ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 11.75/1.99    inference(flattening,[],[f31])).
% 11.75/1.99  
% 11.75/1.99  fof(f62,plain,(
% 11.75/1.99    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.75/1.99    inference(cnf_transformation,[],[f32])).
% 11.75/1.99  
% 11.75/1.99  fof(f7,axiom,(
% 11.75/1.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 11.75/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.75/1.99  
% 11.75/1.99  fof(f26,plain,(
% 11.75/1.99    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 11.75/1.99    inference(ennf_transformation,[],[f7])).
% 11.75/1.99  
% 11.75/1.99  fof(f27,plain,(
% 11.75/1.99    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 11.75/1.99    inference(flattening,[],[f26])).
% 11.75/1.99  
% 11.75/1.99  fof(f59,plain,(
% 11.75/1.99    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.75/1.99    inference(cnf_transformation,[],[f27])).
% 11.75/1.99  
% 11.75/1.99  fof(f12,axiom,(
% 11.75/1.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_tops_1(X0,X1) = k1_xboole_0)))),
% 11.75/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.75/1.99  
% 11.75/1.99  fof(f34,plain,(
% 11.75/1.99    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> k1_tops_1(X0,X1) = k1_xboole_0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.75/1.99    inference(ennf_transformation,[],[f12])).
% 11.75/1.99  
% 11.75/1.99  fof(f45,plain,(
% 11.75/1.99    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | k1_tops_1(X0,X1) != k1_xboole_0) & (k1_tops_1(X0,X1) = k1_xboole_0 | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.75/1.99    inference(nnf_transformation,[],[f34])).
% 11.75/1.99  
% 11.75/1.99  fof(f65,plain,(
% 11.75/1.99    ( ! [X0,X1] : (v2_tops_1(X1,X0) | k1_tops_1(X0,X1) != k1_xboole_0 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.75/1.99    inference(cnf_transformation,[],[f45])).
% 11.75/1.99  
% 11.75/1.99  fof(f68,plain,(
% 11.75/1.99    v2_pre_topc(sK0)),
% 11.75/1.99    inference(cnf_transformation,[],[f48])).
% 11.75/1.99  
% 11.75/1.99  fof(f8,axiom,(
% 11.75/1.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 11.75/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.75/1.99  
% 11.75/1.99  fof(f28,plain,(
% 11.75/1.99    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 11.75/1.99    inference(ennf_transformation,[],[f8])).
% 11.75/1.99  
% 11.75/1.99  fof(f29,plain,(
% 11.75/1.99    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 11.75/1.99    inference(flattening,[],[f28])).
% 11.75/1.99  
% 11.75/1.99  fof(f60,plain,(
% 11.75/1.99    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 11.75/1.99    inference(cnf_transformation,[],[f29])).
% 11.75/1.99  
% 11.75/1.99  fof(f14,axiom,(
% 11.75/1.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) => v3_tops_1(k2_tops_1(X0,X1),X0))))),
% 11.75/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.75/1.99  
% 11.75/1.99  fof(f37,plain,(
% 11.75/1.99    ! [X0] : (! [X1] : ((v3_tops_1(k2_tops_1(X0,X1),X0) | ~v3_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 11.75/1.99    inference(ennf_transformation,[],[f14])).
% 11.75/1.99  
% 11.75/1.99  fof(f38,plain,(
% 11.75/1.99    ! [X0] : (! [X1] : (v3_tops_1(k2_tops_1(X0,X1),X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 11.75/1.99    inference(flattening,[],[f37])).
% 11.75/1.99  
% 11.75/1.99  fof(f67,plain,(
% 11.75/1.99    ( ! [X0,X1] : (v3_tops_1(k2_tops_1(X0,X1),X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 11.75/1.99    inference(cnf_transformation,[],[f38])).
% 11.75/1.99  
% 11.75/1.99  fof(f13,axiom,(
% 11.75/1.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tops_1(X1,X0) => v2_tops_1(X1,X0))))),
% 11.75/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.75/1.99  
% 11.75/1.99  fof(f35,plain,(
% 11.75/1.99    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) | ~v3_tops_1(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.75/1.99    inference(ennf_transformation,[],[f13])).
% 11.75/1.99  
% 11.75/1.99  fof(f36,plain,(
% 11.75/1.99    ! [X0] : (! [X1] : (v2_tops_1(X1,X0) | ~v3_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.75/1.99    inference(flattening,[],[f35])).
% 11.75/1.99  
% 11.75/1.99  fof(f66,plain,(
% 11.75/1.99    ( ! [X0,X1] : (v2_tops_1(X1,X0) | ~v3_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.75/1.99    inference(cnf_transformation,[],[f36])).
% 11.75/1.99  
% 11.75/1.99  fof(f64,plain,(
% 11.75/1.99    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k1_xboole_0 | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.75/1.99    inference(cnf_transformation,[],[f45])).
% 11.75/1.99  
% 11.75/1.99  fof(f72,plain,(
% 11.75/1.99    k1_tops_1(sK0,k2_tops_1(sK0,sK1)) != k1_xboole_0),
% 11.75/1.99    inference(cnf_transformation,[],[f48])).
% 11.75/1.99  
% 11.75/1.99  cnf(c_21,negated_conjecture,
% 11.75/1.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 11.75/1.99      inference(cnf_transformation,[],[f70]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_718,plain,
% 11.75/1.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 11.75/1.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_9,plain,
% 11.75/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.75/1.99      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 11.75/1.99      | ~ l1_pre_topc(X1) ),
% 11.75/1.99      inference(cnf_transformation,[],[f58]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_729,plain,
% 11.75/1.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 11.75/1.99      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 11.75/1.99      | l1_pre_topc(X1) != iProver_top ),
% 11.75/1.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_4,plain,
% 11.75/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.75/1.99      | ~ l1_pre_topc(X1)
% 11.75/1.99      | k2_pre_topc(X1,k2_pre_topc(X1,X0)) = k2_pre_topc(X1,X0) ),
% 11.75/1.99      inference(cnf_transformation,[],[f53]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_734,plain,
% 11.75/1.99      ( k2_pre_topc(X0,k2_pre_topc(X0,X1)) = k2_pre_topc(X0,X1)
% 11.75/1.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 11.75/1.99      | l1_pre_topc(X0) != iProver_top ),
% 11.75/1.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_2063,plain,
% 11.75/1.99      ( k2_pre_topc(X0,k2_pre_topc(X0,k1_tops_1(X0,X1))) = k2_pre_topc(X0,k1_tops_1(X0,X1))
% 11.75/1.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 11.75/1.99      | l1_pre_topc(X0) != iProver_top ),
% 11.75/1.99      inference(superposition,[status(thm)],[c_729,c_734]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_5541,plain,
% 11.75/1.99      ( k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = k2_pre_topc(sK0,k1_tops_1(sK0,sK1))
% 11.75/1.99      | l1_pre_topc(sK0) != iProver_top ),
% 11.75/1.99      inference(superposition,[status(thm)],[c_718,c_2063]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_22,negated_conjecture,
% 11.75/1.99      ( l1_pre_topc(sK0) ),
% 11.75/1.99      inference(cnf_transformation,[],[f69]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_956,plain,
% 11.75/1.99      ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 11.75/1.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.75/1.99      | ~ l1_pre_topc(sK0) ),
% 11.75/1.99      inference(instantiation,[status(thm)],[c_9]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_1145,plain,
% 11.75/1.99      ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 11.75/1.99      | ~ l1_pre_topc(sK0)
% 11.75/1.99      | k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) ),
% 11.75/1.99      inference(instantiation,[status(thm)],[c_4]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_5651,plain,
% 11.75/1.99      ( k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) ),
% 11.75/1.99      inference(global_propositional_subsumption,
% 11.75/1.99                [status(thm)],
% 11.75/1.99                [c_5541,c_22,c_21,c_956,c_1145]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_5,plain,
% 11.75/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.75/1.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 11.75/1.99      | ~ r1_tarski(X0,X2)
% 11.75/1.99      | r1_tarski(k2_pre_topc(X1,X0),k2_pre_topc(X1,X2))
% 11.75/1.99      | ~ l1_pre_topc(X1) ),
% 11.75/1.99      inference(cnf_transformation,[],[f54]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_733,plain,
% 11.75/1.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 11.75/1.99      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 11.75/1.99      | r1_tarski(X0,X2) != iProver_top
% 11.75/1.99      | r1_tarski(k2_pre_topc(X1,X0),k2_pre_topc(X1,X2)) = iProver_top
% 11.75/1.99      | l1_pre_topc(X1) != iProver_top ),
% 11.75/1.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_5660,plain,
% 11.75/1.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.75/1.99      | m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.75/1.99      | r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != iProver_top
% 11.75/1.99      | r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = iProver_top
% 11.75/1.99      | l1_pre_topc(sK0) != iProver_top ),
% 11.75/1.99      inference(superposition,[status(thm)],[c_5651,c_733]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_25,plain,
% 11.75/1.99      ( l1_pre_topc(sK0) = iProver_top ),
% 11.75/1.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_26,plain,
% 11.75/1.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 11.75/1.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_957,plain,
% 11.75/1.99      ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 11.75/1.99      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.75/1.99      | l1_pre_topc(sK0) != iProver_top ),
% 11.75/1.99      inference(predicate_to_equality,[status(thm)],[c_956]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_3,plain,
% 11.75/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.75/1.99      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 11.75/1.99      | ~ l1_pre_topc(X1) ),
% 11.75/1.99      inference(cnf_transformation,[],[f52]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_1150,plain,
% 11.75/1.99      ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 11.75/1.99      | m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
% 11.75/1.99      | ~ l1_pre_topc(sK0) ),
% 11.75/1.99      inference(instantiation,[status(thm)],[c_3]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_1151,plain,
% 11.75/1.99      ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.75/1.99      | m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 11.75/1.99      | l1_pre_topc(sK0) != iProver_top ),
% 11.75/1.99      inference(predicate_to_equality,[status(thm)],[c_1150]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_6138,plain,
% 11.75/1.99      ( r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = iProver_top
% 11.75/1.99      | r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != iProver_top
% 11.75/1.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 11.75/1.99      inference(global_propositional_subsumption,
% 11.75/1.99                [status(thm)],
% 11.75/1.99                [c_5660,c_25,c_26,c_957,c_1151]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_6139,plain,
% 11.75/1.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.75/1.99      | r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != iProver_top
% 11.75/1.99      | r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = iProver_top ),
% 11.75/1.99      inference(renaming,[status(thm)],[c_6138]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_2065,plain,
% 11.75/1.99      ( k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)) = k2_pre_topc(sK0,sK1)
% 11.75/1.99      | l1_pre_topc(sK0) != iProver_top ),
% 11.75/1.99      inference(superposition,[status(thm)],[c_718,c_734]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_997,plain,
% 11.75/1.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.75/1.99      | ~ l1_pre_topc(sK0)
% 11.75/1.99      | k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 11.75/1.99      inference(instantiation,[status(thm)],[c_4]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_2090,plain,
% 11.75/1.99      ( k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 11.75/1.99      inference(global_propositional_subsumption,
% 11.75/1.99                [status(thm)],
% 11.75/1.99                [c_2065,c_22,c_21,c_997]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_3874,plain,
% 11.75/1.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.75/1.99      | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.75/1.99      | r1_tarski(X0,k2_pre_topc(sK0,sK1)) != iProver_top
% 11.75/1.99      | r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,sK1)) = iProver_top
% 11.75/1.99      | l1_pre_topc(sK0) != iProver_top ),
% 11.75/1.99      inference(superposition,[status(thm)],[c_2090,c_733]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_953,plain,
% 11.75/1.99      ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 11.75/1.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.75/1.99      | ~ l1_pre_topc(sK0) ),
% 11.75/1.99      inference(instantiation,[status(thm)],[c_3]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_954,plain,
% 11.75/1.99      ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 11.75/1.99      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.75/1.99      | l1_pre_topc(sK0) != iProver_top ),
% 11.75/1.99      inference(predicate_to_equality,[status(thm)],[c_953]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_4572,plain,
% 11.75/1.99      ( r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,sK1)) = iProver_top
% 11.75/1.99      | r1_tarski(X0,k2_pre_topc(sK0,sK1)) != iProver_top
% 11.75/1.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 11.75/1.99      inference(global_propositional_subsumption,
% 11.75/1.99                [status(thm)],
% 11.75/1.99                [c_3874,c_25,c_26,c_954]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_4573,plain,
% 11.75/1.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.75/1.99      | r1_tarski(X0,k2_pre_topc(sK0,sK1)) != iProver_top
% 11.75/1.99      | r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,sK1)) = iProver_top ),
% 11.75/1.99      inference(renaming,[status(thm)],[c_4572]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_3873,plain,
% 11.75/1.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.75/1.99      | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.75/1.99      | r1_tarski(k2_pre_topc(sK0,sK1),X0) != iProver_top
% 11.75/1.99      | r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X0)) = iProver_top
% 11.75/1.99      | l1_pre_topc(sK0) != iProver_top ),
% 11.75/1.99      inference(superposition,[status(thm)],[c_2090,c_733]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_4321,plain,
% 11.75/1.99      ( r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X0)) = iProver_top
% 11.75/1.99      | r1_tarski(k2_pre_topc(sK0,sK1),X0) != iProver_top
% 11.75/1.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 11.75/1.99      inference(global_propositional_subsumption,
% 11.75/1.99                [status(thm)],
% 11.75/1.99                [c_3873,c_25,c_26,c_954]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_4322,plain,
% 11.75/1.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.75/1.99      | r1_tarski(k2_pre_topc(sK0,sK1),X0) != iProver_top
% 11.75/1.99      | r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X0)) = iProver_top ),
% 11.75/1.99      inference(renaming,[status(thm)],[c_4321]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_0,plain,
% 11.75/1.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 11.75/1.99      inference(cnf_transformation,[],[f51]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_737,plain,
% 11.75/1.99      ( X0 = X1
% 11.75/1.99      | r1_tarski(X0,X1) != iProver_top
% 11.75/1.99      | r1_tarski(X1,X0) != iProver_top ),
% 11.75/1.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_4331,plain,
% 11.75/1.99      ( k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,sK1)
% 11.75/1.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.75/1.99      | r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,sK1)) != iProver_top
% 11.75/1.99      | r1_tarski(k2_pre_topc(sK0,sK1),X0) != iProver_top ),
% 11.75/1.99      inference(superposition,[status(thm)],[c_4322,c_737]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_6653,plain,
% 11.75/1.99      ( k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,sK1)
% 11.75/1.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.75/1.99      | r1_tarski(X0,k2_pre_topc(sK0,sK1)) != iProver_top
% 11.75/1.99      | r1_tarski(k2_pre_topc(sK0,sK1),X0) != iProver_top ),
% 11.75/1.99      inference(superposition,[status(thm)],[c_4573,c_4331]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_322,plain,
% 11.75/1.99      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 11.75/1.99      theory(equality) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_1134,plain,
% 11.75/1.99      ( m1_subset_1(X0,X1)
% 11.75/1.99      | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 11.75/1.99      | X0 != k2_pre_topc(sK0,sK1)
% 11.75/1.99      | X1 != k1_zfmisc_1(u1_struct_0(sK0)) ),
% 11.75/1.99      inference(instantiation,[status(thm)],[c_322]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_2357,plain,
% 11.75/1.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.75/1.99      | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 11.75/1.99      | X0 != k2_pre_topc(sK0,sK1)
% 11.75/1.99      | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(u1_struct_0(sK0)) ),
% 11.75/1.99      inference(instantiation,[status(thm)],[c_1134]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_2359,plain,
% 11.75/1.99      ( X0 != k2_pre_topc(sK0,sK1)
% 11.75/1.99      | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(u1_struct_0(sK0))
% 11.75/1.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 11.75/1.99      | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 11.75/1.99      inference(predicate_to_equality,[status(thm)],[c_2357]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_316,plain,( X0 = X0 ),theory(equality) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_2358,plain,
% 11.75/1.99      ( k1_zfmisc_1(u1_struct_0(sK0)) = k1_zfmisc_1(u1_struct_0(sK0)) ),
% 11.75/1.99      inference(instantiation,[status(thm)],[c_316]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_6105,plain,
% 11.75/1.99      ( ~ r1_tarski(X0,k2_pre_topc(sK0,sK1))
% 11.75/1.99      | ~ r1_tarski(k2_pre_topc(sK0,sK1),X0)
% 11.75/1.99      | X0 = k2_pre_topc(sK0,sK1) ),
% 11.75/1.99      inference(instantiation,[status(thm)],[c_0]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_6106,plain,
% 11.75/1.99      ( X0 = k2_pre_topc(sK0,sK1)
% 11.75/1.99      | r1_tarski(X0,k2_pre_topc(sK0,sK1)) != iProver_top
% 11.75/1.99      | r1_tarski(k2_pre_topc(sK0,sK1),X0) != iProver_top ),
% 11.75/1.99      inference(predicate_to_equality,[status(thm)],[c_6105]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_7778,plain,
% 11.75/1.99      ( k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,sK1)
% 11.75/1.99      | r1_tarski(X0,k2_pre_topc(sK0,sK1)) != iProver_top
% 11.75/1.99      | r1_tarski(k2_pre_topc(sK0,sK1),X0) != iProver_top ),
% 11.75/1.99      inference(global_propositional_subsumption,
% 11.75/1.99                [status(thm)],
% 11.75/1.99                [c_6653,c_25,c_26,c_954,c_2359,c_2358,c_6106]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_7788,plain,
% 11.75/1.99      ( k2_pre_topc(sK0,k2_pre_topc(sK0,X0)) = k2_pre_topc(sK0,sK1)
% 11.75/1.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.75/1.99      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.75/1.99      | r1_tarski(X0,sK1) != iProver_top
% 11.75/1.99      | r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X0)) != iProver_top
% 11.75/1.99      | l1_pre_topc(sK0) != iProver_top ),
% 11.75/1.99      inference(superposition,[status(thm)],[c_733,c_7778]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_33691,plain,
% 11.75/1.99      ( r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X0)) != iProver_top
% 11.75/1.99      | r1_tarski(X0,sK1) != iProver_top
% 11.75/1.99      | k2_pre_topc(sK0,k2_pre_topc(sK0,X0)) = k2_pre_topc(sK0,sK1)
% 11.75/1.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 11.75/1.99      inference(global_propositional_subsumption,
% 11.75/1.99                [status(thm)],
% 11.75/1.99                [c_7788,c_25,c_26]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_33692,plain,
% 11.75/1.99      ( k2_pre_topc(sK0,k2_pre_topc(sK0,X0)) = k2_pre_topc(sK0,sK1)
% 11.75/1.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.75/1.99      | r1_tarski(X0,sK1) != iProver_top
% 11.75/1.99      | r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X0)) != iProver_top ),
% 11.75/1.99      inference(renaming,[status(thm)],[c_33691]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_33705,plain,
% 11.75/1.99      ( k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = k2_pre_topc(sK0,sK1)
% 11.75/1.99      | m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.75/1.99      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.75/1.99      | r1_tarski(k1_tops_1(sK0,sK1),sK1) != iProver_top
% 11.75/1.99      | r1_tarski(sK1,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != iProver_top ),
% 11.75/1.99      inference(superposition,[status(thm)],[c_6139,c_33692]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_33892,plain,
% 11.75/1.99      ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
% 11.75/1.99      | m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.75/1.99      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.75/1.99      | r1_tarski(k1_tops_1(sK0,sK1),sK1) != iProver_top
% 11.75/1.99      | r1_tarski(sK1,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != iProver_top ),
% 11.75/1.99      inference(demodulation,[status(thm)],[c_33705,c_5651]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_20,negated_conjecture,
% 11.75/1.99      ( v4_tops_1(sK1,sK0) ),
% 11.75/1.99      inference(cnf_transformation,[],[f71]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_27,plain,
% 11.75/1.99      ( v4_tops_1(sK1,sK0) = iProver_top ),
% 11.75/1.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_14,plain,
% 11.75/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.75/1.99      | r1_tarski(k1_tops_1(X1,X0),X0)
% 11.75/1.99      | ~ l1_pre_topc(X1) ),
% 11.75/1.99      inference(cnf_transformation,[],[f63]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_962,plain,
% 11.75/1.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.75/1.99      | r1_tarski(k1_tops_1(sK0,sK1),sK1)
% 11.75/1.99      | ~ l1_pre_topc(sK0) ),
% 11.75/1.99      inference(instantiation,[status(thm)],[c_14]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_963,plain,
% 11.75/1.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.75/1.99      | r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top
% 11.75/1.99      | l1_pre_topc(sK0) != iProver_top ),
% 11.75/1.99      inference(predicate_to_equality,[status(thm)],[c_962]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_7,plain,
% 11.75/1.99      ( ~ v4_tops_1(X0,X1)
% 11.75/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.75/1.99      | r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
% 11.75/1.99      | ~ l1_pre_topc(X1) ),
% 11.75/1.99      inference(cnf_transformation,[],[f56]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_1041,plain,
% 11.75/1.99      ( ~ v4_tops_1(sK1,sK0)
% 11.75/1.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.75/1.99      | r1_tarski(sK1,k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))
% 11.75/1.99      | ~ l1_pre_topc(sK0) ),
% 11.75/1.99      inference(instantiation,[status(thm)],[c_7]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_1042,plain,
% 11.75/1.99      ( v4_tops_1(sK1,sK0) != iProver_top
% 11.75/1.99      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.75/1.99      | r1_tarski(sK1,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = iProver_top
% 11.75/1.99      | l1_pre_topc(sK0) != iProver_top ),
% 11.75/1.99      inference(predicate_to_equality,[status(thm)],[c_1041]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_35513,plain,
% 11.75/1.99      ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 11.75/1.99      inference(global_propositional_subsumption,
% 11.75/1.99                [status(thm)],
% 11.75/1.99                [c_33892,c_25,c_26,c_27,c_957,c_963,c_1042]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_12,plain,
% 11.75/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.75/1.99      | ~ l1_pre_topc(X1)
% 11.75/1.99      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
% 11.75/1.99      inference(cnf_transformation,[],[f61]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_726,plain,
% 11.75/1.99      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
% 11.75/1.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 11.75/1.99      | l1_pre_topc(X0) != iProver_top ),
% 11.75/1.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_2601,plain,
% 11.75/1.99      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k1_tops_1(X0,X1)),k1_tops_1(X0,k1_tops_1(X0,X1))) = k2_tops_1(X0,k1_tops_1(X0,X1))
% 11.75/1.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 11.75/1.99      | l1_pre_topc(X0) != iProver_top ),
% 11.75/1.99      inference(superposition,[status(thm)],[c_729,c_726]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_11632,plain,
% 11.75/1.99      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,k1_tops_1(sK0,sK1))) = k2_tops_1(sK0,k1_tops_1(sK0,sK1))
% 11.75/1.99      | l1_pre_topc(sK0) != iProver_top ),
% 11.75/1.99      inference(superposition,[status(thm)],[c_718,c_2601]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_13,plain,
% 11.75/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.75/1.99      | ~ l1_pre_topc(X1)
% 11.75/1.99      | k1_tops_1(X1,k1_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
% 11.75/1.99      inference(cnf_transformation,[],[f62]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_725,plain,
% 11.75/1.99      ( k1_tops_1(X0,k1_tops_1(X0,X1)) = k1_tops_1(X0,X1)
% 11.75/1.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 11.75/1.99      | l1_pre_topc(X0) != iProver_top ),
% 11.75/1.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_1265,plain,
% 11.75/1.99      ( k1_tops_1(sK0,k1_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1)
% 11.75/1.99      | l1_pre_topc(sK0) != iProver_top ),
% 11.75/1.99      inference(superposition,[status(thm)],[c_718,c_725]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_1000,plain,
% 11.75/1.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.75/1.99      | ~ l1_pre_topc(sK0)
% 11.75/1.99      | k1_tops_1(sK0,k1_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
% 11.75/1.99      inference(instantiation,[status(thm)],[c_13]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_1605,plain,
% 11.75/1.99      ( k1_tops_1(sK0,k1_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
% 11.75/1.99      inference(global_propositional_subsumption,
% 11.75/1.99                [status(thm)],
% 11.75/1.99                [c_1265,c_22,c_21,c_1000]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_11635,plain,
% 11.75/1.99      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,k1_tops_1(sK0,sK1))
% 11.75/1.99      | l1_pre_topc(sK0) != iProver_top ),
% 11.75/1.99      inference(light_normalisation,[status(thm)],[c_11632,c_1605]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_12188,plain,
% 11.75/1.99      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,k1_tops_1(sK0,sK1)) ),
% 11.75/1.99      inference(global_propositional_subsumption,
% 11.75/1.99                [status(thm)],
% 11.75/1.99                [c_11635,c_25]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_35537,plain,
% 11.75/1.99      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,k1_tops_1(sK0,sK1)) ),
% 11.75/1.99      inference(demodulation,[status(thm)],[c_35513,c_12188]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_2603,plain,
% 11.75/1.99      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 11.75/1.99      | l1_pre_topc(sK0) != iProver_top ),
% 11.75/1.99      inference(superposition,[status(thm)],[c_718,c_726]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_1047,plain,
% 11.75/1.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.75/1.99      | ~ l1_pre_topc(sK0)
% 11.75/1.99      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 11.75/1.99      inference(instantiation,[status(thm)],[c_12]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_3084,plain,
% 11.75/1.99      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 11.75/1.99      inference(global_propositional_subsumption,
% 11.75/1.99                [status(thm)],
% 11.75/1.99                [c_2603,c_22,c_21,c_1047]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_35558,plain,
% 11.75/1.99      ( k2_tops_1(sK0,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 11.75/1.99      inference(light_normalisation,[status(thm)],[c_35537,c_3084]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_10,plain,
% 11.75/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.75/1.99      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 11.75/1.99      | ~ l1_pre_topc(X1) ),
% 11.75/1.99      inference(cnf_transformation,[],[f59]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_728,plain,
% 11.75/1.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 11.75/1.99      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 11.75/1.99      | l1_pre_topc(X1) != iProver_top ),
% 11.75/1.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_1343,plain,
% 11.75/1.99      ( k1_tops_1(X0,k1_tops_1(X0,k2_tops_1(X0,X1))) = k1_tops_1(X0,k2_tops_1(X0,X1))
% 11.75/1.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 11.75/1.99      | l1_pre_topc(X0) != iProver_top ),
% 11.75/1.99      inference(superposition,[status(thm)],[c_728,c_725]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_4070,plain,
% 11.75/1.99      ( k1_tops_1(X0,k1_tops_1(X0,k2_tops_1(X0,k1_tops_1(X0,X1)))) = k1_tops_1(X0,k2_tops_1(X0,k1_tops_1(X0,X1)))
% 11.75/1.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 11.75/1.99      | l1_pre_topc(X0) != iProver_top ),
% 11.75/1.99      inference(superposition,[status(thm)],[c_729,c_1343]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_10276,plain,
% 11.75/1.99      ( k1_tops_1(sK0,k1_tops_1(sK0,k2_tops_1(sK0,k1_tops_1(sK0,sK1)))) = k1_tops_1(sK0,k2_tops_1(sK0,k1_tops_1(sK0,sK1)))
% 11.75/1.99      | l1_pre_topc(sK0) != iProver_top ),
% 11.75/1.99      inference(superposition,[status(thm)],[c_718,c_4070]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_1148,plain,
% 11.75/1.99      ( m1_subset_1(k2_tops_1(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
% 11.75/1.99      | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 11.75/1.99      | ~ l1_pre_topc(sK0) ),
% 11.75/1.99      inference(instantiation,[status(thm)],[c_10]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_1639,plain,
% 11.75/1.99      ( ~ m1_subset_1(k2_tops_1(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
% 11.75/1.99      | ~ l1_pre_topc(sK0)
% 11.75/1.99      | k1_tops_1(sK0,k1_tops_1(sK0,k2_tops_1(sK0,k1_tops_1(sK0,sK1)))) = k1_tops_1(sK0,k2_tops_1(sK0,k1_tops_1(sK0,sK1))) ),
% 11.75/1.99      inference(instantiation,[status(thm)],[c_13]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_10428,plain,
% 11.75/1.99      ( k1_tops_1(sK0,k1_tops_1(sK0,k2_tops_1(sK0,k1_tops_1(sK0,sK1)))) = k1_tops_1(sK0,k2_tops_1(sK0,k1_tops_1(sK0,sK1))) ),
% 11.75/1.99      inference(global_propositional_subsumption,
% 11.75/1.99                [status(thm)],
% 11.75/1.99                [c_10276,c_22,c_21,c_956,c_1148,c_1639]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_15,plain,
% 11.75/1.99      ( v2_tops_1(X0,X1)
% 11.75/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.75/1.99      | ~ l1_pre_topc(X1)
% 11.75/1.99      | k1_tops_1(X1,X0) != k1_xboole_0 ),
% 11.75/1.99      inference(cnf_transformation,[],[f65]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_723,plain,
% 11.75/1.99      ( k1_tops_1(X0,X1) != k1_xboole_0
% 11.75/1.99      | v2_tops_1(X1,X0) = iProver_top
% 11.75/1.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 11.75/1.99      | l1_pre_topc(X0) != iProver_top ),
% 11.75/1.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_10434,plain,
% 11.75/1.99      ( k1_tops_1(sK0,k2_tops_1(sK0,k1_tops_1(sK0,sK1))) != k1_xboole_0
% 11.75/1.99      | v2_tops_1(k1_tops_1(sK0,k2_tops_1(sK0,k1_tops_1(sK0,sK1))),sK0) = iProver_top
% 11.75/1.99      | m1_subset_1(k1_tops_1(sK0,k2_tops_1(sK0,k1_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.75/1.99      | l1_pre_topc(sK0) != iProver_top ),
% 11.75/1.99      inference(superposition,[status(thm)],[c_10428,c_723]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_23,negated_conjecture,
% 11.75/1.99      ( v2_pre_topc(sK0) ),
% 11.75/1.99      inference(cnf_transformation,[],[f68]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_11,plain,
% 11.75/1.99      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 11.75/1.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 11.75/1.99      | ~ v2_pre_topc(X0)
% 11.75/1.99      | ~ l1_pre_topc(X0) ),
% 11.75/1.99      inference(cnf_transformation,[],[f60]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_967,plain,
% 11.75/1.99      ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
% 11.75/1.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.75/1.99      | ~ v2_pre_topc(sK0)
% 11.75/1.99      | ~ l1_pre_topc(sK0) ),
% 11.75/1.99      inference(instantiation,[status(thm)],[c_11]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_1155,plain,
% 11.75/1.99      ( m1_subset_1(k2_tops_1(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 11.75/1.99      | m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.75/1.99      | l1_pre_topc(sK0) != iProver_top ),
% 11.75/1.99      inference(predicate_to_equality,[status(thm)],[c_1148]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_18,plain,
% 11.75/1.99      ( v3_tops_1(k2_tops_1(X0,X1),X0)
% 11.75/1.99      | ~ v3_pre_topc(X1,X0)
% 11.75/1.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 11.75/1.99      | ~ v2_pre_topc(X0)
% 11.75/1.99      | ~ l1_pre_topc(X0) ),
% 11.75/1.99      inference(cnf_transformation,[],[f67]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_1242,plain,
% 11.75/1.99      ( v3_tops_1(k2_tops_1(sK0,k1_tops_1(sK0,sK1)),sK0)
% 11.75/1.99      | ~ v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
% 11.75/1.99      | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 11.75/1.99      | ~ v2_pre_topc(sK0)
% 11.75/1.99      | ~ l1_pre_topc(sK0) ),
% 11.75/1.99      inference(instantiation,[status(thm)],[c_18]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_1644,plain,
% 11.75/1.99      ( ~ m1_subset_1(k2_tops_1(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
% 11.75/1.99      | m1_subset_1(k1_tops_1(sK0,k2_tops_1(sK0,k1_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
% 11.75/1.99      | ~ l1_pre_topc(sK0) ),
% 11.75/1.99      inference(instantiation,[status(thm)],[c_9]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_1648,plain,
% 11.75/1.99      ( m1_subset_1(k2_tops_1(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.75/1.99      | m1_subset_1(k1_tops_1(sK0,k2_tops_1(sK0,k1_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 11.75/1.99      | l1_pre_topc(sK0) != iProver_top ),
% 11.75/1.99      inference(predicate_to_equality,[status(thm)],[c_1644]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_17,plain,
% 11.75/1.99      ( ~ v3_tops_1(X0,X1)
% 11.75/1.99      | v2_tops_1(X0,X1)
% 11.75/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.75/1.99      | ~ l1_pre_topc(X1) ),
% 11.75/1.99      inference(cnf_transformation,[],[f66]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_2045,plain,
% 11.75/1.99      ( ~ v3_tops_1(k2_tops_1(sK0,k1_tops_1(sK0,sK1)),sK0)
% 11.75/1.99      | v2_tops_1(k2_tops_1(sK0,k1_tops_1(sK0,sK1)),sK0)
% 11.75/1.99      | ~ m1_subset_1(k2_tops_1(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
% 11.75/1.99      | ~ l1_pre_topc(sK0) ),
% 11.75/1.99      inference(instantiation,[status(thm)],[c_17]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_16,plain,
% 11.75/1.99      ( ~ v2_tops_1(X0,X1)
% 11.75/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.75/1.99      | ~ l1_pre_topc(X1)
% 11.75/1.99      | k1_tops_1(X1,X0) = k1_xboole_0 ),
% 11.75/1.99      inference(cnf_transformation,[],[f64]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_3501,plain,
% 11.75/1.99      ( ~ v2_tops_1(k2_tops_1(sK0,k1_tops_1(sK0,sK1)),sK0)
% 11.75/1.99      | ~ m1_subset_1(k2_tops_1(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
% 11.75/1.99      | ~ l1_pre_topc(sK0)
% 11.75/1.99      | k1_tops_1(sK0,k2_tops_1(sK0,k1_tops_1(sK0,sK1))) = k1_xboole_0 ),
% 11.75/1.99      inference(instantiation,[status(thm)],[c_16]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_11469,plain,
% 11.75/1.99      ( v2_tops_1(k1_tops_1(sK0,k2_tops_1(sK0,k1_tops_1(sK0,sK1))),sK0) = iProver_top ),
% 11.75/1.99      inference(global_propositional_subsumption,
% 11.75/1.99                [status(thm)],
% 11.75/1.99                [c_10434,c_23,c_22,c_25,c_21,c_26,c_956,c_957,c_967,
% 11.75/1.99                 c_1148,c_1155,c_1242,c_1648,c_2045,c_3501]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_722,plain,
% 11.75/1.99      ( k1_tops_1(X0,X1) = k1_xboole_0
% 11.75/1.99      | v2_tops_1(X1,X0) != iProver_top
% 11.75/1.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 11.75/1.99      | l1_pre_topc(X0) != iProver_top ),
% 11.75/1.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_2410,plain,
% 11.75/1.99      ( k1_tops_1(X0,k1_tops_1(X0,X1)) = k1_xboole_0
% 11.75/1.99      | v2_tops_1(k1_tops_1(X0,X1),X0) != iProver_top
% 11.75/1.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 11.75/1.99      | l1_pre_topc(X0) != iProver_top ),
% 11.75/1.99      inference(superposition,[status(thm)],[c_729,c_722]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_11474,plain,
% 11.75/1.99      ( k1_tops_1(sK0,k1_tops_1(sK0,k2_tops_1(sK0,k1_tops_1(sK0,sK1)))) = k1_xboole_0
% 11.75/1.99      | m1_subset_1(k2_tops_1(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.75/1.99      | l1_pre_topc(sK0) != iProver_top ),
% 11.75/1.99      inference(superposition,[status(thm)],[c_11469,c_2410]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_11475,plain,
% 11.75/1.99      ( k1_tops_1(sK0,k2_tops_1(sK0,k1_tops_1(sK0,sK1))) = k1_xboole_0
% 11.75/1.99      | m1_subset_1(k2_tops_1(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.75/1.99      | l1_pre_topc(sK0) != iProver_top ),
% 11.75/1.99      inference(demodulation,[status(thm)],[c_11474,c_10428]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_11478,plain,
% 11.75/1.99      ( k1_tops_1(sK0,k2_tops_1(sK0,k1_tops_1(sK0,sK1))) = k1_xboole_0 ),
% 11.75/1.99      inference(global_propositional_subsumption,
% 11.75/1.99                [status(thm)],
% 11.75/1.99                [c_11475,c_23,c_22,c_21,c_956,c_967,c_1148,c_1242,c_2045,
% 11.75/1.99                 c_3501]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_35942,plain,
% 11.75/1.99      ( k1_tops_1(sK0,k2_tops_1(sK0,sK1)) = k1_xboole_0 ),
% 11.75/1.99      inference(demodulation,[status(thm)],[c_35558,c_11478]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(c_19,negated_conjecture,
% 11.75/1.99      ( k1_tops_1(sK0,k2_tops_1(sK0,sK1)) != k1_xboole_0 ),
% 11.75/1.99      inference(cnf_transformation,[],[f72]) ).
% 11.75/1.99  
% 11.75/1.99  cnf(contradiction,plain,
% 11.75/1.99      ( $false ),
% 11.75/1.99      inference(minisat,[status(thm)],[c_35942,c_19]) ).
% 11.75/1.99  
% 11.75/1.99  
% 11.75/1.99  % SZS output end CNFRefutation for theBenchmark.p
% 11.75/1.99  
% 11.75/1.99  ------                               Statistics
% 11.75/1.99  
% 11.75/1.99  ------ Selected
% 11.75/1.99  
% 11.75/1.99  total_time:                             1.292
% 11.75/1.99  
%------------------------------------------------------------------------------
