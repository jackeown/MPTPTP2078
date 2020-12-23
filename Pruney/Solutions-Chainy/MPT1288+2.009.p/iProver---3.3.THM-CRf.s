%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:15:57 EST 2020

% Result     : Theorem 11.86s
% Output     : CNFRefutation 11.86s
% Verified   : 
% Statistics : Number of formulae       :  186 (1177 expanded)
%              Number of clauses        :  114 ( 354 expanded)
%              Number of leaves         :   20 ( 277 expanded)
%              Depth                    :   25
%              Number of atoms          :  632 (4743 expanded)
%              Number of equality atoms :  273 (1230 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal clause size      :   10 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_tops_1(X1,X0)
           => k1_tops_1(X0,k2_tops_1(X0,X1)) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_tops_1(X1,X0)
             => k1_tops_1(X0,k2_tops_1(X0,X1)) = k1_xboole_0 ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f43,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_tops_1(X0,k2_tops_1(X0,X1)) != k1_xboole_0
          & v4_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f44,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_tops_1(X0,k2_tops_1(X0,X1)) != k1_xboole_0
          & v4_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f43])).

fof(f51,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k1_tops_1(X0,k2_tops_1(X0,X1)) != k1_xboole_0
          & v4_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k1_tops_1(X0,k2_tops_1(X0,sK1)) != k1_xboole_0
        & v4_tops_1(sK1,X0)
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
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

fof(f52,plain,
    ( k1_tops_1(sK0,k2_tops_1(sK0,sK1)) != k1_xboole_0
    & v4_tops_1(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f44,f51,f50])).

fof(f75,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f52])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f3,axiom,(
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
    inference(ennf_transformation,[],[f3])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f74,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f56,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f45])).

fof(f55,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f76,plain,(
    v4_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_tops_1(X1,X0)
          <=> ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_tops_1(X1,X0)
          <=> ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f47,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f48,plain,(
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
    inference(flattening,[],[f47])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
      | ~ v4_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
           => v3_tops_1(k2_tops_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tops_1(k2_tops_1(X0,X1),X0)
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tops_1(k2_tops_1(X0,X1),X0)
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f41])).

fof(f72,plain,(
    ! [X0,X1] :
      ( v3_tops_1(k2_tops_1(X0,X1),X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f73,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => ( v3_tops_1(X1,X0)
            <=> k2_tops_1(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tops_1(X1,X0)
          <=> k2_tops_1(X0,X1) = X1 )
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tops_1(X1,X0)
          <=> k2_tops_1(X0,X1) = X1 )
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f39])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tops_1(X1,X0)
              | k2_tops_1(X0,X1) != X1 )
            & ( k2_tops_1(X0,X1) = X1
              | ~ v3_tops_1(X1,X0) ) )
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = X1
      | ~ v3_tops_1(X1,X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) = k1_xboole_0
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) = k1_xboole_0
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) = k1_xboole_0
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f77,plain,(
    k1_tops_1(sK0,k2_tops_1(sK0,sK1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_760,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_772,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k2_pre_topc(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_777,plain,
    ( k2_pre_topc(X0,k2_pre_topc(X0,X1)) = k2_pre_topc(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2051,plain,
    ( k2_pre_topc(X0,k2_pre_topc(X0,k1_tops_1(X0,X1))) = k2_pre_topc(X0,k1_tops_1(X0,X1))
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_772,c_777])).

cnf(c_8349,plain,
    ( k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = k2_pre_topc(sK0,k1_tops_1(sK0,sK1))
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_760,c_2051])).

cnf(c_23,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1014,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1213,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_8510,plain,
    ( k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8349,c_23,c_22,c_1014,c_1213])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k2_pre_topc(X1,X0),k2_pre_topc(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_776,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(k2_pre_topc(X1,X0),k2_pre_topc(X1,X2)) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2053,plain,
    ( k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)) = k2_pre_topc(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_760,c_777])).

cnf(c_1055,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2078,plain,
    ( k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2053,c_23,c_22,c_1055])).

cnf(c_3925,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK0,sK1)) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,sK1)) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2078,c_776])).

cnf(c_26,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_27,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1011,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1012,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1011])).

cnf(c_4730,plain,
    ( r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,sK1)) = iProver_top
    | r1_tarski(X0,k2_pre_topc(sK0,sK1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3925,c_26,c_27,c_1012])).

cnf(c_4731,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK0,sK1)) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,sK1)) = iProver_top ),
    inference(renaming,[status(thm)],[c_4730])).

cnf(c_3923,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,sK1),X0) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X0)) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2078,c_776])).

cnf(c_4494,plain,
    ( r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X0)) = iProver_top
    | r1_tarski(k2_pre_topc(sK0,sK1),X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3923,c_26,c_27,c_1012])).

cnf(c_4495,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,sK1),X0) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_4494])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_780,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4505,plain,
    ( k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,sK1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,sK1)) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,sK1),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4495,c_780])).

cnf(c_6480,plain,
    ( k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,sK1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK0,sK1)) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,sK1),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4731,c_4505])).

cnf(c_337,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1198,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | X0 != k2_pre_topc(sK0,sK1)
    | X1 != k1_zfmisc_1(u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_337])).

cnf(c_2653,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | X0 != k2_pre_topc(sK0,sK1)
    | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1198])).

cnf(c_2655,plain,
    ( X0 != k2_pre_topc(sK0,sK1)
    | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(u1_struct_0(sK0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2653])).

cnf(c_331,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2654,plain,
    ( k1_zfmisc_1(u1_struct_0(sK0)) = k1_zfmisc_1(u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_331])).

cnf(c_6583,plain,
    ( ~ r1_tarski(X0,k2_pre_topc(sK0,sK1))
    | ~ r1_tarski(k2_pre_topc(sK0,sK1),X0)
    | X0 = k2_pre_topc(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_6584,plain,
    ( X0 = k2_pre_topc(sK0,sK1)
    | r1_tarski(X0,k2_pre_topc(sK0,sK1)) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,sK1),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6583])).

cnf(c_7462,plain,
    ( k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,sK1)
    | r1_tarski(X0,k2_pre_topc(sK0,sK1)) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,sK1),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6480,c_26,c_27,c_1012,c_2655,c_2654,c_6584])).

cnf(c_7472,plain,
    ( k2_pre_topc(sK0,k2_pre_topc(sK0,X0)) = k2_pre_topc(sK0,sK1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X0)) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_776,c_7462])).

cnf(c_41681,plain,
    ( r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X0)) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top
    | k2_pre_topc(sK0,k2_pre_topc(sK0,X0)) = k2_pre_topc(sK0,sK1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7472,c_26,c_27])).

cnf(c_41682,plain,
    ( k2_pre_topc(sK0,k2_pre_topc(sK0,X0)) = k2_pre_topc(sK0,sK1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_41681])).

cnf(c_41704,plain,
    ( k2_pre_topc(sK0,k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))) = k2_pre_topc(sK0,sK1)
    | m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),sK1) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8510,c_41682])).

cnf(c_41819,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
    | m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),sK1) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_41704,c_8510])).

cnf(c_21,negated_conjecture,
    ( v4_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_28,plain,
    ( v4_tops_1(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1015,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1014])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1020,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1021,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1020])).

cnf(c_7,plain,
    ( ~ v4_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1102,plain,
    ( ~ v4_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK1,k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1103,plain,
    ( v4_tops_1(sK1,sK0) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK1,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1102])).

cnf(c_8519,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8510,c_776])).

cnf(c_1217,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1218,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1217])).

cnf(c_8979,plain,
    ( r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = iProver_top
    | r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8519,c_26,c_27,c_1015,c_1218])).

cnf(c_8980,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = iProver_top ),
    inference(renaming,[status(thm)],[c_8979])).

cnf(c_41695,plain,
    ( k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = k2_pre_topc(sK0,sK1)
    | m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),sK1) != iProver_top
    | r1_tarski(sK1,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8980,c_41682])).

cnf(c_41908,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
    | m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),sK1) != iProver_top
    | r1_tarski(sK1,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_41695,c_8510])).

cnf(c_43124,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_41819,c_26,c_27,c_28,c_1015,c_1021,c_1103,c_41908])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_768,plain,
    ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2497,plain,
    ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k1_tops_1(X0,X1)),k1_tops_1(X0,k1_tops_1(X0,X1))) = k2_tops_1(X0,k1_tops_1(X0,X1))
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_772,c_768])).

cnf(c_17389,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,k1_tops_1(sK0,sK1))) = k2_tops_1(sK0,k1_tops_1(sK0,sK1))
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_760,c_2497])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,k1_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_766,plain,
    ( k1_tops_1(X0,k1_tops_1(X0,X1)) = k1_tops_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1345,plain,
    ( k1_tops_1(sK0,k1_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_760,c_766])).

cnf(c_1061,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k1_tops_1(sK0,k1_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1695,plain,
    ( k1_tops_1(sK0,k1_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1345,c_23,c_22,c_1061])).

cnf(c_17398,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,k1_tops_1(sK0,sK1))
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_17389,c_1695])).

cnf(c_18287,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,k1_tops_1(sK0,sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_17398,c_26])).

cnf(c_43150,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,k1_tops_1(sK0,sK1)) ),
    inference(demodulation,[status(thm)],[c_43124,c_18287])).

cnf(c_2499,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_760,c_768])).

cnf(c_1108,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_2940,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2499,c_23,c_22,c_1108])).

cnf(c_43170,plain,
    ( k2_tops_1(sK0,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_43150,c_2940])).

cnf(c_19,plain,
    ( v3_tops_1(k2_tops_1(X0,X1),X0)
    | ~ v3_pre_topc(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_762,plain,
    ( v3_tops_1(k2_tops_1(X0,X1),X0) = iProver_top
    | v3_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1468,plain,
    ( v3_tops_1(k2_tops_1(X0,k1_tops_1(X0,X1)),X0) = iProver_top
    | v3_pre_topc(k1_tops_1(X0,X1),X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_772,c_762])).

cnf(c_12,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_50,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_9555,plain,
    ( v3_tops_1(k2_tops_1(X0,k1_tops_1(X0,X1)),X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1468,c_50])).

cnf(c_9566,plain,
    ( v3_tops_1(k2_tops_1(sK0,k1_tops_1(sK0,sK1)),sK0) = iProver_top
    | m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1695,c_9555])).

cnf(c_24,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_25,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_1052,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1053,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1052])).

cnf(c_1327,plain,
    ( v3_tops_1(k2_tops_1(sK0,k1_tops_1(sK0,sK1)),sK0)
    | ~ v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_1328,plain,
    ( v3_tops_1(k2_tops_1(sK0,k1_tops_1(sK0,sK1)),sK0) = iProver_top
    | v3_pre_topc(k1_tops_1(sK0,sK1),sK0) != iProver_top
    | m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1327])).

cnf(c_9981,plain,
    ( v3_tops_1(k2_tops_1(sK0,k1_tops_1(sK0,sK1)),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9566,c_25,c_26,c_27,c_1015,c_1053,c_1328])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_771,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_18,plain,
    ( ~ v3_tops_1(X0,X1)
    | ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_tops_1(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_763,plain,
    ( k2_tops_1(X0,X1) = X1
    | v3_tops_1(X1,X0) != iProver_top
    | v4_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2321,plain,
    ( k2_tops_1(X0,k2_tops_1(X0,X1)) = k2_tops_1(X0,X1)
    | v3_tops_1(k2_tops_1(X0,X1),X0) != iProver_top
    | v4_pre_topc(k2_tops_1(X0,X1),X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_771,c_763])).

cnf(c_13211,plain,
    ( k2_tops_1(sK0,k2_tops_1(sK0,k1_tops_1(sK0,sK1))) = k2_tops_1(sK0,k1_tops_1(sK0,sK1))
    | v4_pre_topc(k2_tops_1(sK0,k1_tops_1(sK0,sK1)),sK0) != iProver_top
    | m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9981,c_2321])).

cnf(c_11,plain,
    ( v4_pre_topc(k2_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1204,plain,
    ( v4_pre_topc(k2_tops_1(sK0,k1_tops_1(sK0,sK1)),sK0)
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1215,plain,
    ( m1_subset_1(k2_tops_1(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1719,plain,
    ( ~ v3_tops_1(k2_tops_1(sK0,k1_tops_1(sK0,sK1)),sK0)
    | ~ v4_pre_topc(k2_tops_1(sK0,k1_tops_1(sK0,sK1)),sK0)
    | ~ m1_subset_1(k2_tops_1(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k2_tops_1(sK0,k2_tops_1(sK0,k1_tops_1(sK0,sK1))) = k2_tops_1(sK0,k1_tops_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_37003,plain,
    ( k2_tops_1(sK0,k2_tops_1(sK0,k1_tops_1(sK0,sK1))) = k2_tops_1(sK0,k1_tops_1(sK0,sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13211,c_24,c_23,c_22,c_1014,c_1052,c_1204,c_1215,c_1327,c_1719])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,k2_tops_1(X1,k2_tops_1(X1,X0))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_767,plain,
    ( k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) = k1_xboole_0
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2750,plain,
    ( k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,k1_tops_1(X0,X1)))) = k1_xboole_0
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_772,c_767])).

cnf(c_11827,plain,
    ( k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,k1_tops_1(sK0,sK1)))) = k1_xboole_0
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_760,c_2750])).

cnf(c_1212,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,k1_tops_1(sK0,sK1)))) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_11909,plain,
    ( k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,k1_tops_1(sK0,sK1)))) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_11827,c_24,c_23,c_22,c_1014,c_1212])).

cnf(c_37014,plain,
    ( k1_tops_1(sK0,k2_tops_1(sK0,k1_tops_1(sK0,sK1))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_37003,c_11909])).

cnf(c_43544,plain,
    ( k1_tops_1(sK0,k2_tops_1(sK0,sK1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_43170,c_37014])).

cnf(c_20,negated_conjecture,
    ( k1_tops_1(sK0,k2_tops_1(sK0,sK1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f77])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_43544,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:10:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 11.86/2.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.86/2.01  
% 11.86/2.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.86/2.01  
% 11.86/2.01  ------  iProver source info
% 11.86/2.01  
% 11.86/2.01  git: date: 2020-06-30 10:37:57 +0100
% 11.86/2.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.86/2.01  git: non_committed_changes: false
% 11.86/2.01  git: last_make_outside_of_git: false
% 11.86/2.01  
% 11.86/2.01  ------ 
% 11.86/2.01  ------ Parsing...
% 11.86/2.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.86/2.01  
% 11.86/2.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 11.86/2.01  
% 11.86/2.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.86/2.01  
% 11.86/2.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.86/2.01  ------ Proving...
% 11.86/2.01  ------ Problem Properties 
% 11.86/2.01  
% 11.86/2.01  
% 11.86/2.01  clauses                                 24
% 11.86/2.01  conjectures                             5
% 11.86/2.01  EPR                                     5
% 11.86/2.01  Horn                                    24
% 11.86/2.01  unary                                   6
% 11.86/2.01  binary                                  0
% 11.86/2.01  lits                                    75
% 11.86/2.01  lits eq                                 8
% 11.86/2.01  fd_pure                                 0
% 11.86/2.01  fd_pseudo                               0
% 11.86/2.01  fd_cond                                 0
% 11.86/2.01  fd_pseudo_cond                          1
% 11.86/2.01  AC symbols                              0
% 11.86/2.01  
% 11.86/2.01  ------ Input Options Time Limit: Unbounded
% 11.86/2.01  
% 11.86/2.01  
% 11.86/2.01  ------ 
% 11.86/2.01  Current options:
% 11.86/2.01  ------ 
% 11.86/2.01  
% 11.86/2.01  
% 11.86/2.01  
% 11.86/2.01  
% 11.86/2.01  ------ Proving...
% 11.86/2.01  
% 11.86/2.01  
% 11.86/2.01  % SZS status Theorem for theBenchmark.p
% 11.86/2.01  
% 11.86/2.01  % SZS output start CNFRefutation for theBenchmark.p
% 11.86/2.01  
% 11.86/2.01  fof(f16,conjecture,(
% 11.86/2.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_tops_1(X1,X0) => k1_tops_1(X0,k2_tops_1(X0,X1)) = k1_xboole_0)))),
% 11.86/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.86/2.01  
% 11.86/2.01  fof(f17,negated_conjecture,(
% 11.86/2.01    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_tops_1(X1,X0) => k1_tops_1(X0,k2_tops_1(X0,X1)) = k1_xboole_0)))),
% 11.86/2.01    inference(negated_conjecture,[],[f16])).
% 11.86/2.01  
% 11.86/2.01  fof(f43,plain,(
% 11.86/2.01    ? [X0] : (? [X1] : ((k1_tops_1(X0,k2_tops_1(X0,X1)) != k1_xboole_0 & v4_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 11.86/2.01    inference(ennf_transformation,[],[f17])).
% 11.86/2.01  
% 11.86/2.01  fof(f44,plain,(
% 11.86/2.01    ? [X0] : (? [X1] : (k1_tops_1(X0,k2_tops_1(X0,X1)) != k1_xboole_0 & v4_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 11.86/2.01    inference(flattening,[],[f43])).
% 11.86/2.01  
% 11.86/2.01  fof(f51,plain,(
% 11.86/2.01    ( ! [X0] : (? [X1] : (k1_tops_1(X0,k2_tops_1(X0,X1)) != k1_xboole_0 & v4_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (k1_tops_1(X0,k2_tops_1(X0,sK1)) != k1_xboole_0 & v4_tops_1(sK1,X0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 11.86/2.01    introduced(choice_axiom,[])).
% 11.86/2.01  
% 11.86/2.01  fof(f50,plain,(
% 11.86/2.01    ? [X0] : (? [X1] : (k1_tops_1(X0,k2_tops_1(X0,X1)) != k1_xboole_0 & v4_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (k1_tops_1(sK0,k2_tops_1(sK0,X1)) != k1_xboole_0 & v4_tops_1(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 11.86/2.01    introduced(choice_axiom,[])).
% 11.86/2.01  
% 11.86/2.01  fof(f52,plain,(
% 11.86/2.01    (k1_tops_1(sK0,k2_tops_1(sK0,sK1)) != k1_xboole_0 & v4_tops_1(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 11.86/2.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f44,f51,f50])).
% 11.86/2.01  
% 11.86/2.01  fof(f75,plain,(
% 11.86/2.01    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 11.86/2.01    inference(cnf_transformation,[],[f52])).
% 11.86/2.01  
% 11.86/2.01  fof(f6,axiom,(
% 11.86/2.01    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 11.86/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.86/2.01  
% 11.86/2.01  fof(f25,plain,(
% 11.86/2.01    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 11.86/2.01    inference(ennf_transformation,[],[f6])).
% 11.86/2.01  
% 11.86/2.01  fof(f26,plain,(
% 11.86/2.01    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 11.86/2.01    inference(flattening,[],[f25])).
% 11.86/2.01  
% 11.86/2.01  fof(f62,plain,(
% 11.86/2.01    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.86/2.01    inference(cnf_transformation,[],[f26])).
% 11.86/2.01  
% 11.86/2.01  fof(f3,axiom,(
% 11.86/2.01    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)))),
% 11.86/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.86/2.01  
% 11.86/2.01  fof(f20,plain,(
% 11.86/2.01    ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 11.86/2.01    inference(ennf_transformation,[],[f3])).
% 11.86/2.01  
% 11.86/2.01  fof(f21,plain,(
% 11.86/2.01    ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 11.86/2.01    inference(flattening,[],[f20])).
% 11.86/2.01  
% 11.86/2.01  fof(f57,plain,(
% 11.86/2.01    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.86/2.01    inference(cnf_transformation,[],[f21])).
% 11.86/2.01  
% 11.86/2.01  fof(f74,plain,(
% 11.86/2.01    l1_pre_topc(sK0)),
% 11.86/2.01    inference(cnf_transformation,[],[f52])).
% 11.86/2.01  
% 11.86/2.01  fof(f4,axiom,(
% 11.86/2.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))))))),
% 11.86/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.86/2.01  
% 11.86/2.01  fof(f22,plain,(
% 11.86/2.01    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.86/2.01    inference(ennf_transformation,[],[f4])).
% 11.86/2.01  
% 11.86/2.01  fof(f23,plain,(
% 11.86/2.01    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.86/2.01    inference(flattening,[],[f22])).
% 11.86/2.01  
% 11.86/2.01  fof(f58,plain,(
% 11.86/2.01    ( ! [X2,X0,X1] : (r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.86/2.01    inference(cnf_transformation,[],[f23])).
% 11.86/2.01  
% 11.86/2.01  fof(f2,axiom,(
% 11.86/2.01    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 11.86/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.86/2.01  
% 11.86/2.01  fof(f18,plain,(
% 11.86/2.01    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 11.86/2.01    inference(ennf_transformation,[],[f2])).
% 11.86/2.01  
% 11.86/2.01  fof(f19,plain,(
% 11.86/2.01    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 11.86/2.01    inference(flattening,[],[f18])).
% 11.86/2.01  
% 11.86/2.01  fof(f56,plain,(
% 11.86/2.01    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.86/2.01    inference(cnf_transformation,[],[f19])).
% 11.86/2.01  
% 11.86/2.01  fof(f1,axiom,(
% 11.86/2.01    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 11.86/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.86/2.01  
% 11.86/2.01  fof(f45,plain,(
% 11.86/2.01    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.86/2.01    inference(nnf_transformation,[],[f1])).
% 11.86/2.01  
% 11.86/2.01  fof(f46,plain,(
% 11.86/2.01    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.86/2.01    inference(flattening,[],[f45])).
% 11.86/2.01  
% 11.86/2.01  fof(f55,plain,(
% 11.86/2.01    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 11.86/2.01    inference(cnf_transformation,[],[f46])).
% 11.86/2.01  
% 11.86/2.01  fof(f76,plain,(
% 11.86/2.01    v4_tops_1(sK1,sK0)),
% 11.86/2.01    inference(cnf_transformation,[],[f52])).
% 11.86/2.01  
% 11.86/2.01  fof(f13,axiom,(
% 11.86/2.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 11.86/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.86/2.01  
% 11.86/2.01  fof(f38,plain,(
% 11.86/2.01    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.86/2.01    inference(ennf_transformation,[],[f13])).
% 11.86/2.01  
% 11.86/2.01  fof(f69,plain,(
% 11.86/2.01    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.86/2.01    inference(cnf_transformation,[],[f38])).
% 11.86/2.01  
% 11.86/2.01  fof(f5,axiom,(
% 11.86/2.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_tops_1(X1,X0) <=> (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)))))),
% 11.86/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.86/2.01  
% 11.86/2.01  fof(f24,plain,(
% 11.86/2.01    ! [X0] : (! [X1] : ((v4_tops_1(X1,X0) <=> (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.86/2.01    inference(ennf_transformation,[],[f5])).
% 11.86/2.01  
% 11.86/2.01  fof(f47,plain,(
% 11.86/2.01    ! [X0] : (! [X1] : (((v4_tops_1(X1,X0) | (~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1))) & ((r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) | ~v4_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.86/2.01    inference(nnf_transformation,[],[f24])).
% 11.86/2.01  
% 11.86/2.01  fof(f48,plain,(
% 11.86/2.01    ! [X0] : (! [X1] : (((v4_tops_1(X1,X0) | ~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) & ((r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) | ~v4_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.86/2.01    inference(flattening,[],[f47])).
% 11.86/2.01  
% 11.86/2.01  fof(f60,plain,(
% 11.86/2.01    ( ! [X0,X1] : (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~v4_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.86/2.01    inference(cnf_transformation,[],[f48])).
% 11.86/2.01  
% 11.86/2.01  fof(f10,axiom,(
% 11.86/2.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 11.86/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.86/2.01  
% 11.86/2.01  fof(f33,plain,(
% 11.86/2.01    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.86/2.01    inference(ennf_transformation,[],[f10])).
% 11.86/2.01  
% 11.86/2.01  fof(f66,plain,(
% 11.86/2.01    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.86/2.01    inference(cnf_transformation,[],[f33])).
% 11.86/2.01  
% 11.86/2.01  fof(f12,axiom,(
% 11.86/2.01    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)))),
% 11.86/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.86/2.01  
% 11.86/2.01  fof(f36,plain,(
% 11.86/2.01    ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 11.86/2.01    inference(ennf_transformation,[],[f12])).
% 11.86/2.01  
% 11.86/2.01  fof(f37,plain,(
% 11.86/2.01    ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 11.86/2.01    inference(flattening,[],[f36])).
% 11.86/2.01  
% 11.86/2.01  fof(f68,plain,(
% 11.86/2.01    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.86/2.01    inference(cnf_transformation,[],[f37])).
% 11.86/2.01  
% 11.86/2.01  fof(f15,axiom,(
% 11.86/2.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) => v3_tops_1(k2_tops_1(X0,X1),X0))))),
% 11.86/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.86/2.01  
% 11.86/2.01  fof(f41,plain,(
% 11.86/2.01    ! [X0] : (! [X1] : ((v3_tops_1(k2_tops_1(X0,X1),X0) | ~v3_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 11.86/2.01    inference(ennf_transformation,[],[f15])).
% 11.86/2.01  
% 11.86/2.01  fof(f42,plain,(
% 11.86/2.01    ! [X0] : (! [X1] : (v3_tops_1(k2_tops_1(X0,X1),X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 11.86/2.01    inference(flattening,[],[f41])).
% 11.86/2.01  
% 11.86/2.01  fof(f72,plain,(
% 11.86/2.01    ( ! [X0,X1] : (v3_tops_1(k2_tops_1(X0,X1),X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 11.86/2.01    inference(cnf_transformation,[],[f42])).
% 11.86/2.01  
% 11.86/2.01  fof(f9,axiom,(
% 11.86/2.01    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 11.86/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.86/2.01  
% 11.86/2.01  fof(f31,plain,(
% 11.86/2.01    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 11.86/2.01    inference(ennf_transformation,[],[f9])).
% 11.86/2.01  
% 11.86/2.01  fof(f32,plain,(
% 11.86/2.01    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 11.86/2.01    inference(flattening,[],[f31])).
% 11.86/2.01  
% 11.86/2.01  fof(f65,plain,(
% 11.86/2.01    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 11.86/2.01    inference(cnf_transformation,[],[f32])).
% 11.86/2.01  
% 11.86/2.01  fof(f73,plain,(
% 11.86/2.01    v2_pre_topc(sK0)),
% 11.86/2.01    inference(cnf_transformation,[],[f52])).
% 11.86/2.01  
% 11.86/2.01  fof(f7,axiom,(
% 11.86/2.01    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 11.86/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.86/2.01  
% 11.86/2.01  fof(f27,plain,(
% 11.86/2.01    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 11.86/2.01    inference(ennf_transformation,[],[f7])).
% 11.86/2.01  
% 11.86/2.01  fof(f28,plain,(
% 11.86/2.01    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 11.86/2.01    inference(flattening,[],[f27])).
% 11.86/2.01  
% 11.86/2.01  fof(f63,plain,(
% 11.86/2.01    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.86/2.01    inference(cnf_transformation,[],[f28])).
% 11.86/2.01  
% 11.86/2.01  fof(f14,axiom,(
% 11.86/2.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => (v3_tops_1(X1,X0) <=> k2_tops_1(X0,X1) = X1))))),
% 11.86/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.86/2.01  
% 11.86/2.01  fof(f39,plain,(
% 11.86/2.01    ! [X0] : (! [X1] : (((v3_tops_1(X1,X0) <=> k2_tops_1(X0,X1) = X1) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.86/2.01    inference(ennf_transformation,[],[f14])).
% 11.86/2.01  
% 11.86/2.01  fof(f40,plain,(
% 11.86/2.01    ! [X0] : (! [X1] : ((v3_tops_1(X1,X0) <=> k2_tops_1(X0,X1) = X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.86/2.01    inference(flattening,[],[f39])).
% 11.86/2.01  
% 11.86/2.01  fof(f49,plain,(
% 11.86/2.01    ! [X0] : (! [X1] : (((v3_tops_1(X1,X0) | k2_tops_1(X0,X1) != X1) & (k2_tops_1(X0,X1) = X1 | ~v3_tops_1(X1,X0))) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.86/2.01    inference(nnf_transformation,[],[f40])).
% 11.86/2.01  
% 11.86/2.01  fof(f70,plain,(
% 11.86/2.01    ( ! [X0,X1] : (k2_tops_1(X0,X1) = X1 | ~v3_tops_1(X1,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.86/2.01    inference(cnf_transformation,[],[f49])).
% 11.86/2.01  
% 11.86/2.01  fof(f8,axiom,(
% 11.86/2.01    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_tops_1(X0,X1),X0))),
% 11.86/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.86/2.01  
% 11.86/2.01  fof(f29,plain,(
% 11.86/2.01    ! [X0,X1] : (v4_pre_topc(k2_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 11.86/2.01    inference(ennf_transformation,[],[f8])).
% 11.86/2.01  
% 11.86/2.01  fof(f30,plain,(
% 11.86/2.01    ! [X0,X1] : (v4_pre_topc(k2_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 11.86/2.01    inference(flattening,[],[f29])).
% 11.86/2.01  
% 11.86/2.01  fof(f64,plain,(
% 11.86/2.01    ( ! [X0,X1] : (v4_pre_topc(k2_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 11.86/2.01    inference(cnf_transformation,[],[f30])).
% 11.86/2.01  
% 11.86/2.01  fof(f11,axiom,(
% 11.86/2.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) = k1_xboole_0))),
% 11.86/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.86/2.01  
% 11.86/2.01  fof(f34,plain,(
% 11.86/2.01    ! [X0] : (! [X1] : (k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) = k1_xboole_0 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 11.86/2.01    inference(ennf_transformation,[],[f11])).
% 11.86/2.01  
% 11.86/2.01  fof(f35,plain,(
% 11.86/2.01    ! [X0] : (! [X1] : (k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) = k1_xboole_0 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 11.86/2.01    inference(flattening,[],[f34])).
% 11.86/2.01  
% 11.86/2.01  fof(f67,plain,(
% 11.86/2.01    ( ! [X0,X1] : (k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) = k1_xboole_0 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 11.86/2.01    inference(cnf_transformation,[],[f35])).
% 11.86/2.01  
% 11.86/2.01  fof(f77,plain,(
% 11.86/2.01    k1_tops_1(sK0,k2_tops_1(sK0,sK1)) != k1_xboole_0),
% 11.86/2.01    inference(cnf_transformation,[],[f52])).
% 11.86/2.01  
% 11.86/2.01  cnf(c_22,negated_conjecture,
% 11.86/2.01      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 11.86/2.01      inference(cnf_transformation,[],[f75]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_760,plain,
% 11.86/2.01      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 11.86/2.01      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_9,plain,
% 11.86/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.86/2.01      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 11.86/2.01      | ~ l1_pre_topc(X1) ),
% 11.86/2.01      inference(cnf_transformation,[],[f62]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_772,plain,
% 11.86/2.01      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 11.86/2.01      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 11.86/2.01      | l1_pre_topc(X1) != iProver_top ),
% 11.86/2.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_4,plain,
% 11.86/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.86/2.01      | ~ l1_pre_topc(X1)
% 11.86/2.01      | k2_pre_topc(X1,k2_pre_topc(X1,X0)) = k2_pre_topc(X1,X0) ),
% 11.86/2.01      inference(cnf_transformation,[],[f57]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_777,plain,
% 11.86/2.01      ( k2_pre_topc(X0,k2_pre_topc(X0,X1)) = k2_pre_topc(X0,X1)
% 11.86/2.01      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 11.86/2.01      | l1_pre_topc(X0) != iProver_top ),
% 11.86/2.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_2051,plain,
% 11.86/2.01      ( k2_pre_topc(X0,k2_pre_topc(X0,k1_tops_1(X0,X1))) = k2_pre_topc(X0,k1_tops_1(X0,X1))
% 11.86/2.01      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 11.86/2.01      | l1_pre_topc(X0) != iProver_top ),
% 11.86/2.01      inference(superposition,[status(thm)],[c_772,c_777]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_8349,plain,
% 11.86/2.01      ( k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = k2_pre_topc(sK0,k1_tops_1(sK0,sK1))
% 11.86/2.01      | l1_pre_topc(sK0) != iProver_top ),
% 11.86/2.01      inference(superposition,[status(thm)],[c_760,c_2051]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_23,negated_conjecture,
% 11.86/2.01      ( l1_pre_topc(sK0) ),
% 11.86/2.01      inference(cnf_transformation,[],[f74]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_1014,plain,
% 11.86/2.01      ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 11.86/2.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.86/2.01      | ~ l1_pre_topc(sK0) ),
% 11.86/2.01      inference(instantiation,[status(thm)],[c_9]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_1213,plain,
% 11.86/2.01      ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 11.86/2.01      | ~ l1_pre_topc(sK0)
% 11.86/2.01      | k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) ),
% 11.86/2.01      inference(instantiation,[status(thm)],[c_4]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_8510,plain,
% 11.86/2.01      ( k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) ),
% 11.86/2.01      inference(global_propositional_subsumption,
% 11.86/2.01                [status(thm)],
% 11.86/2.01                [c_8349,c_23,c_22,c_1014,c_1213]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_5,plain,
% 11.86/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.86/2.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 11.86/2.01      | ~ r1_tarski(X0,X2)
% 11.86/2.01      | r1_tarski(k2_pre_topc(X1,X0),k2_pre_topc(X1,X2))
% 11.86/2.01      | ~ l1_pre_topc(X1) ),
% 11.86/2.01      inference(cnf_transformation,[],[f58]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_776,plain,
% 11.86/2.01      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 11.86/2.01      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 11.86/2.01      | r1_tarski(X0,X2) != iProver_top
% 11.86/2.01      | r1_tarski(k2_pre_topc(X1,X0),k2_pre_topc(X1,X2)) = iProver_top
% 11.86/2.01      | l1_pre_topc(X1) != iProver_top ),
% 11.86/2.01      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_2053,plain,
% 11.86/2.01      ( k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)) = k2_pre_topc(sK0,sK1)
% 11.86/2.01      | l1_pre_topc(sK0) != iProver_top ),
% 11.86/2.01      inference(superposition,[status(thm)],[c_760,c_777]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_1055,plain,
% 11.86/2.01      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.86/2.01      | ~ l1_pre_topc(sK0)
% 11.86/2.01      | k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 11.86/2.01      inference(instantiation,[status(thm)],[c_4]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_2078,plain,
% 11.86/2.01      ( k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 11.86/2.01      inference(global_propositional_subsumption,
% 11.86/2.01                [status(thm)],
% 11.86/2.01                [c_2053,c_23,c_22,c_1055]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_3925,plain,
% 11.86/2.01      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.86/2.01      | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.86/2.01      | r1_tarski(X0,k2_pre_topc(sK0,sK1)) != iProver_top
% 11.86/2.01      | r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,sK1)) = iProver_top
% 11.86/2.01      | l1_pre_topc(sK0) != iProver_top ),
% 11.86/2.01      inference(superposition,[status(thm)],[c_2078,c_776]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_26,plain,
% 11.86/2.01      ( l1_pre_topc(sK0) = iProver_top ),
% 11.86/2.01      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_27,plain,
% 11.86/2.01      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 11.86/2.01      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_3,plain,
% 11.86/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.86/2.01      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 11.86/2.01      | ~ l1_pre_topc(X1) ),
% 11.86/2.01      inference(cnf_transformation,[],[f56]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_1011,plain,
% 11.86/2.01      ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 11.86/2.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.86/2.01      | ~ l1_pre_topc(sK0) ),
% 11.86/2.01      inference(instantiation,[status(thm)],[c_3]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_1012,plain,
% 11.86/2.01      ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 11.86/2.01      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.86/2.01      | l1_pre_topc(sK0) != iProver_top ),
% 11.86/2.01      inference(predicate_to_equality,[status(thm)],[c_1011]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_4730,plain,
% 11.86/2.01      ( r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,sK1)) = iProver_top
% 11.86/2.01      | r1_tarski(X0,k2_pre_topc(sK0,sK1)) != iProver_top
% 11.86/2.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 11.86/2.01      inference(global_propositional_subsumption,
% 11.86/2.01                [status(thm)],
% 11.86/2.01                [c_3925,c_26,c_27,c_1012]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_4731,plain,
% 11.86/2.01      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.86/2.01      | r1_tarski(X0,k2_pre_topc(sK0,sK1)) != iProver_top
% 11.86/2.01      | r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,sK1)) = iProver_top ),
% 11.86/2.01      inference(renaming,[status(thm)],[c_4730]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_3923,plain,
% 11.86/2.01      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.86/2.01      | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.86/2.01      | r1_tarski(k2_pre_topc(sK0,sK1),X0) != iProver_top
% 11.86/2.01      | r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X0)) = iProver_top
% 11.86/2.01      | l1_pre_topc(sK0) != iProver_top ),
% 11.86/2.01      inference(superposition,[status(thm)],[c_2078,c_776]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_4494,plain,
% 11.86/2.01      ( r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X0)) = iProver_top
% 11.86/2.01      | r1_tarski(k2_pre_topc(sK0,sK1),X0) != iProver_top
% 11.86/2.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 11.86/2.01      inference(global_propositional_subsumption,
% 11.86/2.01                [status(thm)],
% 11.86/2.01                [c_3923,c_26,c_27,c_1012]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_4495,plain,
% 11.86/2.01      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.86/2.01      | r1_tarski(k2_pre_topc(sK0,sK1),X0) != iProver_top
% 11.86/2.01      | r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X0)) = iProver_top ),
% 11.86/2.01      inference(renaming,[status(thm)],[c_4494]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_0,plain,
% 11.86/2.01      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 11.86/2.01      inference(cnf_transformation,[],[f55]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_780,plain,
% 11.86/2.01      ( X0 = X1
% 11.86/2.01      | r1_tarski(X0,X1) != iProver_top
% 11.86/2.01      | r1_tarski(X1,X0) != iProver_top ),
% 11.86/2.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_4505,plain,
% 11.86/2.01      ( k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,sK1)
% 11.86/2.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.86/2.01      | r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,sK1)) != iProver_top
% 11.86/2.01      | r1_tarski(k2_pre_topc(sK0,sK1),X0) != iProver_top ),
% 11.86/2.01      inference(superposition,[status(thm)],[c_4495,c_780]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_6480,plain,
% 11.86/2.01      ( k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,sK1)
% 11.86/2.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.86/2.01      | r1_tarski(X0,k2_pre_topc(sK0,sK1)) != iProver_top
% 11.86/2.01      | r1_tarski(k2_pre_topc(sK0,sK1),X0) != iProver_top ),
% 11.86/2.01      inference(superposition,[status(thm)],[c_4731,c_4505]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_337,plain,
% 11.86/2.01      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 11.86/2.01      theory(equality) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_1198,plain,
% 11.86/2.01      ( m1_subset_1(X0,X1)
% 11.86/2.01      | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 11.86/2.01      | X0 != k2_pre_topc(sK0,sK1)
% 11.86/2.01      | X1 != k1_zfmisc_1(u1_struct_0(sK0)) ),
% 11.86/2.01      inference(instantiation,[status(thm)],[c_337]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_2653,plain,
% 11.86/2.01      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.86/2.01      | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 11.86/2.01      | X0 != k2_pre_topc(sK0,sK1)
% 11.86/2.01      | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(u1_struct_0(sK0)) ),
% 11.86/2.01      inference(instantiation,[status(thm)],[c_1198]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_2655,plain,
% 11.86/2.01      ( X0 != k2_pre_topc(sK0,sK1)
% 11.86/2.01      | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(u1_struct_0(sK0))
% 11.86/2.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 11.86/2.01      | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 11.86/2.01      inference(predicate_to_equality,[status(thm)],[c_2653]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_331,plain,( X0 = X0 ),theory(equality) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_2654,plain,
% 11.86/2.01      ( k1_zfmisc_1(u1_struct_0(sK0)) = k1_zfmisc_1(u1_struct_0(sK0)) ),
% 11.86/2.01      inference(instantiation,[status(thm)],[c_331]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_6583,plain,
% 11.86/2.01      ( ~ r1_tarski(X0,k2_pre_topc(sK0,sK1))
% 11.86/2.01      | ~ r1_tarski(k2_pre_topc(sK0,sK1),X0)
% 11.86/2.01      | X0 = k2_pre_topc(sK0,sK1) ),
% 11.86/2.01      inference(instantiation,[status(thm)],[c_0]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_6584,plain,
% 11.86/2.01      ( X0 = k2_pre_topc(sK0,sK1)
% 11.86/2.01      | r1_tarski(X0,k2_pre_topc(sK0,sK1)) != iProver_top
% 11.86/2.01      | r1_tarski(k2_pre_topc(sK0,sK1),X0) != iProver_top ),
% 11.86/2.01      inference(predicate_to_equality,[status(thm)],[c_6583]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_7462,plain,
% 11.86/2.01      ( k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,sK1)
% 11.86/2.01      | r1_tarski(X0,k2_pre_topc(sK0,sK1)) != iProver_top
% 11.86/2.01      | r1_tarski(k2_pre_topc(sK0,sK1),X0) != iProver_top ),
% 11.86/2.01      inference(global_propositional_subsumption,
% 11.86/2.01                [status(thm)],
% 11.86/2.01                [c_6480,c_26,c_27,c_1012,c_2655,c_2654,c_6584]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_7472,plain,
% 11.86/2.01      ( k2_pre_topc(sK0,k2_pre_topc(sK0,X0)) = k2_pre_topc(sK0,sK1)
% 11.86/2.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.86/2.01      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.86/2.01      | r1_tarski(X0,sK1) != iProver_top
% 11.86/2.01      | r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X0)) != iProver_top
% 11.86/2.01      | l1_pre_topc(sK0) != iProver_top ),
% 11.86/2.01      inference(superposition,[status(thm)],[c_776,c_7462]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_41681,plain,
% 11.86/2.01      ( r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X0)) != iProver_top
% 11.86/2.01      | r1_tarski(X0,sK1) != iProver_top
% 11.86/2.01      | k2_pre_topc(sK0,k2_pre_topc(sK0,X0)) = k2_pre_topc(sK0,sK1)
% 11.86/2.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 11.86/2.01      inference(global_propositional_subsumption,
% 11.86/2.01                [status(thm)],
% 11.86/2.01                [c_7472,c_26,c_27]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_41682,plain,
% 11.86/2.01      ( k2_pre_topc(sK0,k2_pre_topc(sK0,X0)) = k2_pre_topc(sK0,sK1)
% 11.86/2.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.86/2.01      | r1_tarski(X0,sK1) != iProver_top
% 11.86/2.01      | r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X0)) != iProver_top ),
% 11.86/2.01      inference(renaming,[status(thm)],[c_41681]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_41704,plain,
% 11.86/2.01      ( k2_pre_topc(sK0,k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))) = k2_pre_topc(sK0,sK1)
% 11.86/2.01      | m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.86/2.01      | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),sK1) != iProver_top
% 11.86/2.01      | r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != iProver_top ),
% 11.86/2.01      inference(superposition,[status(thm)],[c_8510,c_41682]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_41819,plain,
% 11.86/2.01      ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
% 11.86/2.01      | m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.86/2.01      | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),sK1) != iProver_top
% 11.86/2.01      | r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != iProver_top ),
% 11.86/2.01      inference(light_normalisation,[status(thm)],[c_41704,c_8510]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_21,negated_conjecture,
% 11.86/2.01      ( v4_tops_1(sK1,sK0) ),
% 11.86/2.01      inference(cnf_transformation,[],[f76]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_28,plain,
% 11.86/2.01      ( v4_tops_1(sK1,sK0) = iProver_top ),
% 11.86/2.01      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_1015,plain,
% 11.86/2.01      ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 11.86/2.01      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.86/2.01      | l1_pre_topc(sK0) != iProver_top ),
% 11.86/2.01      inference(predicate_to_equality,[status(thm)],[c_1014]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_16,plain,
% 11.86/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.86/2.01      | r1_tarski(k1_tops_1(X1,X0),X0)
% 11.86/2.01      | ~ l1_pre_topc(X1) ),
% 11.86/2.01      inference(cnf_transformation,[],[f69]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_1020,plain,
% 11.86/2.01      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.86/2.01      | r1_tarski(k1_tops_1(sK0,sK1),sK1)
% 11.86/2.01      | ~ l1_pre_topc(sK0) ),
% 11.86/2.01      inference(instantiation,[status(thm)],[c_16]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_1021,plain,
% 11.86/2.01      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.86/2.01      | r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top
% 11.86/2.01      | l1_pre_topc(sK0) != iProver_top ),
% 11.86/2.01      inference(predicate_to_equality,[status(thm)],[c_1020]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_7,plain,
% 11.86/2.01      ( ~ v4_tops_1(X0,X1)
% 11.86/2.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.86/2.01      | r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
% 11.86/2.01      | ~ l1_pre_topc(X1) ),
% 11.86/2.01      inference(cnf_transformation,[],[f60]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_1102,plain,
% 11.86/2.01      ( ~ v4_tops_1(sK1,sK0)
% 11.86/2.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.86/2.01      | r1_tarski(sK1,k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))
% 11.86/2.01      | ~ l1_pre_topc(sK0) ),
% 11.86/2.01      inference(instantiation,[status(thm)],[c_7]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_1103,plain,
% 11.86/2.01      ( v4_tops_1(sK1,sK0) != iProver_top
% 11.86/2.01      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.86/2.01      | r1_tarski(sK1,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = iProver_top
% 11.86/2.01      | l1_pre_topc(sK0) != iProver_top ),
% 11.86/2.01      inference(predicate_to_equality,[status(thm)],[c_1102]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_8519,plain,
% 11.86/2.01      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.86/2.01      | m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.86/2.01      | r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != iProver_top
% 11.86/2.01      | r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = iProver_top
% 11.86/2.01      | l1_pre_topc(sK0) != iProver_top ),
% 11.86/2.01      inference(superposition,[status(thm)],[c_8510,c_776]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_1217,plain,
% 11.86/2.01      ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 11.86/2.01      | m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
% 11.86/2.01      | ~ l1_pre_topc(sK0) ),
% 11.86/2.01      inference(instantiation,[status(thm)],[c_3]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_1218,plain,
% 11.86/2.01      ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.86/2.01      | m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 11.86/2.01      | l1_pre_topc(sK0) != iProver_top ),
% 11.86/2.01      inference(predicate_to_equality,[status(thm)],[c_1217]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_8979,plain,
% 11.86/2.01      ( r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = iProver_top
% 11.86/2.01      | r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != iProver_top
% 11.86/2.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 11.86/2.01      inference(global_propositional_subsumption,
% 11.86/2.01                [status(thm)],
% 11.86/2.01                [c_8519,c_26,c_27,c_1015,c_1218]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_8980,plain,
% 11.86/2.01      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.86/2.01      | r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != iProver_top
% 11.86/2.01      | r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = iProver_top ),
% 11.86/2.01      inference(renaming,[status(thm)],[c_8979]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_41695,plain,
% 11.86/2.01      ( k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) = k2_pre_topc(sK0,sK1)
% 11.86/2.01      | m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.86/2.01      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.86/2.01      | r1_tarski(k1_tops_1(sK0,sK1),sK1) != iProver_top
% 11.86/2.01      | r1_tarski(sK1,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != iProver_top ),
% 11.86/2.01      inference(superposition,[status(thm)],[c_8980,c_41682]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_41908,plain,
% 11.86/2.01      ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
% 11.86/2.01      | m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.86/2.01      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.86/2.01      | r1_tarski(k1_tops_1(sK0,sK1),sK1) != iProver_top
% 11.86/2.01      | r1_tarski(sK1,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) != iProver_top ),
% 11.86/2.01      inference(demodulation,[status(thm)],[c_41695,c_8510]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_43124,plain,
% 11.86/2.01      ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 11.86/2.01      inference(global_propositional_subsumption,
% 11.86/2.01                [status(thm)],
% 11.86/2.01                [c_41819,c_26,c_27,c_28,c_1015,c_1021,c_1103,c_41908]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_13,plain,
% 11.86/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.86/2.01      | ~ l1_pre_topc(X1)
% 11.86/2.01      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
% 11.86/2.01      inference(cnf_transformation,[],[f66]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_768,plain,
% 11.86/2.01      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
% 11.86/2.01      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 11.86/2.01      | l1_pre_topc(X0) != iProver_top ),
% 11.86/2.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_2497,plain,
% 11.86/2.01      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k1_tops_1(X0,X1)),k1_tops_1(X0,k1_tops_1(X0,X1))) = k2_tops_1(X0,k1_tops_1(X0,X1))
% 11.86/2.01      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 11.86/2.01      | l1_pre_topc(X0) != iProver_top ),
% 11.86/2.01      inference(superposition,[status(thm)],[c_772,c_768]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_17389,plain,
% 11.86/2.01      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,k1_tops_1(sK0,sK1))) = k2_tops_1(sK0,k1_tops_1(sK0,sK1))
% 11.86/2.01      | l1_pre_topc(sK0) != iProver_top ),
% 11.86/2.01      inference(superposition,[status(thm)],[c_760,c_2497]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_15,plain,
% 11.86/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.86/2.01      | ~ l1_pre_topc(X1)
% 11.86/2.01      | k1_tops_1(X1,k1_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
% 11.86/2.01      inference(cnf_transformation,[],[f68]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_766,plain,
% 11.86/2.01      ( k1_tops_1(X0,k1_tops_1(X0,X1)) = k1_tops_1(X0,X1)
% 11.86/2.01      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 11.86/2.01      | l1_pre_topc(X0) != iProver_top ),
% 11.86/2.01      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_1345,plain,
% 11.86/2.01      ( k1_tops_1(sK0,k1_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1)
% 11.86/2.01      | l1_pre_topc(sK0) != iProver_top ),
% 11.86/2.01      inference(superposition,[status(thm)],[c_760,c_766]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_1061,plain,
% 11.86/2.01      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.86/2.01      | ~ l1_pre_topc(sK0)
% 11.86/2.01      | k1_tops_1(sK0,k1_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
% 11.86/2.01      inference(instantiation,[status(thm)],[c_15]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_1695,plain,
% 11.86/2.01      ( k1_tops_1(sK0,k1_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
% 11.86/2.01      inference(global_propositional_subsumption,
% 11.86/2.01                [status(thm)],
% 11.86/2.01                [c_1345,c_23,c_22,c_1061]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_17398,plain,
% 11.86/2.01      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,k1_tops_1(sK0,sK1))
% 11.86/2.01      | l1_pre_topc(sK0) != iProver_top ),
% 11.86/2.01      inference(light_normalisation,[status(thm)],[c_17389,c_1695]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_18287,plain,
% 11.86/2.01      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,k1_tops_1(sK0,sK1)) ),
% 11.86/2.01      inference(global_propositional_subsumption,
% 11.86/2.01                [status(thm)],
% 11.86/2.01                [c_17398,c_26]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_43150,plain,
% 11.86/2.01      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,k1_tops_1(sK0,sK1)) ),
% 11.86/2.01      inference(demodulation,[status(thm)],[c_43124,c_18287]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_2499,plain,
% 11.86/2.01      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 11.86/2.01      | l1_pre_topc(sK0) != iProver_top ),
% 11.86/2.01      inference(superposition,[status(thm)],[c_760,c_768]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_1108,plain,
% 11.86/2.01      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.86/2.01      | ~ l1_pre_topc(sK0)
% 11.86/2.01      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 11.86/2.01      inference(instantiation,[status(thm)],[c_13]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_2940,plain,
% 11.86/2.01      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 11.86/2.01      inference(global_propositional_subsumption,
% 11.86/2.01                [status(thm)],
% 11.86/2.01                [c_2499,c_23,c_22,c_1108]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_43170,plain,
% 11.86/2.01      ( k2_tops_1(sK0,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 11.86/2.01      inference(light_normalisation,[status(thm)],[c_43150,c_2940]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_19,plain,
% 11.86/2.01      ( v3_tops_1(k2_tops_1(X0,X1),X0)
% 11.86/2.01      | ~ v3_pre_topc(X1,X0)
% 11.86/2.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 11.86/2.01      | ~ v2_pre_topc(X0)
% 11.86/2.01      | ~ l1_pre_topc(X0) ),
% 11.86/2.01      inference(cnf_transformation,[],[f72]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_762,plain,
% 11.86/2.01      ( v3_tops_1(k2_tops_1(X0,X1),X0) = iProver_top
% 11.86/2.01      | v3_pre_topc(X1,X0) != iProver_top
% 11.86/2.01      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 11.86/2.01      | v2_pre_topc(X0) != iProver_top
% 11.86/2.01      | l1_pre_topc(X0) != iProver_top ),
% 11.86/2.01      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_1468,plain,
% 11.86/2.01      ( v3_tops_1(k2_tops_1(X0,k1_tops_1(X0,X1)),X0) = iProver_top
% 11.86/2.01      | v3_pre_topc(k1_tops_1(X0,X1),X0) != iProver_top
% 11.86/2.01      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 11.86/2.01      | v2_pre_topc(X0) != iProver_top
% 11.86/2.01      | l1_pre_topc(X0) != iProver_top ),
% 11.86/2.01      inference(superposition,[status(thm)],[c_772,c_762]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_12,plain,
% 11.86/2.01      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 11.86/2.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 11.86/2.01      | ~ v2_pre_topc(X0)
% 11.86/2.01      | ~ l1_pre_topc(X0) ),
% 11.86/2.01      inference(cnf_transformation,[],[f65]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_50,plain,
% 11.86/2.01      ( v3_pre_topc(k1_tops_1(X0,X1),X0) = iProver_top
% 11.86/2.01      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 11.86/2.01      | v2_pre_topc(X0) != iProver_top
% 11.86/2.01      | l1_pre_topc(X0) != iProver_top ),
% 11.86/2.01      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_9555,plain,
% 11.86/2.01      ( v3_tops_1(k2_tops_1(X0,k1_tops_1(X0,X1)),X0) = iProver_top
% 11.86/2.01      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 11.86/2.01      | v2_pre_topc(X0) != iProver_top
% 11.86/2.01      | l1_pre_topc(X0) != iProver_top ),
% 11.86/2.01      inference(global_propositional_subsumption,
% 11.86/2.01                [status(thm)],
% 11.86/2.01                [c_1468,c_50]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_9566,plain,
% 11.86/2.01      ( v3_tops_1(k2_tops_1(sK0,k1_tops_1(sK0,sK1)),sK0) = iProver_top
% 11.86/2.01      | m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.86/2.01      | v2_pre_topc(sK0) != iProver_top
% 11.86/2.01      | l1_pre_topc(sK0) != iProver_top ),
% 11.86/2.01      inference(superposition,[status(thm)],[c_1695,c_9555]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_24,negated_conjecture,
% 11.86/2.01      ( v2_pre_topc(sK0) ),
% 11.86/2.01      inference(cnf_transformation,[],[f73]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_25,plain,
% 11.86/2.01      ( v2_pre_topc(sK0) = iProver_top ),
% 11.86/2.01      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_1052,plain,
% 11.86/2.01      ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
% 11.86/2.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.86/2.01      | ~ v2_pre_topc(sK0)
% 11.86/2.01      | ~ l1_pre_topc(sK0) ),
% 11.86/2.01      inference(instantiation,[status(thm)],[c_12]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_1053,plain,
% 11.86/2.01      ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0) = iProver_top
% 11.86/2.01      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.86/2.01      | v2_pre_topc(sK0) != iProver_top
% 11.86/2.01      | l1_pre_topc(sK0) != iProver_top ),
% 11.86/2.01      inference(predicate_to_equality,[status(thm)],[c_1052]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_1327,plain,
% 11.86/2.01      ( v3_tops_1(k2_tops_1(sK0,k1_tops_1(sK0,sK1)),sK0)
% 11.86/2.01      | ~ v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
% 11.86/2.01      | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 11.86/2.01      | ~ v2_pre_topc(sK0)
% 11.86/2.01      | ~ l1_pre_topc(sK0) ),
% 11.86/2.01      inference(instantiation,[status(thm)],[c_19]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_1328,plain,
% 11.86/2.01      ( v3_tops_1(k2_tops_1(sK0,k1_tops_1(sK0,sK1)),sK0) = iProver_top
% 11.86/2.01      | v3_pre_topc(k1_tops_1(sK0,sK1),sK0) != iProver_top
% 11.86/2.01      | m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.86/2.01      | v2_pre_topc(sK0) != iProver_top
% 11.86/2.01      | l1_pre_topc(sK0) != iProver_top ),
% 11.86/2.01      inference(predicate_to_equality,[status(thm)],[c_1327]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_9981,plain,
% 11.86/2.01      ( v3_tops_1(k2_tops_1(sK0,k1_tops_1(sK0,sK1)),sK0) = iProver_top ),
% 11.86/2.01      inference(global_propositional_subsumption,
% 11.86/2.01                [status(thm)],
% 11.86/2.01                [c_9566,c_25,c_26,c_27,c_1015,c_1053,c_1328]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_10,plain,
% 11.86/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.86/2.01      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 11.86/2.01      | ~ l1_pre_topc(X1) ),
% 11.86/2.01      inference(cnf_transformation,[],[f63]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_771,plain,
% 11.86/2.01      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 11.86/2.01      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 11.86/2.01      | l1_pre_topc(X1) != iProver_top ),
% 11.86/2.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_18,plain,
% 11.86/2.01      ( ~ v3_tops_1(X0,X1)
% 11.86/2.01      | ~ v4_pre_topc(X0,X1)
% 11.86/2.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.86/2.01      | ~ l1_pre_topc(X1)
% 11.86/2.01      | k2_tops_1(X1,X0) = X0 ),
% 11.86/2.01      inference(cnf_transformation,[],[f70]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_763,plain,
% 11.86/2.01      ( k2_tops_1(X0,X1) = X1
% 11.86/2.01      | v3_tops_1(X1,X0) != iProver_top
% 11.86/2.01      | v4_pre_topc(X1,X0) != iProver_top
% 11.86/2.01      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 11.86/2.01      | l1_pre_topc(X0) != iProver_top ),
% 11.86/2.01      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_2321,plain,
% 11.86/2.01      ( k2_tops_1(X0,k2_tops_1(X0,X1)) = k2_tops_1(X0,X1)
% 11.86/2.01      | v3_tops_1(k2_tops_1(X0,X1),X0) != iProver_top
% 11.86/2.01      | v4_pre_topc(k2_tops_1(X0,X1),X0) != iProver_top
% 11.86/2.01      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 11.86/2.01      | l1_pre_topc(X0) != iProver_top ),
% 11.86/2.01      inference(superposition,[status(thm)],[c_771,c_763]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_13211,plain,
% 11.86/2.01      ( k2_tops_1(sK0,k2_tops_1(sK0,k1_tops_1(sK0,sK1))) = k2_tops_1(sK0,k1_tops_1(sK0,sK1))
% 11.86/2.01      | v4_pre_topc(k2_tops_1(sK0,k1_tops_1(sK0,sK1)),sK0) != iProver_top
% 11.86/2.01      | m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.86/2.01      | l1_pre_topc(sK0) != iProver_top ),
% 11.86/2.01      inference(superposition,[status(thm)],[c_9981,c_2321]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_11,plain,
% 11.86/2.01      ( v4_pre_topc(k2_tops_1(X0,X1),X0)
% 11.86/2.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 11.86/2.01      | ~ v2_pre_topc(X0)
% 11.86/2.01      | ~ l1_pre_topc(X0) ),
% 11.86/2.01      inference(cnf_transformation,[],[f64]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_1204,plain,
% 11.86/2.01      ( v4_pre_topc(k2_tops_1(sK0,k1_tops_1(sK0,sK1)),sK0)
% 11.86/2.01      | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 11.86/2.01      | ~ v2_pre_topc(sK0)
% 11.86/2.01      | ~ l1_pre_topc(sK0) ),
% 11.86/2.01      inference(instantiation,[status(thm)],[c_11]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_1215,plain,
% 11.86/2.01      ( m1_subset_1(k2_tops_1(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
% 11.86/2.01      | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 11.86/2.01      | ~ l1_pre_topc(sK0) ),
% 11.86/2.01      inference(instantiation,[status(thm)],[c_10]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_1719,plain,
% 11.86/2.01      ( ~ v3_tops_1(k2_tops_1(sK0,k1_tops_1(sK0,sK1)),sK0)
% 11.86/2.01      | ~ v4_pre_topc(k2_tops_1(sK0,k1_tops_1(sK0,sK1)),sK0)
% 11.86/2.01      | ~ m1_subset_1(k2_tops_1(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
% 11.86/2.01      | ~ l1_pre_topc(sK0)
% 11.86/2.01      | k2_tops_1(sK0,k2_tops_1(sK0,k1_tops_1(sK0,sK1))) = k2_tops_1(sK0,k1_tops_1(sK0,sK1)) ),
% 11.86/2.01      inference(instantiation,[status(thm)],[c_18]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_37003,plain,
% 11.86/2.01      ( k2_tops_1(sK0,k2_tops_1(sK0,k1_tops_1(sK0,sK1))) = k2_tops_1(sK0,k1_tops_1(sK0,sK1)) ),
% 11.86/2.01      inference(global_propositional_subsumption,
% 11.86/2.01                [status(thm)],
% 11.86/2.01                [c_13211,c_24,c_23,c_22,c_1014,c_1052,c_1204,c_1215,
% 11.86/2.01                 c_1327,c_1719]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_14,plain,
% 11.86/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.86/2.01      | ~ v2_pre_topc(X1)
% 11.86/2.01      | ~ l1_pre_topc(X1)
% 11.86/2.01      | k1_tops_1(X1,k2_tops_1(X1,k2_tops_1(X1,X0))) = k1_xboole_0 ),
% 11.86/2.01      inference(cnf_transformation,[],[f67]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_767,plain,
% 11.86/2.01      ( k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) = k1_xboole_0
% 11.86/2.01      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 11.86/2.01      | v2_pre_topc(X0) != iProver_top
% 11.86/2.01      | l1_pre_topc(X0) != iProver_top ),
% 11.86/2.01      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_2750,plain,
% 11.86/2.01      ( k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,k1_tops_1(X0,X1)))) = k1_xboole_0
% 11.86/2.01      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 11.86/2.01      | v2_pre_topc(X0) != iProver_top
% 11.86/2.01      | l1_pre_topc(X0) != iProver_top ),
% 11.86/2.01      inference(superposition,[status(thm)],[c_772,c_767]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_11827,plain,
% 11.86/2.01      ( k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,k1_tops_1(sK0,sK1)))) = k1_xboole_0
% 11.86/2.01      | v2_pre_topc(sK0) != iProver_top
% 11.86/2.01      | l1_pre_topc(sK0) != iProver_top ),
% 11.86/2.01      inference(superposition,[status(thm)],[c_760,c_2750]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_1212,plain,
% 11.86/2.01      ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 11.86/2.01      | ~ v2_pre_topc(sK0)
% 11.86/2.01      | ~ l1_pre_topc(sK0)
% 11.86/2.01      | k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,k1_tops_1(sK0,sK1)))) = k1_xboole_0 ),
% 11.86/2.01      inference(instantiation,[status(thm)],[c_14]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_11909,plain,
% 11.86/2.01      ( k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,k1_tops_1(sK0,sK1)))) = k1_xboole_0 ),
% 11.86/2.01      inference(global_propositional_subsumption,
% 11.86/2.01                [status(thm)],
% 11.86/2.01                [c_11827,c_24,c_23,c_22,c_1014,c_1212]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_37014,plain,
% 11.86/2.01      ( k1_tops_1(sK0,k2_tops_1(sK0,k1_tops_1(sK0,sK1))) = k1_xboole_0 ),
% 11.86/2.01      inference(demodulation,[status(thm)],[c_37003,c_11909]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_43544,plain,
% 11.86/2.01      ( k1_tops_1(sK0,k2_tops_1(sK0,sK1)) = k1_xboole_0 ),
% 11.86/2.01      inference(demodulation,[status(thm)],[c_43170,c_37014]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(c_20,negated_conjecture,
% 11.86/2.01      ( k1_tops_1(sK0,k2_tops_1(sK0,sK1)) != k1_xboole_0 ),
% 11.86/2.01      inference(cnf_transformation,[],[f77]) ).
% 11.86/2.01  
% 11.86/2.01  cnf(contradiction,plain,
% 11.86/2.01      ( $false ),
% 11.86/2.01      inference(minisat,[status(thm)],[c_43544,c_20]) ).
% 11.86/2.01  
% 11.86/2.01  
% 11.86/2.01  % SZS output end CNFRefutation for theBenchmark.p
% 11.86/2.01  
% 11.86/2.01  ------                               Statistics
% 11.86/2.01  
% 11.86/2.01  ------ Selected
% 11.86/2.01  
% 11.86/2.01  total_time:                             1.337
% 11.86/2.01  
%------------------------------------------------------------------------------
