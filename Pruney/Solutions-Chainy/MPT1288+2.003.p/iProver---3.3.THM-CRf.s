%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:15:56 EST 2020

% Result     : Theorem 8.01s
% Output     : CNFRefutation 8.01s
% Verified   : 
% Statistics : Number of formulae       :  203 (6026 expanded)
%              Number of clauses        :  134 (1917 expanded)
%              Number of leaves         :   20 (1386 expanded)
%              Depth                    :   39
%              Number of atoms          :  632 (24774 expanded)
%              Number of equality atoms :  242 (4905 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
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
    inference(ennf_transformation,[],[f7])).

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
    inference(nnf_transformation,[],[f24])).

fof(f45,plain,(
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
    inference(flattening,[],[f44])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)
      | ~ v4_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_tops_1(X1,X0)
           => k1_xboole_0 = k1_tops_1(X0,k2_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_tops_1(X1,X0)
             => k1_xboole_0 = k1_tops_1(X0,k2_tops_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 != k1_tops_1(X0,k2_tops_1(X0,X1))
          & v4_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 != k1_tops_1(X0,k2_tops_1(X0,X1))
          & v4_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f39])).

fof(f48,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k1_xboole_0 != k1_tops_1(X0,k2_tops_1(X0,X1))
          & v4_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k1_xboole_0 != k1_tops_1(X0,k2_tops_1(X0,sK1))
        & v4_tops_1(sK1,X0)
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k1_xboole_0 != k1_tops_1(X0,k2_tops_1(X0,X1))
            & v4_tops_1(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( k1_xboole_0 != k1_tops_1(sK0,k2_tops_1(sK0,X1))
          & v4_tops_1(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,k2_tops_1(sK0,sK1))
    & v4_tops_1(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f40,f48,f47])).

fof(f74,plain,(
    v4_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f72,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f73,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f49])).

fof(f3,axiom,(
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
    inference(ennf_transformation,[],[f3])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f8,axiom,(
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
    inference(ennf_transformation,[],[f8])).

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

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f52,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f4,axiom,(
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
    inference(ennf_transformation,[],[f4])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f9,axiom,(
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
    inference(ennf_transformation,[],[f9])).

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
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | k1_xboole_0 != k1_tops_1(X0,X1) )
            & ( k1_xboole_0 = k1_tops_1(X0,X1)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_tops_1(X0,X1)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tops_1(X1,X0)
          <=> v2_tops_1(k2_pre_topc(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tops_1(X1,X0)
          <=> v2_tops_1(k2_pre_topc(X0,X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tops_1(X1,X0)
              | ~ v2_tops_1(k2_pre_topc(X0,X1),X0) )
            & ( v2_tops_1(k2_pre_topc(X0,X1),X0)
              | ~ v3_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v2_tops_1(k2_pre_topc(X0,X1),X0)
      | ~ v3_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => v3_tops_1(k2_tops_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tops_1(k2_tops_1(X0,X1),X0)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tops_1(k2_tops_1(X0,X1),X0)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f37])).

fof(f70,plain,(
    ! [X0,X1] :
      ( v3_tops_1(k2_tops_1(X0,X1),X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f71,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f75,plain,(
    k1_xboole_0 != k1_tops_1(sK0,k2_tops_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_11,plain,
    ( ~ v4_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_22,negated_conjecture,
    ( v4_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_386,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
    | ~ l1_pre_topc(X1)
    | sK1 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_22])).

cnf(c_387,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_386])).

cnf(c_24,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_389,plain,
    ( r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_387,c_24,c_23])).

cnf(c_928,plain,
    ( r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_389])).

cnf(c_929,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_502,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_24])).

cnf(c_503,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_502])).

cnf(c_919,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_503])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,k1_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_430,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,k1_tops_1(X1,X0)) = k1_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_24])).

cnf(c_431,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,k1_tops_1(sK0,X0)) = k1_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_430])).

cnf(c_925,plain,
    ( k1_tops_1(sK0,k1_tops_1(sK0,X0)) = k1_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_431])).

cnf(c_1870,plain,
    ( k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,X0))) = k1_tops_1(sK0,k2_pre_topc(sK0,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_919,c_925])).

cnf(c_3427,plain,
    ( k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) = k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_929,c_1870])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_412,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_24])).

cnf(c_413,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,X1)
    | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,X1)) ),
    inference(unflattening,[status(thm)],[c_412])).

cnf(c_926,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_413])).

cnf(c_3445,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),X0) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3427,c_926])).

cnf(c_28,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_977,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_503])).

cnf(c_978,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_977])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_466,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_24])).

cnf(c_467,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_466])).

cnf(c_1088,plain,
    ( m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_467])).

cnf(c_1092,plain,
    ( m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1088])).

cnf(c_12168,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),X0) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3445,c_28,c_978,c_1092])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_932,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2086,plain,
    ( k1_tops_1(sK0,X0) = k1_tops_1(sK0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_926,c_932])).

cnf(c_12196,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK0,sK1)) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_12168,c_2086])).

cnf(c_26172,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,X0)
    | r1_tarski(X0,k2_pre_topc(sK0,sK1)) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12196,c_28,c_978])).

cnf(c_26173,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK0,sK1)) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_26172])).

cnf(c_26179,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,sK1)
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK1,k2_pre_topc(sK0,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_928,c_26173])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_478,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,X0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_24])).

cnf(c_479,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(X0,k2_pre_topc(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_478])).

cnf(c_985,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_479])).

cnf(c_986,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK1,k2_pre_topc(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_985])).

cnf(c_26830,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_26179,c_28,c_986])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_442,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_24])).

cnf(c_443,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_442])).

cnf(c_924,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_443])).

cnf(c_1986,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_pre_topc(sK0,X0)),k1_tops_1(sK0,k2_pre_topc(sK0,X0))) = k2_tops_1(sK0,k2_pre_topc(sK0,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_919,c_924])).

cnf(c_4892,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) = k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_929,c_1986])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k2_pre_topc(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_490,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,k2_pre_topc(X1,X0)) = k2_pre_topc(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_24])).

cnf(c_491,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k2_pre_topc(sK0,X0)) = k2_pre_topc(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_490])).

cnf(c_920,plain,
    ( k2_pre_topc(sK0,k2_pre_topc(sK0,X0)) = k2_pre_topc(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_491])).

cnf(c_1290,plain,
    ( k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_929,c_920])).

cnf(c_4898,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) = k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) ),
    inference(light_normalisation,[status(thm)],[c_4892,c_1290])).

cnf(c_26854,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) ),
    inference(demodulation,[status(thm)],[c_26830,c_4898])).

cnf(c_1983,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_929,c_924])).

cnf(c_26859,plain,
    ( k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_26854,c_1983])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_454,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_24])).

cnf(c_455,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_454])).

cnf(c_923,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_455])).

cnf(c_1868,plain,
    ( k1_tops_1(sK0,k1_tops_1(sK0,k2_tops_1(sK0,X0))) = k1_tops_1(sK0,k2_tops_1(sK0,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_923,c_925])).

cnf(c_3376,plain,
    ( k1_tops_1(sK0,k1_tops_1(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,X0)))) = k1_tops_1(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,X0)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_919,c_1868])).

cnf(c_10075,plain,
    ( k1_tops_1(sK0,k1_tops_1(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1)))) = k1_tops_1(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))) ),
    inference(superposition,[status(thm)],[c_929,c_3376])).

cnf(c_922,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_467])).

cnf(c_19,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_8,plain,
    ( v2_tops_1(k2_pre_topc(X0,X1),X0)
    | ~ v3_tops_1(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_14,plain,
    ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_20,plain,
    ( ~ v4_pre_topc(X0,X1)
    | v3_tops_1(k2_tops_1(X1,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_279,plain,
    ( v3_tops_1(k2_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X0)
    | X0 != X3
    | k2_pre_topc(X3,X2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_20])).

cnf(c_280,plain,
    ( v3_tops_1(k2_tops_1(X0,k2_pre_topc(X0,X1)),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(unflattening,[status(thm)],[c_279])).

cnf(c_294,plain,
    ( v3_tops_1(k2_tops_1(X0,k2_pre_topc(X0,X1)),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_280,c_4])).

cnf(c_25,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_307,plain,
    ( v3_tops_1(k2_tops_1(X0,k2_pre_topc(X0,X1)),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_294,c_25])).

cnf(c_308,plain,
    ( v3_tops_1(k2_tops_1(sK0,k2_pre_topc(sK0,X0)),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_307])).

cnf(c_312,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_tops_1(k2_tops_1(sK0,k2_pre_topc(sK0,X0)),sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_308,c_24])).

cnf(c_313,plain,
    ( v3_tops_1(k2_tops_1(sK0,k2_pre_topc(sK0,X0)),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(renaming,[status(thm)],[c_312])).

cnf(c_329,plain,
    ( v2_tops_1(k2_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(X0)
    | k2_tops_1(sK0,k2_pre_topc(sK0,X2)) != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_313])).

cnf(c_330,plain,
    ( v2_tops_1(k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,X0))),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_tops_1(sK0,k2_pre_topc(sK0,X0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_329])).

cnf(c_334,plain,
    ( ~ m1_subset_1(k2_tops_1(sK0,k2_pre_topc(sK0,X0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_tops_1(k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,X0))),sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_330,c_24])).

cnf(c_335,plain,
    ( v2_tops_1(k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,X0))),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_tops_1(sK0,k2_pre_topc(sK0,X0)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(renaming,[status(thm)],[c_334])).

cnf(c_355,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_tops_1(sK0,k2_pre_topc(sK0,X2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = k1_xboole_0
    | k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,X2))) != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_335])).

cnf(c_356,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_tops_1(sK0,k2_pre_topc(sK0,X0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,X0))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k1_tops_1(sK0,k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,X0)))) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_355])).

cnf(c_360,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,X0))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_tops_1(sK0,k2_pre_topc(sK0,X0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,X0)))) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_356,c_24])).

cnf(c_361,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_tops_1(sK0,k2_pre_topc(sK0,X0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,X0))),k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,X0)))) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_360])).

cnf(c_539,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_tops_1(sK0,k2_pre_topc(sK0,X0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,X0)))) = k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_503,c_361])).

cnf(c_918,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,X0)))) = k1_xboole_0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_tops_1(sK0,k2_pre_topc(sK0,X0)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_539])).

cnf(c_1695,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,k2_pre_topc(sK0,sK1))))) = k1_xboole_0
    | m1_subset_1(k2_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1290,c_918])).

cnf(c_1697,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1)))) = k1_xboole_0
    | m1_subset_1(k2_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1695,c_1290])).

cnf(c_1004,plain,
    ( ~ m1_subset_1(k2_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1)))) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_539])).

cnf(c_1089,plain,
    ( m1_subset_1(k2_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_455])).

cnf(c_3317,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1)))) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1697,c_23,c_977,c_1004,c_1089])).

cnf(c_3344,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1)))) = k1_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),k1_xboole_0) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3317,c_2086])).

cnf(c_3345,plain,
    ( k1_tops_1(sK0,X0) = k1_xboole_0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),k1_xboole_0) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))),X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3344,c_3317])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_81,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1090,plain,
    ( m1_subset_1(k2_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1089])).

cnf(c_1449,plain,
    ( ~ m1_subset_1(k2_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_503])).

cnf(c_1456,plain,
    ( m1_subset_1(k2_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1449])).

cnf(c_3322,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3317,c_922])).

cnf(c_930,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3323,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1)))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3317,c_926])).

cnf(c_10157,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1)))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3323,c_28,c_978,c_1090,c_1456])).

cnf(c_10164,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_930,c_10157])).

cnf(c_10170,plain,
    ( r1_tarski(k1_tops_1(sK0,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10164,c_28,c_978,c_1090,c_1456,c_3322])).

cnf(c_1487,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_930,c_932])).

cnf(c_10175,plain,
    ( k1_tops_1(sK0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_10170,c_1487])).

cnf(c_10224,plain,
    ( k1_tops_1(sK0,X0) = k1_tops_1(sK0,k1_xboole_0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_10175,c_2086])).

cnf(c_10226,plain,
    ( k1_tops_1(sK0,X0) = k1_xboole_0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10224,c_10175])).

cnf(c_11997,plain,
    ( r1_tarski(k1_tops_1(sK0,X0),k1_xboole_0) != iProver_top
    | k1_tops_1(sK0,X0) = k1_xboole_0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3345,c_28,c_81,c_978,c_1090,c_1456,c_3322,c_10226])).

cnf(c_11998,plain,
    ( k1_tops_1(sK0,X0) = k1_xboole_0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_11997])).

cnf(c_12005,plain,
    ( k1_tops_1(sK0,k1_tops_1(sK0,X0)) = k1_xboole_0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k1_tops_1(sK0,X0)),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_922,c_11998])).

cnf(c_16942,plain,
    ( k1_tops_1(sK0,k1_tops_1(sK0,k1_tops_1(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))))) = k1_xboole_0
    | m1_subset_1(k1_tops_1(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k1_tops_1(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1)))),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_10075,c_12005])).

cnf(c_16969,plain,
    ( k1_tops_1(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))) = k1_xboole_0
    | m1_subset_1(k1_tops_1(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))),k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_16942,c_10075])).

cnf(c_921,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_479])).

cnf(c_1855,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k2_tops_1(sK0,X0),k2_pre_topc(sK0,k2_tops_1(sK0,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_923,c_921])).

cnf(c_3342,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1)))) = k1_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1)))) != iProver_top
    | r1_tarski(k1_xboole_0,k1_tops_1(sK0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3317,c_2086])).

cnf(c_3347,plain,
    ( k1_tops_1(sK0,X0) = k1_xboole_0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1)))) != iProver_top
    | r1_tarski(k1_xboole_0,k1_tops_1(sK0,X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3342,c_3317])).

cnf(c_14286,plain,
    ( r1_tarski(X0,k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1)))) != iProver_top
    | k1_tops_1(sK0,X0) = k1_xboole_0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3347,c_28,c_81,c_978,c_1090,c_1456,c_3322,c_10157,c_10226])).

cnf(c_14287,plain,
    ( k1_tops_1(sK0,X0) = k1_xboole_0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_14286])).

cnf(c_14294,plain,
    ( k1_tops_1(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))) = k1_xboole_0
    | m1_subset_1(k2_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1855,c_14287])).

cnf(c_17316,plain,
    ( k1_tops_1(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_16969,c_28,c_978,c_1090,c_14294])).

cnf(c_28299,plain,
    ( k1_tops_1(sK0,k2_tops_1(sK0,sK1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_26859,c_17316])).

cnf(c_653,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1473,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_653])).

cnf(c_654,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_963,plain,
    ( k1_tops_1(sK0,k2_tops_1(sK0,sK1)) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k1_tops_1(sK0,k2_tops_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_654])).

cnf(c_1118,plain,
    ( k1_tops_1(sK0,k2_tops_1(sK0,sK1)) != k1_xboole_0
    | k1_xboole_0 = k1_tops_1(sK0,k2_tops_1(sK0,sK1))
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_963])).

cnf(c_21,negated_conjecture,
    ( k1_xboole_0 != k1_tops_1(sK0,k2_tops_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f75])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_28299,c_1473,c_1118,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:08:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 8.01/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.01/1.49  
% 8.01/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 8.01/1.49  
% 8.01/1.49  ------  iProver source info
% 8.01/1.49  
% 8.01/1.49  git: date: 2020-06-30 10:37:57 +0100
% 8.01/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 8.01/1.49  git: non_committed_changes: false
% 8.01/1.49  git: last_make_outside_of_git: false
% 8.01/1.49  
% 8.01/1.49  ------ 
% 8.01/1.49  
% 8.01/1.49  ------ Input Options
% 8.01/1.49  
% 8.01/1.49  --out_options                           all
% 8.01/1.49  --tptp_safe_out                         true
% 8.01/1.49  --problem_path                          ""
% 8.01/1.49  --include_path                          ""
% 8.01/1.49  --clausifier                            res/vclausify_rel
% 8.01/1.49  --clausifier_options                    ""
% 8.01/1.49  --stdin                                 false
% 8.01/1.49  --stats_out                             all
% 8.01/1.49  
% 8.01/1.49  ------ General Options
% 8.01/1.49  
% 8.01/1.49  --fof                                   false
% 8.01/1.49  --time_out_real                         305.
% 8.01/1.49  --time_out_virtual                      -1.
% 8.01/1.49  --symbol_type_check                     false
% 8.01/1.49  --clausify_out                          false
% 8.01/1.49  --sig_cnt_out                           false
% 8.01/1.49  --trig_cnt_out                          false
% 8.01/1.49  --trig_cnt_out_tolerance                1.
% 8.01/1.49  --trig_cnt_out_sk_spl                   false
% 8.01/1.49  --abstr_cl_out                          false
% 8.01/1.49  
% 8.01/1.49  ------ Global Options
% 8.01/1.49  
% 8.01/1.49  --schedule                              default
% 8.01/1.49  --add_important_lit                     false
% 8.01/1.49  --prop_solver_per_cl                    1000
% 8.01/1.49  --min_unsat_core                        false
% 8.01/1.49  --soft_assumptions                      false
% 8.01/1.49  --soft_lemma_size                       3
% 8.01/1.49  --prop_impl_unit_size                   0
% 8.01/1.49  --prop_impl_unit                        []
% 8.01/1.49  --share_sel_clauses                     true
% 8.01/1.49  --reset_solvers                         false
% 8.01/1.49  --bc_imp_inh                            [conj_cone]
% 8.01/1.49  --conj_cone_tolerance                   3.
% 8.01/1.49  --extra_neg_conj                        none
% 8.01/1.49  --large_theory_mode                     true
% 8.01/1.49  --prolific_symb_bound                   200
% 8.01/1.49  --lt_threshold                          2000
% 8.01/1.49  --clause_weak_htbl                      true
% 8.01/1.49  --gc_record_bc_elim                     false
% 8.01/1.49  
% 8.01/1.49  ------ Preprocessing Options
% 8.01/1.49  
% 8.01/1.49  --preprocessing_flag                    true
% 8.01/1.49  --time_out_prep_mult                    0.1
% 8.01/1.49  --splitting_mode                        input
% 8.01/1.49  --splitting_grd                         true
% 8.01/1.49  --splitting_cvd                         false
% 8.01/1.49  --splitting_cvd_svl                     false
% 8.01/1.49  --splitting_nvd                         32
% 8.01/1.49  --sub_typing                            true
% 8.01/1.49  --prep_gs_sim                           true
% 8.01/1.49  --prep_unflatten                        true
% 8.01/1.49  --prep_res_sim                          true
% 8.01/1.49  --prep_upred                            true
% 8.01/1.49  --prep_sem_filter                       exhaustive
% 8.01/1.49  --prep_sem_filter_out                   false
% 8.01/1.49  --pred_elim                             true
% 8.01/1.49  --res_sim_input                         true
% 8.01/1.49  --eq_ax_congr_red                       true
% 8.01/1.49  --pure_diseq_elim                       true
% 8.01/1.49  --brand_transform                       false
% 8.01/1.49  --non_eq_to_eq                          false
% 8.01/1.49  --prep_def_merge                        true
% 8.01/1.49  --prep_def_merge_prop_impl              false
% 8.01/1.49  --prep_def_merge_mbd                    true
% 8.01/1.49  --prep_def_merge_tr_red                 false
% 8.01/1.49  --prep_def_merge_tr_cl                  false
% 8.01/1.49  --smt_preprocessing                     true
% 8.01/1.49  --smt_ac_axioms                         fast
% 8.01/1.49  --preprocessed_out                      false
% 8.01/1.49  --preprocessed_stats                    false
% 8.01/1.49  
% 8.01/1.49  ------ Abstraction refinement Options
% 8.01/1.49  
% 8.01/1.49  --abstr_ref                             []
% 8.01/1.49  --abstr_ref_prep                        false
% 8.01/1.49  --abstr_ref_until_sat                   false
% 8.01/1.49  --abstr_ref_sig_restrict                funpre
% 8.01/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 8.01/1.49  --abstr_ref_under                       []
% 8.01/1.49  
% 8.01/1.49  ------ SAT Options
% 8.01/1.49  
% 8.01/1.49  --sat_mode                              false
% 8.01/1.49  --sat_fm_restart_options                ""
% 8.01/1.49  --sat_gr_def                            false
% 8.01/1.49  --sat_epr_types                         true
% 8.01/1.49  --sat_non_cyclic_types                  false
% 8.01/1.49  --sat_finite_models                     false
% 8.01/1.49  --sat_fm_lemmas                         false
% 8.01/1.49  --sat_fm_prep                           false
% 8.01/1.49  --sat_fm_uc_incr                        true
% 8.01/1.49  --sat_out_model                         small
% 8.01/1.49  --sat_out_clauses                       false
% 8.01/1.49  
% 8.01/1.49  ------ QBF Options
% 8.01/1.49  
% 8.01/1.49  --qbf_mode                              false
% 8.01/1.49  --qbf_elim_univ                         false
% 8.01/1.49  --qbf_dom_inst                          none
% 8.01/1.49  --qbf_dom_pre_inst                      false
% 8.01/1.49  --qbf_sk_in                             false
% 8.01/1.49  --qbf_pred_elim                         true
% 8.01/1.49  --qbf_split                             512
% 8.01/1.49  
% 8.01/1.49  ------ BMC1 Options
% 8.01/1.49  
% 8.01/1.49  --bmc1_incremental                      false
% 8.01/1.49  --bmc1_axioms                           reachable_all
% 8.01/1.49  --bmc1_min_bound                        0
% 8.01/1.49  --bmc1_max_bound                        -1
% 8.01/1.49  --bmc1_max_bound_default                -1
% 8.01/1.49  --bmc1_symbol_reachability              true
% 8.01/1.49  --bmc1_property_lemmas                  false
% 8.01/1.49  --bmc1_k_induction                      false
% 8.01/1.49  --bmc1_non_equiv_states                 false
% 8.01/1.49  --bmc1_deadlock                         false
% 8.01/1.49  --bmc1_ucm                              false
% 8.01/1.49  --bmc1_add_unsat_core                   none
% 8.01/1.49  --bmc1_unsat_core_children              false
% 8.01/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 8.01/1.49  --bmc1_out_stat                         full
% 8.01/1.49  --bmc1_ground_init                      false
% 8.01/1.49  --bmc1_pre_inst_next_state              false
% 8.01/1.49  --bmc1_pre_inst_state                   false
% 8.01/1.49  --bmc1_pre_inst_reach_state             false
% 8.01/1.49  --bmc1_out_unsat_core                   false
% 8.01/1.49  --bmc1_aig_witness_out                  false
% 8.01/1.49  --bmc1_verbose                          false
% 8.01/1.49  --bmc1_dump_clauses_tptp                false
% 8.01/1.49  --bmc1_dump_unsat_core_tptp             false
% 8.01/1.49  --bmc1_dump_file                        -
% 8.01/1.49  --bmc1_ucm_expand_uc_limit              128
% 8.01/1.49  --bmc1_ucm_n_expand_iterations          6
% 8.01/1.49  --bmc1_ucm_extend_mode                  1
% 8.01/1.49  --bmc1_ucm_init_mode                    2
% 8.01/1.49  --bmc1_ucm_cone_mode                    none
% 8.01/1.49  --bmc1_ucm_reduced_relation_type        0
% 8.01/1.49  --bmc1_ucm_relax_model                  4
% 8.01/1.49  --bmc1_ucm_full_tr_after_sat            true
% 8.01/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 8.01/1.49  --bmc1_ucm_layered_model                none
% 8.01/1.49  --bmc1_ucm_max_lemma_size               10
% 8.01/1.49  
% 8.01/1.49  ------ AIG Options
% 8.01/1.49  
% 8.01/1.49  --aig_mode                              false
% 8.01/1.49  
% 8.01/1.49  ------ Instantiation Options
% 8.01/1.49  
% 8.01/1.49  --instantiation_flag                    true
% 8.01/1.49  --inst_sos_flag                         true
% 8.01/1.49  --inst_sos_phase                        true
% 8.01/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 8.01/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 8.01/1.49  --inst_lit_sel_side                     num_symb
% 8.01/1.49  --inst_solver_per_active                1400
% 8.01/1.49  --inst_solver_calls_frac                1.
% 8.01/1.49  --inst_passive_queue_type               priority_queues
% 8.01/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 8.01/1.49  --inst_passive_queues_freq              [25;2]
% 8.01/1.49  --inst_dismatching                      true
% 8.01/1.49  --inst_eager_unprocessed_to_passive     true
% 8.01/1.49  --inst_prop_sim_given                   true
% 8.01/1.49  --inst_prop_sim_new                     false
% 8.01/1.49  --inst_subs_new                         false
% 8.01/1.49  --inst_eq_res_simp                      false
% 8.01/1.49  --inst_subs_given                       false
% 8.01/1.49  --inst_orphan_elimination               true
% 8.01/1.49  --inst_learning_loop_flag               true
% 8.01/1.49  --inst_learning_start                   3000
% 8.01/1.49  --inst_learning_factor                  2
% 8.01/1.49  --inst_start_prop_sim_after_learn       3
% 8.01/1.49  --inst_sel_renew                        solver
% 8.01/1.49  --inst_lit_activity_flag                true
% 8.01/1.49  --inst_restr_to_given                   false
% 8.01/1.49  --inst_activity_threshold               500
% 8.01/1.49  --inst_out_proof                        true
% 8.01/1.49  
% 8.01/1.49  ------ Resolution Options
% 8.01/1.49  
% 8.01/1.49  --resolution_flag                       true
% 8.01/1.49  --res_lit_sel                           adaptive
% 8.01/1.49  --res_lit_sel_side                      none
% 8.01/1.49  --res_ordering                          kbo
% 8.01/1.49  --res_to_prop_solver                    active
% 8.01/1.49  --res_prop_simpl_new                    false
% 8.01/1.49  --res_prop_simpl_given                  true
% 8.01/1.49  --res_passive_queue_type                priority_queues
% 8.01/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 8.01/1.49  --res_passive_queues_freq               [15;5]
% 8.01/1.49  --res_forward_subs                      full
% 8.01/1.49  --res_backward_subs                     full
% 8.01/1.49  --res_forward_subs_resolution           true
% 8.01/1.49  --res_backward_subs_resolution          true
% 8.01/1.49  --res_orphan_elimination                true
% 8.01/1.49  --res_time_limit                        2.
% 8.01/1.49  --res_out_proof                         true
% 8.01/1.49  
% 8.01/1.49  ------ Superposition Options
% 8.01/1.49  
% 8.01/1.49  --superposition_flag                    true
% 8.01/1.49  --sup_passive_queue_type                priority_queues
% 8.01/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 8.01/1.49  --sup_passive_queues_freq               [8;1;4]
% 8.01/1.49  --demod_completeness_check              fast
% 8.01/1.49  --demod_use_ground                      true
% 8.01/1.49  --sup_to_prop_solver                    passive
% 8.01/1.49  --sup_prop_simpl_new                    true
% 8.01/1.49  --sup_prop_simpl_given                  true
% 8.01/1.49  --sup_fun_splitting                     true
% 8.01/1.49  --sup_smt_interval                      50000
% 8.01/1.49  
% 8.01/1.49  ------ Superposition Simplification Setup
% 8.01/1.49  
% 8.01/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 8.01/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 8.01/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 8.01/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 8.01/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 8.01/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 8.01/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 8.01/1.49  --sup_immed_triv                        [TrivRules]
% 8.01/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 8.01/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 8.01/1.49  --sup_immed_bw_main                     []
% 8.01/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 8.01/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 8.01/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 8.01/1.49  --sup_input_bw                          []
% 8.01/1.49  
% 8.01/1.49  ------ Combination Options
% 8.01/1.49  
% 8.01/1.49  --comb_res_mult                         3
% 8.01/1.49  --comb_sup_mult                         2
% 8.01/1.49  --comb_inst_mult                        10
% 8.01/1.49  
% 8.01/1.49  ------ Debug Options
% 8.01/1.49  
% 8.01/1.49  --dbg_backtrace                         false
% 8.01/1.49  --dbg_dump_prop_clauses                 false
% 8.01/1.49  --dbg_dump_prop_clauses_file            -
% 8.01/1.49  --dbg_out_stat                          false
% 8.01/1.49  ------ Parsing...
% 8.01/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 8.01/1.49  
% 8.01/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 8.01/1.49  
% 8.01/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 8.01/1.49  
% 8.01/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.01/1.49  ------ Proving...
% 8.01/1.49  ------ Problem Properties 
% 8.01/1.49  
% 8.01/1.49  
% 8.01/1.49  clauses                                 16
% 8.01/1.49  conjectures                             2
% 8.01/1.49  EPR                                     3
% 8.01/1.49  Horn                                    16
% 8.01/1.49  unary                                   6
% 8.01/1.49  binary                                  7
% 8.01/1.49  lits                                    30
% 8.01/1.49  lits eq                                 6
% 8.01/1.49  fd_pure                                 0
% 8.01/1.49  fd_pseudo                               0
% 8.01/1.49  fd_cond                                 0
% 8.01/1.49  fd_pseudo_cond                          1
% 8.01/1.49  AC symbols                              0
% 8.01/1.49  
% 8.01/1.49  ------ Schedule dynamic 5 is on 
% 8.01/1.49  
% 8.01/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 8.01/1.49  
% 8.01/1.49  
% 8.01/1.49  ------ 
% 8.01/1.49  Current options:
% 8.01/1.49  ------ 
% 8.01/1.49  
% 8.01/1.49  ------ Input Options
% 8.01/1.49  
% 8.01/1.49  --out_options                           all
% 8.01/1.49  --tptp_safe_out                         true
% 8.01/1.49  --problem_path                          ""
% 8.01/1.49  --include_path                          ""
% 8.01/1.49  --clausifier                            res/vclausify_rel
% 8.01/1.49  --clausifier_options                    ""
% 8.01/1.49  --stdin                                 false
% 8.01/1.49  --stats_out                             all
% 8.01/1.49  
% 8.01/1.49  ------ General Options
% 8.01/1.49  
% 8.01/1.49  --fof                                   false
% 8.01/1.49  --time_out_real                         305.
% 8.01/1.49  --time_out_virtual                      -1.
% 8.01/1.49  --symbol_type_check                     false
% 8.01/1.49  --clausify_out                          false
% 8.01/1.49  --sig_cnt_out                           false
% 8.01/1.49  --trig_cnt_out                          false
% 8.01/1.49  --trig_cnt_out_tolerance                1.
% 8.01/1.49  --trig_cnt_out_sk_spl                   false
% 8.01/1.49  --abstr_cl_out                          false
% 8.01/1.49  
% 8.01/1.49  ------ Global Options
% 8.01/1.49  
% 8.01/1.49  --schedule                              default
% 8.01/1.49  --add_important_lit                     false
% 8.01/1.49  --prop_solver_per_cl                    1000
% 8.01/1.49  --min_unsat_core                        false
% 8.01/1.49  --soft_assumptions                      false
% 8.01/1.49  --soft_lemma_size                       3
% 8.01/1.49  --prop_impl_unit_size                   0
% 8.01/1.49  --prop_impl_unit                        []
% 8.01/1.49  --share_sel_clauses                     true
% 8.01/1.49  --reset_solvers                         false
% 8.01/1.49  --bc_imp_inh                            [conj_cone]
% 8.01/1.49  --conj_cone_tolerance                   3.
% 8.01/1.49  --extra_neg_conj                        none
% 8.01/1.49  --large_theory_mode                     true
% 8.01/1.49  --prolific_symb_bound                   200
% 8.01/1.49  --lt_threshold                          2000
% 8.01/1.49  --clause_weak_htbl                      true
% 8.01/1.49  --gc_record_bc_elim                     false
% 8.01/1.49  
% 8.01/1.49  ------ Preprocessing Options
% 8.01/1.49  
% 8.01/1.49  --preprocessing_flag                    true
% 8.01/1.49  --time_out_prep_mult                    0.1
% 8.01/1.49  --splitting_mode                        input
% 8.01/1.49  --splitting_grd                         true
% 8.01/1.49  --splitting_cvd                         false
% 8.01/1.49  --splitting_cvd_svl                     false
% 8.01/1.49  --splitting_nvd                         32
% 8.01/1.49  --sub_typing                            true
% 8.01/1.49  --prep_gs_sim                           true
% 8.01/1.49  --prep_unflatten                        true
% 8.01/1.49  --prep_res_sim                          true
% 8.01/1.49  --prep_upred                            true
% 8.01/1.49  --prep_sem_filter                       exhaustive
% 8.01/1.49  --prep_sem_filter_out                   false
% 8.01/1.49  --pred_elim                             true
% 8.01/1.49  --res_sim_input                         true
% 8.01/1.49  --eq_ax_congr_red                       true
% 8.01/1.49  --pure_diseq_elim                       true
% 8.01/1.49  --brand_transform                       false
% 8.01/1.49  --non_eq_to_eq                          false
% 8.01/1.49  --prep_def_merge                        true
% 8.01/1.49  --prep_def_merge_prop_impl              false
% 8.01/1.49  --prep_def_merge_mbd                    true
% 8.01/1.49  --prep_def_merge_tr_red                 false
% 8.01/1.49  --prep_def_merge_tr_cl                  false
% 8.01/1.49  --smt_preprocessing                     true
% 8.01/1.49  --smt_ac_axioms                         fast
% 8.01/1.49  --preprocessed_out                      false
% 8.01/1.49  --preprocessed_stats                    false
% 8.01/1.49  
% 8.01/1.49  ------ Abstraction refinement Options
% 8.01/1.49  
% 8.01/1.49  --abstr_ref                             []
% 8.01/1.49  --abstr_ref_prep                        false
% 8.01/1.49  --abstr_ref_until_sat                   false
% 8.01/1.49  --abstr_ref_sig_restrict                funpre
% 8.01/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 8.01/1.49  --abstr_ref_under                       []
% 8.01/1.49  
% 8.01/1.49  ------ SAT Options
% 8.01/1.49  
% 8.01/1.49  --sat_mode                              false
% 8.01/1.49  --sat_fm_restart_options                ""
% 8.01/1.49  --sat_gr_def                            false
% 8.01/1.49  --sat_epr_types                         true
% 8.01/1.49  --sat_non_cyclic_types                  false
% 8.01/1.49  --sat_finite_models                     false
% 8.01/1.49  --sat_fm_lemmas                         false
% 8.01/1.49  --sat_fm_prep                           false
% 8.01/1.49  --sat_fm_uc_incr                        true
% 8.01/1.49  --sat_out_model                         small
% 8.01/1.49  --sat_out_clauses                       false
% 8.01/1.49  
% 8.01/1.49  ------ QBF Options
% 8.01/1.49  
% 8.01/1.49  --qbf_mode                              false
% 8.01/1.49  --qbf_elim_univ                         false
% 8.01/1.49  --qbf_dom_inst                          none
% 8.01/1.49  --qbf_dom_pre_inst                      false
% 8.01/1.49  --qbf_sk_in                             false
% 8.01/1.49  --qbf_pred_elim                         true
% 8.01/1.49  --qbf_split                             512
% 8.01/1.49  
% 8.01/1.49  ------ BMC1 Options
% 8.01/1.49  
% 8.01/1.49  --bmc1_incremental                      false
% 8.01/1.49  --bmc1_axioms                           reachable_all
% 8.01/1.49  --bmc1_min_bound                        0
% 8.01/1.49  --bmc1_max_bound                        -1
% 8.01/1.49  --bmc1_max_bound_default                -1
% 8.01/1.49  --bmc1_symbol_reachability              true
% 8.01/1.49  --bmc1_property_lemmas                  false
% 8.01/1.49  --bmc1_k_induction                      false
% 8.01/1.49  --bmc1_non_equiv_states                 false
% 8.01/1.49  --bmc1_deadlock                         false
% 8.01/1.49  --bmc1_ucm                              false
% 8.01/1.49  --bmc1_add_unsat_core                   none
% 8.01/1.49  --bmc1_unsat_core_children              false
% 8.01/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 8.01/1.49  --bmc1_out_stat                         full
% 8.01/1.49  --bmc1_ground_init                      false
% 8.01/1.49  --bmc1_pre_inst_next_state              false
% 8.01/1.49  --bmc1_pre_inst_state                   false
% 8.01/1.49  --bmc1_pre_inst_reach_state             false
% 8.01/1.49  --bmc1_out_unsat_core                   false
% 8.01/1.49  --bmc1_aig_witness_out                  false
% 8.01/1.49  --bmc1_verbose                          false
% 8.01/1.49  --bmc1_dump_clauses_tptp                false
% 8.01/1.49  --bmc1_dump_unsat_core_tptp             false
% 8.01/1.49  --bmc1_dump_file                        -
% 8.01/1.49  --bmc1_ucm_expand_uc_limit              128
% 8.01/1.49  --bmc1_ucm_n_expand_iterations          6
% 8.01/1.49  --bmc1_ucm_extend_mode                  1
% 8.01/1.49  --bmc1_ucm_init_mode                    2
% 8.01/1.49  --bmc1_ucm_cone_mode                    none
% 8.01/1.49  --bmc1_ucm_reduced_relation_type        0
% 8.01/1.49  --bmc1_ucm_relax_model                  4
% 8.01/1.49  --bmc1_ucm_full_tr_after_sat            true
% 8.01/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 8.01/1.49  --bmc1_ucm_layered_model                none
% 8.01/1.49  --bmc1_ucm_max_lemma_size               10
% 8.01/1.49  
% 8.01/1.49  ------ AIG Options
% 8.01/1.49  
% 8.01/1.49  --aig_mode                              false
% 8.01/1.49  
% 8.01/1.49  ------ Instantiation Options
% 8.01/1.49  
% 8.01/1.49  --instantiation_flag                    true
% 8.01/1.49  --inst_sos_flag                         true
% 8.01/1.49  --inst_sos_phase                        true
% 8.01/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 8.01/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 8.01/1.49  --inst_lit_sel_side                     none
% 8.01/1.49  --inst_solver_per_active                1400
% 8.01/1.49  --inst_solver_calls_frac                1.
% 8.01/1.49  --inst_passive_queue_type               priority_queues
% 8.01/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 8.01/1.49  --inst_passive_queues_freq              [25;2]
% 8.01/1.49  --inst_dismatching                      true
% 8.01/1.49  --inst_eager_unprocessed_to_passive     true
% 8.01/1.49  --inst_prop_sim_given                   true
% 8.01/1.49  --inst_prop_sim_new                     false
% 8.01/1.49  --inst_subs_new                         false
% 8.01/1.49  --inst_eq_res_simp                      false
% 8.01/1.49  --inst_subs_given                       false
% 8.01/1.49  --inst_orphan_elimination               true
% 8.01/1.49  --inst_learning_loop_flag               true
% 8.01/1.49  --inst_learning_start                   3000
% 8.01/1.49  --inst_learning_factor                  2
% 8.01/1.49  --inst_start_prop_sim_after_learn       3
% 8.01/1.49  --inst_sel_renew                        solver
% 8.01/1.49  --inst_lit_activity_flag                true
% 8.01/1.49  --inst_restr_to_given                   false
% 8.01/1.49  --inst_activity_threshold               500
% 8.01/1.49  --inst_out_proof                        true
% 8.01/1.49  
% 8.01/1.49  ------ Resolution Options
% 8.01/1.49  
% 8.01/1.49  --resolution_flag                       false
% 8.01/1.49  --res_lit_sel                           adaptive
% 8.01/1.49  --res_lit_sel_side                      none
% 8.01/1.49  --res_ordering                          kbo
% 8.01/1.49  --res_to_prop_solver                    active
% 8.01/1.49  --res_prop_simpl_new                    false
% 8.01/1.49  --res_prop_simpl_given                  true
% 8.01/1.49  --res_passive_queue_type                priority_queues
% 8.01/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 8.01/1.49  --res_passive_queues_freq               [15;5]
% 8.01/1.49  --res_forward_subs                      full
% 8.01/1.49  --res_backward_subs                     full
% 8.01/1.49  --res_forward_subs_resolution           true
% 8.01/1.49  --res_backward_subs_resolution          true
% 8.01/1.49  --res_orphan_elimination                true
% 8.01/1.49  --res_time_limit                        2.
% 8.01/1.49  --res_out_proof                         true
% 8.01/1.49  
% 8.01/1.49  ------ Superposition Options
% 8.01/1.49  
% 8.01/1.49  --superposition_flag                    true
% 8.01/1.49  --sup_passive_queue_type                priority_queues
% 8.01/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 8.01/1.49  --sup_passive_queues_freq               [8;1;4]
% 8.01/1.49  --demod_completeness_check              fast
% 8.01/1.49  --demod_use_ground                      true
% 8.01/1.49  --sup_to_prop_solver                    passive
% 8.01/1.49  --sup_prop_simpl_new                    true
% 8.01/1.49  --sup_prop_simpl_given                  true
% 8.01/1.49  --sup_fun_splitting                     true
% 8.01/1.49  --sup_smt_interval                      50000
% 8.01/1.49  
% 8.01/1.49  ------ Superposition Simplification Setup
% 8.01/1.49  
% 8.01/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 8.01/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 8.01/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 8.01/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 8.01/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 8.01/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 8.01/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 8.01/1.49  --sup_immed_triv                        [TrivRules]
% 8.01/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 8.01/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 8.01/1.49  --sup_immed_bw_main                     []
% 8.01/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 8.01/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 8.01/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 8.01/1.49  --sup_input_bw                          []
% 8.01/1.49  
% 8.01/1.49  ------ Combination Options
% 8.01/1.49  
% 8.01/1.49  --comb_res_mult                         3
% 8.01/1.49  --comb_sup_mult                         2
% 8.01/1.49  --comb_inst_mult                        10
% 8.01/1.49  
% 8.01/1.49  ------ Debug Options
% 8.01/1.49  
% 8.01/1.49  --dbg_backtrace                         false
% 8.01/1.49  --dbg_dump_prop_clauses                 false
% 8.01/1.49  --dbg_dump_prop_clauses_file            -
% 8.01/1.49  --dbg_out_stat                          false
% 8.01/1.49  
% 8.01/1.49  
% 8.01/1.49  
% 8.01/1.49  
% 8.01/1.49  ------ Proving...
% 8.01/1.49  
% 8.01/1.49  
% 8.01/1.49  % SZS status Theorem for theBenchmark.p
% 8.01/1.49  
% 8.01/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 8.01/1.49  
% 8.01/1.49  fof(f7,axiom,(
% 8.01/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_tops_1(X1,X0) <=> (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)))))),
% 8.01/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.01/1.49  
% 8.01/1.49  fof(f24,plain,(
% 8.01/1.49    ! [X0] : (! [X1] : ((v4_tops_1(X1,X0) <=> (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 8.01/1.49    inference(ennf_transformation,[],[f7])).
% 8.01/1.49  
% 8.01/1.49  fof(f44,plain,(
% 8.01/1.49    ! [X0] : (! [X1] : (((v4_tops_1(X1,X0) | (~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1))) & ((r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) | ~v4_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 8.01/1.49    inference(nnf_transformation,[],[f24])).
% 8.01/1.49  
% 8.01/1.49  fof(f45,plain,(
% 8.01/1.49    ! [X0] : (! [X1] : (((v4_tops_1(X1,X0) | ~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) & ((r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) | ~v4_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 8.01/1.49    inference(flattening,[],[f44])).
% 8.01/1.49  
% 8.01/1.49  fof(f59,plain,(
% 8.01/1.49    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) | ~v4_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 8.01/1.49    inference(cnf_transformation,[],[f45])).
% 8.01/1.49  
% 8.01/1.49  fof(f16,conjecture,(
% 8.01/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_tops_1(X1,X0) => k1_xboole_0 = k1_tops_1(X0,k2_tops_1(X0,X1)))))),
% 8.01/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.01/1.49  
% 8.01/1.49  fof(f17,negated_conjecture,(
% 8.01/1.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_tops_1(X1,X0) => k1_xboole_0 = k1_tops_1(X0,k2_tops_1(X0,X1)))))),
% 8.01/1.49    inference(negated_conjecture,[],[f16])).
% 8.01/1.49  
% 8.01/1.49  fof(f39,plain,(
% 8.01/1.49    ? [X0] : (? [X1] : ((k1_xboole_0 != k1_tops_1(X0,k2_tops_1(X0,X1)) & v4_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 8.01/1.49    inference(ennf_transformation,[],[f17])).
% 8.01/1.49  
% 8.01/1.49  fof(f40,plain,(
% 8.01/1.49    ? [X0] : (? [X1] : (k1_xboole_0 != k1_tops_1(X0,k2_tops_1(X0,X1)) & v4_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 8.01/1.49    inference(flattening,[],[f39])).
% 8.01/1.49  
% 8.01/1.49  fof(f48,plain,(
% 8.01/1.49    ( ! [X0] : (? [X1] : (k1_xboole_0 != k1_tops_1(X0,k2_tops_1(X0,X1)) & v4_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (k1_xboole_0 != k1_tops_1(X0,k2_tops_1(X0,sK1)) & v4_tops_1(sK1,X0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 8.01/1.49    introduced(choice_axiom,[])).
% 8.01/1.49  
% 8.01/1.49  fof(f47,plain,(
% 8.01/1.49    ? [X0] : (? [X1] : (k1_xboole_0 != k1_tops_1(X0,k2_tops_1(X0,X1)) & v4_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (k1_xboole_0 != k1_tops_1(sK0,k2_tops_1(sK0,X1)) & v4_tops_1(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 8.01/1.49    introduced(choice_axiom,[])).
% 8.01/1.49  
% 8.01/1.49  fof(f49,plain,(
% 8.01/1.49    (k1_xboole_0 != k1_tops_1(sK0,k2_tops_1(sK0,sK1)) & v4_tops_1(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 8.01/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f40,f48,f47])).
% 8.01/1.49  
% 8.01/1.49  fof(f74,plain,(
% 8.01/1.49    v4_tops_1(sK1,sK0)),
% 8.01/1.49    inference(cnf_transformation,[],[f49])).
% 8.01/1.49  
% 8.01/1.49  fof(f72,plain,(
% 8.01/1.49    l1_pre_topc(sK0)),
% 8.01/1.49    inference(cnf_transformation,[],[f49])).
% 8.01/1.49  
% 8.01/1.49  fof(f73,plain,(
% 8.01/1.49    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 8.01/1.49    inference(cnf_transformation,[],[f49])).
% 8.01/1.49  
% 8.01/1.49  fof(f3,axiom,(
% 8.01/1.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 8.01/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.01/1.49  
% 8.01/1.49  fof(f18,plain,(
% 8.01/1.49    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 8.01/1.49    inference(ennf_transformation,[],[f3])).
% 8.01/1.49  
% 8.01/1.49  fof(f19,plain,(
% 8.01/1.49    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 8.01/1.49    inference(flattening,[],[f18])).
% 8.01/1.49  
% 8.01/1.49  fof(f54,plain,(
% 8.01/1.49    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 8.01/1.49    inference(cnf_transformation,[],[f19])).
% 8.01/1.49  
% 8.01/1.49  fof(f12,axiom,(
% 8.01/1.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)))),
% 8.01/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.01/1.49  
% 8.01/1.49  fof(f32,plain,(
% 8.01/1.49    ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 8.01/1.49    inference(ennf_transformation,[],[f12])).
% 8.01/1.49  
% 8.01/1.49  fof(f33,plain,(
% 8.01/1.49    ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 8.01/1.49    inference(flattening,[],[f32])).
% 8.01/1.49  
% 8.01/1.49  fof(f66,plain,(
% 8.01/1.49    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 8.01/1.49    inference(cnf_transformation,[],[f33])).
% 8.01/1.49  
% 8.01/1.49  fof(f13,axiom,(
% 8.01/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 8.01/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.01/1.49  
% 8.01/1.49  fof(f34,plain,(
% 8.01/1.49    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 8.01/1.49    inference(ennf_transformation,[],[f13])).
% 8.01/1.49  
% 8.01/1.49  fof(f35,plain,(
% 8.01/1.49    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 8.01/1.49    inference(flattening,[],[f34])).
% 8.01/1.49  
% 8.01/1.49  fof(f67,plain,(
% 8.01/1.49    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 8.01/1.49    inference(cnf_transformation,[],[f35])).
% 8.01/1.49  
% 8.01/1.49  fof(f8,axiom,(
% 8.01/1.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 8.01/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.01/1.49  
% 8.01/1.49  fof(f25,plain,(
% 8.01/1.49    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 8.01/1.49    inference(ennf_transformation,[],[f8])).
% 8.01/1.49  
% 8.01/1.49  fof(f26,plain,(
% 8.01/1.49    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 8.01/1.49    inference(flattening,[],[f25])).
% 8.01/1.49  
% 8.01/1.49  fof(f62,plain,(
% 8.01/1.49    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 8.01/1.49    inference(cnf_transformation,[],[f26])).
% 8.01/1.49  
% 8.01/1.49  fof(f1,axiom,(
% 8.01/1.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 8.01/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.01/1.49  
% 8.01/1.49  fof(f41,plain,(
% 8.01/1.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 8.01/1.49    inference(nnf_transformation,[],[f1])).
% 8.01/1.49  
% 8.01/1.49  fof(f42,plain,(
% 8.01/1.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 8.01/1.49    inference(flattening,[],[f41])).
% 8.01/1.49  
% 8.01/1.49  fof(f52,plain,(
% 8.01/1.49    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 8.01/1.49    inference(cnf_transformation,[],[f42])).
% 8.01/1.49  
% 8.01/1.49  fof(f5,axiom,(
% 8.01/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 8.01/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.01/1.49  
% 8.01/1.49  fof(f22,plain,(
% 8.01/1.49    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 8.01/1.49    inference(ennf_transformation,[],[f5])).
% 8.01/1.49  
% 8.01/1.49  fof(f56,plain,(
% 8.01/1.49    ( ! [X0,X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 8.01/1.49    inference(cnf_transformation,[],[f22])).
% 8.01/1.49  
% 8.01/1.49  fof(f11,axiom,(
% 8.01/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 8.01/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.01/1.49  
% 8.01/1.49  fof(f31,plain,(
% 8.01/1.49    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 8.01/1.49    inference(ennf_transformation,[],[f11])).
% 8.01/1.49  
% 8.01/1.49  fof(f65,plain,(
% 8.01/1.49    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 8.01/1.49    inference(cnf_transformation,[],[f31])).
% 8.01/1.49  
% 8.01/1.49  fof(f4,axiom,(
% 8.01/1.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)))),
% 8.01/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.01/1.49  
% 8.01/1.49  fof(f20,plain,(
% 8.01/1.49    ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 8.01/1.49    inference(ennf_transformation,[],[f4])).
% 8.01/1.49  
% 8.01/1.49  fof(f21,plain,(
% 8.01/1.49    ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 8.01/1.49    inference(flattening,[],[f20])).
% 8.01/1.49  
% 8.01/1.49  fof(f55,plain,(
% 8.01/1.49    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 8.01/1.49    inference(cnf_transformation,[],[f21])).
% 8.01/1.49  
% 8.01/1.49  fof(f9,axiom,(
% 8.01/1.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 8.01/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.01/1.49  
% 8.01/1.49  fof(f27,plain,(
% 8.01/1.49    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 8.01/1.49    inference(ennf_transformation,[],[f9])).
% 8.01/1.49  
% 8.01/1.49  fof(f28,plain,(
% 8.01/1.49    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 8.01/1.49    inference(flattening,[],[f27])).
% 8.01/1.49  
% 8.01/1.49  fof(f63,plain,(
% 8.01/1.49    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 8.01/1.49    inference(cnf_transformation,[],[f28])).
% 8.01/1.49  
% 8.01/1.49  fof(f14,axiom,(
% 8.01/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 8.01/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.01/1.49  
% 8.01/1.49  fof(f36,plain,(
% 8.01/1.49    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 8.01/1.49    inference(ennf_transformation,[],[f14])).
% 8.01/1.49  
% 8.01/1.49  fof(f46,plain,(
% 8.01/1.49    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1)) & (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 8.01/1.49    inference(nnf_transformation,[],[f36])).
% 8.01/1.49  
% 8.01/1.49  fof(f68,plain,(
% 8.01/1.49    ( ! [X0,X1] : (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 8.01/1.49    inference(cnf_transformation,[],[f46])).
% 8.01/1.49  
% 8.01/1.49  fof(f6,axiom,(
% 8.01/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tops_1(X1,X0) <=> v2_tops_1(k2_pre_topc(X0,X1),X0))))),
% 8.01/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.01/1.49  
% 8.01/1.49  fof(f23,plain,(
% 8.01/1.49    ! [X0] : (! [X1] : ((v3_tops_1(X1,X0) <=> v2_tops_1(k2_pre_topc(X0,X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 8.01/1.49    inference(ennf_transformation,[],[f6])).
% 8.01/1.49  
% 8.01/1.49  fof(f43,plain,(
% 8.01/1.49    ! [X0] : (! [X1] : (((v3_tops_1(X1,X0) | ~v2_tops_1(k2_pre_topc(X0,X1),X0)) & (v2_tops_1(k2_pre_topc(X0,X1),X0) | ~v3_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 8.01/1.49    inference(nnf_transformation,[],[f23])).
% 8.01/1.49  
% 8.01/1.49  fof(f57,plain,(
% 8.01/1.49    ( ! [X0,X1] : (v2_tops_1(k2_pre_topc(X0,X1),X0) | ~v3_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 8.01/1.49    inference(cnf_transformation,[],[f43])).
% 8.01/1.49  
% 8.01/1.49  fof(f10,axiom,(
% 8.01/1.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_pre_topc(X0,X1),X0))),
% 8.01/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.01/1.49  
% 8.01/1.49  fof(f29,plain,(
% 8.01/1.49    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 8.01/1.49    inference(ennf_transformation,[],[f10])).
% 8.01/1.49  
% 8.01/1.49  fof(f30,plain,(
% 8.01/1.49    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 8.01/1.49    inference(flattening,[],[f29])).
% 8.01/1.49  
% 8.01/1.49  fof(f64,plain,(
% 8.01/1.49    ( ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 8.01/1.49    inference(cnf_transformation,[],[f30])).
% 8.01/1.49  
% 8.01/1.49  fof(f15,axiom,(
% 8.01/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => v3_tops_1(k2_tops_1(X0,X1),X0))))),
% 8.01/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.01/1.49  
% 8.01/1.49  fof(f37,plain,(
% 8.01/1.49    ! [X0] : (! [X1] : ((v3_tops_1(k2_tops_1(X0,X1),X0) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 8.01/1.49    inference(ennf_transformation,[],[f15])).
% 8.01/1.49  
% 8.01/1.49  fof(f38,plain,(
% 8.01/1.49    ! [X0] : (! [X1] : (v3_tops_1(k2_tops_1(X0,X1),X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 8.01/1.49    inference(flattening,[],[f37])).
% 8.01/1.49  
% 8.01/1.49  fof(f70,plain,(
% 8.01/1.49    ( ! [X0,X1] : (v3_tops_1(k2_tops_1(X0,X1),X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 8.01/1.49    inference(cnf_transformation,[],[f38])).
% 8.01/1.49  
% 8.01/1.49  fof(f71,plain,(
% 8.01/1.49    v2_pre_topc(sK0)),
% 8.01/1.49    inference(cnf_transformation,[],[f49])).
% 8.01/1.49  
% 8.01/1.49  fof(f2,axiom,(
% 8.01/1.49    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 8.01/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.01/1.49  
% 8.01/1.49  fof(f53,plain,(
% 8.01/1.49    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 8.01/1.49    inference(cnf_transformation,[],[f2])).
% 8.01/1.49  
% 8.01/1.49  fof(f75,plain,(
% 8.01/1.49    k1_xboole_0 != k1_tops_1(sK0,k2_tops_1(sK0,sK1))),
% 8.01/1.49    inference(cnf_transformation,[],[f49])).
% 8.01/1.49  
% 8.01/1.49  cnf(c_11,plain,
% 8.01/1.49      ( ~ v4_tops_1(X0,X1)
% 8.01/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 8.01/1.49      | r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
% 8.01/1.49      | ~ l1_pre_topc(X1) ),
% 8.01/1.49      inference(cnf_transformation,[],[f59]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_22,negated_conjecture,
% 8.01/1.49      ( v4_tops_1(sK1,sK0) ),
% 8.01/1.49      inference(cnf_transformation,[],[f74]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_386,plain,
% 8.01/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 8.01/1.49      | r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
% 8.01/1.49      | ~ l1_pre_topc(X1)
% 8.01/1.49      | sK1 != X0
% 8.01/1.49      | sK0 != X1 ),
% 8.01/1.49      inference(resolution_lifted,[status(thm)],[c_11,c_22]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_387,plain,
% 8.01/1.49      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 8.01/1.49      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK1)
% 8.01/1.49      | ~ l1_pre_topc(sK0) ),
% 8.01/1.49      inference(unflattening,[status(thm)],[c_386]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_24,negated_conjecture,
% 8.01/1.49      ( l1_pre_topc(sK0) ),
% 8.01/1.49      inference(cnf_transformation,[],[f72]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_23,negated_conjecture,
% 8.01/1.49      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 8.01/1.49      inference(cnf_transformation,[],[f73]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_389,plain,
% 8.01/1.49      ( r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK1) ),
% 8.01/1.49      inference(global_propositional_subsumption,
% 8.01/1.49                [status(thm)],
% 8.01/1.49                [c_387,c_24,c_23]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_928,plain,
% 8.01/1.49      ( r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK1) = iProver_top ),
% 8.01/1.49      inference(predicate_to_equality,[status(thm)],[c_389]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_929,plain,
% 8.01/1.49      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 8.01/1.49      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_4,plain,
% 8.01/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 8.01/1.49      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 8.01/1.49      | ~ l1_pre_topc(X1) ),
% 8.01/1.49      inference(cnf_transformation,[],[f54]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_502,plain,
% 8.01/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 8.01/1.49      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 8.01/1.49      | sK0 != X1 ),
% 8.01/1.49      inference(resolution_lifted,[status(thm)],[c_4,c_24]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_503,plain,
% 8.01/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 8.01/1.49      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 8.01/1.49      inference(unflattening,[status(thm)],[c_502]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_919,plain,
% 8.01/1.49      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.01/1.49      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 8.01/1.49      inference(predicate_to_equality,[status(thm)],[c_503]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_16,plain,
% 8.01/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 8.01/1.49      | ~ l1_pre_topc(X1)
% 8.01/1.49      | k1_tops_1(X1,k1_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
% 8.01/1.49      inference(cnf_transformation,[],[f66]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_430,plain,
% 8.01/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 8.01/1.49      | k1_tops_1(X1,k1_tops_1(X1,X0)) = k1_tops_1(X1,X0)
% 8.01/1.49      | sK0 != X1 ),
% 8.01/1.49      inference(resolution_lifted,[status(thm)],[c_16,c_24]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_431,plain,
% 8.01/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 8.01/1.49      | k1_tops_1(sK0,k1_tops_1(sK0,X0)) = k1_tops_1(sK0,X0) ),
% 8.01/1.49      inference(unflattening,[status(thm)],[c_430]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_925,plain,
% 8.01/1.49      ( k1_tops_1(sK0,k1_tops_1(sK0,X0)) = k1_tops_1(sK0,X0)
% 8.01/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 8.01/1.49      inference(predicate_to_equality,[status(thm)],[c_431]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_1870,plain,
% 8.01/1.49      ( k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,X0))) = k1_tops_1(sK0,k2_pre_topc(sK0,X0))
% 8.01/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 8.01/1.49      inference(superposition,[status(thm)],[c_919,c_925]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_3427,plain,
% 8.01/1.49      ( k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) = k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) ),
% 8.01/1.49      inference(superposition,[status(thm)],[c_929,c_1870]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_17,plain,
% 8.01/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 8.01/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 8.01/1.49      | ~ r1_tarski(X0,X2)
% 8.01/1.49      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 8.01/1.49      | ~ l1_pre_topc(X1) ),
% 8.01/1.49      inference(cnf_transformation,[],[f67]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_412,plain,
% 8.01/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 8.01/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 8.01/1.49      | ~ r1_tarski(X0,X2)
% 8.01/1.49      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 8.01/1.49      | sK0 != X1 ),
% 8.01/1.49      inference(resolution_lifted,[status(thm)],[c_17,c_24]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_413,plain,
% 8.01/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 8.01/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 8.01/1.49      | ~ r1_tarski(X0,X1)
% 8.01/1.49      | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,X1)) ),
% 8.01/1.49      inference(unflattening,[status(thm)],[c_412]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_926,plain,
% 8.01/1.49      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.01/1.49      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.01/1.49      | r1_tarski(X0,X1) != iProver_top
% 8.01/1.49      | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,X1)) = iProver_top ),
% 8.01/1.49      inference(predicate_to_equality,[status(thm)],[c_413]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_3445,plain,
% 8.01/1.49      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.01/1.49      | m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.01/1.49      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),X0) != iProver_top
% 8.01/1.49      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,X0)) = iProver_top ),
% 8.01/1.49      inference(superposition,[status(thm)],[c_3427,c_926]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_28,plain,
% 8.01/1.49      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 8.01/1.49      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_977,plain,
% 8.01/1.49      ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 8.01/1.49      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 8.01/1.49      inference(instantiation,[status(thm)],[c_503]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_978,plain,
% 8.01/1.49      ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 8.01/1.49      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 8.01/1.49      inference(predicate_to_equality,[status(thm)],[c_977]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_12,plain,
% 8.01/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 8.01/1.49      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 8.01/1.49      | ~ l1_pre_topc(X1) ),
% 8.01/1.49      inference(cnf_transformation,[],[f62]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_466,plain,
% 8.01/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 8.01/1.49      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 8.01/1.49      | sK0 != X1 ),
% 8.01/1.49      inference(resolution_lifted,[status(thm)],[c_12,c_24]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_467,plain,
% 8.01/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 8.01/1.49      | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 8.01/1.49      inference(unflattening,[status(thm)],[c_466]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_1088,plain,
% 8.01/1.49      ( m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
% 8.01/1.49      | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 8.01/1.49      inference(instantiation,[status(thm)],[c_467]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_1092,plain,
% 8.01/1.49      ( m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 8.01/1.49      | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 8.01/1.49      inference(predicate_to_equality,[status(thm)],[c_1088]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_12168,plain,
% 8.01/1.49      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.01/1.49      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),X0) != iProver_top
% 8.01/1.49      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,X0)) = iProver_top ),
% 8.01/1.49      inference(global_propositional_subsumption,
% 8.01/1.49                [status(thm)],
% 8.01/1.49                [c_3445,c_28,c_978,c_1092]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_0,plain,
% 8.01/1.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 8.01/1.49      inference(cnf_transformation,[],[f52]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_932,plain,
% 8.01/1.49      ( X0 = X1
% 8.01/1.49      | r1_tarski(X0,X1) != iProver_top
% 8.01/1.49      | r1_tarski(X1,X0) != iProver_top ),
% 8.01/1.49      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_2086,plain,
% 8.01/1.49      ( k1_tops_1(sK0,X0) = k1_tops_1(sK0,X1)
% 8.01/1.49      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.01/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.01/1.49      | r1_tarski(X1,X0) != iProver_top
% 8.01/1.49      | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,X1)) != iProver_top ),
% 8.01/1.49      inference(superposition,[status(thm)],[c_926,c_932]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_12196,plain,
% 8.01/1.49      ( k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,X0)
% 8.01/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.01/1.49      | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.01/1.49      | r1_tarski(X0,k2_pre_topc(sK0,sK1)) != iProver_top
% 8.01/1.49      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),X0) != iProver_top ),
% 8.01/1.49      inference(superposition,[status(thm)],[c_12168,c_2086]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_26172,plain,
% 8.01/1.49      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.01/1.49      | k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,X0)
% 8.01/1.49      | r1_tarski(X0,k2_pre_topc(sK0,sK1)) != iProver_top
% 8.01/1.49      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),X0) != iProver_top ),
% 8.01/1.49      inference(global_propositional_subsumption,
% 8.01/1.49                [status(thm)],
% 8.01/1.49                [c_12196,c_28,c_978]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_26173,plain,
% 8.01/1.49      ( k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,X0)
% 8.01/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.01/1.49      | r1_tarski(X0,k2_pre_topc(sK0,sK1)) != iProver_top
% 8.01/1.49      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),X0) != iProver_top ),
% 8.01/1.49      inference(renaming,[status(thm)],[c_26172]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_26179,plain,
% 8.01/1.49      ( k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,sK1)
% 8.01/1.49      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.01/1.49      | r1_tarski(sK1,k2_pre_topc(sK0,sK1)) != iProver_top ),
% 8.01/1.49      inference(superposition,[status(thm)],[c_928,c_26173]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_6,plain,
% 8.01/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 8.01/1.49      | r1_tarski(X0,k2_pre_topc(X1,X0))
% 8.01/1.49      | ~ l1_pre_topc(X1) ),
% 8.01/1.49      inference(cnf_transformation,[],[f56]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_478,plain,
% 8.01/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 8.01/1.49      | r1_tarski(X0,k2_pre_topc(X1,X0))
% 8.01/1.49      | sK0 != X1 ),
% 8.01/1.49      inference(resolution_lifted,[status(thm)],[c_6,c_24]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_479,plain,
% 8.01/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 8.01/1.49      | r1_tarski(X0,k2_pre_topc(sK0,X0)) ),
% 8.01/1.49      inference(unflattening,[status(thm)],[c_478]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_985,plain,
% 8.01/1.49      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 8.01/1.49      | r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
% 8.01/1.49      inference(instantiation,[status(thm)],[c_479]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_986,plain,
% 8.01/1.49      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.01/1.49      | r1_tarski(sK1,k2_pre_topc(sK0,sK1)) = iProver_top ),
% 8.01/1.49      inference(predicate_to_equality,[status(thm)],[c_985]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_26830,plain,
% 8.01/1.49      ( k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
% 8.01/1.49      inference(global_propositional_subsumption,
% 8.01/1.49                [status(thm)],
% 8.01/1.49                [c_26179,c_28,c_986]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_15,plain,
% 8.01/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 8.01/1.49      | ~ l1_pre_topc(X1)
% 8.01/1.49      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
% 8.01/1.49      inference(cnf_transformation,[],[f65]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_442,plain,
% 8.01/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 8.01/1.49      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0)
% 8.01/1.49      | sK0 != X1 ),
% 8.01/1.49      inference(resolution_lifted,[status(thm)],[c_15,c_24]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_443,plain,
% 8.01/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 8.01/1.49      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
% 8.01/1.49      inference(unflattening,[status(thm)],[c_442]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_924,plain,
% 8.01/1.49      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0)
% 8.01/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 8.01/1.49      inference(predicate_to_equality,[status(thm)],[c_443]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_1986,plain,
% 8.01/1.49      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_pre_topc(sK0,X0)),k1_tops_1(sK0,k2_pre_topc(sK0,X0))) = k2_tops_1(sK0,k2_pre_topc(sK0,X0))
% 8.01/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 8.01/1.49      inference(superposition,[status(thm)],[c_919,c_924]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_4892,plain,
% 8.01/1.49      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) = k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) ),
% 8.01/1.49      inference(superposition,[status(thm)],[c_929,c_1986]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_5,plain,
% 8.01/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 8.01/1.49      | ~ l1_pre_topc(X1)
% 8.01/1.49      | k2_pre_topc(X1,k2_pre_topc(X1,X0)) = k2_pre_topc(X1,X0) ),
% 8.01/1.49      inference(cnf_transformation,[],[f55]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_490,plain,
% 8.01/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 8.01/1.49      | k2_pre_topc(X1,k2_pre_topc(X1,X0)) = k2_pre_topc(X1,X0)
% 8.01/1.49      | sK0 != X1 ),
% 8.01/1.49      inference(resolution_lifted,[status(thm)],[c_5,c_24]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_491,plain,
% 8.01/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 8.01/1.49      | k2_pre_topc(sK0,k2_pre_topc(sK0,X0)) = k2_pre_topc(sK0,X0) ),
% 8.01/1.49      inference(unflattening,[status(thm)],[c_490]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_920,plain,
% 8.01/1.49      ( k2_pre_topc(sK0,k2_pre_topc(sK0,X0)) = k2_pre_topc(sK0,X0)
% 8.01/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 8.01/1.49      inference(predicate_to_equality,[status(thm)],[c_491]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_1290,plain,
% 8.01/1.49      ( k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 8.01/1.49      inference(superposition,[status(thm)],[c_929,c_920]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_4898,plain,
% 8.01/1.49      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) = k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) ),
% 8.01/1.49      inference(light_normalisation,[status(thm)],[c_4892,c_1290]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_26854,plain,
% 8.01/1.49      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) ),
% 8.01/1.49      inference(demodulation,[status(thm)],[c_26830,c_4898]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_1983,plain,
% 8.01/1.49      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 8.01/1.49      inference(superposition,[status(thm)],[c_929,c_924]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_26859,plain,
% 8.01/1.49      ( k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 8.01/1.49      inference(light_normalisation,[status(thm)],[c_26854,c_1983]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_13,plain,
% 8.01/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 8.01/1.49      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 8.01/1.49      | ~ l1_pre_topc(X1) ),
% 8.01/1.49      inference(cnf_transformation,[],[f63]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_454,plain,
% 8.01/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 8.01/1.49      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 8.01/1.49      | sK0 != X1 ),
% 8.01/1.49      inference(resolution_lifted,[status(thm)],[c_13,c_24]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_455,plain,
% 8.01/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 8.01/1.49      | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 8.01/1.49      inference(unflattening,[status(thm)],[c_454]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_923,plain,
% 8.01/1.49      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.01/1.49      | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 8.01/1.49      inference(predicate_to_equality,[status(thm)],[c_455]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_1868,plain,
% 8.01/1.49      ( k1_tops_1(sK0,k1_tops_1(sK0,k2_tops_1(sK0,X0))) = k1_tops_1(sK0,k2_tops_1(sK0,X0))
% 8.01/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 8.01/1.49      inference(superposition,[status(thm)],[c_923,c_925]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_3376,plain,
% 8.01/1.49      ( k1_tops_1(sK0,k1_tops_1(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,X0)))) = k1_tops_1(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,X0)))
% 8.01/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 8.01/1.49      inference(superposition,[status(thm)],[c_919,c_1868]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_10075,plain,
% 8.01/1.49      ( k1_tops_1(sK0,k1_tops_1(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1)))) = k1_tops_1(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))) ),
% 8.01/1.49      inference(superposition,[status(thm)],[c_929,c_3376]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_922,plain,
% 8.01/1.49      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.01/1.49      | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 8.01/1.49      inference(predicate_to_equality,[status(thm)],[c_467]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_19,plain,
% 8.01/1.49      ( ~ v2_tops_1(X0,X1)
% 8.01/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 8.01/1.49      | ~ l1_pre_topc(X1)
% 8.01/1.49      | k1_tops_1(X1,X0) = k1_xboole_0 ),
% 8.01/1.49      inference(cnf_transformation,[],[f68]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_8,plain,
% 8.01/1.49      ( v2_tops_1(k2_pre_topc(X0,X1),X0)
% 8.01/1.49      | ~ v3_tops_1(X1,X0)
% 8.01/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 8.01/1.49      | ~ l1_pre_topc(X0) ),
% 8.01/1.49      inference(cnf_transformation,[],[f57]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_14,plain,
% 8.01/1.49      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
% 8.01/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 8.01/1.49      | ~ v2_pre_topc(X0)
% 8.01/1.49      | ~ l1_pre_topc(X0) ),
% 8.01/1.49      inference(cnf_transformation,[],[f64]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_20,plain,
% 8.01/1.49      ( ~ v4_pre_topc(X0,X1)
% 8.01/1.49      | v3_tops_1(k2_tops_1(X1,X0),X1)
% 8.01/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 8.01/1.49      | ~ v2_pre_topc(X1)
% 8.01/1.49      | ~ l1_pre_topc(X1) ),
% 8.01/1.49      inference(cnf_transformation,[],[f70]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_279,plain,
% 8.01/1.49      ( v3_tops_1(k2_tops_1(X0,X1),X0)
% 8.01/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 8.01/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 8.01/1.49      | ~ v2_pre_topc(X3)
% 8.01/1.49      | ~ v2_pre_topc(X0)
% 8.01/1.49      | ~ l1_pre_topc(X3)
% 8.01/1.49      | ~ l1_pre_topc(X0)
% 8.01/1.49      | X0 != X3
% 8.01/1.49      | k2_pre_topc(X3,X2) != X1 ),
% 8.01/1.49      inference(resolution_lifted,[status(thm)],[c_14,c_20]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_280,plain,
% 8.01/1.49      ( v3_tops_1(k2_tops_1(X0,k2_pre_topc(X0,X1)),X0)
% 8.01/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 8.01/1.49      | ~ m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
% 8.01/1.49      | ~ v2_pre_topc(X0)
% 8.01/1.49      | ~ l1_pre_topc(X0) ),
% 8.01/1.49      inference(unflattening,[status(thm)],[c_279]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_294,plain,
% 8.01/1.49      ( v3_tops_1(k2_tops_1(X0,k2_pre_topc(X0,X1)),X0)
% 8.01/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 8.01/1.49      | ~ v2_pre_topc(X0)
% 8.01/1.49      | ~ l1_pre_topc(X0) ),
% 8.01/1.49      inference(forward_subsumption_resolution,[status(thm)],[c_280,c_4]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_25,negated_conjecture,
% 8.01/1.49      ( v2_pre_topc(sK0) ),
% 8.01/1.49      inference(cnf_transformation,[],[f71]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_307,plain,
% 8.01/1.49      ( v3_tops_1(k2_tops_1(X0,k2_pre_topc(X0,X1)),X0)
% 8.01/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 8.01/1.49      | ~ l1_pre_topc(X0)
% 8.01/1.49      | sK0 != X0 ),
% 8.01/1.49      inference(resolution_lifted,[status(thm)],[c_294,c_25]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_308,plain,
% 8.01/1.49      ( v3_tops_1(k2_tops_1(sK0,k2_pre_topc(sK0,X0)),sK0)
% 8.01/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 8.01/1.49      | ~ l1_pre_topc(sK0) ),
% 8.01/1.49      inference(unflattening,[status(thm)],[c_307]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_312,plain,
% 8.01/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 8.01/1.49      | v3_tops_1(k2_tops_1(sK0,k2_pre_topc(sK0,X0)),sK0) ),
% 8.01/1.49      inference(global_propositional_subsumption,
% 8.01/1.49                [status(thm)],
% 8.01/1.49                [c_308,c_24]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_313,plain,
% 8.01/1.49      ( v3_tops_1(k2_tops_1(sK0,k2_pre_topc(sK0,X0)),sK0)
% 8.01/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 8.01/1.49      inference(renaming,[status(thm)],[c_312]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_329,plain,
% 8.01/1.49      ( v2_tops_1(k2_pre_topc(X0,X1),X0)
% 8.01/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 8.01/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
% 8.01/1.49      | ~ l1_pre_topc(X0)
% 8.01/1.49      | k2_tops_1(sK0,k2_pre_topc(sK0,X2)) != X1
% 8.01/1.49      | sK0 != X0 ),
% 8.01/1.49      inference(resolution_lifted,[status(thm)],[c_8,c_313]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_330,plain,
% 8.01/1.49      ( v2_tops_1(k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,X0))),sK0)
% 8.01/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 8.01/1.49      | ~ m1_subset_1(k2_tops_1(sK0,k2_pre_topc(sK0,X0)),k1_zfmisc_1(u1_struct_0(sK0)))
% 8.01/1.49      | ~ l1_pre_topc(sK0) ),
% 8.01/1.49      inference(unflattening,[status(thm)],[c_329]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_334,plain,
% 8.01/1.49      ( ~ m1_subset_1(k2_tops_1(sK0,k2_pre_topc(sK0,X0)),k1_zfmisc_1(u1_struct_0(sK0)))
% 8.01/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 8.01/1.49      | v2_tops_1(k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,X0))),sK0) ),
% 8.01/1.49      inference(global_propositional_subsumption,
% 8.01/1.49                [status(thm)],
% 8.01/1.49                [c_330,c_24]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_335,plain,
% 8.01/1.49      ( v2_tops_1(k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,X0))),sK0)
% 8.01/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 8.01/1.49      | ~ m1_subset_1(k2_tops_1(sK0,k2_pre_topc(sK0,X0)),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 8.01/1.49      inference(renaming,[status(thm)],[c_334]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_355,plain,
% 8.01/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 8.01/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
% 8.01/1.49      | ~ m1_subset_1(k2_tops_1(sK0,k2_pre_topc(sK0,X2)),k1_zfmisc_1(u1_struct_0(sK0)))
% 8.01/1.49      | ~ l1_pre_topc(X1)
% 8.01/1.49      | k1_tops_1(X1,X0) = k1_xboole_0
% 8.01/1.49      | k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,X2))) != X0
% 8.01/1.49      | sK0 != X1 ),
% 8.01/1.49      inference(resolution_lifted,[status(thm)],[c_19,c_335]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_356,plain,
% 8.01/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 8.01/1.49      | ~ m1_subset_1(k2_tops_1(sK0,k2_pre_topc(sK0,X0)),k1_zfmisc_1(u1_struct_0(sK0)))
% 8.01/1.49      | ~ m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,X0))),k1_zfmisc_1(u1_struct_0(sK0)))
% 8.01/1.49      | ~ l1_pre_topc(sK0)
% 8.01/1.49      | k1_tops_1(sK0,k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,X0)))) = k1_xboole_0 ),
% 8.01/1.49      inference(unflattening,[status(thm)],[c_355]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_360,plain,
% 8.01/1.49      ( ~ m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,X0))),k1_zfmisc_1(u1_struct_0(sK0)))
% 8.01/1.49      | ~ m1_subset_1(k2_tops_1(sK0,k2_pre_topc(sK0,X0)),k1_zfmisc_1(u1_struct_0(sK0)))
% 8.01/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 8.01/1.49      | k1_tops_1(sK0,k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,X0)))) = k1_xboole_0 ),
% 8.01/1.49      inference(global_propositional_subsumption,
% 8.01/1.49                [status(thm)],
% 8.01/1.49                [c_356,c_24]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_361,plain,
% 8.01/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 8.01/1.49      | ~ m1_subset_1(k2_tops_1(sK0,k2_pre_topc(sK0,X0)),k1_zfmisc_1(u1_struct_0(sK0)))
% 8.01/1.49      | ~ m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,X0))),k1_zfmisc_1(u1_struct_0(sK0)))
% 8.01/1.49      | k1_tops_1(sK0,k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,X0)))) = k1_xboole_0 ),
% 8.01/1.49      inference(renaming,[status(thm)],[c_360]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_539,plain,
% 8.01/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 8.01/1.49      | ~ m1_subset_1(k2_tops_1(sK0,k2_pre_topc(sK0,X0)),k1_zfmisc_1(u1_struct_0(sK0)))
% 8.01/1.49      | k1_tops_1(sK0,k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,X0)))) = k1_xboole_0 ),
% 8.01/1.49      inference(backward_subsumption_resolution,
% 8.01/1.49                [status(thm)],
% 8.01/1.49                [c_503,c_361]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_918,plain,
% 8.01/1.49      ( k1_tops_1(sK0,k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,X0)))) = k1_xboole_0
% 8.01/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.01/1.49      | m1_subset_1(k2_tops_1(sK0,k2_pre_topc(sK0,X0)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 8.01/1.49      inference(predicate_to_equality,[status(thm)],[c_539]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_1695,plain,
% 8.01/1.49      ( k1_tops_1(sK0,k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,k2_pre_topc(sK0,sK1))))) = k1_xboole_0
% 8.01/1.49      | m1_subset_1(k2_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.01/1.49      | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 8.01/1.49      inference(superposition,[status(thm)],[c_1290,c_918]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_1697,plain,
% 8.01/1.49      ( k1_tops_1(sK0,k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1)))) = k1_xboole_0
% 8.01/1.49      | m1_subset_1(k2_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.01/1.49      | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 8.01/1.49      inference(light_normalisation,[status(thm)],[c_1695,c_1290]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_1004,plain,
% 8.01/1.49      ( ~ m1_subset_1(k2_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
% 8.01/1.49      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 8.01/1.49      | k1_tops_1(sK0,k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1)))) = k1_xboole_0 ),
% 8.01/1.49      inference(instantiation,[status(thm)],[c_539]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_1089,plain,
% 8.01/1.49      ( m1_subset_1(k2_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
% 8.01/1.49      | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 8.01/1.49      inference(instantiation,[status(thm)],[c_455]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_3317,plain,
% 8.01/1.49      ( k1_tops_1(sK0,k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1)))) = k1_xboole_0 ),
% 8.01/1.49      inference(global_propositional_subsumption,
% 8.01/1.49                [status(thm)],
% 8.01/1.49                [c_1697,c_23,c_977,c_1004,c_1089]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_3344,plain,
% 8.01/1.49      ( k1_tops_1(sK0,k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1)))) = k1_tops_1(sK0,X0)
% 8.01/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.01/1.49      | m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.01/1.49      | r1_tarski(k1_tops_1(sK0,X0),k1_xboole_0) != iProver_top
% 8.01/1.49      | r1_tarski(k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))),X0) != iProver_top ),
% 8.01/1.49      inference(superposition,[status(thm)],[c_3317,c_2086]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_3345,plain,
% 8.01/1.49      ( k1_tops_1(sK0,X0) = k1_xboole_0
% 8.01/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.01/1.49      | m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.01/1.49      | r1_tarski(k1_tops_1(sK0,X0),k1_xboole_0) != iProver_top
% 8.01/1.49      | r1_tarski(k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))),X0) != iProver_top ),
% 8.01/1.49      inference(light_normalisation,[status(thm)],[c_3344,c_3317]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_3,plain,
% 8.01/1.49      ( r1_tarski(k1_xboole_0,X0) ),
% 8.01/1.49      inference(cnf_transformation,[],[f53]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_81,plain,
% 8.01/1.49      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 8.01/1.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_1090,plain,
% 8.01/1.49      ( m1_subset_1(k2_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 8.01/1.49      | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 8.01/1.49      inference(predicate_to_equality,[status(thm)],[c_1089]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_1449,plain,
% 8.01/1.49      ( ~ m1_subset_1(k2_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
% 8.01/1.49      | m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 8.01/1.49      inference(instantiation,[status(thm)],[c_503]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_1456,plain,
% 8.01/1.49      ( m1_subset_1(k2_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.01/1.49      | m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 8.01/1.49      inference(predicate_to_equality,[status(thm)],[c_1449]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_3322,plain,
% 8.01/1.49      ( m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.01/1.49      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 8.01/1.49      inference(superposition,[status(thm)],[c_3317,c_922]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_930,plain,
% 8.01/1.49      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 8.01/1.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_3323,plain,
% 8.01/1.49      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.01/1.49      | m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.01/1.49      | r1_tarski(X0,k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1)))) != iProver_top
% 8.01/1.49      | r1_tarski(k1_tops_1(sK0,X0),k1_xboole_0) = iProver_top ),
% 8.01/1.49      inference(superposition,[status(thm)],[c_3317,c_926]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_10157,plain,
% 8.01/1.49      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.01/1.49      | r1_tarski(X0,k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1)))) != iProver_top
% 8.01/1.49      | r1_tarski(k1_tops_1(sK0,X0),k1_xboole_0) = iProver_top ),
% 8.01/1.49      inference(global_propositional_subsumption,
% 8.01/1.49                [status(thm)],
% 8.01/1.49                [c_3323,c_28,c_978,c_1090,c_1456]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_10164,plain,
% 8.01/1.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.01/1.49      | r1_tarski(k1_tops_1(sK0,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 8.01/1.49      inference(superposition,[status(thm)],[c_930,c_10157]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_10170,plain,
% 8.01/1.49      ( r1_tarski(k1_tops_1(sK0,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 8.01/1.49      inference(global_propositional_subsumption,
% 8.01/1.49                [status(thm)],
% 8.01/1.49                [c_10164,c_28,c_978,c_1090,c_1456,c_3322]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_1487,plain,
% 8.01/1.49      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 8.01/1.49      inference(superposition,[status(thm)],[c_930,c_932]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_10175,plain,
% 8.01/1.49      ( k1_tops_1(sK0,k1_xboole_0) = k1_xboole_0 ),
% 8.01/1.49      inference(superposition,[status(thm)],[c_10170,c_1487]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_10224,plain,
% 8.01/1.49      ( k1_tops_1(sK0,X0) = k1_tops_1(sK0,k1_xboole_0)
% 8.01/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.01/1.49      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.01/1.49      | r1_tarski(k1_tops_1(sK0,X0),k1_xboole_0) != iProver_top
% 8.01/1.49      | r1_tarski(k1_xboole_0,X0) != iProver_top ),
% 8.01/1.49      inference(superposition,[status(thm)],[c_10175,c_2086]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_10226,plain,
% 8.01/1.49      ( k1_tops_1(sK0,X0) = k1_xboole_0
% 8.01/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.01/1.49      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.01/1.49      | r1_tarski(k1_tops_1(sK0,X0),k1_xboole_0) != iProver_top
% 8.01/1.49      | r1_tarski(k1_xboole_0,X0) != iProver_top ),
% 8.01/1.49      inference(light_normalisation,[status(thm)],[c_10224,c_10175]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_11997,plain,
% 8.01/1.49      ( r1_tarski(k1_tops_1(sK0,X0),k1_xboole_0) != iProver_top
% 8.01/1.49      | k1_tops_1(sK0,X0) = k1_xboole_0
% 8.01/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 8.01/1.49      inference(global_propositional_subsumption,
% 8.01/1.49                [status(thm)],
% 8.01/1.49                [c_3345,c_28,c_81,c_978,c_1090,c_1456,c_3322,c_10226]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_11998,plain,
% 8.01/1.49      ( k1_tops_1(sK0,X0) = k1_xboole_0
% 8.01/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.01/1.49      | r1_tarski(k1_tops_1(sK0,X0),k1_xboole_0) != iProver_top ),
% 8.01/1.49      inference(renaming,[status(thm)],[c_11997]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_12005,plain,
% 8.01/1.49      ( k1_tops_1(sK0,k1_tops_1(sK0,X0)) = k1_xboole_0
% 8.01/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.01/1.49      | r1_tarski(k1_tops_1(sK0,k1_tops_1(sK0,X0)),k1_xboole_0) != iProver_top ),
% 8.01/1.49      inference(superposition,[status(thm)],[c_922,c_11998]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_16942,plain,
% 8.01/1.49      ( k1_tops_1(sK0,k1_tops_1(sK0,k1_tops_1(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))))) = k1_xboole_0
% 8.01/1.49      | m1_subset_1(k1_tops_1(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.01/1.49      | r1_tarski(k1_tops_1(sK0,k1_tops_1(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1)))),k1_xboole_0) != iProver_top ),
% 8.01/1.49      inference(superposition,[status(thm)],[c_10075,c_12005]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_16969,plain,
% 8.01/1.49      ( k1_tops_1(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))) = k1_xboole_0
% 8.01/1.49      | m1_subset_1(k1_tops_1(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.01/1.49      | r1_tarski(k1_tops_1(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))),k1_xboole_0) != iProver_top ),
% 8.01/1.49      inference(light_normalisation,[status(thm)],[c_16942,c_10075]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_921,plain,
% 8.01/1.49      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.01/1.49      | r1_tarski(X0,k2_pre_topc(sK0,X0)) = iProver_top ),
% 8.01/1.49      inference(predicate_to_equality,[status(thm)],[c_479]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_1855,plain,
% 8.01/1.49      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.01/1.49      | r1_tarski(k2_tops_1(sK0,X0),k2_pre_topc(sK0,k2_tops_1(sK0,X0))) = iProver_top ),
% 8.01/1.49      inference(superposition,[status(thm)],[c_923,c_921]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_3342,plain,
% 8.01/1.49      ( k1_tops_1(sK0,k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1)))) = k1_tops_1(sK0,X0)
% 8.01/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.01/1.49      | m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.01/1.49      | r1_tarski(X0,k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1)))) != iProver_top
% 8.01/1.49      | r1_tarski(k1_xboole_0,k1_tops_1(sK0,X0)) != iProver_top ),
% 8.01/1.49      inference(superposition,[status(thm)],[c_3317,c_2086]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_3347,plain,
% 8.01/1.49      ( k1_tops_1(sK0,X0) = k1_xboole_0
% 8.01/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.01/1.49      | m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.01/1.49      | r1_tarski(X0,k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1)))) != iProver_top
% 8.01/1.49      | r1_tarski(k1_xboole_0,k1_tops_1(sK0,X0)) != iProver_top ),
% 8.01/1.49      inference(light_normalisation,[status(thm)],[c_3342,c_3317]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_14286,plain,
% 8.01/1.49      ( r1_tarski(X0,k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1)))) != iProver_top
% 8.01/1.49      | k1_tops_1(sK0,X0) = k1_xboole_0
% 8.01/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 8.01/1.49      inference(global_propositional_subsumption,
% 8.01/1.49                [status(thm)],
% 8.01/1.49                [c_3347,c_28,c_81,c_978,c_1090,c_1456,c_3322,c_10157,
% 8.01/1.49                 c_10226]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_14287,plain,
% 8.01/1.49      ( k1_tops_1(sK0,X0) = k1_xboole_0
% 8.01/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.01/1.49      | r1_tarski(X0,k2_pre_topc(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1)))) != iProver_top ),
% 8.01/1.49      inference(renaming,[status(thm)],[c_14286]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_14294,plain,
% 8.01/1.49      ( k1_tops_1(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))) = k1_xboole_0
% 8.01/1.49      | m1_subset_1(k2_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.01/1.49      | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 8.01/1.49      inference(superposition,[status(thm)],[c_1855,c_14287]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_17316,plain,
% 8.01/1.49      ( k1_tops_1(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))) = k1_xboole_0 ),
% 8.01/1.49      inference(global_propositional_subsumption,
% 8.01/1.49                [status(thm)],
% 8.01/1.49                [c_16969,c_28,c_978,c_1090,c_14294]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_28299,plain,
% 8.01/1.49      ( k1_tops_1(sK0,k2_tops_1(sK0,sK1)) = k1_xboole_0 ),
% 8.01/1.49      inference(demodulation,[status(thm)],[c_26859,c_17316]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_653,plain,( X0 = X0 ),theory(equality) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_1473,plain,
% 8.01/1.49      ( k1_xboole_0 = k1_xboole_0 ),
% 8.01/1.49      inference(instantiation,[status(thm)],[c_653]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_654,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_963,plain,
% 8.01/1.49      ( k1_tops_1(sK0,k2_tops_1(sK0,sK1)) != X0
% 8.01/1.49      | k1_xboole_0 != X0
% 8.01/1.49      | k1_xboole_0 = k1_tops_1(sK0,k2_tops_1(sK0,sK1)) ),
% 8.01/1.49      inference(instantiation,[status(thm)],[c_654]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_1118,plain,
% 8.01/1.49      ( k1_tops_1(sK0,k2_tops_1(sK0,sK1)) != k1_xboole_0
% 8.01/1.49      | k1_xboole_0 = k1_tops_1(sK0,k2_tops_1(sK0,sK1))
% 8.01/1.49      | k1_xboole_0 != k1_xboole_0 ),
% 8.01/1.49      inference(instantiation,[status(thm)],[c_963]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(c_21,negated_conjecture,
% 8.01/1.49      ( k1_xboole_0 != k1_tops_1(sK0,k2_tops_1(sK0,sK1)) ),
% 8.01/1.49      inference(cnf_transformation,[],[f75]) ).
% 8.01/1.49  
% 8.01/1.49  cnf(contradiction,plain,
% 8.01/1.49      ( $false ),
% 8.01/1.49      inference(minisat,[status(thm)],[c_28299,c_1473,c_1118,c_21]) ).
% 8.01/1.49  
% 8.01/1.49  
% 8.01/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 8.01/1.49  
% 8.01/1.49  ------                               Statistics
% 8.01/1.49  
% 8.01/1.49  ------ General
% 8.01/1.49  
% 8.01/1.49  abstr_ref_over_cycles:                  0
% 8.01/1.49  abstr_ref_under_cycles:                 0
% 8.01/1.49  gc_basic_clause_elim:                   0
% 8.01/1.49  forced_gc_time:                         0
% 8.01/1.49  parsing_time:                           0.012
% 8.01/1.49  unif_index_cands_time:                  0.
% 8.01/1.49  unif_index_add_time:                    0.
% 8.01/1.49  orderings_time:                         0.
% 8.01/1.49  out_proof_time:                         0.017
% 8.01/1.49  total_time:                             0.903
% 8.01/1.49  num_of_symbols:                         48
% 8.01/1.49  num_of_terms:                           43092
% 8.01/1.49  
% 8.01/1.49  ------ Preprocessing
% 8.01/1.49  
% 8.01/1.49  num_of_splits:                          0
% 8.01/1.49  num_of_split_atoms:                     0
% 8.01/1.49  num_of_reused_defs:                     0
% 8.01/1.49  num_eq_ax_congr_red:                    4
% 8.01/1.49  num_of_sem_filtered_clauses:            1
% 8.01/1.49  num_of_subtypes:                        0
% 8.01/1.49  monotx_restored_types:                  0
% 8.01/1.49  sat_num_of_epr_types:                   0
% 8.01/1.49  sat_num_of_non_cyclic_types:            0
% 8.01/1.49  sat_guarded_non_collapsed_types:        0
% 8.01/1.49  num_pure_diseq_elim:                    0
% 8.01/1.49  simp_replaced_by:                       0
% 8.01/1.49  res_preprocessed:                       94
% 8.01/1.49  prep_upred:                             0
% 8.01/1.49  prep_unflattend:                        19
% 8.01/1.49  smt_new_axioms:                         0
% 8.01/1.49  pred_elim_cands:                        2
% 8.01/1.49  pred_elim:                              6
% 8.01/1.49  pred_elim_cl:                           9
% 8.01/1.49  pred_elim_cycles:                       8
% 8.01/1.49  merged_defs:                            0
% 8.01/1.49  merged_defs_ncl:                        0
% 8.01/1.49  bin_hyper_res:                          0
% 8.01/1.49  prep_cycles:                            4
% 8.01/1.49  pred_elim_time:                         0.007
% 8.01/1.49  splitting_time:                         0.
% 8.01/1.49  sem_filter_time:                        0.
% 8.01/1.49  monotx_time:                            0.
% 8.01/1.49  subtype_inf_time:                       0.
% 8.01/1.49  
% 8.01/1.49  ------ Problem properties
% 8.01/1.49  
% 8.01/1.49  clauses:                                16
% 8.01/1.49  conjectures:                            2
% 8.01/1.49  epr:                                    3
% 8.01/1.49  horn:                                   16
% 8.01/1.49  ground:                                 4
% 8.01/1.49  unary:                                  6
% 8.01/1.49  binary:                                 7
% 8.01/1.49  lits:                                   30
% 8.01/1.49  lits_eq:                                6
% 8.01/1.49  fd_pure:                                0
% 8.01/1.49  fd_pseudo:                              0
% 8.01/1.49  fd_cond:                                0
% 8.01/1.49  fd_pseudo_cond:                         1
% 8.01/1.49  ac_symbols:                             0
% 8.01/1.49  
% 8.01/1.49  ------ Propositional Solver
% 8.01/1.49  
% 8.01/1.49  prop_solver_calls:                      32
% 8.01/1.49  prop_fast_solver_calls:                 1313
% 8.01/1.49  smt_solver_calls:                       0
% 8.01/1.49  smt_fast_solver_calls:                  0
% 8.01/1.49  prop_num_of_clauses:                    10831
% 8.01/1.49  prop_preprocess_simplified:             17110
% 8.01/1.49  prop_fo_subsumed:                       81
% 8.01/1.49  prop_solver_time:                       0.
% 8.01/1.49  smt_solver_time:                        0.
% 8.01/1.49  smt_fast_solver_time:                   0.
% 8.01/1.49  prop_fast_solver_time:                  0.
% 8.01/1.49  prop_unsat_core_time:                   0.001
% 8.01/1.49  
% 8.01/1.49  ------ QBF
% 8.01/1.49  
% 8.01/1.49  qbf_q_res:                              0
% 8.01/1.49  qbf_num_tautologies:                    0
% 8.01/1.49  qbf_prep_cycles:                        0
% 8.01/1.49  
% 8.01/1.49  ------ BMC1
% 8.01/1.49  
% 8.01/1.49  bmc1_current_bound:                     -1
% 8.01/1.49  bmc1_last_solved_bound:                 -1
% 8.01/1.49  bmc1_unsat_core_size:                   -1
% 8.01/1.49  bmc1_unsat_core_parents_size:           -1
% 8.01/1.49  bmc1_merge_next_fun:                    0
% 8.01/1.49  bmc1_unsat_core_clauses_time:           0.
% 8.01/1.49  
% 8.01/1.49  ------ Instantiation
% 8.01/1.49  
% 8.01/1.49  inst_num_of_clauses:                    2908
% 8.01/1.49  inst_num_in_passive:                    1319
% 8.01/1.49  inst_num_in_active:                     1318
% 8.01/1.49  inst_num_in_unprocessed:                271
% 8.01/1.49  inst_num_of_loops:                      1430
% 8.01/1.49  inst_num_of_learning_restarts:          0
% 8.01/1.49  inst_num_moves_active_passive:          110
% 8.01/1.49  inst_lit_activity:                      0
% 8.01/1.49  inst_lit_activity_moves:                1
% 8.01/1.49  inst_num_tautologies:                   0
% 8.01/1.49  inst_num_prop_implied:                  0
% 8.01/1.49  inst_num_existing_simplified:           0
% 8.01/1.49  inst_num_eq_res_simplified:             0
% 8.01/1.49  inst_num_child_elim:                    0
% 8.01/1.49  inst_num_of_dismatching_blockings:      7168
% 8.01/1.49  inst_num_of_non_proper_insts:           2210
% 8.01/1.49  inst_num_of_duplicates:                 0
% 8.01/1.49  inst_inst_num_from_inst_to_res:         0
% 8.01/1.49  inst_dismatching_checking_time:         0.
% 8.01/1.49  
% 8.01/1.49  ------ Resolution
% 8.01/1.49  
% 8.01/1.49  res_num_of_clauses:                     0
% 8.01/1.49  res_num_in_passive:                     0
% 8.01/1.49  res_num_in_active:                      0
% 8.01/1.49  res_num_of_loops:                       98
% 8.01/1.49  res_forward_subset_subsumed:            285
% 8.01/1.49  res_backward_subset_subsumed:           0
% 8.01/1.49  res_forward_subsumed:                   0
% 8.01/1.49  res_backward_subsumed:                  0
% 8.01/1.49  res_forward_subsumption_resolution:     1
% 8.01/1.49  res_backward_subsumption_resolution:    1
% 8.01/1.49  res_clause_to_clause_subsumption:       6265
% 8.01/1.49  res_orphan_elimination:                 0
% 8.01/1.49  res_tautology_del:                      132
% 8.01/1.49  res_num_eq_res_simplified:              0
% 8.01/1.49  res_num_sel_changes:                    0
% 8.01/1.49  res_moves_from_active_to_pass:          0
% 8.01/1.49  
% 8.01/1.49  ------ Superposition
% 8.01/1.49  
% 8.01/1.49  sup_time_total:                         0.
% 8.01/1.49  sup_time_generating:                    0.
% 8.01/1.49  sup_time_sim_full:                      0.
% 8.01/1.49  sup_time_sim_immed:                     0.
% 8.01/1.49  
% 8.01/1.49  sup_num_of_clauses:                     945
% 8.01/1.49  sup_num_in_active:                      236
% 8.01/1.49  sup_num_in_passive:                     709
% 8.01/1.49  sup_num_of_loops:                       284
% 8.01/1.49  sup_fw_superposition:                   934
% 8.01/1.49  sup_bw_superposition:                   1136
% 8.01/1.49  sup_immediate_simplified:               1042
% 8.01/1.49  sup_given_eliminated:                   1
% 8.01/1.49  comparisons_done:                       0
% 8.01/1.49  comparisons_avoided:                    0
% 8.01/1.49  
% 8.01/1.49  ------ Simplifications
% 8.01/1.49  
% 8.01/1.49  
% 8.01/1.49  sim_fw_subset_subsumed:                 127
% 8.01/1.49  sim_bw_subset_subsumed:                 76
% 8.01/1.49  sim_fw_subsumed:                        445
% 8.01/1.49  sim_bw_subsumed:                        1
% 8.01/1.49  sim_fw_subsumption_res:                 0
% 8.01/1.49  sim_bw_subsumption_res:                 0
% 8.01/1.49  sim_tautology_del:                      90
% 8.01/1.49  sim_eq_tautology_del:                   175
% 8.01/1.49  sim_eq_res_simp:                        0
% 8.01/1.49  sim_fw_demodulated:                     61
% 8.01/1.49  sim_bw_demodulated:                     45
% 8.01/1.49  sim_light_normalised:                   608
% 8.01/1.49  sim_joinable_taut:                      0
% 8.01/1.49  sim_joinable_simp:                      0
% 8.01/1.49  sim_ac_normalised:                      0
% 8.01/1.49  sim_smt_subsumption:                    0
% 8.01/1.49  
%------------------------------------------------------------------------------
