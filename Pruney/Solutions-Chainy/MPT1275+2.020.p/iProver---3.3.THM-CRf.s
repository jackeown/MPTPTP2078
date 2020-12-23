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
% DateTime   : Thu Dec  3 12:15:26 EST 2020

% Result     : Theorem 3.60s
% Output     : CNFRefutation 3.60s
% Verified   : 
% Statistics : Number of formulae       :  164 ( 687 expanded)
%              Number of clauses        :   95 ( 203 expanded)
%              Number of leaves         :   19 ( 142 expanded)
%              Depth                    :   18
%              Number of atoms          :  464 (3206 expanded)
%              Number of equality atoms :  165 ( 882 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f37])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f78,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f48])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f59,f52])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X0))
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f18,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => ( v3_tops_1(X1,X0)
            <=> k2_tops_1(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
             => ( v3_tops_1(X1,X0)
              <=> k2_tops_1(X0,X1) = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tops_1(X1,X0)
          <~> k2_tops_1(X0,X1) = X1 )
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tops_1(X1,X0)
          <~> k2_tops_1(X0,X1) = X1 )
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f43,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != X1
            | ~ v3_tops_1(X1,X0) )
          & ( k2_tops_1(X0,X1) = X1
            | v3_tops_1(X1,X0) )
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f44,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != X1
            | ~ v3_tops_1(X1,X0) )
          & ( k2_tops_1(X0,X1) = X1
            | v3_tops_1(X1,X0) )
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f43])).

fof(f46,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != X1
            | ~ v3_tops_1(X1,X0) )
          & ( k2_tops_1(X0,X1) = X1
            | v3_tops_1(X1,X0) )
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( k2_tops_1(X0,sK1) != sK1
          | ~ v3_tops_1(sK1,X0) )
        & ( k2_tops_1(X0,sK1) = sK1
          | v3_tops_1(sK1,X0) )
        & v4_pre_topc(sK1,X0)
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k2_tops_1(X0,X1) != X1
              | ~ v3_tops_1(X1,X0) )
            & ( k2_tops_1(X0,X1) = X1
              | v3_tops_1(X1,X0) )
            & v4_pre_topc(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k2_tops_1(sK0,X1) != X1
            | ~ v3_tops_1(X1,sK0) )
          & ( k2_tops_1(sK0,X1) = X1
            | v3_tops_1(X1,sK0) )
          & v4_pre_topc(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ( k2_tops_1(sK0,sK1) != sK1
      | ~ v3_tops_1(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = sK1
      | v3_tops_1(sK1,sK0) )
    & v4_pre_topc(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f44,f46,f45])).

fof(f72,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f47])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f71,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => k2_pre_topc(X0,X1) = X1 ) ) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = X1
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = X1
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f73,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | k1_xboole_0 != k1_tops_1(X0,X1) )
            & ( k1_xboole_0 = k1_tops_1(X0,X1)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_tops_1(X0,X1)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> r1_tarski(X1,k2_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> r1_tarski(X1,k2_tops_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | ~ r1_tarski(X1,k2_tops_1(X0,X1)) )
            & ( r1_tarski(X1,k2_tops_1(X0,X1))
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f69,plain,(
    ! [X0,X1] :
      ( v2_tops_1(X1,X0)
      | ~ r1_tarski(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f74,plain,
    ( k2_tops_1(sK0,sK1) = sK1
    | v3_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tops_1(X1,X0)
           => v2_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tops_1(X1,X0)
          | ~ v3_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tops_1(X1,X0)
          | ~ v3_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f70,plain,(
    ! [X0,X1] :
      ( v2_tops_1(X1,X0)
      | ~ v3_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f75,plain,
    ( k2_tops_1(sK0,sK1) != sK1
    | ~ v3_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tops_1(X1,X0)
          <=> v2_tops_1(k2_pre_topc(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tops_1(X1,X0)
          <=> v2_tops_1(k2_pre_topc(X0,X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tops_1(X1,X0)
              | ~ v2_tops_1(k2_pre_topc(X0,X1),X0) )
            & ( v2_tops_1(k2_pre_topc(X0,X1),X0)
              | ~ v3_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v3_tops_1(X1,X0)
      | ~ v2_tops_1(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f67,plain,(
    ! [X0,X1] :
      ( v2_tops_1(X1,X0)
      | k1_xboole_0 != k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_2205,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X2) = X2 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_11,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_209,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_11])).

cnf(c_210,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_209])).

cnf(c_258,plain,
    ( ~ r1_tarski(X0,X1)
    | k9_subset_1(X1,X2,X2) = X2 ),
    inference(bin_hyper_res,[status(thm)],[c_8,c_210])).

cnf(c_2197,plain,
    ( k9_subset_1(X0,X1,X1) = X1
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_258])).

cnf(c_3769,plain,
    ( k9_subset_1(X0,X1,X1) = X1 ),
    inference(superposition,[status(thm)],[c_2205,c_2197])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k4_xboole_0(X2,k4_xboole_0(X2,X0)) = k9_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_260,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X2,k4_xboole_0(X2,X0)) = k9_subset_1(X1,X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_10,c_210])).

cnf(c_2195,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k9_subset_1(X2,X0,X1)
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_260])).

cnf(c_4959,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k9_subset_1(X1,X0,X1) ),
    inference(superposition,[status(thm)],[c_2205,c_2195])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,k4_xboole_0(X1,X0))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2204,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k4_xboole_0(X1,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_6058,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(k4_xboole_0(X0,X1),k9_subset_1(X1,X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4959,c_2204])).

cnf(c_6066,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0
    | r1_tarski(k4_xboole_0(X0,X0),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3769,c_6058])).

cnf(c_87,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_256,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_5,c_210])).

cnf(c_2199,plain,
    ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_256])).

cnf(c_3918,plain,
    ( k3_subset_1(X0,X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_2205,c_2199])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_257,plain,
    ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
    | ~ r1_tarski(X1,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_7,c_210])).

cnf(c_2198,plain,
    ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) = iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_257])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2201,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4658,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k3_subset_1(X1,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2198,c_2201])).

cnf(c_4888,plain,
    ( r1_tarski(X0,X0) != iProver_top
    | r1_tarski(k4_xboole_0(X0,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3918,c_4658])).

cnf(c_9109,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6066,c_87,c_4888])).

cnf(c_9187,plain,
    ( k9_subset_1(X0,X0,X0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_9109,c_4959])).

cnf(c_9189,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(demodulation,[status(thm)],[c_9187,c_3769])).

cnf(c_9191,plain,
    ( k4_xboole_0(sK1,k1_xboole_0) = sK1 ),
    inference(instantiation,[status(thm)],[c_9189])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2200,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2944,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2200,c_2201])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_259,plain,
    ( ~ r1_tarski(X0,X1)
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_9,c_210])).

cnf(c_2196,plain,
    ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_259])).

cnf(c_4402,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
    inference(superposition,[status(thm)],[c_2944,c_2196])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_26,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_478,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_26])).

cnf(c_479,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_478])).

cnf(c_2190,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_479])).

cnf(c_2412,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_2200,c_2190])).

cnf(c_13,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_24,negated_conjecture,
    ( v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_364,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0
    | sK1 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_24])).

cnf(c_365,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(unflattening,[status(thm)],[c_364])).

cnf(c_367,plain,
    ( k2_pre_topc(sK0,sK1) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_365,c_26,c_25])).

cnf(c_18,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_448,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,X0) = k1_xboole_0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_26])).

cnf(c_449,plain,
    ( ~ v2_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_448])).

cnf(c_2192,plain,
    ( k1_tops_1(sK0,X0) = k1_xboole_0
    | v2_tops_1(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_449])).

cnf(c_2395,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0
    | v2_tops_1(sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2200,c_2192])).

cnf(c_88,plain,
    ( r1_tarski(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_19,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,k2_tops_1(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_433,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,k2_tops_1(X1,X0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_26])).

cnf(c_434,plain,
    ( v2_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,k2_tops_1(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_433])).

cnf(c_436,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(sK1,k2_tops_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_434])).

cnf(c_451,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,sK1) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_449])).

cnf(c_23,negated_conjecture,
    ( v3_tops_1(sK1,sK0)
    | k2_tops_1(sK0,sK1) = sK1 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_213,plain,
    ( v3_tops_1(sK1,sK0)
    | k2_tops_1(sK0,sK1) = sK1 ),
    inference(prop_impl,[status(thm)],[c_23])).

cnf(c_21,plain,
    ( v2_tops_1(X0,X1)
    | ~ v3_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_403,plain,
    ( v2_tops_1(X0,X1)
    | ~ v3_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_26])).

cnf(c_404,plain,
    ( v2_tops_1(X0,sK0)
    | ~ v3_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_403])).

cnf(c_537,plain,
    ( v2_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_tops_1(sK0,sK1) = sK1
    | sK1 != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_213,c_404])).

cnf(c_538,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_tops_1(sK0,sK1) = sK1 ),
    inference(unflattening,[status(thm)],[c_537])).

cnf(c_540,plain,
    ( v2_tops_1(sK1,sK0)
    | k2_tops_1(sK0,sK1) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_538,c_25])).

cnf(c_1678,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,X2)
    | X2 != X1 ),
    theory(equality)).

cnf(c_2379,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k2_tops_1(sK0,X0))
    | k2_tops_1(sK0,X0) != X1 ),
    inference(instantiation,[status(thm)],[c_1678])).

cnf(c_2381,plain,
    ( r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | ~ r1_tarski(sK1,sK1)
    | k2_tops_1(sK0,sK1) != sK1 ),
    inference(instantiation,[status(thm)],[c_2379])).

cnf(c_2398,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2395,c_25,c_88,c_436,c_451,c_540,c_2381])).

cnf(c_2413,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) = k2_tops_1(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_2412,c_367,c_2398])).

cnf(c_4496,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_4402,c_2413])).

cnf(c_22,negated_conjecture,
    ( ~ v3_tops_1(sK1,sK0)
    | k2_tops_1(sK0,sK1) != sK1 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_211,plain,
    ( ~ v3_tops_1(sK1,sK0)
    | k2_tops_1(sK0,sK1) != sK1 ),
    inference(prop_impl,[status(thm)],[c_22])).

cnf(c_14,plain,
    ( ~ v2_tops_1(k2_pre_topc(X0,X1),X0)
    | v3_tops_1(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_388,plain,
    ( ~ v2_tops_1(k2_pre_topc(X0,X1),X0)
    | v3_tops_1(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_26])).

cnf(c_389,plain,
    ( ~ v2_tops_1(k2_pre_topc(sK0,X0),sK0)
    | v3_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_388])).

cnf(c_565,plain,
    ( ~ v2_tops_1(k2_pre_topc(sK0,X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_tops_1(sK0,sK1) != sK1
    | sK1 != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_211,c_389])).

cnf(c_566,plain,
    ( ~ v2_tops_1(k2_pre_topc(sK0,sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_tops_1(sK0,sK1) != sK1 ),
    inference(unflattening,[status(thm)],[c_565])).

cnf(c_568,plain,
    ( ~ v2_tops_1(k2_pre_topc(sK0,sK1),sK0)
    | k2_tops_1(sK0,sK1) != sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_566,c_25])).

cnf(c_1139,plain,
    ( ~ v2_tops_1(k2_pre_topc(sK0,sK1),sK0)
    | k2_tops_1(sK0,sK1) != sK1 ),
    inference(prop_impl,[status(thm)],[c_25,c_566])).

cnf(c_2187,plain,
    ( k2_tops_1(sK0,sK1) != sK1
    | v2_tops_1(k2_pre_topc(sK0,sK1),sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1139])).

cnf(c_2244,plain,
    ( k2_tops_1(sK0,sK1) != sK1
    | v2_tops_1(sK1,sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2187,c_367])).

cnf(c_5203,plain,
    ( k4_xboole_0(sK1,k1_xboole_0) != sK1
    | v2_tops_1(sK1,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4496,c_2244])).

cnf(c_17,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_463,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,X0) != k1_xboole_0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_26])).

cnf(c_464,plain,
    ( v2_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_463])).

cnf(c_939,plain,
    ( v2_tops_1(X0,sK0)
    | k1_tops_1(sK0,X0) != k1_xboole_0
    | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(u1_struct_0(sK0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_464])).

cnf(c_940,plain,
    ( v2_tops_1(sK1,sK0)
    | k1_tops_1(sK0,sK1) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_939])).

cnf(c_941,plain,
    ( k1_tops_1(sK0,sK1) != k1_xboole_0
    | v2_tops_1(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_940])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9191,c_5203,c_2398,c_941])).

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
% 0.13/0.34  % DateTime   : Tue Dec  1 14:33:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.60/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.60/1.02  
% 3.60/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.60/1.02  
% 3.60/1.02  ------  iProver source info
% 3.60/1.02  
% 3.60/1.02  git: date: 2020-06-30 10:37:57 +0100
% 3.60/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.60/1.02  git: non_committed_changes: false
% 3.60/1.02  git: last_make_outside_of_git: false
% 3.60/1.02  
% 3.60/1.02  ------ 
% 3.60/1.02  
% 3.60/1.02  ------ Input Options
% 3.60/1.02  
% 3.60/1.02  --out_options                           all
% 3.60/1.02  --tptp_safe_out                         true
% 3.60/1.02  --problem_path                          ""
% 3.60/1.02  --include_path                          ""
% 3.60/1.02  --clausifier                            res/vclausify_rel
% 3.60/1.02  --clausifier_options                    --mode clausify
% 3.60/1.02  --stdin                                 false
% 3.60/1.02  --stats_out                             all
% 3.60/1.02  
% 3.60/1.02  ------ General Options
% 3.60/1.02  
% 3.60/1.02  --fof                                   false
% 3.60/1.02  --time_out_real                         305.
% 3.60/1.02  --time_out_virtual                      -1.
% 3.60/1.02  --symbol_type_check                     false
% 3.60/1.02  --clausify_out                          false
% 3.60/1.02  --sig_cnt_out                           false
% 3.60/1.02  --trig_cnt_out                          false
% 3.60/1.02  --trig_cnt_out_tolerance                1.
% 3.60/1.02  --trig_cnt_out_sk_spl                   false
% 3.60/1.02  --abstr_cl_out                          false
% 3.60/1.02  
% 3.60/1.02  ------ Global Options
% 3.60/1.02  
% 3.60/1.02  --schedule                              default
% 3.60/1.02  --add_important_lit                     false
% 3.60/1.02  --prop_solver_per_cl                    1000
% 3.60/1.02  --min_unsat_core                        false
% 3.60/1.02  --soft_assumptions                      false
% 3.60/1.02  --soft_lemma_size                       3
% 3.60/1.02  --prop_impl_unit_size                   0
% 3.60/1.02  --prop_impl_unit                        []
% 3.60/1.02  --share_sel_clauses                     true
% 3.60/1.02  --reset_solvers                         false
% 3.60/1.02  --bc_imp_inh                            [conj_cone]
% 3.60/1.02  --conj_cone_tolerance                   3.
% 3.60/1.02  --extra_neg_conj                        none
% 3.60/1.02  --large_theory_mode                     true
% 3.60/1.02  --prolific_symb_bound                   200
% 3.60/1.02  --lt_threshold                          2000
% 3.60/1.02  --clause_weak_htbl                      true
% 3.60/1.02  --gc_record_bc_elim                     false
% 3.60/1.02  
% 3.60/1.02  ------ Preprocessing Options
% 3.60/1.02  
% 3.60/1.02  --preprocessing_flag                    true
% 3.60/1.02  --time_out_prep_mult                    0.1
% 3.60/1.02  --splitting_mode                        input
% 3.60/1.02  --splitting_grd                         true
% 3.60/1.02  --splitting_cvd                         false
% 3.60/1.02  --splitting_cvd_svl                     false
% 3.60/1.02  --splitting_nvd                         32
% 3.60/1.02  --sub_typing                            true
% 3.60/1.02  --prep_gs_sim                           true
% 3.60/1.02  --prep_unflatten                        true
% 3.60/1.02  --prep_res_sim                          true
% 3.60/1.02  --prep_upred                            true
% 3.60/1.02  --prep_sem_filter                       exhaustive
% 3.60/1.02  --prep_sem_filter_out                   false
% 3.60/1.02  --pred_elim                             true
% 3.60/1.02  --res_sim_input                         true
% 3.60/1.02  --eq_ax_congr_red                       true
% 3.60/1.02  --pure_diseq_elim                       true
% 3.60/1.02  --brand_transform                       false
% 3.60/1.02  --non_eq_to_eq                          false
% 3.60/1.02  --prep_def_merge                        true
% 3.60/1.02  --prep_def_merge_prop_impl              false
% 3.60/1.02  --prep_def_merge_mbd                    true
% 3.60/1.02  --prep_def_merge_tr_red                 false
% 3.60/1.02  --prep_def_merge_tr_cl                  false
% 3.60/1.02  --smt_preprocessing                     true
% 3.60/1.02  --smt_ac_axioms                         fast
% 3.60/1.02  --preprocessed_out                      false
% 3.60/1.02  --preprocessed_stats                    false
% 3.60/1.02  
% 3.60/1.02  ------ Abstraction refinement Options
% 3.60/1.02  
% 3.60/1.02  --abstr_ref                             []
% 3.60/1.02  --abstr_ref_prep                        false
% 3.60/1.02  --abstr_ref_until_sat                   false
% 3.60/1.02  --abstr_ref_sig_restrict                funpre
% 3.60/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.60/1.02  --abstr_ref_under                       []
% 3.60/1.02  
% 3.60/1.02  ------ SAT Options
% 3.60/1.02  
% 3.60/1.02  --sat_mode                              false
% 3.60/1.02  --sat_fm_restart_options                ""
% 3.60/1.02  --sat_gr_def                            false
% 3.60/1.02  --sat_epr_types                         true
% 3.60/1.02  --sat_non_cyclic_types                  false
% 3.60/1.02  --sat_finite_models                     false
% 3.60/1.02  --sat_fm_lemmas                         false
% 3.60/1.02  --sat_fm_prep                           false
% 3.60/1.02  --sat_fm_uc_incr                        true
% 3.60/1.02  --sat_out_model                         small
% 3.60/1.02  --sat_out_clauses                       false
% 3.60/1.02  
% 3.60/1.02  ------ QBF Options
% 3.60/1.02  
% 3.60/1.02  --qbf_mode                              false
% 3.60/1.02  --qbf_elim_univ                         false
% 3.60/1.02  --qbf_dom_inst                          none
% 3.60/1.02  --qbf_dom_pre_inst                      false
% 3.60/1.02  --qbf_sk_in                             false
% 3.60/1.02  --qbf_pred_elim                         true
% 3.60/1.02  --qbf_split                             512
% 3.60/1.02  
% 3.60/1.02  ------ BMC1 Options
% 3.60/1.02  
% 3.60/1.02  --bmc1_incremental                      false
% 3.60/1.02  --bmc1_axioms                           reachable_all
% 3.60/1.02  --bmc1_min_bound                        0
% 3.60/1.02  --bmc1_max_bound                        -1
% 3.60/1.02  --bmc1_max_bound_default                -1
% 3.60/1.02  --bmc1_symbol_reachability              true
% 3.60/1.02  --bmc1_property_lemmas                  false
% 3.60/1.02  --bmc1_k_induction                      false
% 3.60/1.02  --bmc1_non_equiv_states                 false
% 3.60/1.02  --bmc1_deadlock                         false
% 3.60/1.02  --bmc1_ucm                              false
% 3.60/1.02  --bmc1_add_unsat_core                   none
% 3.60/1.02  --bmc1_unsat_core_children              false
% 3.60/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.60/1.02  --bmc1_out_stat                         full
% 3.60/1.02  --bmc1_ground_init                      false
% 3.60/1.02  --bmc1_pre_inst_next_state              false
% 3.60/1.02  --bmc1_pre_inst_state                   false
% 3.60/1.02  --bmc1_pre_inst_reach_state             false
% 3.60/1.02  --bmc1_out_unsat_core                   false
% 3.60/1.02  --bmc1_aig_witness_out                  false
% 3.60/1.02  --bmc1_verbose                          false
% 3.60/1.02  --bmc1_dump_clauses_tptp                false
% 3.60/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.60/1.02  --bmc1_dump_file                        -
% 3.60/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.60/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.60/1.02  --bmc1_ucm_extend_mode                  1
% 3.60/1.02  --bmc1_ucm_init_mode                    2
% 3.60/1.02  --bmc1_ucm_cone_mode                    none
% 3.60/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.60/1.02  --bmc1_ucm_relax_model                  4
% 3.60/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.60/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.60/1.02  --bmc1_ucm_layered_model                none
% 3.60/1.02  --bmc1_ucm_max_lemma_size               10
% 3.60/1.02  
% 3.60/1.02  ------ AIG Options
% 3.60/1.02  
% 3.60/1.02  --aig_mode                              false
% 3.60/1.02  
% 3.60/1.02  ------ Instantiation Options
% 3.60/1.02  
% 3.60/1.02  --instantiation_flag                    true
% 3.60/1.02  --inst_sos_flag                         false
% 3.60/1.02  --inst_sos_phase                        true
% 3.60/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.60/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.60/1.02  --inst_lit_sel_side                     num_symb
% 3.60/1.02  --inst_solver_per_active                1400
% 3.60/1.02  --inst_solver_calls_frac                1.
% 3.60/1.02  --inst_passive_queue_type               priority_queues
% 3.60/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.60/1.02  --inst_passive_queues_freq              [25;2]
% 3.60/1.02  --inst_dismatching                      true
% 3.60/1.02  --inst_eager_unprocessed_to_passive     true
% 3.60/1.02  --inst_prop_sim_given                   true
% 3.60/1.02  --inst_prop_sim_new                     false
% 3.60/1.02  --inst_subs_new                         false
% 3.60/1.02  --inst_eq_res_simp                      false
% 3.60/1.02  --inst_subs_given                       false
% 3.60/1.02  --inst_orphan_elimination               true
% 3.60/1.02  --inst_learning_loop_flag               true
% 3.60/1.02  --inst_learning_start                   3000
% 3.60/1.02  --inst_learning_factor                  2
% 3.60/1.02  --inst_start_prop_sim_after_learn       3
% 3.60/1.02  --inst_sel_renew                        solver
% 3.60/1.02  --inst_lit_activity_flag                true
% 3.60/1.02  --inst_restr_to_given                   false
% 3.60/1.02  --inst_activity_threshold               500
% 3.60/1.02  --inst_out_proof                        true
% 3.60/1.02  
% 3.60/1.02  ------ Resolution Options
% 3.60/1.02  
% 3.60/1.02  --resolution_flag                       true
% 3.60/1.02  --res_lit_sel                           adaptive
% 3.60/1.02  --res_lit_sel_side                      none
% 3.60/1.02  --res_ordering                          kbo
% 3.60/1.02  --res_to_prop_solver                    active
% 3.60/1.02  --res_prop_simpl_new                    false
% 3.60/1.02  --res_prop_simpl_given                  true
% 3.60/1.02  --res_passive_queue_type                priority_queues
% 3.60/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.60/1.02  --res_passive_queues_freq               [15;5]
% 3.60/1.02  --res_forward_subs                      full
% 3.60/1.02  --res_backward_subs                     full
% 3.60/1.02  --res_forward_subs_resolution           true
% 3.60/1.02  --res_backward_subs_resolution          true
% 3.60/1.02  --res_orphan_elimination                true
% 3.60/1.02  --res_time_limit                        2.
% 3.60/1.02  --res_out_proof                         true
% 3.60/1.02  
% 3.60/1.02  ------ Superposition Options
% 3.60/1.02  
% 3.60/1.02  --superposition_flag                    true
% 3.60/1.02  --sup_passive_queue_type                priority_queues
% 3.60/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.60/1.02  --sup_passive_queues_freq               [8;1;4]
% 3.60/1.02  --demod_completeness_check              fast
% 3.60/1.02  --demod_use_ground                      true
% 3.60/1.02  --sup_to_prop_solver                    passive
% 3.60/1.02  --sup_prop_simpl_new                    true
% 3.60/1.02  --sup_prop_simpl_given                  true
% 3.60/1.02  --sup_fun_splitting                     false
% 3.60/1.02  --sup_smt_interval                      50000
% 3.60/1.02  
% 3.60/1.02  ------ Superposition Simplification Setup
% 3.60/1.02  
% 3.60/1.02  --sup_indices_passive                   []
% 3.60/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.60/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.60/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.60/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.60/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.60/1.02  --sup_full_bw                           [BwDemod]
% 3.60/1.02  --sup_immed_triv                        [TrivRules]
% 3.60/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.60/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.60/1.02  --sup_immed_bw_main                     []
% 3.60/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.60/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.60/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.60/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.60/1.02  
% 3.60/1.02  ------ Combination Options
% 3.60/1.02  
% 3.60/1.02  --comb_res_mult                         3
% 3.60/1.02  --comb_sup_mult                         2
% 3.60/1.02  --comb_inst_mult                        10
% 3.60/1.02  
% 3.60/1.02  ------ Debug Options
% 3.60/1.02  
% 3.60/1.02  --dbg_backtrace                         false
% 3.60/1.02  --dbg_dump_prop_clauses                 false
% 3.60/1.02  --dbg_dump_prop_clauses_file            -
% 3.60/1.02  --dbg_out_stat                          false
% 3.60/1.02  ------ Parsing...
% 3.60/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.60/1.02  
% 3.60/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.60/1.02  
% 3.60/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.60/1.02  
% 3.60/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.60/1.02  ------ Proving...
% 3.60/1.02  ------ Problem Properties 
% 3.60/1.02  
% 3.60/1.02  
% 3.60/1.02  clauses                                 23
% 3.60/1.02  conjectures                             1
% 3.60/1.02  EPR                                     2
% 3.60/1.02  Horn                                    22
% 3.60/1.02  unary                                   5
% 3.60/1.02  binary                                  12
% 3.60/1.02  lits                                    47
% 3.60/1.02  lits eq                                 13
% 3.60/1.02  fd_pure                                 0
% 3.60/1.02  fd_pseudo                               0
% 3.60/1.02  fd_cond                                 1
% 3.60/1.02  fd_pseudo_cond                          1
% 3.60/1.02  AC symbols                              0
% 3.60/1.02  
% 3.60/1.02  ------ Schedule dynamic 5 is on 
% 3.60/1.02  
% 3.60/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.60/1.02  
% 3.60/1.02  
% 3.60/1.02  ------ 
% 3.60/1.02  Current options:
% 3.60/1.02  ------ 
% 3.60/1.02  
% 3.60/1.02  ------ Input Options
% 3.60/1.02  
% 3.60/1.02  --out_options                           all
% 3.60/1.02  --tptp_safe_out                         true
% 3.60/1.02  --problem_path                          ""
% 3.60/1.02  --include_path                          ""
% 3.60/1.02  --clausifier                            res/vclausify_rel
% 3.60/1.02  --clausifier_options                    --mode clausify
% 3.60/1.02  --stdin                                 false
% 3.60/1.02  --stats_out                             all
% 3.60/1.02  
% 3.60/1.02  ------ General Options
% 3.60/1.02  
% 3.60/1.02  --fof                                   false
% 3.60/1.02  --time_out_real                         305.
% 3.60/1.02  --time_out_virtual                      -1.
% 3.60/1.02  --symbol_type_check                     false
% 3.60/1.02  --clausify_out                          false
% 3.60/1.02  --sig_cnt_out                           false
% 3.60/1.02  --trig_cnt_out                          false
% 3.60/1.02  --trig_cnt_out_tolerance                1.
% 3.60/1.02  --trig_cnt_out_sk_spl                   false
% 3.60/1.02  --abstr_cl_out                          false
% 3.60/1.02  
% 3.60/1.02  ------ Global Options
% 3.60/1.02  
% 3.60/1.02  --schedule                              default
% 3.60/1.02  --add_important_lit                     false
% 3.60/1.02  --prop_solver_per_cl                    1000
% 3.60/1.02  --min_unsat_core                        false
% 3.60/1.02  --soft_assumptions                      false
% 3.60/1.02  --soft_lemma_size                       3
% 3.60/1.02  --prop_impl_unit_size                   0
% 3.60/1.02  --prop_impl_unit                        []
% 3.60/1.02  --share_sel_clauses                     true
% 3.60/1.02  --reset_solvers                         false
% 3.60/1.02  --bc_imp_inh                            [conj_cone]
% 3.60/1.02  --conj_cone_tolerance                   3.
% 3.60/1.02  --extra_neg_conj                        none
% 3.60/1.02  --large_theory_mode                     true
% 3.60/1.02  --prolific_symb_bound                   200
% 3.60/1.02  --lt_threshold                          2000
% 3.60/1.02  --clause_weak_htbl                      true
% 3.60/1.02  --gc_record_bc_elim                     false
% 3.60/1.02  
% 3.60/1.02  ------ Preprocessing Options
% 3.60/1.02  
% 3.60/1.02  --preprocessing_flag                    true
% 3.60/1.02  --time_out_prep_mult                    0.1
% 3.60/1.02  --splitting_mode                        input
% 3.60/1.02  --splitting_grd                         true
% 3.60/1.02  --splitting_cvd                         false
% 3.60/1.02  --splitting_cvd_svl                     false
% 3.60/1.02  --splitting_nvd                         32
% 3.60/1.02  --sub_typing                            true
% 3.60/1.02  --prep_gs_sim                           true
% 3.60/1.02  --prep_unflatten                        true
% 3.60/1.02  --prep_res_sim                          true
% 3.60/1.02  --prep_upred                            true
% 3.60/1.02  --prep_sem_filter                       exhaustive
% 3.60/1.02  --prep_sem_filter_out                   false
% 3.60/1.02  --pred_elim                             true
% 3.60/1.02  --res_sim_input                         true
% 3.60/1.02  --eq_ax_congr_red                       true
% 3.60/1.02  --pure_diseq_elim                       true
% 3.60/1.02  --brand_transform                       false
% 3.60/1.02  --non_eq_to_eq                          false
% 3.60/1.02  --prep_def_merge                        true
% 3.60/1.02  --prep_def_merge_prop_impl              false
% 3.60/1.02  --prep_def_merge_mbd                    true
% 3.60/1.02  --prep_def_merge_tr_red                 false
% 3.60/1.02  --prep_def_merge_tr_cl                  false
% 3.60/1.02  --smt_preprocessing                     true
% 3.60/1.02  --smt_ac_axioms                         fast
% 3.60/1.02  --preprocessed_out                      false
% 3.60/1.02  --preprocessed_stats                    false
% 3.60/1.02  
% 3.60/1.02  ------ Abstraction refinement Options
% 3.60/1.02  
% 3.60/1.02  --abstr_ref                             []
% 3.60/1.02  --abstr_ref_prep                        false
% 3.60/1.02  --abstr_ref_until_sat                   false
% 3.60/1.02  --abstr_ref_sig_restrict                funpre
% 3.60/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.60/1.02  --abstr_ref_under                       []
% 3.60/1.02  
% 3.60/1.02  ------ SAT Options
% 3.60/1.02  
% 3.60/1.02  --sat_mode                              false
% 3.60/1.02  --sat_fm_restart_options                ""
% 3.60/1.02  --sat_gr_def                            false
% 3.60/1.02  --sat_epr_types                         true
% 3.60/1.02  --sat_non_cyclic_types                  false
% 3.60/1.02  --sat_finite_models                     false
% 3.60/1.02  --sat_fm_lemmas                         false
% 3.60/1.02  --sat_fm_prep                           false
% 3.60/1.02  --sat_fm_uc_incr                        true
% 3.60/1.02  --sat_out_model                         small
% 3.60/1.02  --sat_out_clauses                       false
% 3.60/1.02  
% 3.60/1.02  ------ QBF Options
% 3.60/1.02  
% 3.60/1.02  --qbf_mode                              false
% 3.60/1.02  --qbf_elim_univ                         false
% 3.60/1.02  --qbf_dom_inst                          none
% 3.60/1.02  --qbf_dom_pre_inst                      false
% 3.60/1.02  --qbf_sk_in                             false
% 3.60/1.02  --qbf_pred_elim                         true
% 3.60/1.02  --qbf_split                             512
% 3.60/1.02  
% 3.60/1.02  ------ BMC1 Options
% 3.60/1.02  
% 3.60/1.02  --bmc1_incremental                      false
% 3.60/1.02  --bmc1_axioms                           reachable_all
% 3.60/1.02  --bmc1_min_bound                        0
% 3.60/1.02  --bmc1_max_bound                        -1
% 3.60/1.02  --bmc1_max_bound_default                -1
% 3.60/1.02  --bmc1_symbol_reachability              true
% 3.60/1.02  --bmc1_property_lemmas                  false
% 3.60/1.02  --bmc1_k_induction                      false
% 3.60/1.02  --bmc1_non_equiv_states                 false
% 3.60/1.02  --bmc1_deadlock                         false
% 3.60/1.02  --bmc1_ucm                              false
% 3.60/1.02  --bmc1_add_unsat_core                   none
% 3.60/1.02  --bmc1_unsat_core_children              false
% 3.60/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.60/1.02  --bmc1_out_stat                         full
% 3.60/1.02  --bmc1_ground_init                      false
% 3.60/1.02  --bmc1_pre_inst_next_state              false
% 3.60/1.02  --bmc1_pre_inst_state                   false
% 3.60/1.02  --bmc1_pre_inst_reach_state             false
% 3.60/1.02  --bmc1_out_unsat_core                   false
% 3.60/1.02  --bmc1_aig_witness_out                  false
% 3.60/1.02  --bmc1_verbose                          false
% 3.60/1.02  --bmc1_dump_clauses_tptp                false
% 3.60/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.60/1.02  --bmc1_dump_file                        -
% 3.60/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.60/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.60/1.02  --bmc1_ucm_extend_mode                  1
% 3.60/1.02  --bmc1_ucm_init_mode                    2
% 3.60/1.02  --bmc1_ucm_cone_mode                    none
% 3.60/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.60/1.02  --bmc1_ucm_relax_model                  4
% 3.60/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.60/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.60/1.02  --bmc1_ucm_layered_model                none
% 3.60/1.02  --bmc1_ucm_max_lemma_size               10
% 3.60/1.02  
% 3.60/1.02  ------ AIG Options
% 3.60/1.02  
% 3.60/1.02  --aig_mode                              false
% 3.60/1.02  
% 3.60/1.02  ------ Instantiation Options
% 3.60/1.02  
% 3.60/1.02  --instantiation_flag                    true
% 3.60/1.02  --inst_sos_flag                         false
% 3.60/1.02  --inst_sos_phase                        true
% 3.60/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.60/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.60/1.02  --inst_lit_sel_side                     none
% 3.60/1.02  --inst_solver_per_active                1400
% 3.60/1.02  --inst_solver_calls_frac                1.
% 3.60/1.02  --inst_passive_queue_type               priority_queues
% 3.60/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.60/1.02  --inst_passive_queues_freq              [25;2]
% 3.60/1.02  --inst_dismatching                      true
% 3.60/1.02  --inst_eager_unprocessed_to_passive     true
% 3.60/1.02  --inst_prop_sim_given                   true
% 3.60/1.02  --inst_prop_sim_new                     false
% 3.60/1.02  --inst_subs_new                         false
% 3.60/1.02  --inst_eq_res_simp                      false
% 3.60/1.02  --inst_subs_given                       false
% 3.60/1.02  --inst_orphan_elimination               true
% 3.60/1.02  --inst_learning_loop_flag               true
% 3.60/1.02  --inst_learning_start                   3000
% 3.60/1.02  --inst_learning_factor                  2
% 3.60/1.02  --inst_start_prop_sim_after_learn       3
% 3.60/1.02  --inst_sel_renew                        solver
% 3.60/1.02  --inst_lit_activity_flag                true
% 3.60/1.02  --inst_restr_to_given                   false
% 3.60/1.02  --inst_activity_threshold               500
% 3.60/1.02  --inst_out_proof                        true
% 3.60/1.02  
% 3.60/1.02  ------ Resolution Options
% 3.60/1.02  
% 3.60/1.02  --resolution_flag                       false
% 3.60/1.02  --res_lit_sel                           adaptive
% 3.60/1.02  --res_lit_sel_side                      none
% 3.60/1.02  --res_ordering                          kbo
% 3.60/1.02  --res_to_prop_solver                    active
% 3.60/1.02  --res_prop_simpl_new                    false
% 3.60/1.02  --res_prop_simpl_given                  true
% 3.60/1.02  --res_passive_queue_type                priority_queues
% 3.60/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.60/1.02  --res_passive_queues_freq               [15;5]
% 3.60/1.02  --res_forward_subs                      full
% 3.60/1.02  --res_backward_subs                     full
% 3.60/1.02  --res_forward_subs_resolution           true
% 3.60/1.02  --res_backward_subs_resolution          true
% 3.60/1.02  --res_orphan_elimination                true
% 3.60/1.02  --res_time_limit                        2.
% 3.60/1.02  --res_out_proof                         true
% 3.60/1.02  
% 3.60/1.02  ------ Superposition Options
% 3.60/1.02  
% 3.60/1.02  --superposition_flag                    true
% 3.60/1.02  --sup_passive_queue_type                priority_queues
% 3.60/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.60/1.02  --sup_passive_queues_freq               [8;1;4]
% 3.60/1.02  --demod_completeness_check              fast
% 3.60/1.02  --demod_use_ground                      true
% 3.60/1.02  --sup_to_prop_solver                    passive
% 3.60/1.02  --sup_prop_simpl_new                    true
% 3.60/1.02  --sup_prop_simpl_given                  true
% 3.60/1.02  --sup_fun_splitting                     false
% 3.60/1.02  --sup_smt_interval                      50000
% 3.60/1.02  
% 3.60/1.02  ------ Superposition Simplification Setup
% 3.60/1.02  
% 3.60/1.02  --sup_indices_passive                   []
% 3.60/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.60/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.60/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.60/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.60/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.60/1.02  --sup_full_bw                           [BwDemod]
% 3.60/1.02  --sup_immed_triv                        [TrivRules]
% 3.60/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.60/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.60/1.02  --sup_immed_bw_main                     []
% 3.60/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.60/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.60/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.60/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.60/1.02  
% 3.60/1.02  ------ Combination Options
% 3.60/1.02  
% 3.60/1.02  --comb_res_mult                         3
% 3.60/1.02  --comb_sup_mult                         2
% 3.60/1.02  --comb_inst_mult                        10
% 3.60/1.02  
% 3.60/1.02  ------ Debug Options
% 3.60/1.02  
% 3.60/1.02  --dbg_backtrace                         false
% 3.60/1.02  --dbg_dump_prop_clauses                 false
% 3.60/1.02  --dbg_dump_prop_clauses_file            -
% 3.60/1.02  --dbg_out_stat                          false
% 3.60/1.02  
% 3.60/1.02  
% 3.60/1.02  
% 3.60/1.02  
% 3.60/1.02  ------ Proving...
% 3.60/1.02  
% 3.60/1.02  
% 3.60/1.02  % SZS status Theorem for theBenchmark.p
% 3.60/1.02  
% 3.60/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 3.60/1.02  
% 3.60/1.02  fof(f1,axiom,(
% 3.60/1.02    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.60/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/1.02  
% 3.60/1.02  fof(f37,plain,(
% 3.60/1.02    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.60/1.02    inference(nnf_transformation,[],[f1])).
% 3.60/1.02  
% 3.60/1.02  fof(f38,plain,(
% 3.60/1.02    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.60/1.02    inference(flattening,[],[f37])).
% 3.60/1.02  
% 3.60/1.02  fof(f48,plain,(
% 3.60/1.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.60/1.02    inference(cnf_transformation,[],[f38])).
% 3.60/1.02  
% 3.60/1.02  fof(f78,plain,(
% 3.60/1.02    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.60/1.02    inference(equality_resolution,[],[f48])).
% 3.60/1.02  
% 3.60/1.02  fof(f8,axiom,(
% 3.60/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X1) = X1)),
% 3.60/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/1.02  
% 3.60/1.02  fof(f24,plain,(
% 3.60/1.02    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 3.60/1.02    inference(ennf_transformation,[],[f8])).
% 3.60/1.02  
% 3.60/1.02  fof(f57,plain,(
% 3.60/1.02    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.60/1.02    inference(cnf_transformation,[],[f24])).
% 3.60/1.02  
% 3.60/1.02  fof(f11,axiom,(
% 3.60/1.02    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.60/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/1.02  
% 3.60/1.02  fof(f39,plain,(
% 3.60/1.02    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.60/1.02    inference(nnf_transformation,[],[f11])).
% 3.60/1.02  
% 3.60/1.02  fof(f61,plain,(
% 3.60/1.02    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.60/1.02    inference(cnf_transformation,[],[f39])).
% 3.60/1.02  
% 3.60/1.02  fof(f10,axiom,(
% 3.60/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 3.60/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/1.02  
% 3.60/1.02  fof(f26,plain,(
% 3.60/1.02    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 3.60/1.02    inference(ennf_transformation,[],[f10])).
% 3.60/1.02  
% 3.60/1.02  fof(f59,plain,(
% 3.60/1.02    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.60/1.02    inference(cnf_transformation,[],[f26])).
% 3.60/1.02  
% 3.60/1.02  fof(f3,axiom,(
% 3.60/1.02    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 3.60/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/1.02  
% 3.60/1.02  fof(f52,plain,(
% 3.60/1.02    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 3.60/1.02    inference(cnf_transformation,[],[f3])).
% 3.60/1.02  
% 3.60/1.02  fof(f76,plain,(
% 3.60/1.02    ( ! [X2,X0,X1] : (k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.60/1.02    inference(definition_unfolding,[],[f59,f52])).
% 3.60/1.02  
% 3.60/1.02  fof(f2,axiom,(
% 3.60/1.02    ! [X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X0)) => k1_xboole_0 = X0)),
% 3.60/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/1.02  
% 3.60/1.02  fof(f21,plain,(
% 3.60/1.02    ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k4_xboole_0(X1,X0)))),
% 3.60/1.02    inference(ennf_transformation,[],[f2])).
% 3.60/1.02  
% 3.60/1.02  fof(f51,plain,(
% 3.60/1.02    ( ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k4_xboole_0(X1,X0))) )),
% 3.60/1.02    inference(cnf_transformation,[],[f21])).
% 3.60/1.02  
% 3.60/1.02  fof(f5,axiom,(
% 3.60/1.02    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 3.60/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/1.02  
% 3.60/1.02  fof(f22,plain,(
% 3.60/1.02    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.60/1.02    inference(ennf_transformation,[],[f5])).
% 3.60/1.02  
% 3.60/1.02  fof(f54,plain,(
% 3.60/1.02    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.60/1.02    inference(cnf_transformation,[],[f22])).
% 3.60/1.02  
% 3.60/1.02  fof(f7,axiom,(
% 3.60/1.02    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 3.60/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/1.02  
% 3.60/1.02  fof(f23,plain,(
% 3.60/1.02    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.60/1.02    inference(ennf_transformation,[],[f7])).
% 3.60/1.02  
% 3.60/1.02  fof(f56,plain,(
% 3.60/1.02    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.60/1.02    inference(cnf_transformation,[],[f23])).
% 3.60/1.02  
% 3.60/1.02  fof(f60,plain,(
% 3.60/1.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.60/1.02    inference(cnf_transformation,[],[f39])).
% 3.60/1.02  
% 3.60/1.02  fof(f18,conjecture,(
% 3.60/1.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => (v3_tops_1(X1,X0) <=> k2_tops_1(X0,X1) = X1))))),
% 3.60/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/1.02  
% 3.60/1.02  fof(f19,negated_conjecture,(
% 3.60/1.02    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => (v3_tops_1(X1,X0) <=> k2_tops_1(X0,X1) = X1))))),
% 3.60/1.02    inference(negated_conjecture,[],[f18])).
% 3.60/1.02  
% 3.60/1.02  fof(f35,plain,(
% 3.60/1.02    ? [X0] : (? [X1] : (((v3_tops_1(X1,X0) <~> k2_tops_1(X0,X1) = X1) & v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.60/1.02    inference(ennf_transformation,[],[f19])).
% 3.60/1.02  
% 3.60/1.02  fof(f36,plain,(
% 3.60/1.02    ? [X0] : (? [X1] : ((v3_tops_1(X1,X0) <~> k2_tops_1(X0,X1) = X1) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.60/1.02    inference(flattening,[],[f35])).
% 3.60/1.02  
% 3.60/1.02  fof(f43,plain,(
% 3.60/1.02    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != X1 | ~v3_tops_1(X1,X0)) & (k2_tops_1(X0,X1) = X1 | v3_tops_1(X1,X0))) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.60/1.02    inference(nnf_transformation,[],[f36])).
% 3.60/1.02  
% 3.60/1.02  fof(f44,plain,(
% 3.60/1.02    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != X1 | ~v3_tops_1(X1,X0)) & (k2_tops_1(X0,X1) = X1 | v3_tops_1(X1,X0)) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.60/1.02    inference(flattening,[],[f43])).
% 3.60/1.02  
% 3.60/1.02  fof(f46,plain,(
% 3.60/1.02    ( ! [X0] : (? [X1] : ((k2_tops_1(X0,X1) != X1 | ~v3_tops_1(X1,X0)) & (k2_tops_1(X0,X1) = X1 | v3_tops_1(X1,X0)) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((k2_tops_1(X0,sK1) != sK1 | ~v3_tops_1(sK1,X0)) & (k2_tops_1(X0,sK1) = sK1 | v3_tops_1(sK1,X0)) & v4_pre_topc(sK1,X0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.60/1.02    introduced(choice_axiom,[])).
% 3.60/1.02  
% 3.60/1.02  fof(f45,plain,(
% 3.60/1.02    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != X1 | ~v3_tops_1(X1,X0)) & (k2_tops_1(X0,X1) = X1 | v3_tops_1(X1,X0)) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != X1 | ~v3_tops_1(X1,sK0)) & (k2_tops_1(sK0,X1) = X1 | v3_tops_1(X1,sK0)) & v4_pre_topc(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 3.60/1.02    introduced(choice_axiom,[])).
% 3.60/1.02  
% 3.60/1.02  fof(f47,plain,(
% 3.60/1.02    ((k2_tops_1(sK0,sK1) != sK1 | ~v3_tops_1(sK1,sK0)) & (k2_tops_1(sK0,sK1) = sK1 | v3_tops_1(sK1,sK0)) & v4_pre_topc(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 3.60/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f44,f46,f45])).
% 3.60/1.02  
% 3.60/1.02  fof(f72,plain,(
% 3.60/1.02    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.60/1.02    inference(cnf_transformation,[],[f47])).
% 3.60/1.02  
% 3.60/1.02  fof(f9,axiom,(
% 3.60/1.02    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 3.60/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/1.02  
% 3.60/1.02  fof(f25,plain,(
% 3.60/1.02    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.60/1.02    inference(ennf_transformation,[],[f9])).
% 3.60/1.02  
% 3.60/1.02  fof(f58,plain,(
% 3.60/1.02    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.60/1.02    inference(cnf_transformation,[],[f25])).
% 3.60/1.02  
% 3.60/1.02  fof(f14,axiom,(
% 3.60/1.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)))),
% 3.60/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/1.02  
% 3.60/1.02  fof(f30,plain,(
% 3.60/1.02    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.60/1.02    inference(ennf_transformation,[],[f14])).
% 3.60/1.02  
% 3.60/1.02  fof(f65,plain,(
% 3.60/1.02    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.60/1.02    inference(cnf_transformation,[],[f30])).
% 3.60/1.02  
% 3.60/1.02  fof(f71,plain,(
% 3.60/1.02    l1_pre_topc(sK0)),
% 3.60/1.02    inference(cnf_transformation,[],[f47])).
% 3.60/1.02  
% 3.60/1.02  fof(f12,axiom,(
% 3.60/1.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 3.60/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/1.02  
% 3.60/1.02  fof(f20,plain,(
% 3.60/1.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1)))),
% 3.60/1.02    inference(pure_predicate_removal,[],[f12])).
% 3.60/1.02  
% 3.60/1.02  fof(f27,plain,(
% 3.60/1.02    ! [X0] : (! [X1] : ((k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.60/1.02    inference(ennf_transformation,[],[f20])).
% 3.60/1.02  
% 3.60/1.02  fof(f28,plain,(
% 3.60/1.02    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.60/1.02    inference(flattening,[],[f27])).
% 3.60/1.02  
% 3.60/1.02  fof(f62,plain,(
% 3.60/1.02    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.60/1.02    inference(cnf_transformation,[],[f28])).
% 3.60/1.02  
% 3.60/1.02  fof(f73,plain,(
% 3.60/1.02    v4_pre_topc(sK1,sK0)),
% 3.60/1.02    inference(cnf_transformation,[],[f47])).
% 3.60/1.02  
% 3.60/1.02  fof(f15,axiom,(
% 3.60/1.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 3.60/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/1.02  
% 3.60/1.02  fof(f31,plain,(
% 3.60/1.02    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.60/1.02    inference(ennf_transformation,[],[f15])).
% 3.60/1.02  
% 3.60/1.02  fof(f41,plain,(
% 3.60/1.02    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1)) & (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.60/1.02    inference(nnf_transformation,[],[f31])).
% 3.60/1.02  
% 3.60/1.02  fof(f66,plain,(
% 3.60/1.02    ( ! [X0,X1] : (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.60/1.02    inference(cnf_transformation,[],[f41])).
% 3.60/1.02  
% 3.60/1.02  fof(f16,axiom,(
% 3.60/1.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> r1_tarski(X1,k2_tops_1(X0,X1)))))),
% 3.60/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/1.02  
% 3.60/1.02  fof(f32,plain,(
% 3.60/1.02    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> r1_tarski(X1,k2_tops_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.60/1.02    inference(ennf_transformation,[],[f16])).
% 3.60/1.02  
% 3.60/1.02  fof(f42,plain,(
% 3.60/1.02    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | ~r1_tarski(X1,k2_tops_1(X0,X1))) & (r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.60/1.02    inference(nnf_transformation,[],[f32])).
% 3.60/1.02  
% 3.60/1.02  fof(f69,plain,(
% 3.60/1.02    ( ! [X0,X1] : (v2_tops_1(X1,X0) | ~r1_tarski(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.60/1.02    inference(cnf_transformation,[],[f42])).
% 3.60/1.02  
% 3.60/1.02  fof(f74,plain,(
% 3.60/1.02    k2_tops_1(sK0,sK1) = sK1 | v3_tops_1(sK1,sK0)),
% 3.60/1.02    inference(cnf_transformation,[],[f47])).
% 3.60/1.02  
% 3.60/1.02  fof(f17,axiom,(
% 3.60/1.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tops_1(X1,X0) => v2_tops_1(X1,X0))))),
% 3.60/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/1.02  
% 3.60/1.02  fof(f33,plain,(
% 3.60/1.02    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) | ~v3_tops_1(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.60/1.02    inference(ennf_transformation,[],[f17])).
% 3.60/1.02  
% 3.60/1.02  fof(f34,plain,(
% 3.60/1.02    ! [X0] : (! [X1] : (v2_tops_1(X1,X0) | ~v3_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.60/1.02    inference(flattening,[],[f33])).
% 3.60/1.02  
% 3.60/1.02  fof(f70,plain,(
% 3.60/1.02    ( ! [X0,X1] : (v2_tops_1(X1,X0) | ~v3_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.60/1.02    inference(cnf_transformation,[],[f34])).
% 3.60/1.02  
% 3.60/1.02  fof(f75,plain,(
% 3.60/1.02    k2_tops_1(sK0,sK1) != sK1 | ~v3_tops_1(sK1,sK0)),
% 3.60/1.02    inference(cnf_transformation,[],[f47])).
% 3.60/1.02  
% 3.60/1.02  fof(f13,axiom,(
% 3.60/1.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tops_1(X1,X0) <=> v2_tops_1(k2_pre_topc(X0,X1),X0))))),
% 3.60/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.60/1.02  
% 3.60/1.02  fof(f29,plain,(
% 3.60/1.02    ! [X0] : (! [X1] : ((v3_tops_1(X1,X0) <=> v2_tops_1(k2_pre_topc(X0,X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.60/1.02    inference(ennf_transformation,[],[f13])).
% 3.60/1.02  
% 3.60/1.02  fof(f40,plain,(
% 3.60/1.02    ! [X0] : (! [X1] : (((v3_tops_1(X1,X0) | ~v2_tops_1(k2_pre_topc(X0,X1),X0)) & (v2_tops_1(k2_pre_topc(X0,X1),X0) | ~v3_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.60/1.02    inference(nnf_transformation,[],[f29])).
% 3.60/1.02  
% 3.60/1.02  fof(f64,plain,(
% 3.60/1.02    ( ! [X0,X1] : (v3_tops_1(X1,X0) | ~v2_tops_1(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.60/1.02    inference(cnf_transformation,[],[f40])).
% 3.60/1.02  
% 3.60/1.02  fof(f67,plain,(
% 3.60/1.02    ( ! [X0,X1] : (v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.60/1.02    inference(cnf_transformation,[],[f41])).
% 3.60/1.02  
% 3.60/1.02  cnf(c_2,plain,
% 3.60/1.02      ( r1_tarski(X0,X0) ),
% 3.60/1.02      inference(cnf_transformation,[],[f78]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_2205,plain,
% 3.60/1.02      ( r1_tarski(X0,X0) = iProver_top ),
% 3.60/1.02      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_8,plain,
% 3.60/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | k9_subset_1(X1,X2,X2) = X2 ),
% 3.60/1.02      inference(cnf_transformation,[],[f57]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_11,plain,
% 3.60/1.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.60/1.02      inference(cnf_transformation,[],[f61]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_209,plain,
% 3.60/1.02      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.60/1.02      inference(prop_impl,[status(thm)],[c_11]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_210,plain,
% 3.60/1.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.60/1.02      inference(renaming,[status(thm)],[c_209]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_258,plain,
% 3.60/1.02      ( ~ r1_tarski(X0,X1) | k9_subset_1(X1,X2,X2) = X2 ),
% 3.60/1.02      inference(bin_hyper_res,[status(thm)],[c_8,c_210]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_2197,plain,
% 3.60/1.02      ( k9_subset_1(X0,X1,X1) = X1 | r1_tarski(X2,X0) != iProver_top ),
% 3.60/1.02      inference(predicate_to_equality,[status(thm)],[c_258]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_3769,plain,
% 3.60/1.02      ( k9_subset_1(X0,X1,X1) = X1 ),
% 3.60/1.02      inference(superposition,[status(thm)],[c_2205,c_2197]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_10,plain,
% 3.60/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.60/1.02      | k4_xboole_0(X2,k4_xboole_0(X2,X0)) = k9_subset_1(X1,X2,X0) ),
% 3.60/1.02      inference(cnf_transformation,[],[f76]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_260,plain,
% 3.60/1.02      ( ~ r1_tarski(X0,X1)
% 3.60/1.02      | k4_xboole_0(X2,k4_xboole_0(X2,X0)) = k9_subset_1(X1,X2,X0) ),
% 3.60/1.02      inference(bin_hyper_res,[status(thm)],[c_10,c_210]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_2195,plain,
% 3.60/1.02      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k9_subset_1(X2,X0,X1)
% 3.60/1.02      | r1_tarski(X1,X2) != iProver_top ),
% 3.60/1.02      inference(predicate_to_equality,[status(thm)],[c_260]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_4959,plain,
% 3.60/1.02      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k9_subset_1(X1,X0,X1) ),
% 3.60/1.02      inference(superposition,[status(thm)],[c_2205,c_2195]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_3,plain,
% 3.60/1.02      ( ~ r1_tarski(X0,k4_xboole_0(X1,X0)) | k1_xboole_0 = X0 ),
% 3.60/1.02      inference(cnf_transformation,[],[f51]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_2204,plain,
% 3.60/1.02      ( k1_xboole_0 = X0
% 3.60/1.02      | r1_tarski(X0,k4_xboole_0(X1,X0)) != iProver_top ),
% 3.60/1.02      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_6058,plain,
% 3.60/1.02      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 3.60/1.02      | r1_tarski(k4_xboole_0(X0,X1),k9_subset_1(X1,X0,X1)) != iProver_top ),
% 3.60/1.02      inference(superposition,[status(thm)],[c_4959,c_2204]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_6066,plain,
% 3.60/1.02      ( k4_xboole_0(X0,X0) = k1_xboole_0
% 3.60/1.02      | r1_tarski(k4_xboole_0(X0,X0),X0) != iProver_top ),
% 3.60/1.02      inference(superposition,[status(thm)],[c_3769,c_6058]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_87,plain,
% 3.60/1.02      ( r1_tarski(X0,X0) = iProver_top ),
% 3.60/1.02      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_5,plain,
% 3.60/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.60/1.02      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 3.60/1.02      inference(cnf_transformation,[],[f54]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_256,plain,
% 3.60/1.02      ( ~ r1_tarski(X0,X1) | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 3.60/1.02      inference(bin_hyper_res,[status(thm)],[c_5,c_210]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_2199,plain,
% 3.60/1.02      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
% 3.60/1.02      | r1_tarski(X1,X0) != iProver_top ),
% 3.60/1.02      inference(predicate_to_equality,[status(thm)],[c_256]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_3918,plain,
% 3.60/1.02      ( k3_subset_1(X0,X0) = k4_xboole_0(X0,X0) ),
% 3.60/1.02      inference(superposition,[status(thm)],[c_2205,c_2199]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_7,plain,
% 3.60/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.60/1.02      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 3.60/1.02      inference(cnf_transformation,[],[f56]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_257,plain,
% 3.60/1.02      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
% 3.60/1.02      | ~ r1_tarski(X1,X0) ),
% 3.60/1.02      inference(bin_hyper_res,[status(thm)],[c_7,c_210]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_2198,plain,
% 3.60/1.02      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) = iProver_top
% 3.60/1.02      | r1_tarski(X1,X0) != iProver_top ),
% 3.60/1.02      inference(predicate_to_equality,[status(thm)],[c_257]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_12,plain,
% 3.60/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.60/1.02      inference(cnf_transformation,[],[f60]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_2201,plain,
% 3.60/1.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.60/1.02      | r1_tarski(X0,X1) = iProver_top ),
% 3.60/1.02      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_4658,plain,
% 3.60/1.02      ( r1_tarski(X0,X1) != iProver_top
% 3.60/1.02      | r1_tarski(k3_subset_1(X1,X0),X1) = iProver_top ),
% 3.60/1.02      inference(superposition,[status(thm)],[c_2198,c_2201]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_4888,plain,
% 3.60/1.02      ( r1_tarski(X0,X0) != iProver_top
% 3.60/1.02      | r1_tarski(k4_xboole_0(X0,X0),X0) = iProver_top ),
% 3.60/1.02      inference(superposition,[status(thm)],[c_3918,c_4658]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_9109,plain,
% 3.60/1.02      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.60/1.02      inference(global_propositional_subsumption,
% 3.60/1.02                [status(thm)],
% 3.60/1.02                [c_6066,c_87,c_4888]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_9187,plain,
% 3.60/1.02      ( k9_subset_1(X0,X0,X0) = k4_xboole_0(X0,k1_xboole_0) ),
% 3.60/1.02      inference(superposition,[status(thm)],[c_9109,c_4959]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_9189,plain,
% 3.60/1.02      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.60/1.02      inference(demodulation,[status(thm)],[c_9187,c_3769]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_9191,plain,
% 3.60/1.02      ( k4_xboole_0(sK1,k1_xboole_0) = sK1 ),
% 3.60/1.02      inference(instantiation,[status(thm)],[c_9189]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_25,negated_conjecture,
% 3.60/1.02      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.60/1.02      inference(cnf_transformation,[],[f72]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_2200,plain,
% 3.60/1.02      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.60/1.02      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_2944,plain,
% 3.60/1.02      ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
% 3.60/1.02      inference(superposition,[status(thm)],[c_2200,c_2201]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_9,plain,
% 3.60/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.60/1.02      | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 3.60/1.02      inference(cnf_transformation,[],[f58]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_259,plain,
% 3.60/1.02      ( ~ r1_tarski(X0,X1) | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 3.60/1.02      inference(bin_hyper_res,[status(thm)],[c_9,c_210]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_2196,plain,
% 3.60/1.02      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
% 3.60/1.02      | r1_tarski(X1,X0) != iProver_top ),
% 3.60/1.02      inference(predicate_to_equality,[status(thm)],[c_259]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_4402,plain,
% 3.60/1.02      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
% 3.60/1.02      inference(superposition,[status(thm)],[c_2944,c_2196]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_16,plain,
% 3.60/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.60/1.02      | ~ l1_pre_topc(X1)
% 3.60/1.02      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
% 3.60/1.02      inference(cnf_transformation,[],[f65]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_26,negated_conjecture,
% 3.60/1.02      ( l1_pre_topc(sK0) ),
% 3.60/1.02      inference(cnf_transformation,[],[f71]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_478,plain,
% 3.60/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.60/1.02      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0)
% 3.60/1.02      | sK0 != X1 ),
% 3.60/1.02      inference(resolution_lifted,[status(thm)],[c_16,c_26]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_479,plain,
% 3.60/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.60/1.02      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
% 3.60/1.02      inference(unflattening,[status(thm)],[c_478]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_2190,plain,
% 3.60/1.02      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0)
% 3.60/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.60/1.02      inference(predicate_to_equality,[status(thm)],[c_479]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_2412,plain,
% 3.60/1.02      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 3.60/1.02      inference(superposition,[status(thm)],[c_2200,c_2190]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_13,plain,
% 3.60/1.02      ( ~ v4_pre_topc(X0,X1)
% 3.60/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.60/1.02      | ~ l1_pre_topc(X1)
% 3.60/1.02      | k2_pre_topc(X1,X0) = X0 ),
% 3.60/1.02      inference(cnf_transformation,[],[f62]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_24,negated_conjecture,
% 3.60/1.02      ( v4_pre_topc(sK1,sK0) ),
% 3.60/1.02      inference(cnf_transformation,[],[f73]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_364,plain,
% 3.60/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.60/1.02      | ~ l1_pre_topc(X1)
% 3.60/1.02      | k2_pre_topc(X1,X0) = X0
% 3.60/1.02      | sK1 != X0
% 3.60/1.02      | sK0 != X1 ),
% 3.60/1.02      inference(resolution_lifted,[status(thm)],[c_13,c_24]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_365,plain,
% 3.60/1.02      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.60/1.02      | ~ l1_pre_topc(sK0)
% 3.60/1.02      | k2_pre_topc(sK0,sK1) = sK1 ),
% 3.60/1.02      inference(unflattening,[status(thm)],[c_364]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_367,plain,
% 3.60/1.02      ( k2_pre_topc(sK0,sK1) = sK1 ),
% 3.60/1.02      inference(global_propositional_subsumption,
% 3.60/1.02                [status(thm)],
% 3.60/1.02                [c_365,c_26,c_25]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_18,plain,
% 3.60/1.02      ( ~ v2_tops_1(X0,X1)
% 3.60/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.60/1.02      | ~ l1_pre_topc(X1)
% 3.60/1.02      | k1_tops_1(X1,X0) = k1_xboole_0 ),
% 3.60/1.02      inference(cnf_transformation,[],[f66]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_448,plain,
% 3.60/1.02      ( ~ v2_tops_1(X0,X1)
% 3.60/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.60/1.02      | k1_tops_1(X1,X0) = k1_xboole_0
% 3.60/1.02      | sK0 != X1 ),
% 3.60/1.02      inference(resolution_lifted,[status(thm)],[c_18,c_26]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_449,plain,
% 3.60/1.02      ( ~ v2_tops_1(X0,sK0)
% 3.60/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.60/1.02      | k1_tops_1(sK0,X0) = k1_xboole_0 ),
% 3.60/1.02      inference(unflattening,[status(thm)],[c_448]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_2192,plain,
% 3.60/1.02      ( k1_tops_1(sK0,X0) = k1_xboole_0
% 3.60/1.02      | v2_tops_1(X0,sK0) != iProver_top
% 3.60/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.60/1.02      inference(predicate_to_equality,[status(thm)],[c_449]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_2395,plain,
% 3.60/1.02      ( k1_tops_1(sK0,sK1) = k1_xboole_0
% 3.60/1.02      | v2_tops_1(sK1,sK0) != iProver_top ),
% 3.60/1.02      inference(superposition,[status(thm)],[c_2200,c_2192]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_88,plain,
% 3.60/1.02      ( r1_tarski(sK1,sK1) ),
% 3.60/1.02      inference(instantiation,[status(thm)],[c_2]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_19,plain,
% 3.60/1.02      ( v2_tops_1(X0,X1)
% 3.60/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.60/1.02      | ~ r1_tarski(X0,k2_tops_1(X1,X0))
% 3.60/1.02      | ~ l1_pre_topc(X1) ),
% 3.60/1.02      inference(cnf_transformation,[],[f69]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_433,plain,
% 3.60/1.02      ( v2_tops_1(X0,X1)
% 3.60/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.60/1.02      | ~ r1_tarski(X0,k2_tops_1(X1,X0))
% 3.60/1.02      | sK0 != X1 ),
% 3.60/1.02      inference(resolution_lifted,[status(thm)],[c_19,c_26]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_434,plain,
% 3.60/1.02      ( v2_tops_1(X0,sK0)
% 3.60/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.60/1.02      | ~ r1_tarski(X0,k2_tops_1(sK0,X0)) ),
% 3.60/1.02      inference(unflattening,[status(thm)],[c_433]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_436,plain,
% 3.60/1.02      ( v2_tops_1(sK1,sK0)
% 3.60/1.02      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.60/1.02      | ~ r1_tarski(sK1,k2_tops_1(sK0,sK1)) ),
% 3.60/1.02      inference(instantiation,[status(thm)],[c_434]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_451,plain,
% 3.60/1.02      ( ~ v2_tops_1(sK1,sK0)
% 3.60/1.02      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.60/1.02      | k1_tops_1(sK0,sK1) = k1_xboole_0 ),
% 3.60/1.02      inference(instantiation,[status(thm)],[c_449]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_23,negated_conjecture,
% 3.60/1.02      ( v3_tops_1(sK1,sK0) | k2_tops_1(sK0,sK1) = sK1 ),
% 3.60/1.02      inference(cnf_transformation,[],[f74]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_213,plain,
% 3.60/1.02      ( v3_tops_1(sK1,sK0) | k2_tops_1(sK0,sK1) = sK1 ),
% 3.60/1.02      inference(prop_impl,[status(thm)],[c_23]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_21,plain,
% 3.60/1.02      ( v2_tops_1(X0,X1)
% 3.60/1.02      | ~ v3_tops_1(X0,X1)
% 3.60/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.60/1.02      | ~ l1_pre_topc(X1) ),
% 3.60/1.02      inference(cnf_transformation,[],[f70]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_403,plain,
% 3.60/1.02      ( v2_tops_1(X0,X1)
% 3.60/1.02      | ~ v3_tops_1(X0,X1)
% 3.60/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.60/1.02      | sK0 != X1 ),
% 3.60/1.02      inference(resolution_lifted,[status(thm)],[c_21,c_26]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_404,plain,
% 3.60/1.02      ( v2_tops_1(X0,sK0)
% 3.60/1.02      | ~ v3_tops_1(X0,sK0)
% 3.60/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.60/1.02      inference(unflattening,[status(thm)],[c_403]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_537,plain,
% 3.60/1.02      ( v2_tops_1(X0,sK0)
% 3.60/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.60/1.02      | k2_tops_1(sK0,sK1) = sK1
% 3.60/1.02      | sK1 != X0
% 3.60/1.02      | sK0 != sK0 ),
% 3.60/1.02      inference(resolution_lifted,[status(thm)],[c_213,c_404]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_538,plain,
% 3.60/1.02      ( v2_tops_1(sK1,sK0)
% 3.60/1.02      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.60/1.02      | k2_tops_1(sK0,sK1) = sK1 ),
% 3.60/1.02      inference(unflattening,[status(thm)],[c_537]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_540,plain,
% 3.60/1.02      ( v2_tops_1(sK1,sK0) | k2_tops_1(sK0,sK1) = sK1 ),
% 3.60/1.02      inference(global_propositional_subsumption,
% 3.60/1.02                [status(thm)],
% 3.60/1.02                [c_538,c_25]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_1678,plain,
% 3.60/1.02      ( ~ r1_tarski(X0,X1) | r1_tarski(X0,X2) | X2 != X1 ),
% 3.60/1.02      theory(equality) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_2379,plain,
% 3.60/1.02      ( ~ r1_tarski(X0,X1)
% 3.60/1.02      | r1_tarski(X0,k2_tops_1(sK0,X0))
% 3.60/1.02      | k2_tops_1(sK0,X0) != X1 ),
% 3.60/1.02      inference(instantiation,[status(thm)],[c_1678]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_2381,plain,
% 3.60/1.02      ( r1_tarski(sK1,k2_tops_1(sK0,sK1))
% 3.60/1.02      | ~ r1_tarski(sK1,sK1)
% 3.60/1.02      | k2_tops_1(sK0,sK1) != sK1 ),
% 3.60/1.02      inference(instantiation,[status(thm)],[c_2379]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_2398,plain,
% 3.60/1.02      ( k1_tops_1(sK0,sK1) = k1_xboole_0 ),
% 3.60/1.02      inference(global_propositional_subsumption,
% 3.60/1.02                [status(thm)],
% 3.60/1.02                [c_2395,c_25,c_88,c_436,c_451,c_540,c_2381]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_2413,plain,
% 3.60/1.02      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) = k2_tops_1(sK0,sK1) ),
% 3.60/1.02      inference(light_normalisation,[status(thm)],[c_2412,c_367,c_2398]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_4496,plain,
% 3.60/1.02      ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_xboole_0) ),
% 3.60/1.02      inference(demodulation,[status(thm)],[c_4402,c_2413]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_22,negated_conjecture,
% 3.60/1.02      ( ~ v3_tops_1(sK1,sK0) | k2_tops_1(sK0,sK1) != sK1 ),
% 3.60/1.02      inference(cnf_transformation,[],[f75]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_211,plain,
% 3.60/1.02      ( ~ v3_tops_1(sK1,sK0) | k2_tops_1(sK0,sK1) != sK1 ),
% 3.60/1.02      inference(prop_impl,[status(thm)],[c_22]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_14,plain,
% 3.60/1.02      ( ~ v2_tops_1(k2_pre_topc(X0,X1),X0)
% 3.60/1.02      | v3_tops_1(X1,X0)
% 3.60/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.60/1.02      | ~ l1_pre_topc(X0) ),
% 3.60/1.02      inference(cnf_transformation,[],[f64]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_388,plain,
% 3.60/1.02      ( ~ v2_tops_1(k2_pre_topc(X0,X1),X0)
% 3.60/1.02      | v3_tops_1(X1,X0)
% 3.60/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.60/1.02      | sK0 != X0 ),
% 3.60/1.02      inference(resolution_lifted,[status(thm)],[c_14,c_26]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_389,plain,
% 3.60/1.02      ( ~ v2_tops_1(k2_pre_topc(sK0,X0),sK0)
% 3.60/1.02      | v3_tops_1(X0,sK0)
% 3.60/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.60/1.02      inference(unflattening,[status(thm)],[c_388]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_565,plain,
% 3.60/1.02      ( ~ v2_tops_1(k2_pre_topc(sK0,X0),sK0)
% 3.60/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.60/1.02      | k2_tops_1(sK0,sK1) != sK1
% 3.60/1.02      | sK1 != X0
% 3.60/1.02      | sK0 != sK0 ),
% 3.60/1.02      inference(resolution_lifted,[status(thm)],[c_211,c_389]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_566,plain,
% 3.60/1.02      ( ~ v2_tops_1(k2_pre_topc(sK0,sK1),sK0)
% 3.60/1.02      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.60/1.02      | k2_tops_1(sK0,sK1) != sK1 ),
% 3.60/1.02      inference(unflattening,[status(thm)],[c_565]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_568,plain,
% 3.60/1.02      ( ~ v2_tops_1(k2_pre_topc(sK0,sK1),sK0)
% 3.60/1.02      | k2_tops_1(sK0,sK1) != sK1 ),
% 3.60/1.02      inference(global_propositional_subsumption,
% 3.60/1.02                [status(thm)],
% 3.60/1.02                [c_566,c_25]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_1139,plain,
% 3.60/1.02      ( ~ v2_tops_1(k2_pre_topc(sK0,sK1),sK0)
% 3.60/1.02      | k2_tops_1(sK0,sK1) != sK1 ),
% 3.60/1.02      inference(prop_impl,[status(thm)],[c_25,c_566]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_2187,plain,
% 3.60/1.02      ( k2_tops_1(sK0,sK1) != sK1
% 3.60/1.02      | v2_tops_1(k2_pre_topc(sK0,sK1),sK0) != iProver_top ),
% 3.60/1.02      inference(predicate_to_equality,[status(thm)],[c_1139]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_2244,plain,
% 3.60/1.02      ( k2_tops_1(sK0,sK1) != sK1 | v2_tops_1(sK1,sK0) != iProver_top ),
% 3.60/1.02      inference(light_normalisation,[status(thm)],[c_2187,c_367]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_5203,plain,
% 3.60/1.02      ( k4_xboole_0(sK1,k1_xboole_0) != sK1
% 3.60/1.02      | v2_tops_1(sK1,sK0) != iProver_top ),
% 3.60/1.02      inference(demodulation,[status(thm)],[c_4496,c_2244]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_17,plain,
% 3.60/1.02      ( v2_tops_1(X0,X1)
% 3.60/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.60/1.02      | ~ l1_pre_topc(X1)
% 3.60/1.02      | k1_tops_1(X1,X0) != k1_xboole_0 ),
% 3.60/1.02      inference(cnf_transformation,[],[f67]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_463,plain,
% 3.60/1.02      ( v2_tops_1(X0,X1)
% 3.60/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.60/1.02      | k1_tops_1(X1,X0) != k1_xboole_0
% 3.60/1.02      | sK0 != X1 ),
% 3.60/1.02      inference(resolution_lifted,[status(thm)],[c_17,c_26]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_464,plain,
% 3.60/1.02      ( v2_tops_1(X0,sK0)
% 3.60/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.60/1.02      | k1_tops_1(sK0,X0) != k1_xboole_0 ),
% 3.60/1.02      inference(unflattening,[status(thm)],[c_463]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_939,plain,
% 3.60/1.02      ( v2_tops_1(X0,sK0)
% 3.60/1.02      | k1_tops_1(sK0,X0) != k1_xboole_0
% 3.60/1.02      | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(u1_struct_0(sK0))
% 3.60/1.02      | sK1 != X0 ),
% 3.60/1.02      inference(resolution_lifted,[status(thm)],[c_25,c_464]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_940,plain,
% 3.60/1.02      ( v2_tops_1(sK1,sK0) | k1_tops_1(sK0,sK1) != k1_xboole_0 ),
% 3.60/1.02      inference(unflattening,[status(thm)],[c_939]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(c_941,plain,
% 3.60/1.02      ( k1_tops_1(sK0,sK1) != k1_xboole_0
% 3.60/1.02      | v2_tops_1(sK1,sK0) = iProver_top ),
% 3.60/1.02      inference(predicate_to_equality,[status(thm)],[c_940]) ).
% 3.60/1.02  
% 3.60/1.02  cnf(contradiction,plain,
% 3.60/1.02      ( $false ),
% 3.60/1.02      inference(minisat,[status(thm)],[c_9191,c_5203,c_2398,c_941]) ).
% 3.60/1.02  
% 3.60/1.02  
% 3.60/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 3.60/1.02  
% 3.60/1.02  ------                               Statistics
% 3.60/1.02  
% 3.60/1.02  ------ General
% 3.60/1.02  
% 3.60/1.02  abstr_ref_over_cycles:                  0
% 3.60/1.02  abstr_ref_under_cycles:                 0
% 3.60/1.02  gc_basic_clause_elim:                   0
% 3.60/1.02  forced_gc_time:                         0
% 3.60/1.02  parsing_time:                           0.011
% 3.60/1.02  unif_index_cands_time:                  0.
% 3.60/1.02  unif_index_add_time:                    0.
% 3.60/1.02  orderings_time:                         0.
% 3.60/1.02  out_proof_time:                         0.012
% 3.60/1.02  total_time:                             0.349
% 3.60/1.02  num_of_symbols:                         50
% 3.60/1.02  num_of_terms:                           8130
% 3.60/1.02  
% 3.60/1.02  ------ Preprocessing
% 3.60/1.02  
% 3.60/1.02  num_of_splits:                          0
% 3.60/1.02  num_of_split_atoms:                     0
% 3.60/1.02  num_of_reused_defs:                     0
% 3.60/1.02  num_eq_ax_congr_red:                    31
% 3.60/1.02  num_of_sem_filtered_clauses:            1
% 3.60/1.02  num_of_subtypes:                        0
% 3.60/1.02  monotx_restored_types:                  0
% 3.60/1.02  sat_num_of_epr_types:                   0
% 3.60/1.02  sat_num_of_non_cyclic_types:            0
% 3.60/1.02  sat_guarded_non_collapsed_types:        0
% 3.60/1.02  num_pure_diseq_elim:                    0
% 3.60/1.02  simp_replaced_by:                       0
% 3.60/1.02  res_preprocessed:                       120
% 3.60/1.02  prep_upred:                             0
% 3.60/1.02  prep_unflattend:                        67
% 3.60/1.02  smt_new_axioms:                         0
% 3.60/1.02  pred_elim_cands:                        3
% 3.60/1.02  pred_elim:                              3
% 3.60/1.02  pred_elim_cl:                           3
% 3.60/1.02  pred_elim_cycles:                       5
% 3.60/1.02  merged_defs:                            16
% 3.60/1.02  merged_defs_ncl:                        0
% 3.60/1.02  bin_hyper_res:                          22
% 3.60/1.02  prep_cycles:                            4
% 3.60/1.02  pred_elim_time:                         0.018
% 3.60/1.02  splitting_time:                         0.
% 3.60/1.02  sem_filter_time:                        0.
% 3.60/1.02  monotx_time:                            0.
% 3.60/1.02  subtype_inf_time:                       0.
% 3.60/1.02  
% 3.60/1.02  ------ Problem properties
% 3.60/1.02  
% 3.60/1.02  clauses:                                23
% 3.60/1.02  conjectures:                            1
% 3.60/1.02  epr:                                    2
% 3.60/1.02  horn:                                   22
% 3.60/1.02  ground:                                 5
% 3.60/1.02  unary:                                  5
% 3.60/1.02  binary:                                 12
% 3.60/1.02  lits:                                   47
% 3.60/1.02  lits_eq:                                13
% 3.60/1.02  fd_pure:                                0
% 3.60/1.02  fd_pseudo:                              0
% 3.60/1.02  fd_cond:                                1
% 3.60/1.02  fd_pseudo_cond:                         1
% 3.60/1.02  ac_symbols:                             0
% 3.60/1.02  
% 3.60/1.02  ------ Propositional Solver
% 3.60/1.02  
% 3.60/1.02  prop_solver_calls:                      30
% 3.60/1.02  prop_fast_solver_calls:                 960
% 3.60/1.02  smt_solver_calls:                       0
% 3.60/1.02  smt_fast_solver_calls:                  0
% 3.60/1.02  prop_num_of_clauses:                    3637
% 3.60/1.02  prop_preprocess_simplified:             8960
% 3.60/1.02  prop_fo_subsumed:                       18
% 3.60/1.02  prop_solver_time:                       0.
% 3.60/1.02  smt_solver_time:                        0.
% 3.60/1.02  smt_fast_solver_time:                   0.
% 3.60/1.02  prop_fast_solver_time:                  0.
% 3.60/1.02  prop_unsat_core_time:                   0.
% 3.60/1.02  
% 3.60/1.02  ------ QBF
% 3.60/1.02  
% 3.60/1.02  qbf_q_res:                              0
% 3.60/1.02  qbf_num_tautologies:                    0
% 3.60/1.02  qbf_prep_cycles:                        0
% 3.60/1.02  
% 3.60/1.02  ------ BMC1
% 3.60/1.02  
% 3.60/1.02  bmc1_current_bound:                     -1
% 3.60/1.02  bmc1_last_solved_bound:                 -1
% 3.60/1.02  bmc1_unsat_core_size:                   -1
% 3.60/1.02  bmc1_unsat_core_parents_size:           -1
% 3.60/1.02  bmc1_merge_next_fun:                    0
% 3.60/1.02  bmc1_unsat_core_clauses_time:           0.
% 3.60/1.02  
% 3.60/1.02  ------ Instantiation
% 3.60/1.02  
% 3.60/1.02  inst_num_of_clauses:                    1163
% 3.60/1.02  inst_num_in_passive:                    176
% 3.60/1.02  inst_num_in_active:                     448
% 3.60/1.02  inst_num_in_unprocessed:                540
% 3.60/1.02  inst_num_of_loops:                      470
% 3.60/1.02  inst_num_of_learning_restarts:          0
% 3.60/1.02  inst_num_moves_active_passive:          18
% 3.60/1.02  inst_lit_activity:                      0
% 3.60/1.02  inst_lit_activity_moves:                0
% 3.60/1.02  inst_num_tautologies:                   0
% 3.60/1.02  inst_num_prop_implied:                  0
% 3.60/1.02  inst_num_existing_simplified:           0
% 3.60/1.02  inst_num_eq_res_simplified:             0
% 3.60/1.02  inst_num_child_elim:                    0
% 3.60/1.02  inst_num_of_dismatching_blockings:      285
% 3.60/1.02  inst_num_of_non_proper_insts:           1224
% 3.60/1.02  inst_num_of_duplicates:                 0
% 3.60/1.02  inst_inst_num_from_inst_to_res:         0
% 3.60/1.02  inst_dismatching_checking_time:         0.
% 3.60/1.02  
% 3.60/1.02  ------ Resolution
% 3.60/1.02  
% 3.60/1.02  res_num_of_clauses:                     0
% 3.60/1.02  res_num_in_passive:                     0
% 3.60/1.02  res_num_in_active:                      0
% 3.60/1.02  res_num_of_loops:                       124
% 3.60/1.02  res_forward_subset_subsumed:            76
% 3.60/1.02  res_backward_subset_subsumed:           4
% 3.60/1.02  res_forward_subsumed:                   0
% 3.60/1.02  res_backward_subsumed:                  0
% 3.60/1.02  res_forward_subsumption_resolution:     0
% 3.60/1.02  res_backward_subsumption_resolution:    0
% 3.60/1.02  res_clause_to_clause_subsumption:       745
% 3.60/1.02  res_orphan_elimination:                 0
% 3.60/1.02  res_tautology_del:                      152
% 3.60/1.02  res_num_eq_res_simplified:              0
% 3.60/1.02  res_num_sel_changes:                    0
% 3.60/1.02  res_moves_from_active_to_pass:          0
% 3.60/1.02  
% 3.60/1.02  ------ Superposition
% 3.60/1.02  
% 3.60/1.02  sup_time_total:                         0.
% 3.60/1.02  sup_time_generating:                    0.
% 3.60/1.02  sup_time_sim_full:                      0.
% 3.60/1.02  sup_time_sim_immed:                     0.
% 3.60/1.02  
% 3.60/1.02  sup_num_of_clauses:                     123
% 3.60/1.02  sup_num_in_active:                      77
% 3.60/1.02  sup_num_in_passive:                     46
% 3.60/1.02  sup_num_of_loops:                       93
% 3.60/1.02  sup_fw_superposition:                   91
% 3.60/1.02  sup_bw_superposition:                   104
% 3.60/1.02  sup_immediate_simplified:               54
% 3.60/1.02  sup_given_eliminated:                   0
% 3.60/1.02  comparisons_done:                       0
% 3.60/1.02  comparisons_avoided:                    0
% 3.60/1.02  
% 3.60/1.02  ------ Simplifications
% 3.60/1.02  
% 3.60/1.02  
% 3.60/1.02  sim_fw_subset_subsumed:                 11
% 3.60/1.02  sim_bw_subset_subsumed:                 15
% 3.60/1.02  sim_fw_subsumed:                        5
% 3.60/1.02  sim_bw_subsumed:                        4
% 3.60/1.02  sim_fw_subsumption_res:                 0
% 3.60/1.02  sim_bw_subsumption_res:                 3
% 3.60/1.02  sim_tautology_del:                      16
% 3.60/1.02  sim_eq_tautology_del:                   3
% 3.60/1.02  sim_eq_res_simp:                        0
% 3.60/1.02  sim_fw_demodulated:                     18
% 3.60/1.02  sim_bw_demodulated:                     22
% 3.60/1.02  sim_light_normalised:                   19
% 3.60/1.02  sim_joinable_taut:                      0
% 3.60/1.02  sim_joinable_simp:                      0
% 3.60/1.02  sim_ac_normalised:                      0
% 3.60/1.02  sim_smt_subsumption:                    0
% 3.60/1.02  
%------------------------------------------------------------------------------
