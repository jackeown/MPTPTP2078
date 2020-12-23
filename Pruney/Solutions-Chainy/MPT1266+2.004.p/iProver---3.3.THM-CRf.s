%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:14:58 EST 2020

% Result     : Theorem 3.70s
% Output     : CNFRefutation 3.70s
% Verified   : 
% Statistics : Number of formulae       :  175 (1311 expanded)
%              Number of clauses        :  107 ( 426 expanded)
%              Number of leaves         :   21 ( 297 expanded)
%              Depth                    :   21
%              Number of atoms          :  466 (4897 expanded)
%              Number of equality atoms :  168 (1547 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f37])).

fof(f76,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f27,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tops_1(X1,X0)
            <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f27])).

fof(f50,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_1(X1,X0)
          <~> k1_xboole_0 = k1_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f54,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k1_xboole_0 != k1_tops_1(X0,X1)
            | ~ v2_tops_1(X1,X0) )
          & ( k1_xboole_0 = k1_tops_1(X0,X1)
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f50])).

fof(f55,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k1_xboole_0 != k1_tops_1(X0,X1)
            | ~ v2_tops_1(X1,X0) )
          & ( k1_xboole_0 = k1_tops_1(X0,X1)
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f54])).

fof(f57,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( k1_xboole_0 != k1_tops_1(X0,X1)
            | ~ v2_tops_1(X1,X0) )
          & ( k1_xboole_0 = k1_tops_1(X0,X1)
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( k1_xboole_0 != k1_tops_1(X0,sK1)
          | ~ v2_tops_1(sK1,X0) )
        & ( k1_xboole_0 = k1_tops_1(X0,sK1)
          | v2_tops_1(sK1,X0) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k1_xboole_0 != k1_tops_1(X0,X1)
              | ~ v2_tops_1(X1,X0) )
            & ( k1_xboole_0 = k1_tops_1(X0,X1)
              | v2_tops_1(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k1_xboole_0 != k1_tops_1(sK0,X1)
            | ~ v2_tops_1(X1,sK0) )
          & ( k1_xboole_0 = k1_tops_1(sK0,X1)
            | v2_tops_1(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,
    ( ( k1_xboole_0 != k1_tops_1(sK0,sK1)
      | ~ v2_tops_1(sK1,sK0) )
    & ( k1_xboole_0 = k1_tops_1(sK0,sK1)
      | v2_tops_1(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f55,f57,f56])).

fof(f87,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f89,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f22,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f81,plain,(
    ! [X0,X1] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_pre_topc(X0,X1) = k2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_pre_topc(X0,X1) = k2_struct_0(X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_pre_topc(X0,X1) != k2_struct_0(X0) )
            & ( k2_pre_topc(X0,X1) = k2_struct_0(X0)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_struct_0(X0)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f88,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f58])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f69,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f75,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f14,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f60,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f24,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => v1_xboole_0(k1_tops_1(X0,k1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_tops_1(X0,k1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f84,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_tops_1(X0,k1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f26,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => k1_tops_1(X0,k1_struct_0(X0)) = k1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] :
      ( k1_tops_1(X0,k1_struct_0(X0)) = k1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f86,plain,(
    ! [X0] :
      ( k1_tops_1(X0,k1_struct_0(X0)) = k1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f9,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f13,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f8,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f91,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f71,f66])).

fof(f94,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f67,f91])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_xboole_0(X1)
           => v2_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tops_1(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tops_1(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f39])).

fof(f77,plain,(
    ! [X0,X1] :
      ( v2_tops_1(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f10,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f95,plain,(
    ! [X0] : m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f68,f91])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( k3_subset_1(X0,X1) = k3_subset_1(X0,X2)
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | k3_subset_1(X0,X1) != k3_subset_1(X0,X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | k3_subset_1(X0,X1) != k3_subset_1(X0,X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f35])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | k3_subset_1(X0,X1) != k3_subset_1(X0,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f90,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f82,plain,(
    ! [X0,X1] :
      ( v2_tops_1(X1,X0)
      | ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f80,plain,(
    ! [X0,X1] :
      ( v1_tops_1(X1,X0)
      | k2_pre_topc(X0,X1) != k2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1013,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_5054,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) != X0
    | k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k3_subset_1(u1_struct_0(sK0),k2_struct_0(sK0))
    | k3_subset_1(u1_struct_0(sK0),k2_struct_0(sK0)) != X0 ),
    inference(instantiation,[status(thm)],[c_1013])).

cnf(c_5055,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k3_subset_1(u1_struct_0(sK0),k2_struct_0(sK0))
    | k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) != k1_xboole_0
    | k3_subset_1(u1_struct_0(sK0),k2_struct_0(sK0)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5054])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_28,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_601,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_28])).

cnf(c_602,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_601])).

cnf(c_1521,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_602])).

cnf(c_4456,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_1521])).

cnf(c_26,negated_conjecture,
    ( v2_tops_1(sK1,sK0)
    | k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_217,plain,
    ( v2_tops_1(sK1,sK0)
    | k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    inference(prop_impl,[status(thm)],[c_26])).

cnf(c_20,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
    | ~ v2_tops_1(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_490,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
    | ~ v2_tops_1(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_28])).

cnf(c_491,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(sK0),X0),sK0)
    | ~ v2_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_490])).

cnf(c_18,plain,
    ( ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = k2_struct_0(X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_544,plain,
    ( ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,X0) = k2_struct_0(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_28])).

cnf(c_545,plain,
    ( ~ v1_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,X0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_544])).

cnf(c_683,plain,
    ( ~ v2_tops_1(X0,sK0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,X1) = k2_struct_0(sK0)
    | k3_subset_1(u1_struct_0(sK0),X0) != X1
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_491,c_545])).

cnf(c_684,plain,
    ( ~ v2_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_683])).

cnf(c_729,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,sK1) = k1_xboole_0
    | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k2_struct_0(sK0)
    | sK1 != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_217,c_684])).

cnf(c_730,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,sK1) = k1_xboole_0
    | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_729])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_732,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,sK1) = k1_xboole_0
    | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_730,c_27])).

cnf(c_1448,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0
    | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_struct_0(sK0)
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_732])).

cnf(c_30,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_734,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0
    | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_struct_0(sK0)
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_732])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_12,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_213,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_12])).

cnf(c_214,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_213])).

cnf(c_264,plain,
    ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
    | ~ r1_tarski(X1,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_8,c_214])).

cnf(c_1633,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_264])).

cnf(c_1805,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1633])).

cnf(c_1806,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | r1_tarski(sK1,u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1805])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1640,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(X0,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1895,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1640])).

cnf(c_1898,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1895])).

cnf(c_2441,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_struct_0(sK0)
    | k1_tops_1(sK0,sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1448,c_30,c_734,c_1806,c_1898])).

cnf(c_2442,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0
    | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_struct_0(sK0) ),
    inference(renaming,[status(thm)],[c_2441])).

cnf(c_1455,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_574,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_28])).

cnf(c_575,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_574])).

cnf(c_1450,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_575])).

cnf(c_1763,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k1_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_1455,c_1450])).

cnf(c_2445,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0
    | k3_subset_1(u1_struct_0(sK0),k2_struct_0(sK0)) = k1_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_2442,c_1763])).

cnf(c_10,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1458,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1800,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k1_xboole_0))) = k1_tops_1(sK0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1458,c_1450])).

cnf(c_2,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_22,plain,
    ( ~ l1_pre_topc(X0)
    | v1_xboole_0(k1_tops_1(X0,k1_struct_0(X0))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_483,plain,
    ( v1_xboole_0(k1_tops_1(X0,k1_struct_0(X0)))
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_28])).

cnf(c_484,plain,
    ( v1_xboole_0(k1_tops_1(sK0,k1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_483])).

cnf(c_670,plain,
    ( k1_tops_1(sK0,k1_struct_0(sK0)) != X0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_484])).

cnf(c_671,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,k1_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_670])).

cnf(c_24,plain,
    ( ~ l1_pre_topc(X0)
    | k1_tops_1(X0,k1_struct_0(X0)) = k1_struct_0(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_478,plain,
    ( k1_tops_1(X0,k1_struct_0(X0)) = k1_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_28])).

cnf(c_479,plain,
    ( k1_tops_1(sK0,k1_struct_0(sK0)) = k1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_478])).

cnf(c_1462,plain,
    ( k1_struct_0(sK0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_479,c_671])).

cnf(c_1638,plain,
    ( k1_tops_1(sK0,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_671,c_671,c_1462])).

cnf(c_1803,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k1_xboole_0))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1800,c_1638])).

cnf(c_6,plain,
    ( k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_15,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_586,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_xboole_0(X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_28])).

cnf(c_587,plain,
    ( v2_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_586])).

cnf(c_648,plain,
    ( v2_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_587])).

cnf(c_649,plain,
    ( v2_tops_1(k1_xboole_0,sK0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_648])).

cnf(c_655,plain,
    ( v2_tops_1(k1_xboole_0,sK0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_649,c_10])).

cnf(c_788,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k2_struct_0(sK0)
    | sK0 != sK0
    | k1_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_684,c_655])).

cnf(c_789,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k1_xboole_0)) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_788])).

cnf(c_7,plain,
    ( m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_797,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k1_xboole_0)) = k2_struct_0(sK0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_789,c_10,c_7])).

cnf(c_1464,plain,
    ( k2_pre_topc(sK0,u1_struct_0(sK0)) = k2_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_797,c_6])).

cnf(c_1804,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_struct_0(sK0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1803,c_6,c_1464])).

cnf(c_2446,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2445,c_1804])).

cnf(c_3904,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2446,c_1763])).

cnf(c_3323,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1640])).

cnf(c_2569,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k2_struct_0(sK0),u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1640])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | X2 = X0
    | k3_subset_1(X1,X2) != k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_266,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,X1)
    | X0 = X2
    | k3_subset_1(X1,X0) != k3_subset_1(X1,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_11,c_214])).

cnf(c_899,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_12])).

cnf(c_900,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_899])).

cnf(c_940,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | X0 = X2
    | k3_subset_1(X1,X0) != k3_subset_1(X1,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_266,c_900])).

cnf(c_2279,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),X0)
    | ~ r1_tarski(k2_struct_0(sK0),X0)
    | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_struct_0(sK0)
    | k3_subset_1(X0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) != k3_subset_1(X0,k2_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_940])).

cnf(c_2567,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0))
    | ~ r1_tarski(k2_struct_0(sK0),u1_struct_0(sK0))
    | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_struct_0(sK0)
    | k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) != k3_subset_1(u1_struct_0(sK0),k2_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_2279])).

cnf(c_1459,plain,
    ( m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1463,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1459,c_6])).

cnf(c_1449,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_602])).

cnf(c_2109,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1464,c_1449])).

cnf(c_2287,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1463,c_2109])).

cnf(c_2288,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2287])).

cnf(c_25,negated_conjecture,
    ( ~ v2_tops_1(sK1,sK0)
    | k1_xboole_0 != k1_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_215,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | k1_xboole_0 != k1_tops_1(sK0,sK1) ),
    inference(prop_impl,[status(thm)],[c_25])).

cnf(c_19,plain,
    ( ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
    | v2_tops_1(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_505,plain,
    ( ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
    | v2_tops_1(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_28])).

cnf(c_506,plain,
    ( ~ v1_tops_1(k3_subset_1(u1_struct_0(sK0),X0),sK0)
    | v2_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_505])).

cnf(c_17,plain,
    ( v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) != k2_struct_0(X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_559,plain,
    ( v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,X0) != k2_struct_0(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_28])).

cnf(c_560,plain,
    ( v1_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,X0) != k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_559])).

cnf(c_701,plain,
    ( v2_tops_1(X0,sK0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,X1) != k2_struct_0(sK0)
    | k3_subset_1(u1_struct_0(sK0),X0) != X1
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_506,c_560])).

cnf(c_702,plain,
    ( v2_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)) != k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_701])).

cnf(c_746,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,sK1) != k1_xboole_0
    | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)) != k2_struct_0(sK0)
    | sK1 != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_215,c_702])).

cnf(c_747,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,sK1) != k1_xboole_0
    | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) != k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_746])).

cnf(c_748,plain,
    ( k1_tops_1(sK0,sK1) != k1_xboole_0
    | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) != k2_struct_0(sK0)
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_747])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5055,c_4456,c_3904,c_3323,c_2569,c_2567,c_2446,c_2288,c_1898,c_1895,c_1806,c_1805,c_1804,c_748,c_30,c_27])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n011.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:13:57 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.70/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.70/0.99  
% 3.70/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.70/0.99  
% 3.70/0.99  ------  iProver source info
% 3.70/0.99  
% 3.70/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.70/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.70/0.99  git: non_committed_changes: false
% 3.70/0.99  git: last_make_outside_of_git: false
% 3.70/0.99  
% 3.70/0.99  ------ 
% 3.70/0.99  
% 3.70/0.99  ------ Input Options
% 3.70/0.99  
% 3.70/0.99  --out_options                           all
% 3.70/0.99  --tptp_safe_out                         true
% 3.70/0.99  --problem_path                          ""
% 3.70/0.99  --include_path                          ""
% 3.70/0.99  --clausifier                            res/vclausify_rel
% 3.70/0.99  --clausifier_options                    ""
% 3.70/0.99  --stdin                                 false
% 3.70/0.99  --stats_out                             all
% 3.70/0.99  
% 3.70/0.99  ------ General Options
% 3.70/0.99  
% 3.70/0.99  --fof                                   false
% 3.70/0.99  --time_out_real                         305.
% 3.70/0.99  --time_out_virtual                      -1.
% 3.70/0.99  --symbol_type_check                     false
% 3.70/0.99  --clausify_out                          false
% 3.70/0.99  --sig_cnt_out                           false
% 3.70/0.99  --trig_cnt_out                          false
% 3.70/0.99  --trig_cnt_out_tolerance                1.
% 3.70/0.99  --trig_cnt_out_sk_spl                   false
% 3.70/0.99  --abstr_cl_out                          false
% 3.70/0.99  
% 3.70/0.99  ------ Global Options
% 3.70/0.99  
% 3.70/0.99  --schedule                              default
% 3.70/0.99  --add_important_lit                     false
% 3.70/0.99  --prop_solver_per_cl                    1000
% 3.70/0.99  --min_unsat_core                        false
% 3.70/0.99  --soft_assumptions                      false
% 3.70/0.99  --soft_lemma_size                       3
% 3.70/0.99  --prop_impl_unit_size                   0
% 3.70/0.99  --prop_impl_unit                        []
% 3.70/0.99  --share_sel_clauses                     true
% 3.70/0.99  --reset_solvers                         false
% 3.70/0.99  --bc_imp_inh                            [conj_cone]
% 3.70/0.99  --conj_cone_tolerance                   3.
% 3.70/0.99  --extra_neg_conj                        none
% 3.70/0.99  --large_theory_mode                     true
% 3.70/0.99  --prolific_symb_bound                   200
% 3.70/0.99  --lt_threshold                          2000
% 3.70/0.99  --clause_weak_htbl                      true
% 3.70/0.99  --gc_record_bc_elim                     false
% 3.70/0.99  
% 3.70/0.99  ------ Preprocessing Options
% 3.70/0.99  
% 3.70/0.99  --preprocessing_flag                    true
% 3.70/0.99  --time_out_prep_mult                    0.1
% 3.70/0.99  --splitting_mode                        input
% 3.70/0.99  --splitting_grd                         true
% 3.70/0.99  --splitting_cvd                         false
% 3.70/0.99  --splitting_cvd_svl                     false
% 3.70/0.99  --splitting_nvd                         32
% 3.70/0.99  --sub_typing                            true
% 3.70/0.99  --prep_gs_sim                           true
% 3.70/0.99  --prep_unflatten                        true
% 3.70/0.99  --prep_res_sim                          true
% 3.70/0.99  --prep_upred                            true
% 3.70/0.99  --prep_sem_filter                       exhaustive
% 3.70/0.99  --prep_sem_filter_out                   false
% 3.70/0.99  --pred_elim                             true
% 3.70/0.99  --res_sim_input                         true
% 3.70/0.99  --eq_ax_congr_red                       true
% 3.70/0.99  --pure_diseq_elim                       true
% 3.70/0.99  --brand_transform                       false
% 3.70/0.99  --non_eq_to_eq                          false
% 3.70/0.99  --prep_def_merge                        true
% 3.70/0.99  --prep_def_merge_prop_impl              false
% 3.70/0.99  --prep_def_merge_mbd                    true
% 3.70/0.99  --prep_def_merge_tr_red                 false
% 3.70/0.99  --prep_def_merge_tr_cl                  false
% 3.70/0.99  --smt_preprocessing                     true
% 3.70/0.99  --smt_ac_axioms                         fast
% 3.70/0.99  --preprocessed_out                      false
% 3.70/0.99  --preprocessed_stats                    false
% 3.70/0.99  
% 3.70/0.99  ------ Abstraction refinement Options
% 3.70/0.99  
% 3.70/0.99  --abstr_ref                             []
% 3.70/0.99  --abstr_ref_prep                        false
% 3.70/0.99  --abstr_ref_until_sat                   false
% 3.70/0.99  --abstr_ref_sig_restrict                funpre
% 3.70/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.70/0.99  --abstr_ref_under                       []
% 3.70/0.99  
% 3.70/0.99  ------ SAT Options
% 3.70/0.99  
% 3.70/0.99  --sat_mode                              false
% 3.70/0.99  --sat_fm_restart_options                ""
% 3.70/0.99  --sat_gr_def                            false
% 3.70/0.99  --sat_epr_types                         true
% 3.70/0.99  --sat_non_cyclic_types                  false
% 3.70/0.99  --sat_finite_models                     false
% 3.70/0.99  --sat_fm_lemmas                         false
% 3.70/0.99  --sat_fm_prep                           false
% 3.70/0.99  --sat_fm_uc_incr                        true
% 3.70/0.99  --sat_out_model                         small
% 3.70/0.99  --sat_out_clauses                       false
% 3.70/0.99  
% 3.70/0.99  ------ QBF Options
% 3.70/0.99  
% 3.70/0.99  --qbf_mode                              false
% 3.70/0.99  --qbf_elim_univ                         false
% 3.70/0.99  --qbf_dom_inst                          none
% 3.70/0.99  --qbf_dom_pre_inst                      false
% 3.70/0.99  --qbf_sk_in                             false
% 3.70/0.99  --qbf_pred_elim                         true
% 3.70/0.99  --qbf_split                             512
% 3.70/0.99  
% 3.70/0.99  ------ BMC1 Options
% 3.70/0.99  
% 3.70/0.99  --bmc1_incremental                      false
% 3.70/0.99  --bmc1_axioms                           reachable_all
% 3.70/0.99  --bmc1_min_bound                        0
% 3.70/0.99  --bmc1_max_bound                        -1
% 3.70/0.99  --bmc1_max_bound_default                -1
% 3.70/0.99  --bmc1_symbol_reachability              true
% 3.70/0.99  --bmc1_property_lemmas                  false
% 3.70/0.99  --bmc1_k_induction                      false
% 3.70/0.99  --bmc1_non_equiv_states                 false
% 3.70/0.99  --bmc1_deadlock                         false
% 3.70/0.99  --bmc1_ucm                              false
% 3.70/0.99  --bmc1_add_unsat_core                   none
% 3.70/0.99  --bmc1_unsat_core_children              false
% 3.70/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.70/0.99  --bmc1_out_stat                         full
% 3.70/0.99  --bmc1_ground_init                      false
% 3.70/0.99  --bmc1_pre_inst_next_state              false
% 3.70/0.99  --bmc1_pre_inst_state                   false
% 3.70/0.99  --bmc1_pre_inst_reach_state             false
% 3.70/0.99  --bmc1_out_unsat_core                   false
% 3.70/0.99  --bmc1_aig_witness_out                  false
% 3.70/0.99  --bmc1_verbose                          false
% 3.70/0.99  --bmc1_dump_clauses_tptp                false
% 3.70/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.70/0.99  --bmc1_dump_file                        -
% 3.70/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.70/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.70/0.99  --bmc1_ucm_extend_mode                  1
% 3.70/0.99  --bmc1_ucm_init_mode                    2
% 3.70/0.99  --bmc1_ucm_cone_mode                    none
% 3.70/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.70/0.99  --bmc1_ucm_relax_model                  4
% 3.70/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.70/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.70/0.99  --bmc1_ucm_layered_model                none
% 3.70/0.99  --bmc1_ucm_max_lemma_size               10
% 3.70/0.99  
% 3.70/0.99  ------ AIG Options
% 3.70/0.99  
% 3.70/0.99  --aig_mode                              false
% 3.70/0.99  
% 3.70/0.99  ------ Instantiation Options
% 3.70/0.99  
% 3.70/0.99  --instantiation_flag                    true
% 3.70/0.99  --inst_sos_flag                         true
% 3.70/0.99  --inst_sos_phase                        true
% 3.70/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.70/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.70/0.99  --inst_lit_sel_side                     num_symb
% 3.70/0.99  --inst_solver_per_active                1400
% 3.70/0.99  --inst_solver_calls_frac                1.
% 3.70/0.99  --inst_passive_queue_type               priority_queues
% 3.70/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.70/0.99  --inst_passive_queues_freq              [25;2]
% 3.70/0.99  --inst_dismatching                      true
% 3.70/0.99  --inst_eager_unprocessed_to_passive     true
% 3.70/0.99  --inst_prop_sim_given                   true
% 3.70/0.99  --inst_prop_sim_new                     false
% 3.70/0.99  --inst_subs_new                         false
% 3.70/0.99  --inst_eq_res_simp                      false
% 3.70/0.99  --inst_subs_given                       false
% 3.70/0.99  --inst_orphan_elimination               true
% 3.70/0.99  --inst_learning_loop_flag               true
% 3.70/0.99  --inst_learning_start                   3000
% 3.70/0.99  --inst_learning_factor                  2
% 3.70/0.99  --inst_start_prop_sim_after_learn       3
% 3.70/0.99  --inst_sel_renew                        solver
% 3.70/0.99  --inst_lit_activity_flag                true
% 3.70/0.99  --inst_restr_to_given                   false
% 3.70/0.99  --inst_activity_threshold               500
% 3.70/0.99  --inst_out_proof                        true
% 3.70/0.99  
% 3.70/0.99  ------ Resolution Options
% 3.70/0.99  
% 3.70/0.99  --resolution_flag                       true
% 3.70/0.99  --res_lit_sel                           adaptive
% 3.70/0.99  --res_lit_sel_side                      none
% 3.70/0.99  --res_ordering                          kbo
% 3.70/0.99  --res_to_prop_solver                    active
% 3.70/0.99  --res_prop_simpl_new                    false
% 3.70/0.99  --res_prop_simpl_given                  true
% 3.70/0.99  --res_passive_queue_type                priority_queues
% 3.70/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.70/0.99  --res_passive_queues_freq               [15;5]
% 3.70/0.99  --res_forward_subs                      full
% 3.70/0.99  --res_backward_subs                     full
% 3.70/0.99  --res_forward_subs_resolution           true
% 3.70/0.99  --res_backward_subs_resolution          true
% 3.70/0.99  --res_orphan_elimination                true
% 3.70/0.99  --res_time_limit                        2.
% 3.70/0.99  --res_out_proof                         true
% 3.70/0.99  
% 3.70/0.99  ------ Superposition Options
% 3.70/0.99  
% 3.70/0.99  --superposition_flag                    true
% 3.70/0.99  --sup_passive_queue_type                priority_queues
% 3.70/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.70/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.70/0.99  --demod_completeness_check              fast
% 3.70/0.99  --demod_use_ground                      true
% 3.70/0.99  --sup_to_prop_solver                    passive
% 3.70/0.99  --sup_prop_simpl_new                    true
% 3.70/0.99  --sup_prop_simpl_given                  true
% 3.70/0.99  --sup_fun_splitting                     true
% 3.70/0.99  --sup_smt_interval                      50000
% 3.70/0.99  
% 3.70/0.99  ------ Superposition Simplification Setup
% 3.70/0.99  
% 3.70/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.70/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.70/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.70/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.70/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.70/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.70/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.70/0.99  --sup_immed_triv                        [TrivRules]
% 3.70/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.70/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.70/0.99  --sup_immed_bw_main                     []
% 3.70/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.70/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.70/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.70/0.99  --sup_input_bw                          []
% 3.70/0.99  
% 3.70/0.99  ------ Combination Options
% 3.70/0.99  
% 3.70/0.99  --comb_res_mult                         3
% 3.70/0.99  --comb_sup_mult                         2
% 3.70/0.99  --comb_inst_mult                        10
% 3.70/0.99  
% 3.70/0.99  ------ Debug Options
% 3.70/0.99  
% 3.70/0.99  --dbg_backtrace                         false
% 3.70/0.99  --dbg_dump_prop_clauses                 false
% 3.70/0.99  --dbg_dump_prop_clauses_file            -
% 3.70/0.99  --dbg_out_stat                          false
% 3.70/0.99  ------ Parsing...
% 3.70/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.70/0.99  
% 3.70/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 3.70/0.99  
% 3.70/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.70/0.99  
% 3.70/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.70/0.99  ------ Proving...
% 3.70/0.99  ------ Problem Properties 
% 3.70/0.99  
% 3.70/0.99  
% 3.70/0.99  clauses                                 25
% 3.70/0.99  conjectures                             1
% 3.70/0.99  EPR                                     1
% 3.70/0.99  Horn                                    24
% 3.70/0.99  unary                                   10
% 3.70/0.99  binary                                  9
% 3.70/0.99  lits                                    47
% 3.70/0.99  lits eq                                 20
% 3.70/0.99  fd_pure                                 0
% 3.70/0.99  fd_pseudo                               0
% 3.70/0.99  fd_cond                                 0
% 3.70/0.99  fd_pseudo_cond                          1
% 3.70/0.99  AC symbols                              0
% 3.70/0.99  
% 3.70/0.99  ------ Schedule dynamic 5 is on 
% 3.70/0.99  
% 3.70/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.70/0.99  
% 3.70/0.99  
% 3.70/0.99  ------ 
% 3.70/0.99  Current options:
% 3.70/0.99  ------ 
% 3.70/0.99  
% 3.70/0.99  ------ Input Options
% 3.70/0.99  
% 3.70/0.99  --out_options                           all
% 3.70/0.99  --tptp_safe_out                         true
% 3.70/0.99  --problem_path                          ""
% 3.70/0.99  --include_path                          ""
% 3.70/0.99  --clausifier                            res/vclausify_rel
% 3.70/0.99  --clausifier_options                    ""
% 3.70/0.99  --stdin                                 false
% 3.70/0.99  --stats_out                             all
% 3.70/0.99  
% 3.70/0.99  ------ General Options
% 3.70/0.99  
% 3.70/0.99  --fof                                   false
% 3.70/0.99  --time_out_real                         305.
% 3.70/0.99  --time_out_virtual                      -1.
% 3.70/0.99  --symbol_type_check                     false
% 3.70/0.99  --clausify_out                          false
% 3.70/0.99  --sig_cnt_out                           false
% 3.70/0.99  --trig_cnt_out                          false
% 3.70/0.99  --trig_cnt_out_tolerance                1.
% 3.70/0.99  --trig_cnt_out_sk_spl                   false
% 3.70/0.99  --abstr_cl_out                          false
% 3.70/0.99  
% 3.70/0.99  ------ Global Options
% 3.70/0.99  
% 3.70/0.99  --schedule                              default
% 3.70/0.99  --add_important_lit                     false
% 3.70/0.99  --prop_solver_per_cl                    1000
% 3.70/0.99  --min_unsat_core                        false
% 3.70/0.99  --soft_assumptions                      false
% 3.70/0.99  --soft_lemma_size                       3
% 3.70/0.99  --prop_impl_unit_size                   0
% 3.70/0.99  --prop_impl_unit                        []
% 3.70/0.99  --share_sel_clauses                     true
% 3.70/0.99  --reset_solvers                         false
% 3.70/0.99  --bc_imp_inh                            [conj_cone]
% 3.70/0.99  --conj_cone_tolerance                   3.
% 3.70/0.99  --extra_neg_conj                        none
% 3.70/0.99  --large_theory_mode                     true
% 3.70/0.99  --prolific_symb_bound                   200
% 3.70/0.99  --lt_threshold                          2000
% 3.70/0.99  --clause_weak_htbl                      true
% 3.70/0.99  --gc_record_bc_elim                     false
% 3.70/0.99  
% 3.70/0.99  ------ Preprocessing Options
% 3.70/0.99  
% 3.70/0.99  --preprocessing_flag                    true
% 3.70/0.99  --time_out_prep_mult                    0.1
% 3.70/0.99  --splitting_mode                        input
% 3.70/0.99  --splitting_grd                         true
% 3.70/0.99  --splitting_cvd                         false
% 3.70/0.99  --splitting_cvd_svl                     false
% 3.70/0.99  --splitting_nvd                         32
% 3.70/0.99  --sub_typing                            true
% 3.70/0.99  --prep_gs_sim                           true
% 3.70/0.99  --prep_unflatten                        true
% 3.70/0.99  --prep_res_sim                          true
% 3.70/0.99  --prep_upred                            true
% 3.70/0.99  --prep_sem_filter                       exhaustive
% 3.70/0.99  --prep_sem_filter_out                   false
% 3.70/0.99  --pred_elim                             true
% 3.70/0.99  --res_sim_input                         true
% 3.70/0.99  --eq_ax_congr_red                       true
% 3.70/0.99  --pure_diseq_elim                       true
% 3.70/0.99  --brand_transform                       false
% 3.70/0.99  --non_eq_to_eq                          false
% 3.70/0.99  --prep_def_merge                        true
% 3.70/0.99  --prep_def_merge_prop_impl              false
% 3.70/0.99  --prep_def_merge_mbd                    true
% 3.70/0.99  --prep_def_merge_tr_red                 false
% 3.70/0.99  --prep_def_merge_tr_cl                  false
% 3.70/0.99  --smt_preprocessing                     true
% 3.70/0.99  --smt_ac_axioms                         fast
% 3.70/0.99  --preprocessed_out                      false
% 3.70/0.99  --preprocessed_stats                    false
% 3.70/0.99  
% 3.70/0.99  ------ Abstraction refinement Options
% 3.70/0.99  
% 3.70/0.99  --abstr_ref                             []
% 3.70/0.99  --abstr_ref_prep                        false
% 3.70/0.99  --abstr_ref_until_sat                   false
% 3.70/0.99  --abstr_ref_sig_restrict                funpre
% 3.70/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.70/0.99  --abstr_ref_under                       []
% 3.70/0.99  
% 3.70/0.99  ------ SAT Options
% 3.70/0.99  
% 3.70/0.99  --sat_mode                              false
% 3.70/0.99  --sat_fm_restart_options                ""
% 3.70/0.99  --sat_gr_def                            false
% 3.70/0.99  --sat_epr_types                         true
% 3.70/0.99  --sat_non_cyclic_types                  false
% 3.70/0.99  --sat_finite_models                     false
% 3.70/0.99  --sat_fm_lemmas                         false
% 3.70/0.99  --sat_fm_prep                           false
% 3.70/0.99  --sat_fm_uc_incr                        true
% 3.70/0.99  --sat_out_model                         small
% 3.70/0.99  --sat_out_clauses                       false
% 3.70/0.99  
% 3.70/0.99  ------ QBF Options
% 3.70/0.99  
% 3.70/0.99  --qbf_mode                              false
% 3.70/0.99  --qbf_elim_univ                         false
% 3.70/0.99  --qbf_dom_inst                          none
% 3.70/0.99  --qbf_dom_pre_inst                      false
% 3.70/0.99  --qbf_sk_in                             false
% 3.70/0.99  --qbf_pred_elim                         true
% 3.70/0.99  --qbf_split                             512
% 3.70/0.99  
% 3.70/0.99  ------ BMC1 Options
% 3.70/0.99  
% 3.70/0.99  --bmc1_incremental                      false
% 3.70/0.99  --bmc1_axioms                           reachable_all
% 3.70/0.99  --bmc1_min_bound                        0
% 3.70/0.99  --bmc1_max_bound                        -1
% 3.70/0.99  --bmc1_max_bound_default                -1
% 3.70/0.99  --bmc1_symbol_reachability              true
% 3.70/0.99  --bmc1_property_lemmas                  false
% 3.70/0.99  --bmc1_k_induction                      false
% 3.70/0.99  --bmc1_non_equiv_states                 false
% 3.70/0.99  --bmc1_deadlock                         false
% 3.70/0.99  --bmc1_ucm                              false
% 3.70/0.99  --bmc1_add_unsat_core                   none
% 3.70/0.99  --bmc1_unsat_core_children              false
% 3.70/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.70/0.99  --bmc1_out_stat                         full
% 3.70/0.99  --bmc1_ground_init                      false
% 3.70/0.99  --bmc1_pre_inst_next_state              false
% 3.70/0.99  --bmc1_pre_inst_state                   false
% 3.70/0.99  --bmc1_pre_inst_reach_state             false
% 3.70/0.99  --bmc1_out_unsat_core                   false
% 3.70/0.99  --bmc1_aig_witness_out                  false
% 3.70/0.99  --bmc1_verbose                          false
% 3.70/0.99  --bmc1_dump_clauses_tptp                false
% 3.70/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.70/0.99  --bmc1_dump_file                        -
% 3.70/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.70/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.70/0.99  --bmc1_ucm_extend_mode                  1
% 3.70/0.99  --bmc1_ucm_init_mode                    2
% 3.70/0.99  --bmc1_ucm_cone_mode                    none
% 3.70/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.70/0.99  --bmc1_ucm_relax_model                  4
% 3.70/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.70/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.70/0.99  --bmc1_ucm_layered_model                none
% 3.70/0.99  --bmc1_ucm_max_lemma_size               10
% 3.70/0.99  
% 3.70/0.99  ------ AIG Options
% 3.70/0.99  
% 3.70/0.99  --aig_mode                              false
% 3.70/0.99  
% 3.70/0.99  ------ Instantiation Options
% 3.70/0.99  
% 3.70/0.99  --instantiation_flag                    true
% 3.70/0.99  --inst_sos_flag                         true
% 3.70/0.99  --inst_sos_phase                        true
% 3.70/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.70/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.70/0.99  --inst_lit_sel_side                     none
% 3.70/0.99  --inst_solver_per_active                1400
% 3.70/0.99  --inst_solver_calls_frac                1.
% 3.70/0.99  --inst_passive_queue_type               priority_queues
% 3.70/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.70/0.99  --inst_passive_queues_freq              [25;2]
% 3.70/0.99  --inst_dismatching                      true
% 3.70/0.99  --inst_eager_unprocessed_to_passive     true
% 3.70/0.99  --inst_prop_sim_given                   true
% 3.70/0.99  --inst_prop_sim_new                     false
% 3.70/0.99  --inst_subs_new                         false
% 3.70/0.99  --inst_eq_res_simp                      false
% 3.70/0.99  --inst_subs_given                       false
% 3.70/0.99  --inst_orphan_elimination               true
% 3.70/0.99  --inst_learning_loop_flag               true
% 3.70/0.99  --inst_learning_start                   3000
% 3.70/0.99  --inst_learning_factor                  2
% 3.70/0.99  --inst_start_prop_sim_after_learn       3
% 3.70/0.99  --inst_sel_renew                        solver
% 3.70/0.99  --inst_lit_activity_flag                true
% 3.70/0.99  --inst_restr_to_given                   false
% 3.70/0.99  --inst_activity_threshold               500
% 3.70/0.99  --inst_out_proof                        true
% 3.70/0.99  
% 3.70/0.99  ------ Resolution Options
% 3.70/0.99  
% 3.70/0.99  --resolution_flag                       false
% 3.70/0.99  --res_lit_sel                           adaptive
% 3.70/0.99  --res_lit_sel_side                      none
% 3.70/0.99  --res_ordering                          kbo
% 3.70/0.99  --res_to_prop_solver                    active
% 3.70/0.99  --res_prop_simpl_new                    false
% 3.70/0.99  --res_prop_simpl_given                  true
% 3.70/0.99  --res_passive_queue_type                priority_queues
% 3.70/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.70/0.99  --res_passive_queues_freq               [15;5]
% 3.70/0.99  --res_forward_subs                      full
% 3.70/0.99  --res_backward_subs                     full
% 3.70/0.99  --res_forward_subs_resolution           true
% 3.70/0.99  --res_backward_subs_resolution          true
% 3.70/0.99  --res_orphan_elimination                true
% 3.70/0.99  --res_time_limit                        2.
% 3.70/0.99  --res_out_proof                         true
% 3.70/0.99  
% 3.70/0.99  ------ Superposition Options
% 3.70/0.99  
% 3.70/0.99  --superposition_flag                    true
% 3.70/0.99  --sup_passive_queue_type                priority_queues
% 3.70/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.70/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.70/0.99  --demod_completeness_check              fast
% 3.70/0.99  --demod_use_ground                      true
% 3.70/0.99  --sup_to_prop_solver                    passive
% 3.70/0.99  --sup_prop_simpl_new                    true
% 3.70/0.99  --sup_prop_simpl_given                  true
% 3.70/0.99  --sup_fun_splitting                     true
% 3.70/0.99  --sup_smt_interval                      50000
% 3.70/0.99  
% 3.70/0.99  ------ Superposition Simplification Setup
% 3.70/0.99  
% 3.70/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.70/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.70/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.70/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.70/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.70/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.70/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.70/0.99  --sup_immed_triv                        [TrivRules]
% 3.70/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.70/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.70/0.99  --sup_immed_bw_main                     []
% 3.70/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.70/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.70/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.70/0.99  --sup_input_bw                          []
% 3.70/0.99  
% 3.70/0.99  ------ Combination Options
% 3.70/0.99  
% 3.70/0.99  --comb_res_mult                         3
% 3.70/0.99  --comb_sup_mult                         2
% 3.70/0.99  --comb_inst_mult                        10
% 3.70/0.99  
% 3.70/0.99  ------ Debug Options
% 3.70/0.99  
% 3.70/0.99  --dbg_backtrace                         false
% 3.70/0.99  --dbg_dump_prop_clauses                 false
% 3.70/0.99  --dbg_dump_prop_clauses_file            -
% 3.70/0.99  --dbg_out_stat                          false
% 3.70/0.99  
% 3.70/0.99  
% 3.70/0.99  
% 3.70/0.99  
% 3.70/0.99  ------ Proving...
% 3.70/0.99  
% 3.70/0.99  
% 3.70/0.99  % SZS status Theorem for theBenchmark.p
% 3.70/0.99  
% 3.70/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.70/0.99  
% 3.70/0.99  fof(f18,axiom,(
% 3.70/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.70/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/0.99  
% 3.70/0.99  fof(f37,plain,(
% 3.70/0.99    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.70/0.99    inference(ennf_transformation,[],[f18])).
% 3.70/0.99  
% 3.70/0.99  fof(f38,plain,(
% 3.70/0.99    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.70/0.99    inference(flattening,[],[f37])).
% 3.70/0.99  
% 3.70/0.99  fof(f76,plain,(
% 3.70/0.99    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.70/0.99    inference(cnf_transformation,[],[f38])).
% 3.70/0.99  
% 3.70/0.99  fof(f27,conjecture,(
% 3.70/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 3.70/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/0.99  
% 3.70/0.99  fof(f28,negated_conjecture,(
% 3.70/0.99    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 3.70/0.99    inference(negated_conjecture,[],[f27])).
% 3.70/0.99  
% 3.70/0.99  fof(f50,plain,(
% 3.70/0.99    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> k1_xboole_0 = k1_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.70/0.99    inference(ennf_transformation,[],[f28])).
% 3.70/0.99  
% 3.70/0.99  fof(f54,plain,(
% 3.70/0.99    ? [X0] : (? [X1] : (((k1_xboole_0 != k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) & (k1_xboole_0 = k1_tops_1(X0,X1) | v2_tops_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.70/0.99    inference(nnf_transformation,[],[f50])).
% 3.70/0.99  
% 3.70/0.99  fof(f55,plain,(
% 3.70/0.99    ? [X0] : (? [X1] : ((k1_xboole_0 != k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) & (k1_xboole_0 = k1_tops_1(X0,X1) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.70/0.99    inference(flattening,[],[f54])).
% 3.70/0.99  
% 3.70/0.99  fof(f57,plain,(
% 3.70/0.99    ( ! [X0] : (? [X1] : ((k1_xboole_0 != k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) & (k1_xboole_0 = k1_tops_1(X0,X1) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((k1_xboole_0 != k1_tops_1(X0,sK1) | ~v2_tops_1(sK1,X0)) & (k1_xboole_0 = k1_tops_1(X0,sK1) | v2_tops_1(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.70/0.99    introduced(choice_axiom,[])).
% 3.70/0.99  
% 3.70/0.99  fof(f56,plain,(
% 3.70/0.99    ? [X0] : (? [X1] : ((k1_xboole_0 != k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) & (k1_xboole_0 = k1_tops_1(X0,X1) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((k1_xboole_0 != k1_tops_1(sK0,X1) | ~v2_tops_1(X1,sK0)) & (k1_xboole_0 = k1_tops_1(sK0,X1) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 3.70/0.99    introduced(choice_axiom,[])).
% 3.70/0.99  
% 3.70/0.99  fof(f58,plain,(
% 3.70/0.99    ((k1_xboole_0 != k1_tops_1(sK0,sK1) | ~v2_tops_1(sK1,sK0)) & (k1_xboole_0 = k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 3.70/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f55,f57,f56])).
% 3.70/0.99  
% 3.70/0.99  fof(f87,plain,(
% 3.70/0.99    l1_pre_topc(sK0)),
% 3.70/0.99    inference(cnf_transformation,[],[f58])).
% 3.70/0.99  
% 3.70/0.99  fof(f89,plain,(
% 3.70/0.99    k1_xboole_0 = k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0)),
% 3.70/0.99    inference(cnf_transformation,[],[f58])).
% 3.70/0.99  
% 3.70/0.99  fof(f22,axiom,(
% 3.70/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 3.70/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/0.99  
% 3.70/0.99  fof(f43,plain,(
% 3.70/0.99    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.70/0.99    inference(ennf_transformation,[],[f22])).
% 3.70/0.99  
% 3.70/0.99  fof(f53,plain,(
% 3.70/0.99    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | ~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.70/0.99    inference(nnf_transformation,[],[f43])).
% 3.70/0.99  
% 3.70/0.99  fof(f81,plain,(
% 3.70/0.99    ( ! [X0,X1] : (v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.70/0.99    inference(cnf_transformation,[],[f53])).
% 3.70/0.99  
% 3.70/0.99  fof(f21,axiom,(
% 3.70/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_pre_topc(X0,X1) = k2_struct_0(X0))))),
% 3.70/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/0.99  
% 3.70/0.99  fof(f42,plain,(
% 3.70/0.99    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_pre_topc(X0,X1) = k2_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.70/0.99    inference(ennf_transformation,[],[f21])).
% 3.70/0.99  
% 3.70/0.99  fof(f52,plain,(
% 3.70/0.99    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | k2_pre_topc(X0,X1) != k2_struct_0(X0)) & (k2_pre_topc(X0,X1) = k2_struct_0(X0) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.70/0.99    inference(nnf_transformation,[],[f42])).
% 3.70/0.99  
% 3.70/0.99  fof(f79,plain,(
% 3.70/0.99    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_struct_0(X0) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.70/0.99    inference(cnf_transformation,[],[f52])).
% 3.70/0.99  
% 3.70/0.99  fof(f88,plain,(
% 3.70/0.99    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.70/0.99    inference(cnf_transformation,[],[f58])).
% 3.70/0.99  
% 3.70/0.99  fof(f11,axiom,(
% 3.70/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 3.70/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/0.99  
% 3.70/0.99  fof(f33,plain,(
% 3.70/0.99    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.70/0.99    inference(ennf_transformation,[],[f11])).
% 3.70/0.99  
% 3.70/0.99  fof(f69,plain,(
% 3.70/0.99    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.70/0.99    inference(cnf_transformation,[],[f33])).
% 3.70/0.99  
% 3.70/0.99  fof(f16,axiom,(
% 3.70/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.70/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/0.99  
% 3.70/0.99  fof(f51,plain,(
% 3.70/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.70/0.99    inference(nnf_transformation,[],[f16])).
% 3.70/0.99  
% 3.70/0.99  fof(f75,plain,(
% 3.70/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.70/0.99    inference(cnf_transformation,[],[f51])).
% 3.70/0.99  
% 3.70/0.99  fof(f74,plain,(
% 3.70/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.70/0.99    inference(cnf_transformation,[],[f51])).
% 3.70/0.99  
% 3.70/0.99  fof(f20,axiom,(
% 3.70/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)))),
% 3.70/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/0.99  
% 3.70/0.99  fof(f41,plain,(
% 3.70/0.99    ! [X0] : (! [X1] : (k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.70/0.99    inference(ennf_transformation,[],[f20])).
% 3.70/0.99  
% 3.70/0.99  fof(f78,plain,(
% 3.70/0.99    ( ! [X0,X1] : (k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.70/0.99    inference(cnf_transformation,[],[f41])).
% 3.70/0.99  
% 3.70/0.99  fof(f14,axiom,(
% 3.70/0.99    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.70/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/0.99  
% 3.70/0.99  fof(f72,plain,(
% 3.70/0.99    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.70/0.99    inference(cnf_transformation,[],[f14])).
% 3.70/0.99  
% 3.70/0.99  fof(f2,axiom,(
% 3.70/0.99    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 3.70/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/0.99  
% 3.70/0.99  fof(f30,plain,(
% 3.70/0.99    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 3.70/0.99    inference(ennf_transformation,[],[f2])).
% 3.70/0.99  
% 3.70/0.99  fof(f60,plain,(
% 3.70/0.99    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 3.70/0.99    inference(cnf_transformation,[],[f30])).
% 3.70/0.99  
% 3.70/0.99  fof(f24,axiom,(
% 3.70/0.99    ! [X0] : (l1_pre_topc(X0) => v1_xboole_0(k1_tops_1(X0,k1_struct_0(X0))))),
% 3.70/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/0.99  
% 3.70/0.99  fof(f46,plain,(
% 3.70/0.99    ! [X0] : (v1_xboole_0(k1_tops_1(X0,k1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.70/0.99    inference(ennf_transformation,[],[f24])).
% 3.70/0.99  
% 3.70/0.99  fof(f84,plain,(
% 3.70/0.99    ( ! [X0] : (v1_xboole_0(k1_tops_1(X0,k1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.70/0.99    inference(cnf_transformation,[],[f46])).
% 3.70/0.99  
% 3.70/0.99  fof(f26,axiom,(
% 3.70/0.99    ! [X0] : (l1_pre_topc(X0) => k1_tops_1(X0,k1_struct_0(X0)) = k1_struct_0(X0))),
% 3.70/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/0.99  
% 3.70/0.99  fof(f49,plain,(
% 3.70/0.99    ! [X0] : (k1_tops_1(X0,k1_struct_0(X0)) = k1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.70/0.99    inference(ennf_transformation,[],[f26])).
% 3.70/0.99  
% 3.70/0.99  fof(f86,plain,(
% 3.70/0.99    ( ! [X0] : (k1_tops_1(X0,k1_struct_0(X0)) = k1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.70/0.99    inference(cnf_transformation,[],[f49])).
% 3.70/0.99  
% 3.70/0.99  fof(f9,axiom,(
% 3.70/0.99    ! [X0] : k2_subset_1(X0) = X0),
% 3.70/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/0.99  
% 3.70/0.99  fof(f67,plain,(
% 3.70/0.99    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 3.70/0.99    inference(cnf_transformation,[],[f9])).
% 3.70/0.99  
% 3.70/0.99  fof(f13,axiom,(
% 3.70/0.99    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 3.70/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/0.99  
% 3.70/0.99  fof(f71,plain,(
% 3.70/0.99    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 3.70/0.99    inference(cnf_transformation,[],[f13])).
% 3.70/0.99  
% 3.70/0.99  fof(f8,axiom,(
% 3.70/0.99    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 3.70/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/0.99  
% 3.70/0.99  fof(f66,plain,(
% 3.70/0.99    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 3.70/0.99    inference(cnf_transformation,[],[f8])).
% 3.70/0.99  
% 3.70/0.99  fof(f91,plain,(
% 3.70/0.99    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 3.70/0.99    inference(definition_unfolding,[],[f71,f66])).
% 3.70/0.99  
% 3.70/0.99  fof(f94,plain,(
% 3.70/0.99    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 3.70/0.99    inference(definition_unfolding,[],[f67,f91])).
% 3.70/0.99  
% 3.70/0.99  fof(f1,axiom,(
% 3.70/0.99    v1_xboole_0(k1_xboole_0)),
% 3.70/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/0.99  
% 3.70/0.99  fof(f59,plain,(
% 3.70/0.99    v1_xboole_0(k1_xboole_0)),
% 3.70/0.99    inference(cnf_transformation,[],[f1])).
% 3.70/0.99  
% 3.70/0.99  fof(f19,axiom,(
% 3.70/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_xboole_0(X1) => v2_tops_1(X1,X0))))),
% 3.70/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/0.99  
% 3.70/0.99  fof(f39,plain,(
% 3.70/0.99    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) | ~v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.70/0.99    inference(ennf_transformation,[],[f19])).
% 3.70/0.99  
% 3.70/0.99  fof(f40,plain,(
% 3.70/0.99    ! [X0] : (! [X1] : (v2_tops_1(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.70/0.99    inference(flattening,[],[f39])).
% 3.70/0.99  
% 3.70/0.99  fof(f77,plain,(
% 3.70/0.99    ( ! [X0,X1] : (v2_tops_1(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.70/0.99    inference(cnf_transformation,[],[f40])).
% 3.70/0.99  
% 3.70/0.99  fof(f10,axiom,(
% 3.70/0.99    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 3.70/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/0.99  
% 3.70/0.99  fof(f68,plain,(
% 3.70/0.99    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 3.70/0.99    inference(cnf_transformation,[],[f10])).
% 3.70/0.99  
% 3.70/0.99  fof(f95,plain,(
% 3.70/0.99    ( ! [X0] : (m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0))) )),
% 3.70/0.99    inference(definition_unfolding,[],[f68,f91])).
% 3.70/0.99  
% 3.70/0.99  fof(f15,axiom,(
% 3.70/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (k3_subset_1(X0,X1) = k3_subset_1(X0,X2) => X1 = X2)))),
% 3.70/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/0.99  
% 3.70/0.99  fof(f35,plain,(
% 3.70/0.99    ! [X0,X1] : (! [X2] : ((X1 = X2 | k3_subset_1(X0,X1) != k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.70/0.99    inference(ennf_transformation,[],[f15])).
% 3.70/0.99  
% 3.70/0.99  fof(f36,plain,(
% 3.70/0.99    ! [X0,X1] : (! [X2] : (X1 = X2 | k3_subset_1(X0,X1) != k3_subset_1(X0,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.70/0.99    inference(flattening,[],[f35])).
% 3.70/0.99  
% 3.70/0.99  fof(f73,plain,(
% 3.70/0.99    ( ! [X2,X0,X1] : (X1 = X2 | k3_subset_1(X0,X1) != k3_subset_1(X0,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.70/0.99    inference(cnf_transformation,[],[f36])).
% 3.70/0.99  
% 3.70/0.99  fof(f90,plain,(
% 3.70/0.99    k1_xboole_0 != k1_tops_1(sK0,sK1) | ~v2_tops_1(sK1,sK0)),
% 3.70/0.99    inference(cnf_transformation,[],[f58])).
% 3.70/0.99  
% 3.70/0.99  fof(f82,plain,(
% 3.70/0.99    ( ! [X0,X1] : (v2_tops_1(X1,X0) | ~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.70/0.99    inference(cnf_transformation,[],[f53])).
% 3.70/0.99  
% 3.70/0.99  fof(f80,plain,(
% 3.70/0.99    ( ! [X0,X1] : (v1_tops_1(X1,X0) | k2_pre_topc(X0,X1) != k2_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.70/0.99    inference(cnf_transformation,[],[f52])).
% 3.70/0.99  
% 3.70/0.99  cnf(c_1013,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_5054,plain,
% 3.70/0.99      ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) != X0
% 3.70/0.99      | k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k3_subset_1(u1_struct_0(sK0),k2_struct_0(sK0))
% 3.70/0.99      | k3_subset_1(u1_struct_0(sK0),k2_struct_0(sK0)) != X0 ),
% 3.70/0.99      inference(instantiation,[status(thm)],[c_1013]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_5055,plain,
% 3.70/0.99      ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k3_subset_1(u1_struct_0(sK0),k2_struct_0(sK0))
% 3.70/0.99      | k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) != k1_xboole_0
% 3.70/0.99      | k3_subset_1(u1_struct_0(sK0),k2_struct_0(sK0)) != k1_xboole_0 ),
% 3.70/0.99      inference(instantiation,[status(thm)],[c_5054]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_14,plain,
% 3.70/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.70/0.99      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.70/0.99      | ~ l1_pre_topc(X1) ),
% 3.70/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_28,negated_conjecture,
% 3.70/0.99      ( l1_pre_topc(sK0) ),
% 3.70/0.99      inference(cnf_transformation,[],[f87]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_601,plain,
% 3.70/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.70/0.99      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.70/0.99      | sK0 != X1 ),
% 3.70/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_28]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_602,plain,
% 3.70/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.70/0.99      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.70/0.99      inference(unflattening,[status(thm)],[c_601]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_1521,plain,
% 3.70/0.99      ( m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.70/0.99      | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.70/0.99      inference(instantiation,[status(thm)],[c_602]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_4456,plain,
% 3.70/0.99      ( m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.70/0.99      | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.70/0.99      inference(instantiation,[status(thm)],[c_1521]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_26,negated_conjecture,
% 3.70/0.99      ( v2_tops_1(sK1,sK0) | k1_xboole_0 = k1_tops_1(sK0,sK1) ),
% 3.70/0.99      inference(cnf_transformation,[],[f89]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_217,plain,
% 3.70/0.99      ( v2_tops_1(sK1,sK0) | k1_xboole_0 = k1_tops_1(sK0,sK1) ),
% 3.70/0.99      inference(prop_impl,[status(thm)],[c_26]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_20,plain,
% 3.70/0.99      ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
% 3.70/0.99      | ~ v2_tops_1(X1,X0)
% 3.70/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.70/0.99      | ~ l1_pre_topc(X0) ),
% 3.70/0.99      inference(cnf_transformation,[],[f81]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_490,plain,
% 3.70/0.99      ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
% 3.70/0.99      | ~ v2_tops_1(X1,X0)
% 3.70/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.70/0.99      | sK0 != X0 ),
% 3.70/0.99      inference(resolution_lifted,[status(thm)],[c_20,c_28]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_491,plain,
% 3.70/0.99      ( v1_tops_1(k3_subset_1(u1_struct_0(sK0),X0),sK0)
% 3.70/0.99      | ~ v2_tops_1(X0,sK0)
% 3.70/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.70/0.99      inference(unflattening,[status(thm)],[c_490]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_18,plain,
% 3.70/0.99      ( ~ v1_tops_1(X0,X1)
% 3.70/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.70/0.99      | ~ l1_pre_topc(X1)
% 3.70/0.99      | k2_pre_topc(X1,X0) = k2_struct_0(X1) ),
% 3.70/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_544,plain,
% 3.70/0.99      ( ~ v1_tops_1(X0,X1)
% 3.70/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.70/0.99      | k2_pre_topc(X1,X0) = k2_struct_0(X1)
% 3.70/0.99      | sK0 != X1 ),
% 3.70/0.99      inference(resolution_lifted,[status(thm)],[c_18,c_28]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_545,plain,
% 3.70/0.99      ( ~ v1_tops_1(X0,sK0)
% 3.70/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.70/0.99      | k2_pre_topc(sK0,X0) = k2_struct_0(sK0) ),
% 3.70/0.99      inference(unflattening,[status(thm)],[c_544]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_683,plain,
% 3.70/0.99      ( ~ v2_tops_1(X0,sK0)
% 3.70/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.70/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.70/0.99      | k2_pre_topc(sK0,X1) = k2_struct_0(sK0)
% 3.70/0.99      | k3_subset_1(u1_struct_0(sK0),X0) != X1
% 3.70/0.99      | sK0 != sK0 ),
% 3.70/0.99      inference(resolution_lifted,[status(thm)],[c_491,c_545]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_684,plain,
% 3.70/0.99      ( ~ v2_tops_1(X0,sK0)
% 3.70/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.70/0.99      | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.70/0.99      | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k2_struct_0(sK0) ),
% 3.70/0.99      inference(unflattening,[status(thm)],[c_683]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_729,plain,
% 3.70/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.70/0.99      | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.70/0.99      | k1_tops_1(sK0,sK1) = k1_xboole_0
% 3.70/0.99      | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k2_struct_0(sK0)
% 3.70/0.99      | sK1 != X0
% 3.70/0.99      | sK0 != sK0 ),
% 3.70/0.99      inference(resolution_lifted,[status(thm)],[c_217,c_684]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_730,plain,
% 3.70/0.99      ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.70/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.70/0.99      | k1_tops_1(sK0,sK1) = k1_xboole_0
% 3.70/0.99      | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_struct_0(sK0) ),
% 3.70/0.99      inference(unflattening,[status(thm)],[c_729]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_27,negated_conjecture,
% 3.70/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.70/0.99      inference(cnf_transformation,[],[f88]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_732,plain,
% 3.70/0.99      ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.70/0.99      | k1_tops_1(sK0,sK1) = k1_xboole_0
% 3.70/0.99      | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_struct_0(sK0) ),
% 3.70/0.99      inference(global_propositional_subsumption,
% 3.70/0.99                [status(thm)],
% 3.70/0.99                [c_730,c_27]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_1448,plain,
% 3.70/0.99      ( k1_tops_1(sK0,sK1) = k1_xboole_0
% 3.70/0.99      | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_struct_0(sK0)
% 3.70/0.99      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.70/0.99      inference(predicate_to_equality,[status(thm)],[c_732]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_30,plain,
% 3.70/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.70/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_734,plain,
% 3.70/0.99      ( k1_tops_1(sK0,sK1) = k1_xboole_0
% 3.70/0.99      | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_struct_0(sK0)
% 3.70/0.99      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.70/0.99      inference(predicate_to_equality,[status(thm)],[c_732]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_8,plain,
% 3.70/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.70/0.99      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 3.70/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_12,plain,
% 3.70/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.70/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_213,plain,
% 3.70/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.70/0.99      inference(prop_impl,[status(thm)],[c_12]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_214,plain,
% 3.70/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.70/0.99      inference(renaming,[status(thm)],[c_213]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_264,plain,
% 3.70/0.99      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
% 3.70/0.99      | ~ r1_tarski(X1,X0) ),
% 3.70/0.99      inference(bin_hyper_res,[status(thm)],[c_8,c_214]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_1633,plain,
% 3.70/0.99      ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.70/0.99      | ~ r1_tarski(X0,u1_struct_0(sK0)) ),
% 3.70/0.99      inference(instantiation,[status(thm)],[c_264]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_1805,plain,
% 3.70/0.99      ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.70/0.99      | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
% 3.70/0.99      inference(instantiation,[status(thm)],[c_1633]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_1806,plain,
% 3.70/0.99      ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 3.70/0.99      | r1_tarski(sK1,u1_struct_0(sK0)) != iProver_top ),
% 3.70/0.99      inference(predicate_to_equality,[status(thm)],[c_1805]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_13,plain,
% 3.70/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.70/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_1640,plain,
% 3.70/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.70/0.99      | r1_tarski(X0,u1_struct_0(sK0)) ),
% 3.70/0.99      inference(instantiation,[status(thm)],[c_13]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_1895,plain,
% 3.70/0.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.70/0.99      | r1_tarski(sK1,u1_struct_0(sK0)) ),
% 3.70/0.99      inference(instantiation,[status(thm)],[c_1640]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_1898,plain,
% 3.70/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.70/0.99      | r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
% 3.70/0.99      inference(predicate_to_equality,[status(thm)],[c_1895]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_2441,plain,
% 3.70/0.99      ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_struct_0(sK0)
% 3.70/0.99      | k1_tops_1(sK0,sK1) = k1_xboole_0 ),
% 3.70/0.99      inference(global_propositional_subsumption,
% 3.70/0.99                [status(thm)],
% 3.70/0.99                [c_1448,c_30,c_734,c_1806,c_1898]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_2442,plain,
% 3.70/0.99      ( k1_tops_1(sK0,sK1) = k1_xboole_0
% 3.70/0.99      | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_struct_0(sK0) ),
% 3.70/0.99      inference(renaming,[status(thm)],[c_2441]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_1455,plain,
% 3.70/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.70/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_16,plain,
% 3.70/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.70/0.99      | ~ l1_pre_topc(X1)
% 3.70/0.99      | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0) ),
% 3.70/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_574,plain,
% 3.70/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.70/0.99      | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0)
% 3.70/0.99      | sK0 != X1 ),
% 3.70/0.99      inference(resolution_lifted,[status(thm)],[c_16,c_28]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_575,plain,
% 3.70/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.70/0.99      | k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0) ),
% 3.70/0.99      inference(unflattening,[status(thm)],[c_574]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_1450,plain,
% 3.70/0.99      ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
% 3.70/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.70/0.99      inference(predicate_to_equality,[status(thm)],[c_575]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_1763,plain,
% 3.70/0.99      ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k1_tops_1(sK0,sK1) ),
% 3.70/0.99      inference(superposition,[status(thm)],[c_1455,c_1450]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_2445,plain,
% 3.70/0.99      ( k1_tops_1(sK0,sK1) = k1_xboole_0
% 3.70/0.99      | k3_subset_1(u1_struct_0(sK0),k2_struct_0(sK0)) = k1_tops_1(sK0,sK1) ),
% 3.70/0.99      inference(superposition,[status(thm)],[c_2442,c_1763]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_10,plain,
% 3.70/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 3.70/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_1458,plain,
% 3.70/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.70/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_1800,plain,
% 3.70/0.99      ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k1_xboole_0))) = k1_tops_1(sK0,k1_xboole_0) ),
% 3.70/0.99      inference(superposition,[status(thm)],[c_1458,c_1450]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_2,plain,
% 3.70/0.99      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 3.70/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_22,plain,
% 3.70/0.99      ( ~ l1_pre_topc(X0) | v1_xboole_0(k1_tops_1(X0,k1_struct_0(X0))) ),
% 3.70/0.99      inference(cnf_transformation,[],[f84]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_483,plain,
% 3.70/0.99      ( v1_xboole_0(k1_tops_1(X0,k1_struct_0(X0))) | sK0 != X0 ),
% 3.70/0.99      inference(resolution_lifted,[status(thm)],[c_22,c_28]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_484,plain,
% 3.70/0.99      ( v1_xboole_0(k1_tops_1(sK0,k1_struct_0(sK0))) ),
% 3.70/0.99      inference(unflattening,[status(thm)],[c_483]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_670,plain,
% 3.70/0.99      ( k1_tops_1(sK0,k1_struct_0(sK0)) != X0 | k1_xboole_0 = X0 ),
% 3.70/0.99      inference(resolution_lifted,[status(thm)],[c_2,c_484]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_671,plain,
% 3.70/0.99      ( k1_xboole_0 = k1_tops_1(sK0,k1_struct_0(sK0)) ),
% 3.70/0.99      inference(unflattening,[status(thm)],[c_670]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_24,plain,
% 3.70/0.99      ( ~ l1_pre_topc(X0)
% 3.70/0.99      | k1_tops_1(X0,k1_struct_0(X0)) = k1_struct_0(X0) ),
% 3.70/0.99      inference(cnf_transformation,[],[f86]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_478,plain,
% 3.70/0.99      ( k1_tops_1(X0,k1_struct_0(X0)) = k1_struct_0(X0) | sK0 != X0 ),
% 3.70/0.99      inference(resolution_lifted,[status(thm)],[c_24,c_28]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_479,plain,
% 3.70/0.99      ( k1_tops_1(sK0,k1_struct_0(sK0)) = k1_struct_0(sK0) ),
% 3.70/0.99      inference(unflattening,[status(thm)],[c_478]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_1462,plain,
% 3.70/0.99      ( k1_struct_0(sK0) = k1_xboole_0 ),
% 3.70/0.99      inference(light_normalisation,[status(thm)],[c_479,c_671]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_1638,plain,
% 3.70/0.99      ( k1_tops_1(sK0,k1_xboole_0) = k1_xboole_0 ),
% 3.70/0.99      inference(light_normalisation,[status(thm)],[c_671,c_671,c_1462]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_1803,plain,
% 3.70/0.99      ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k1_xboole_0))) = k1_xboole_0 ),
% 3.70/0.99      inference(light_normalisation,[status(thm)],[c_1800,c_1638]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_6,plain,
% 3.70/0.99      ( k3_subset_1(X0,k1_xboole_0) = X0 ),
% 3.70/0.99      inference(cnf_transformation,[],[f94]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_1,plain,
% 3.70/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 3.70/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_15,plain,
% 3.70/0.99      ( v2_tops_1(X0,X1)
% 3.70/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.70/0.99      | ~ l1_pre_topc(X1)
% 3.70/0.99      | ~ v1_xboole_0(X0) ),
% 3.70/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_586,plain,
% 3.70/0.99      ( v2_tops_1(X0,X1)
% 3.70/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.70/0.99      | ~ v1_xboole_0(X0)
% 3.70/0.99      | sK0 != X1 ),
% 3.70/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_28]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_587,plain,
% 3.70/0.99      ( v2_tops_1(X0,sK0)
% 3.70/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.70/0.99      | ~ v1_xboole_0(X0) ),
% 3.70/0.99      inference(unflattening,[status(thm)],[c_586]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_648,plain,
% 3.70/0.99      ( v2_tops_1(X0,sK0)
% 3.70/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.70/0.99      | k1_xboole_0 != X0 ),
% 3.70/0.99      inference(resolution_lifted,[status(thm)],[c_1,c_587]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_649,plain,
% 3.70/0.99      ( v2_tops_1(k1_xboole_0,sK0)
% 3.70/0.99      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.70/0.99      inference(unflattening,[status(thm)],[c_648]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_655,plain,
% 3.70/0.99      ( v2_tops_1(k1_xboole_0,sK0) ),
% 3.70/0.99      inference(forward_subsumption_resolution,
% 3.70/0.99                [status(thm)],
% 3.70/0.99                [c_649,c_10]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_788,plain,
% 3.70/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.70/0.99      | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.70/0.99      | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k2_struct_0(sK0)
% 3.70/0.99      | sK0 != sK0
% 3.70/0.99      | k1_xboole_0 != X0 ),
% 3.70/0.99      inference(resolution_lifted,[status(thm)],[c_684,c_655]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_789,plain,
% 3.70/0.99      ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.70/0.99      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.70/0.99      | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k1_xboole_0)) = k2_struct_0(sK0) ),
% 3.70/0.99      inference(unflattening,[status(thm)],[c_788]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_7,plain,
% 3.70/0.99      ( m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) ),
% 3.70/0.99      inference(cnf_transformation,[],[f95]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_797,plain,
% 3.70/0.99      ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k1_xboole_0)) = k2_struct_0(sK0) ),
% 3.70/0.99      inference(forward_subsumption_resolution,
% 3.70/0.99                [status(thm)],
% 3.70/0.99                [c_789,c_10,c_7]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_1464,plain,
% 3.70/0.99      ( k2_pre_topc(sK0,u1_struct_0(sK0)) = k2_struct_0(sK0) ),
% 3.70/0.99      inference(demodulation,[status(thm)],[c_797,c_6]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_1804,plain,
% 3.70/0.99      ( k3_subset_1(u1_struct_0(sK0),k2_struct_0(sK0)) = k1_xboole_0 ),
% 3.70/0.99      inference(demodulation,[status(thm)],[c_1803,c_6,c_1464]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_2446,plain,
% 3.70/0.99      ( k1_tops_1(sK0,sK1) = k1_xboole_0 ),
% 3.70/0.99      inference(light_normalisation,[status(thm)],[c_2445,c_1804]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_3904,plain,
% 3.70/0.99      ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k1_xboole_0 ),
% 3.70/0.99      inference(demodulation,[status(thm)],[c_2446,c_1763]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_3323,plain,
% 3.70/0.99      ( ~ m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.70/0.99      | r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0)) ),
% 3.70/0.99      inference(instantiation,[status(thm)],[c_1640]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_2569,plain,
% 3.70/0.99      ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.70/0.99      | r1_tarski(k2_struct_0(sK0),u1_struct_0(sK0)) ),
% 3.70/0.99      inference(instantiation,[status(thm)],[c_1640]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_11,plain,
% 3.70/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.70/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.70/0.99      | X2 = X0
% 3.70/0.99      | k3_subset_1(X1,X2) != k3_subset_1(X1,X0) ),
% 3.70/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_266,plain,
% 3.70/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.70/0.99      | ~ r1_tarski(X2,X1)
% 3.70/0.99      | X0 = X2
% 3.70/0.99      | k3_subset_1(X1,X0) != k3_subset_1(X1,X2) ),
% 3.70/0.99      inference(bin_hyper_res,[status(thm)],[c_11,c_214]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_899,plain,
% 3.70/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.70/0.99      inference(prop_impl,[status(thm)],[c_12]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_900,plain,
% 3.70/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.70/0.99      inference(renaming,[status(thm)],[c_899]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_940,plain,
% 3.70/0.99      ( ~ r1_tarski(X0,X1)
% 3.70/0.99      | ~ r1_tarski(X2,X1)
% 3.70/0.99      | X0 = X2
% 3.70/0.99      | k3_subset_1(X1,X0) != k3_subset_1(X1,X2) ),
% 3.70/0.99      inference(bin_hyper_res,[status(thm)],[c_266,c_900]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_2279,plain,
% 3.70/0.99      ( ~ r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),X0)
% 3.70/0.99      | ~ r1_tarski(k2_struct_0(sK0),X0)
% 3.70/0.99      | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_struct_0(sK0)
% 3.70/0.99      | k3_subset_1(X0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) != k3_subset_1(X0,k2_struct_0(sK0)) ),
% 3.70/0.99      inference(instantiation,[status(thm)],[c_940]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_2567,plain,
% 3.70/0.99      ( ~ r1_tarski(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),u1_struct_0(sK0))
% 3.70/0.99      | ~ r1_tarski(k2_struct_0(sK0),u1_struct_0(sK0))
% 3.70/0.99      | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_struct_0(sK0)
% 3.70/0.99      | k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) != k3_subset_1(u1_struct_0(sK0),k2_struct_0(sK0)) ),
% 3.70/0.99      inference(instantiation,[status(thm)],[c_2279]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_1459,plain,
% 3.70/0.99      ( m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) = iProver_top ),
% 3.70/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_1463,plain,
% 3.70/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.70/0.99      inference(light_normalisation,[status(thm)],[c_1459,c_6]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_1449,plain,
% 3.70/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.70/0.99      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.70/0.99      inference(predicate_to_equality,[status(thm)],[c_602]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_2109,plain,
% 3.70/0.99      ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 3.70/0.99      | m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.70/0.99      inference(superposition,[status(thm)],[c_1464,c_1449]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_2287,plain,
% 3.70/0.99      ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.70/0.99      inference(superposition,[status(thm)],[c_1463,c_2109]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_2288,plain,
% 3.70/0.99      ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.70/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_2287]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_25,negated_conjecture,
% 3.70/0.99      ( ~ v2_tops_1(sK1,sK0) | k1_xboole_0 != k1_tops_1(sK0,sK1) ),
% 3.70/0.99      inference(cnf_transformation,[],[f90]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_215,plain,
% 3.70/0.99      ( ~ v2_tops_1(sK1,sK0) | k1_xboole_0 != k1_tops_1(sK0,sK1) ),
% 3.70/0.99      inference(prop_impl,[status(thm)],[c_25]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_19,plain,
% 3.70/0.99      ( ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
% 3.70/0.99      | v2_tops_1(X1,X0)
% 3.70/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.70/0.99      | ~ l1_pre_topc(X0) ),
% 3.70/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_505,plain,
% 3.70/0.99      ( ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
% 3.70/0.99      | v2_tops_1(X1,X0)
% 3.70/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.70/0.99      | sK0 != X0 ),
% 3.70/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_28]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_506,plain,
% 3.70/0.99      ( ~ v1_tops_1(k3_subset_1(u1_struct_0(sK0),X0),sK0)
% 3.70/0.99      | v2_tops_1(X0,sK0)
% 3.70/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.70/0.99      inference(unflattening,[status(thm)],[c_505]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_17,plain,
% 3.70/0.99      ( v1_tops_1(X0,X1)
% 3.70/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.70/0.99      | ~ l1_pre_topc(X1)
% 3.70/0.99      | k2_pre_topc(X1,X0) != k2_struct_0(X1) ),
% 3.70/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_559,plain,
% 3.70/0.99      ( v1_tops_1(X0,X1)
% 3.70/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.70/0.99      | k2_pre_topc(X1,X0) != k2_struct_0(X1)
% 3.70/0.99      | sK0 != X1 ),
% 3.70/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_28]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_560,plain,
% 3.70/0.99      ( v1_tops_1(X0,sK0)
% 3.70/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.70/0.99      | k2_pre_topc(sK0,X0) != k2_struct_0(sK0) ),
% 3.70/0.99      inference(unflattening,[status(thm)],[c_559]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_701,plain,
% 3.70/0.99      ( v2_tops_1(X0,sK0)
% 3.70/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.70/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.70/0.99      | k2_pre_topc(sK0,X1) != k2_struct_0(sK0)
% 3.70/0.99      | k3_subset_1(u1_struct_0(sK0),X0) != X1
% 3.70/0.99      | sK0 != sK0 ),
% 3.70/0.99      inference(resolution_lifted,[status(thm)],[c_506,c_560]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_702,plain,
% 3.70/0.99      ( v2_tops_1(X0,sK0)
% 3.70/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.70/0.99      | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.70/0.99      | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)) != k2_struct_0(sK0) ),
% 3.70/0.99      inference(unflattening,[status(thm)],[c_701]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_746,plain,
% 3.70/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.70/0.99      | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.70/0.99      | k1_tops_1(sK0,sK1) != k1_xboole_0
% 3.70/0.99      | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)) != k2_struct_0(sK0)
% 3.70/0.99      | sK1 != X0
% 3.70/0.99      | sK0 != sK0 ),
% 3.70/0.99      inference(resolution_lifted,[status(thm)],[c_215,c_702]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_747,plain,
% 3.70/0.99      ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 3.70/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.70/0.99      | k1_tops_1(sK0,sK1) != k1_xboole_0
% 3.70/0.99      | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) != k2_struct_0(sK0) ),
% 3.70/0.99      inference(unflattening,[status(thm)],[c_746]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(c_748,plain,
% 3.70/0.99      ( k1_tops_1(sK0,sK1) != k1_xboole_0
% 3.70/0.99      | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) != k2_struct_0(sK0)
% 3.70/0.99      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.70/0.99      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.70/0.99      inference(predicate_to_equality,[status(thm)],[c_747]) ).
% 3.70/0.99  
% 3.70/0.99  cnf(contradiction,plain,
% 3.70/0.99      ( $false ),
% 3.70/0.99      inference(minisat,
% 3.70/0.99                [status(thm)],
% 3.70/0.99                [c_5055,c_4456,c_3904,c_3323,c_2569,c_2567,c_2446,c_2288,
% 3.70/0.99                 c_1898,c_1895,c_1806,c_1805,c_1804,c_748,c_30,c_27]) ).
% 3.70/0.99  
% 3.70/0.99  
% 3.70/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.70/0.99  
% 3.70/0.99  ------                               Statistics
% 3.70/0.99  
% 3.70/0.99  ------ General
% 3.70/0.99  
% 3.70/0.99  abstr_ref_over_cycles:                  0
% 3.70/0.99  abstr_ref_under_cycles:                 0
% 3.70/0.99  gc_basic_clause_elim:                   0
% 3.70/0.99  forced_gc_time:                         0
% 3.70/0.99  parsing_time:                           0.01
% 3.70/0.99  unif_index_cands_time:                  0.
% 3.70/0.99  unif_index_add_time:                    0.
% 3.70/0.99  orderings_time:                         0.
% 3.70/0.99  out_proof_time:                         0.011
% 3.70/0.99  total_time:                             0.186
% 3.70/0.99  num_of_symbols:                         49
% 3.70/0.99  num_of_terms:                           3901
% 3.70/0.99  
% 3.70/0.99  ------ Preprocessing
% 3.70/0.99  
% 3.70/0.99  num_of_splits:                          0
% 3.70/0.99  num_of_split_atoms:                     0
% 3.70/0.99  num_of_reused_defs:                     0
% 3.70/0.99  num_eq_ax_congr_red:                    13
% 3.70/0.99  num_of_sem_filtered_clauses:            1
% 3.70/0.99  num_of_subtypes:                        0
% 3.70/0.99  monotx_restored_types:                  0
% 3.70/0.99  sat_num_of_epr_types:                   0
% 3.70/0.99  sat_num_of_non_cyclic_types:            0
% 3.70/0.99  sat_guarded_non_collapsed_types:        0
% 3.70/0.99  num_pure_diseq_elim:                    0
% 3.70/0.99  simp_replaced_by:                       0
% 3.70/0.99  res_preprocessed:                       131
% 3.70/0.99  prep_upred:                             0
% 3.70/0.99  prep_unflattend:                        29
% 3.70/0.99  smt_new_axioms:                         0
% 3.70/0.99  pred_elim_cands:                        2
% 3.70/0.99  pred_elim:                              4
% 3.70/0.99  pred_elim_cl:                           4
% 3.70/0.99  pred_elim_cycles:                       8
% 3.70/0.99  merged_defs:                            10
% 3.70/0.99  merged_defs_ncl:                        0
% 3.70/0.99  bin_hyper_res:                          14
% 3.70/0.99  prep_cycles:                            4
% 3.70/0.99  pred_elim_time:                         0.009
% 3.70/0.99  splitting_time:                         0.
% 3.70/0.99  sem_filter_time:                        0.
% 3.70/0.99  monotx_time:                            0.001
% 3.70/0.99  subtype_inf_time:                       0.
% 3.70/0.99  
% 3.70/0.99  ------ Problem properties
% 3.70/0.99  
% 3.70/0.99  clauses:                                25
% 3.70/0.99  conjectures:                            1
% 3.70/0.99  epr:                                    1
% 3.70/0.99  horn:                                   24
% 3.70/0.99  ground:                                 9
% 3.70/0.99  unary:                                  10
% 3.70/0.99  binary:                                 9
% 3.70/0.99  lits:                                   47
% 3.70/0.99  lits_eq:                                20
% 3.70/0.99  fd_pure:                                0
% 3.70/0.99  fd_pseudo:                              0
% 3.70/0.99  fd_cond:                                0
% 3.70/0.99  fd_pseudo_cond:                         1
% 3.70/0.99  ac_symbols:                             0
% 3.70/0.99  
% 3.70/0.99  ------ Propositional Solver
% 3.70/0.99  
% 3.70/0.99  prop_solver_calls:                      30
% 3.70/0.99  prop_fast_solver_calls:                 755
% 3.70/0.99  smt_solver_calls:                       0
% 3.70/0.99  smt_fast_solver_calls:                  0
% 3.70/0.99  prop_num_of_clauses:                    2042
% 3.70/0.99  prop_preprocess_simplified:             5323
% 3.70/0.99  prop_fo_subsumed:                       4
% 3.70/0.99  prop_solver_time:                       0.
% 3.70/0.99  smt_solver_time:                        0.
% 3.70/0.99  smt_fast_solver_time:                   0.
% 3.70/0.99  prop_fast_solver_time:                  0.
% 3.70/0.99  prop_unsat_core_time:                   0.
% 3.70/0.99  
% 3.70/0.99  ------ QBF
% 3.70/0.99  
% 3.70/0.99  qbf_q_res:                              0
% 3.70/0.99  qbf_num_tautologies:                    0
% 3.70/0.99  qbf_prep_cycles:                        0
% 3.70/0.99  
% 3.70/0.99  ------ BMC1
% 3.70/0.99  
% 3.70/0.99  bmc1_current_bound:                     -1
% 3.70/0.99  bmc1_last_solved_bound:                 -1
% 3.70/0.99  bmc1_unsat_core_size:                   -1
% 3.70/0.99  bmc1_unsat_core_parents_size:           -1
% 3.70/0.99  bmc1_merge_next_fun:                    0
% 3.70/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.70/0.99  
% 3.70/0.99  ------ Instantiation
% 3.70/0.99  
% 3.70/0.99  inst_num_of_clauses:                    551
% 3.70/0.99  inst_num_in_passive:                    201
% 3.70/0.99  inst_num_in_active:                     347
% 3.70/0.99  inst_num_in_unprocessed:                2
% 3.70/0.99  inst_num_of_loops:                      402
% 3.70/0.99  inst_num_of_learning_restarts:          0
% 3.70/0.99  inst_num_moves_active_passive:          50
% 3.70/0.99  inst_lit_activity:                      0
% 3.70/0.99  inst_lit_activity_moves:                0
% 3.70/0.99  inst_num_tautologies:                   0
% 3.70/0.99  inst_num_prop_implied:                  0
% 3.70/0.99  inst_num_existing_simplified:           0
% 3.70/0.99  inst_num_eq_res_simplified:             0
% 3.70/0.99  inst_num_child_elim:                    0
% 3.70/0.99  inst_num_of_dismatching_blockings:      96
% 3.70/0.99  inst_num_of_non_proper_insts:           766
% 3.70/0.99  inst_num_of_duplicates:                 0
% 3.70/0.99  inst_inst_num_from_inst_to_res:         0
% 3.70/0.99  inst_dismatching_checking_time:         0.
% 3.70/0.99  
% 3.70/0.99  ------ Resolution
% 3.70/0.99  
% 3.70/0.99  res_num_of_clauses:                     0
% 3.70/0.99  res_num_in_passive:                     0
% 3.70/0.99  res_num_in_active:                      0
% 3.70/0.99  res_num_of_loops:                       135
% 3.70/0.99  res_forward_subset_subsumed:            84
% 3.70/0.99  res_backward_subset_subsumed:           2
% 3.70/0.99  res_forward_subsumed:                   0
% 3.70/0.99  res_backward_subsumed:                  0
% 3.70/0.99  res_forward_subsumption_resolution:     4
% 3.70/0.99  res_backward_subsumption_resolution:    0
% 3.70/0.99  res_clause_to_clause_subsumption:       650
% 3.70/0.99  res_orphan_elimination:                 0
% 3.70/0.99  res_tautology_del:                      109
% 3.70/0.99  res_num_eq_res_simplified:              2
% 3.70/0.99  res_num_sel_changes:                    0
% 3.70/0.99  res_moves_from_active_to_pass:          0
% 3.70/0.99  
% 3.70/0.99  ------ Superposition
% 3.70/0.99  
% 3.70/0.99  sup_time_total:                         0.
% 3.70/0.99  sup_time_generating:                    0.
% 3.70/0.99  sup_time_sim_full:                      0.
% 3.70/0.99  sup_time_sim_immed:                     0.
% 3.70/0.99  
% 3.70/0.99  sup_num_of_clauses:                     175
% 3.70/0.99  sup_num_in_active:                      72
% 3.70/0.99  sup_num_in_passive:                     103
% 3.70/0.99  sup_num_of_loops:                       80
% 3.70/0.99  sup_fw_superposition:                   186
% 3.70/0.99  sup_bw_superposition:                   84
% 3.70/0.99  sup_immediate_simplified:               105
% 3.70/0.99  sup_given_eliminated:                   1
% 3.70/0.99  comparisons_done:                       0
% 3.70/0.99  comparisons_avoided:                    3
% 3.70/0.99  
% 3.70/0.99  ------ Simplifications
% 3.70/0.99  
% 3.70/0.99  
% 3.70/0.99  sim_fw_subset_subsumed:                 1
% 3.70/0.99  sim_bw_subset_subsumed:                 4
% 3.70/0.99  sim_fw_subsumed:                        15
% 3.70/0.99  sim_bw_subsumed:                        0
% 3.70/0.99  sim_fw_subsumption_res:                 0
% 3.70/0.99  sim_bw_subsumption_res:                 0
% 3.70/0.99  sim_tautology_del:                      12
% 3.70/0.99  sim_eq_tautology_del:                   67
% 3.70/0.99  sim_eq_res_simp:                        2
% 3.70/0.99  sim_fw_demodulated:                     11
% 3.70/0.99  sim_bw_demodulated:                     6
% 3.70/0.99  sim_light_normalised:                   89
% 3.70/0.99  sim_joinable_taut:                      0
% 3.70/0.99  sim_joinable_simp:                      0
% 3.70/0.99  sim_ac_normalised:                      0
% 3.70/0.99  sim_smt_subsumption:                    0
% 3.70/0.99  
%------------------------------------------------------------------------------
