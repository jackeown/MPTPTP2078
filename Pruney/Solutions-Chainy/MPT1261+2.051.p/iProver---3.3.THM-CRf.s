%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:14:31 EST 2020

% Result     : Theorem 42.97s
% Output     : CNFRefutation 42.97s
% Verified   : 
% Statistics : Number of formulae       :  168 (1396 expanded)
%              Number of clauses        :   96 ( 436 expanded)
%              Number of leaves         :   22 ( 314 expanded)
%              Depth                    :   26
%              Number of atoms          :  381 (5015 expanded)
%              Number of equality atoms :  203 (1800 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f24,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f46,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f47,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f46])).

fof(f48,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1)
            | ~ v4_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f47])).

fof(f49,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1)
            | ~ v4_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f48])).

fof(f51,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1)
            | ~ v4_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) != k2_tops_1(X0,sK1)
          | ~ v4_pre_topc(sK1,X0) )
        & ( k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) = k2_tops_1(X0,sK1)
          | v4_pre_topc(sK1,X0) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1)
              | ~ v4_pre_topc(X1,X0) )
            & ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
              | v4_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) != k2_tops_1(sK0,X1)
            | ~ v4_pre_topc(X1,sK0) )
          & ( k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) = k2_tops_1(sK0,X1)
            | v4_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f49,f51,f50])).

fof(f79,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f52])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f80,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f18,axiom,(
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

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f37])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f78,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f16,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f87,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(definition_unfolding,[],[f68,f58])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f17])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f69,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f22,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f82,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f54,f58])).

fof(f3,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f3])).

fof(f84,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f55,f58])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f7,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f85,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(definition_unfolding,[],[f61,f59])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f39])).

fof(f72,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f31])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k4_xboole_0(X2,X1)) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f65,f59])).

fof(f23,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f71,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) != X1
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f81,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f77,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_775,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_787,plain,
    ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_5979,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
    inference(superposition,[status(thm)],[c_775,c_787])).

cnf(c_23,negated_conjecture,
    ( v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_776,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_6250,plain,
    ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5979,c_776])).

cnf(c_16,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_783,plain,
    ( k2_pre_topc(X0,X1) = X1
    | v4_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_7253,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | v4_pre_topc(sK1,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_775,c_783])).

cnf(c_25,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_28,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_8028,plain,
    ( v4_pre_topc(sK1,sK0) != iProver_top
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7253,c_28])).

cnf(c_8029,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_8028])).

cnf(c_8034,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_6250,c_8029])).

cnf(c_13,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_8044,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_8034,c_13])).

cnf(c_3,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_792,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1588,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_13,c_792])).

cnf(c_14,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_785,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_789,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3616,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | r1_tarski(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_785,c_789])).

cnf(c_3712,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,k1_setfam_1(k2_tarski(X0,X1)))) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(superposition,[status(thm)],[c_1588,c_3616])).

cnf(c_8543,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k3_subset_1(sK1,k3_subset_1(sK1,k4_xboole_0(sK1,k2_tops_1(sK0,sK1)))) = k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))) ),
    inference(superposition,[status(thm)],[c_8044,c_3712])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_791,plain,
    ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4241,plain,
    ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_785,c_791])).

cnf(c_5576,plain,
    ( k3_subset_1(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_792,c_4241])).

cnf(c_5597,plain,
    ( k3_subset_1(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_5576,c_13])).

cnf(c_8590,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k3_subset_1(sK1,k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1)))) = k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))) ),
    inference(demodulation,[status(thm)],[c_8543,c_5597])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_779,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(k1_tops_1(X1,X0),X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2260,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_775,c_779])).

cnf(c_29,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_1011,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_1012,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1011])).

cnf(c_2681,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2260,c_28,c_29,c_1012])).

cnf(c_5577,plain,
    ( k3_subset_1(sK1,k1_tops_1(sK0,sK1)) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_2681,c_4241])).

cnf(c_3711,plain,
    ( k3_subset_1(sK1,k3_subset_1(sK1,k1_tops_1(sK0,sK1))) = k1_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_2681,c_3616])).

cnf(c_5604,plain,
    ( k3_subset_1(sK1,k4_xboole_0(sK1,k1_tops_1(sK0,sK1))) = k1_tops_1(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_5577,c_3711])).

cnf(c_7201,plain,
    ( k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))) = k1_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_5604,c_5597])).

cnf(c_108625,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k3_subset_1(sK1,k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1)))) = k1_tops_1(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_8590,c_7201])).

cnf(c_108633,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k3_subset_1(sK1,k1_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_108625,c_3712])).

cnf(c_108645,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    inference(light_normalisation,[status(thm)],[c_108633,c_5577])).

cnf(c_5,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_813,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_0,c_13])).

cnf(c_2523,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_5,c_813])).

cnf(c_109370,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k5_xboole_0(k2_tops_1(sK0,sK1),k4_xboole_0(sK1,k1_tops_1(sK0,sK1))) = k4_xboole_0(k2_tops_1(sK0,sK1),sK1) ),
    inference(superposition,[status(thm)],[c_108645,c_2523])).

cnf(c_130674,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k5_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) = k4_xboole_0(k2_tops_1(sK0,sK1),sK1) ),
    inference(superposition,[status(thm)],[c_8034,c_109370])).

cnf(c_2,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_4,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_805,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2,c_4])).

cnf(c_1427,plain,
    ( k1_setfam_1(k2_tarski(X0,X0)) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_805,c_13])).

cnf(c_1439,plain,
    ( k1_setfam_1(k2_tarski(X0,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1427,c_4])).

cnf(c_2520,plain,
    ( k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_1439,c_813])).

cnf(c_2536,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2520,c_805])).

cnf(c_130675,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k4_xboole_0(k2_tops_1(sK0,sK1),sK1) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_130674,c_2536])).

cnf(c_6,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_130736,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k5_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_130675,c_6])).

cnf(c_1428,plain,
    ( k1_setfam_1(k2_tarski(X0,k1_xboole_0)) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_4,c_13])).

cnf(c_1436,plain,
    ( k1_setfam_1(k2_tarski(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1428,c_805])).

cnf(c_2521,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1436,c_813])).

cnf(c_2530,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_2521,c_4])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_782,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k5_xboole_0(X0,k4_xboole_0(X2,X0)) = k4_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_788,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k4_subset_1(X2,X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_862,plain,
    ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_788,c_6])).

cnf(c_20978,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k3_tarski(k2_tarski(sK1,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_775,c_862])).

cnf(c_21783,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_782,c_20978])).

cnf(c_22620,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_21783,c_28])).

cnf(c_22621,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_22620])).

cnf(c_22631,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
    inference(superposition,[status(thm)],[c_775,c_22621])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_778,plain,
    ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1198,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_775,c_778])).

cnf(c_1077,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_1607,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1198,c_25,c_24,c_1077])).

cnf(c_22639,plain,
    ( k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k2_pre_topc(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_22631,c_1607])).

cnf(c_130756,plain,
    ( k2_pre_topc(sK0,sK1) = sK1 ),
    inference(demodulation,[status(thm)],[c_130736,c_2530,c_22639])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_780,plain,
    ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3215,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_775,c_780])).

cnf(c_1107,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_3704,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3215,c_25,c_24,c_1107])).

cnf(c_130981,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_130756,c_3704])).

cnf(c_15,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | k2_pre_topc(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1074,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | k2_pre_topc(sK0,sK1) != sK1 ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_22,negated_conjecture,
    ( ~ v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_26,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f77])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_130981,c_130756,c_1074,c_22,c_24,c_25,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:18:54 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 42.97/6.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 42.97/6.00  
% 42.97/6.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 42.97/6.00  
% 42.97/6.00  ------  iProver source info
% 42.97/6.00  
% 42.97/6.00  git: date: 2020-06-30 10:37:57 +0100
% 42.97/6.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 42.97/6.00  git: non_committed_changes: false
% 42.97/6.00  git: last_make_outside_of_git: false
% 42.97/6.00  
% 42.97/6.00  ------ 
% 42.97/6.00  ------ Parsing...
% 42.97/6.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 42.97/6.00  
% 42.97/6.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 42.97/6.00  
% 42.97/6.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 42.97/6.00  
% 42.97/6.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 42.97/6.00  ------ Proving...
% 42.97/6.00  ------ Problem Properties 
% 42.97/6.00  
% 42.97/6.00  
% 42.97/6.00  clauses                                 27
% 42.97/6.00  conjectures                             5
% 42.97/6.00  EPR                                     2
% 42.97/6.00  Horn                                    26
% 42.97/6.00  unary                                   11
% 42.97/6.00  binary                                  7
% 42.97/6.00  lits                                    57
% 42.97/6.00  lits eq                                 19
% 42.97/6.00  fd_pure                                 0
% 42.97/6.00  fd_pseudo                               0
% 42.97/6.00  fd_cond                                 0
% 42.97/6.00  fd_pseudo_cond                          1
% 42.97/6.00  AC symbols                              0
% 42.97/6.00  
% 42.97/6.00  ------ Input Options Time Limit: Unbounded
% 42.97/6.00  
% 42.97/6.00  
% 42.97/6.00  ------ 
% 42.97/6.00  Current options:
% 42.97/6.00  ------ 
% 42.97/6.00  
% 42.97/6.00  
% 42.97/6.00  
% 42.97/6.00  
% 42.97/6.00  ------ Proving...
% 42.97/6.00  
% 42.97/6.00  
% 42.97/6.00  % SZS status Theorem for theBenchmark.p
% 42.97/6.00  
% 42.97/6.00  % SZS output start CNFRefutation for theBenchmark.p
% 42.97/6.00  
% 42.97/6.00  fof(f24,conjecture,(
% 42.97/6.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 42.97/6.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 42.97/6.00  
% 42.97/6.00  fof(f25,negated_conjecture,(
% 42.97/6.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 42.97/6.00    inference(negated_conjecture,[],[f24])).
% 42.97/6.00  
% 42.97/6.00  fof(f46,plain,(
% 42.97/6.00    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 42.97/6.00    inference(ennf_transformation,[],[f25])).
% 42.97/6.00  
% 42.97/6.00  fof(f47,plain,(
% 42.97/6.00    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 42.97/6.00    inference(flattening,[],[f46])).
% 42.97/6.00  
% 42.97/6.00  fof(f48,plain,(
% 42.97/6.00    ? [X0] : (? [X1] : (((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 42.97/6.00    inference(nnf_transformation,[],[f47])).
% 42.97/6.00  
% 42.97/6.00  fof(f49,plain,(
% 42.97/6.00    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 42.97/6.00    inference(flattening,[],[f48])).
% 42.97/6.00  
% 42.97/6.00  fof(f51,plain,(
% 42.97/6.00    ( ! [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) != k2_tops_1(X0,sK1) | ~v4_pre_topc(sK1,X0)) & (k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) = k2_tops_1(X0,sK1) | v4_pre_topc(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 42.97/6.00    introduced(choice_axiom,[])).
% 42.97/6.00  
% 42.97/6.00  fof(f50,plain,(
% 42.97/6.00    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) != k2_tops_1(sK0,X1) | ~v4_pre_topc(X1,sK0)) & (k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) = k2_tops_1(sK0,X1) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 42.97/6.00    introduced(choice_axiom,[])).
% 42.97/6.00  
% 42.97/6.00  fof(f52,plain,(
% 42.97/6.00    ((k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)) & (k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 42.97/6.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f49,f51,f50])).
% 42.97/6.00  
% 42.97/6.00  fof(f79,plain,(
% 42.97/6.00    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 42.97/6.00    inference(cnf_transformation,[],[f52])).
% 42.97/6.00  
% 42.97/6.00  fof(f14,axiom,(
% 42.97/6.00    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 42.97/6.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 42.97/6.00  
% 42.97/6.00  fof(f33,plain,(
% 42.97/6.00    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 42.97/6.00    inference(ennf_transformation,[],[f14])).
% 42.97/6.00  
% 42.97/6.00  fof(f66,plain,(
% 42.97/6.00    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 42.97/6.00    inference(cnf_transformation,[],[f33])).
% 42.97/6.00  
% 42.97/6.00  fof(f80,plain,(
% 42.97/6.00    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)),
% 42.97/6.00    inference(cnf_transformation,[],[f52])).
% 42.97/6.00  
% 42.97/6.00  fof(f18,axiom,(
% 42.97/6.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 42.97/6.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 42.97/6.00  
% 42.97/6.00  fof(f37,plain,(
% 42.97/6.00    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 42.97/6.00    inference(ennf_transformation,[],[f18])).
% 42.97/6.00  
% 42.97/6.00  fof(f38,plain,(
% 42.97/6.00    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 42.97/6.00    inference(flattening,[],[f37])).
% 42.97/6.00  
% 42.97/6.00  fof(f70,plain,(
% 42.97/6.00    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 42.97/6.00    inference(cnf_transformation,[],[f38])).
% 42.97/6.00  
% 42.97/6.00  fof(f78,plain,(
% 42.97/6.00    l1_pre_topc(sK0)),
% 42.97/6.00    inference(cnf_transformation,[],[f52])).
% 42.97/6.00  
% 42.97/6.00  fof(f16,axiom,(
% 42.97/6.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 42.97/6.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 42.97/6.00  
% 42.97/6.00  fof(f68,plain,(
% 42.97/6.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 42.97/6.00    inference(cnf_transformation,[],[f16])).
% 42.97/6.00  
% 42.97/6.00  fof(f6,axiom,(
% 42.97/6.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 42.97/6.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 42.97/6.00  
% 42.97/6.00  fof(f58,plain,(
% 42.97/6.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 42.97/6.00    inference(cnf_transformation,[],[f6])).
% 42.97/6.00  
% 42.97/6.00  fof(f87,plain,(
% 42.97/6.00    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 42.97/6.00    inference(definition_unfolding,[],[f68,f58])).
% 42.97/6.00  
% 42.97/6.00  fof(f4,axiom,(
% 42.97/6.00    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 42.97/6.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 42.97/6.00  
% 42.97/6.00  fof(f56,plain,(
% 42.97/6.00    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 42.97/6.00    inference(cnf_transformation,[],[f4])).
% 42.97/6.00  
% 42.97/6.00  fof(f17,axiom,(
% 42.97/6.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 42.97/6.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 42.97/6.00  
% 42.97/6.00  fof(f27,plain,(
% 42.97/6.00    ! [X0,X1] : (r1_tarski(X0,X1) => m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 42.97/6.00    inference(unused_predicate_definition_removal,[],[f17])).
% 42.97/6.00  
% 42.97/6.00  fof(f36,plain,(
% 42.97/6.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 42.97/6.00    inference(ennf_transformation,[],[f27])).
% 42.97/6.00  
% 42.97/6.00  fof(f69,plain,(
% 42.97/6.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 42.97/6.00    inference(cnf_transformation,[],[f36])).
% 42.97/6.00  
% 42.97/6.00  fof(f12,axiom,(
% 42.97/6.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 42.97/6.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 42.97/6.00  
% 42.97/6.00  fof(f30,plain,(
% 42.97/6.00    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 42.97/6.00    inference(ennf_transformation,[],[f12])).
% 42.97/6.00  
% 42.97/6.00  fof(f64,plain,(
% 42.97/6.00    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 42.97/6.00    inference(cnf_transformation,[],[f30])).
% 42.97/6.00  
% 42.97/6.00  fof(f10,axiom,(
% 42.97/6.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 42.97/6.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 42.97/6.00  
% 42.97/6.00  fof(f28,plain,(
% 42.97/6.00    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 42.97/6.00    inference(ennf_transformation,[],[f10])).
% 42.97/6.00  
% 42.97/6.00  fof(f62,plain,(
% 42.97/6.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 42.97/6.00    inference(cnf_transformation,[],[f28])).
% 42.97/6.00  
% 42.97/6.00  fof(f22,axiom,(
% 42.97/6.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 42.97/6.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 42.97/6.00  
% 42.97/6.00  fof(f44,plain,(
% 42.97/6.00    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 42.97/6.00    inference(ennf_transformation,[],[f22])).
% 42.97/6.00  
% 42.97/6.00  fof(f75,plain,(
% 42.97/6.00    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 42.97/6.00    inference(cnf_transformation,[],[f44])).
% 42.97/6.00  
% 42.97/6.00  fof(f8,axiom,(
% 42.97/6.00    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 42.97/6.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 42.97/6.00  
% 42.97/6.00  fof(f60,plain,(
% 42.97/6.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 42.97/6.00    inference(cnf_transformation,[],[f8])).
% 42.97/6.00  
% 42.97/6.00  fof(f2,axiom,(
% 42.97/6.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 42.97/6.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 42.97/6.00  
% 42.97/6.00  fof(f54,plain,(
% 42.97/6.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 42.97/6.00    inference(cnf_transformation,[],[f2])).
% 42.97/6.00  
% 42.97/6.00  fof(f82,plain,(
% 42.97/6.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 42.97/6.00    inference(definition_unfolding,[],[f54,f58])).
% 42.97/6.00  
% 42.97/6.00  fof(f3,axiom,(
% 42.97/6.00    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 42.97/6.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 42.97/6.00  
% 42.97/6.00  fof(f55,plain,(
% 42.97/6.00    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 42.97/6.00    inference(cnf_transformation,[],[f3])).
% 42.97/6.00  
% 42.97/6.00  fof(f84,plain,(
% 42.97/6.00    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0) )),
% 42.97/6.00    inference(definition_unfolding,[],[f55,f58])).
% 42.97/6.00  
% 42.97/6.00  fof(f5,axiom,(
% 42.97/6.00    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 42.97/6.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 42.97/6.00  
% 42.97/6.00  fof(f57,plain,(
% 42.97/6.00    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 42.97/6.00    inference(cnf_transformation,[],[f5])).
% 42.97/6.00  
% 42.97/6.00  fof(f9,axiom,(
% 42.97/6.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 42.97/6.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 42.97/6.00  
% 42.97/6.00  fof(f61,plain,(
% 42.97/6.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 42.97/6.00    inference(cnf_transformation,[],[f9])).
% 42.97/6.00  
% 42.97/6.00  fof(f7,axiom,(
% 42.97/6.00    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 42.97/6.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 42.97/6.00  
% 42.97/6.00  fof(f59,plain,(
% 42.97/6.00    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 42.97/6.00    inference(cnf_transformation,[],[f7])).
% 42.97/6.00  
% 42.97/6.00  fof(f85,plain,(
% 42.97/6.00    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k2_tarski(X0,X1))) )),
% 42.97/6.00    inference(definition_unfolding,[],[f61,f59])).
% 42.97/6.00  
% 42.97/6.00  fof(f19,axiom,(
% 42.97/6.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 42.97/6.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 42.97/6.00  
% 42.97/6.00  fof(f39,plain,(
% 42.97/6.00    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 42.97/6.00    inference(ennf_transformation,[],[f19])).
% 42.97/6.00  
% 42.97/6.00  fof(f40,plain,(
% 42.97/6.00    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 42.97/6.00    inference(flattening,[],[f39])).
% 42.97/6.00  
% 42.97/6.00  fof(f72,plain,(
% 42.97/6.00    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 42.97/6.00    inference(cnf_transformation,[],[f40])).
% 42.97/6.00  
% 42.97/6.00  fof(f13,axiom,(
% 42.97/6.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 42.97/6.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 42.97/6.00  
% 42.97/6.00  fof(f31,plain,(
% 42.97/6.00    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 42.97/6.00    inference(ennf_transformation,[],[f13])).
% 42.97/6.00  
% 42.97/6.00  fof(f32,plain,(
% 42.97/6.00    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 42.97/6.00    inference(flattening,[],[f31])).
% 42.97/6.00  
% 42.97/6.00  fof(f65,plain,(
% 42.97/6.00    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 42.97/6.00    inference(cnf_transformation,[],[f32])).
% 42.97/6.00  
% 42.97/6.00  fof(f86,plain,(
% 42.97/6.00    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k4_xboole_0(X2,X1)) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 42.97/6.00    inference(definition_unfolding,[],[f65,f59])).
% 42.97/6.00  
% 42.97/6.00  fof(f23,axiom,(
% 42.97/6.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)))),
% 42.97/6.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 42.97/6.00  
% 42.97/6.00  fof(f45,plain,(
% 42.97/6.00    ! [X0] : (! [X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 42.97/6.00    inference(ennf_transformation,[],[f23])).
% 42.97/6.00  
% 42.97/6.00  fof(f76,plain,(
% 42.97/6.00    ( ! [X0,X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 42.97/6.00    inference(cnf_transformation,[],[f45])).
% 42.97/6.00  
% 42.97/6.00  fof(f21,axiom,(
% 42.97/6.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)))),
% 42.97/6.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 42.97/6.00  
% 42.97/6.00  fof(f43,plain,(
% 42.97/6.00    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 42.97/6.00    inference(ennf_transformation,[],[f21])).
% 42.97/6.00  
% 42.97/6.00  fof(f74,plain,(
% 42.97/6.00    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 42.97/6.00    inference(cnf_transformation,[],[f43])).
% 42.97/6.00  
% 42.97/6.00  fof(f71,plain,(
% 42.97/6.00    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 42.97/6.00    inference(cnf_transformation,[],[f38])).
% 42.97/6.00  
% 42.97/6.00  fof(f81,plain,(
% 42.97/6.00    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)),
% 42.97/6.00    inference(cnf_transformation,[],[f52])).
% 42.97/6.00  
% 42.97/6.00  fof(f77,plain,(
% 42.97/6.00    v2_pre_topc(sK0)),
% 42.97/6.00    inference(cnf_transformation,[],[f52])).
% 42.97/6.00  
% 42.97/6.00  cnf(c_24,negated_conjecture,
% 42.97/6.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 42.97/6.00      inference(cnf_transformation,[],[f79]) ).
% 42.97/6.00  
% 42.97/6.00  cnf(c_775,plain,
% 42.97/6.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 42.97/6.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 42.97/6.00  
% 42.97/6.00  cnf(c_11,plain,
% 42.97/6.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 42.97/6.00      | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 42.97/6.00      inference(cnf_transformation,[],[f66]) ).
% 42.97/6.00  
% 42.97/6.00  cnf(c_787,plain,
% 42.97/6.00      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
% 42.97/6.00      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 42.97/6.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 42.97/6.00  
% 42.97/6.00  cnf(c_5979,plain,
% 42.97/6.00      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
% 42.97/6.00      inference(superposition,[status(thm)],[c_775,c_787]) ).
% 42.97/6.00  
% 42.97/6.00  cnf(c_23,negated_conjecture,
% 42.97/6.00      ( v4_pre_topc(sK1,sK0)
% 42.97/6.00      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 42.97/6.00      inference(cnf_transformation,[],[f80]) ).
% 42.97/6.00  
% 42.97/6.00  cnf(c_776,plain,
% 42.97/6.00      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 42.97/6.00      | v4_pre_topc(sK1,sK0) = iProver_top ),
% 42.97/6.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 42.97/6.00  
% 42.97/6.00  cnf(c_6250,plain,
% 42.97/6.00      ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 42.97/6.00      | v4_pre_topc(sK1,sK0) = iProver_top ),
% 42.97/6.00      inference(demodulation,[status(thm)],[c_5979,c_776]) ).
% 42.97/6.00  
% 42.97/6.00  cnf(c_16,plain,
% 42.97/6.00      ( ~ v4_pre_topc(X0,X1)
% 42.97/6.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 42.97/6.00      | ~ l1_pre_topc(X1)
% 42.97/6.00      | k2_pre_topc(X1,X0) = X0 ),
% 42.97/6.00      inference(cnf_transformation,[],[f70]) ).
% 42.97/6.00  
% 42.97/6.00  cnf(c_783,plain,
% 42.97/6.00      ( k2_pre_topc(X0,X1) = X1
% 42.97/6.00      | v4_pre_topc(X1,X0) != iProver_top
% 42.97/6.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 42.97/6.00      | l1_pre_topc(X0) != iProver_top ),
% 42.97/6.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 42.97/6.00  
% 42.97/6.00  cnf(c_7253,plain,
% 42.97/6.00      ( k2_pre_topc(sK0,sK1) = sK1
% 42.97/6.00      | v4_pre_topc(sK1,sK0) != iProver_top
% 42.97/6.00      | l1_pre_topc(sK0) != iProver_top ),
% 42.97/6.00      inference(superposition,[status(thm)],[c_775,c_783]) ).
% 42.97/6.00  
% 42.97/6.00  cnf(c_25,negated_conjecture,
% 42.97/6.00      ( l1_pre_topc(sK0) ),
% 42.97/6.00      inference(cnf_transformation,[],[f78]) ).
% 42.97/6.00  
% 42.97/6.00  cnf(c_28,plain,
% 42.97/6.00      ( l1_pre_topc(sK0) = iProver_top ),
% 42.97/6.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 42.97/6.00  
% 42.97/6.00  cnf(c_8028,plain,
% 42.97/6.00      ( v4_pre_topc(sK1,sK0) != iProver_top
% 42.97/6.00      | k2_pre_topc(sK0,sK1) = sK1 ),
% 42.97/6.00      inference(global_propositional_subsumption,
% 42.97/6.00                [status(thm)],
% 42.97/6.00                [c_7253,c_28]) ).
% 42.97/6.00  
% 42.97/6.00  cnf(c_8029,plain,
% 42.97/6.00      ( k2_pre_topc(sK0,sK1) = sK1
% 42.97/6.00      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 42.97/6.00      inference(renaming,[status(thm)],[c_8028]) ).
% 42.97/6.00  
% 42.97/6.00  cnf(c_8034,plain,
% 42.97/6.00      ( k2_pre_topc(sK0,sK1) = sK1
% 42.97/6.00      | k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 42.97/6.00      inference(superposition,[status(thm)],[c_6250,c_8029]) ).
% 42.97/6.00  
% 42.97/6.00  cnf(c_13,plain,
% 42.97/6.00      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
% 42.97/6.00      inference(cnf_transformation,[],[f87]) ).
% 42.97/6.00  
% 42.97/6.00  cnf(c_8044,plain,
% 42.97/6.00      ( k2_pre_topc(sK0,sK1) = sK1
% 42.97/6.00      | k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
% 42.97/6.00      inference(superposition,[status(thm)],[c_8034,c_13]) ).
% 42.97/6.00  
% 42.97/6.00  cnf(c_3,plain,
% 42.97/6.00      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 42.97/6.00      inference(cnf_transformation,[],[f56]) ).
% 42.97/6.00  
% 42.97/6.00  cnf(c_792,plain,
% 42.97/6.00      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 42.97/6.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 42.97/6.00  
% 42.97/6.00  cnf(c_1588,plain,
% 42.97/6.00      ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) = iProver_top ),
% 42.97/6.00      inference(superposition,[status(thm)],[c_13,c_792]) ).
% 42.97/6.00  
% 42.97/6.00  cnf(c_14,plain,
% 42.97/6.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 42.97/6.00      inference(cnf_transformation,[],[f69]) ).
% 42.97/6.00  
% 42.97/6.00  cnf(c_785,plain,
% 42.97/6.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 42.97/6.00      | r1_tarski(X0,X1) != iProver_top ),
% 42.97/6.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 42.97/6.00  
% 42.97/6.00  cnf(c_9,plain,
% 42.97/6.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 42.97/6.00      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 42.97/6.00      inference(cnf_transformation,[],[f64]) ).
% 42.97/6.00  
% 42.97/6.00  cnf(c_789,plain,
% 42.97/6.00      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 42.97/6.00      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 42.97/6.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 42.97/6.00  
% 42.97/6.00  cnf(c_3616,plain,
% 42.97/6.00      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 42.97/6.00      | r1_tarski(X1,X0) != iProver_top ),
% 42.97/6.00      inference(superposition,[status(thm)],[c_785,c_789]) ).
% 42.97/6.00  
% 42.97/6.00  cnf(c_3712,plain,
% 42.97/6.00      ( k3_subset_1(X0,k3_subset_1(X0,k1_setfam_1(k2_tarski(X0,X1)))) = k1_setfam_1(k2_tarski(X0,X1)) ),
% 42.97/6.00      inference(superposition,[status(thm)],[c_1588,c_3616]) ).
% 42.97/6.00  
% 42.97/6.00  cnf(c_8543,plain,
% 42.97/6.00      ( k2_pre_topc(sK0,sK1) = sK1
% 42.97/6.00      | k3_subset_1(sK1,k3_subset_1(sK1,k4_xboole_0(sK1,k2_tops_1(sK0,sK1)))) = k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))) ),
% 42.97/6.00      inference(superposition,[status(thm)],[c_8044,c_3712]) ).
% 42.97/6.00  
% 42.97/6.00  cnf(c_7,plain,
% 42.97/6.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 42.97/6.00      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 42.97/6.00      inference(cnf_transformation,[],[f62]) ).
% 42.97/6.00  
% 42.97/6.00  cnf(c_791,plain,
% 42.97/6.00      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
% 42.97/6.00      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 42.97/6.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 42.97/6.00  
% 42.97/6.00  cnf(c_4241,plain,
% 42.97/6.00      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
% 42.97/6.00      | r1_tarski(X1,X0) != iProver_top ),
% 42.97/6.00      inference(superposition,[status(thm)],[c_785,c_791]) ).
% 42.97/6.00  
% 42.97/6.00  cnf(c_5576,plain,
% 42.97/6.00      ( k3_subset_1(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 42.97/6.00      inference(superposition,[status(thm)],[c_792,c_4241]) ).
% 42.97/6.00  
% 42.97/6.00  cnf(c_5597,plain,
% 42.97/6.00      ( k3_subset_1(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
% 42.97/6.00      inference(light_normalisation,[status(thm)],[c_5576,c_13]) ).
% 42.97/6.00  
% 42.97/6.00  cnf(c_8590,plain,
% 42.97/6.00      ( k2_pre_topc(sK0,sK1) = sK1
% 42.97/6.00      | k3_subset_1(sK1,k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1)))) = k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))) ),
% 42.97/6.00      inference(demodulation,[status(thm)],[c_8543,c_5597]) ).
% 42.97/6.00  
% 42.97/6.00  cnf(c_20,plain,
% 42.97/6.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 42.97/6.00      | r1_tarski(k1_tops_1(X1,X0),X0)
% 42.97/6.00      | ~ l1_pre_topc(X1) ),
% 42.97/6.00      inference(cnf_transformation,[],[f75]) ).
% 42.97/6.00  
% 42.97/6.00  cnf(c_779,plain,
% 42.97/6.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 42.97/6.00      | r1_tarski(k1_tops_1(X1,X0),X0) = iProver_top
% 42.97/6.00      | l1_pre_topc(X1) != iProver_top ),
% 42.97/6.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 42.97/6.00  
% 42.97/6.00  cnf(c_2260,plain,
% 42.97/6.00      ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top
% 42.97/6.00      | l1_pre_topc(sK0) != iProver_top ),
% 42.97/6.00      inference(superposition,[status(thm)],[c_775,c_779]) ).
% 42.97/6.00  
% 42.97/6.00  cnf(c_29,plain,
% 42.97/6.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 42.97/6.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 42.97/6.00  
% 42.97/6.00  cnf(c_1011,plain,
% 42.97/6.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 42.97/6.00      | r1_tarski(k1_tops_1(sK0,sK1),sK1)
% 42.97/6.00      | ~ l1_pre_topc(sK0) ),
% 42.97/6.00      inference(instantiation,[status(thm)],[c_20]) ).
% 42.97/6.00  
% 42.97/6.00  cnf(c_1012,plain,
% 42.97/6.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 42.97/6.00      | r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top
% 42.97/6.00      | l1_pre_topc(sK0) != iProver_top ),
% 42.97/6.00      inference(predicate_to_equality,[status(thm)],[c_1011]) ).
% 42.97/6.00  
% 42.97/6.00  cnf(c_2681,plain,
% 42.97/6.00      ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
% 42.97/6.00      inference(global_propositional_subsumption,
% 42.97/6.00                [status(thm)],
% 42.97/6.00                [c_2260,c_28,c_29,c_1012]) ).
% 42.97/6.00  
% 42.97/6.00  cnf(c_5577,plain,
% 42.97/6.00      ( k3_subset_1(sK1,k1_tops_1(sK0,sK1)) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
% 42.97/6.00      inference(superposition,[status(thm)],[c_2681,c_4241]) ).
% 42.97/6.00  
% 42.97/6.00  cnf(c_3711,plain,
% 42.97/6.00      ( k3_subset_1(sK1,k3_subset_1(sK1,k1_tops_1(sK0,sK1))) = k1_tops_1(sK0,sK1) ),
% 42.97/6.00      inference(superposition,[status(thm)],[c_2681,c_3616]) ).
% 42.97/6.00  
% 42.97/6.00  cnf(c_5604,plain,
% 42.97/6.00      ( k3_subset_1(sK1,k4_xboole_0(sK1,k1_tops_1(sK0,sK1))) = k1_tops_1(sK0,sK1) ),
% 42.97/6.00      inference(demodulation,[status(thm)],[c_5577,c_3711]) ).
% 42.97/6.00  
% 42.97/6.00  cnf(c_7201,plain,
% 42.97/6.00      ( k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))) = k1_tops_1(sK0,sK1) ),
% 42.97/6.00      inference(superposition,[status(thm)],[c_5604,c_5597]) ).
% 42.97/6.00  
% 42.97/6.00  cnf(c_108625,plain,
% 42.97/6.00      ( k2_pre_topc(sK0,sK1) = sK1
% 42.97/6.00      | k3_subset_1(sK1,k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1)))) = k1_tops_1(sK0,sK1) ),
% 42.97/6.00      inference(light_normalisation,[status(thm)],[c_8590,c_7201]) ).
% 42.97/6.00  
% 42.97/6.00  cnf(c_108633,plain,
% 42.97/6.00      ( k2_pre_topc(sK0,sK1) = sK1
% 42.97/6.00      | k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k3_subset_1(sK1,k1_tops_1(sK0,sK1)) ),
% 42.97/6.00      inference(superposition,[status(thm)],[c_108625,c_3712]) ).
% 42.97/6.00  
% 42.97/6.00  cnf(c_108645,plain,
% 42.97/6.00      ( k2_pre_topc(sK0,sK1) = sK1
% 42.97/6.00      | k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
% 42.97/6.00      inference(light_normalisation,[status(thm)],[c_108633,c_5577]) ).
% 42.97/6.00  
% 42.97/6.00  cnf(c_5,plain,
% 42.97/6.00      ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
% 42.97/6.00      inference(cnf_transformation,[],[f60]) ).
% 42.97/6.00  
% 42.97/6.00  cnf(c_0,plain,
% 42.97/6.00      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 42.97/6.00      inference(cnf_transformation,[],[f82]) ).
% 42.97/6.00  
% 42.97/6.00  cnf(c_813,plain,
% 42.97/6.00      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k4_xboole_0(X0,X1) ),
% 42.97/6.00      inference(light_normalisation,[status(thm)],[c_0,c_13]) ).
% 42.97/6.00  
% 42.97/6.00  cnf(c_2523,plain,
% 42.97/6.00      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0))) = k4_xboole_0(X0,X1) ),
% 42.97/6.00      inference(superposition,[status(thm)],[c_5,c_813]) ).
% 42.97/6.00  
% 42.97/6.00  cnf(c_109370,plain,
% 42.97/6.00      ( k2_pre_topc(sK0,sK1) = sK1
% 42.97/6.00      | k5_xboole_0(k2_tops_1(sK0,sK1),k4_xboole_0(sK1,k1_tops_1(sK0,sK1))) = k4_xboole_0(k2_tops_1(sK0,sK1),sK1) ),
% 42.97/6.00      inference(superposition,[status(thm)],[c_108645,c_2523]) ).
% 42.97/6.00  
% 42.97/6.00  cnf(c_130674,plain,
% 42.97/6.00      ( k2_pre_topc(sK0,sK1) = sK1
% 42.97/6.00      | k5_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) = k4_xboole_0(k2_tops_1(sK0,sK1),sK1) ),
% 42.97/6.00      inference(superposition,[status(thm)],[c_8034,c_109370]) ).
% 42.97/6.00  
% 42.97/6.00  cnf(c_2,plain,
% 42.97/6.00      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 42.97/6.00      inference(cnf_transformation,[],[f84]) ).
% 42.97/6.00  
% 42.97/6.00  cnf(c_4,plain,
% 42.97/6.00      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 42.97/6.00      inference(cnf_transformation,[],[f57]) ).
% 42.97/6.00  
% 42.97/6.00  cnf(c_805,plain,
% 42.97/6.00      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 42.97/6.00      inference(light_normalisation,[status(thm)],[c_2,c_4]) ).
% 42.97/6.00  
% 42.97/6.00  cnf(c_1427,plain,
% 42.97/6.00      ( k1_setfam_1(k2_tarski(X0,X0)) = k4_xboole_0(X0,k1_xboole_0) ),
% 42.97/6.00      inference(superposition,[status(thm)],[c_805,c_13]) ).
% 42.97/6.00  
% 42.97/6.00  cnf(c_1439,plain,
% 42.97/6.00      ( k1_setfam_1(k2_tarski(X0,X0)) = X0 ),
% 42.97/6.00      inference(light_normalisation,[status(thm)],[c_1427,c_4]) ).
% 42.97/6.00  
% 42.97/6.00  cnf(c_2520,plain,
% 42.97/6.00      ( k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0) ),
% 42.97/6.00      inference(superposition,[status(thm)],[c_1439,c_813]) ).
% 42.97/6.00  
% 42.97/6.00  cnf(c_2536,plain,
% 42.97/6.00      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 42.97/6.00      inference(light_normalisation,[status(thm)],[c_2520,c_805]) ).
% 42.97/6.00  
% 42.97/6.00  cnf(c_130675,plain,
% 42.97/6.00      ( k2_pre_topc(sK0,sK1) = sK1
% 42.97/6.00      | k4_xboole_0(k2_tops_1(sK0,sK1),sK1) = k1_xboole_0 ),
% 42.97/6.00      inference(demodulation,[status(thm)],[c_130674,c_2536]) ).
% 42.97/6.00  
% 42.97/6.00  cnf(c_6,plain,
% 42.97/6.00      ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k2_tarski(X0,X1)) ),
% 42.97/6.00      inference(cnf_transformation,[],[f85]) ).
% 42.97/6.00  
% 42.97/6.00  cnf(c_130736,plain,
% 42.97/6.00      ( k2_pre_topc(sK0,sK1) = sK1
% 42.97/6.00      | k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k5_xboole_0(sK1,k1_xboole_0) ),
% 42.97/6.00      inference(superposition,[status(thm)],[c_130675,c_6]) ).
% 42.97/6.00  
% 42.97/6.00  cnf(c_1428,plain,
% 42.97/6.00      ( k1_setfam_1(k2_tarski(X0,k1_xboole_0)) = k4_xboole_0(X0,X0) ),
% 42.97/6.00      inference(superposition,[status(thm)],[c_4,c_13]) ).
% 42.97/6.00  
% 42.97/6.00  cnf(c_1436,plain,
% 42.97/6.00      ( k1_setfam_1(k2_tarski(X0,k1_xboole_0)) = k1_xboole_0 ),
% 42.97/6.00      inference(light_normalisation,[status(thm)],[c_1428,c_805]) ).
% 42.97/6.00  
% 42.97/6.00  cnf(c_2521,plain,
% 42.97/6.00      ( k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
% 42.97/6.00      inference(superposition,[status(thm)],[c_1436,c_813]) ).
% 42.97/6.00  
% 42.97/6.00  cnf(c_2530,plain,
% 42.97/6.00      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 42.97/6.00      inference(light_normalisation,[status(thm)],[c_2521,c_4]) ).
% 42.97/6.00  
% 42.97/6.00  cnf(c_17,plain,
% 42.97/6.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 42.97/6.00      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 42.97/6.00      | ~ l1_pre_topc(X1) ),
% 42.97/6.00      inference(cnf_transformation,[],[f72]) ).
% 42.97/6.00  
% 42.97/6.00  cnf(c_782,plain,
% 42.97/6.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 42.97/6.00      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 42.97/6.00      | l1_pre_topc(X1) != iProver_top ),
% 42.97/6.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 42.97/6.00  
% 42.97/6.00  cnf(c_10,plain,
% 42.97/6.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 42.97/6.00      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 42.97/6.00      | k5_xboole_0(X0,k4_xboole_0(X2,X0)) = k4_subset_1(X1,X0,X2) ),
% 42.97/6.00      inference(cnf_transformation,[],[f86]) ).
% 42.97/6.00  
% 42.97/6.00  cnf(c_788,plain,
% 42.97/6.00      ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k4_subset_1(X2,X0,X1)
% 42.97/6.00      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 42.97/6.00      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 42.97/6.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 42.97/6.00  
% 42.97/6.00  cnf(c_862,plain,
% 42.97/6.00      ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
% 42.97/6.00      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
% 42.97/6.00      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 42.97/6.00      inference(light_normalisation,[status(thm)],[c_788,c_6]) ).
% 42.97/6.00  
% 42.97/6.00  cnf(c_20978,plain,
% 42.97/6.00      ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k3_tarski(k2_tarski(sK1,X0))
% 42.97/6.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 42.97/6.00      inference(superposition,[status(thm)],[c_775,c_862]) ).
% 42.97/6.00  
% 42.97/6.00  cnf(c_21783,plain,
% 42.97/6.00      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0)))
% 42.97/6.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 42.97/6.00      | l1_pre_topc(sK0) != iProver_top ),
% 42.97/6.00      inference(superposition,[status(thm)],[c_782,c_20978]) ).
% 42.97/6.00  
% 42.97/6.00  cnf(c_22620,plain,
% 42.97/6.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 42.97/6.00      | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0))) ),
% 42.97/6.00      inference(global_propositional_subsumption,
% 42.97/6.00                [status(thm)],
% 42.97/6.00                [c_21783,c_28]) ).
% 42.97/6.00  
% 42.97/6.00  cnf(c_22621,plain,
% 42.97/6.00      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0)))
% 42.97/6.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 42.97/6.00      inference(renaming,[status(thm)],[c_22620]) ).
% 42.97/6.00  
% 42.97/6.00  cnf(c_22631,plain,
% 42.97/6.00      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
% 42.97/6.00      inference(superposition,[status(thm)],[c_775,c_22621]) ).
% 42.97/6.00  
% 42.97/6.00  cnf(c_21,plain,
% 42.97/6.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 42.97/6.00      | ~ l1_pre_topc(X1)
% 42.97/6.00      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
% 42.97/6.00      inference(cnf_transformation,[],[f76]) ).
% 42.97/6.00  
% 42.97/6.00  cnf(c_778,plain,
% 42.97/6.00      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
% 42.97/6.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 42.97/6.00      | l1_pre_topc(X0) != iProver_top ),
% 42.97/6.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 42.97/6.00  
% 42.97/6.00  cnf(c_1198,plain,
% 42.97/6.00      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
% 42.97/6.00      | l1_pre_topc(sK0) != iProver_top ),
% 42.97/6.00      inference(superposition,[status(thm)],[c_775,c_778]) ).
% 42.97/6.00  
% 42.97/6.00  cnf(c_1077,plain,
% 42.97/6.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 42.97/6.00      | ~ l1_pre_topc(sK0)
% 42.97/6.00      | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 42.97/6.00      inference(instantiation,[status(thm)],[c_21]) ).
% 42.97/6.00  
% 42.97/6.00  cnf(c_1607,plain,
% 42.97/6.00      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 42.97/6.00      inference(global_propositional_subsumption,
% 42.97/6.00                [status(thm)],
% 42.97/6.00                [c_1198,c_25,c_24,c_1077]) ).
% 42.97/6.00  
% 42.97/6.00  cnf(c_22639,plain,
% 42.97/6.00      ( k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k2_pre_topc(sK0,sK1) ),
% 42.97/6.00      inference(light_normalisation,[status(thm)],[c_22631,c_1607]) ).
% 42.97/6.00  
% 42.97/6.00  cnf(c_130756,plain,
% 42.97/6.00      ( k2_pre_topc(sK0,sK1) = sK1 ),
% 42.97/6.00      inference(demodulation,[status(thm)],[c_130736,c_2530,c_22639]) ).
% 42.97/6.00  
% 42.97/6.00  cnf(c_19,plain,
% 42.97/6.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 42.97/6.00      | ~ l1_pre_topc(X1)
% 42.97/6.00      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
% 42.97/6.00      inference(cnf_transformation,[],[f74]) ).
% 42.97/6.00  
% 42.97/6.00  cnf(c_780,plain,
% 42.97/6.00      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
% 42.97/6.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 42.97/6.00      | l1_pre_topc(X0) != iProver_top ),
% 42.97/6.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 42.97/6.00  
% 42.97/6.00  cnf(c_3215,plain,
% 42.97/6.00      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 42.97/6.00      | l1_pre_topc(sK0) != iProver_top ),
% 42.97/6.00      inference(superposition,[status(thm)],[c_775,c_780]) ).
% 42.97/6.00  
% 42.97/6.00  cnf(c_1107,plain,
% 42.97/6.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 42.97/6.00      | ~ l1_pre_topc(sK0)
% 42.97/6.00      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 42.97/6.00      inference(instantiation,[status(thm)],[c_19]) ).
% 42.97/6.00  
% 42.97/6.00  cnf(c_3704,plain,
% 42.97/6.00      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 42.97/6.00      inference(global_propositional_subsumption,
% 42.97/6.00                [status(thm)],
% 42.97/6.00                [c_3215,c_25,c_24,c_1107]) ).
% 42.97/6.00  
% 42.97/6.00  cnf(c_130981,plain,
% 42.97/6.00      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 42.97/6.00      inference(demodulation,[status(thm)],[c_130756,c_3704]) ).
% 42.97/6.00  
% 42.97/6.00  cnf(c_15,plain,
% 42.97/6.00      ( v4_pre_topc(X0,X1)
% 42.97/6.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 42.97/6.00      | ~ l1_pre_topc(X1)
% 42.97/6.00      | ~ v2_pre_topc(X1)
% 42.97/6.00      | k2_pre_topc(X1,X0) != X0 ),
% 42.97/6.00      inference(cnf_transformation,[],[f71]) ).
% 42.97/6.00  
% 42.97/6.00  cnf(c_1074,plain,
% 42.97/6.00      ( v4_pre_topc(sK1,sK0)
% 42.97/6.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 42.97/6.00      | ~ l1_pre_topc(sK0)
% 42.97/6.00      | ~ v2_pre_topc(sK0)
% 42.97/6.00      | k2_pre_topc(sK0,sK1) != sK1 ),
% 42.97/6.00      inference(instantiation,[status(thm)],[c_15]) ).
% 42.97/6.00  
% 42.97/6.00  cnf(c_22,negated_conjecture,
% 42.97/6.00      ( ~ v4_pre_topc(sK1,sK0)
% 42.97/6.00      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
% 42.97/6.00      inference(cnf_transformation,[],[f81]) ).
% 42.97/6.00  
% 42.97/6.00  cnf(c_26,negated_conjecture,
% 42.97/6.00      ( v2_pre_topc(sK0) ),
% 42.97/6.00      inference(cnf_transformation,[],[f77]) ).
% 42.97/6.00  
% 42.97/6.00  cnf(contradiction,plain,
% 42.97/6.00      ( $false ),
% 42.97/6.00      inference(minisat,
% 42.97/6.00                [status(thm)],
% 42.97/6.00                [c_130981,c_130756,c_1074,c_22,c_24,c_25,c_26]) ).
% 42.97/6.00  
% 42.97/6.00  
% 42.97/6.00  % SZS output end CNFRefutation for theBenchmark.p
% 42.97/6.00  
% 42.97/6.00  ------                               Statistics
% 42.97/6.00  
% 42.97/6.00  ------ Selected
% 42.97/6.00  
% 42.97/6.00  total_time:                             5.218
% 42.97/6.00  
%------------------------------------------------------------------------------
