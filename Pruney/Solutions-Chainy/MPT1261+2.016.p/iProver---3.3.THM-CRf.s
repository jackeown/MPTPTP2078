%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:14:27 EST 2020

% Result     : Theorem 3.74s
% Output     : CNFRefutation 3.74s
% Verified   : 
% Statistics : Number of formulae       :  150 ( 767 expanded)
%              Number of clauses        :   81 ( 223 expanded)
%              Number of leaves         :   20 ( 179 expanded)
%              Depth                    :   20
%              Number of atoms          :  347 (2862 expanded)
%              Number of equality atoms :  173 (1027 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1)
            | ~ v4_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1)
            | ~ v4_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f37])).

fof(f40,plain,(
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

fof(f39,plain,
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

fof(f41,plain,
    ( ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f38,f40,f39])).

fof(f64,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f41])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f55,f45])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f63,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f68,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) ),
    inference(definition_unfolding,[],[f51,f45,f45])).

fof(f65,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => r1_tarski(k2_tops_1(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_tops_1(X0,X1),X1)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f13,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f57,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f22])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f9,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f67,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f52,f45])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f54,f67])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f69,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
    inference(definition_unfolding,[],[f46,f67])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f71,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f50,f45])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f35])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f75,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f42])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f28,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f62,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f66,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_800,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X0,k3_xboole_0(X0,X2)) = k7_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_808,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k7_subset_1(X2,X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_5735,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k3_xboole_0(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_800,c_808])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_803,plain,
    ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1155,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_800,c_803])).

cnf(c_21,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1036,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1428,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1155,c_21,c_20,c_1036])).

cnf(c_6198,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,k2_tops_1(sK0,sK1))) = k1_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_5735,c_1428])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_6983,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tops_1(sK0,sK1))) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_6198,c_0])).

cnf(c_19,negated_conjecture,
    ( v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_801,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_6183,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tops_1(sK0,sK1))) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5735,c_801])).

cnf(c_7176,plain,
    ( k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6983,c_6183])).

cnf(c_16,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k2_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_804,plain,
    ( v4_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(k2_tops_1(X1,X0),X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1957,plain,
    ( v4_pre_topc(sK1,sK0) != iProver_top
    | r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_800,c_804])).

cnf(c_24,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2495,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1957,c_24])).

cnf(c_2496,plain,
    ( v4_pre_topc(sK1,sK0) != iProver_top
    | r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(renaming,[status(thm)],[c_2495])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_812,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2501,plain,
    ( k3_xboole_0(k2_tops_1(sK0,sK1),sK1) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2496,c_812])).

cnf(c_7534,plain,
    ( k3_xboole_0(k2_tops_1(sK0,sK1),sK1) = k2_tops_1(sK0,sK1)
    | k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_7176,c_2501])).

cnf(c_9,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_12,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1257,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_9,c_12])).

cnf(c_1572,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_1257,c_12])).

cnf(c_8803,plain,
    ( k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_7534,c_1572])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_807,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k5_xboole_0(X2,k5_xboole_0(X0,k3_xboole_0(X0,X2))) = k4_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_809,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k4_subset_1(X2,X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_6046,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(X0,k3_xboole_0(X0,sK1))) = k4_subset_1(u1_struct_0(sK0),sK1,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_800,c_809])).

cnf(c_6326,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(k2_tops_1(sK0,X0),k3_xboole_0(k2_tops_1(sK0,X0),sK1))) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_807,c_6046])).

cnf(c_6993,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | k5_xboole_0(sK1,k5_xboole_0(k2_tops_1(sK0,X0),k3_xboole_0(k2_tops_1(sK0,X0),sK1))) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6326,c_24])).

cnf(c_6994,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(k2_tops_1(sK0,X0),k3_xboole_0(k2_tops_1(sK0,X0),sK1))) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_6993])).

cnf(c_7002,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(k2_tops_1(sK0,sK1),k3_xboole_0(k2_tops_1(sK0,sK1),sK1))) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_800,c_6994])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_805,plain,
    ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3349,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_800,c_805])).

cnf(c_1033,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_3542,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3349,c_21,c_20,c_1033])).

cnf(c_7004,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(k2_tops_1(sK0,sK1),k3_xboole_0(k2_tops_1(sK0,sK1),sK1))) = k2_pre_topc(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_7002,c_3542])).

cnf(c_7060,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(k2_tops_1(sK0,sK1),k3_xboole_0(sK1,k2_tops_1(sK0,sK1)))) = k2_pre_topc(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_1572,c_7004])).

cnf(c_8815,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))) = k2_pre_topc(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_8803,c_7060])).

cnf(c_6,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_811,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2346,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_811,c_812])).

cnf(c_4,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_2772,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) = X0 ),
    inference(demodulation,[status(thm)],[c_2346,c_4])).

cnf(c_8,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1260,plain,
    ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8,c_4])).

cnf(c_2774,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_2772,c_1260])).

cnf(c_2786,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2346,c_1572])).

cnf(c_3059,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k1_xboole_0))) = k3_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2786,c_0])).

cnf(c_3061,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k1_xboole_0))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3059,c_2786])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_813,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2345,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_813,c_812])).

cnf(c_3063,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3061,c_2345,c_2774])).

cnf(c_8824,plain,
    ( k2_pre_topc(sK0,sK1) = sK1 ),
    inference(demodulation,[status(thm)],[c_8815,c_2774,c_3063])).

cnf(c_14,plain,
    ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_806,plain,
    ( v4_pre_topc(k2_pre_topc(X0,X1),X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_4016,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_800,c_806])).

cnf(c_22,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_23,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_25,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_982,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_983,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_982])).

cnf(c_4606,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4016,c_23,c_24,c_25,c_983])).

cnf(c_10081,plain,
    ( v4_pre_topc(sK1,sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8824,c_4606])).

cnf(c_18,negated_conjecture,
    ( ~ v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_802,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_6184,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tops_1(sK0,sK1))) != k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5735,c_802])).

cnf(c_7177,plain,
    ( k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6983,c_6184])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10081,c_8803,c_7177])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:45:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.74/0.96  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.74/0.96  
% 3.74/0.96  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.74/0.96  
% 3.74/0.96  ------  iProver source info
% 3.74/0.96  
% 3.74/0.96  git: date: 2020-06-30 10:37:57 +0100
% 3.74/0.96  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.74/0.96  git: non_committed_changes: false
% 3.74/0.96  git: last_make_outside_of_git: false
% 3.74/0.96  
% 3.74/0.96  ------ 
% 3.74/0.96  ------ Parsing...
% 3.74/0.96  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.74/0.96  
% 3.74/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 3.74/0.96  
% 3.74/0.96  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.74/0.96  
% 3.74/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.74/0.96  ------ Proving...
% 3.74/0.96  ------ Problem Properties 
% 3.74/0.96  
% 3.74/0.96  
% 3.74/0.96  clauses                                 22
% 3.74/0.96  conjectures                             5
% 3.74/0.96  EPR                                     5
% 3.74/0.96  Horn                                    21
% 3.74/0.96  unary                                   11
% 3.74/0.96  binary                                  4
% 3.74/0.96  lits                                    42
% 3.74/0.96  lits eq                                 13
% 3.74/0.96  fd_pure                                 0
% 3.74/0.96  fd_pseudo                               0
% 3.74/0.96  fd_cond                                 0
% 3.74/0.96  fd_pseudo_cond                          1
% 3.74/0.96  AC symbols                              0
% 3.74/0.96  
% 3.74/0.96  ------ Input Options Time Limit: Unbounded
% 3.74/0.96  
% 3.74/0.96  
% 3.74/0.96  ------ 
% 3.74/0.96  Current options:
% 3.74/0.96  ------ 
% 3.74/0.96  
% 3.74/0.96  
% 3.74/0.96  
% 3.74/0.96  
% 3.74/0.96  ------ Proving...
% 3.74/0.96  
% 3.74/0.96  
% 3.74/0.96  % SZS status Theorem for theBenchmark.p
% 3.74/0.96  
% 3.74/0.96  % SZS output start CNFRefutation for theBenchmark.p
% 3.74/0.96  
% 3.74/0.96  fof(f19,conjecture,(
% 3.74/0.96    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 3.74/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.74/0.96  
% 3.74/0.96  fof(f20,negated_conjecture,(
% 3.74/0.96    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 3.74/0.96    inference(negated_conjecture,[],[f19])).
% 3.74/0.96  
% 3.74/0.96  fof(f33,plain,(
% 3.74/0.96    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 3.74/0.96    inference(ennf_transformation,[],[f20])).
% 3.74/0.96  
% 3.74/0.96  fof(f34,plain,(
% 3.74/0.96    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.74/0.96    inference(flattening,[],[f33])).
% 3.74/0.96  
% 3.74/0.96  fof(f37,plain,(
% 3.74/0.96    ? [X0] : (? [X1] : (((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.74/0.96    inference(nnf_transformation,[],[f34])).
% 3.74/0.96  
% 3.74/0.96  fof(f38,plain,(
% 3.74/0.96    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.74/0.96    inference(flattening,[],[f37])).
% 3.74/0.96  
% 3.74/0.96  fof(f40,plain,(
% 3.74/0.96    ( ! [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) != k2_tops_1(X0,sK1) | ~v4_pre_topc(sK1,X0)) & (k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) = k2_tops_1(X0,sK1) | v4_pre_topc(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.74/0.96    introduced(choice_axiom,[])).
% 3.74/0.96  
% 3.74/0.96  fof(f39,plain,(
% 3.74/0.96    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) != k2_tops_1(sK0,X1) | ~v4_pre_topc(X1,sK0)) & (k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) = k2_tops_1(sK0,X1) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 3.74/0.96    introduced(choice_axiom,[])).
% 3.74/0.96  
% 3.74/0.96  fof(f41,plain,(
% 3.74/0.96    ((k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)) & (k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 3.74/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f38,f40,f39])).
% 3.74/0.96  
% 3.74/0.96  fof(f64,plain,(
% 3.74/0.96    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.74/0.96    inference(cnf_transformation,[],[f41])).
% 3.74/0.96  
% 3.74/0.96  fof(f12,axiom,(
% 3.74/0.96    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 3.74/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.74/0.96  
% 3.74/0.96  fof(f24,plain,(
% 3.74/0.96    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.74/0.96    inference(ennf_transformation,[],[f12])).
% 3.74/0.96  
% 3.74/0.96  fof(f55,plain,(
% 3.74/0.96    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.74/0.96    inference(cnf_transformation,[],[f24])).
% 3.74/0.96  
% 3.74/0.96  fof(f2,axiom,(
% 3.74/0.96    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.74/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.74/0.96  
% 3.74/0.96  fof(f45,plain,(
% 3.74/0.96    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.74/0.96    inference(cnf_transformation,[],[f2])).
% 3.74/0.96  
% 3.74/0.96  fof(f73,plain,(
% 3.74/0.96    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.74/0.96    inference(definition_unfolding,[],[f55,f45])).
% 3.74/0.96  
% 3.74/0.96  fof(f18,axiom,(
% 3.74/0.96    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)))),
% 3.74/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.74/0.96  
% 3.74/0.96  fof(f32,plain,(
% 3.74/0.96    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.74/0.96    inference(ennf_transformation,[],[f18])).
% 3.74/0.96  
% 3.74/0.96  fof(f61,plain,(
% 3.74/0.96    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.74/0.96    inference(cnf_transformation,[],[f32])).
% 3.74/0.96  
% 3.74/0.96  fof(f63,plain,(
% 3.74/0.96    l1_pre_topc(sK0)),
% 3.74/0.96    inference(cnf_transformation,[],[f41])).
% 3.74/0.96  
% 3.74/0.96  fof(f8,axiom,(
% 3.74/0.96    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 3.74/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.74/0.96  
% 3.74/0.96  fof(f51,plain,(
% 3.74/0.96    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 3.74/0.96    inference(cnf_transformation,[],[f8])).
% 3.74/0.96  
% 3.74/0.96  fof(f68,plain,(
% 3.74/0.96    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) )),
% 3.74/0.96    inference(definition_unfolding,[],[f51,f45,f45])).
% 3.74/0.96  
% 3.74/0.96  fof(f65,plain,(
% 3.74/0.96    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)),
% 3.74/0.96    inference(cnf_transformation,[],[f41])).
% 3.74/0.96  
% 3.74/0.96  fof(f17,axiom,(
% 3.74/0.96    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => r1_tarski(k2_tops_1(X0,X1),X1))))),
% 3.74/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.74/0.96  
% 3.74/0.96  fof(f30,plain,(
% 3.74/0.96    ! [X0] : (! [X1] : ((r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.74/0.96    inference(ennf_transformation,[],[f17])).
% 3.74/0.96  
% 3.74/0.96  fof(f31,plain,(
% 3.74/0.96    ! [X0] : (! [X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.74/0.96    inference(flattening,[],[f30])).
% 3.74/0.96  
% 3.74/0.96  fof(f60,plain,(
% 3.74/0.96    ( ! [X0,X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.74/0.96    inference(cnf_transformation,[],[f31])).
% 3.74/0.96  
% 3.74/0.96  fof(f4,axiom,(
% 3.74/0.96    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.74/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.74/0.96  
% 3.74/0.96  fof(f21,plain,(
% 3.74/0.96    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.74/0.96    inference(ennf_transformation,[],[f4])).
% 3.74/0.96  
% 3.74/0.96  fof(f47,plain,(
% 3.74/0.96    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.74/0.96    inference(cnf_transformation,[],[f21])).
% 3.74/0.96  
% 3.74/0.96  fof(f10,axiom,(
% 3.74/0.96    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 3.74/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.74/0.96  
% 3.74/0.96  fof(f53,plain,(
% 3.74/0.96    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 3.74/0.96    inference(cnf_transformation,[],[f10])).
% 3.74/0.96  
% 3.74/0.96  fof(f13,axiom,(
% 3.74/0.96    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.74/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.74/0.96  
% 3.74/0.96  fof(f56,plain,(
% 3.74/0.96    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.74/0.96    inference(cnf_transformation,[],[f13])).
% 3.74/0.96  
% 3.74/0.96  fof(f14,axiom,(
% 3.74/0.96    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.74/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.74/0.96  
% 3.74/0.96  fof(f25,plain,(
% 3.74/0.96    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.74/0.96    inference(ennf_transformation,[],[f14])).
% 3.74/0.96  
% 3.74/0.96  fof(f26,plain,(
% 3.74/0.96    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.74/0.96    inference(flattening,[],[f25])).
% 3.74/0.96  
% 3.74/0.96  fof(f57,plain,(
% 3.74/0.96    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.74/0.96    inference(cnf_transformation,[],[f26])).
% 3.74/0.96  
% 3.74/0.96  fof(f11,axiom,(
% 3.74/0.96    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 3.74/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.74/0.96  
% 3.74/0.96  fof(f22,plain,(
% 3.74/0.96    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 3.74/0.96    inference(ennf_transformation,[],[f11])).
% 3.74/0.96  
% 3.74/0.96  fof(f23,plain,(
% 3.74/0.96    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.74/0.96    inference(flattening,[],[f22])).
% 3.74/0.96  
% 3.74/0.96  fof(f54,plain,(
% 3.74/0.96    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.74/0.96    inference(cnf_transformation,[],[f23])).
% 3.74/0.96  
% 3.74/0.96  fof(f9,axiom,(
% 3.74/0.96    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 3.74/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.74/0.96  
% 3.74/0.96  fof(f52,plain,(
% 3.74/0.96    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 3.74/0.96    inference(cnf_transformation,[],[f9])).
% 3.74/0.96  
% 3.74/0.96  fof(f67,plain,(
% 3.74/0.96    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 3.74/0.96    inference(definition_unfolding,[],[f52,f45])).
% 3.74/0.96  
% 3.74/0.96  fof(f72,plain,(
% 3.74/0.96    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.74/0.96    inference(definition_unfolding,[],[f54,f67])).
% 3.74/0.96  
% 3.74/0.96  fof(f16,axiom,(
% 3.74/0.96    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)))),
% 3.74/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.74/0.96  
% 3.74/0.96  fof(f29,plain,(
% 3.74/0.96    ! [X0] : (! [X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.74/0.96    inference(ennf_transformation,[],[f16])).
% 3.74/0.96  
% 3.74/0.96  fof(f59,plain,(
% 3.74/0.96    ( ! [X0,X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.74/0.96    inference(cnf_transformation,[],[f29])).
% 3.74/0.96  
% 3.74/0.96  fof(f5,axiom,(
% 3.74/0.96    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.74/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.74/0.96  
% 3.74/0.96  fof(f48,plain,(
% 3.74/0.96    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.74/0.96    inference(cnf_transformation,[],[f5])).
% 3.74/0.96  
% 3.74/0.96  fof(f3,axiom,(
% 3.74/0.96    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 3.74/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.74/0.96  
% 3.74/0.96  fof(f46,plain,(
% 3.74/0.96    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.74/0.96    inference(cnf_transformation,[],[f3])).
% 3.74/0.96  
% 3.74/0.96  fof(f69,plain,(
% 3.74/0.96    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0) )),
% 3.74/0.96    inference(definition_unfolding,[],[f46,f67])).
% 3.74/0.96  
% 3.74/0.96  fof(f7,axiom,(
% 3.74/0.96    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.74/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.74/0.96  
% 3.74/0.96  fof(f50,plain,(
% 3.74/0.96    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.74/0.96    inference(cnf_transformation,[],[f7])).
% 3.74/0.96  
% 3.74/0.96  fof(f71,plain,(
% 3.74/0.96    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 3.74/0.96    inference(definition_unfolding,[],[f50,f45])).
% 3.74/0.96  
% 3.74/0.96  fof(f1,axiom,(
% 3.74/0.96    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.74/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.74/0.96  
% 3.74/0.96  fof(f35,plain,(
% 3.74/0.96    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.74/0.96    inference(nnf_transformation,[],[f1])).
% 3.74/0.96  
% 3.74/0.96  fof(f36,plain,(
% 3.74/0.96    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.74/0.96    inference(flattening,[],[f35])).
% 3.74/0.96  
% 3.74/0.96  fof(f42,plain,(
% 3.74/0.96    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.74/0.96    inference(cnf_transformation,[],[f36])).
% 3.74/0.96  
% 3.74/0.96  fof(f75,plain,(
% 3.74/0.96    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.74/0.96    inference(equality_resolution,[],[f42])).
% 3.74/0.96  
% 3.74/0.96  fof(f15,axiom,(
% 3.74/0.96    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_pre_topc(X0,X1),X0))),
% 3.74/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.74/0.96  
% 3.74/0.96  fof(f27,plain,(
% 3.74/0.96    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.74/0.96    inference(ennf_transformation,[],[f15])).
% 3.74/0.96  
% 3.74/0.96  fof(f28,plain,(
% 3.74/0.96    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.74/0.96    inference(flattening,[],[f27])).
% 3.74/0.96  
% 3.74/0.96  fof(f58,plain,(
% 3.74/0.96    ( ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.74/0.96    inference(cnf_transformation,[],[f28])).
% 3.74/0.96  
% 3.74/0.96  fof(f62,plain,(
% 3.74/0.96    v2_pre_topc(sK0)),
% 3.74/0.96    inference(cnf_transformation,[],[f41])).
% 3.74/0.96  
% 3.74/0.96  fof(f66,plain,(
% 3.74/0.96    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)),
% 3.74/0.96    inference(cnf_transformation,[],[f41])).
% 3.74/0.96  
% 3.74/0.96  cnf(c_20,negated_conjecture,
% 3.74/0.96      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.74/0.96      inference(cnf_transformation,[],[f64]) ).
% 3.74/0.96  
% 3.74/0.96  cnf(c_800,plain,
% 3.74/0.96      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.74/0.96      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.74/0.96  
% 3.74/0.96  cnf(c_11,plain,
% 3.74/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.74/0.96      | k5_xboole_0(X0,k3_xboole_0(X0,X2)) = k7_subset_1(X1,X0,X2) ),
% 3.74/0.96      inference(cnf_transformation,[],[f73]) ).
% 3.74/0.96  
% 3.74/0.96  cnf(c_808,plain,
% 3.74/0.96      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k7_subset_1(X2,X0,X1)
% 3.74/0.96      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
% 3.74/0.96      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.74/0.96  
% 3.74/0.96  cnf(c_5735,plain,
% 3.74/0.96      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k3_xboole_0(sK1,X0)) ),
% 3.74/0.96      inference(superposition,[status(thm)],[c_800,c_808]) ).
% 3.74/0.96  
% 3.74/0.96  cnf(c_17,plain,
% 3.74/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.74/0.96      | ~ l1_pre_topc(X1)
% 3.74/0.96      | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
% 3.74/0.96      inference(cnf_transformation,[],[f61]) ).
% 3.74/0.96  
% 3.74/0.96  cnf(c_803,plain,
% 3.74/0.96      ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
% 3.74/0.96      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.74/0.96      | l1_pre_topc(X0) != iProver_top ),
% 3.74/0.96      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.74/0.96  
% 3.74/0.96  cnf(c_1155,plain,
% 3.74/0.96      ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1)
% 3.74/0.96      | l1_pre_topc(sK0) != iProver_top ),
% 3.74/0.96      inference(superposition,[status(thm)],[c_800,c_803]) ).
% 3.74/0.96  
% 3.74/0.96  cnf(c_21,negated_conjecture,
% 3.74/0.96      ( l1_pre_topc(sK0) ),
% 3.74/0.96      inference(cnf_transformation,[],[f63]) ).
% 3.74/0.96  
% 3.74/0.96  cnf(c_1036,plain,
% 3.74/0.96      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.74/0.96      | ~ l1_pre_topc(sK0)
% 3.74/0.96      | k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
% 3.74/0.96      inference(instantiation,[status(thm)],[c_17]) ).
% 3.74/0.96  
% 3.74/0.96  cnf(c_1428,plain,
% 3.74/0.96      ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
% 3.74/0.96      inference(global_propositional_subsumption,
% 3.74/0.96                [status(thm)],
% 3.74/0.96                [c_1155,c_21,c_20,c_1036]) ).
% 3.74/0.96  
% 3.74/0.96  cnf(c_6198,plain,
% 3.74/0.96      ( k5_xboole_0(sK1,k3_xboole_0(sK1,k2_tops_1(sK0,sK1))) = k1_tops_1(sK0,sK1) ),
% 3.74/0.96      inference(superposition,[status(thm)],[c_5735,c_1428]) ).
% 3.74/0.96  
% 3.74/0.96  cnf(c_0,plain,
% 3.74/0.96      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,X1) ),
% 3.74/0.96      inference(cnf_transformation,[],[f68]) ).
% 3.74/0.96  
% 3.74/0.96  cnf(c_6983,plain,
% 3.74/0.96      ( k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tops_1(sK0,sK1))) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
% 3.74/0.96      inference(superposition,[status(thm)],[c_6198,c_0]) ).
% 3.74/0.96  
% 3.74/0.96  cnf(c_19,negated_conjecture,
% 3.74/0.96      ( v4_pre_topc(sK1,sK0)
% 3.74/0.96      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 3.74/0.96      inference(cnf_transformation,[],[f65]) ).
% 3.74/0.96  
% 3.74/0.96  cnf(c_801,plain,
% 3.74/0.96      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 3.74/0.96      | v4_pre_topc(sK1,sK0) = iProver_top ),
% 3.74/0.96      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.74/0.96  
% 3.74/0.96  cnf(c_6183,plain,
% 3.74/0.96      ( k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tops_1(sK0,sK1))) = k2_tops_1(sK0,sK1)
% 3.74/0.96      | v4_pre_topc(sK1,sK0) = iProver_top ),
% 3.74/0.96      inference(demodulation,[status(thm)],[c_5735,c_801]) ).
% 3.74/0.96  
% 3.74/0.96  cnf(c_7176,plain,
% 3.74/0.96      ( k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 3.74/0.96      | v4_pre_topc(sK1,sK0) = iProver_top ),
% 3.74/0.96      inference(demodulation,[status(thm)],[c_6983,c_6183]) ).
% 3.74/0.96  
% 3.74/0.96  cnf(c_16,plain,
% 3.74/0.96      ( ~ v4_pre_topc(X0,X1)
% 3.74/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.74/0.96      | r1_tarski(k2_tops_1(X1,X0),X0)
% 3.74/0.96      | ~ l1_pre_topc(X1) ),
% 3.74/0.96      inference(cnf_transformation,[],[f60]) ).
% 3.74/0.96  
% 3.74/0.96  cnf(c_804,plain,
% 3.74/0.96      ( v4_pre_topc(X0,X1) != iProver_top
% 3.74/0.96      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.74/0.96      | r1_tarski(k2_tops_1(X1,X0),X0) = iProver_top
% 3.74/0.96      | l1_pre_topc(X1) != iProver_top ),
% 3.74/0.96      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.74/0.96  
% 3.74/0.96  cnf(c_1957,plain,
% 3.74/0.96      ( v4_pre_topc(sK1,sK0) != iProver_top
% 3.74/0.96      | r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top
% 3.74/0.96      | l1_pre_topc(sK0) != iProver_top ),
% 3.74/0.96      inference(superposition,[status(thm)],[c_800,c_804]) ).
% 3.74/0.96  
% 3.74/0.96  cnf(c_24,plain,
% 3.74/0.96      ( l1_pre_topc(sK0) = iProver_top ),
% 3.74/0.96      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.74/0.96  
% 3.74/0.96  cnf(c_2495,plain,
% 3.74/0.96      ( r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top
% 3.74/0.96      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 3.74/0.96      inference(global_propositional_subsumption,
% 3.74/0.96                [status(thm)],
% 3.74/0.96                [c_1957,c_24]) ).
% 3.74/0.96  
% 3.74/0.96  cnf(c_2496,plain,
% 3.74/0.96      ( v4_pre_topc(sK1,sK0) != iProver_top
% 3.74/0.96      | r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top ),
% 3.74/0.96      inference(renaming,[status(thm)],[c_2495]) ).
% 3.74/0.96  
% 3.74/0.96  cnf(c_5,plain,
% 3.74/0.96      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 3.74/0.96      inference(cnf_transformation,[],[f47]) ).
% 3.74/0.96  
% 3.74/0.96  cnf(c_812,plain,
% 3.74/0.96      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 3.74/0.96      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.74/0.96  
% 3.74/0.96  cnf(c_2501,plain,
% 3.74/0.96      ( k3_xboole_0(k2_tops_1(sK0,sK1),sK1) = k2_tops_1(sK0,sK1)
% 3.74/0.96      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 3.74/0.96      inference(superposition,[status(thm)],[c_2496,c_812]) ).
% 3.74/0.96  
% 3.74/0.96  cnf(c_7534,plain,
% 3.74/0.96      ( k3_xboole_0(k2_tops_1(sK0,sK1),sK1) = k2_tops_1(sK0,sK1)
% 3.74/0.96      | k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 3.74/0.96      inference(superposition,[status(thm)],[c_7176,c_2501]) ).
% 3.74/0.96  
% 3.74/0.96  cnf(c_9,plain,
% 3.74/0.96      ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
% 3.74/0.96      inference(cnf_transformation,[],[f53]) ).
% 3.74/0.96  
% 3.74/0.96  cnf(c_12,plain,
% 3.74/0.96      ( k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
% 3.74/0.96      inference(cnf_transformation,[],[f56]) ).
% 3.74/0.96  
% 3.74/0.96  cnf(c_1257,plain,
% 3.74/0.96      ( k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X1,X0) ),
% 3.74/0.96      inference(superposition,[status(thm)],[c_9,c_12]) ).
% 3.74/0.96  
% 3.74/0.96  cnf(c_1572,plain,
% 3.74/0.96      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 3.74/0.96      inference(superposition,[status(thm)],[c_1257,c_12]) ).
% 3.74/0.96  
% 3.74/0.96  cnf(c_8803,plain,
% 3.74/0.96      ( k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 3.74/0.96      inference(superposition,[status(thm)],[c_7534,c_1572]) ).
% 3.74/0.96  
% 3.74/0.96  cnf(c_13,plain,
% 3.74/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.74/0.96      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.74/0.96      | ~ l1_pre_topc(X1) ),
% 3.74/0.96      inference(cnf_transformation,[],[f57]) ).
% 3.74/0.96  
% 3.74/0.96  cnf(c_807,plain,
% 3.74/0.96      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.74/0.96      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 3.74/0.96      | l1_pre_topc(X1) != iProver_top ),
% 3.74/0.96      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.74/0.96  
% 3.74/0.96  cnf(c_10,plain,
% 3.74/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.74/0.96      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.74/0.96      | k5_xboole_0(X2,k5_xboole_0(X0,k3_xboole_0(X0,X2))) = k4_subset_1(X1,X2,X0) ),
% 3.74/0.96      inference(cnf_transformation,[],[f72]) ).
% 3.74/0.96  
% 3.74/0.96  cnf(c_809,plain,
% 3.74/0.96      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k4_subset_1(X2,X0,X1)
% 3.74/0.96      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
% 3.74/0.96      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
% 3.74/0.96      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.74/0.96  
% 3.74/0.96  cnf(c_6046,plain,
% 3.74/0.96      ( k5_xboole_0(sK1,k5_xboole_0(X0,k3_xboole_0(X0,sK1))) = k4_subset_1(u1_struct_0(sK0),sK1,X0)
% 3.74/0.96      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.74/0.96      inference(superposition,[status(thm)],[c_800,c_809]) ).
% 3.74/0.96  
% 3.74/0.96  cnf(c_6326,plain,
% 3.74/0.96      ( k5_xboole_0(sK1,k5_xboole_0(k2_tops_1(sK0,X0),k3_xboole_0(k2_tops_1(sK0,X0),sK1))) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0))
% 3.74/0.96      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.74/0.96      | l1_pre_topc(sK0) != iProver_top ),
% 3.74/0.96      inference(superposition,[status(thm)],[c_807,c_6046]) ).
% 3.74/0.96  
% 3.74/0.96  cnf(c_6993,plain,
% 3.74/0.96      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.74/0.96      | k5_xboole_0(sK1,k5_xboole_0(k2_tops_1(sK0,X0),k3_xboole_0(k2_tops_1(sK0,X0),sK1))) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) ),
% 3.74/0.96      inference(global_propositional_subsumption,
% 3.74/0.96                [status(thm)],
% 3.74/0.96                [c_6326,c_24]) ).
% 3.74/0.96  
% 3.74/0.96  cnf(c_6994,plain,
% 3.74/0.96      ( k5_xboole_0(sK1,k5_xboole_0(k2_tops_1(sK0,X0),k3_xboole_0(k2_tops_1(sK0,X0),sK1))) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0))
% 3.74/0.96      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.74/0.96      inference(renaming,[status(thm)],[c_6993]) ).
% 3.74/0.96  
% 3.74/0.96  cnf(c_7002,plain,
% 3.74/0.96      ( k5_xboole_0(sK1,k5_xboole_0(k2_tops_1(sK0,sK1),k3_xboole_0(k2_tops_1(sK0,sK1),sK1))) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
% 3.74/0.96      inference(superposition,[status(thm)],[c_800,c_6994]) ).
% 3.74/0.96  
% 3.74/0.96  cnf(c_15,plain,
% 3.74/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.74/0.96      | ~ l1_pre_topc(X1)
% 3.74/0.96      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
% 3.74/0.96      inference(cnf_transformation,[],[f59]) ).
% 3.74/0.96  
% 3.74/0.96  cnf(c_805,plain,
% 3.74/0.96      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
% 3.74/0.96      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.74/0.96      | l1_pre_topc(X0) != iProver_top ),
% 3.74/0.96      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.74/0.96  
% 3.74/0.96  cnf(c_3349,plain,
% 3.74/0.96      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
% 3.74/0.96      | l1_pre_topc(sK0) != iProver_top ),
% 3.74/0.96      inference(superposition,[status(thm)],[c_800,c_805]) ).
% 3.74/0.96  
% 3.74/0.96  cnf(c_1033,plain,
% 3.74/0.96      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.74/0.96      | ~ l1_pre_topc(sK0)
% 3.74/0.96      | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 3.74/0.96      inference(instantiation,[status(thm)],[c_15]) ).
% 3.74/0.96  
% 3.74/0.96  cnf(c_3542,plain,
% 3.74/0.96      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 3.74/0.96      inference(global_propositional_subsumption,
% 3.74/0.96                [status(thm)],
% 3.74/0.96                [c_3349,c_21,c_20,c_1033]) ).
% 3.74/0.96  
% 3.74/0.96  cnf(c_7004,plain,
% 3.74/0.96      ( k5_xboole_0(sK1,k5_xboole_0(k2_tops_1(sK0,sK1),k3_xboole_0(k2_tops_1(sK0,sK1),sK1))) = k2_pre_topc(sK0,sK1) ),
% 3.74/0.96      inference(light_normalisation,[status(thm)],[c_7002,c_3542]) ).
% 3.74/0.96  
% 3.74/0.96  cnf(c_7060,plain,
% 3.74/0.96      ( k5_xboole_0(sK1,k5_xboole_0(k2_tops_1(sK0,sK1),k3_xboole_0(sK1,k2_tops_1(sK0,sK1)))) = k2_pre_topc(sK0,sK1) ),
% 3.74/0.96      inference(superposition,[status(thm)],[c_1572,c_7004]) ).
% 3.74/0.96  
% 3.74/0.96  cnf(c_8815,plain,
% 3.74/0.96      ( k5_xboole_0(sK1,k5_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))) = k2_pre_topc(sK0,sK1) ),
% 3.74/0.96      inference(demodulation,[status(thm)],[c_8803,c_7060]) ).
% 3.74/0.96  
% 3.74/0.96  cnf(c_6,plain,
% 3.74/0.96      ( r1_tarski(k1_xboole_0,X0) ),
% 3.74/0.96      inference(cnf_transformation,[],[f48]) ).
% 3.74/0.96  
% 3.74/0.96  cnf(c_811,plain,
% 3.74/0.96      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.74/0.96      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.74/0.96  
% 3.74/0.96  cnf(c_2346,plain,
% 3.74/0.96      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.74/0.96      inference(superposition,[status(thm)],[c_811,c_812]) ).
% 3.74/0.96  
% 3.74/0.96  cnf(c_4,plain,
% 3.74/0.96      ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
% 3.74/0.96      inference(cnf_transformation,[],[f69]) ).
% 3.74/0.96  
% 3.74/0.96  cnf(c_2772,plain,
% 3.74/0.96      ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) = X0 ),
% 3.74/0.96      inference(demodulation,[status(thm)],[c_2346,c_4]) ).
% 3.74/0.96  
% 3.74/0.96  cnf(c_8,plain,
% 3.74/0.96      ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
% 3.74/0.96      inference(cnf_transformation,[],[f71]) ).
% 3.74/0.96  
% 3.74/0.96  cnf(c_1260,plain,
% 3.74/0.96      ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.74/0.96      inference(superposition,[status(thm)],[c_8,c_4]) ).
% 3.74/0.96  
% 3.74/0.96  cnf(c_2774,plain,
% 3.74/0.96      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.74/0.96      inference(light_normalisation,[status(thm)],[c_2772,c_1260]) ).
% 3.74/0.96  
% 3.74/0.96  cnf(c_2786,plain,
% 3.74/0.96      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.74/0.96      inference(superposition,[status(thm)],[c_2346,c_1572]) ).
% 3.74/0.96  
% 3.74/0.96  cnf(c_3059,plain,
% 3.74/0.96      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k1_xboole_0))) = k3_xboole_0(X0,k1_xboole_0) ),
% 3.74/0.96      inference(superposition,[status(thm)],[c_2786,c_0]) ).
% 3.74/0.96  
% 3.74/0.96  cnf(c_3061,plain,
% 3.74/0.96      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k1_xboole_0))) = k1_xboole_0 ),
% 3.74/0.96      inference(light_normalisation,[status(thm)],[c_3059,c_2786]) ).
% 3.74/0.96  
% 3.74/0.96  cnf(c_3,plain,
% 3.74/0.96      ( r1_tarski(X0,X0) ),
% 3.74/0.96      inference(cnf_transformation,[],[f75]) ).
% 3.74/0.96  
% 3.74/0.96  cnf(c_813,plain,
% 3.74/0.96      ( r1_tarski(X0,X0) = iProver_top ),
% 3.74/0.96      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.74/0.96  
% 3.74/0.96  cnf(c_2345,plain,
% 3.74/0.96      ( k3_xboole_0(X0,X0) = X0 ),
% 3.74/0.96      inference(superposition,[status(thm)],[c_813,c_812]) ).
% 3.74/0.96  
% 3.74/0.96  cnf(c_3063,plain,
% 3.74/0.96      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.74/0.96      inference(light_normalisation,[status(thm)],[c_3061,c_2345,c_2774]) ).
% 3.74/0.96  
% 3.74/0.96  cnf(c_8824,plain,
% 3.74/0.96      ( k2_pre_topc(sK0,sK1) = sK1 ),
% 3.74/0.96      inference(demodulation,[status(thm)],[c_8815,c_2774,c_3063]) ).
% 3.74/0.96  
% 3.74/0.96  cnf(c_14,plain,
% 3.74/0.96      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
% 3.74/0.96      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.74/0.96      | ~ v2_pre_topc(X0)
% 3.74/0.96      | ~ l1_pre_topc(X0) ),
% 3.74/0.96      inference(cnf_transformation,[],[f58]) ).
% 3.74/0.96  
% 3.74/0.96  cnf(c_806,plain,
% 3.74/0.96      ( v4_pre_topc(k2_pre_topc(X0,X1),X0) = iProver_top
% 3.74/0.96      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.74/0.96      | v2_pre_topc(X0) != iProver_top
% 3.74/0.96      | l1_pre_topc(X0) != iProver_top ),
% 3.74/0.96      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.74/0.96  
% 3.74/0.96  cnf(c_4016,plain,
% 3.74/0.96      ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) = iProver_top
% 3.74/0.96      | v2_pre_topc(sK0) != iProver_top
% 3.74/0.96      | l1_pre_topc(sK0) != iProver_top ),
% 3.74/0.96      inference(superposition,[status(thm)],[c_800,c_806]) ).
% 3.74/0.96  
% 3.74/0.96  cnf(c_22,negated_conjecture,
% 3.74/0.96      ( v2_pre_topc(sK0) ),
% 3.74/0.96      inference(cnf_transformation,[],[f62]) ).
% 3.74/0.96  
% 3.74/0.96  cnf(c_23,plain,
% 3.74/0.96      ( v2_pre_topc(sK0) = iProver_top ),
% 3.74/0.96      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.74/0.96  
% 3.74/0.96  cnf(c_25,plain,
% 3.74/0.96      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.74/0.96      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.74/0.96  
% 3.74/0.96  cnf(c_982,plain,
% 3.74/0.96      ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0)
% 3.74/0.96      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.74/0.96      | ~ v2_pre_topc(sK0)
% 3.74/0.96      | ~ l1_pre_topc(sK0) ),
% 3.74/0.96      inference(instantiation,[status(thm)],[c_14]) ).
% 3.74/0.96  
% 3.74/0.96  cnf(c_983,plain,
% 3.74/0.96      ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) = iProver_top
% 3.74/0.96      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.74/0.96      | v2_pre_topc(sK0) != iProver_top
% 3.74/0.96      | l1_pre_topc(sK0) != iProver_top ),
% 3.74/0.96      inference(predicate_to_equality,[status(thm)],[c_982]) ).
% 3.74/0.96  
% 3.74/0.96  cnf(c_4606,plain,
% 3.74/0.96      ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) = iProver_top ),
% 3.74/0.96      inference(global_propositional_subsumption,
% 3.74/0.96                [status(thm)],
% 3.74/0.96                [c_4016,c_23,c_24,c_25,c_983]) ).
% 3.74/0.96  
% 3.74/0.96  cnf(c_10081,plain,
% 3.74/0.96      ( v4_pre_topc(sK1,sK0) = iProver_top ),
% 3.74/0.96      inference(demodulation,[status(thm)],[c_8824,c_4606]) ).
% 3.74/0.96  
% 3.74/0.96  cnf(c_18,negated_conjecture,
% 3.74/0.96      ( ~ v4_pre_topc(sK1,sK0)
% 3.74/0.96      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
% 3.74/0.96      inference(cnf_transformation,[],[f66]) ).
% 3.74/0.96  
% 3.74/0.96  cnf(c_802,plain,
% 3.74/0.96      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
% 3.74/0.96      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 3.74/0.96      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.74/0.96  
% 3.74/0.96  cnf(c_6184,plain,
% 3.74/0.96      ( k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tops_1(sK0,sK1))) != k2_tops_1(sK0,sK1)
% 3.74/0.96      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 3.74/0.96      inference(demodulation,[status(thm)],[c_5735,c_802]) ).
% 3.74/0.96  
% 3.74/0.96  cnf(c_7177,plain,
% 3.74/0.96      ( k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
% 3.74/0.96      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 3.74/0.96      inference(demodulation,[status(thm)],[c_6983,c_6184]) ).
% 3.74/0.96  
% 3.74/0.96  cnf(contradiction,plain,
% 3.74/0.96      ( $false ),
% 3.74/0.96      inference(minisat,[status(thm)],[c_10081,c_8803,c_7177]) ).
% 3.74/0.96  
% 3.74/0.96  
% 3.74/0.96  % SZS output end CNFRefutation for theBenchmark.p
% 3.74/0.96  
% 3.74/0.96  ------                               Statistics
% 3.74/0.96  
% 3.74/0.96  ------ Selected
% 3.74/0.96  
% 3.74/0.96  total_time:                             0.277
% 3.74/0.96  
%------------------------------------------------------------------------------
