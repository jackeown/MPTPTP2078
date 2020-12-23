%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:14:45 EST 2020

% Result     : Theorem 8.03s
% Output     : CNFRefutation 8.03s
% Verified   : 
% Statistics : Number of formulae       :  144 (1136 expanded)
%              Number of clauses        :   78 ( 336 expanded)
%              Number of leaves         :   20 ( 258 expanded)
%              Depth                    :   26
%              Number of atoms          :  336 (4551 expanded)
%              Number of equality atoms :  174 (1611 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1)
            | ~ v4_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f35])).

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
    inference(flattening,[],[f36])).

fof(f39,plain,(
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

fof(f38,plain,
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

fof(f40,plain,
    ( ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f37,f39,f38])).

fof(f61,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f40])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f60,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f62,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => r1_tarski(k2_tops_1(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_tops_1(X0,X1),X1)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f46,f50])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f65,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f41,f50,f50])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f64,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f43,f50])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f9,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f42,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f20])).

fof(f66,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f42,f50])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f23])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f63,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f13,axiom,(
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

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) != X1
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f59,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_648,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_651,plain,
    ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_28751,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_648,c_651])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_657,plain,
    ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_7274,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
    inference(superposition,[status(thm)],[c_648,c_657])).

cnf(c_28754,plain,
    ( k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_28751,c_7274])).

cnf(c_20,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_23,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_29472,plain,
    ( k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_28754,c_23])).

cnf(c_18,negated_conjecture,
    ( v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_649,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_15,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k2_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_652,plain,
    ( v4_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(k2_tops_1(X1,X0),X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1103,plain,
    ( v4_pre_topc(sK1,sK0) != iProver_top
    | r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_648,c_652])).

cnf(c_1393,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1103,c_23])).

cnf(c_1394,plain,
    ( v4_pre_topc(sK1,sK0) != iProver_top
    | r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(renaming,[status(thm)],[c_1393])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_660,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4754,plain,
    ( k4_xboole_0(k2_tops_1(sK0,sK1),k4_xboole_0(k2_tops_1(sK0,sK1),sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1394,c_660])).

cnf(c_5744,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | k4_xboole_0(k2_tops_1(sK0,sK1),k4_xboole_0(k2_tops_1(sK0,sK1),sK1)) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_649,c_4754])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_5953,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | k4_xboole_0(sK1,k4_xboole_0(sK1,k2_tops_1(sK0,sK1))) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_5744,c_1])).

cnf(c_29508,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_29472,c_5953])).

cnf(c_29528,plain,
    ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_29508,c_7274])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1214,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1,c_0])).

cnf(c_2170,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_1,c_1214])).

cnf(c_30443,plain,
    ( k5_xboole_0(k2_tops_1(sK0,sK1),k4_xboole_0(sK1,k4_xboole_0(k1_tops_1(sK0,sK1),k4_xboole_0(k1_tops_1(sK0,sK1),sK1)))) = k4_xboole_0(k4_xboole_0(sK1,k1_tops_1(sK0,sK1)),sK1) ),
    inference(superposition,[status(thm)],[c_29528,c_2170])).

cnf(c_30486,plain,
    ( k5_xboole_0(k1_tops_1(sK0,sK1),k4_xboole_0(sK1,k2_tops_1(sK0,sK1))) = k4_xboole_0(k1_tops_1(sK0,sK1),sK1) ),
    inference(superposition,[status(thm)],[c_29528,c_1214])).

cnf(c_30491,plain,
    ( k5_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) = k4_xboole_0(k1_tops_1(sK0,sK1),sK1) ),
    inference(light_normalisation,[status(thm)],[c_30486,c_29472])).

cnf(c_6,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_659,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_661,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2933,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(superposition,[status(thm)],[c_659,c_661])).

cnf(c_4,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_4105,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2933,c_4])).

cnf(c_8,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1208,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_8,c_1])).

cnf(c_4263,plain,
    ( k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_4105,c_1208])).

cnf(c_4265,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4263,c_4105])).

cnf(c_2,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1195,plain,
    ( k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_2,c_0])).

cnf(c_4414,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4265,c_1195])).

cnf(c_30492,plain,
    ( k4_xboole_0(k1_tops_1(sK0,sK1),sK1) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_30491,c_4414])).

cnf(c_30620,plain,
    ( k5_xboole_0(k2_tops_1(sK0,sK1),k4_xboole_0(sK1,k4_xboole_0(k1_tops_1(sK0,sK1),k1_xboole_0))) = k4_xboole_0(k2_tops_1(sK0,sK1),sK1) ),
    inference(light_normalisation,[status(thm)],[c_30443,c_29528,c_30492])).

cnf(c_30622,plain,
    ( k4_xboole_0(k2_tops_1(sK0,sK1),sK1) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_30620,c_8,c_4414,c_29528])).

cnf(c_7,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_31569,plain,
    ( k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_30622,c_7])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_653,plain,
    ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_29026,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_648,c_653])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_654,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_658,plain,
    ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_15007,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k2_xboole_0(sK1,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_648,c_658])).

cnf(c_15029,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_654,c_15007])).

cnf(c_15216,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_15029,c_23])).

cnf(c_15217,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_15216])).

cnf(c_15225,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_648,c_15217])).

cnf(c_29029,plain,
    ( k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_29026,c_15225])).

cnf(c_30712,plain,
    ( k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_29029,c_23])).

cnf(c_31571,plain,
    ( k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = sK1 ),
    inference(demodulation,[status(thm)],[c_31569,c_4,c_30712])).

cnf(c_31772,plain,
    ( k2_pre_topc(sK0,sK1) = sK1 ),
    inference(demodulation,[status(thm)],[c_31571,c_30712])).

cnf(c_17,negated_conjecture,
    ( ~ v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_650,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_7644,plain,
    ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7274,c_650])).

cnf(c_11,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | k2_pre_topc(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_897,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | k2_pre_topc(sK0,sK1) != sK1 ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_898,plain,
    ( k2_pre_topc(sK0,sK1) != sK1
    | v4_pre_topc(sK1,sK0) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_897])).

cnf(c_24,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_21,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_22,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_31772,c_29528,c_7644,c_898,c_24,c_23,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n002.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:12:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 8.03/1.47  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.03/1.47  
% 8.03/1.47  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 8.03/1.47  
% 8.03/1.47  ------  iProver source info
% 8.03/1.47  
% 8.03/1.47  git: date: 2020-06-30 10:37:57 +0100
% 8.03/1.47  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 8.03/1.47  git: non_committed_changes: false
% 8.03/1.47  git: last_make_outside_of_git: false
% 8.03/1.47  
% 8.03/1.47  ------ 
% 8.03/1.47  ------ Parsing...
% 8.03/1.47  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 8.03/1.47  
% 8.03/1.47  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 8.03/1.47  
% 8.03/1.47  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 8.03/1.47  
% 8.03/1.47  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.03/1.47  ------ Proving...
% 8.03/1.47  ------ Problem Properties 
% 8.03/1.47  
% 8.03/1.47  
% 8.03/1.47  clauses                                 22
% 8.03/1.47  conjectures                             5
% 8.03/1.47  EPR                                     2
% 8.03/1.47  Horn                                    21
% 8.03/1.47  unary                                   10
% 8.03/1.47  binary                                  5
% 8.03/1.47  lits                                    45
% 8.03/1.47  lits eq                                 16
% 8.03/1.47  fd_pure                                 0
% 8.03/1.47  fd_pseudo                               0
% 8.03/1.47  fd_cond                                 0
% 8.03/1.47  fd_pseudo_cond                          0
% 8.03/1.47  AC symbols                              0
% 8.03/1.47  
% 8.03/1.47  ------ Input Options Time Limit: Unbounded
% 8.03/1.47  
% 8.03/1.47  
% 8.03/1.47  ------ 
% 8.03/1.47  Current options:
% 8.03/1.47  ------ 
% 8.03/1.47  
% 8.03/1.47  
% 8.03/1.47  
% 8.03/1.47  
% 8.03/1.47  ------ Proving...
% 8.03/1.47  
% 8.03/1.47  
% 8.03/1.47  % SZS status Theorem for theBenchmark.p
% 8.03/1.47  
% 8.03/1.47  % SZS output start CNFRefutation for theBenchmark.p
% 8.03/1.47  
% 8.03/1.47  fof(f18,conjecture,(
% 8.03/1.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 8.03/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.03/1.47  
% 8.03/1.47  fof(f19,negated_conjecture,(
% 8.03/1.47    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 8.03/1.47    inference(negated_conjecture,[],[f18])).
% 8.03/1.47  
% 8.03/1.47  fof(f34,plain,(
% 8.03/1.47    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 8.03/1.47    inference(ennf_transformation,[],[f19])).
% 8.03/1.47  
% 8.03/1.47  fof(f35,plain,(
% 8.03/1.47    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 8.03/1.47    inference(flattening,[],[f34])).
% 8.03/1.47  
% 8.03/1.47  fof(f36,plain,(
% 8.03/1.47    ? [X0] : (? [X1] : (((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 8.03/1.47    inference(nnf_transformation,[],[f35])).
% 8.03/1.47  
% 8.03/1.47  fof(f37,plain,(
% 8.03/1.47    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 8.03/1.47    inference(flattening,[],[f36])).
% 8.03/1.47  
% 8.03/1.47  fof(f39,plain,(
% 8.03/1.47    ( ! [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) != k2_tops_1(X0,sK1) | ~v4_pre_topc(sK1,X0)) & (k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) = k2_tops_1(X0,sK1) | v4_pre_topc(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 8.03/1.47    introduced(choice_axiom,[])).
% 8.03/1.47  
% 8.03/1.47  fof(f38,plain,(
% 8.03/1.47    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) != k2_tops_1(sK0,X1) | ~v4_pre_topc(X1,sK0)) & (k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) = k2_tops_1(sK0,X1) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 8.03/1.47    introduced(choice_axiom,[])).
% 8.03/1.47  
% 8.03/1.47  fof(f40,plain,(
% 8.03/1.47    ((k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)) & (k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 8.03/1.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f37,f39,f38])).
% 8.03/1.47  
% 8.03/1.47  fof(f61,plain,(
% 8.03/1.47    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 8.03/1.47    inference(cnf_transformation,[],[f40])).
% 8.03/1.47  
% 8.03/1.47  fof(f17,axiom,(
% 8.03/1.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)))),
% 8.03/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.03/1.47  
% 8.03/1.47  fof(f33,plain,(
% 8.03/1.47    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 8.03/1.47    inference(ennf_transformation,[],[f17])).
% 8.03/1.47  
% 8.03/1.47  fof(f58,plain,(
% 8.03/1.47    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 8.03/1.47    inference(cnf_transformation,[],[f33])).
% 8.03/1.47  
% 8.03/1.47  fof(f12,axiom,(
% 8.03/1.47    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 8.03/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.03/1.47  
% 8.03/1.47  fof(f25,plain,(
% 8.03/1.47    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 8.03/1.47    inference(ennf_transformation,[],[f12])).
% 8.03/1.47  
% 8.03/1.47  fof(f52,plain,(
% 8.03/1.47    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 8.03/1.47    inference(cnf_transformation,[],[f25])).
% 8.03/1.47  
% 8.03/1.47  fof(f60,plain,(
% 8.03/1.47    l1_pre_topc(sK0)),
% 8.03/1.47    inference(cnf_transformation,[],[f40])).
% 8.03/1.47  
% 8.03/1.47  fof(f62,plain,(
% 8.03/1.47    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)),
% 8.03/1.47    inference(cnf_transformation,[],[f40])).
% 8.03/1.47  
% 8.03/1.47  fof(f16,axiom,(
% 8.03/1.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => r1_tarski(k2_tops_1(X0,X1),X1))))),
% 8.03/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.03/1.47  
% 8.03/1.47  fof(f31,plain,(
% 8.03/1.47    ! [X0] : (! [X1] : ((r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 8.03/1.47    inference(ennf_transformation,[],[f16])).
% 8.03/1.47  
% 8.03/1.47  fof(f32,plain,(
% 8.03/1.47    ! [X0] : (! [X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 8.03/1.47    inference(flattening,[],[f31])).
% 8.03/1.47  
% 8.03/1.47  fof(f57,plain,(
% 8.03/1.47    ( ! [X0,X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 8.03/1.47    inference(cnf_transformation,[],[f32])).
% 8.03/1.47  
% 8.03/1.47  fof(f6,axiom,(
% 8.03/1.47    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 8.03/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.03/1.47  
% 8.03/1.47  fof(f22,plain,(
% 8.03/1.47    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 8.03/1.47    inference(ennf_transformation,[],[f6])).
% 8.03/1.47  
% 8.03/1.47  fof(f46,plain,(
% 8.03/1.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 8.03/1.47    inference(cnf_transformation,[],[f22])).
% 8.03/1.47  
% 8.03/1.47  fof(f10,axiom,(
% 8.03/1.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 8.03/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.03/1.47  
% 8.03/1.47  fof(f50,plain,(
% 8.03/1.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 8.03/1.47    inference(cnf_transformation,[],[f10])).
% 8.03/1.47  
% 8.03/1.47  fof(f67,plain,(
% 8.03/1.47    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 8.03/1.47    inference(definition_unfolding,[],[f46,f50])).
% 8.03/1.47  
% 8.03/1.47  fof(f1,axiom,(
% 8.03/1.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 8.03/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.03/1.47  
% 8.03/1.47  fof(f41,plain,(
% 8.03/1.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 8.03/1.47    inference(cnf_transformation,[],[f1])).
% 8.03/1.47  
% 8.03/1.47  fof(f65,plain,(
% 8.03/1.47    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 8.03/1.47    inference(definition_unfolding,[],[f41,f50,f50])).
% 8.03/1.47  
% 8.03/1.47  fof(f3,axiom,(
% 8.03/1.47    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 8.03/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.03/1.47  
% 8.03/1.47  fof(f43,plain,(
% 8.03/1.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 8.03/1.47    inference(cnf_transformation,[],[f3])).
% 8.03/1.47  
% 8.03/1.47  fof(f64,plain,(
% 8.03/1.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 8.03/1.47    inference(definition_unfolding,[],[f43,f50])).
% 8.03/1.47  
% 8.03/1.47  fof(f7,axiom,(
% 8.03/1.47    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 8.03/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.03/1.47  
% 8.03/1.47  fof(f47,plain,(
% 8.03/1.47    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 8.03/1.47    inference(cnf_transformation,[],[f7])).
% 8.03/1.47  
% 8.03/1.47  fof(f4,axiom,(
% 8.03/1.47    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 8.03/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.03/1.47  
% 8.03/1.47  fof(f21,plain,(
% 8.03/1.47    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 8.03/1.47    inference(ennf_transformation,[],[f4])).
% 8.03/1.47  
% 8.03/1.47  fof(f44,plain,(
% 8.03/1.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 8.03/1.47    inference(cnf_transformation,[],[f21])).
% 8.03/1.47  
% 8.03/1.47  fof(f5,axiom,(
% 8.03/1.47    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 8.03/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.03/1.47  
% 8.03/1.47  fof(f45,plain,(
% 8.03/1.47    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 8.03/1.47    inference(cnf_transformation,[],[f5])).
% 8.03/1.47  
% 8.03/1.47  fof(f9,axiom,(
% 8.03/1.47    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 8.03/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.03/1.47  
% 8.03/1.47  fof(f49,plain,(
% 8.03/1.47    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 8.03/1.47    inference(cnf_transformation,[],[f9])).
% 8.03/1.47  
% 8.03/1.47  fof(f2,axiom,(
% 8.03/1.47    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 8.03/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.03/1.47  
% 8.03/1.47  fof(f20,plain,(
% 8.03/1.47    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 8.03/1.47    inference(rectify,[],[f2])).
% 8.03/1.47  
% 8.03/1.47  fof(f42,plain,(
% 8.03/1.47    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 8.03/1.47    inference(cnf_transformation,[],[f20])).
% 8.03/1.47  
% 8.03/1.47  fof(f66,plain,(
% 8.03/1.47    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 8.03/1.47    inference(definition_unfolding,[],[f42,f50])).
% 8.03/1.47  
% 8.03/1.47  fof(f8,axiom,(
% 8.03/1.47    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 8.03/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.03/1.47  
% 8.03/1.47  fof(f48,plain,(
% 8.03/1.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 8.03/1.47    inference(cnf_transformation,[],[f8])).
% 8.03/1.47  
% 8.03/1.47  fof(f15,axiom,(
% 8.03/1.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)))),
% 8.03/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.03/1.47  
% 8.03/1.47  fof(f30,plain,(
% 8.03/1.47    ! [X0] : (! [X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 8.03/1.47    inference(ennf_transformation,[],[f15])).
% 8.03/1.47  
% 8.03/1.47  fof(f56,plain,(
% 8.03/1.47    ( ! [X0,X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 8.03/1.47    inference(cnf_transformation,[],[f30])).
% 8.03/1.47  
% 8.03/1.47  fof(f14,axiom,(
% 8.03/1.47    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 8.03/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.03/1.47  
% 8.03/1.47  fof(f28,plain,(
% 8.03/1.47    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 8.03/1.47    inference(ennf_transformation,[],[f14])).
% 8.03/1.47  
% 8.03/1.47  fof(f29,plain,(
% 8.03/1.47    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 8.03/1.47    inference(flattening,[],[f28])).
% 8.03/1.47  
% 8.03/1.47  fof(f55,plain,(
% 8.03/1.47    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 8.03/1.47    inference(cnf_transformation,[],[f29])).
% 8.03/1.47  
% 8.03/1.47  fof(f11,axiom,(
% 8.03/1.47    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 8.03/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.03/1.47  
% 8.03/1.47  fof(f23,plain,(
% 8.03/1.47    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 8.03/1.47    inference(ennf_transformation,[],[f11])).
% 8.03/1.47  
% 8.03/1.47  fof(f24,plain,(
% 8.03/1.47    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 8.03/1.47    inference(flattening,[],[f23])).
% 8.03/1.47  
% 8.03/1.47  fof(f51,plain,(
% 8.03/1.47    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 8.03/1.47    inference(cnf_transformation,[],[f24])).
% 8.03/1.47  
% 8.03/1.47  fof(f63,plain,(
% 8.03/1.47    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)),
% 8.03/1.47    inference(cnf_transformation,[],[f40])).
% 8.03/1.47  
% 8.03/1.47  fof(f13,axiom,(
% 8.03/1.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 8.03/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.03/1.47  
% 8.03/1.47  fof(f26,plain,(
% 8.03/1.47    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 8.03/1.47    inference(ennf_transformation,[],[f13])).
% 8.03/1.47  
% 8.03/1.47  fof(f27,plain,(
% 8.03/1.47    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 8.03/1.47    inference(flattening,[],[f26])).
% 8.03/1.47  
% 8.03/1.47  fof(f54,plain,(
% 8.03/1.47    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 8.03/1.47    inference(cnf_transformation,[],[f27])).
% 8.03/1.47  
% 8.03/1.47  fof(f59,plain,(
% 8.03/1.47    v2_pre_topc(sK0)),
% 8.03/1.47    inference(cnf_transformation,[],[f40])).
% 8.03/1.47  
% 8.03/1.47  cnf(c_19,negated_conjecture,
% 8.03/1.47      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 8.03/1.47      inference(cnf_transformation,[],[f61]) ).
% 8.03/1.47  
% 8.03/1.47  cnf(c_648,plain,
% 8.03/1.47      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 8.03/1.47      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 8.03/1.47  
% 8.03/1.47  cnf(c_16,plain,
% 8.03/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 8.03/1.47      | ~ l1_pre_topc(X1)
% 8.03/1.47      | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
% 8.03/1.47      inference(cnf_transformation,[],[f58]) ).
% 8.03/1.47  
% 8.03/1.47  cnf(c_651,plain,
% 8.03/1.47      ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
% 8.03/1.47      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 8.03/1.47      | l1_pre_topc(X0) != iProver_top ),
% 8.03/1.47      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 8.03/1.47  
% 8.03/1.47  cnf(c_28751,plain,
% 8.03/1.47      ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1)
% 8.03/1.47      | l1_pre_topc(sK0) != iProver_top ),
% 8.03/1.47      inference(superposition,[status(thm)],[c_648,c_651]) ).
% 8.03/1.47  
% 8.03/1.47  cnf(c_10,plain,
% 8.03/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 8.03/1.47      | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 8.03/1.47      inference(cnf_transformation,[],[f52]) ).
% 8.03/1.47  
% 8.03/1.47  cnf(c_657,plain,
% 8.03/1.47      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
% 8.03/1.47      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 8.03/1.47      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 8.03/1.47  
% 8.03/1.47  cnf(c_7274,plain,
% 8.03/1.47      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
% 8.03/1.47      inference(superposition,[status(thm)],[c_648,c_657]) ).
% 8.03/1.47  
% 8.03/1.47  cnf(c_28754,plain,
% 8.03/1.47      ( k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1)
% 8.03/1.47      | l1_pre_topc(sK0) != iProver_top ),
% 8.03/1.47      inference(demodulation,[status(thm)],[c_28751,c_7274]) ).
% 8.03/1.47  
% 8.03/1.47  cnf(c_20,negated_conjecture,
% 8.03/1.47      ( l1_pre_topc(sK0) ),
% 8.03/1.47      inference(cnf_transformation,[],[f60]) ).
% 8.03/1.47  
% 8.03/1.47  cnf(c_23,plain,
% 8.03/1.47      ( l1_pre_topc(sK0) = iProver_top ),
% 8.03/1.47      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 8.03/1.47  
% 8.03/1.47  cnf(c_29472,plain,
% 8.03/1.47      ( k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
% 8.03/1.47      inference(global_propositional_subsumption,
% 8.03/1.47                [status(thm)],
% 8.03/1.47                [c_28754,c_23]) ).
% 8.03/1.47  
% 8.03/1.47  cnf(c_18,negated_conjecture,
% 8.03/1.47      ( v4_pre_topc(sK1,sK0)
% 8.03/1.47      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 8.03/1.47      inference(cnf_transformation,[],[f62]) ).
% 8.03/1.47  
% 8.03/1.47  cnf(c_649,plain,
% 8.03/1.47      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 8.03/1.47      | v4_pre_topc(sK1,sK0) = iProver_top ),
% 8.03/1.47      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 8.03/1.47  
% 8.03/1.47  cnf(c_15,plain,
% 8.03/1.47      ( ~ v4_pre_topc(X0,X1)
% 8.03/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 8.03/1.47      | r1_tarski(k2_tops_1(X1,X0),X0)
% 8.03/1.47      | ~ l1_pre_topc(X1) ),
% 8.03/1.47      inference(cnf_transformation,[],[f57]) ).
% 8.03/1.47  
% 8.03/1.47  cnf(c_652,plain,
% 8.03/1.47      ( v4_pre_topc(X0,X1) != iProver_top
% 8.03/1.47      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 8.03/1.47      | r1_tarski(k2_tops_1(X1,X0),X0) = iProver_top
% 8.03/1.47      | l1_pre_topc(X1) != iProver_top ),
% 8.03/1.47      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 8.03/1.47  
% 8.03/1.47  cnf(c_1103,plain,
% 8.03/1.47      ( v4_pre_topc(sK1,sK0) != iProver_top
% 8.03/1.47      | r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top
% 8.03/1.47      | l1_pre_topc(sK0) != iProver_top ),
% 8.03/1.47      inference(superposition,[status(thm)],[c_648,c_652]) ).
% 8.03/1.47  
% 8.03/1.47  cnf(c_1393,plain,
% 8.03/1.47      ( r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top
% 8.03/1.47      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 8.03/1.47      inference(global_propositional_subsumption,
% 8.03/1.47                [status(thm)],
% 8.03/1.47                [c_1103,c_23]) ).
% 8.03/1.47  
% 8.03/1.47  cnf(c_1394,plain,
% 8.03/1.47      ( v4_pre_topc(sK1,sK0) != iProver_top
% 8.03/1.47      | r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top ),
% 8.03/1.47      inference(renaming,[status(thm)],[c_1393]) ).
% 8.03/1.47  
% 8.03/1.47  cnf(c_5,plain,
% 8.03/1.47      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 8.03/1.47      inference(cnf_transformation,[],[f67]) ).
% 8.03/1.47  
% 8.03/1.47  cnf(c_660,plain,
% 8.03/1.47      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
% 8.03/1.47      | r1_tarski(X0,X1) != iProver_top ),
% 8.03/1.47      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 8.03/1.47  
% 8.03/1.47  cnf(c_4754,plain,
% 8.03/1.47      ( k4_xboole_0(k2_tops_1(sK0,sK1),k4_xboole_0(k2_tops_1(sK0,sK1),sK1)) = k2_tops_1(sK0,sK1)
% 8.03/1.47      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 8.03/1.47      inference(superposition,[status(thm)],[c_1394,c_660]) ).
% 8.03/1.47  
% 8.03/1.47  cnf(c_5744,plain,
% 8.03/1.47      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 8.03/1.47      | k4_xboole_0(k2_tops_1(sK0,sK1),k4_xboole_0(k2_tops_1(sK0,sK1),sK1)) = k2_tops_1(sK0,sK1) ),
% 8.03/1.47      inference(superposition,[status(thm)],[c_649,c_4754]) ).
% 8.03/1.47  
% 8.03/1.47  cnf(c_1,plain,
% 8.03/1.47      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 8.03/1.47      inference(cnf_transformation,[],[f65]) ).
% 8.03/1.47  
% 8.03/1.47  cnf(c_5953,plain,
% 8.03/1.47      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 8.03/1.47      | k4_xboole_0(sK1,k4_xboole_0(sK1,k2_tops_1(sK0,sK1))) = k2_tops_1(sK0,sK1) ),
% 8.03/1.47      inference(superposition,[status(thm)],[c_5744,c_1]) ).
% 8.03/1.47  
% 8.03/1.47  cnf(c_29508,plain,
% 8.03/1.47      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 8.03/1.47      | k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 8.03/1.47      inference(demodulation,[status(thm)],[c_29472,c_5953]) ).
% 8.03/1.47  
% 8.03/1.47  cnf(c_29528,plain,
% 8.03/1.47      ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 8.03/1.47      inference(demodulation,[status(thm)],[c_29508,c_7274]) ).
% 8.03/1.47  
% 8.03/1.47  cnf(c_0,plain,
% 8.03/1.47      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 8.03/1.47      inference(cnf_transformation,[],[f64]) ).
% 8.03/1.47  
% 8.03/1.47  cnf(c_1214,plain,
% 8.03/1.47      ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 8.03/1.47      inference(superposition,[status(thm)],[c_1,c_0]) ).
% 8.03/1.47  
% 8.03/1.47  cnf(c_2170,plain,
% 8.03/1.47      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 8.03/1.47      inference(superposition,[status(thm)],[c_1,c_1214]) ).
% 8.03/1.47  
% 8.03/1.47  cnf(c_30443,plain,
% 8.03/1.47      ( k5_xboole_0(k2_tops_1(sK0,sK1),k4_xboole_0(sK1,k4_xboole_0(k1_tops_1(sK0,sK1),k4_xboole_0(k1_tops_1(sK0,sK1),sK1)))) = k4_xboole_0(k4_xboole_0(sK1,k1_tops_1(sK0,sK1)),sK1) ),
% 8.03/1.47      inference(superposition,[status(thm)],[c_29528,c_2170]) ).
% 8.03/1.47  
% 8.03/1.47  cnf(c_30486,plain,
% 8.03/1.47      ( k5_xboole_0(k1_tops_1(sK0,sK1),k4_xboole_0(sK1,k2_tops_1(sK0,sK1))) = k4_xboole_0(k1_tops_1(sK0,sK1),sK1) ),
% 8.03/1.47      inference(superposition,[status(thm)],[c_29528,c_1214]) ).
% 8.03/1.47  
% 8.03/1.47  cnf(c_30491,plain,
% 8.03/1.47      ( k5_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) = k4_xboole_0(k1_tops_1(sK0,sK1),sK1) ),
% 8.03/1.47      inference(light_normalisation,[status(thm)],[c_30486,c_29472]) ).
% 8.03/1.47  
% 8.03/1.47  cnf(c_6,plain,
% 8.03/1.47      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 8.03/1.47      inference(cnf_transformation,[],[f47]) ).
% 8.03/1.47  
% 8.03/1.47  cnf(c_659,plain,
% 8.03/1.47      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 8.03/1.47      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 8.03/1.47  
% 8.03/1.47  cnf(c_3,plain,
% 8.03/1.47      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 8.03/1.47      inference(cnf_transformation,[],[f44]) ).
% 8.03/1.47  
% 8.03/1.47  cnf(c_661,plain,
% 8.03/1.47      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 8.03/1.47      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 8.03/1.47  
% 8.03/1.47  cnf(c_2933,plain,
% 8.03/1.47      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
% 8.03/1.47      inference(superposition,[status(thm)],[c_659,c_661]) ).
% 8.03/1.47  
% 8.03/1.47  cnf(c_4,plain,
% 8.03/1.47      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 8.03/1.47      inference(cnf_transformation,[],[f45]) ).
% 8.03/1.47  
% 8.03/1.47  cnf(c_4105,plain,
% 8.03/1.47      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 8.03/1.47      inference(superposition,[status(thm)],[c_2933,c_4]) ).
% 8.03/1.47  
% 8.03/1.47  cnf(c_8,plain,
% 8.03/1.47      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 8.03/1.47      inference(cnf_transformation,[],[f49]) ).
% 8.03/1.47  
% 8.03/1.47  cnf(c_1208,plain,
% 8.03/1.47      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0) ),
% 8.03/1.47      inference(superposition,[status(thm)],[c_8,c_1]) ).
% 8.03/1.47  
% 8.03/1.47  cnf(c_4263,plain,
% 8.03/1.47      ( k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 8.03/1.47      inference(demodulation,[status(thm)],[c_4105,c_1208]) ).
% 8.03/1.47  
% 8.03/1.47  cnf(c_4265,plain,
% 8.03/1.47      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 8.03/1.47      inference(demodulation,[status(thm)],[c_4263,c_4105]) ).
% 8.03/1.47  
% 8.03/1.47  cnf(c_2,plain,
% 8.03/1.47      ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
% 8.03/1.47      inference(cnf_transformation,[],[f66]) ).
% 8.03/1.47  
% 8.03/1.47  cnf(c_1195,plain,
% 8.03/1.47      ( k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0) ),
% 8.03/1.47      inference(superposition,[status(thm)],[c_2,c_0]) ).
% 8.03/1.47  
% 8.03/1.47  cnf(c_4414,plain,
% 8.03/1.47      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 8.03/1.47      inference(demodulation,[status(thm)],[c_4265,c_1195]) ).
% 8.03/1.47  
% 8.03/1.47  cnf(c_30492,plain,
% 8.03/1.47      ( k4_xboole_0(k1_tops_1(sK0,sK1),sK1) = k1_xboole_0 ),
% 8.03/1.47      inference(demodulation,[status(thm)],[c_30491,c_4414]) ).
% 8.03/1.47  
% 8.03/1.47  cnf(c_30620,plain,
% 8.03/1.47      ( k5_xboole_0(k2_tops_1(sK0,sK1),k4_xboole_0(sK1,k4_xboole_0(k1_tops_1(sK0,sK1),k1_xboole_0))) = k4_xboole_0(k2_tops_1(sK0,sK1),sK1) ),
% 8.03/1.47      inference(light_normalisation,
% 8.03/1.47                [status(thm)],
% 8.03/1.47                [c_30443,c_29528,c_30492]) ).
% 8.03/1.47  
% 8.03/1.47  cnf(c_30622,plain,
% 8.03/1.47      ( k4_xboole_0(k2_tops_1(sK0,sK1),sK1) = k1_xboole_0 ),
% 8.03/1.47      inference(demodulation,[status(thm)],[c_30620,c_8,c_4414,c_29528]) ).
% 8.03/1.47  
% 8.03/1.47  cnf(c_7,plain,
% 8.03/1.47      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 8.03/1.47      inference(cnf_transformation,[],[f48]) ).
% 8.03/1.47  
% 8.03/1.47  cnf(c_31569,plain,
% 8.03/1.47      ( k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k1_xboole_0) ),
% 8.03/1.47      inference(superposition,[status(thm)],[c_30622,c_7]) ).
% 8.03/1.47  
% 8.03/1.47  cnf(c_14,plain,
% 8.03/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 8.03/1.47      | ~ l1_pre_topc(X1)
% 8.03/1.47      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
% 8.03/1.47      inference(cnf_transformation,[],[f56]) ).
% 8.03/1.47  
% 8.03/1.47  cnf(c_653,plain,
% 8.03/1.47      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
% 8.03/1.47      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 8.03/1.47      | l1_pre_topc(X0) != iProver_top ),
% 8.03/1.47      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 8.03/1.47  
% 8.03/1.47  cnf(c_29026,plain,
% 8.03/1.47      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
% 8.03/1.47      | l1_pre_topc(sK0) != iProver_top ),
% 8.03/1.47      inference(superposition,[status(thm)],[c_648,c_653]) ).
% 8.03/1.47  
% 8.03/1.47  cnf(c_13,plain,
% 8.03/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 8.03/1.47      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 8.03/1.47      | ~ l1_pre_topc(X1) ),
% 8.03/1.47      inference(cnf_transformation,[],[f55]) ).
% 8.03/1.47  
% 8.03/1.47  cnf(c_654,plain,
% 8.03/1.47      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 8.03/1.47      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 8.03/1.47      | l1_pre_topc(X1) != iProver_top ),
% 8.03/1.47      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 8.03/1.47  
% 8.03/1.47  cnf(c_9,plain,
% 8.03/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 8.03/1.47      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 8.03/1.47      | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
% 8.03/1.47      inference(cnf_transformation,[],[f51]) ).
% 8.03/1.47  
% 8.03/1.47  cnf(c_658,plain,
% 8.03/1.47      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
% 8.03/1.47      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
% 8.03/1.47      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 8.03/1.47      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 8.03/1.47  
% 8.03/1.47  cnf(c_15007,plain,
% 8.03/1.47      ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k2_xboole_0(sK1,X0)
% 8.03/1.47      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 8.03/1.47      inference(superposition,[status(thm)],[c_648,c_658]) ).
% 8.03/1.47  
% 8.03/1.47  cnf(c_15029,plain,
% 8.03/1.47      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0))
% 8.03/1.47      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.03/1.47      | l1_pre_topc(sK0) != iProver_top ),
% 8.03/1.47      inference(superposition,[status(thm)],[c_654,c_15007]) ).
% 8.03/1.47  
% 8.03/1.47  cnf(c_15216,plain,
% 8.03/1.47      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.03/1.47      | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0)) ),
% 8.03/1.47      inference(global_propositional_subsumption,
% 8.03/1.47                [status(thm)],
% 8.03/1.47                [c_15029,c_23]) ).
% 8.03/1.47  
% 8.03/1.47  cnf(c_15217,plain,
% 8.03/1.47      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0))
% 8.03/1.47      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 8.03/1.47      inference(renaming,[status(thm)],[c_15216]) ).
% 8.03/1.47  
% 8.03/1.47  cnf(c_15225,plain,
% 8.03/1.47      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
% 8.03/1.47      inference(superposition,[status(thm)],[c_648,c_15217]) ).
% 8.03/1.47  
% 8.03/1.47  cnf(c_29029,plain,
% 8.03/1.47      ( k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
% 8.03/1.47      | l1_pre_topc(sK0) != iProver_top ),
% 8.03/1.47      inference(demodulation,[status(thm)],[c_29026,c_15225]) ).
% 8.03/1.47  
% 8.03/1.47  cnf(c_30712,plain,
% 8.03/1.47      ( k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 8.03/1.47      inference(global_propositional_subsumption,
% 8.03/1.47                [status(thm)],
% 8.03/1.47                [c_29029,c_23]) ).
% 8.03/1.47  
% 8.03/1.47  cnf(c_31571,plain,
% 8.03/1.47      ( k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = sK1 ),
% 8.03/1.47      inference(demodulation,[status(thm)],[c_31569,c_4,c_30712]) ).
% 8.03/1.47  
% 8.03/1.47  cnf(c_31772,plain,
% 8.03/1.47      ( k2_pre_topc(sK0,sK1) = sK1 ),
% 8.03/1.47      inference(demodulation,[status(thm)],[c_31571,c_30712]) ).
% 8.03/1.47  
% 8.03/1.47  cnf(c_17,negated_conjecture,
% 8.03/1.47      ( ~ v4_pre_topc(sK1,sK0)
% 8.03/1.47      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
% 8.03/1.47      inference(cnf_transformation,[],[f63]) ).
% 8.03/1.47  
% 8.03/1.47  cnf(c_650,plain,
% 8.03/1.47      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
% 8.03/1.47      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 8.03/1.47      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 8.03/1.47  
% 8.03/1.47  cnf(c_7644,plain,
% 8.03/1.47      ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
% 8.03/1.47      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 8.03/1.47      inference(demodulation,[status(thm)],[c_7274,c_650]) ).
% 8.03/1.47  
% 8.03/1.47  cnf(c_11,plain,
% 8.03/1.47      ( v4_pre_topc(X0,X1)
% 8.03/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 8.03/1.47      | ~ l1_pre_topc(X1)
% 8.03/1.47      | ~ v2_pre_topc(X1)
% 8.03/1.47      | k2_pre_topc(X1,X0) != X0 ),
% 8.03/1.47      inference(cnf_transformation,[],[f54]) ).
% 8.03/1.47  
% 8.03/1.47  cnf(c_897,plain,
% 8.03/1.47      ( v4_pre_topc(sK1,sK0)
% 8.03/1.47      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 8.03/1.47      | ~ l1_pre_topc(sK0)
% 8.03/1.47      | ~ v2_pre_topc(sK0)
% 8.03/1.47      | k2_pre_topc(sK0,sK1) != sK1 ),
% 8.03/1.47      inference(instantiation,[status(thm)],[c_11]) ).
% 8.03/1.47  
% 8.03/1.47  cnf(c_898,plain,
% 8.03/1.47      ( k2_pre_topc(sK0,sK1) != sK1
% 8.03/1.47      | v4_pre_topc(sK1,sK0) = iProver_top
% 8.03/1.47      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.03/1.47      | l1_pre_topc(sK0) != iProver_top
% 8.03/1.47      | v2_pre_topc(sK0) != iProver_top ),
% 8.03/1.47      inference(predicate_to_equality,[status(thm)],[c_897]) ).
% 8.03/1.47  
% 8.03/1.47  cnf(c_24,plain,
% 8.03/1.47      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 8.03/1.47      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 8.03/1.47  
% 8.03/1.47  cnf(c_21,negated_conjecture,
% 8.03/1.47      ( v2_pre_topc(sK0) ),
% 8.03/1.47      inference(cnf_transformation,[],[f59]) ).
% 8.03/1.47  
% 8.03/1.47  cnf(c_22,plain,
% 8.03/1.47      ( v2_pre_topc(sK0) = iProver_top ),
% 8.03/1.47      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 8.03/1.47  
% 8.03/1.47  cnf(contradiction,plain,
% 8.03/1.47      ( $false ),
% 8.03/1.47      inference(minisat,
% 8.03/1.47                [status(thm)],
% 8.03/1.47                [c_31772,c_29528,c_7644,c_898,c_24,c_23,c_22]) ).
% 8.03/1.47  
% 8.03/1.47  
% 8.03/1.47  % SZS output end CNFRefutation for theBenchmark.p
% 8.03/1.47  
% 8.03/1.47  ------                               Statistics
% 8.03/1.47  
% 8.03/1.47  ------ Selected
% 8.03/1.47  
% 8.03/1.47  total_time:                             0.945
% 8.03/1.47  
%------------------------------------------------------------------------------
