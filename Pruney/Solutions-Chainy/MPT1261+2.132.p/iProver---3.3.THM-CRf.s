%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:14:43 EST 2020

% Result     : Theorem 11.44s
% Output     : CNFRefutation 11.44s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 836 expanded)
%              Number of clauses        :   69 ( 218 expanded)
%              Number of leaves         :   18 ( 204 expanded)
%              Depth                    :   22
%              Number of atoms          :  325 (3121 expanded)
%              Number of equality atoms :  162 (1148 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f22,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f43,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1)
            | ~ v4_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f44,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1)
            | ~ v4_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f43])).

fof(f46,plain,(
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

fof(f45,plain,
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

fof(f47,plain,
    ( ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f44,f46,f45])).

fof(f74,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f47])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f75,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f17,axiom,(
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

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f73,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f78,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f48,f58,f58])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f64,f58])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f79,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f57,f58])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f77,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f54,f58])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f40])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f82,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f49])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f68,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f26])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f67,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) != X1
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f76,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f72,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_956,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_967,plain,
    ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_4084,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
    inference(superposition,[status(thm)],[c_956,c_967])).

cnf(c_24,negated_conjecture,
    ( v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_957,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_4253,plain,
    ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4084,c_957])).

cnf(c_18,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_963,plain,
    ( k2_pre_topc(X0,X1) = X1
    | v4_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_6911,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | v4_pre_topc(sK1,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_956,c_963])).

cnf(c_26,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_29,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_7752,plain,
    ( v4_pre_topc(sK1,sK0) != iProver_top
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6911,c_29])).

cnf(c_7753,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_7752])).

cnf(c_7758,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_4253,c_7753])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k4_xboole_0(X2,k4_xboole_0(X2,X0)) = k9_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_966,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k9_subset_1(X2,X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_7371,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,sK1)) = k9_subset_1(u1_struct_0(sK0),X0,sK1) ),
    inference(superposition,[status(thm)],[c_956,c_966])).

cnf(c_9,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1625,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1,c_0])).

cnf(c_2109,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_9,c_1625])).

cnf(c_7406,plain,
    ( k5_xboole_0(k9_subset_1(u1_struct_0(sK0),X0,sK1),k9_subset_1(u1_struct_0(sK0),X0,sK1)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK1)),X0) ),
    inference(superposition,[status(thm)],[c_7371,c_2109])).

cnf(c_7430,plain,
    ( k9_subset_1(u1_struct_0(sK0),X0,sK1) = k4_xboole_0(sK1,k4_xboole_0(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_7371,c_1])).

cnf(c_7493,plain,
    ( k5_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,X0)),k4_xboole_0(sK1,k4_xboole_0(sK1,X0))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK1)),X0) ),
    inference(light_normalisation,[status(thm)],[c_7406,c_7430])).

cnf(c_8339,plain,
    ( k5_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,X0)),k4_xboole_0(sK1,k4_xboole_0(sK1,X0))) = k4_xboole_0(k9_subset_1(u1_struct_0(sK0),X0,sK1),X0) ),
    inference(superposition,[status(thm)],[c_7371,c_7493])).

cnf(c_8435,plain,
    ( k5_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,X0)),k4_xboole_0(sK1,k4_xboole_0(sK1,X0))) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,X0)),X0) ),
    inference(light_normalisation,[status(thm)],[c_8339,c_7430])).

cnf(c_8518,plain,
    ( k5_xboole_0(k4_xboole_0(sK1,k4_xboole_0(X0,k4_xboole_0(X0,sK1))),k4_xboole_0(sK1,k4_xboole_0(X0,k4_xboole_0(X0,sK1)))) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,X0))),k4_xboole_0(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_1,c_8435])).

cnf(c_1740,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1,c_9])).

cnf(c_4,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_973,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_972,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2462,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_973,c_972])).

cnf(c_8854,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,X0),sK1) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_8518,c_9,c_1740,c_2109,c_2462])).

cnf(c_8,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_9076,plain,
    ( k2_xboole_0(sK1,k4_xboole_0(sK1,X0)) = k2_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_8854,c_8])).

cnf(c_7,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_9084,plain,
    ( k2_xboole_0(sK1,k4_xboole_0(sK1,X0)) = sK1 ),
    inference(demodulation,[status(thm)],[c_9076,c_7])).

cnf(c_9162,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_7758,c_9084])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_962,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_968,plain,
    ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_35342,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k2_xboole_0(sK1,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_956,c_968])).

cnf(c_35378,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_962,c_35342])).

cnf(c_36388,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_35378,c_29])).

cnf(c_36389,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_36388])).

cnf(c_36398,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_956,c_36389])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_959,plain,
    ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1391,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_956,c_959])).

cnf(c_1251,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_1761,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1391,c_26,c_25,c_1251])).

cnf(c_36403,plain,
    ( k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_36398,c_1761])).

cnf(c_36417,plain,
    ( k2_pre_topc(sK0,sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_9162,c_36403])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_960,plain,
    ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2438,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_956,c_960])).

cnf(c_1258,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_2713,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2438,c_26,c_25,c_1258])).

cnf(c_36507,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_36417,c_2713])).

cnf(c_17,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | k2_pre_topc(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1244,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | k2_pre_topc(sK0,sK1) != sK1 ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_23,negated_conjecture,
    ( ~ v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_27,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f72])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_36507,c_36417,c_1244,c_23,c_25,c_26,c_27])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:49:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 11.44/2.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.44/2.01  
% 11.44/2.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.44/2.01  
% 11.44/2.01  ------  iProver source info
% 11.44/2.01  
% 11.44/2.01  git: date: 2020-06-30 10:37:57 +0100
% 11.44/2.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.44/2.01  git: non_committed_changes: false
% 11.44/2.01  git: last_make_outside_of_git: false
% 11.44/2.01  
% 11.44/2.01  ------ 
% 11.44/2.01  ------ Parsing...
% 11.44/2.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.44/2.01  
% 11.44/2.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 11.44/2.01  
% 11.44/2.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.44/2.01  
% 11.44/2.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.44/2.01  ------ Proving...
% 11.44/2.01  ------ Problem Properties 
% 11.44/2.01  
% 11.44/2.01  
% 11.44/2.01  clauses                                 27
% 11.44/2.01  conjectures                             5
% 11.44/2.01  EPR                                     4
% 11.44/2.01  Horn                                    26
% 11.44/2.01  unary                                   12
% 11.44/2.01  binary                                  7
% 11.44/2.01  lits                                    54
% 11.44/2.01  lits eq                                 19
% 11.44/2.01  fd_pure                                 0
% 11.44/2.01  fd_pseudo                               0
% 11.44/2.01  fd_cond                                 0
% 11.44/2.01  fd_pseudo_cond                          1
% 11.44/2.01  AC symbols                              0
% 11.44/2.01  
% 11.44/2.01  ------ Input Options Time Limit: Unbounded
% 11.44/2.01  
% 11.44/2.01  
% 11.44/2.01  ------ 
% 11.44/2.01  Current options:
% 11.44/2.01  ------ 
% 11.44/2.01  
% 11.44/2.01  
% 11.44/2.01  
% 11.44/2.01  
% 11.44/2.01  ------ Proving...
% 11.44/2.01  
% 11.44/2.01  
% 11.44/2.01  % SZS status Theorem for theBenchmark.p
% 11.44/2.01  
% 11.44/2.01  % SZS output start CNFRefutation for theBenchmark.p
% 11.44/2.01  
% 11.44/2.01  fof(f22,conjecture,(
% 11.44/2.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 11.44/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.44/2.01  
% 11.44/2.01  fof(f23,negated_conjecture,(
% 11.44/2.01    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 11.44/2.01    inference(negated_conjecture,[],[f22])).
% 11.44/2.01  
% 11.44/2.01  fof(f38,plain,(
% 11.44/2.01    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 11.44/2.01    inference(ennf_transformation,[],[f23])).
% 11.44/2.01  
% 11.44/2.01  fof(f39,plain,(
% 11.44/2.01    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 11.44/2.01    inference(flattening,[],[f38])).
% 11.44/2.01  
% 11.44/2.01  fof(f43,plain,(
% 11.44/2.01    ? [X0] : (? [X1] : (((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 11.44/2.01    inference(nnf_transformation,[],[f39])).
% 11.44/2.01  
% 11.44/2.01  fof(f44,plain,(
% 11.44/2.01    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 11.44/2.01    inference(flattening,[],[f43])).
% 11.44/2.01  
% 11.44/2.01  fof(f46,plain,(
% 11.44/2.01    ( ! [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) != k2_tops_1(X0,sK1) | ~v4_pre_topc(sK1,X0)) & (k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) = k2_tops_1(X0,sK1) | v4_pre_topc(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 11.44/2.01    introduced(choice_axiom,[])).
% 11.44/2.01  
% 11.44/2.01  fof(f45,plain,(
% 11.44/2.01    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) != k2_tops_1(sK0,X1) | ~v4_pre_topc(X1,sK0)) & (k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) = k2_tops_1(sK0,X1) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 11.44/2.01    introduced(choice_axiom,[])).
% 11.44/2.01  
% 11.44/2.01  fof(f47,plain,(
% 11.44/2.01    ((k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)) & (k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 11.44/2.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f44,f46,f45])).
% 11.44/2.01  
% 11.44/2.01  fof(f74,plain,(
% 11.44/2.01    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 11.44/2.01    inference(cnf_transformation,[],[f47])).
% 11.44/2.01  
% 11.44/2.01  fof(f13,axiom,(
% 11.44/2.01    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 11.44/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.44/2.01  
% 11.44/2.01  fof(f28,plain,(
% 11.44/2.01    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.44/2.01    inference(ennf_transformation,[],[f13])).
% 11.44/2.01  
% 11.44/2.01  fof(f63,plain,(
% 11.44/2.01    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.44/2.01    inference(cnf_transformation,[],[f28])).
% 11.44/2.01  
% 11.44/2.01  fof(f75,plain,(
% 11.44/2.01    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)),
% 11.44/2.01    inference(cnf_transformation,[],[f47])).
% 11.44/2.01  
% 11.44/2.01  fof(f17,axiom,(
% 11.44/2.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 11.44/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.44/2.01  
% 11.44/2.01  fof(f30,plain,(
% 11.44/2.01    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.44/2.01    inference(ennf_transformation,[],[f17])).
% 11.44/2.01  
% 11.44/2.01  fof(f31,plain,(
% 11.44/2.01    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.44/2.01    inference(flattening,[],[f30])).
% 11.44/2.01  
% 11.44/2.01  fof(f66,plain,(
% 11.44/2.01    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.44/2.01    inference(cnf_transformation,[],[f31])).
% 11.44/2.01  
% 11.44/2.01  fof(f73,plain,(
% 11.44/2.01    l1_pre_topc(sK0)),
% 11.44/2.01    inference(cnf_transformation,[],[f47])).
% 11.44/2.01  
% 11.44/2.01  fof(f1,axiom,(
% 11.44/2.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 11.44/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.44/2.01  
% 11.44/2.01  fof(f48,plain,(
% 11.44/2.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 11.44/2.01    inference(cnf_transformation,[],[f1])).
% 11.44/2.01  
% 11.44/2.01  fof(f8,axiom,(
% 11.44/2.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 11.44/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.44/2.01  
% 11.44/2.01  fof(f58,plain,(
% 11.44/2.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 11.44/2.01    inference(cnf_transformation,[],[f8])).
% 11.44/2.01  
% 11.44/2.01  fof(f78,plain,(
% 11.44/2.01    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 11.44/2.01    inference(definition_unfolding,[],[f48,f58,f58])).
% 11.44/2.01  
% 11.44/2.01  fof(f14,axiom,(
% 11.44/2.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 11.44/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.44/2.01  
% 11.44/2.01  fof(f29,plain,(
% 11.44/2.01    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 11.44/2.01    inference(ennf_transformation,[],[f14])).
% 11.44/2.01  
% 11.44/2.01  fof(f64,plain,(
% 11.44/2.01    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 11.44/2.01    inference(cnf_transformation,[],[f29])).
% 11.44/2.01  
% 11.44/2.01  fof(f80,plain,(
% 11.44/2.01    ( ! [X2,X0,X1] : (k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 11.44/2.01    inference(definition_unfolding,[],[f64,f58])).
% 11.44/2.01  
% 11.44/2.01  fof(f7,axiom,(
% 11.44/2.01    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 11.44/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.44/2.01  
% 11.44/2.01  fof(f57,plain,(
% 11.44/2.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 11.44/2.01    inference(cnf_transformation,[],[f7])).
% 11.44/2.01  
% 11.44/2.01  fof(f79,plain,(
% 11.44/2.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 11.44/2.01    inference(definition_unfolding,[],[f57,f58])).
% 11.44/2.01  
% 11.44/2.01  fof(f4,axiom,(
% 11.44/2.01    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 11.44/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.44/2.01  
% 11.44/2.01  fof(f54,plain,(
% 11.44/2.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 11.44/2.01    inference(cnf_transformation,[],[f4])).
% 11.44/2.01  
% 11.44/2.01  fof(f77,plain,(
% 11.44/2.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 11.44/2.01    inference(definition_unfolding,[],[f54,f58])).
% 11.44/2.01  
% 11.44/2.01  fof(f2,axiom,(
% 11.44/2.01    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 11.44/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.44/2.01  
% 11.44/2.01  fof(f40,plain,(
% 11.44/2.01    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.44/2.01    inference(nnf_transformation,[],[f2])).
% 11.44/2.01  
% 11.44/2.01  fof(f41,plain,(
% 11.44/2.01    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.44/2.01    inference(flattening,[],[f40])).
% 11.44/2.01  
% 11.44/2.01  fof(f49,plain,(
% 11.44/2.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 11.44/2.01    inference(cnf_transformation,[],[f41])).
% 11.44/2.01  
% 11.44/2.01  fof(f82,plain,(
% 11.44/2.01    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 11.44/2.01    inference(equality_resolution,[],[f49])).
% 11.44/2.01  
% 11.44/2.01  fof(f3,axiom,(
% 11.44/2.01    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 11.44/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.44/2.01  
% 11.44/2.01  fof(f42,plain,(
% 11.44/2.01    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 11.44/2.01    inference(nnf_transformation,[],[f3])).
% 11.44/2.01  
% 11.44/2.01  fof(f53,plain,(
% 11.44/2.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 11.44/2.01    inference(cnf_transformation,[],[f42])).
% 11.44/2.01  
% 11.44/2.01  fof(f6,axiom,(
% 11.44/2.01    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 11.44/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.44/2.01  
% 11.44/2.01  fof(f56,plain,(
% 11.44/2.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 11.44/2.01    inference(cnf_transformation,[],[f6])).
% 11.44/2.01  
% 11.44/2.01  fof(f5,axiom,(
% 11.44/2.01    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 11.44/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.44/2.01  
% 11.44/2.01  fof(f55,plain,(
% 11.44/2.01    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 11.44/2.01    inference(cnf_transformation,[],[f5])).
% 11.44/2.01  
% 11.44/2.01  fof(f18,axiom,(
% 11.44/2.01    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 11.44/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.44/2.01  
% 11.44/2.01  fof(f32,plain,(
% 11.44/2.01    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 11.44/2.01    inference(ennf_transformation,[],[f18])).
% 11.44/2.01  
% 11.44/2.01  fof(f33,plain,(
% 11.44/2.01    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 11.44/2.01    inference(flattening,[],[f32])).
% 11.44/2.01  
% 11.44/2.01  fof(f68,plain,(
% 11.44/2.01    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.44/2.01    inference(cnf_transformation,[],[f33])).
% 11.44/2.01  
% 11.44/2.01  fof(f12,axiom,(
% 11.44/2.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 11.44/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.44/2.01  
% 11.44/2.01  fof(f26,plain,(
% 11.44/2.01    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 11.44/2.01    inference(ennf_transformation,[],[f12])).
% 11.44/2.01  
% 11.44/2.01  fof(f27,plain,(
% 11.44/2.01    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.44/2.01    inference(flattening,[],[f26])).
% 11.44/2.01  
% 11.44/2.01  fof(f62,plain,(
% 11.44/2.01    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.44/2.01    inference(cnf_transformation,[],[f27])).
% 11.44/2.01  
% 11.44/2.01  fof(f21,axiom,(
% 11.44/2.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)))),
% 11.44/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.44/2.01  
% 11.44/2.01  fof(f37,plain,(
% 11.44/2.01    ! [X0] : (! [X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.44/2.01    inference(ennf_transformation,[],[f21])).
% 11.44/2.01  
% 11.44/2.01  fof(f71,plain,(
% 11.44/2.01    ( ! [X0,X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.44/2.01    inference(cnf_transformation,[],[f37])).
% 11.44/2.01  
% 11.44/2.01  fof(f20,axiom,(
% 11.44/2.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)))),
% 11.44/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.44/2.01  
% 11.44/2.01  fof(f36,plain,(
% 11.44/2.01    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.44/2.01    inference(ennf_transformation,[],[f20])).
% 11.44/2.01  
% 11.44/2.01  fof(f70,plain,(
% 11.44/2.01    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.44/2.01    inference(cnf_transformation,[],[f36])).
% 11.44/2.01  
% 11.44/2.01  fof(f67,plain,(
% 11.44/2.01    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.44/2.01    inference(cnf_transformation,[],[f31])).
% 11.44/2.01  
% 11.44/2.01  fof(f76,plain,(
% 11.44/2.01    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)),
% 11.44/2.01    inference(cnf_transformation,[],[f47])).
% 11.44/2.01  
% 11.44/2.01  fof(f72,plain,(
% 11.44/2.01    v2_pre_topc(sK0)),
% 11.44/2.01    inference(cnf_transformation,[],[f47])).
% 11.44/2.01  
% 11.44/2.01  cnf(c_25,negated_conjecture,
% 11.44/2.01      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 11.44/2.01      inference(cnf_transformation,[],[f74]) ).
% 11.44/2.01  
% 11.44/2.01  cnf(c_956,plain,
% 11.44/2.01      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 11.44/2.01      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 11.44/2.01  
% 11.44/2.01  cnf(c_14,plain,
% 11.44/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.44/2.01      | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 11.44/2.01      inference(cnf_transformation,[],[f63]) ).
% 11.44/2.01  
% 11.44/2.01  cnf(c_967,plain,
% 11.44/2.01      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
% 11.44/2.01      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 11.44/2.01      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 11.44/2.01  
% 11.44/2.01  cnf(c_4084,plain,
% 11.44/2.01      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
% 11.44/2.01      inference(superposition,[status(thm)],[c_956,c_967]) ).
% 11.44/2.01  
% 11.44/2.01  cnf(c_24,negated_conjecture,
% 11.44/2.01      ( v4_pre_topc(sK1,sK0)
% 11.44/2.01      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 11.44/2.01      inference(cnf_transformation,[],[f75]) ).
% 11.44/2.01  
% 11.44/2.01  cnf(c_957,plain,
% 11.44/2.01      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 11.44/2.01      | v4_pre_topc(sK1,sK0) = iProver_top ),
% 11.44/2.01      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 11.44/2.01  
% 11.44/2.01  cnf(c_4253,plain,
% 11.44/2.01      ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 11.44/2.01      | v4_pre_topc(sK1,sK0) = iProver_top ),
% 11.44/2.01      inference(demodulation,[status(thm)],[c_4084,c_957]) ).
% 11.44/2.01  
% 11.44/2.01  cnf(c_18,plain,
% 11.44/2.01      ( ~ v4_pre_topc(X0,X1)
% 11.44/2.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.44/2.01      | ~ l1_pre_topc(X1)
% 11.44/2.01      | k2_pre_topc(X1,X0) = X0 ),
% 11.44/2.01      inference(cnf_transformation,[],[f66]) ).
% 11.44/2.01  
% 11.44/2.01  cnf(c_963,plain,
% 11.44/2.01      ( k2_pre_topc(X0,X1) = X1
% 11.44/2.01      | v4_pre_topc(X1,X0) != iProver_top
% 11.44/2.01      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 11.44/2.01      | l1_pre_topc(X0) != iProver_top ),
% 11.44/2.01      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 11.44/2.01  
% 11.44/2.01  cnf(c_6911,plain,
% 11.44/2.01      ( k2_pre_topc(sK0,sK1) = sK1
% 11.44/2.01      | v4_pre_topc(sK1,sK0) != iProver_top
% 11.44/2.01      | l1_pre_topc(sK0) != iProver_top ),
% 11.44/2.01      inference(superposition,[status(thm)],[c_956,c_963]) ).
% 11.44/2.01  
% 11.44/2.01  cnf(c_26,negated_conjecture,
% 11.44/2.01      ( l1_pre_topc(sK0) ),
% 11.44/2.01      inference(cnf_transformation,[],[f73]) ).
% 11.44/2.01  
% 11.44/2.01  cnf(c_29,plain,
% 11.44/2.01      ( l1_pre_topc(sK0) = iProver_top ),
% 11.44/2.01      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 11.44/2.01  
% 11.44/2.01  cnf(c_7752,plain,
% 11.44/2.01      ( v4_pre_topc(sK1,sK0) != iProver_top
% 11.44/2.01      | k2_pre_topc(sK0,sK1) = sK1 ),
% 11.44/2.01      inference(global_propositional_subsumption,
% 11.44/2.01                [status(thm)],
% 11.44/2.01                [c_6911,c_29]) ).
% 11.44/2.01  
% 11.44/2.01  cnf(c_7753,plain,
% 11.44/2.01      ( k2_pre_topc(sK0,sK1) = sK1
% 11.44/2.01      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 11.44/2.01      inference(renaming,[status(thm)],[c_7752]) ).
% 11.44/2.01  
% 11.44/2.01  cnf(c_7758,plain,
% 11.44/2.01      ( k2_pre_topc(sK0,sK1) = sK1
% 11.44/2.01      | k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 11.44/2.01      inference(superposition,[status(thm)],[c_4253,c_7753]) ).
% 11.44/2.01  
% 11.44/2.01  cnf(c_1,plain,
% 11.44/2.01      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 11.44/2.01      inference(cnf_transformation,[],[f78]) ).
% 11.44/2.01  
% 11.44/2.01  cnf(c_15,plain,
% 11.44/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.44/2.01      | k4_xboole_0(X2,k4_xboole_0(X2,X0)) = k9_subset_1(X1,X2,X0) ),
% 11.44/2.01      inference(cnf_transformation,[],[f80]) ).
% 11.44/2.01  
% 11.44/2.01  cnf(c_966,plain,
% 11.44/2.01      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k9_subset_1(X2,X0,X1)
% 11.44/2.01      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 11.44/2.01      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 11.44/2.01  
% 11.44/2.01  cnf(c_7371,plain,
% 11.44/2.01      ( k4_xboole_0(X0,k4_xboole_0(X0,sK1)) = k9_subset_1(u1_struct_0(sK0),X0,sK1) ),
% 11.44/2.01      inference(superposition,[status(thm)],[c_956,c_966]) ).
% 11.44/2.01  
% 11.44/2.01  cnf(c_9,plain,
% 11.44/2.01      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 11.44/2.01      inference(cnf_transformation,[],[f79]) ).
% 11.44/2.01  
% 11.44/2.01  cnf(c_0,plain,
% 11.44/2.01      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 11.44/2.01      inference(cnf_transformation,[],[f77]) ).
% 11.44/2.01  
% 11.44/2.01  cnf(c_1625,plain,
% 11.44/2.01      ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 11.44/2.01      inference(superposition,[status(thm)],[c_1,c_0]) ).
% 11.44/2.01  
% 11.44/2.01  cnf(c_2109,plain,
% 11.44/2.01      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 11.44/2.01      inference(superposition,[status(thm)],[c_9,c_1625]) ).
% 11.44/2.01  
% 11.44/2.01  cnf(c_7406,plain,
% 11.44/2.01      ( k5_xboole_0(k9_subset_1(u1_struct_0(sK0),X0,sK1),k9_subset_1(u1_struct_0(sK0),X0,sK1)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK1)),X0) ),
% 11.44/2.01      inference(superposition,[status(thm)],[c_7371,c_2109]) ).
% 11.44/2.01  
% 11.44/2.01  cnf(c_7430,plain,
% 11.44/2.01      ( k9_subset_1(u1_struct_0(sK0),X0,sK1) = k4_xboole_0(sK1,k4_xboole_0(sK1,X0)) ),
% 11.44/2.01      inference(superposition,[status(thm)],[c_7371,c_1]) ).
% 11.44/2.01  
% 11.44/2.01  cnf(c_7493,plain,
% 11.44/2.01      ( k5_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,X0)),k4_xboole_0(sK1,k4_xboole_0(sK1,X0))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK1)),X0) ),
% 11.44/2.01      inference(light_normalisation,[status(thm)],[c_7406,c_7430]) ).
% 11.44/2.01  
% 11.44/2.01  cnf(c_8339,plain,
% 11.44/2.01      ( k5_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,X0)),k4_xboole_0(sK1,k4_xboole_0(sK1,X0))) = k4_xboole_0(k9_subset_1(u1_struct_0(sK0),X0,sK1),X0) ),
% 11.44/2.01      inference(superposition,[status(thm)],[c_7371,c_7493]) ).
% 11.44/2.01  
% 11.44/2.01  cnf(c_8435,plain,
% 11.44/2.01      ( k5_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,X0)),k4_xboole_0(sK1,k4_xboole_0(sK1,X0))) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,X0)),X0) ),
% 11.44/2.01      inference(light_normalisation,[status(thm)],[c_8339,c_7430]) ).
% 11.44/2.01  
% 11.44/2.01  cnf(c_8518,plain,
% 11.44/2.01      ( k5_xboole_0(k4_xboole_0(sK1,k4_xboole_0(X0,k4_xboole_0(X0,sK1))),k4_xboole_0(sK1,k4_xboole_0(X0,k4_xboole_0(X0,sK1)))) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,X0))),k4_xboole_0(sK1,X0)) ),
% 11.44/2.01      inference(superposition,[status(thm)],[c_1,c_8435]) ).
% 11.44/2.01  
% 11.44/2.01  cnf(c_1740,plain,
% 11.44/2.01      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 11.44/2.01      inference(superposition,[status(thm)],[c_1,c_9]) ).
% 11.44/2.01  
% 11.44/2.01  cnf(c_4,plain,
% 11.44/2.01      ( r1_tarski(X0,X0) ),
% 11.44/2.01      inference(cnf_transformation,[],[f82]) ).
% 11.44/2.01  
% 11.44/2.01  cnf(c_973,plain,
% 11.44/2.01      ( r1_tarski(X0,X0) = iProver_top ),
% 11.44/2.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 11.44/2.01  
% 11.44/2.01  cnf(c_5,plain,
% 11.44/2.01      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 11.44/2.01      inference(cnf_transformation,[],[f53]) ).
% 11.44/2.01  
% 11.44/2.01  cnf(c_972,plain,
% 11.44/2.01      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 11.44/2.01      | r1_tarski(X0,X1) != iProver_top ),
% 11.44/2.01      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 11.44/2.01  
% 11.44/2.01  cnf(c_2462,plain,
% 11.44/2.01      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 11.44/2.01      inference(superposition,[status(thm)],[c_973,c_972]) ).
% 11.44/2.01  
% 11.44/2.01  cnf(c_8854,plain,
% 11.44/2.01      ( k4_xboole_0(k4_xboole_0(sK1,X0),sK1) = k1_xboole_0 ),
% 11.44/2.01      inference(demodulation,
% 11.44/2.01                [status(thm)],
% 11.44/2.01                [c_8518,c_9,c_1740,c_2109,c_2462]) ).
% 11.44/2.01  
% 11.44/2.01  cnf(c_8,plain,
% 11.44/2.01      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 11.44/2.01      inference(cnf_transformation,[],[f56]) ).
% 11.44/2.01  
% 11.44/2.01  cnf(c_9076,plain,
% 11.44/2.01      ( k2_xboole_0(sK1,k4_xboole_0(sK1,X0)) = k2_xboole_0(sK1,k1_xboole_0) ),
% 11.44/2.01      inference(superposition,[status(thm)],[c_8854,c_8]) ).
% 11.44/2.01  
% 11.44/2.01  cnf(c_7,plain,
% 11.44/2.01      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 11.44/2.01      inference(cnf_transformation,[],[f55]) ).
% 11.44/2.01  
% 11.44/2.01  cnf(c_9084,plain,
% 11.44/2.01      ( k2_xboole_0(sK1,k4_xboole_0(sK1,X0)) = sK1 ),
% 11.44/2.01      inference(demodulation,[status(thm)],[c_9076,c_7]) ).
% 11.44/2.01  
% 11.44/2.01  cnf(c_9162,plain,
% 11.44/2.01      ( k2_pre_topc(sK0,sK1) = sK1
% 11.44/2.01      | k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = sK1 ),
% 11.44/2.01      inference(superposition,[status(thm)],[c_7758,c_9084]) ).
% 11.44/2.01  
% 11.44/2.01  cnf(c_19,plain,
% 11.44/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.44/2.01      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 11.44/2.01      | ~ l1_pre_topc(X1) ),
% 11.44/2.01      inference(cnf_transformation,[],[f68]) ).
% 11.44/2.01  
% 11.44/2.01  cnf(c_962,plain,
% 11.44/2.01      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 11.44/2.01      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 11.44/2.01      | l1_pre_topc(X1) != iProver_top ),
% 11.44/2.01      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 11.44/2.01  
% 11.44/2.01  cnf(c_13,plain,
% 11.44/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.44/2.01      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 11.44/2.01      | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
% 11.44/2.01      inference(cnf_transformation,[],[f62]) ).
% 11.44/2.01  
% 11.44/2.01  cnf(c_968,plain,
% 11.44/2.01      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
% 11.44/2.01      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
% 11.44/2.01      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 11.44/2.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 11.44/2.01  
% 11.44/2.01  cnf(c_35342,plain,
% 11.44/2.01      ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k2_xboole_0(sK1,X0)
% 11.44/2.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 11.44/2.01      inference(superposition,[status(thm)],[c_956,c_968]) ).
% 11.44/2.01  
% 11.44/2.01  cnf(c_35378,plain,
% 11.44/2.01      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0))
% 11.44/2.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.44/2.01      | l1_pre_topc(sK0) != iProver_top ),
% 11.44/2.01      inference(superposition,[status(thm)],[c_962,c_35342]) ).
% 11.44/2.01  
% 11.44/2.01  cnf(c_36388,plain,
% 11.44/2.01      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.44/2.01      | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0)) ),
% 11.44/2.01      inference(global_propositional_subsumption,
% 11.44/2.01                [status(thm)],
% 11.44/2.01                [c_35378,c_29]) ).
% 11.44/2.01  
% 11.44/2.01  cnf(c_36389,plain,
% 11.44/2.01      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0))
% 11.44/2.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 11.44/2.01      inference(renaming,[status(thm)],[c_36388]) ).
% 11.44/2.01  
% 11.44/2.01  cnf(c_36398,plain,
% 11.44/2.01      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
% 11.44/2.01      inference(superposition,[status(thm)],[c_956,c_36389]) ).
% 11.44/2.01  
% 11.44/2.01  cnf(c_22,plain,
% 11.44/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.44/2.01      | ~ l1_pre_topc(X1)
% 11.44/2.01      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
% 11.44/2.01      inference(cnf_transformation,[],[f71]) ).
% 11.44/2.01  
% 11.44/2.01  cnf(c_959,plain,
% 11.44/2.01      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
% 11.44/2.01      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 11.44/2.01      | l1_pre_topc(X0) != iProver_top ),
% 11.44/2.01      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 11.44/2.01  
% 11.44/2.01  cnf(c_1391,plain,
% 11.44/2.01      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
% 11.44/2.01      | l1_pre_topc(sK0) != iProver_top ),
% 11.44/2.01      inference(superposition,[status(thm)],[c_956,c_959]) ).
% 11.44/2.01  
% 11.44/2.01  cnf(c_1251,plain,
% 11.44/2.01      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.44/2.01      | ~ l1_pre_topc(sK0)
% 11.44/2.01      | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 11.44/2.01      inference(instantiation,[status(thm)],[c_22]) ).
% 11.44/2.01  
% 11.44/2.01  cnf(c_1761,plain,
% 11.44/2.01      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 11.44/2.01      inference(global_propositional_subsumption,
% 11.44/2.01                [status(thm)],
% 11.44/2.01                [c_1391,c_26,c_25,c_1251]) ).
% 11.44/2.01  
% 11.44/2.01  cnf(c_36403,plain,
% 11.44/2.01      ( k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 11.44/2.01      inference(light_normalisation,[status(thm)],[c_36398,c_1761]) ).
% 11.44/2.01  
% 11.44/2.01  cnf(c_36417,plain,
% 11.44/2.01      ( k2_pre_topc(sK0,sK1) = sK1 ),
% 11.44/2.01      inference(superposition,[status(thm)],[c_9162,c_36403]) ).
% 11.44/2.01  
% 11.44/2.01  cnf(c_21,plain,
% 11.44/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.44/2.01      | ~ l1_pre_topc(X1)
% 11.44/2.01      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
% 11.44/2.01      inference(cnf_transformation,[],[f70]) ).
% 11.44/2.01  
% 11.44/2.01  cnf(c_960,plain,
% 11.44/2.01      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
% 11.44/2.01      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 11.44/2.01      | l1_pre_topc(X0) != iProver_top ),
% 11.44/2.01      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 11.44/2.01  
% 11.44/2.01  cnf(c_2438,plain,
% 11.44/2.01      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 11.44/2.01      | l1_pre_topc(sK0) != iProver_top ),
% 11.44/2.01      inference(superposition,[status(thm)],[c_956,c_960]) ).
% 11.44/2.01  
% 11.44/2.01  cnf(c_1258,plain,
% 11.44/2.01      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.44/2.01      | ~ l1_pre_topc(sK0)
% 11.44/2.01      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 11.44/2.01      inference(instantiation,[status(thm)],[c_21]) ).
% 11.44/2.01  
% 11.44/2.01  cnf(c_2713,plain,
% 11.44/2.01      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 11.44/2.01      inference(global_propositional_subsumption,
% 11.44/2.01                [status(thm)],
% 11.44/2.01                [c_2438,c_26,c_25,c_1258]) ).
% 11.44/2.01  
% 11.44/2.01  cnf(c_36507,plain,
% 11.44/2.01      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 11.44/2.01      inference(demodulation,[status(thm)],[c_36417,c_2713]) ).
% 11.44/2.01  
% 11.44/2.01  cnf(c_17,plain,
% 11.44/2.01      ( v4_pre_topc(X0,X1)
% 11.44/2.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.44/2.01      | ~ l1_pre_topc(X1)
% 11.44/2.01      | ~ v2_pre_topc(X1)
% 11.44/2.01      | k2_pre_topc(X1,X0) != X0 ),
% 11.44/2.01      inference(cnf_transformation,[],[f67]) ).
% 11.44/2.01  
% 11.44/2.01  cnf(c_1244,plain,
% 11.44/2.01      ( v4_pre_topc(sK1,sK0)
% 11.44/2.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.44/2.01      | ~ l1_pre_topc(sK0)
% 11.44/2.01      | ~ v2_pre_topc(sK0)
% 11.44/2.01      | k2_pre_topc(sK0,sK1) != sK1 ),
% 11.44/2.01      inference(instantiation,[status(thm)],[c_17]) ).
% 11.44/2.01  
% 11.44/2.01  cnf(c_23,negated_conjecture,
% 11.44/2.01      ( ~ v4_pre_topc(sK1,sK0)
% 11.44/2.01      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
% 11.44/2.01      inference(cnf_transformation,[],[f76]) ).
% 11.44/2.01  
% 11.44/2.01  cnf(c_27,negated_conjecture,
% 11.44/2.01      ( v2_pre_topc(sK0) ),
% 11.44/2.01      inference(cnf_transformation,[],[f72]) ).
% 11.44/2.01  
% 11.44/2.01  cnf(contradiction,plain,
% 11.44/2.01      ( $false ),
% 11.44/2.01      inference(minisat,
% 11.44/2.01                [status(thm)],
% 11.44/2.01                [c_36507,c_36417,c_1244,c_23,c_25,c_26,c_27]) ).
% 11.44/2.01  
% 11.44/2.01  
% 11.44/2.01  % SZS output end CNFRefutation for theBenchmark.p
% 11.44/2.01  
% 11.44/2.01  ------                               Statistics
% 11.44/2.01  
% 11.44/2.01  ------ Selected
% 11.44/2.01  
% 11.44/2.01  total_time:                             1.022
% 11.44/2.01  
%------------------------------------------------------------------------------
