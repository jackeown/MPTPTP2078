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
% DateTime   : Thu Dec  3 12:14:33 EST 2020

% Result     : Theorem 11.53s
% Output     : CNFRefutation 11.53s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 912 expanded)
%              Number of clauses        :   89 ( 277 expanded)
%              Number of leaves         :   20 ( 224 expanded)
%              Depth                    :   24
%              Number of atoms          :  354 (2561 expanded)
%              Number of equality atoms :  181 (1128 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    6 (   2 average)

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

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

fof(f63,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f14])).

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
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f61,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f62,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f40])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f44,f48])).

fof(f13,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f70,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(definition_unfolding,[],[f53,f48])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f65,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f42,f48])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f41,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f21])).

fof(f66,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f41,f48])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f56,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f9,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k4_xboole_0(X2,X1)) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f51,f49])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f67,plain,(
    ! [X0] : k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(definition_unfolding,[],[f43,f49])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f64,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) != X1
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f60,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_18,negated_conjecture,
    ( v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_136,plain,
    ( v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(prop_impl,[status(thm)],[c_18])).

cnf(c_12,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_20,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_336,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,X0) = X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_20])).

cnf(c_337,plain,
    ( ~ v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_336])).

cnf(c_383,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,X0) = X0
    | sK1 != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_136,c_337])).

cnf(c_384,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(unflattening,[status(thm)],[c_383])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_386,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_384,c_19])).

cnf(c_476,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(prop_impl,[status(thm)],[c_386])).

cnf(c_477,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(renaming,[status(thm)],[c_476])).

cnf(c_893,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_894,plain,
    ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4727,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
    inference(superposition,[status(thm)],[c_893,c_894])).

cnf(c_4795,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_477,c_4727])).

cnf(c_5,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_896,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_7717,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_4795,c_896])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_898,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_10,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_900,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_898,c_10])).

cnf(c_8197,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),sK1)) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_7717,c_900])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_899,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_0,c_10])).

cnf(c_12647,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k5_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) = k4_xboole_0(k2_tops_1(sK0,sK1),sK1) ),
    inference(superposition,[status(thm)],[c_8197,c_899])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1833,plain,
    ( k1_setfam_1(k2_tarski(X0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_10,c_1])).

cnf(c_3452,plain,
    ( k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_1833,c_899])).

cnf(c_4,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_897,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_4607,plain,
    ( k1_setfam_1(k2_tarski(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_897,c_900])).

cnf(c_7,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_6,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1831,plain,
    ( k1_setfam_1(k2_tarski(X0,k1_xboole_0)) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_6,c_10])).

cnf(c_2404,plain,
    ( k1_setfam_1(k2_tarski(k1_xboole_0,X0)) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_7,c_1831])).

cnf(c_5755,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4607,c_2404])).

cnf(c_6051,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3452,c_3452,c_5755])).

cnf(c_12657,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k4_xboole_0(k2_tops_1(sK0,sK1),sK1) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_12647,c_6051])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_324,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_20])).

cnf(c_325,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_324])).

cnf(c_890,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_325])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k5_xboole_0(X2,k4_xboole_0(X0,X2)) = k4_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_895,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k4_subset_1(X2,X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2782,plain,
    ( k5_xboole_0(X0,k4_xboole_0(k2_tops_1(sK0,X1),X0)) = k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X1))
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_890,c_895])).

cnf(c_3346,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k5_xboole_0(sK1,k4_xboole_0(k2_tops_1(sK0,X0),sK1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_893,c_2782])).

cnf(c_3873,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k4_xboole_0(k2_tops_1(sK0,sK1),sK1)) ),
    inference(superposition,[status(thm)],[c_893,c_3346])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_300,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_20])).

cnf(c_301,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_300])).

cnf(c_892,plain,
    ( k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_301])).

cnf(c_994,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_893,c_892])).

cnf(c_3875,plain,
    ( k5_xboole_0(sK1,k4_xboole_0(k2_tops_1(sK0,sK1),sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_3873,c_994])).

cnf(c_33456,plain,
    ( k2_pre_topc(sK0,sK1) = k5_xboole_0(sK1,k1_xboole_0)
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_12657,c_3875])).

cnf(c_1832,plain,
    ( k1_setfam_1(k2_tarski(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(superposition,[status(thm)],[c_10,c_10])).

cnf(c_4623,plain,
    ( k1_setfam_1(k2_tarski(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0))) ),
    inference(superposition,[status(thm)],[c_7,c_1832])).

cnf(c_2,plain,
    ( k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1834,plain,
    ( k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),k1_setfam_1(k2_tarski(k1_xboole_0,X0))) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_10,c_2])).

cnf(c_4266,plain,
    ( k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_7,c_1834])).

cnf(c_4710,plain,
    ( k5_xboole_0(k1_setfam_1(k2_tarski(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))),k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0,k1_xboole_0)),k1_xboole_0))) = k4_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) ),
    inference(superposition,[status(thm)],[c_4623,c_4266])).

cnf(c_4718,plain,
    ( k5_xboole_0(k1_setfam_1(k2_tarski(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))),k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0,k1_xboole_0)),k1_xboole_0))) = k1_setfam_1(k2_tarski(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) ),
    inference(demodulation,[status(thm)],[c_4710,c_4623])).

cnf(c_3455,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_7,c_899])).

cnf(c_2330,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_10,c_896])).

cnf(c_2499,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_2330])).

cnf(c_4611,plain,
    ( k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(superposition,[status(thm)],[c_2499,c_900])).

cnf(c_4719,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4718,c_3455,c_4607,c_4611])).

cnf(c_5657,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(demodulation,[status(thm)],[c_4719,c_2])).

cnf(c_33457,plain,
    ( k2_pre_topc(sK0,sK1) = sK1 ),
    inference(demodulation,[status(thm)],[c_33456,c_5657])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_312,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_20])).

cnf(c_313,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_312])).

cnf(c_891,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_313])).

cnf(c_1047,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_893,c_891])).

cnf(c_33579,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_33457,c_1047])).

cnf(c_17,negated_conjecture,
    ( ~ v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_134,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
    inference(prop_impl,[status(thm)],[c_17])).

cnf(c_11,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | k2_pre_topc(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_21,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_272,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_21])).

cnf(c_273,plain,
    ( v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k2_pre_topc(sK0,X0) != X0 ),
    inference(unflattening,[status(thm)],[c_272])).

cnf(c_277,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(X0,sK0)
    | k2_pre_topc(sK0,X0) != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_273,c_20])).

cnf(c_278,plain,
    ( v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,X0) != X0 ),
    inference(renaming,[status(thm)],[c_277])).

cnf(c_394,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,X0) != X0
    | sK1 != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_134,c_278])).

cnf(c_395,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,sK1) != sK1 ),
    inference(unflattening,[status(thm)],[c_394])).

cnf(c_397,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,sK1) != sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_395,c_19])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_33579,c_33457,c_397])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n024.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 09:33:51 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 11.53/1.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.53/1.99  
% 11.53/1.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.53/1.99  
% 11.53/1.99  ------  iProver source info
% 11.53/1.99  
% 11.53/1.99  git: date: 2020-06-30 10:37:57 +0100
% 11.53/1.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.53/1.99  git: non_committed_changes: false
% 11.53/1.99  git: last_make_outside_of_git: false
% 11.53/1.99  
% 11.53/1.99  ------ 
% 11.53/1.99  
% 11.53/1.99  ------ Input Options
% 11.53/1.99  
% 11.53/1.99  --out_options                           all
% 11.53/1.99  --tptp_safe_out                         true
% 11.53/1.99  --problem_path                          ""
% 11.53/1.99  --include_path                          ""
% 11.53/1.99  --clausifier                            res/vclausify_rel
% 11.53/1.99  --clausifier_options                    ""
% 11.53/1.99  --stdin                                 false
% 11.53/1.99  --stats_out                             all
% 11.53/1.99  
% 11.53/1.99  ------ General Options
% 11.53/1.99  
% 11.53/1.99  --fof                                   false
% 11.53/1.99  --time_out_real                         305.
% 11.53/1.99  --time_out_virtual                      -1.
% 11.53/1.99  --symbol_type_check                     false
% 11.53/1.99  --clausify_out                          false
% 11.53/1.99  --sig_cnt_out                           false
% 11.53/1.99  --trig_cnt_out                          false
% 11.53/1.99  --trig_cnt_out_tolerance                1.
% 11.53/1.99  --trig_cnt_out_sk_spl                   false
% 11.53/1.99  --abstr_cl_out                          false
% 11.53/1.99  
% 11.53/1.99  ------ Global Options
% 11.53/1.99  
% 11.53/1.99  --schedule                              default
% 11.53/1.99  --add_important_lit                     false
% 11.53/1.99  --prop_solver_per_cl                    1000
% 11.53/1.99  --min_unsat_core                        false
% 11.53/1.99  --soft_assumptions                      false
% 11.53/1.99  --soft_lemma_size                       3
% 11.53/1.99  --prop_impl_unit_size                   0
% 11.53/1.99  --prop_impl_unit                        []
% 11.53/1.99  --share_sel_clauses                     true
% 11.53/1.99  --reset_solvers                         false
% 11.53/1.99  --bc_imp_inh                            [conj_cone]
% 11.53/1.99  --conj_cone_tolerance                   3.
% 11.53/1.99  --extra_neg_conj                        none
% 11.53/1.99  --large_theory_mode                     true
% 11.53/1.99  --prolific_symb_bound                   200
% 11.53/1.99  --lt_threshold                          2000
% 11.53/1.99  --clause_weak_htbl                      true
% 11.53/1.99  --gc_record_bc_elim                     false
% 11.53/1.99  
% 11.53/1.99  ------ Preprocessing Options
% 11.53/1.99  
% 11.53/1.99  --preprocessing_flag                    true
% 11.53/1.99  --time_out_prep_mult                    0.1
% 11.53/1.99  --splitting_mode                        input
% 11.53/1.99  --splitting_grd                         true
% 11.53/1.99  --splitting_cvd                         false
% 11.53/1.99  --splitting_cvd_svl                     false
% 11.53/1.99  --splitting_nvd                         32
% 11.53/1.99  --sub_typing                            true
% 11.53/1.99  --prep_gs_sim                           true
% 11.53/1.99  --prep_unflatten                        true
% 11.53/1.99  --prep_res_sim                          true
% 11.53/1.99  --prep_upred                            true
% 11.53/1.99  --prep_sem_filter                       exhaustive
% 11.53/1.99  --prep_sem_filter_out                   false
% 11.53/1.99  --pred_elim                             true
% 11.53/1.99  --res_sim_input                         true
% 11.53/1.99  --eq_ax_congr_red                       true
% 11.53/1.99  --pure_diseq_elim                       true
% 11.53/1.99  --brand_transform                       false
% 11.53/1.99  --non_eq_to_eq                          false
% 11.53/1.99  --prep_def_merge                        true
% 11.53/1.99  --prep_def_merge_prop_impl              false
% 11.53/1.99  --prep_def_merge_mbd                    true
% 11.53/1.99  --prep_def_merge_tr_red                 false
% 11.53/1.99  --prep_def_merge_tr_cl                  false
% 11.53/1.99  --smt_preprocessing                     true
% 11.53/1.99  --smt_ac_axioms                         fast
% 11.53/1.99  --preprocessed_out                      false
% 11.53/1.99  --preprocessed_stats                    false
% 11.53/1.99  
% 11.53/1.99  ------ Abstraction refinement Options
% 11.53/1.99  
% 11.53/1.99  --abstr_ref                             []
% 11.53/1.99  --abstr_ref_prep                        false
% 11.53/1.99  --abstr_ref_until_sat                   false
% 11.53/1.99  --abstr_ref_sig_restrict                funpre
% 11.53/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.53/1.99  --abstr_ref_under                       []
% 11.53/1.99  
% 11.53/1.99  ------ SAT Options
% 11.53/1.99  
% 11.53/1.99  --sat_mode                              false
% 11.53/1.99  --sat_fm_restart_options                ""
% 11.53/1.99  --sat_gr_def                            false
% 11.53/1.99  --sat_epr_types                         true
% 11.53/1.99  --sat_non_cyclic_types                  false
% 11.53/1.99  --sat_finite_models                     false
% 11.53/1.99  --sat_fm_lemmas                         false
% 11.53/1.99  --sat_fm_prep                           false
% 11.53/1.99  --sat_fm_uc_incr                        true
% 11.53/1.99  --sat_out_model                         small
% 11.53/1.99  --sat_out_clauses                       false
% 11.53/1.99  
% 11.53/1.99  ------ QBF Options
% 11.53/1.99  
% 11.53/1.99  --qbf_mode                              false
% 11.53/1.99  --qbf_elim_univ                         false
% 11.53/1.99  --qbf_dom_inst                          none
% 11.53/1.99  --qbf_dom_pre_inst                      false
% 11.53/1.99  --qbf_sk_in                             false
% 11.53/1.99  --qbf_pred_elim                         true
% 11.53/1.99  --qbf_split                             512
% 11.53/1.99  
% 11.53/1.99  ------ BMC1 Options
% 11.53/1.99  
% 11.53/1.99  --bmc1_incremental                      false
% 11.53/1.99  --bmc1_axioms                           reachable_all
% 11.53/1.99  --bmc1_min_bound                        0
% 11.53/1.99  --bmc1_max_bound                        -1
% 11.53/1.99  --bmc1_max_bound_default                -1
% 11.53/1.99  --bmc1_symbol_reachability              true
% 11.53/1.99  --bmc1_property_lemmas                  false
% 11.53/1.99  --bmc1_k_induction                      false
% 11.53/1.99  --bmc1_non_equiv_states                 false
% 11.53/1.99  --bmc1_deadlock                         false
% 11.53/1.99  --bmc1_ucm                              false
% 11.53/1.99  --bmc1_add_unsat_core                   none
% 11.53/1.99  --bmc1_unsat_core_children              false
% 11.53/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.53/1.99  --bmc1_out_stat                         full
% 11.53/1.99  --bmc1_ground_init                      false
% 11.53/1.99  --bmc1_pre_inst_next_state              false
% 11.53/1.99  --bmc1_pre_inst_state                   false
% 11.53/1.99  --bmc1_pre_inst_reach_state             false
% 11.53/1.99  --bmc1_out_unsat_core                   false
% 11.53/1.99  --bmc1_aig_witness_out                  false
% 11.53/1.99  --bmc1_verbose                          false
% 11.53/1.99  --bmc1_dump_clauses_tptp                false
% 11.53/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.53/1.99  --bmc1_dump_file                        -
% 11.53/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.53/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.53/1.99  --bmc1_ucm_extend_mode                  1
% 11.53/1.99  --bmc1_ucm_init_mode                    2
% 11.53/1.99  --bmc1_ucm_cone_mode                    none
% 11.53/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.53/1.99  --bmc1_ucm_relax_model                  4
% 11.53/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.53/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.53/1.99  --bmc1_ucm_layered_model                none
% 11.53/1.99  --bmc1_ucm_max_lemma_size               10
% 11.53/1.99  
% 11.53/1.99  ------ AIG Options
% 11.53/1.99  
% 11.53/1.99  --aig_mode                              false
% 11.53/1.99  
% 11.53/1.99  ------ Instantiation Options
% 11.53/1.99  
% 11.53/1.99  --instantiation_flag                    true
% 11.53/1.99  --inst_sos_flag                         true
% 11.53/1.99  --inst_sos_phase                        true
% 11.53/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.53/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.53/1.99  --inst_lit_sel_side                     num_symb
% 11.53/1.99  --inst_solver_per_active                1400
% 11.53/1.99  --inst_solver_calls_frac                1.
% 11.53/1.99  --inst_passive_queue_type               priority_queues
% 11.53/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.53/1.99  --inst_passive_queues_freq              [25;2]
% 11.53/1.99  --inst_dismatching                      true
% 11.53/1.99  --inst_eager_unprocessed_to_passive     true
% 11.53/1.99  --inst_prop_sim_given                   true
% 11.53/1.99  --inst_prop_sim_new                     false
% 11.53/1.99  --inst_subs_new                         false
% 11.53/1.99  --inst_eq_res_simp                      false
% 11.53/1.99  --inst_subs_given                       false
% 11.53/1.99  --inst_orphan_elimination               true
% 11.53/1.99  --inst_learning_loop_flag               true
% 11.53/1.99  --inst_learning_start                   3000
% 11.53/1.99  --inst_learning_factor                  2
% 11.53/1.99  --inst_start_prop_sim_after_learn       3
% 11.53/1.99  --inst_sel_renew                        solver
% 11.53/1.99  --inst_lit_activity_flag                true
% 11.53/1.99  --inst_restr_to_given                   false
% 11.53/1.99  --inst_activity_threshold               500
% 11.53/1.99  --inst_out_proof                        true
% 11.53/1.99  
% 11.53/1.99  ------ Resolution Options
% 11.53/1.99  
% 11.53/1.99  --resolution_flag                       true
% 11.53/1.99  --res_lit_sel                           adaptive
% 11.53/1.99  --res_lit_sel_side                      none
% 11.53/1.99  --res_ordering                          kbo
% 11.53/1.99  --res_to_prop_solver                    active
% 11.53/1.99  --res_prop_simpl_new                    false
% 11.53/1.99  --res_prop_simpl_given                  true
% 11.53/1.99  --res_passive_queue_type                priority_queues
% 11.53/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.53/1.99  --res_passive_queues_freq               [15;5]
% 11.53/1.99  --res_forward_subs                      full
% 11.53/1.99  --res_backward_subs                     full
% 11.53/1.99  --res_forward_subs_resolution           true
% 11.53/1.99  --res_backward_subs_resolution          true
% 11.53/1.99  --res_orphan_elimination                true
% 11.53/1.99  --res_time_limit                        2.
% 11.53/1.99  --res_out_proof                         true
% 11.53/1.99  
% 11.53/1.99  ------ Superposition Options
% 11.53/1.99  
% 11.53/1.99  --superposition_flag                    true
% 11.53/1.99  --sup_passive_queue_type                priority_queues
% 11.53/1.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.53/1.99  --sup_passive_queues_freq               [8;1;4]
% 11.53/1.99  --demod_completeness_check              fast
% 11.53/1.99  --demod_use_ground                      true
% 11.53/1.99  --sup_to_prop_solver                    passive
% 11.53/1.99  --sup_prop_simpl_new                    true
% 11.53/1.99  --sup_prop_simpl_given                  true
% 11.53/1.99  --sup_fun_splitting                     true
% 11.53/1.99  --sup_smt_interval                      50000
% 11.53/1.99  
% 11.53/1.99  ------ Superposition Simplification Setup
% 11.53/1.99  
% 11.53/1.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.53/1.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.53/1.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.53/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.53/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 11.53/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.53/1.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.53/1.99  --sup_immed_triv                        [TrivRules]
% 11.53/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.53/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.53/1.99  --sup_immed_bw_main                     []
% 11.53/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.53/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 11.53/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.53/1.99  --sup_input_bw                          []
% 11.53/1.99  
% 11.53/1.99  ------ Combination Options
% 11.53/1.99  
% 11.53/1.99  --comb_res_mult                         3
% 11.53/1.99  --comb_sup_mult                         2
% 11.53/1.99  --comb_inst_mult                        10
% 11.53/1.99  
% 11.53/1.99  ------ Debug Options
% 11.53/1.99  
% 11.53/1.99  --dbg_backtrace                         false
% 11.53/1.99  --dbg_dump_prop_clauses                 false
% 11.53/1.99  --dbg_dump_prop_clauses_file            -
% 11.53/1.99  --dbg_out_stat                          false
% 11.53/1.99  ------ Parsing...
% 11.53/1.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.53/1.99  
% 11.53/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 11.53/1.99  
% 11.53/1.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.53/1.99  
% 11.53/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.53/1.99  ------ Proving...
% 11.53/1.99  ------ Problem Properties 
% 11.53/1.99  
% 11.53/1.99  
% 11.53/1.99  clauses                                 19
% 11.53/1.99  conjectures                             1
% 11.53/1.99  EPR                                     1
% 11.53/1.99  Horn                                    18
% 11.53/1.99  unary                                   9
% 11.53/1.99  binary                                  7
% 11.53/1.99  lits                                    32
% 11.53/1.99  lits eq                                 18
% 11.53/1.99  fd_pure                                 0
% 11.53/1.99  fd_pseudo                               0
% 11.53/1.99  fd_cond                                 0
% 11.53/1.99  fd_pseudo_cond                          0
% 11.53/1.99  AC symbols                              0
% 11.53/1.99  
% 11.53/1.99  ------ Schedule dynamic 5 is on 
% 11.53/1.99  
% 11.53/1.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.53/1.99  
% 11.53/1.99  
% 11.53/1.99  ------ 
% 11.53/1.99  Current options:
% 11.53/1.99  ------ 
% 11.53/1.99  
% 11.53/1.99  ------ Input Options
% 11.53/1.99  
% 11.53/1.99  --out_options                           all
% 11.53/1.99  --tptp_safe_out                         true
% 11.53/1.99  --problem_path                          ""
% 11.53/1.99  --include_path                          ""
% 11.53/1.99  --clausifier                            res/vclausify_rel
% 11.53/1.99  --clausifier_options                    ""
% 11.53/1.99  --stdin                                 false
% 11.53/1.99  --stats_out                             all
% 11.53/1.99  
% 11.53/1.99  ------ General Options
% 11.53/1.99  
% 11.53/1.99  --fof                                   false
% 11.53/1.99  --time_out_real                         305.
% 11.53/1.99  --time_out_virtual                      -1.
% 11.53/1.99  --symbol_type_check                     false
% 11.53/1.99  --clausify_out                          false
% 11.53/1.99  --sig_cnt_out                           false
% 11.53/1.99  --trig_cnt_out                          false
% 11.53/1.99  --trig_cnt_out_tolerance                1.
% 11.53/1.99  --trig_cnt_out_sk_spl                   false
% 11.53/1.99  --abstr_cl_out                          false
% 11.53/1.99  
% 11.53/1.99  ------ Global Options
% 11.53/1.99  
% 11.53/1.99  --schedule                              default
% 11.53/1.99  --add_important_lit                     false
% 11.53/1.99  --prop_solver_per_cl                    1000
% 11.53/1.99  --min_unsat_core                        false
% 11.53/1.99  --soft_assumptions                      false
% 11.53/1.99  --soft_lemma_size                       3
% 11.53/1.99  --prop_impl_unit_size                   0
% 11.53/1.99  --prop_impl_unit                        []
% 11.53/1.99  --share_sel_clauses                     true
% 11.53/1.99  --reset_solvers                         false
% 11.53/1.99  --bc_imp_inh                            [conj_cone]
% 11.53/1.99  --conj_cone_tolerance                   3.
% 11.53/1.99  --extra_neg_conj                        none
% 11.53/1.99  --large_theory_mode                     true
% 11.53/1.99  --prolific_symb_bound                   200
% 11.53/1.99  --lt_threshold                          2000
% 11.53/1.99  --clause_weak_htbl                      true
% 11.53/1.99  --gc_record_bc_elim                     false
% 11.53/1.99  
% 11.53/1.99  ------ Preprocessing Options
% 11.53/1.99  
% 11.53/1.99  --preprocessing_flag                    true
% 11.53/1.99  --time_out_prep_mult                    0.1
% 11.53/1.99  --splitting_mode                        input
% 11.53/1.99  --splitting_grd                         true
% 11.53/1.99  --splitting_cvd                         false
% 11.53/1.99  --splitting_cvd_svl                     false
% 11.53/1.99  --splitting_nvd                         32
% 11.53/1.99  --sub_typing                            true
% 11.53/1.99  --prep_gs_sim                           true
% 11.53/1.99  --prep_unflatten                        true
% 11.53/1.99  --prep_res_sim                          true
% 11.53/1.99  --prep_upred                            true
% 11.53/1.99  --prep_sem_filter                       exhaustive
% 11.53/1.99  --prep_sem_filter_out                   false
% 11.53/1.99  --pred_elim                             true
% 11.53/1.99  --res_sim_input                         true
% 11.53/1.99  --eq_ax_congr_red                       true
% 11.53/1.99  --pure_diseq_elim                       true
% 11.53/1.99  --brand_transform                       false
% 11.53/1.99  --non_eq_to_eq                          false
% 11.53/1.99  --prep_def_merge                        true
% 11.53/1.99  --prep_def_merge_prop_impl              false
% 11.53/1.99  --prep_def_merge_mbd                    true
% 11.53/1.99  --prep_def_merge_tr_red                 false
% 11.53/1.99  --prep_def_merge_tr_cl                  false
% 11.53/1.99  --smt_preprocessing                     true
% 11.53/1.99  --smt_ac_axioms                         fast
% 11.53/1.99  --preprocessed_out                      false
% 11.53/1.99  --preprocessed_stats                    false
% 11.53/1.99  
% 11.53/1.99  ------ Abstraction refinement Options
% 11.53/1.99  
% 11.53/1.99  --abstr_ref                             []
% 11.53/1.99  --abstr_ref_prep                        false
% 11.53/1.99  --abstr_ref_until_sat                   false
% 11.53/1.99  --abstr_ref_sig_restrict                funpre
% 11.53/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.53/1.99  --abstr_ref_under                       []
% 11.53/1.99  
% 11.53/1.99  ------ SAT Options
% 11.53/1.99  
% 11.53/1.99  --sat_mode                              false
% 11.53/1.99  --sat_fm_restart_options                ""
% 11.53/1.99  --sat_gr_def                            false
% 11.53/1.99  --sat_epr_types                         true
% 11.53/1.99  --sat_non_cyclic_types                  false
% 11.53/1.99  --sat_finite_models                     false
% 11.53/1.99  --sat_fm_lemmas                         false
% 11.53/1.99  --sat_fm_prep                           false
% 11.53/1.99  --sat_fm_uc_incr                        true
% 11.53/1.99  --sat_out_model                         small
% 11.53/1.99  --sat_out_clauses                       false
% 11.53/1.99  
% 11.53/1.99  ------ QBF Options
% 11.53/1.99  
% 11.53/1.99  --qbf_mode                              false
% 11.53/1.99  --qbf_elim_univ                         false
% 11.53/1.99  --qbf_dom_inst                          none
% 11.53/1.99  --qbf_dom_pre_inst                      false
% 11.53/1.99  --qbf_sk_in                             false
% 11.53/1.99  --qbf_pred_elim                         true
% 11.53/1.99  --qbf_split                             512
% 11.53/1.99  
% 11.53/1.99  ------ BMC1 Options
% 11.53/1.99  
% 11.53/1.99  --bmc1_incremental                      false
% 11.53/1.99  --bmc1_axioms                           reachable_all
% 11.53/1.99  --bmc1_min_bound                        0
% 11.53/1.99  --bmc1_max_bound                        -1
% 11.53/1.99  --bmc1_max_bound_default                -1
% 11.53/1.99  --bmc1_symbol_reachability              true
% 11.53/1.99  --bmc1_property_lemmas                  false
% 11.53/1.99  --bmc1_k_induction                      false
% 11.53/1.99  --bmc1_non_equiv_states                 false
% 11.53/1.99  --bmc1_deadlock                         false
% 11.53/1.99  --bmc1_ucm                              false
% 11.53/1.99  --bmc1_add_unsat_core                   none
% 11.53/1.99  --bmc1_unsat_core_children              false
% 11.53/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.53/1.99  --bmc1_out_stat                         full
% 11.53/1.99  --bmc1_ground_init                      false
% 11.53/1.99  --bmc1_pre_inst_next_state              false
% 11.53/1.99  --bmc1_pre_inst_state                   false
% 11.53/1.99  --bmc1_pre_inst_reach_state             false
% 11.53/1.99  --bmc1_out_unsat_core                   false
% 11.53/1.99  --bmc1_aig_witness_out                  false
% 11.53/1.99  --bmc1_verbose                          false
% 11.53/1.99  --bmc1_dump_clauses_tptp                false
% 11.53/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.53/1.99  --bmc1_dump_file                        -
% 11.53/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.53/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.53/1.99  --bmc1_ucm_extend_mode                  1
% 11.53/1.99  --bmc1_ucm_init_mode                    2
% 11.53/1.99  --bmc1_ucm_cone_mode                    none
% 11.53/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.53/1.99  --bmc1_ucm_relax_model                  4
% 11.53/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.53/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.53/1.99  --bmc1_ucm_layered_model                none
% 11.53/1.99  --bmc1_ucm_max_lemma_size               10
% 11.53/1.99  
% 11.53/1.99  ------ AIG Options
% 11.53/1.99  
% 11.53/1.99  --aig_mode                              false
% 11.53/1.99  
% 11.53/1.99  ------ Instantiation Options
% 11.53/1.99  
% 11.53/1.99  --instantiation_flag                    true
% 11.53/1.99  --inst_sos_flag                         true
% 11.53/1.99  --inst_sos_phase                        true
% 11.53/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.53/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.53/1.99  --inst_lit_sel_side                     none
% 11.53/1.99  --inst_solver_per_active                1400
% 11.53/1.99  --inst_solver_calls_frac                1.
% 11.53/1.99  --inst_passive_queue_type               priority_queues
% 11.53/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.53/1.99  --inst_passive_queues_freq              [25;2]
% 11.53/1.99  --inst_dismatching                      true
% 11.53/1.99  --inst_eager_unprocessed_to_passive     true
% 11.53/1.99  --inst_prop_sim_given                   true
% 11.53/1.99  --inst_prop_sim_new                     false
% 11.53/1.99  --inst_subs_new                         false
% 11.53/1.99  --inst_eq_res_simp                      false
% 11.53/1.99  --inst_subs_given                       false
% 11.53/1.99  --inst_orphan_elimination               true
% 11.53/1.99  --inst_learning_loop_flag               true
% 11.53/1.99  --inst_learning_start                   3000
% 11.53/1.99  --inst_learning_factor                  2
% 11.53/1.99  --inst_start_prop_sim_after_learn       3
% 11.53/1.99  --inst_sel_renew                        solver
% 11.53/1.99  --inst_lit_activity_flag                true
% 11.53/1.99  --inst_restr_to_given                   false
% 11.53/1.99  --inst_activity_threshold               500
% 11.53/1.99  --inst_out_proof                        true
% 11.53/1.99  
% 11.53/1.99  ------ Resolution Options
% 11.53/1.99  
% 11.53/1.99  --resolution_flag                       false
% 11.53/1.99  --res_lit_sel                           adaptive
% 11.53/1.99  --res_lit_sel_side                      none
% 11.53/1.99  --res_ordering                          kbo
% 11.53/1.99  --res_to_prop_solver                    active
% 11.53/1.99  --res_prop_simpl_new                    false
% 11.53/1.99  --res_prop_simpl_given                  true
% 11.53/1.99  --res_passive_queue_type                priority_queues
% 11.53/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.53/1.99  --res_passive_queues_freq               [15;5]
% 11.53/1.99  --res_forward_subs                      full
% 11.53/1.99  --res_backward_subs                     full
% 11.53/1.99  --res_forward_subs_resolution           true
% 11.53/1.99  --res_backward_subs_resolution          true
% 11.53/1.99  --res_orphan_elimination                true
% 11.53/1.99  --res_time_limit                        2.
% 11.53/1.99  --res_out_proof                         true
% 11.53/1.99  
% 11.53/1.99  ------ Superposition Options
% 11.53/1.99  
% 11.53/1.99  --superposition_flag                    true
% 11.53/1.99  --sup_passive_queue_type                priority_queues
% 11.53/1.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.53/1.99  --sup_passive_queues_freq               [8;1;4]
% 11.53/1.99  --demod_completeness_check              fast
% 11.53/1.99  --demod_use_ground                      true
% 11.53/1.99  --sup_to_prop_solver                    passive
% 11.53/1.99  --sup_prop_simpl_new                    true
% 11.53/1.99  --sup_prop_simpl_given                  true
% 11.53/1.99  --sup_fun_splitting                     true
% 11.53/1.99  --sup_smt_interval                      50000
% 11.53/1.99  
% 11.53/1.99  ------ Superposition Simplification Setup
% 11.53/1.99  
% 11.53/1.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.53/1.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.53/1.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.53/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.53/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 11.53/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.53/1.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.53/1.99  --sup_immed_triv                        [TrivRules]
% 11.53/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.53/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.53/1.99  --sup_immed_bw_main                     []
% 11.53/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.53/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 11.53/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.53/1.99  --sup_input_bw                          []
% 11.53/1.99  
% 11.53/1.99  ------ Combination Options
% 11.53/1.99  
% 11.53/1.99  --comb_res_mult                         3
% 11.53/1.99  --comb_sup_mult                         2
% 11.53/1.99  --comb_inst_mult                        10
% 11.53/1.99  
% 11.53/1.99  ------ Debug Options
% 11.53/1.99  
% 11.53/1.99  --dbg_backtrace                         false
% 11.53/1.99  --dbg_dump_prop_clauses                 false
% 11.53/1.99  --dbg_dump_prop_clauses_file            -
% 11.53/1.99  --dbg_out_stat                          false
% 11.53/1.99  
% 11.53/1.99  
% 11.53/1.99  
% 11.53/1.99  
% 11.53/1.99  ------ Proving...
% 11.53/1.99  
% 11.53/1.99  
% 11.53/1.99  % SZS status Theorem for theBenchmark.p
% 11.53/1.99  
% 11.53/1.99  % SZS output start CNFRefutation for theBenchmark.p
% 11.53/1.99  
% 11.53/1.99  fof(f19,conjecture,(
% 11.53/1.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 11.53/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.53/1.99  
% 11.53/1.99  fof(f20,negated_conjecture,(
% 11.53/1.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 11.53/1.99    inference(negated_conjecture,[],[f19])).
% 11.53/1.99  
% 11.53/1.99  fof(f34,plain,(
% 11.53/1.99    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 11.53/1.99    inference(ennf_transformation,[],[f20])).
% 11.53/1.99  
% 11.53/1.99  fof(f35,plain,(
% 11.53/1.99    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 11.53/1.99    inference(flattening,[],[f34])).
% 11.53/1.99  
% 11.53/1.99  fof(f36,plain,(
% 11.53/1.99    ? [X0] : (? [X1] : (((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 11.53/1.99    inference(nnf_transformation,[],[f35])).
% 11.53/1.99  
% 11.53/1.99  fof(f37,plain,(
% 11.53/1.99    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 11.53/1.99    inference(flattening,[],[f36])).
% 11.53/1.99  
% 11.53/1.99  fof(f39,plain,(
% 11.53/1.99    ( ! [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) != k2_tops_1(X0,sK1) | ~v4_pre_topc(sK1,X0)) & (k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) = k2_tops_1(X0,sK1) | v4_pre_topc(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 11.53/1.99    introduced(choice_axiom,[])).
% 11.53/1.99  
% 11.53/1.99  fof(f38,plain,(
% 11.53/1.99    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) != k2_tops_1(sK0,X1) | ~v4_pre_topc(X1,sK0)) & (k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) = k2_tops_1(sK0,X1) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 11.53/1.99    introduced(choice_axiom,[])).
% 11.53/1.99  
% 11.53/1.99  fof(f40,plain,(
% 11.53/1.99    ((k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)) & (k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 11.53/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f37,f39,f38])).
% 11.53/1.99  
% 11.53/1.99  fof(f63,plain,(
% 11.53/1.99    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)),
% 11.53/1.99    inference(cnf_transformation,[],[f40])).
% 11.53/1.99  
% 11.53/1.99  fof(f14,axiom,(
% 11.53/1.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 11.53/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.53/1.99  
% 11.53/1.99  fof(f26,plain,(
% 11.53/1.99    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.53/1.99    inference(ennf_transformation,[],[f14])).
% 11.53/1.99  
% 11.53/1.99  fof(f27,plain,(
% 11.53/1.99    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.53/1.99    inference(flattening,[],[f26])).
% 11.53/1.99  
% 11.53/1.99  fof(f54,plain,(
% 11.53/1.99    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.53/1.99    inference(cnf_transformation,[],[f27])).
% 11.53/1.99  
% 11.53/1.99  fof(f61,plain,(
% 11.53/1.99    l1_pre_topc(sK0)),
% 11.53/1.99    inference(cnf_transformation,[],[f40])).
% 11.53/1.99  
% 11.53/1.99  fof(f62,plain,(
% 11.53/1.99    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 11.53/1.99    inference(cnf_transformation,[],[f40])).
% 11.53/1.99  
% 11.53/1.99  fof(f12,axiom,(
% 11.53/1.99    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 11.53/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.53/1.99  
% 11.53/1.99  fof(f25,plain,(
% 11.53/1.99    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.53/1.99    inference(ennf_transformation,[],[f12])).
% 11.53/1.99  
% 11.53/1.99  fof(f52,plain,(
% 11.53/1.99    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.53/1.99    inference(cnf_transformation,[],[f25])).
% 11.53/1.99  
% 11.53/1.99  fof(f6,axiom,(
% 11.53/1.99    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 11.53/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.53/1.99  
% 11.53/1.99  fof(f46,plain,(
% 11.53/1.99    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 11.53/1.99    inference(cnf_transformation,[],[f6])).
% 11.53/1.99  
% 11.53/1.99  fof(f4,axiom,(
% 11.53/1.99    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 11.53/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.53/1.99  
% 11.53/1.99  fof(f22,plain,(
% 11.53/1.99    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 11.53/1.99    inference(ennf_transformation,[],[f4])).
% 11.53/1.99  
% 11.53/1.99  fof(f44,plain,(
% 11.53/1.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 11.53/1.99    inference(cnf_transformation,[],[f22])).
% 11.53/1.99  
% 11.53/1.99  fof(f8,axiom,(
% 11.53/1.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 11.53/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.53/1.99  
% 11.53/1.99  fof(f48,plain,(
% 11.53/1.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 11.53/1.99    inference(cnf_transformation,[],[f8])).
% 11.53/1.99  
% 11.53/1.99  fof(f68,plain,(
% 11.53/1.99    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 11.53/1.99    inference(definition_unfolding,[],[f44,f48])).
% 11.53/1.99  
% 11.53/1.99  fof(f13,axiom,(
% 11.53/1.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 11.53/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.53/1.99  
% 11.53/1.99  fof(f53,plain,(
% 11.53/1.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 11.53/1.99    inference(cnf_transformation,[],[f13])).
% 11.53/1.99  
% 11.53/1.99  fof(f70,plain,(
% 11.53/1.99    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 11.53/1.99    inference(definition_unfolding,[],[f53,f48])).
% 11.53/1.99  
% 11.53/1.99  fof(f2,axiom,(
% 11.53/1.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 11.53/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.53/1.99  
% 11.53/1.99  fof(f42,plain,(
% 11.53/1.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 11.53/1.99    inference(cnf_transformation,[],[f2])).
% 11.53/1.99  
% 11.53/1.99  fof(f65,plain,(
% 11.53/1.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 11.53/1.99    inference(definition_unfolding,[],[f42,f48])).
% 11.53/1.99  
% 11.53/1.99  fof(f1,axiom,(
% 11.53/1.99    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 11.53/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.53/1.99  
% 11.53/1.99  fof(f21,plain,(
% 11.53/1.99    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 11.53/1.99    inference(rectify,[],[f1])).
% 11.53/1.99  
% 11.53/1.99  fof(f41,plain,(
% 11.53/1.99    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 11.53/1.99    inference(cnf_transformation,[],[f21])).
% 11.53/1.99  
% 11.53/1.99  fof(f66,plain,(
% 11.53/1.99    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 11.53/1.99    inference(definition_unfolding,[],[f41,f48])).
% 11.53/1.99  
% 11.53/1.99  fof(f5,axiom,(
% 11.53/1.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 11.53/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.53/1.99  
% 11.53/1.99  fof(f45,plain,(
% 11.53/1.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 11.53/1.99    inference(cnf_transformation,[],[f5])).
% 11.53/1.99  
% 11.53/1.99  fof(f10,axiom,(
% 11.53/1.99    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 11.53/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.53/1.99  
% 11.53/1.99  fof(f50,plain,(
% 11.53/1.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 11.53/1.99    inference(cnf_transformation,[],[f10])).
% 11.53/1.99  
% 11.53/1.99  fof(f7,axiom,(
% 11.53/1.99    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 11.53/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.53/1.99  
% 11.53/1.99  fof(f47,plain,(
% 11.53/1.99    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 11.53/1.99    inference(cnf_transformation,[],[f7])).
% 11.53/1.99  
% 11.53/1.99  fof(f15,axiom,(
% 11.53/1.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 11.53/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.53/1.99  
% 11.53/1.99  fof(f28,plain,(
% 11.53/1.99    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 11.53/1.99    inference(ennf_transformation,[],[f15])).
% 11.53/1.99  
% 11.53/1.99  fof(f29,plain,(
% 11.53/1.99    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 11.53/1.99    inference(flattening,[],[f28])).
% 11.53/1.99  
% 11.53/1.99  fof(f56,plain,(
% 11.53/1.99    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.53/1.99    inference(cnf_transformation,[],[f29])).
% 11.53/1.99  
% 11.53/1.99  fof(f11,axiom,(
% 11.53/1.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 11.53/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.53/1.99  
% 11.53/1.99  fof(f23,plain,(
% 11.53/1.99    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 11.53/1.99    inference(ennf_transformation,[],[f11])).
% 11.53/1.99  
% 11.53/1.99  fof(f24,plain,(
% 11.53/1.99    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.53/1.99    inference(flattening,[],[f23])).
% 11.53/1.99  
% 11.53/1.99  fof(f51,plain,(
% 11.53/1.99    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.53/1.99    inference(cnf_transformation,[],[f24])).
% 11.53/1.99  
% 11.53/1.99  fof(f9,axiom,(
% 11.53/1.99    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 11.53/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.53/1.99  
% 11.53/1.99  fof(f49,plain,(
% 11.53/1.99    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 11.53/1.99    inference(cnf_transformation,[],[f9])).
% 11.53/1.99  
% 11.53/1.99  fof(f69,plain,(
% 11.53/1.99    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k4_xboole_0(X2,X1)) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.53/1.99    inference(definition_unfolding,[],[f51,f49])).
% 11.53/1.99  
% 11.53/1.99  fof(f18,axiom,(
% 11.53/1.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)))),
% 11.53/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.53/1.99  
% 11.53/1.99  fof(f33,plain,(
% 11.53/1.99    ! [X0] : (! [X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.53/1.99    inference(ennf_transformation,[],[f18])).
% 11.53/1.99  
% 11.53/1.99  fof(f59,plain,(
% 11.53/1.99    ( ! [X0,X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.53/1.99    inference(cnf_transformation,[],[f33])).
% 11.53/1.99  
% 11.53/1.99  fof(f3,axiom,(
% 11.53/1.99    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 11.53/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.53/1.99  
% 11.53/1.99  fof(f43,plain,(
% 11.53/1.99    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 11.53/1.99    inference(cnf_transformation,[],[f3])).
% 11.53/1.99  
% 11.53/1.99  fof(f67,plain,(
% 11.53/1.99    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0) )),
% 11.53/1.99    inference(definition_unfolding,[],[f43,f49])).
% 11.53/1.99  
% 11.53/1.99  fof(f17,axiom,(
% 11.53/1.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)))),
% 11.53/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.53/1.99  
% 11.53/1.99  fof(f32,plain,(
% 11.53/1.99    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.53/1.99    inference(ennf_transformation,[],[f17])).
% 11.53/1.99  
% 11.53/1.99  fof(f58,plain,(
% 11.53/1.99    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.53/1.99    inference(cnf_transformation,[],[f32])).
% 11.53/1.99  
% 11.53/1.99  fof(f64,plain,(
% 11.53/1.99    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)),
% 11.53/1.99    inference(cnf_transformation,[],[f40])).
% 11.53/1.99  
% 11.53/1.99  fof(f55,plain,(
% 11.53/1.99    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.53/1.99    inference(cnf_transformation,[],[f27])).
% 11.53/1.99  
% 11.53/1.99  fof(f60,plain,(
% 11.53/1.99    v2_pre_topc(sK0)),
% 11.53/1.99    inference(cnf_transformation,[],[f40])).
% 11.53/1.99  
% 11.53/1.99  cnf(c_18,negated_conjecture,
% 11.53/1.99      ( v4_pre_topc(sK1,sK0)
% 11.53/1.99      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 11.53/1.99      inference(cnf_transformation,[],[f63]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_136,plain,
% 11.53/1.99      ( v4_pre_topc(sK1,sK0)
% 11.53/1.99      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 11.53/1.99      inference(prop_impl,[status(thm)],[c_18]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_12,plain,
% 11.53/1.99      ( ~ v4_pre_topc(X0,X1)
% 11.53/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.53/1.99      | ~ l1_pre_topc(X1)
% 11.53/1.99      | k2_pre_topc(X1,X0) = X0 ),
% 11.53/1.99      inference(cnf_transformation,[],[f54]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_20,negated_conjecture,
% 11.53/1.99      ( l1_pre_topc(sK0) ),
% 11.53/1.99      inference(cnf_transformation,[],[f61]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_336,plain,
% 11.53/1.99      ( ~ v4_pre_topc(X0,X1)
% 11.53/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.53/1.99      | k2_pre_topc(X1,X0) = X0
% 11.53/1.99      | sK0 != X1 ),
% 11.53/1.99      inference(resolution_lifted,[status(thm)],[c_12,c_20]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_337,plain,
% 11.53/1.99      ( ~ v4_pre_topc(X0,sK0)
% 11.53/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.53/1.99      | k2_pre_topc(sK0,X0) = X0 ),
% 11.53/1.99      inference(unflattening,[status(thm)],[c_336]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_383,plain,
% 11.53/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.53/1.99      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 11.53/1.99      | k2_pre_topc(sK0,X0) = X0
% 11.53/1.99      | sK1 != X0
% 11.53/1.99      | sK0 != sK0 ),
% 11.53/1.99      inference(resolution_lifted,[status(thm)],[c_136,c_337]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_384,plain,
% 11.53/1.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.53/1.99      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 11.53/1.99      | k2_pre_topc(sK0,sK1) = sK1 ),
% 11.53/1.99      inference(unflattening,[status(thm)],[c_383]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_19,negated_conjecture,
% 11.53/1.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 11.53/1.99      inference(cnf_transformation,[],[f62]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_386,plain,
% 11.53/1.99      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 11.53/1.99      | k2_pre_topc(sK0,sK1) = sK1 ),
% 11.53/1.99      inference(global_propositional_subsumption,
% 11.53/1.99                [status(thm)],
% 11.53/1.99                [c_384,c_19]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_476,plain,
% 11.53/1.99      ( k2_pre_topc(sK0,sK1) = sK1
% 11.53/1.99      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 11.53/1.99      inference(prop_impl,[status(thm)],[c_386]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_477,plain,
% 11.53/1.99      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 11.53/1.99      | k2_pre_topc(sK0,sK1) = sK1 ),
% 11.53/1.99      inference(renaming,[status(thm)],[c_476]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_893,plain,
% 11.53/1.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 11.53/1.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_9,plain,
% 11.53/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.53/1.99      | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 11.53/1.99      inference(cnf_transformation,[],[f52]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_894,plain,
% 11.53/1.99      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
% 11.53/1.99      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 11.53/1.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_4727,plain,
% 11.53/1.99      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
% 11.53/1.99      inference(superposition,[status(thm)],[c_893,c_894]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_4795,plain,
% 11.53/1.99      ( k2_pre_topc(sK0,sK1) = sK1
% 11.53/1.99      | k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 11.53/1.99      inference(superposition,[status(thm)],[c_477,c_4727]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_5,plain,
% 11.53/1.99      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 11.53/1.99      inference(cnf_transformation,[],[f46]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_896,plain,
% 11.53/1.99      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 11.53/1.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_7717,plain,
% 11.53/1.99      ( k2_pre_topc(sK0,sK1) = sK1
% 11.53/1.99      | r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top ),
% 11.53/1.99      inference(superposition,[status(thm)],[c_4795,c_896]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_3,plain,
% 11.53/1.99      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 11.53/1.99      inference(cnf_transformation,[],[f68]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_898,plain,
% 11.53/1.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
% 11.53/1.99      | r1_tarski(X0,X1) != iProver_top ),
% 11.53/1.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_10,plain,
% 11.53/1.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
% 11.53/1.99      inference(cnf_transformation,[],[f70]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_900,plain,
% 11.53/1.99      ( k1_setfam_1(k2_tarski(X0,X1)) = X0
% 11.53/1.99      | r1_tarski(X0,X1) != iProver_top ),
% 11.53/1.99      inference(demodulation,[status(thm)],[c_898,c_10]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_8197,plain,
% 11.53/1.99      ( k2_pre_topc(sK0,sK1) = sK1
% 11.53/1.99      | k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),sK1)) = k2_tops_1(sK0,sK1) ),
% 11.53/1.99      inference(superposition,[status(thm)],[c_7717,c_900]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_0,plain,
% 11.53/1.99      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 11.53/1.99      inference(cnf_transformation,[],[f65]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_899,plain,
% 11.53/1.99      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k4_xboole_0(X0,X1) ),
% 11.53/1.99      inference(light_normalisation,[status(thm)],[c_0,c_10]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_12647,plain,
% 11.53/1.99      ( k2_pre_topc(sK0,sK1) = sK1
% 11.53/1.99      | k5_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) = k4_xboole_0(k2_tops_1(sK0,sK1),sK1) ),
% 11.53/1.99      inference(superposition,[status(thm)],[c_8197,c_899]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_1,plain,
% 11.53/1.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
% 11.53/1.99      inference(cnf_transformation,[],[f66]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_1833,plain,
% 11.53/1.99      ( k1_setfam_1(k2_tarski(X0,X0)) = X0 ),
% 11.53/1.99      inference(superposition,[status(thm)],[c_10,c_1]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_3452,plain,
% 11.53/1.99      ( k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0) ),
% 11.53/1.99      inference(superposition,[status(thm)],[c_1833,c_899]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_4,plain,
% 11.53/1.99      ( r1_tarski(k1_xboole_0,X0) ),
% 11.53/1.99      inference(cnf_transformation,[],[f45]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_897,plain,
% 11.53/1.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 11.53/1.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_4607,plain,
% 11.53/1.99      ( k1_setfam_1(k2_tarski(k1_xboole_0,X0)) = k1_xboole_0 ),
% 11.53/1.99      inference(superposition,[status(thm)],[c_897,c_900]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_7,plain,
% 11.53/1.99      ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
% 11.53/1.99      inference(cnf_transformation,[],[f50]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_6,plain,
% 11.53/1.99      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 11.53/1.99      inference(cnf_transformation,[],[f47]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_1831,plain,
% 11.53/1.99      ( k1_setfam_1(k2_tarski(X0,k1_xboole_0)) = k4_xboole_0(X0,X0) ),
% 11.53/1.99      inference(superposition,[status(thm)],[c_6,c_10]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_2404,plain,
% 11.53/1.99      ( k1_setfam_1(k2_tarski(k1_xboole_0,X0)) = k4_xboole_0(X0,X0) ),
% 11.53/1.99      inference(superposition,[status(thm)],[c_7,c_1831]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_5755,plain,
% 11.53/1.99      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 11.53/1.99      inference(demodulation,[status(thm)],[c_4607,c_2404]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_6051,plain,
% 11.53/1.99      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 11.53/1.99      inference(light_normalisation,[status(thm)],[c_3452,c_3452,c_5755]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_12657,plain,
% 11.53/1.99      ( k2_pre_topc(sK0,sK1) = sK1
% 11.53/1.99      | k4_xboole_0(k2_tops_1(sK0,sK1),sK1) = k1_xboole_0 ),
% 11.53/1.99      inference(demodulation,[status(thm)],[c_12647,c_6051]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_13,plain,
% 11.53/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.53/1.99      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 11.53/1.99      | ~ l1_pre_topc(X1) ),
% 11.53/1.99      inference(cnf_transformation,[],[f56]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_324,plain,
% 11.53/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.53/1.99      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 11.53/1.99      | sK0 != X1 ),
% 11.53/1.99      inference(resolution_lifted,[status(thm)],[c_13,c_20]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_325,plain,
% 11.53/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.53/1.99      | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 11.53/1.99      inference(unflattening,[status(thm)],[c_324]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_890,plain,
% 11.53/1.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.53/1.99      | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 11.53/1.99      inference(predicate_to_equality,[status(thm)],[c_325]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_8,plain,
% 11.53/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.53/1.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 11.53/1.99      | k5_xboole_0(X2,k4_xboole_0(X0,X2)) = k4_subset_1(X1,X2,X0) ),
% 11.53/1.99      inference(cnf_transformation,[],[f69]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_895,plain,
% 11.53/1.99      ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k4_subset_1(X2,X0,X1)
% 11.53/1.99      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
% 11.53/1.99      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
% 11.53/1.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_2782,plain,
% 11.53/1.99      ( k5_xboole_0(X0,k4_xboole_0(k2_tops_1(sK0,X1),X0)) = k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X1))
% 11.53/1.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.53/1.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 11.53/1.99      inference(superposition,[status(thm)],[c_890,c_895]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_3346,plain,
% 11.53/1.99      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k5_xboole_0(sK1,k4_xboole_0(k2_tops_1(sK0,X0),sK1))
% 11.53/1.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 11.53/1.99      inference(superposition,[status(thm)],[c_893,c_2782]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_3873,plain,
% 11.53/1.99      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k4_xboole_0(k2_tops_1(sK0,sK1),sK1)) ),
% 11.53/1.99      inference(superposition,[status(thm)],[c_893,c_3346]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_16,plain,
% 11.53/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.53/1.99      | ~ l1_pre_topc(X1)
% 11.53/1.99      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
% 11.53/1.99      inference(cnf_transformation,[],[f59]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_300,plain,
% 11.53/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.53/1.99      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0)
% 11.53/1.99      | sK0 != X1 ),
% 11.53/1.99      inference(resolution_lifted,[status(thm)],[c_16,c_20]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_301,plain,
% 11.53/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.53/1.99      | k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0) ),
% 11.53/1.99      inference(unflattening,[status(thm)],[c_300]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_892,plain,
% 11.53/1.99      ( k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0)
% 11.53/1.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 11.53/1.99      inference(predicate_to_equality,[status(thm)],[c_301]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_994,plain,
% 11.53/1.99      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 11.53/1.99      inference(superposition,[status(thm)],[c_893,c_892]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_3875,plain,
% 11.53/1.99      ( k5_xboole_0(sK1,k4_xboole_0(k2_tops_1(sK0,sK1),sK1)) = k2_pre_topc(sK0,sK1) ),
% 11.53/1.99      inference(light_normalisation,[status(thm)],[c_3873,c_994]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_33456,plain,
% 11.53/1.99      ( k2_pre_topc(sK0,sK1) = k5_xboole_0(sK1,k1_xboole_0)
% 11.53/1.99      | k2_pre_topc(sK0,sK1) = sK1 ),
% 11.53/1.99      inference(superposition,[status(thm)],[c_12657,c_3875]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_1832,plain,
% 11.53/1.99      ( k1_setfam_1(k2_tarski(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
% 11.53/1.99      inference(superposition,[status(thm)],[c_10,c_10]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_4623,plain,
% 11.53/1.99      ( k1_setfam_1(k2_tarski(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0))) ),
% 11.53/1.99      inference(superposition,[status(thm)],[c_7,c_1832]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_2,plain,
% 11.53/1.99      ( k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
% 11.53/1.99      inference(cnf_transformation,[],[f67]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_1834,plain,
% 11.53/1.99      ( k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),k1_setfam_1(k2_tarski(k1_xboole_0,X0))) = k4_xboole_0(k1_xboole_0,X0) ),
% 11.53/1.99      inference(superposition,[status(thm)],[c_10,c_2]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_4266,plain,
% 11.53/1.99      ( k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = k4_xboole_0(k1_xboole_0,X0) ),
% 11.53/1.99      inference(superposition,[status(thm)],[c_7,c_1834]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_4710,plain,
% 11.53/1.99      ( k5_xboole_0(k1_setfam_1(k2_tarski(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))),k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0,k1_xboole_0)),k1_xboole_0))) = k4_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) ),
% 11.53/1.99      inference(superposition,[status(thm)],[c_4623,c_4266]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_4718,plain,
% 11.53/1.99      ( k5_xboole_0(k1_setfam_1(k2_tarski(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))),k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0,k1_xboole_0)),k1_xboole_0))) = k1_setfam_1(k2_tarski(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) ),
% 11.53/1.99      inference(demodulation,[status(thm)],[c_4710,c_4623]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_3455,plain,
% 11.53/1.99      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0))) = k4_xboole_0(X0,X1) ),
% 11.53/1.99      inference(superposition,[status(thm)],[c_7,c_899]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_2330,plain,
% 11.53/1.99      ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) = iProver_top ),
% 11.53/1.99      inference(superposition,[status(thm)],[c_10,c_896]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_2499,plain,
% 11.53/1.99      ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X1) = iProver_top ),
% 11.53/1.99      inference(superposition,[status(thm)],[c_7,c_2330]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_4611,plain,
% 11.53/1.99      ( k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
% 11.53/1.99      inference(superposition,[status(thm)],[c_2499,c_900]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_4719,plain,
% 11.53/1.99      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 11.53/1.99      inference(demodulation,[status(thm)],[c_4718,c_3455,c_4607,c_4611]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_5657,plain,
% 11.53/1.99      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 11.53/1.99      inference(demodulation,[status(thm)],[c_4719,c_2]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_33457,plain,
% 11.53/1.99      ( k2_pre_topc(sK0,sK1) = sK1 ),
% 11.53/1.99      inference(demodulation,[status(thm)],[c_33456,c_5657]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_15,plain,
% 11.53/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.53/1.99      | ~ l1_pre_topc(X1)
% 11.53/1.99      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
% 11.53/1.99      inference(cnf_transformation,[],[f58]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_312,plain,
% 11.53/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.53/1.99      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0)
% 11.53/1.99      | sK0 != X1 ),
% 11.53/1.99      inference(resolution_lifted,[status(thm)],[c_15,c_20]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_313,plain,
% 11.53/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.53/1.99      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
% 11.53/1.99      inference(unflattening,[status(thm)],[c_312]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_891,plain,
% 11.53/1.99      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0)
% 11.53/1.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 11.53/1.99      inference(predicate_to_equality,[status(thm)],[c_313]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_1047,plain,
% 11.53/1.99      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 11.53/1.99      inference(superposition,[status(thm)],[c_893,c_891]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_33579,plain,
% 11.53/1.99      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 11.53/1.99      inference(demodulation,[status(thm)],[c_33457,c_1047]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_17,negated_conjecture,
% 11.53/1.99      ( ~ v4_pre_topc(sK1,sK0)
% 11.53/1.99      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
% 11.53/1.99      inference(cnf_transformation,[],[f64]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_134,plain,
% 11.53/1.99      ( ~ v4_pre_topc(sK1,sK0)
% 11.53/1.99      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
% 11.53/1.99      inference(prop_impl,[status(thm)],[c_17]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_11,plain,
% 11.53/1.99      ( v4_pre_topc(X0,X1)
% 11.53/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.53/1.99      | ~ l1_pre_topc(X1)
% 11.53/1.99      | ~ v2_pre_topc(X1)
% 11.53/1.99      | k2_pre_topc(X1,X0) != X0 ),
% 11.53/1.99      inference(cnf_transformation,[],[f55]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_21,negated_conjecture,
% 11.53/1.99      ( v2_pre_topc(sK0) ),
% 11.53/1.99      inference(cnf_transformation,[],[f60]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_272,plain,
% 11.53/1.99      ( v4_pre_topc(X0,X1)
% 11.53/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.53/1.99      | ~ l1_pre_topc(X1)
% 11.53/1.99      | k2_pre_topc(X1,X0) != X0
% 11.53/1.99      | sK0 != X1 ),
% 11.53/1.99      inference(resolution_lifted,[status(thm)],[c_11,c_21]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_273,plain,
% 11.53/1.99      ( v4_pre_topc(X0,sK0)
% 11.53/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.53/1.99      | ~ l1_pre_topc(sK0)
% 11.53/1.99      | k2_pre_topc(sK0,X0) != X0 ),
% 11.53/1.99      inference(unflattening,[status(thm)],[c_272]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_277,plain,
% 11.53/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.53/1.99      | v4_pre_topc(X0,sK0)
% 11.53/1.99      | k2_pre_topc(sK0,X0) != X0 ),
% 11.53/1.99      inference(global_propositional_subsumption,
% 11.53/1.99                [status(thm)],
% 11.53/1.99                [c_273,c_20]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_278,plain,
% 11.53/1.99      ( v4_pre_topc(X0,sK0)
% 11.53/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.53/1.99      | k2_pre_topc(sK0,X0) != X0 ),
% 11.53/1.99      inference(renaming,[status(thm)],[c_277]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_394,plain,
% 11.53/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.53/1.99      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
% 11.53/1.99      | k2_pre_topc(sK0,X0) != X0
% 11.53/1.99      | sK1 != X0
% 11.53/1.99      | sK0 != sK0 ),
% 11.53/1.99      inference(resolution_lifted,[status(thm)],[c_134,c_278]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_395,plain,
% 11.53/1.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.53/1.99      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
% 11.53/1.99      | k2_pre_topc(sK0,sK1) != sK1 ),
% 11.53/1.99      inference(unflattening,[status(thm)],[c_394]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(c_397,plain,
% 11.53/1.99      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
% 11.53/1.99      | k2_pre_topc(sK0,sK1) != sK1 ),
% 11.53/1.99      inference(global_propositional_subsumption,
% 11.53/1.99                [status(thm)],
% 11.53/1.99                [c_395,c_19]) ).
% 11.53/1.99  
% 11.53/1.99  cnf(contradiction,plain,
% 11.53/1.99      ( $false ),
% 11.53/1.99      inference(minisat,[status(thm)],[c_33579,c_33457,c_397]) ).
% 11.53/1.99  
% 11.53/1.99  
% 11.53/1.99  % SZS output end CNFRefutation for theBenchmark.p
% 11.53/1.99  
% 11.53/1.99  ------                               Statistics
% 11.53/1.99  
% 11.53/1.99  ------ General
% 11.53/1.99  
% 11.53/1.99  abstr_ref_over_cycles:                  0
% 11.53/1.99  abstr_ref_under_cycles:                 0
% 11.53/1.99  gc_basic_clause_elim:                   0
% 11.53/1.99  forced_gc_time:                         0
% 11.53/1.99  parsing_time:                           0.011
% 11.53/1.99  unif_index_cands_time:                  0.
% 11.53/1.99  unif_index_add_time:                    0.
% 11.53/1.99  orderings_time:                         0.
% 11.53/1.99  out_proof_time:                         0.011
% 11.53/1.99  total_time:                             1.28
% 11.53/1.99  num_of_symbols:                         50
% 11.53/1.99  num_of_terms:                           30147
% 11.53/1.99  
% 11.53/1.99  ------ Preprocessing
% 11.53/1.99  
% 11.53/1.99  num_of_splits:                          0
% 11.53/1.99  num_of_split_atoms:                     0
% 11.53/1.99  num_of_reused_defs:                     0
% 11.53/1.99  num_eq_ax_congr_red:                    17
% 11.53/1.99  num_of_sem_filtered_clauses:            1
% 11.53/1.99  num_of_subtypes:                        0
% 11.53/1.99  monotx_restored_types:                  0
% 11.53/1.99  sat_num_of_epr_types:                   0
% 11.53/1.99  sat_num_of_non_cyclic_types:            0
% 11.53/1.99  sat_guarded_non_collapsed_types:        0
% 11.53/1.99  num_pure_diseq_elim:                    0
% 11.53/1.99  simp_replaced_by:                       0
% 11.53/1.99  res_preprocessed:                       108
% 11.53/1.99  prep_upred:                             0
% 11.53/1.99  prep_unflattend:                        17
% 11.53/1.99  smt_new_axioms:                         0
% 11.53/1.99  pred_elim_cands:                        2
% 11.53/1.99  pred_elim:                              3
% 11.53/1.99  pred_elim_cl:                           3
% 11.53/1.99  pred_elim_cycles:                       6
% 11.53/1.99  merged_defs:                            8
% 11.53/1.99  merged_defs_ncl:                        0
% 11.53/1.99  bin_hyper_res:                          9
% 11.53/1.99  prep_cycles:                            4
% 11.53/1.99  pred_elim_time:                         0.004
% 11.53/1.99  splitting_time:                         0.
% 11.53/1.99  sem_filter_time:                        0.
% 11.53/1.99  monotx_time:                            0.
% 11.53/1.99  subtype_inf_time:                       0.
% 11.53/1.99  
% 11.53/1.99  ------ Problem properties
% 11.53/1.99  
% 11.53/1.99  clauses:                                19
% 11.53/1.99  conjectures:                            1
% 11.53/1.99  epr:                                    1
% 11.53/1.99  horn:                                   18
% 11.53/1.99  ground:                                 3
% 11.53/1.99  unary:                                  9
% 11.53/1.99  binary:                                 7
% 11.53/1.99  lits:                                   32
% 11.53/1.99  lits_eq:                                18
% 11.53/1.99  fd_pure:                                0
% 11.53/1.99  fd_pseudo:                              0
% 11.53/1.99  fd_cond:                                0
% 11.53/1.99  fd_pseudo_cond:                         0
% 11.53/1.99  ac_symbols:                             0
% 11.53/1.99  
% 11.53/1.99  ------ Propositional Solver
% 11.53/1.99  
% 11.53/1.99  prop_solver_calls:                      35
% 11.53/1.99  prop_fast_solver_calls:                 1196
% 11.53/1.99  smt_solver_calls:                       0
% 11.53/1.99  smt_fast_solver_calls:                  0
% 11.53/1.99  prop_num_of_clauses:                    16158
% 11.53/1.99  prop_preprocess_simplified:             34688
% 11.53/1.99  prop_fo_subsumed:                       4
% 11.53/1.99  prop_solver_time:                       0.
% 11.53/1.99  smt_solver_time:                        0.
% 11.53/1.99  smt_fast_solver_time:                   0.
% 11.53/1.99  prop_fast_solver_time:                  0.
% 11.53/1.99  prop_unsat_core_time:                   0.002
% 11.53/1.99  
% 11.53/1.99  ------ QBF
% 11.53/1.99  
% 11.53/1.99  qbf_q_res:                              0
% 11.53/1.99  qbf_num_tautologies:                    0
% 11.53/1.99  qbf_prep_cycles:                        0
% 11.53/1.99  
% 11.53/1.99  ------ BMC1
% 11.53/1.99  
% 11.53/1.99  bmc1_current_bound:                     -1
% 11.53/1.99  bmc1_last_solved_bound:                 -1
% 11.53/1.99  bmc1_unsat_core_size:                   -1
% 11.53/1.99  bmc1_unsat_core_parents_size:           -1
% 11.53/1.99  bmc1_merge_next_fun:                    0
% 11.53/1.99  bmc1_unsat_core_clauses_time:           0.
% 11.53/1.99  
% 11.53/1.99  ------ Instantiation
% 11.53/1.99  
% 11.53/1.99  inst_num_of_clauses:                    5843
% 11.53/1.99  inst_num_in_passive:                    2989
% 11.53/1.99  inst_num_in_active:                     1891
% 11.53/1.99  inst_num_in_unprocessed:                963
% 11.53/1.99  inst_num_of_loops:                      2150
% 11.53/1.99  inst_num_of_learning_restarts:          0
% 11.53/1.99  inst_num_moves_active_passive:          255
% 11.53/1.99  inst_lit_activity:                      0
% 11.53/1.99  inst_lit_activity_moves:                2
% 11.53/1.99  inst_num_tautologies:                   0
% 11.53/1.99  inst_num_prop_implied:                  0
% 11.53/1.99  inst_num_existing_simplified:           0
% 11.53/1.99  inst_num_eq_res_simplified:             0
% 11.53/1.99  inst_num_child_elim:                    0
% 11.53/1.99  inst_num_of_dismatching_blockings:      3070
% 11.53/1.99  inst_num_of_non_proper_insts:           5510
% 11.53/1.99  inst_num_of_duplicates:                 0
% 11.53/1.99  inst_inst_num_from_inst_to_res:         0
% 11.53/1.99  inst_dismatching_checking_time:         0.
% 11.53/1.99  
% 11.53/1.99  ------ Resolution
% 11.53/1.99  
% 11.53/1.99  res_num_of_clauses:                     0
% 11.53/1.99  res_num_in_passive:                     0
% 11.53/1.99  res_num_in_active:                      0
% 11.53/1.99  res_num_of_loops:                       112
% 11.53/1.99  res_forward_subset_subsumed:            436
% 11.53/1.99  res_backward_subset_subsumed:           0
% 11.53/1.99  res_forward_subsumed:                   0
% 11.53/1.99  res_backward_subsumed:                  0
% 11.53/1.99  res_forward_subsumption_resolution:     0
% 11.53/1.99  res_backward_subsumption_resolution:    0
% 11.53/1.99  res_clause_to_clause_subsumption:       6477
% 11.53/1.99  res_orphan_elimination:                 0
% 11.53/1.99  res_tautology_del:                      541
% 11.53/1.99  res_num_eq_res_simplified:              1
% 11.53/1.99  res_num_sel_changes:                    0
% 11.53/1.99  res_moves_from_active_to_pass:          0
% 11.53/1.99  
% 11.53/1.99  ------ Superposition
% 11.53/1.99  
% 11.53/1.99  sup_time_total:                         0.
% 11.53/1.99  sup_time_generating:                    0.
% 11.53/1.99  sup_time_sim_full:                      0.
% 11.53/1.99  sup_time_sim_immed:                     0.
% 11.53/1.99  
% 11.53/1.99  sup_num_of_clauses:                     389
% 11.53/1.99  sup_num_in_active:                      329
% 11.53/1.99  sup_num_in_passive:                     60
% 11.53/1.99  sup_num_of_loops:                       428
% 11.53/1.99  sup_fw_superposition:                   972
% 11.53/1.99  sup_bw_superposition:                   1059
% 11.53/1.99  sup_immediate_simplified:               595
% 11.53/1.99  sup_given_eliminated:                   0
% 11.53/1.99  comparisons_done:                       0
% 11.53/1.99  comparisons_avoided:                    174
% 11.53/1.99  
% 11.53/1.99  ------ Simplifications
% 11.53/1.99  
% 11.53/1.99  
% 11.53/1.99  sim_fw_subset_subsumed:                 5
% 11.53/1.99  sim_bw_subset_subsumed:                 314
% 11.53/1.99  sim_fw_subsumed:                        122
% 11.53/1.99  sim_bw_subsumed:                        2
% 11.53/1.99  sim_fw_subsumption_res:                 0
% 11.53/1.99  sim_bw_subsumption_res:                 0
% 11.53/1.99  sim_tautology_del:                      1
% 11.53/1.99  sim_eq_tautology_del:                   147
% 11.53/1.99  sim_eq_res_simp:                        1
% 11.53/1.99  sim_fw_demodulated:                     380
% 11.53/1.99  sim_bw_demodulated:                     30
% 11.53/1.99  sim_light_normalised:                   188
% 11.53/1.99  sim_joinable_taut:                      0
% 11.53/1.99  sim_joinable_simp:                      0
% 11.53/1.99  sim_ac_normalised:                      0
% 11.53/1.99  sim_smt_subsumption:                    0
% 11.53/1.99  
%------------------------------------------------------------------------------
