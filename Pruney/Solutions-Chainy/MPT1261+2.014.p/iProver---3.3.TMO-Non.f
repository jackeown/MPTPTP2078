%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:14:27 EST 2020

% Result     : Timeout 59.68s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :  141 ( 908 expanded)
%              Number of clauses        :   76 ( 244 expanded)
%              Number of leaves         :   19 ( 224 expanded)
%              Depth                    :   20
%              Number of atoms          :  327 (3169 expanded)
%              Number of equality atoms :  175 (1224 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f21,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1)
            | ~ v4_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1)
            | ~ v4_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f43,plain,(
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

fof(f42,plain,
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

fof(f44,plain,
    ( ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f41,f43,f42])).

fof(f70,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f44])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f71,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f15,axiom,(
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
    inference(ennf_transformation,[],[f15])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f69,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f14,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f80,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(definition_unfolding,[],[f60,f54])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f73,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f49,f54])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f9,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f78,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(definition_unfolding,[],[f57,f55])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f77,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f53,f55])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f76,plain,(
    ! [X0] : k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(definition_unfolding,[],[f51,f55])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f45,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f23])).

fof(f74,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f45,f54])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f24])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k4_xboole_0(X2,X1)) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f58,f55])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) != X1
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f72,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f68,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_852,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_862,plain,
    ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_5785,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
    inference(superposition,[status(thm)],[c_852,c_862])).

cnf(c_22,negated_conjecture,
    ( v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_853,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_5880,plain,
    ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5785,c_853])).

cnf(c_15,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_860,plain,
    ( k2_pre_topc(X0,X1) = X1
    | v4_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_6975,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | v4_pre_topc(sK1,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_852,c_860])).

cnf(c_24,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_27,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_7333,plain,
    ( v4_pre_topc(sK1,sK0) != iProver_top
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6975,c_27])).

cnf(c_7334,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_7333])).

cnf(c_7339,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_5880,c_7334])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_855,plain,
    ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1208,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_852,c_855])).

cnf(c_1126,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_1437,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1208,c_24,c_23,c_1126])).

cnf(c_5892,plain,
    ( k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_1437,c_5785])).

cnf(c_13,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_5987,plain,
    ( k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_5892,c_13])).

cnf(c_9,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_898,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_0,c_13])).

cnf(c_3035,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_9,c_898])).

cnf(c_6254,plain,
    ( k5_xboole_0(k2_tops_1(sK0,sK1),k4_xboole_0(sK1,k1_tops_1(sK0,sK1))) = k4_xboole_0(k2_tops_1(sK0,sK1),sK1) ),
    inference(superposition,[status(thm)],[c_5987,c_3035])).

cnf(c_10646,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k5_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) = k4_xboole_0(k2_tops_1(sK0,sK1),sK1) ),
    inference(superposition,[status(thm)],[c_7339,c_6254])).

cnf(c_10,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_8,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_894,plain,
    ( k4_xboole_0(X0,k3_tarski(k2_tarski(X0,X1))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_10,c_8])).

cnf(c_1739,plain,
    ( k4_xboole_0(X0,k3_tarski(k2_tarski(X1,X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_9,c_894])).

cnf(c_2687,plain,
    ( k1_setfam_1(k2_tarski(X0,k3_tarski(k2_tarski(X1,X0)))) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1739,c_13])).

cnf(c_6,plain,
    ( k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1269,plain,
    ( k3_tarski(k2_tarski(X0,k1_xboole_0)) = X0 ),
    inference(superposition,[status(thm)],[c_10,c_6])).

cnf(c_1737,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1269,c_894])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1766,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(demodulation,[status(thm)],[c_1737,c_1])).

cnf(c_2693,plain,
    ( k1_setfam_1(k2_tarski(X0,k3_tarski(k2_tarski(X1,X0)))) = X0 ),
    inference(light_normalisation,[status(thm)],[c_2687,c_1766])).

cnf(c_3034,plain,
    ( k4_xboole_0(X0,k3_tarski(k2_tarski(X1,X0))) = k5_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_2693,c_898])).

cnf(c_3043,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3034,c_1739])).

cnf(c_10647,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k4_xboole_0(k2_tops_1(sK0,sK1),sK1) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_10646,c_3043])).

cnf(c_141084,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k5_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_10647,c_10])).

cnf(c_1742,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X0)),k1_xboole_0) = k3_tarski(k2_tarski(k1_xboole_0,X0)) ),
    inference(superposition,[status(thm)],[c_894,c_6])).

cnf(c_1550,plain,
    ( k3_tarski(k2_tarski(k1_xboole_0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_9,c_1269])).

cnf(c_1747,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1742,c_1550])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_859,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k5_xboole_0(X2,k4_xboole_0(X0,X2)) = k4_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_863,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k4_subset_1(X2,X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_937,plain,
    ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_863,c_10])).

cnf(c_20840,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k3_tarski(k2_tarski(sK1,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_852,c_937])).

cnf(c_20926,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_859,c_20840])).

cnf(c_21279,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_20926,c_27])).

cnf(c_21280,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_21279])).

cnf(c_21288,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
    inference(superposition,[status(thm)],[c_852,c_21280])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_856,plain,
    ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1924,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_852,c_856])).

cnf(c_1123,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_2455,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1924,c_24,c_23,c_1123])).

cnf(c_21290,plain,
    ( k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k2_pre_topc(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_21288,c_2455])).

cnf(c_141110,plain,
    ( k2_pre_topc(sK0,sK1) = sK1 ),
    inference(demodulation,[status(thm)],[c_141084,c_1747,c_21290])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_857,plain,
    ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2837,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_852,c_857])).

cnf(c_1134,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_3516,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2837,c_24,c_23,c_1134])).

cnf(c_141394,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_141110,c_3516])).

cnf(c_14,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | k2_pre_topc(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1120,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | k2_pre_topc(sK0,sK1) != sK1 ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_21,negated_conjecture,
    ( ~ v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_25,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f68])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_141394,c_141110,c_1120,c_21,c_23,c_24,c_25])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:46:25 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 59.68/8.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 59.68/8.01  
% 59.68/8.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 59.68/8.01  
% 59.68/8.01  ------  iProver source info
% 59.68/8.01  
% 59.68/8.01  git: date: 2020-06-30 10:37:57 +0100
% 59.68/8.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 59.68/8.01  git: non_committed_changes: false
% 59.68/8.01  git: last_make_outside_of_git: false
% 59.68/8.01  
% 59.68/8.01  ------ 
% 59.68/8.01  ------ Parsing...
% 59.68/8.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 59.68/8.01  
% 59.68/8.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 59.68/8.01  
% 59.68/8.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 59.68/8.01  
% 59.68/8.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 59.68/8.01  ------ Proving...
% 59.68/8.01  ------ Problem Properties 
% 59.68/8.01  
% 59.68/8.01  
% 59.68/8.01  clauses                                 25
% 59.68/8.01  conjectures                             5
% 59.68/8.01  EPR                                     5
% 59.68/8.01  Horn                                    24
% 59.68/8.01  unary                                   13
% 59.68/8.01  binary                                  3
% 59.68/8.01  lits                                    50
% 59.68/8.01  lits eq                                 17
% 59.68/8.01  fd_pure                                 0
% 59.68/8.01  fd_pseudo                               0
% 59.68/8.01  fd_cond                                 0
% 59.68/8.01  fd_pseudo_cond                          1
% 59.68/8.01  AC symbols                              0
% 59.68/8.01  
% 59.68/8.01  ------ Input Options Time Limit: Unbounded
% 59.68/8.01  
% 59.68/8.01  
% 59.68/8.01  ------ 
% 59.68/8.01  Current options:
% 59.68/8.01  ------ 
% 59.68/8.01  
% 59.68/8.01  
% 59.68/8.01  
% 59.68/8.01  
% 59.68/8.01  ------ Proving...
% 59.68/8.01  
% 59.68/8.01  
% 59.68/8.01  % SZS status Theorem for theBenchmark.p
% 59.68/8.01  
% 59.68/8.01  % SZS output start CNFRefutation for theBenchmark.p
% 59.68/8.01  
% 59.68/8.01  fof(f21,conjecture,(
% 59.68/8.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 59.68/8.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.68/8.01  
% 59.68/8.01  fof(f22,negated_conjecture,(
% 59.68/8.01    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 59.68/8.01    inference(negated_conjecture,[],[f21])).
% 59.68/8.01  
% 59.68/8.01  fof(f36,plain,(
% 59.68/8.01    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 59.68/8.01    inference(ennf_transformation,[],[f22])).
% 59.68/8.01  
% 59.68/8.01  fof(f37,plain,(
% 59.68/8.01    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 59.68/8.01    inference(flattening,[],[f36])).
% 59.68/8.01  
% 59.68/8.01  fof(f40,plain,(
% 59.68/8.01    ? [X0] : (? [X1] : (((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 59.68/8.01    inference(nnf_transformation,[],[f37])).
% 59.68/8.01  
% 59.68/8.01  fof(f41,plain,(
% 59.68/8.01    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 59.68/8.01    inference(flattening,[],[f40])).
% 59.68/8.01  
% 59.68/8.01  fof(f43,plain,(
% 59.68/8.01    ( ! [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) != k2_tops_1(X0,sK1) | ~v4_pre_topc(sK1,X0)) & (k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) = k2_tops_1(X0,sK1) | v4_pre_topc(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 59.68/8.01    introduced(choice_axiom,[])).
% 59.68/8.01  
% 59.68/8.01  fof(f42,plain,(
% 59.68/8.01    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) != k2_tops_1(sK0,X1) | ~v4_pre_topc(X1,sK0)) & (k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) = k2_tops_1(sK0,X1) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 59.68/8.01    introduced(choice_axiom,[])).
% 59.68/8.01  
% 59.68/8.01  fof(f44,plain,(
% 59.68/8.01    ((k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)) & (k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 59.68/8.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f41,f43,f42])).
% 59.68/8.01  
% 59.68/8.01  fof(f70,plain,(
% 59.68/8.01    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 59.68/8.01    inference(cnf_transformation,[],[f44])).
% 59.68/8.01  
% 59.68/8.01  fof(f13,axiom,(
% 59.68/8.01    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 59.68/8.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.68/8.01  
% 59.68/8.01  fof(f26,plain,(
% 59.68/8.01    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 59.68/8.01    inference(ennf_transformation,[],[f13])).
% 59.68/8.01  
% 59.68/8.01  fof(f59,plain,(
% 59.68/8.01    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 59.68/8.01    inference(cnf_transformation,[],[f26])).
% 59.68/8.01  
% 59.68/8.01  fof(f71,plain,(
% 59.68/8.01    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)),
% 59.68/8.01    inference(cnf_transformation,[],[f44])).
% 59.68/8.01  
% 59.68/8.01  fof(f15,axiom,(
% 59.68/8.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 59.68/8.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.68/8.01  
% 59.68/8.01  fof(f27,plain,(
% 59.68/8.01    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 59.68/8.01    inference(ennf_transformation,[],[f15])).
% 59.68/8.01  
% 59.68/8.01  fof(f28,plain,(
% 59.68/8.01    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 59.68/8.01    inference(flattening,[],[f27])).
% 59.68/8.01  
% 59.68/8.01  fof(f61,plain,(
% 59.68/8.01    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 59.68/8.01    inference(cnf_transformation,[],[f28])).
% 59.68/8.01  
% 59.68/8.01  fof(f69,plain,(
% 59.68/8.01    l1_pre_topc(sK0)),
% 59.68/8.01    inference(cnf_transformation,[],[f44])).
% 59.68/8.01  
% 59.68/8.01  fof(f20,axiom,(
% 59.68/8.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)))),
% 59.68/8.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.68/8.01  
% 59.68/8.01  fof(f35,plain,(
% 59.68/8.01    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 59.68/8.01    inference(ennf_transformation,[],[f20])).
% 59.68/8.01  
% 59.68/8.01  fof(f67,plain,(
% 59.68/8.01    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 59.68/8.01    inference(cnf_transformation,[],[f35])).
% 59.68/8.01  
% 59.68/8.01  fof(f14,axiom,(
% 59.68/8.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 59.68/8.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.68/8.01  
% 59.68/8.01  fof(f60,plain,(
% 59.68/8.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 59.68/8.01    inference(cnf_transformation,[],[f14])).
% 59.68/8.01  
% 59.68/8.01  fof(f8,axiom,(
% 59.68/8.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 59.68/8.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.68/8.01  
% 59.68/8.01  fof(f54,plain,(
% 59.68/8.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 59.68/8.01    inference(cnf_transformation,[],[f8])).
% 59.68/8.01  
% 59.68/8.01  fof(f80,plain,(
% 59.68/8.01    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 59.68/8.01    inference(definition_unfolding,[],[f60,f54])).
% 59.68/8.01  
% 59.68/8.01  fof(f10,axiom,(
% 59.68/8.01    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 59.68/8.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.68/8.01  
% 59.68/8.01  fof(f56,plain,(
% 59.68/8.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 59.68/8.01    inference(cnf_transformation,[],[f10])).
% 59.68/8.01  
% 59.68/8.01  fof(f3,axiom,(
% 59.68/8.01    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 59.68/8.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.68/8.01  
% 59.68/8.01  fof(f49,plain,(
% 59.68/8.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 59.68/8.01    inference(cnf_transformation,[],[f3])).
% 59.68/8.01  
% 59.68/8.01  fof(f73,plain,(
% 59.68/8.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 59.68/8.01    inference(definition_unfolding,[],[f49,f54])).
% 59.68/8.01  
% 59.68/8.01  fof(f11,axiom,(
% 59.68/8.01    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 59.68/8.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.68/8.01  
% 59.68/8.01  fof(f57,plain,(
% 59.68/8.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 59.68/8.01    inference(cnf_transformation,[],[f11])).
% 59.68/8.01  
% 59.68/8.01  fof(f9,axiom,(
% 59.68/8.01    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 59.68/8.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.68/8.01  
% 59.68/8.01  fof(f55,plain,(
% 59.68/8.01    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 59.68/8.01    inference(cnf_transformation,[],[f9])).
% 59.68/8.01  
% 59.68/8.01  fof(f78,plain,(
% 59.68/8.01    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k2_tarski(X0,X1))) )),
% 59.68/8.01    inference(definition_unfolding,[],[f57,f55])).
% 59.68/8.01  
% 59.68/8.01  fof(f7,axiom,(
% 59.68/8.01    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 59.68/8.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.68/8.01  
% 59.68/8.01  fof(f53,plain,(
% 59.68/8.01    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 59.68/8.01    inference(cnf_transformation,[],[f7])).
% 59.68/8.01  
% 59.68/8.01  fof(f77,plain,(
% 59.68/8.01    ( ! [X0,X1] : (k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) = k1_xboole_0) )),
% 59.68/8.01    inference(definition_unfolding,[],[f53,f55])).
% 59.68/8.01  
% 59.68/8.01  fof(f5,axiom,(
% 59.68/8.01    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 59.68/8.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.68/8.01  
% 59.68/8.01  fof(f51,plain,(
% 59.68/8.01    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 59.68/8.01    inference(cnf_transformation,[],[f5])).
% 59.68/8.01  
% 59.68/8.01  fof(f76,plain,(
% 59.68/8.01    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0) )),
% 59.68/8.01    inference(definition_unfolding,[],[f51,f55])).
% 59.68/8.01  
% 59.68/8.01  fof(f1,axiom,(
% 59.68/8.01    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 59.68/8.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.68/8.01  
% 59.68/8.01  fof(f23,plain,(
% 59.68/8.01    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 59.68/8.01    inference(rectify,[],[f1])).
% 59.68/8.01  
% 59.68/8.01  fof(f45,plain,(
% 59.68/8.01    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 59.68/8.01    inference(cnf_transformation,[],[f23])).
% 59.68/8.01  
% 59.68/8.01  fof(f74,plain,(
% 59.68/8.01    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 59.68/8.01    inference(definition_unfolding,[],[f45,f54])).
% 59.68/8.01  
% 59.68/8.01  fof(f16,axiom,(
% 59.68/8.01    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 59.68/8.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.68/8.01  
% 59.68/8.01  fof(f29,plain,(
% 59.68/8.01    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 59.68/8.01    inference(ennf_transformation,[],[f16])).
% 59.68/8.01  
% 59.68/8.01  fof(f30,plain,(
% 59.68/8.01    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 59.68/8.01    inference(flattening,[],[f29])).
% 59.68/8.01  
% 59.68/8.01  fof(f63,plain,(
% 59.68/8.01    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 59.68/8.01    inference(cnf_transformation,[],[f30])).
% 59.68/8.01  
% 59.68/8.01  fof(f12,axiom,(
% 59.68/8.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 59.68/8.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.68/8.01  
% 59.68/8.01  fof(f24,plain,(
% 59.68/8.01    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 59.68/8.01    inference(ennf_transformation,[],[f12])).
% 59.68/8.01  
% 59.68/8.01  fof(f25,plain,(
% 59.68/8.01    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 59.68/8.01    inference(flattening,[],[f24])).
% 59.68/8.01  
% 59.68/8.01  fof(f58,plain,(
% 59.68/8.01    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 59.68/8.01    inference(cnf_transformation,[],[f25])).
% 59.68/8.01  
% 59.68/8.01  fof(f79,plain,(
% 59.68/8.01    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k4_xboole_0(X2,X1)) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 59.68/8.01    inference(definition_unfolding,[],[f58,f55])).
% 59.68/8.01  
% 59.68/8.01  fof(f19,axiom,(
% 59.68/8.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)))),
% 59.68/8.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.68/8.01  
% 59.68/8.01  fof(f34,plain,(
% 59.68/8.01    ! [X0] : (! [X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 59.68/8.01    inference(ennf_transformation,[],[f19])).
% 59.68/8.01  
% 59.68/8.01  fof(f66,plain,(
% 59.68/8.01    ( ! [X0,X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 59.68/8.01    inference(cnf_transformation,[],[f34])).
% 59.68/8.01  
% 59.68/8.01  fof(f18,axiom,(
% 59.68/8.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)))),
% 59.68/8.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 59.68/8.01  
% 59.68/8.01  fof(f33,plain,(
% 59.68/8.01    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 59.68/8.01    inference(ennf_transformation,[],[f18])).
% 59.68/8.01  
% 59.68/8.01  fof(f65,plain,(
% 59.68/8.01    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 59.68/8.01    inference(cnf_transformation,[],[f33])).
% 59.68/8.01  
% 59.68/8.01  fof(f62,plain,(
% 59.68/8.01    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 59.68/8.01    inference(cnf_transformation,[],[f28])).
% 59.68/8.01  
% 59.68/8.01  fof(f72,plain,(
% 59.68/8.01    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)),
% 59.68/8.01    inference(cnf_transformation,[],[f44])).
% 59.68/8.01  
% 59.68/8.01  fof(f68,plain,(
% 59.68/8.01    v2_pre_topc(sK0)),
% 59.68/8.01    inference(cnf_transformation,[],[f44])).
% 59.68/8.01  
% 59.68/8.01  cnf(c_23,negated_conjecture,
% 59.68/8.01      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 59.68/8.01      inference(cnf_transformation,[],[f70]) ).
% 59.68/8.01  
% 59.68/8.01  cnf(c_852,plain,
% 59.68/8.01      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 59.68/8.01      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 59.68/8.01  
% 59.68/8.01  cnf(c_12,plain,
% 59.68/8.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 59.68/8.01      | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 59.68/8.01      inference(cnf_transformation,[],[f59]) ).
% 59.68/8.01  
% 59.68/8.01  cnf(c_862,plain,
% 59.68/8.01      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
% 59.68/8.01      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 59.68/8.01      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 59.68/8.01  
% 59.68/8.01  cnf(c_5785,plain,
% 59.68/8.01      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
% 59.68/8.01      inference(superposition,[status(thm)],[c_852,c_862]) ).
% 59.68/8.01  
% 59.68/8.01  cnf(c_22,negated_conjecture,
% 59.68/8.01      ( v4_pre_topc(sK1,sK0)
% 59.68/8.01      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 59.68/8.01      inference(cnf_transformation,[],[f71]) ).
% 59.68/8.01  
% 59.68/8.01  cnf(c_853,plain,
% 59.68/8.01      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 59.68/8.01      | v4_pre_topc(sK1,sK0) = iProver_top ),
% 59.68/8.01      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 59.68/8.01  
% 59.68/8.01  cnf(c_5880,plain,
% 59.68/8.01      ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 59.68/8.01      | v4_pre_topc(sK1,sK0) = iProver_top ),
% 59.68/8.01      inference(demodulation,[status(thm)],[c_5785,c_853]) ).
% 59.68/8.01  
% 59.68/8.01  cnf(c_15,plain,
% 59.68/8.01      ( ~ v4_pre_topc(X0,X1)
% 59.68/8.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 59.68/8.01      | ~ l1_pre_topc(X1)
% 59.68/8.01      | k2_pre_topc(X1,X0) = X0 ),
% 59.68/8.01      inference(cnf_transformation,[],[f61]) ).
% 59.68/8.01  
% 59.68/8.01  cnf(c_860,plain,
% 59.68/8.01      ( k2_pre_topc(X0,X1) = X1
% 59.68/8.01      | v4_pre_topc(X1,X0) != iProver_top
% 59.68/8.01      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 59.68/8.01      | l1_pre_topc(X0) != iProver_top ),
% 59.68/8.01      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 59.68/8.01  
% 59.68/8.01  cnf(c_6975,plain,
% 59.68/8.01      ( k2_pre_topc(sK0,sK1) = sK1
% 59.68/8.01      | v4_pre_topc(sK1,sK0) != iProver_top
% 59.68/8.01      | l1_pre_topc(sK0) != iProver_top ),
% 59.68/8.01      inference(superposition,[status(thm)],[c_852,c_860]) ).
% 59.68/8.01  
% 59.68/8.01  cnf(c_24,negated_conjecture,
% 59.68/8.01      ( l1_pre_topc(sK0) ),
% 59.68/8.01      inference(cnf_transformation,[],[f69]) ).
% 59.68/8.01  
% 59.68/8.01  cnf(c_27,plain,
% 59.68/8.01      ( l1_pre_topc(sK0) = iProver_top ),
% 59.68/8.01      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 59.68/8.01  
% 59.68/8.01  cnf(c_7333,plain,
% 59.68/8.01      ( v4_pre_topc(sK1,sK0) != iProver_top
% 59.68/8.01      | k2_pre_topc(sK0,sK1) = sK1 ),
% 59.68/8.01      inference(global_propositional_subsumption,
% 59.68/8.01                [status(thm)],
% 59.68/8.01                [c_6975,c_27]) ).
% 59.68/8.01  
% 59.68/8.01  cnf(c_7334,plain,
% 59.68/8.01      ( k2_pre_topc(sK0,sK1) = sK1
% 59.68/8.01      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 59.68/8.01      inference(renaming,[status(thm)],[c_7333]) ).
% 59.68/8.01  
% 59.68/8.01  cnf(c_7339,plain,
% 59.68/8.01      ( k2_pre_topc(sK0,sK1) = sK1
% 59.68/8.01      | k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 59.68/8.01      inference(superposition,[status(thm)],[c_5880,c_7334]) ).
% 59.68/8.01  
% 59.68/8.01  cnf(c_20,plain,
% 59.68/8.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 59.68/8.01      | ~ l1_pre_topc(X1)
% 59.68/8.01      | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
% 59.68/8.01      inference(cnf_transformation,[],[f67]) ).
% 59.68/8.01  
% 59.68/8.01  cnf(c_855,plain,
% 59.68/8.01      ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
% 59.68/8.01      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 59.68/8.01      | l1_pre_topc(X0) != iProver_top ),
% 59.68/8.01      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 59.68/8.01  
% 59.68/8.01  cnf(c_1208,plain,
% 59.68/8.01      ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1)
% 59.68/8.01      | l1_pre_topc(sK0) != iProver_top ),
% 59.68/8.01      inference(superposition,[status(thm)],[c_852,c_855]) ).
% 59.68/8.01  
% 59.68/8.01  cnf(c_1126,plain,
% 59.68/8.01      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 59.68/8.01      | ~ l1_pre_topc(sK0)
% 59.68/8.01      | k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
% 59.68/8.01      inference(instantiation,[status(thm)],[c_20]) ).
% 59.68/8.01  
% 59.68/8.01  cnf(c_1437,plain,
% 59.68/8.01      ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
% 59.68/8.01      inference(global_propositional_subsumption,
% 59.68/8.01                [status(thm)],
% 59.68/8.01                [c_1208,c_24,c_23,c_1126]) ).
% 59.68/8.01  
% 59.68/8.01  cnf(c_5892,plain,
% 59.68/8.01      ( k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
% 59.68/8.01      inference(superposition,[status(thm)],[c_1437,c_5785]) ).
% 59.68/8.01  
% 59.68/8.01  cnf(c_13,plain,
% 59.68/8.01      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
% 59.68/8.01      inference(cnf_transformation,[],[f80]) ).
% 59.68/8.01  
% 59.68/8.01  cnf(c_5987,plain,
% 59.68/8.01      ( k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
% 59.68/8.01      inference(superposition,[status(thm)],[c_5892,c_13]) ).
% 59.68/8.01  
% 59.68/8.01  cnf(c_9,plain,
% 59.68/8.01      ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
% 59.68/8.01      inference(cnf_transformation,[],[f56]) ).
% 59.68/8.01  
% 59.68/8.01  cnf(c_0,plain,
% 59.68/8.01      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 59.68/8.01      inference(cnf_transformation,[],[f73]) ).
% 59.68/8.01  
% 59.68/8.01  cnf(c_898,plain,
% 59.68/8.01      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k4_xboole_0(X0,X1) ),
% 59.68/8.01      inference(light_normalisation,[status(thm)],[c_0,c_13]) ).
% 59.68/8.01  
% 59.68/8.01  cnf(c_3035,plain,
% 59.68/8.01      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0))) = k4_xboole_0(X0,X1) ),
% 59.68/8.01      inference(superposition,[status(thm)],[c_9,c_898]) ).
% 59.68/8.01  
% 59.68/8.01  cnf(c_6254,plain,
% 59.68/8.01      ( k5_xboole_0(k2_tops_1(sK0,sK1),k4_xboole_0(sK1,k1_tops_1(sK0,sK1))) = k4_xboole_0(k2_tops_1(sK0,sK1),sK1) ),
% 59.68/8.01      inference(superposition,[status(thm)],[c_5987,c_3035]) ).
% 59.68/8.01  
% 59.68/8.01  cnf(c_10646,plain,
% 59.68/8.01      ( k2_pre_topc(sK0,sK1) = sK1
% 59.68/8.01      | k5_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) = k4_xboole_0(k2_tops_1(sK0,sK1),sK1) ),
% 59.68/8.01      inference(superposition,[status(thm)],[c_7339,c_6254]) ).
% 59.68/8.01  
% 59.68/8.01  cnf(c_10,plain,
% 59.68/8.01      ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k2_tarski(X0,X1)) ),
% 59.68/8.01      inference(cnf_transformation,[],[f78]) ).
% 59.68/8.01  
% 59.68/8.01  cnf(c_8,plain,
% 59.68/8.01      ( k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) = k1_xboole_0 ),
% 59.68/8.01      inference(cnf_transformation,[],[f77]) ).
% 59.68/8.01  
% 59.68/8.01  cnf(c_894,plain,
% 59.68/8.01      ( k4_xboole_0(X0,k3_tarski(k2_tarski(X0,X1))) = k1_xboole_0 ),
% 59.68/8.01      inference(demodulation,[status(thm)],[c_10,c_8]) ).
% 59.68/8.01  
% 59.68/8.01  cnf(c_1739,plain,
% 59.68/8.01      ( k4_xboole_0(X0,k3_tarski(k2_tarski(X1,X0))) = k1_xboole_0 ),
% 59.68/8.01      inference(superposition,[status(thm)],[c_9,c_894]) ).
% 59.68/8.01  
% 59.68/8.01  cnf(c_2687,plain,
% 59.68/8.01      ( k1_setfam_1(k2_tarski(X0,k3_tarski(k2_tarski(X1,X0)))) = k4_xboole_0(X0,k1_xboole_0) ),
% 59.68/8.01      inference(superposition,[status(thm)],[c_1739,c_13]) ).
% 59.68/8.01  
% 59.68/8.01  cnf(c_6,plain,
% 59.68/8.01      ( k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
% 59.68/8.01      inference(cnf_transformation,[],[f76]) ).
% 59.68/8.01  
% 59.68/8.01  cnf(c_1269,plain,
% 59.68/8.01      ( k3_tarski(k2_tarski(X0,k1_xboole_0)) = X0 ),
% 59.68/8.01      inference(superposition,[status(thm)],[c_10,c_6]) ).
% 59.68/8.01  
% 59.68/8.01  cnf(c_1737,plain,
% 59.68/8.01      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 59.68/8.01      inference(superposition,[status(thm)],[c_1269,c_894]) ).
% 59.68/8.01  
% 59.68/8.01  cnf(c_1,plain,
% 59.68/8.01      ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
% 59.68/8.01      inference(cnf_transformation,[],[f74]) ).
% 59.68/8.01  
% 59.68/8.01  cnf(c_1766,plain,
% 59.68/8.01      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 59.68/8.01      inference(demodulation,[status(thm)],[c_1737,c_1]) ).
% 59.68/8.01  
% 59.68/8.01  cnf(c_2693,plain,
% 59.68/8.01      ( k1_setfam_1(k2_tarski(X0,k3_tarski(k2_tarski(X1,X0)))) = X0 ),
% 59.68/8.01      inference(light_normalisation,[status(thm)],[c_2687,c_1766]) ).
% 59.68/8.01  
% 59.68/8.01  cnf(c_3034,plain,
% 59.68/8.01      ( k4_xboole_0(X0,k3_tarski(k2_tarski(X1,X0))) = k5_xboole_0(X0,X0) ),
% 59.68/8.01      inference(superposition,[status(thm)],[c_2693,c_898]) ).
% 59.68/8.01  
% 59.68/8.01  cnf(c_3043,plain,
% 59.68/8.01      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 59.68/8.01      inference(light_normalisation,[status(thm)],[c_3034,c_1739]) ).
% 59.68/8.01  
% 59.68/8.01  cnf(c_10647,plain,
% 59.68/8.01      ( k2_pre_topc(sK0,sK1) = sK1
% 59.68/8.01      | k4_xboole_0(k2_tops_1(sK0,sK1),sK1) = k1_xboole_0 ),
% 59.68/8.01      inference(demodulation,[status(thm)],[c_10646,c_3043]) ).
% 59.68/8.01  
% 59.68/8.01  cnf(c_141084,plain,
% 59.68/8.01      ( k2_pre_topc(sK0,sK1) = sK1
% 59.68/8.01      | k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k5_xboole_0(sK1,k1_xboole_0) ),
% 59.68/8.01      inference(superposition,[status(thm)],[c_10647,c_10]) ).
% 59.68/8.01  
% 59.68/8.01  cnf(c_1742,plain,
% 59.68/8.01      ( k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X0)),k1_xboole_0) = k3_tarski(k2_tarski(k1_xboole_0,X0)) ),
% 59.68/8.01      inference(superposition,[status(thm)],[c_894,c_6]) ).
% 59.68/8.01  
% 59.68/8.01  cnf(c_1550,plain,
% 59.68/8.01      ( k3_tarski(k2_tarski(k1_xboole_0,X0)) = X0 ),
% 59.68/8.01      inference(superposition,[status(thm)],[c_9,c_1269]) ).
% 59.68/8.01  
% 59.68/8.01  cnf(c_1747,plain,
% 59.68/8.01      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 59.68/8.01      inference(light_normalisation,[status(thm)],[c_1742,c_1550]) ).
% 59.68/8.01  
% 59.68/8.01  cnf(c_16,plain,
% 59.68/8.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 59.68/8.01      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 59.68/8.01      | ~ l1_pre_topc(X1) ),
% 59.68/8.01      inference(cnf_transformation,[],[f63]) ).
% 59.68/8.01  
% 59.68/8.01  cnf(c_859,plain,
% 59.68/8.01      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 59.68/8.01      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 59.68/8.01      | l1_pre_topc(X1) != iProver_top ),
% 59.68/8.01      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 59.68/8.01  
% 59.68/8.01  cnf(c_11,plain,
% 59.68/8.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 59.68/8.01      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 59.68/8.01      | k5_xboole_0(X2,k4_xboole_0(X0,X2)) = k4_subset_1(X1,X2,X0) ),
% 59.68/8.01      inference(cnf_transformation,[],[f79]) ).
% 59.68/8.01  
% 59.68/8.01  cnf(c_863,plain,
% 59.68/8.01      ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k4_subset_1(X2,X0,X1)
% 59.68/8.01      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
% 59.68/8.01      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
% 59.68/8.01      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 59.68/8.01  
% 59.68/8.01  cnf(c_937,plain,
% 59.68/8.01      ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
% 59.68/8.01      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
% 59.68/8.01      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 59.68/8.01      inference(light_normalisation,[status(thm)],[c_863,c_10]) ).
% 59.68/8.01  
% 59.68/8.01  cnf(c_20840,plain,
% 59.68/8.01      ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k3_tarski(k2_tarski(sK1,X0))
% 59.68/8.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 59.68/8.01      inference(superposition,[status(thm)],[c_852,c_937]) ).
% 59.68/8.01  
% 59.68/8.01  cnf(c_20926,plain,
% 59.68/8.01      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0)))
% 59.68/8.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 59.68/8.01      | l1_pre_topc(sK0) != iProver_top ),
% 59.68/8.01      inference(superposition,[status(thm)],[c_859,c_20840]) ).
% 59.68/8.01  
% 59.68/8.01  cnf(c_21279,plain,
% 59.68/8.01      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 59.68/8.01      | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0))) ),
% 59.68/8.01      inference(global_propositional_subsumption,
% 59.68/8.01                [status(thm)],
% 59.68/8.01                [c_20926,c_27]) ).
% 59.68/8.01  
% 59.68/8.01  cnf(c_21280,plain,
% 59.68/8.01      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0)))
% 59.68/8.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 59.68/8.01      inference(renaming,[status(thm)],[c_21279]) ).
% 59.68/8.01  
% 59.68/8.01  cnf(c_21288,plain,
% 59.68/8.01      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
% 59.68/8.01      inference(superposition,[status(thm)],[c_852,c_21280]) ).
% 59.68/8.01  
% 59.68/8.01  cnf(c_19,plain,
% 59.68/8.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 59.68/8.01      | ~ l1_pre_topc(X1)
% 59.68/8.01      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
% 59.68/8.01      inference(cnf_transformation,[],[f66]) ).
% 59.68/8.01  
% 59.68/8.01  cnf(c_856,plain,
% 59.68/8.01      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
% 59.68/8.01      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 59.68/8.01      | l1_pre_topc(X0) != iProver_top ),
% 59.68/8.01      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 59.68/8.01  
% 59.68/8.01  cnf(c_1924,plain,
% 59.68/8.01      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
% 59.68/8.01      | l1_pre_topc(sK0) != iProver_top ),
% 59.68/8.01      inference(superposition,[status(thm)],[c_852,c_856]) ).
% 59.68/8.01  
% 59.68/8.01  cnf(c_1123,plain,
% 59.68/8.01      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 59.68/8.01      | ~ l1_pre_topc(sK0)
% 59.68/8.01      | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 59.68/8.01      inference(instantiation,[status(thm)],[c_19]) ).
% 59.68/8.01  
% 59.68/8.01  cnf(c_2455,plain,
% 59.68/8.01      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 59.68/8.01      inference(global_propositional_subsumption,
% 59.68/8.01                [status(thm)],
% 59.68/8.01                [c_1924,c_24,c_23,c_1123]) ).
% 59.68/8.01  
% 59.68/8.01  cnf(c_21290,plain,
% 59.68/8.01      ( k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k2_pre_topc(sK0,sK1) ),
% 59.68/8.01      inference(light_normalisation,[status(thm)],[c_21288,c_2455]) ).
% 59.68/8.01  
% 59.68/8.01  cnf(c_141110,plain,
% 59.68/8.01      ( k2_pre_topc(sK0,sK1) = sK1 ),
% 59.68/8.01      inference(demodulation,[status(thm)],[c_141084,c_1747,c_21290]) ).
% 59.68/8.01  
% 59.68/8.01  cnf(c_18,plain,
% 59.68/8.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 59.68/8.01      | ~ l1_pre_topc(X1)
% 59.68/8.01      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
% 59.68/8.01      inference(cnf_transformation,[],[f65]) ).
% 59.68/8.01  
% 59.68/8.01  cnf(c_857,plain,
% 59.68/8.01      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
% 59.68/8.01      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 59.68/8.01      | l1_pre_topc(X0) != iProver_top ),
% 59.68/8.01      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 59.68/8.01  
% 59.68/8.01  cnf(c_2837,plain,
% 59.68/8.01      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 59.68/8.01      | l1_pre_topc(sK0) != iProver_top ),
% 59.68/8.01      inference(superposition,[status(thm)],[c_852,c_857]) ).
% 59.68/8.01  
% 59.68/8.01  cnf(c_1134,plain,
% 59.68/8.01      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 59.68/8.01      | ~ l1_pre_topc(sK0)
% 59.68/8.01      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 59.68/8.01      inference(instantiation,[status(thm)],[c_18]) ).
% 59.68/8.01  
% 59.68/8.01  cnf(c_3516,plain,
% 59.68/8.01      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 59.68/8.01      inference(global_propositional_subsumption,
% 59.68/8.01                [status(thm)],
% 59.68/8.01                [c_2837,c_24,c_23,c_1134]) ).
% 59.68/8.01  
% 59.68/8.01  cnf(c_141394,plain,
% 59.68/8.01      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 59.68/8.01      inference(demodulation,[status(thm)],[c_141110,c_3516]) ).
% 59.68/8.01  
% 59.68/8.01  cnf(c_14,plain,
% 59.68/8.01      ( v4_pre_topc(X0,X1)
% 59.68/8.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 59.68/8.01      | ~ l1_pre_topc(X1)
% 59.68/8.01      | ~ v2_pre_topc(X1)
% 59.68/8.01      | k2_pre_topc(X1,X0) != X0 ),
% 59.68/8.01      inference(cnf_transformation,[],[f62]) ).
% 59.68/8.01  
% 59.68/8.01  cnf(c_1120,plain,
% 59.68/8.01      ( v4_pre_topc(sK1,sK0)
% 59.68/8.01      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 59.68/8.01      | ~ l1_pre_topc(sK0)
% 59.68/8.01      | ~ v2_pre_topc(sK0)
% 59.68/8.01      | k2_pre_topc(sK0,sK1) != sK1 ),
% 59.68/8.01      inference(instantiation,[status(thm)],[c_14]) ).
% 59.68/8.01  
% 59.68/8.01  cnf(c_21,negated_conjecture,
% 59.68/8.01      ( ~ v4_pre_topc(sK1,sK0)
% 59.68/8.01      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
% 59.68/8.01      inference(cnf_transformation,[],[f72]) ).
% 59.68/8.01  
% 59.68/8.01  cnf(c_25,negated_conjecture,
% 59.68/8.01      ( v2_pre_topc(sK0) ),
% 59.68/8.01      inference(cnf_transformation,[],[f68]) ).
% 59.68/8.01  
% 59.68/8.01  cnf(contradiction,plain,
% 59.68/8.01      ( $false ),
% 59.68/8.01      inference(minisat,
% 59.68/8.01                [status(thm)],
% 59.68/8.01                [c_141394,c_141110,c_1120,c_21,c_23,c_24,c_25]) ).
% 59.68/8.01  
% 59.68/8.01  
% 59.68/8.01  % SZS output end CNFRefutation for theBenchmark.p
% 59.68/8.01  
% 59.68/8.01  ------                               Statistics
% 59.68/8.01  
% 59.68/8.01  ------ Selected
% 59.68/8.01  
% 59.68/8.01  total_time:                             7.287
% 59.68/8.01  
%------------------------------------------------------------------------------
