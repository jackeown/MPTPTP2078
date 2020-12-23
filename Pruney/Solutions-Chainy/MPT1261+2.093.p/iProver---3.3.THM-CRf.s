%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:14:37 EST 2020

% Result     : Theorem 12.00s
% Output     : CNFRefutation 12.00s
% Verified   : 
% Statistics : Number of formulae       :  201 (2208 expanded)
%              Number of clauses        :  128 ( 691 expanded)
%              Number of leaves         :   22 ( 502 expanded)
%              Depth                    :   21
%              Number of atoms          :  439 (7931 expanded)
%              Number of equality atoms :  240 (2716 expanded)
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

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

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
    inference(nnf_transformation,[],[f39])).

fof(f42,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1)
            | ~ v4_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f41])).

fof(f44,plain,(
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

fof(f43,plain,
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

fof(f45,plain,
    ( ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f42,f44,f43])).

fof(f70,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f45])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f71,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f16,axiom,(
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
    inference(ennf_transformation,[],[f16])).

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

fof(f62,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f69,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
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
    inference(cnf_transformation,[],[f37])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f26])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f14,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f76,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(definition_unfolding,[],[f59,f52])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => r1_tarski(k2_tops_1(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_tops_1(X0,X1),X1)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f49,f52])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f74,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f47,f52,f52])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f8,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f18,axiom,(
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
    inference(ennf_transformation,[],[f18])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f73,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f48,f52])).

fof(f72,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) != X1
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f68,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_807,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_816,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1879,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_807,c_816])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_13,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_153,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_13])).

cnf(c_154,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_153])).

cnf(c_198,plain,
    ( ~ r1_tarski(X0,X1)
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_10,c_154])).

cnf(c_801,plain,
    ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_198])).

cnf(c_14828,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
    inference(superposition,[status(thm)],[c_1879,c_801])).

cnf(c_22,negated_conjecture,
    ( v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_808,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_16,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_814,plain,
    ( k2_pre_topc(X0,X1) = X1
    | v4_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_7438,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | v4_pre_topc(sK1,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_807,c_814])).

cnf(c_24,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_27,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_7866,plain,
    ( v4_pre_topc(sK1,sK0) != iProver_top
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7438,c_27])).

cnf(c_7867,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_7866])).

cnf(c_7872,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_808,c_7867])).

cnf(c_15920,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_14828,c_7872])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_810,plain,
    ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_7255,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_807,c_810])).

cnf(c_1094,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_7746,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7255,c_24,c_23,c_1094])).

cnf(c_15922,plain,
    ( k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_14828,c_7746])).

cnf(c_4,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_818,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_817,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_197,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,X1)
    | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_9,c_154])).

cnf(c_802,plain,
    ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_197])).

cnf(c_37281,plain,
    ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_817,c_802])).

cnf(c_41959,plain,
    ( k4_subset_1(X0,k4_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X1),X2)
    | r1_tarski(X2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_818,c_37281])).

cnf(c_42168,plain,
    ( k4_subset_1(X0,k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_818,c_41959])).

cnf(c_43731,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,k2_tops_1(sK0,sK1)),k4_xboole_0(sK1,X0)) = k4_subset_1(sK1,k1_tops_1(sK0,sK1),k4_xboole_0(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_15922,c_42168])).

cnf(c_43838,plain,
    ( k4_subset_1(sK1,k1_tops_1(sK0,sK1),k4_xboole_0(sK1,X0)) = k2_xboole_0(k1_tops_1(sK0,sK1),k4_xboole_0(sK1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_43731,c_15922])).

cnf(c_44272,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k2_xboole_0(k1_tops_1(sK0,sK1),k4_xboole_0(sK1,k1_tops_1(sK0,sK1))) = k4_subset_1(sK1,k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_15920,c_43838])).

cnf(c_12,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_16237,plain,
    ( k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_15922,c_12])).

cnf(c_19,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k2_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_811,plain,
    ( v4_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(k2_tops_1(X1,X0),X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1210,plain,
    ( v4_pre_topc(sK1,sK0) != iProver_top
    | r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_807,c_811])).

cnf(c_1558,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1210,c_27])).

cnf(c_1559,plain,
    ( v4_pre_topc(sK1,sK0) != iProver_top
    | r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(renaming,[status(thm)],[c_1558])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_819,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_836,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_2,c_12])).

cnf(c_854,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = X1
    | r1_tarski(X1,X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_819,c_836])).

cnf(c_2476,plain,
    ( k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1559,c_854])).

cnf(c_2651,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_808,c_2476])).

cnf(c_15921,plain,
    ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_14828,c_2651])).

cnf(c_16884,plain,
    ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_16237,c_15921])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_195,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_7,c_154])).

cnf(c_804,plain,
    ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_195])).

cnf(c_12887,plain,
    ( k3_subset_1(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_818,c_804])).

cnf(c_12947,plain,
    ( k3_subset_1(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_12887,c_836])).

cnf(c_16224,plain,
    ( k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),sK1)) = k3_subset_1(sK1,k1_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_15922,c_12947])).

cnf(c_16236,plain,
    ( k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),sK1)) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_15922,c_836])).

cnf(c_16268,plain,
    ( k3_subset_1(sK1,k1_tops_1(sK0,sK1)) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    inference(light_normalisation,[status(thm)],[c_16224,c_16236])).

cnf(c_22483,plain,
    ( k3_subset_1(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_16268,c_16884])).

cnf(c_16238,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_15922,c_818])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X0,k3_subset_1(X1,X0)) = k2_subset_1(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_199,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_subset_1(X1,X0,k3_subset_1(X1,X0)) = k2_subset_1(X1) ),
    inference(bin_hyper_res,[status(thm)],[c_11,c_154])).

cnf(c_800,plain,
    ( k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = k2_subset_1(X0)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_199])).

cnf(c_6,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_867,plain,
    ( k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = X0
    | r1_tarski(X1,X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_800,c_6])).

cnf(c_17268,plain,
    ( k4_subset_1(sK1,k1_tops_1(sK0,sK1),k3_subset_1(sK1,k1_tops_1(sK0,sK1))) = sK1 ),
    inference(superposition,[status(thm)],[c_16238,c_867])).

cnf(c_22485,plain,
    ( k4_subset_1(sK1,k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) = sK1 ),
    inference(demodulation,[status(thm)],[c_22483,c_17268])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_813,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2077,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(k2_tops_1(X1,X0),u1_struct_0(X1)) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_813,c_816])).

cnf(c_41963,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k2_xboole_0(sK1,X0)
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1879,c_37281])).

cnf(c_42483,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2077,c_41963])).

cnf(c_43181,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_42483,c_27])).

cnf(c_43182,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_43181])).

cnf(c_43192,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_807,c_43182])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_812,plain,
    ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_7407,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_807,c_812])).

cnf(c_1091,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_7750,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7407,c_24,c_23,c_1091])).

cnf(c_43197,plain,
    ( k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_43192,c_7750])).

cnf(c_2474,plain,
    ( k1_setfam_1(k2_tarski(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_818,c_854])).

cnf(c_1539,plain,
    ( k1_setfam_1(k2_tarski(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0))) ),
    inference(superposition,[status(thm)],[c_836,c_12])).

cnf(c_5,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2295,plain,
    ( k2_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),k1_setfam_1(k2_tarski(X1,k4_xboole_0(X1,X0)))) = k2_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),X1) ),
    inference(superposition,[status(thm)],[c_1539,c_5])).

cnf(c_8416,plain,
    ( k2_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),k4_xboole_0(X1,X0)) = k2_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),X1) ),
    inference(demodulation,[status(thm)],[c_2474,c_2295])).

cnf(c_1427,plain,
    ( k1_setfam_1(k2_tarski(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(superposition,[status(thm)],[c_12,c_12])).

cnf(c_2278,plain,
    ( k2_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),k1_setfam_1(k2_tarski(X0,k4_xboole_0(X0,X1)))) = k2_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
    inference(superposition,[status(thm)],[c_1427,c_5])).

cnf(c_8411,plain,
    ( k2_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),k4_xboole_0(X0,X1)) = k2_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
    inference(demodulation,[status(thm)],[c_2474,c_2278])).

cnf(c_1,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_21260,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k1_setfam_1(k2_tarski(X0,X1))) = k2_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
    inference(superposition,[status(thm)],[c_8411,c_1])).

cnf(c_1430,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k1_setfam_1(k2_tarski(X0,X1))) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_12,c_5])).

cnf(c_21263,plain,
    ( k2_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),X0) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(light_normalisation,[status(thm)],[c_21260,c_1430])).

cnf(c_21299,plain,
    ( k2_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_21263,c_1])).

cnf(c_21580,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = k2_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_2474,c_21299])).

cnf(c_21623,plain,
    ( k2_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),X1) = k2_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_21580,c_836])).

cnf(c_23200,plain,
    ( k2_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),k4_xboole_0(X1,X0)) = k2_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_8416,c_21623])).

cnf(c_23226,plain,
    ( k2_xboole_0(k1_setfam_1(k2_tarski(k1_tops_1(sK0,sK1),sK1)),k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k4_xboole_0(sK1,k1_tops_1(sK0,sK1))) ),
    inference(superposition,[status(thm)],[c_16884,c_23200])).

cnf(c_1541,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(superposition,[status(thm)],[c_836,c_12])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_839,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_0,c_836])).

cnf(c_1763,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1541,c_839])).

cnf(c_8444,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_2474,c_1763])).

cnf(c_8453,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_8444,c_836])).

cnf(c_9659,plain,
    ( k1_setfam_1(k2_tarski(k4_xboole_0(X0,X1),X0)) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(superposition,[status(thm)],[c_12,c_8453])).

cnf(c_9683,plain,
    ( k1_setfam_1(k2_tarski(k4_xboole_0(X0,X1),X0)) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_9659,c_1763])).

cnf(c_16231,plain,
    ( k1_setfam_1(k2_tarski(k1_tops_1(sK0,sK1),sK1)) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_15922,c_9683])).

cnf(c_16257,plain,
    ( k1_setfam_1(k2_tarski(k1_tops_1(sK0,sK1),sK1)) = k1_tops_1(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_16231,c_15922])).

cnf(c_23241,plain,
    ( k2_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    inference(light_normalisation,[status(thm)],[c_23226,c_16257,c_16884])).

cnf(c_43384,plain,
    ( k2_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_43197,c_23241])).

cnf(c_44279,plain,
    ( k2_pre_topc(sK0,sK1) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_44272,c_16884,c_22485,c_43384])).

cnf(c_21,negated_conjecture,
    ( ~ v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_809,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_15904,plain,
    ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_14828,c_809])).

cnf(c_15,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | k2_pre_topc(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1088,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | k2_pre_topc(sK0,sK1) != sK1 ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1089,plain,
    ( k2_pre_topc(sK0,sK1) != sK1
    | v4_pre_topc(sK1,sK0) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1088])).

cnf(c_28,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_25,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_26,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_44279,c_16884,c_15904,c_1089,c_28,c_27,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:22:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 12.00/1.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.00/1.98  
% 12.00/1.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 12.00/1.98  
% 12.00/1.98  ------  iProver source info
% 12.00/1.98  
% 12.00/1.98  git: date: 2020-06-30 10:37:57 +0100
% 12.00/1.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 12.00/1.98  git: non_committed_changes: false
% 12.00/1.98  git: last_make_outside_of_git: false
% 12.00/1.98  
% 12.00/1.98  ------ 
% 12.00/1.98  ------ Parsing...
% 12.00/1.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 12.00/1.98  
% 12.00/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 12.00/1.98  
% 12.00/1.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 12.00/1.98  
% 12.00/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 12.00/1.98  ------ Proving...
% 12.00/1.98  ------ Problem Properties 
% 12.00/1.98  
% 12.00/1.98  
% 12.00/1.98  clauses                                 26
% 12.00/1.98  conjectures                             5
% 12.00/1.98  EPR                                     2
% 12.00/1.98  Horn                                    25
% 12.00/1.98  unary                                   10
% 12.00/1.98  binary                                  9
% 12.00/1.98  lits                                    53
% 12.00/1.98  lits eq                                 17
% 12.00/1.98  fd_pure                                 0
% 12.00/1.98  fd_pseudo                               0
% 12.00/1.98  fd_cond                                 0
% 12.00/1.98  fd_pseudo_cond                          0
% 12.00/1.98  AC symbols                              0
% 12.00/1.98  
% 12.00/1.98  ------ Input Options Time Limit: Unbounded
% 12.00/1.98  
% 12.00/1.98  
% 12.00/1.98  ------ 
% 12.00/1.98  Current options:
% 12.00/1.98  ------ 
% 12.00/1.98  
% 12.00/1.98  
% 12.00/1.98  
% 12.00/1.98  
% 12.00/1.98  ------ Proving...
% 12.00/1.98  
% 12.00/1.98  
% 12.00/1.98  % SZS status Theorem for theBenchmark.p
% 12.00/1.98  
% 12.00/1.98  % SZS output start CNFRefutation for theBenchmark.p
% 12.00/1.98  
% 12.00/1.98  fof(f21,conjecture,(
% 12.00/1.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 12.00/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.00/1.98  
% 12.00/1.98  fof(f22,negated_conjecture,(
% 12.00/1.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 12.00/1.98    inference(negated_conjecture,[],[f21])).
% 12.00/1.98  
% 12.00/1.98  fof(f38,plain,(
% 12.00/1.98    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 12.00/1.98    inference(ennf_transformation,[],[f22])).
% 12.00/1.98  
% 12.00/1.98  fof(f39,plain,(
% 12.00/1.98    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 12.00/1.98    inference(flattening,[],[f38])).
% 12.00/1.98  
% 12.00/1.98  fof(f41,plain,(
% 12.00/1.98    ? [X0] : (? [X1] : (((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 12.00/1.98    inference(nnf_transformation,[],[f39])).
% 12.00/1.98  
% 12.00/1.98  fof(f42,plain,(
% 12.00/1.98    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 12.00/1.98    inference(flattening,[],[f41])).
% 12.00/1.98  
% 12.00/1.98  fof(f44,plain,(
% 12.00/1.98    ( ! [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) != k2_tops_1(X0,sK1) | ~v4_pre_topc(sK1,X0)) & (k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) = k2_tops_1(X0,sK1) | v4_pre_topc(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 12.00/1.98    introduced(choice_axiom,[])).
% 12.00/1.98  
% 12.00/1.98  fof(f43,plain,(
% 12.00/1.98    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) != k2_tops_1(sK0,X1) | ~v4_pre_topc(X1,sK0)) & (k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) = k2_tops_1(sK0,X1) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 12.00/1.98    introduced(choice_axiom,[])).
% 12.00/1.98  
% 12.00/1.98  fof(f45,plain,(
% 12.00/1.98    ((k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)) & (k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 12.00/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f42,f44,f43])).
% 12.00/1.98  
% 12.00/1.98  fof(f70,plain,(
% 12.00/1.98    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 12.00/1.98    inference(cnf_transformation,[],[f45])).
% 12.00/1.98  
% 12.00/1.98  fof(f15,axiom,(
% 12.00/1.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 12.00/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.00/1.98  
% 12.00/1.98  fof(f40,plain,(
% 12.00/1.98    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 12.00/1.98    inference(nnf_transformation,[],[f15])).
% 12.00/1.98  
% 12.00/1.98  fof(f60,plain,(
% 12.00/1.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 12.00/1.98    inference(cnf_transformation,[],[f40])).
% 12.00/1.98  
% 12.00/1.98  fof(f12,axiom,(
% 12.00/1.98    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 12.00/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.00/1.98  
% 12.00/1.98  fof(f28,plain,(
% 12.00/1.98    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 12.00/1.98    inference(ennf_transformation,[],[f12])).
% 12.00/1.98  
% 12.00/1.98  fof(f57,plain,(
% 12.00/1.98    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 12.00/1.98    inference(cnf_transformation,[],[f28])).
% 12.00/1.98  
% 12.00/1.98  fof(f61,plain,(
% 12.00/1.98    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 12.00/1.98    inference(cnf_transformation,[],[f40])).
% 12.00/1.98  
% 12.00/1.98  fof(f71,plain,(
% 12.00/1.98    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)),
% 12.00/1.98    inference(cnf_transformation,[],[f45])).
% 12.00/1.98  
% 12.00/1.98  fof(f16,axiom,(
% 12.00/1.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 12.00/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.00/1.98  
% 12.00/1.98  fof(f30,plain,(
% 12.00/1.98    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 12.00/1.98    inference(ennf_transformation,[],[f16])).
% 12.00/1.98  
% 12.00/1.98  fof(f31,plain,(
% 12.00/1.98    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 12.00/1.98    inference(flattening,[],[f30])).
% 12.00/1.98  
% 12.00/1.98  fof(f62,plain,(
% 12.00/1.98    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 12.00/1.98    inference(cnf_transformation,[],[f31])).
% 12.00/1.98  
% 12.00/1.98  fof(f69,plain,(
% 12.00/1.98    l1_pre_topc(sK0)),
% 12.00/1.98    inference(cnf_transformation,[],[f45])).
% 12.00/1.98  
% 12.00/1.98  fof(f20,axiom,(
% 12.00/1.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)))),
% 12.00/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.00/1.98  
% 12.00/1.98  fof(f37,plain,(
% 12.00/1.98    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 12.00/1.98    inference(ennf_transformation,[],[f20])).
% 12.00/1.98  
% 12.00/1.98  fof(f67,plain,(
% 12.00/1.98    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 12.00/1.98    inference(cnf_transformation,[],[f37])).
% 12.00/1.98  
% 12.00/1.98  fof(f5,axiom,(
% 12.00/1.98    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 12.00/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.00/1.98  
% 12.00/1.98  fof(f50,plain,(
% 12.00/1.98    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 12.00/1.98    inference(cnf_transformation,[],[f5])).
% 12.00/1.98  
% 12.00/1.98  fof(f11,axiom,(
% 12.00/1.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 12.00/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.00/1.98  
% 12.00/1.98  fof(f26,plain,(
% 12.00/1.98    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 12.00/1.98    inference(ennf_transformation,[],[f11])).
% 12.00/1.98  
% 12.00/1.98  fof(f27,plain,(
% 12.00/1.98    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 12.00/1.98    inference(flattening,[],[f26])).
% 12.00/1.98  
% 12.00/1.98  fof(f56,plain,(
% 12.00/1.98    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 12.00/1.98    inference(cnf_transformation,[],[f27])).
% 12.00/1.98  
% 12.00/1.98  fof(f14,axiom,(
% 12.00/1.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 12.00/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.00/1.98  
% 12.00/1.98  fof(f59,plain,(
% 12.00/1.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 12.00/1.99    inference(cnf_transformation,[],[f14])).
% 12.00/1.99  
% 12.00/1.99  fof(f7,axiom,(
% 12.00/1.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 12.00/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.00/1.99  
% 12.00/1.99  fof(f52,plain,(
% 12.00/1.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 12.00/1.99    inference(cnf_transformation,[],[f7])).
% 12.00/1.99  
% 12.00/1.99  fof(f76,plain,(
% 12.00/1.99    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 12.00/1.99    inference(definition_unfolding,[],[f59,f52])).
% 12.00/1.99  
% 12.00/1.99  fof(f19,axiom,(
% 12.00/1.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => r1_tarski(k2_tops_1(X0,X1),X1))))),
% 12.00/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.00/1.99  
% 12.00/1.99  fof(f35,plain,(
% 12.00/1.99    ! [X0] : (! [X1] : ((r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 12.00/1.99    inference(ennf_transformation,[],[f19])).
% 12.00/1.99  
% 12.00/1.99  fof(f36,plain,(
% 12.00/1.99    ! [X0] : (! [X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 12.00/1.99    inference(flattening,[],[f35])).
% 12.00/1.99  
% 12.00/1.99  fof(f66,plain,(
% 12.00/1.99    ( ! [X0,X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 12.00/1.99    inference(cnf_transformation,[],[f36])).
% 12.00/1.99  
% 12.00/1.99  fof(f4,axiom,(
% 12.00/1.99    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 12.00/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.00/1.99  
% 12.00/1.99  fof(f23,plain,(
% 12.00/1.99    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 12.00/1.99    inference(ennf_transformation,[],[f4])).
% 12.00/1.99  
% 12.00/1.99  fof(f49,plain,(
% 12.00/1.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 12.00/1.99    inference(cnf_transformation,[],[f23])).
% 12.00/1.99  
% 12.00/1.99  fof(f75,plain,(
% 12.00/1.99    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 12.00/1.99    inference(definition_unfolding,[],[f49,f52])).
% 12.00/1.99  
% 12.00/1.99  fof(f2,axiom,(
% 12.00/1.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 12.00/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.00/1.99  
% 12.00/1.99  fof(f47,plain,(
% 12.00/1.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 12.00/1.99    inference(cnf_transformation,[],[f2])).
% 12.00/1.99  
% 12.00/1.99  fof(f74,plain,(
% 12.00/1.99    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 12.00/1.99    inference(definition_unfolding,[],[f47,f52,f52])).
% 12.00/1.99  
% 12.00/1.99  fof(f9,axiom,(
% 12.00/1.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 12.00/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.00/1.99  
% 12.00/1.99  fof(f24,plain,(
% 12.00/1.99    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 12.00/1.99    inference(ennf_transformation,[],[f9])).
% 12.00/1.99  
% 12.00/1.99  fof(f54,plain,(
% 12.00/1.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 12.00/1.99    inference(cnf_transformation,[],[f24])).
% 12.00/1.99  
% 12.00/1.99  fof(f13,axiom,(
% 12.00/1.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 12.00/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.00/1.99  
% 12.00/1.99  fof(f29,plain,(
% 12.00/1.99    ! [X0,X1] : (k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 12.00/1.99    inference(ennf_transformation,[],[f13])).
% 12.00/1.99  
% 12.00/1.99  fof(f58,plain,(
% 12.00/1.99    ( ! [X0,X1] : (k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 12.00/1.99    inference(cnf_transformation,[],[f29])).
% 12.00/1.99  
% 12.00/1.99  fof(f8,axiom,(
% 12.00/1.99    ! [X0] : k2_subset_1(X0) = X0),
% 12.00/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.00/1.99  
% 12.00/1.99  fof(f53,plain,(
% 12.00/1.99    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 12.00/1.99    inference(cnf_transformation,[],[f8])).
% 12.00/1.99  
% 12.00/1.99  fof(f17,axiom,(
% 12.00/1.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 12.00/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.00/1.99  
% 12.00/1.99  fof(f32,plain,(
% 12.00/1.99    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 12.00/1.99    inference(ennf_transformation,[],[f17])).
% 12.00/1.99  
% 12.00/1.99  fof(f33,plain,(
% 12.00/1.99    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 12.00/1.99    inference(flattening,[],[f32])).
% 12.00/1.99  
% 12.00/1.99  fof(f64,plain,(
% 12.00/1.99    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 12.00/1.99    inference(cnf_transformation,[],[f33])).
% 12.00/1.99  
% 12.00/1.99  fof(f18,axiom,(
% 12.00/1.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)))),
% 12.00/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.00/1.99  
% 12.00/1.99  fof(f34,plain,(
% 12.00/1.99    ! [X0] : (! [X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 12.00/1.99    inference(ennf_transformation,[],[f18])).
% 12.00/1.99  
% 12.00/1.99  fof(f65,plain,(
% 12.00/1.99    ( ! [X0,X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 12.00/1.99    inference(cnf_transformation,[],[f34])).
% 12.00/1.99  
% 12.00/1.99  fof(f6,axiom,(
% 12.00/1.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 12.00/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.00/1.99  
% 12.00/1.99  fof(f51,plain,(
% 12.00/1.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 12.00/1.99    inference(cnf_transformation,[],[f6])).
% 12.00/1.99  
% 12.00/1.99  fof(f1,axiom,(
% 12.00/1.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 12.00/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.00/1.99  
% 12.00/1.99  fof(f46,plain,(
% 12.00/1.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 12.00/1.99    inference(cnf_transformation,[],[f1])).
% 12.00/1.99  
% 12.00/1.99  fof(f3,axiom,(
% 12.00/1.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 12.00/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.00/1.99  
% 12.00/1.99  fof(f48,plain,(
% 12.00/1.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 12.00/1.99    inference(cnf_transformation,[],[f3])).
% 12.00/1.99  
% 12.00/1.99  fof(f73,plain,(
% 12.00/1.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 12.00/1.99    inference(definition_unfolding,[],[f48,f52])).
% 12.00/1.99  
% 12.00/1.99  fof(f72,plain,(
% 12.00/1.99    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)),
% 12.00/1.99    inference(cnf_transformation,[],[f45])).
% 12.00/1.99  
% 12.00/1.99  fof(f63,plain,(
% 12.00/1.99    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 12.00/1.99    inference(cnf_transformation,[],[f31])).
% 12.00/1.99  
% 12.00/1.99  fof(f68,plain,(
% 12.00/1.99    v2_pre_topc(sK0)),
% 12.00/1.99    inference(cnf_transformation,[],[f45])).
% 12.00/1.99  
% 12.00/1.99  cnf(c_23,negated_conjecture,
% 12.00/1.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 12.00/1.99      inference(cnf_transformation,[],[f70]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_807,plain,
% 12.00/1.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 12.00/1.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_14,plain,
% 12.00/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 12.00/1.99      inference(cnf_transformation,[],[f60]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_816,plain,
% 12.00/1.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 12.00/1.99      | r1_tarski(X0,X1) = iProver_top ),
% 12.00/1.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_1879,plain,
% 12.00/1.99      ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
% 12.00/1.99      inference(superposition,[status(thm)],[c_807,c_816]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_10,plain,
% 12.00/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 12.00/1.99      | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 12.00/1.99      inference(cnf_transformation,[],[f57]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_13,plain,
% 12.00/1.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 12.00/1.99      inference(cnf_transformation,[],[f61]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_153,plain,
% 12.00/1.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 12.00/1.99      inference(prop_impl,[status(thm)],[c_13]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_154,plain,
% 12.00/1.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 12.00/1.99      inference(renaming,[status(thm)],[c_153]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_198,plain,
% 12.00/1.99      ( ~ r1_tarski(X0,X1) | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 12.00/1.99      inference(bin_hyper_res,[status(thm)],[c_10,c_154]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_801,plain,
% 12.00/1.99      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
% 12.00/1.99      | r1_tarski(X1,X0) != iProver_top ),
% 12.00/1.99      inference(predicate_to_equality,[status(thm)],[c_198]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_14828,plain,
% 12.00/1.99      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
% 12.00/1.99      inference(superposition,[status(thm)],[c_1879,c_801]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_22,negated_conjecture,
% 12.00/1.99      ( v4_pre_topc(sK1,sK0)
% 12.00/1.99      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 12.00/1.99      inference(cnf_transformation,[],[f71]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_808,plain,
% 12.00/1.99      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 12.00/1.99      | v4_pre_topc(sK1,sK0) = iProver_top ),
% 12.00/1.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_16,plain,
% 12.00/1.99      ( ~ v4_pre_topc(X0,X1)
% 12.00/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 12.00/1.99      | ~ l1_pre_topc(X1)
% 12.00/1.99      | k2_pre_topc(X1,X0) = X0 ),
% 12.00/1.99      inference(cnf_transformation,[],[f62]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_814,plain,
% 12.00/1.99      ( k2_pre_topc(X0,X1) = X1
% 12.00/1.99      | v4_pre_topc(X1,X0) != iProver_top
% 12.00/1.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 12.00/1.99      | l1_pre_topc(X0) != iProver_top ),
% 12.00/1.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_7438,plain,
% 12.00/1.99      ( k2_pre_topc(sK0,sK1) = sK1
% 12.00/1.99      | v4_pre_topc(sK1,sK0) != iProver_top
% 12.00/1.99      | l1_pre_topc(sK0) != iProver_top ),
% 12.00/1.99      inference(superposition,[status(thm)],[c_807,c_814]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_24,negated_conjecture,
% 12.00/1.99      ( l1_pre_topc(sK0) ),
% 12.00/1.99      inference(cnf_transformation,[],[f69]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_27,plain,
% 12.00/1.99      ( l1_pre_topc(sK0) = iProver_top ),
% 12.00/1.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_7866,plain,
% 12.00/1.99      ( v4_pre_topc(sK1,sK0) != iProver_top
% 12.00/1.99      | k2_pre_topc(sK0,sK1) = sK1 ),
% 12.00/1.99      inference(global_propositional_subsumption,
% 12.00/1.99                [status(thm)],
% 12.00/1.99                [c_7438,c_27]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_7867,plain,
% 12.00/1.99      ( k2_pre_topc(sK0,sK1) = sK1
% 12.00/1.99      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 12.00/1.99      inference(renaming,[status(thm)],[c_7866]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_7872,plain,
% 12.00/1.99      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 12.00/1.99      | k2_pre_topc(sK0,sK1) = sK1 ),
% 12.00/1.99      inference(superposition,[status(thm)],[c_808,c_7867]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_15920,plain,
% 12.00/1.99      ( k2_pre_topc(sK0,sK1) = sK1
% 12.00/1.99      | k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 12.00/1.99      inference(superposition,[status(thm)],[c_14828,c_7872]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_20,plain,
% 12.00/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 12.00/1.99      | ~ l1_pre_topc(X1)
% 12.00/1.99      | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
% 12.00/1.99      inference(cnf_transformation,[],[f67]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_810,plain,
% 12.00/1.99      ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
% 12.00/1.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 12.00/1.99      | l1_pre_topc(X0) != iProver_top ),
% 12.00/1.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_7255,plain,
% 12.00/1.99      ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1)
% 12.00/1.99      | l1_pre_topc(sK0) != iProver_top ),
% 12.00/1.99      inference(superposition,[status(thm)],[c_807,c_810]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_1094,plain,
% 12.00/1.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 12.00/1.99      | ~ l1_pre_topc(sK0)
% 12.00/1.99      | k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
% 12.00/1.99      inference(instantiation,[status(thm)],[c_20]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_7746,plain,
% 12.00/1.99      ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
% 12.00/1.99      inference(global_propositional_subsumption,
% 12.00/1.99                [status(thm)],
% 12.00/1.99                [c_7255,c_24,c_23,c_1094]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_15922,plain,
% 12.00/1.99      ( k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
% 12.00/1.99      inference(superposition,[status(thm)],[c_14828,c_7746]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_4,plain,
% 12.00/1.99      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 12.00/1.99      inference(cnf_transformation,[],[f50]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_818,plain,
% 12.00/1.99      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 12.00/1.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_817,plain,
% 12.00/1.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 12.00/1.99      | r1_tarski(X0,X1) != iProver_top ),
% 12.00/1.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_9,plain,
% 12.00/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 12.00/1.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 12.00/1.99      | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
% 12.00/1.99      inference(cnf_transformation,[],[f56]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_197,plain,
% 12.00/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 12.00/1.99      | ~ r1_tarski(X2,X1)
% 12.00/1.99      | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
% 12.00/1.99      inference(bin_hyper_res,[status(thm)],[c_9,c_154]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_802,plain,
% 12.00/1.99      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
% 12.00/1.99      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
% 12.00/1.99      | r1_tarski(X1,X0) != iProver_top ),
% 12.00/1.99      inference(predicate_to_equality,[status(thm)],[c_197]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_37281,plain,
% 12.00/1.99      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
% 12.00/1.99      | r1_tarski(X2,X0) != iProver_top
% 12.00/1.99      | r1_tarski(X1,X0) != iProver_top ),
% 12.00/1.99      inference(superposition,[status(thm)],[c_817,c_802]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_41959,plain,
% 12.00/1.99      ( k4_subset_1(X0,k4_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X1),X2)
% 12.00/1.99      | r1_tarski(X2,X0) != iProver_top ),
% 12.00/1.99      inference(superposition,[status(thm)],[c_818,c_37281]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_42168,plain,
% 12.00/1.99      ( k4_subset_1(X0,k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
% 12.00/1.99      inference(superposition,[status(thm)],[c_818,c_41959]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_43731,plain,
% 12.00/1.99      ( k2_xboole_0(k4_xboole_0(sK1,k2_tops_1(sK0,sK1)),k4_xboole_0(sK1,X0)) = k4_subset_1(sK1,k1_tops_1(sK0,sK1),k4_xboole_0(sK1,X0)) ),
% 12.00/1.99      inference(superposition,[status(thm)],[c_15922,c_42168]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_43838,plain,
% 12.00/1.99      ( k4_subset_1(sK1,k1_tops_1(sK0,sK1),k4_xboole_0(sK1,X0)) = k2_xboole_0(k1_tops_1(sK0,sK1),k4_xboole_0(sK1,X0)) ),
% 12.00/1.99      inference(light_normalisation,[status(thm)],[c_43731,c_15922]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_44272,plain,
% 12.00/1.99      ( k2_pre_topc(sK0,sK1) = sK1
% 12.00/1.99      | k2_xboole_0(k1_tops_1(sK0,sK1),k4_xboole_0(sK1,k1_tops_1(sK0,sK1))) = k4_subset_1(sK1,k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) ),
% 12.00/1.99      inference(superposition,[status(thm)],[c_15920,c_43838]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_12,plain,
% 12.00/1.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
% 12.00/1.99      inference(cnf_transformation,[],[f76]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_16237,plain,
% 12.00/1.99      ( k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
% 12.00/1.99      inference(superposition,[status(thm)],[c_15922,c_12]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_19,plain,
% 12.00/1.99      ( ~ v4_pre_topc(X0,X1)
% 12.00/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 12.00/1.99      | r1_tarski(k2_tops_1(X1,X0),X0)
% 12.00/1.99      | ~ l1_pre_topc(X1) ),
% 12.00/1.99      inference(cnf_transformation,[],[f66]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_811,plain,
% 12.00/1.99      ( v4_pre_topc(X0,X1) != iProver_top
% 12.00/1.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 12.00/1.99      | r1_tarski(k2_tops_1(X1,X0),X0) = iProver_top
% 12.00/1.99      | l1_pre_topc(X1) != iProver_top ),
% 12.00/1.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_1210,plain,
% 12.00/1.99      ( v4_pre_topc(sK1,sK0) != iProver_top
% 12.00/1.99      | r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top
% 12.00/1.99      | l1_pre_topc(sK0) != iProver_top ),
% 12.00/1.99      inference(superposition,[status(thm)],[c_807,c_811]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_1558,plain,
% 12.00/1.99      ( r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top
% 12.00/1.99      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 12.00/1.99      inference(global_propositional_subsumption,
% 12.00/1.99                [status(thm)],
% 12.00/1.99                [c_1210,c_27]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_1559,plain,
% 12.00/1.99      ( v4_pre_topc(sK1,sK0) != iProver_top
% 12.00/1.99      | r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top ),
% 12.00/1.99      inference(renaming,[status(thm)],[c_1558]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_3,plain,
% 12.00/1.99      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 12.00/1.99      inference(cnf_transformation,[],[f75]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_819,plain,
% 12.00/1.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
% 12.00/1.99      | r1_tarski(X0,X1) != iProver_top ),
% 12.00/1.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_2,plain,
% 12.00/1.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 12.00/1.99      inference(cnf_transformation,[],[f74]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_836,plain,
% 12.00/1.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X1,X0)) ),
% 12.00/1.99      inference(light_normalisation,[status(thm)],[c_2,c_12]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_854,plain,
% 12.00/1.99      ( k1_setfam_1(k2_tarski(X0,X1)) = X1
% 12.00/1.99      | r1_tarski(X1,X0) != iProver_top ),
% 12.00/1.99      inference(demodulation,[status(thm)],[c_819,c_836]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_2476,plain,
% 12.00/1.99      ( k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k2_tops_1(sK0,sK1)
% 12.00/1.99      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 12.00/1.99      inference(superposition,[status(thm)],[c_1559,c_854]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_2651,plain,
% 12.00/1.99      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 12.00/1.99      | k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k2_tops_1(sK0,sK1) ),
% 12.00/1.99      inference(superposition,[status(thm)],[c_808,c_2476]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_15921,plain,
% 12.00/1.99      ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 12.00/1.99      | k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k2_tops_1(sK0,sK1) ),
% 12.00/1.99      inference(superposition,[status(thm)],[c_14828,c_2651]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_16884,plain,
% 12.00/1.99      ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 12.00/1.99      inference(superposition,[status(thm)],[c_16237,c_15921]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_7,plain,
% 12.00/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 12.00/1.99      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 12.00/1.99      inference(cnf_transformation,[],[f54]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_195,plain,
% 12.00/1.99      ( ~ r1_tarski(X0,X1) | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 12.00/1.99      inference(bin_hyper_res,[status(thm)],[c_7,c_154]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_804,plain,
% 12.00/1.99      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
% 12.00/1.99      | r1_tarski(X1,X0) != iProver_top ),
% 12.00/1.99      inference(predicate_to_equality,[status(thm)],[c_195]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_12887,plain,
% 12.00/1.99      ( k3_subset_1(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 12.00/1.99      inference(superposition,[status(thm)],[c_818,c_804]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_12947,plain,
% 12.00/1.99      ( k3_subset_1(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X1,X0)) ),
% 12.00/1.99      inference(light_normalisation,[status(thm)],[c_12887,c_836]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_16224,plain,
% 12.00/1.99      ( k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),sK1)) = k3_subset_1(sK1,k1_tops_1(sK0,sK1)) ),
% 12.00/1.99      inference(superposition,[status(thm)],[c_15922,c_12947]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_16236,plain,
% 12.00/1.99      ( k1_setfam_1(k2_tarski(k2_tops_1(sK0,sK1),sK1)) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
% 12.00/1.99      inference(superposition,[status(thm)],[c_15922,c_836]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_16268,plain,
% 12.00/1.99      ( k3_subset_1(sK1,k1_tops_1(sK0,sK1)) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
% 12.00/1.99      inference(light_normalisation,[status(thm)],[c_16224,c_16236]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_22483,plain,
% 12.00/1.99      ( k3_subset_1(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 12.00/1.99      inference(light_normalisation,[status(thm)],[c_16268,c_16884]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_16238,plain,
% 12.00/1.99      ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
% 12.00/1.99      inference(superposition,[status(thm)],[c_15922,c_818]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_11,plain,
% 12.00/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 12.00/1.99      | k4_subset_1(X1,X0,k3_subset_1(X1,X0)) = k2_subset_1(X1) ),
% 12.00/1.99      inference(cnf_transformation,[],[f58]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_199,plain,
% 12.00/1.99      ( ~ r1_tarski(X0,X1)
% 12.00/1.99      | k4_subset_1(X1,X0,k3_subset_1(X1,X0)) = k2_subset_1(X1) ),
% 12.00/1.99      inference(bin_hyper_res,[status(thm)],[c_11,c_154]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_800,plain,
% 12.00/1.99      ( k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = k2_subset_1(X0)
% 12.00/1.99      | r1_tarski(X1,X0) != iProver_top ),
% 12.00/1.99      inference(predicate_to_equality,[status(thm)],[c_199]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_6,plain,
% 12.00/1.99      ( k2_subset_1(X0) = X0 ),
% 12.00/1.99      inference(cnf_transformation,[],[f53]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_867,plain,
% 12.00/1.99      ( k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = X0
% 12.00/1.99      | r1_tarski(X1,X0) != iProver_top ),
% 12.00/1.99      inference(light_normalisation,[status(thm)],[c_800,c_6]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_17268,plain,
% 12.00/1.99      ( k4_subset_1(sK1,k1_tops_1(sK0,sK1),k3_subset_1(sK1,k1_tops_1(sK0,sK1))) = sK1 ),
% 12.00/1.99      inference(superposition,[status(thm)],[c_16238,c_867]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_22485,plain,
% 12.00/1.99      ( k4_subset_1(sK1,k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) = sK1 ),
% 12.00/1.99      inference(demodulation,[status(thm)],[c_22483,c_17268]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_17,plain,
% 12.00/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 12.00/1.99      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 12.00/1.99      | ~ l1_pre_topc(X1) ),
% 12.00/1.99      inference(cnf_transformation,[],[f64]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_813,plain,
% 12.00/1.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 12.00/1.99      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 12.00/1.99      | l1_pre_topc(X1) != iProver_top ),
% 12.00/1.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_2077,plain,
% 12.00/1.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 12.00/1.99      | r1_tarski(k2_tops_1(X1,X0),u1_struct_0(X1)) = iProver_top
% 12.00/1.99      | l1_pre_topc(X1) != iProver_top ),
% 12.00/1.99      inference(superposition,[status(thm)],[c_813,c_816]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_41963,plain,
% 12.00/1.99      ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k2_xboole_0(sK1,X0)
% 12.00/1.99      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
% 12.00/1.99      inference(superposition,[status(thm)],[c_1879,c_37281]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_42483,plain,
% 12.00/1.99      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0))
% 12.00/1.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 12.00/1.99      | l1_pre_topc(sK0) != iProver_top ),
% 12.00/1.99      inference(superposition,[status(thm)],[c_2077,c_41963]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_43181,plain,
% 12.00/1.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 12.00/1.99      | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0)) ),
% 12.00/1.99      inference(global_propositional_subsumption,
% 12.00/1.99                [status(thm)],
% 12.00/1.99                [c_42483,c_27]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_43182,plain,
% 12.00/1.99      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0))
% 12.00/1.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 12.00/1.99      inference(renaming,[status(thm)],[c_43181]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_43192,plain,
% 12.00/1.99      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
% 12.00/1.99      inference(superposition,[status(thm)],[c_807,c_43182]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_18,plain,
% 12.00/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 12.00/1.99      | ~ l1_pre_topc(X1)
% 12.00/1.99      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
% 12.00/1.99      inference(cnf_transformation,[],[f65]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_812,plain,
% 12.00/1.99      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
% 12.00/1.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 12.00/1.99      | l1_pre_topc(X0) != iProver_top ),
% 12.00/1.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_7407,plain,
% 12.00/1.99      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
% 12.00/1.99      | l1_pre_topc(sK0) != iProver_top ),
% 12.00/1.99      inference(superposition,[status(thm)],[c_807,c_812]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_1091,plain,
% 12.00/1.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 12.00/1.99      | ~ l1_pre_topc(sK0)
% 12.00/1.99      | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 12.00/1.99      inference(instantiation,[status(thm)],[c_18]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_7750,plain,
% 12.00/1.99      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 12.00/1.99      inference(global_propositional_subsumption,
% 12.00/1.99                [status(thm)],
% 12.00/1.99                [c_7407,c_24,c_23,c_1091]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_43197,plain,
% 12.00/1.99      ( k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 12.00/1.99      inference(light_normalisation,[status(thm)],[c_43192,c_7750]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_2474,plain,
% 12.00/1.99      ( k1_setfam_1(k2_tarski(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 12.00/1.99      inference(superposition,[status(thm)],[c_818,c_854]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_1539,plain,
% 12.00/1.99      ( k1_setfam_1(k2_tarski(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0))) ),
% 12.00/1.99      inference(superposition,[status(thm)],[c_836,c_12]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_5,plain,
% 12.00/1.99      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 12.00/1.99      inference(cnf_transformation,[],[f51]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_2295,plain,
% 12.00/1.99      ( k2_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),k1_setfam_1(k2_tarski(X1,k4_xboole_0(X1,X0)))) = k2_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),X1) ),
% 12.00/1.99      inference(superposition,[status(thm)],[c_1539,c_5]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_8416,plain,
% 12.00/1.99      ( k2_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),k4_xboole_0(X1,X0)) = k2_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),X1) ),
% 12.00/1.99      inference(demodulation,[status(thm)],[c_2474,c_2295]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_1427,plain,
% 12.00/1.99      ( k1_setfam_1(k2_tarski(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
% 12.00/1.99      inference(superposition,[status(thm)],[c_12,c_12]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_2278,plain,
% 12.00/1.99      ( k2_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),k1_setfam_1(k2_tarski(X0,k4_xboole_0(X0,X1)))) = k2_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
% 12.00/1.99      inference(superposition,[status(thm)],[c_1427,c_5]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_8411,plain,
% 12.00/1.99      ( k2_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),k4_xboole_0(X0,X1)) = k2_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
% 12.00/1.99      inference(demodulation,[status(thm)],[c_2474,c_2278]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_1,plain,
% 12.00/1.99      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 12.00/1.99      inference(cnf_transformation,[],[f46]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_21260,plain,
% 12.00/1.99      ( k2_xboole_0(k4_xboole_0(X0,X1),k1_setfam_1(k2_tarski(X0,X1))) = k2_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
% 12.00/1.99      inference(superposition,[status(thm)],[c_8411,c_1]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_1430,plain,
% 12.00/1.99      ( k2_xboole_0(k4_xboole_0(X0,X1),k1_setfam_1(k2_tarski(X0,X1))) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 12.00/1.99      inference(superposition,[status(thm)],[c_12,c_5]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_21263,plain,
% 12.00/1.99      ( k2_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),X0) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 12.00/1.99      inference(light_normalisation,[status(thm)],[c_21260,c_1430]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_21299,plain,
% 12.00/1.99      ( k2_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 12.00/1.99      inference(superposition,[status(thm)],[c_21263,c_1]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_21580,plain,
% 12.00/1.99      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = k2_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 12.00/1.99      inference(superposition,[status(thm)],[c_2474,c_21299]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_21623,plain,
% 12.00/1.99      ( k2_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),X1) = k2_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 12.00/1.99      inference(light_normalisation,[status(thm)],[c_21580,c_836]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_23200,plain,
% 12.00/1.99      ( k2_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),k4_xboole_0(X1,X0)) = k2_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 12.00/1.99      inference(light_normalisation,[status(thm)],[c_8416,c_21623]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_23226,plain,
% 12.00/1.99      ( k2_xboole_0(k1_setfam_1(k2_tarski(k1_tops_1(sK0,sK1),sK1)),k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k4_xboole_0(sK1,k1_tops_1(sK0,sK1))) ),
% 12.00/1.99      inference(superposition,[status(thm)],[c_16884,c_23200]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_1541,plain,
% 12.00/1.99      ( k1_setfam_1(k2_tarski(X0,X1)) = k1_setfam_1(k2_tarski(X1,X0)) ),
% 12.00/1.99      inference(superposition,[status(thm)],[c_836,c_12]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_0,plain,
% 12.00/1.99      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 12.00/1.99      inference(cnf_transformation,[],[f73]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_839,plain,
% 12.00/1.99      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0))) = k4_xboole_0(X0,X1) ),
% 12.00/1.99      inference(light_normalisation,[status(thm)],[c_0,c_836]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_1763,plain,
% 12.00/1.99      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k4_xboole_0(X0,X1) ),
% 12.00/1.99      inference(superposition,[status(thm)],[c_1541,c_839]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_8444,plain,
% 12.00/1.99      ( k5_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 12.00/1.99      inference(superposition,[status(thm)],[c_2474,c_1763]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_8453,plain,
% 12.00/1.99      ( k5_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X1,X0)) ),
% 12.00/1.99      inference(light_normalisation,[status(thm)],[c_8444,c_836]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_9659,plain,
% 12.00/1.99      ( k1_setfam_1(k2_tarski(k4_xboole_0(X0,X1),X0)) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
% 12.00/1.99      inference(superposition,[status(thm)],[c_12,c_8453]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_9683,plain,
% 12.00/1.99      ( k1_setfam_1(k2_tarski(k4_xboole_0(X0,X1),X0)) = k4_xboole_0(X0,X1) ),
% 12.00/1.99      inference(light_normalisation,[status(thm)],[c_9659,c_1763]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_16231,plain,
% 12.00/1.99      ( k1_setfam_1(k2_tarski(k1_tops_1(sK0,sK1),sK1)) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
% 12.00/1.99      inference(superposition,[status(thm)],[c_15922,c_9683]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_16257,plain,
% 12.00/1.99      ( k1_setfam_1(k2_tarski(k1_tops_1(sK0,sK1),sK1)) = k1_tops_1(sK0,sK1) ),
% 12.00/1.99      inference(light_normalisation,[status(thm)],[c_16231,c_15922]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_23241,plain,
% 12.00/1.99      ( k2_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
% 12.00/1.99      inference(light_normalisation,
% 12.00/1.99                [status(thm)],
% 12.00/1.99                [c_23226,c_16257,c_16884]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_43384,plain,
% 12.00/1.99      ( k2_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 12.00/1.99      inference(demodulation,[status(thm)],[c_43197,c_23241]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_44279,plain,
% 12.00/1.99      ( k2_pre_topc(sK0,sK1) = sK1 ),
% 12.00/1.99      inference(light_normalisation,
% 12.00/1.99                [status(thm)],
% 12.00/1.99                [c_44272,c_16884,c_22485,c_43384]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_21,negated_conjecture,
% 12.00/1.99      ( ~ v4_pre_topc(sK1,sK0)
% 12.00/1.99      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
% 12.00/1.99      inference(cnf_transformation,[],[f72]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_809,plain,
% 12.00/1.99      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
% 12.00/1.99      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 12.00/1.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_15904,plain,
% 12.00/1.99      ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
% 12.00/1.99      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 12.00/1.99      inference(demodulation,[status(thm)],[c_14828,c_809]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_15,plain,
% 12.00/1.99      ( v4_pre_topc(X0,X1)
% 12.00/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 12.00/1.99      | ~ l1_pre_topc(X1)
% 12.00/1.99      | ~ v2_pre_topc(X1)
% 12.00/1.99      | k2_pre_topc(X1,X0) != X0 ),
% 12.00/1.99      inference(cnf_transformation,[],[f63]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_1088,plain,
% 12.00/1.99      ( v4_pre_topc(sK1,sK0)
% 12.00/1.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 12.00/1.99      | ~ l1_pre_topc(sK0)
% 12.00/1.99      | ~ v2_pre_topc(sK0)
% 12.00/1.99      | k2_pre_topc(sK0,sK1) != sK1 ),
% 12.00/1.99      inference(instantiation,[status(thm)],[c_15]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_1089,plain,
% 12.00/1.99      ( k2_pre_topc(sK0,sK1) != sK1
% 12.00/1.99      | v4_pre_topc(sK1,sK0) = iProver_top
% 12.00/1.99      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 12.00/1.99      | l1_pre_topc(sK0) != iProver_top
% 12.00/1.99      | v2_pre_topc(sK0) != iProver_top ),
% 12.00/1.99      inference(predicate_to_equality,[status(thm)],[c_1088]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_28,plain,
% 12.00/1.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 12.00/1.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_25,negated_conjecture,
% 12.00/1.99      ( v2_pre_topc(sK0) ),
% 12.00/1.99      inference(cnf_transformation,[],[f68]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(c_26,plain,
% 12.00/1.99      ( v2_pre_topc(sK0) = iProver_top ),
% 12.00/1.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 12.00/1.99  
% 12.00/1.99  cnf(contradiction,plain,
% 12.00/1.99      ( $false ),
% 12.00/1.99      inference(minisat,
% 12.00/1.99                [status(thm)],
% 12.00/1.99                [c_44279,c_16884,c_15904,c_1089,c_28,c_27,c_26]) ).
% 12.00/1.99  
% 12.00/1.99  
% 12.00/1.99  % SZS output end CNFRefutation for theBenchmark.p
% 12.00/1.99  
% 12.00/1.99  ------                               Statistics
% 12.00/1.99  
% 12.00/1.99  ------ Selected
% 12.00/1.99  
% 12.00/1.99  total_time:                             1.366
% 12.00/1.99  
%------------------------------------------------------------------------------
