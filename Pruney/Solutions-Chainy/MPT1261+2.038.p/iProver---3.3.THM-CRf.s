%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:14:30 EST 2020

% Result     : Theorem 7.98s
% Output     : CNFRefutation 7.98s
% Verified   : 
% Statistics : Number of formulae       :  160 (6212 expanded)
%              Number of clauses        :   91 (1774 expanded)
%              Number of leaves         :   20 (1390 expanded)
%              Depth                    :   30
%              Number of atoms          :  389 (25467 expanded)
%              Number of equality atoms :  202 (8332 expanded)
%              Maximal formula depth    :    9 (   4 average)
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

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

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
    inference(nnf_transformation,[],[f39])).

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

fof(f66,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f44])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f69,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f45,f55])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f53,f69])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f65,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f12])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f50,f69])).

fof(f67,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f44])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
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
    inference(flattening,[],[f29])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f5,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f8,axiom,(
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
    inference(ennf_transformation,[],[f8])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f24])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k2_tarski(X1,X2)) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f52,f48])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f70,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) ),
    inference(definition_unfolding,[],[f46,f48,f48,f48])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) != X1
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f68,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f64,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_698,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2))) = k7_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_710,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X2,X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2258,plain,
    ( k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0))) = k7_subset_1(u1_struct_0(sK0),sK1,X0) ),
    inference(superposition,[status(thm)],[c_698,c_710])).

cnf(c_14,plain,
    ( r1_tarski(k1_tops_1(X0,X1),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_702,plain,
    ( r1_tarski(k1_tops_1(X0,X1),X1) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2048,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_698,c_702])).

cnf(c_19,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_22,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_23,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_890,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_891,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_890])).

cnf(c_2935,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2048,c_22,c_23,c_891])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_708,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_713,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k3_subset_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1728,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k3_subset_1(X0,X1)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_708,c_713])).

cnf(c_2940,plain,
    ( k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1)))) = k3_subset_1(sK1,k1_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_2935,c_1728])).

cnf(c_3177,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k3_subset_1(sK1,k1_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_2258,c_2940])).

cnf(c_17,negated_conjecture,
    ( v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_699,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3180,plain,
    ( k3_subset_1(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3177,c_699])).

cnf(c_10,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_706,plain,
    ( k2_pre_topc(X0,X1) = X1
    | v4_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_6561,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | v4_pre_topc(sK1,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_698,c_706])).

cnf(c_6647,plain,
    ( v4_pre_topc(sK1,sK0) != iProver_top
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6561,c_22])).

cnf(c_6648,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_6647])).

cnf(c_6653,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k3_subset_1(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_3180,c_6648])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X0,k3_subset_1(X1,X0)) = k2_subset_1(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_709,plain,
    ( k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = k2_subset_1(X0)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_738,plain,
    ( k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = X0
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_709,c_2])).

cnf(c_1454,plain,
    ( k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = X0
    | r1_tarski(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_708,c_738])).

cnf(c_2941,plain,
    ( k4_subset_1(sK1,k1_tops_1(sK0,sK1),k3_subset_1(sK1,k1_tops_1(sK0,sK1))) = sK1 ),
    inference(superposition,[status(thm)],[c_2935,c_1454])).

cnf(c_7685,plain,
    ( k4_subset_1(sK1,k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) = sK1
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_6653,c_2941])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_712,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_7683,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6653,c_712])).

cnf(c_1096,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1097,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1) != iProver_top
    | m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1096])).

cnf(c_9840,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7683,c_22,c_23,c_891,c_1097])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X0,X2) = k3_tarski(k2_tarski(X0,X2)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_711,plain,
    ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_6515,plain,
    ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
    | r1_tarski(X1,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_708,c_711])).

cnf(c_13749,plain,
    ( k4_subset_1(sK1,X0,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(X0,k2_tops_1(sK0,sK1)))
    | k2_pre_topc(sK0,sK1) = sK1
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_9840,c_6515])).

cnf(c_16166,plain,
    ( k4_subset_1(sK1,k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)))
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_2935,c_13749])).

cnf(c_17109,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k3_tarski(k2_tarski(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))) = sK1 ),
    inference(superposition,[status(thm)],[c_7685,c_16166])).

cnf(c_0,plain,
    ( k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_17262,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k3_tarski(k2_tarski(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))) = k3_tarski(k2_tarski(k1_tops_1(sK0,sK1),sK1)) ),
    inference(superposition,[status(thm)],[c_17109,c_0])).

cnf(c_18070,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k3_tarski(k2_tarski(k1_tops_1(sK0,sK1),sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_17262,c_17109])).

cnf(c_1,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1020,plain,
    ( k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X1,X0)))) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(superposition,[status(thm)],[c_1,c_0])).

cnf(c_1157,plain,
    ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X0)) ),
    inference(superposition,[status(thm)],[c_0,c_1020])).

cnf(c_2027,plain,
    ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(k3_tarski(k2_tarski(X1,X0)),X1)) ),
    inference(superposition,[status(thm)],[c_1,c_1157])).

cnf(c_2233,plain,
    ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X0)) = k3_tarski(k2_tarski(k3_tarski(k2_tarski(X1,X0)),X1)) ),
    inference(superposition,[status(thm)],[c_2027,c_1157])).

cnf(c_4301,plain,
    ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X0)) = k3_tarski(k2_tarski(X1,k3_tarski(k2_tarski(X1,X0)))) ),
    inference(superposition,[status(thm)],[c_1,c_2233])).

cnf(c_4403,plain,
    ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X0)) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_4301,c_0])).

cnf(c_4499,plain,
    ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X1)) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(superposition,[status(thm)],[c_1,c_4403])).

cnf(c_18058,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k3_tarski(k2_tarski(k3_tarski(k2_tarski(k1_tops_1(sK0,sK1),sK1)),k2_tops_1(sK0,sK1))) = k3_tarski(k2_tarski(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))) ),
    inference(superposition,[status(thm)],[c_17262,c_4499])).

cnf(c_24319,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k3_tarski(k2_tarski(k3_tarski(k2_tarski(k1_tops_1(sK0,sK1),sK1)),k3_tarski(k2_tarski(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))))) = k3_tarski(k2_tarski(k3_tarski(k2_tarski(k1_tops_1(sK0,sK1),sK1)),k2_tops_1(sK0,sK1))) ),
    inference(superposition,[status(thm)],[c_18058,c_0])).

cnf(c_24388,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k3_tarski(k2_tarski(k3_tarski(k2_tarski(k1_tops_1(sK0,sK1),sK1)),k2_tops_1(sK0,sK1))) = k3_tarski(k2_tarski(k3_tarski(k2_tarski(k1_tops_1(sK0,sK1),sK1)),sK1)) ),
    inference(superposition,[status(thm)],[c_17109,c_24319])).

cnf(c_24463,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k3_tarski(k2_tarski(k3_tarski(k2_tarski(k1_tops_1(sK0,sK1),sK1)),k2_tops_1(sK0,sK1))) = k3_tarski(k2_tarski(k1_tops_1(sK0,sK1),sK1)) ),
    inference(demodulation,[status(thm)],[c_24388,c_4499])).

cnf(c_28991,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k3_tarski(k2_tarski(k1_tops_1(sK0,sK1),sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
    inference(superposition,[status(thm)],[c_18070,c_24463])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_705,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_6518,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k3_tarski(k2_tarski(sK1,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_698,c_711])).

cnf(c_6659,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_705,c_6518])).

cnf(c_7175,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6659,c_22])).

cnf(c_7176,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_7175])).

cnf(c_7186,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
    inference(superposition,[status(thm)],[c_698,c_7176])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_701,plain,
    ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1154,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_698,c_701])).

cnf(c_970,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1617,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1154,c_19,c_18,c_970])).

cnf(c_7188,plain,
    ( k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k2_pre_topc(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_7186,c_1617])).

cnf(c_29050,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k3_tarski(k2_tarski(k1_tops_1(sK0,sK1),sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_28991,c_7188])).

cnf(c_29494,plain,
    ( k2_pre_topc(sK0,sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_29050,c_18070])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_703,plain,
    ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3300,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_698,c_703])).

cnf(c_973,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_3976,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3300,c_19,c_18,c_973])).

cnf(c_29509,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_29494,c_3976])).

cnf(c_9,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | k2_pre_topc(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_967,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | k2_pre_topc(sK0,sK1) != sK1 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_16,negated_conjecture,
    ( ~ v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_20,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f64])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_29509,c_29494,c_967,c_16,c_18,c_19,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:30:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 7.98/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.98/1.49  
% 7.98/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.98/1.49  
% 7.98/1.49  ------  iProver source info
% 7.98/1.49  
% 7.98/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.98/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.98/1.49  git: non_committed_changes: false
% 7.98/1.49  git: last_make_outside_of_git: false
% 7.98/1.49  
% 7.98/1.49  ------ 
% 7.98/1.49  ------ Parsing...
% 7.98/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.98/1.49  
% 7.98/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 7.98/1.49  
% 7.98/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.98/1.49  
% 7.98/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.98/1.49  ------ Proving...
% 7.98/1.49  ------ Problem Properties 
% 7.98/1.49  
% 7.98/1.49  
% 7.98/1.49  clauses                                 21
% 7.98/1.49  conjectures                             5
% 7.98/1.49  EPR                                     2
% 7.98/1.49  Horn                                    20
% 7.98/1.49  unary                                   6
% 7.98/1.49  binary                                  7
% 7.98/1.49  lits                                    48
% 7.98/1.49  lits eq                                 13
% 7.98/1.49  fd_pure                                 0
% 7.98/1.49  fd_pseudo                               0
% 7.98/1.49  fd_cond                                 0
% 7.98/1.49  fd_pseudo_cond                          0
% 7.98/1.49  AC symbols                              0
% 7.98/1.49  
% 7.98/1.49  ------ Input Options Time Limit: Unbounded
% 7.98/1.49  
% 7.98/1.49  
% 7.98/1.49  ------ 
% 7.98/1.49  Current options:
% 7.98/1.49  ------ 
% 7.98/1.49  
% 7.98/1.49  
% 7.98/1.49  
% 7.98/1.49  
% 7.98/1.49  ------ Proving...
% 7.98/1.49  
% 7.98/1.49  
% 7.98/1.49  % SZS status Theorem for theBenchmark.p
% 7.98/1.49  
% 7.98/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.98/1.49  
% 7.98/1.49  fof(f19,conjecture,(
% 7.98/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 7.98/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.98/1.49  
% 7.98/1.49  fof(f20,negated_conjecture,(
% 7.98/1.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 7.98/1.49    inference(negated_conjecture,[],[f19])).
% 7.98/1.49  
% 7.98/1.49  fof(f38,plain,(
% 7.98/1.49    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 7.98/1.49    inference(ennf_transformation,[],[f20])).
% 7.98/1.49  
% 7.98/1.49  fof(f39,plain,(
% 7.98/1.49    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 7.98/1.49    inference(flattening,[],[f38])).
% 7.98/1.49  
% 7.98/1.49  fof(f40,plain,(
% 7.98/1.49    ? [X0] : (? [X1] : (((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 7.98/1.49    inference(nnf_transformation,[],[f39])).
% 7.98/1.49  
% 7.98/1.49  fof(f41,plain,(
% 7.98/1.49    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 7.98/1.49    inference(flattening,[],[f40])).
% 7.98/1.49  
% 7.98/1.49  fof(f43,plain,(
% 7.98/1.49    ( ! [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) != k2_tops_1(X0,sK1) | ~v4_pre_topc(sK1,X0)) & (k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) = k2_tops_1(X0,sK1) | v4_pre_topc(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 7.98/1.49    introduced(choice_axiom,[])).
% 7.98/1.49  
% 7.98/1.49  fof(f42,plain,(
% 7.98/1.49    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) != k2_tops_1(sK0,X1) | ~v4_pre_topc(X1,sK0)) & (k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) = k2_tops_1(sK0,X1) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 7.98/1.49    introduced(choice_axiom,[])).
% 7.98/1.49  
% 7.98/1.49  fof(f44,plain,(
% 7.98/1.49    ((k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)) & (k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 7.98/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f41,f43,f42])).
% 7.98/1.49  
% 7.98/1.49  fof(f66,plain,(
% 7.98/1.49    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 7.98/1.49    inference(cnf_transformation,[],[f44])).
% 7.98/1.49  
% 7.98/1.49  fof(f9,axiom,(
% 7.98/1.49    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 7.98/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.98/1.49  
% 7.98/1.49  fof(f26,plain,(
% 7.98/1.49    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.98/1.49    inference(ennf_transformation,[],[f9])).
% 7.98/1.49  
% 7.98/1.49  fof(f53,plain,(
% 7.98/1.49    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.98/1.49    inference(cnf_transformation,[],[f26])).
% 7.98/1.49  
% 7.98/1.49  fof(f1,axiom,(
% 7.98/1.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 7.98/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.98/1.49  
% 7.98/1.49  fof(f45,plain,(
% 7.98/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 7.98/1.49    inference(cnf_transformation,[],[f1])).
% 7.98/1.49  
% 7.98/1.49  fof(f11,axiom,(
% 7.98/1.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 7.98/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.98/1.49  
% 7.98/1.49  fof(f55,plain,(
% 7.98/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 7.98/1.49    inference(cnf_transformation,[],[f11])).
% 7.98/1.49  
% 7.98/1.49  fof(f69,plain,(
% 7.98/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 7.98/1.49    inference(definition_unfolding,[],[f45,f55])).
% 7.98/1.49  
% 7.98/1.49  fof(f73,plain,(
% 7.98/1.49    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.98/1.49    inference(definition_unfolding,[],[f53,f69])).
% 7.98/1.49  
% 7.98/1.49  fof(f17,axiom,(
% 7.98/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 7.98/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.98/1.49  
% 7.98/1.49  fof(f36,plain,(
% 7.98/1.49    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.98/1.49    inference(ennf_transformation,[],[f17])).
% 7.98/1.49  
% 7.98/1.49  fof(f62,plain,(
% 7.98/1.49    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.98/1.49    inference(cnf_transformation,[],[f36])).
% 7.98/1.49  
% 7.98/1.49  fof(f65,plain,(
% 7.98/1.49    l1_pre_topc(sK0)),
% 7.98/1.49    inference(cnf_transformation,[],[f44])).
% 7.98/1.49  
% 7.98/1.49  fof(f12,axiom,(
% 7.98/1.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.98/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.98/1.49  
% 7.98/1.49  fof(f21,plain,(
% 7.98/1.49    ! [X0,X1] : (r1_tarski(X0,X1) => m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 7.98/1.49    inference(unused_predicate_definition_removal,[],[f12])).
% 7.98/1.49  
% 7.98/1.49  fof(f28,plain,(
% 7.98/1.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 7.98/1.49    inference(ennf_transformation,[],[f21])).
% 7.98/1.49  
% 7.98/1.49  fof(f56,plain,(
% 7.98/1.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.98/1.49    inference(cnf_transformation,[],[f28])).
% 7.98/1.49  
% 7.98/1.49  fof(f6,axiom,(
% 7.98/1.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 7.98/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.98/1.49  
% 7.98/1.49  fof(f22,plain,(
% 7.98/1.49    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.98/1.49    inference(ennf_transformation,[],[f6])).
% 7.98/1.49  
% 7.98/1.49  fof(f50,plain,(
% 7.98/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.98/1.49    inference(cnf_transformation,[],[f22])).
% 7.98/1.49  
% 7.98/1.49  fof(f71,plain,(
% 7.98/1.49    ( ! [X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.98/1.49    inference(definition_unfolding,[],[f50,f69])).
% 7.98/1.49  
% 7.98/1.49  fof(f67,plain,(
% 7.98/1.49    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)),
% 7.98/1.49    inference(cnf_transformation,[],[f44])).
% 7.98/1.49  
% 7.98/1.49  fof(f13,axiom,(
% 7.98/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 7.98/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.98/1.49  
% 7.98/1.49  fof(f29,plain,(
% 7.98/1.49    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.98/1.49    inference(ennf_transformation,[],[f13])).
% 7.98/1.49  
% 7.98/1.49  fof(f30,plain,(
% 7.98/1.49    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.98/1.49    inference(flattening,[],[f29])).
% 7.98/1.49  
% 7.98/1.49  fof(f57,plain,(
% 7.98/1.49    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.98/1.49    inference(cnf_transformation,[],[f30])).
% 7.98/1.49  
% 7.98/1.49  fof(f10,axiom,(
% 7.98/1.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 7.98/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.98/1.49  
% 7.98/1.49  fof(f27,plain,(
% 7.98/1.49    ! [X0,X1] : (k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.98/1.49    inference(ennf_transformation,[],[f10])).
% 7.98/1.49  
% 7.98/1.49  fof(f54,plain,(
% 7.98/1.49    ( ! [X0,X1] : (k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.98/1.49    inference(cnf_transformation,[],[f27])).
% 7.98/1.49  
% 7.98/1.49  fof(f5,axiom,(
% 7.98/1.49    ! [X0] : k2_subset_1(X0) = X0),
% 7.98/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.98/1.49  
% 7.98/1.49  fof(f49,plain,(
% 7.98/1.49    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 7.98/1.49    inference(cnf_transformation,[],[f5])).
% 7.98/1.49  
% 7.98/1.49  fof(f7,axiom,(
% 7.98/1.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 7.98/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.98/1.49  
% 7.98/1.49  fof(f23,plain,(
% 7.98/1.49    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.98/1.49    inference(ennf_transformation,[],[f7])).
% 7.98/1.49  
% 7.98/1.49  fof(f51,plain,(
% 7.98/1.49    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.98/1.49    inference(cnf_transformation,[],[f23])).
% 7.98/1.49  
% 7.98/1.49  fof(f8,axiom,(
% 7.98/1.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 7.98/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.98/1.49  
% 7.98/1.49  fof(f24,plain,(
% 7.98/1.49    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 7.98/1.49    inference(ennf_transformation,[],[f8])).
% 7.98/1.49  
% 7.98/1.49  fof(f25,plain,(
% 7.98/1.49    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.98/1.49    inference(flattening,[],[f24])).
% 7.98/1.49  
% 7.98/1.49  fof(f52,plain,(
% 7.98/1.49    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.98/1.49    inference(cnf_transformation,[],[f25])).
% 7.98/1.49  
% 7.98/1.49  fof(f4,axiom,(
% 7.98/1.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 7.98/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.98/1.49  
% 7.98/1.49  fof(f48,plain,(
% 7.98/1.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 7.98/1.49    inference(cnf_transformation,[],[f4])).
% 7.98/1.49  
% 7.98/1.49  fof(f72,plain,(
% 7.98/1.49    ( ! [X2,X0,X1] : (k3_tarski(k2_tarski(X1,X2)) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.98/1.49    inference(definition_unfolding,[],[f52,f48])).
% 7.98/1.49  
% 7.98/1.49  fof(f2,axiom,(
% 7.98/1.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))),
% 7.98/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.98/1.49  
% 7.98/1.49  fof(f46,plain,(
% 7.98/1.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 7.98/1.49    inference(cnf_transformation,[],[f2])).
% 7.98/1.49  
% 7.98/1.49  fof(f70,plain,(
% 7.98/1.49    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1))))) )),
% 7.98/1.49    inference(definition_unfolding,[],[f46,f48,f48,f48])).
% 7.98/1.49  
% 7.98/1.49  fof(f3,axiom,(
% 7.98/1.49    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 7.98/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.98/1.49  
% 7.98/1.49  fof(f47,plain,(
% 7.98/1.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 7.98/1.49    inference(cnf_transformation,[],[f3])).
% 7.98/1.49  
% 7.98/1.49  fof(f14,axiom,(
% 7.98/1.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 7.98/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.98/1.49  
% 7.98/1.49  fof(f31,plain,(
% 7.98/1.49    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 7.98/1.49    inference(ennf_transformation,[],[f14])).
% 7.98/1.49  
% 7.98/1.49  fof(f32,plain,(
% 7.98/1.49    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 7.98/1.49    inference(flattening,[],[f31])).
% 7.98/1.49  
% 7.98/1.49  fof(f59,plain,(
% 7.98/1.49    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.98/1.49    inference(cnf_transformation,[],[f32])).
% 7.98/1.49  
% 7.98/1.49  fof(f18,axiom,(
% 7.98/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)))),
% 7.98/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.98/1.49  
% 7.98/1.49  fof(f37,plain,(
% 7.98/1.49    ! [X0] : (! [X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.98/1.49    inference(ennf_transformation,[],[f18])).
% 7.98/1.49  
% 7.98/1.49  fof(f63,plain,(
% 7.98/1.49    ( ! [X0,X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.98/1.49    inference(cnf_transformation,[],[f37])).
% 7.98/1.49  
% 7.98/1.49  fof(f16,axiom,(
% 7.98/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)))),
% 7.98/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.98/1.49  
% 7.98/1.49  fof(f35,plain,(
% 7.98/1.49    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.98/1.49    inference(ennf_transformation,[],[f16])).
% 7.98/1.49  
% 7.98/1.49  fof(f61,plain,(
% 7.98/1.49    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.98/1.49    inference(cnf_transformation,[],[f35])).
% 7.98/1.49  
% 7.98/1.49  fof(f58,plain,(
% 7.98/1.49    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.98/1.49    inference(cnf_transformation,[],[f30])).
% 7.98/1.49  
% 7.98/1.49  fof(f68,plain,(
% 7.98/1.49    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)),
% 7.98/1.49    inference(cnf_transformation,[],[f44])).
% 7.98/1.49  
% 7.98/1.49  fof(f64,plain,(
% 7.98/1.49    v2_pre_topc(sK0)),
% 7.98/1.49    inference(cnf_transformation,[],[f44])).
% 7.98/1.49  
% 7.98/1.49  cnf(c_18,negated_conjecture,
% 7.98/1.49      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.98/1.49      inference(cnf_transformation,[],[f66]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_698,plain,
% 7.98/1.49      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 7.98/1.49      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_6,plain,
% 7.98/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.98/1.49      | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2))) = k7_subset_1(X1,X0,X2) ),
% 7.98/1.49      inference(cnf_transformation,[],[f73]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_710,plain,
% 7.98/1.49      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X2,X0,X1)
% 7.98/1.49      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
% 7.98/1.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_2258,plain,
% 7.98/1.49      ( k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0))) = k7_subset_1(u1_struct_0(sK0),sK1,X0) ),
% 7.98/1.49      inference(superposition,[status(thm)],[c_698,c_710]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_14,plain,
% 7.98/1.49      ( r1_tarski(k1_tops_1(X0,X1),X1)
% 7.98/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 7.98/1.49      | ~ l1_pre_topc(X0) ),
% 7.98/1.49      inference(cnf_transformation,[],[f62]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_702,plain,
% 7.98/1.49      ( r1_tarski(k1_tops_1(X0,X1),X1) = iProver_top
% 7.98/1.49      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.98/1.49      | l1_pre_topc(X0) != iProver_top ),
% 7.98/1.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_2048,plain,
% 7.98/1.49      ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top
% 7.98/1.49      | l1_pre_topc(sK0) != iProver_top ),
% 7.98/1.49      inference(superposition,[status(thm)],[c_698,c_702]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_19,negated_conjecture,
% 7.98/1.49      ( l1_pre_topc(sK0) ),
% 7.98/1.49      inference(cnf_transformation,[],[f65]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_22,plain,
% 7.98/1.49      ( l1_pre_topc(sK0) = iProver_top ),
% 7.98/1.49      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_23,plain,
% 7.98/1.49      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 7.98/1.49      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_890,plain,
% 7.98/1.49      ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
% 7.98/1.49      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.98/1.49      | ~ l1_pre_topc(sK0) ),
% 7.98/1.49      inference(instantiation,[status(thm)],[c_14]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_891,plain,
% 7.98/1.49      ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top
% 7.98/1.49      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.98/1.49      | l1_pre_topc(sK0) != iProver_top ),
% 7.98/1.49      inference(predicate_to_equality,[status(thm)],[c_890]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_2935,plain,
% 7.98/1.49      ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
% 7.98/1.49      inference(global_propositional_subsumption,
% 7.98/1.49                [status(thm)],
% 7.98/1.49                [c_2048,c_22,c_23,c_891]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_8,plain,
% 7.98/1.49      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 7.98/1.49      inference(cnf_transformation,[],[f56]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_708,plain,
% 7.98/1.49      ( r1_tarski(X0,X1) != iProver_top
% 7.98/1.49      | m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top ),
% 7.98/1.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_3,plain,
% 7.98/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.98/1.49      | k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))) = k3_subset_1(X1,X0) ),
% 7.98/1.49      inference(cnf_transformation,[],[f71]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_713,plain,
% 7.98/1.49      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k3_subset_1(X0,X1)
% 7.98/1.49      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 7.98/1.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_1728,plain,
% 7.98/1.49      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k3_subset_1(X0,X1)
% 7.98/1.49      | r1_tarski(X1,X0) != iProver_top ),
% 7.98/1.49      inference(superposition,[status(thm)],[c_708,c_713]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_2940,plain,
% 7.98/1.49      ( k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1)))) = k3_subset_1(sK1,k1_tops_1(sK0,sK1)) ),
% 7.98/1.49      inference(superposition,[status(thm)],[c_2935,c_1728]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_3177,plain,
% 7.98/1.49      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k3_subset_1(sK1,k1_tops_1(sK0,sK1)) ),
% 7.98/1.49      inference(superposition,[status(thm)],[c_2258,c_2940]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_17,negated_conjecture,
% 7.98/1.49      ( v4_pre_topc(sK1,sK0)
% 7.98/1.49      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 7.98/1.49      inference(cnf_transformation,[],[f67]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_699,plain,
% 7.98/1.49      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 7.98/1.49      | v4_pre_topc(sK1,sK0) = iProver_top ),
% 7.98/1.49      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_3180,plain,
% 7.98/1.49      ( k3_subset_1(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 7.98/1.49      | v4_pre_topc(sK1,sK0) = iProver_top ),
% 7.98/1.49      inference(demodulation,[status(thm)],[c_3177,c_699]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_10,plain,
% 7.98/1.49      ( ~ v4_pre_topc(X0,X1)
% 7.98/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.98/1.49      | ~ l1_pre_topc(X1)
% 7.98/1.49      | k2_pre_topc(X1,X0) = X0 ),
% 7.98/1.49      inference(cnf_transformation,[],[f57]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_706,plain,
% 7.98/1.49      ( k2_pre_topc(X0,X1) = X1
% 7.98/1.49      | v4_pre_topc(X1,X0) != iProver_top
% 7.98/1.49      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.98/1.49      | l1_pre_topc(X0) != iProver_top ),
% 7.98/1.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_6561,plain,
% 7.98/1.49      ( k2_pre_topc(sK0,sK1) = sK1
% 7.98/1.49      | v4_pre_topc(sK1,sK0) != iProver_top
% 7.98/1.49      | l1_pre_topc(sK0) != iProver_top ),
% 7.98/1.49      inference(superposition,[status(thm)],[c_698,c_706]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_6647,plain,
% 7.98/1.49      ( v4_pre_topc(sK1,sK0) != iProver_top
% 7.98/1.49      | k2_pre_topc(sK0,sK1) = sK1 ),
% 7.98/1.49      inference(global_propositional_subsumption,
% 7.98/1.49                [status(thm)],
% 7.98/1.49                [c_6561,c_22]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_6648,plain,
% 7.98/1.49      ( k2_pre_topc(sK0,sK1) = sK1
% 7.98/1.49      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 7.98/1.49      inference(renaming,[status(thm)],[c_6647]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_6653,plain,
% 7.98/1.49      ( k2_pre_topc(sK0,sK1) = sK1
% 7.98/1.49      | k3_subset_1(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 7.98/1.49      inference(superposition,[status(thm)],[c_3180,c_6648]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_7,plain,
% 7.98/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.98/1.49      | k4_subset_1(X1,X0,k3_subset_1(X1,X0)) = k2_subset_1(X1) ),
% 7.98/1.49      inference(cnf_transformation,[],[f54]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_709,plain,
% 7.98/1.49      ( k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = k2_subset_1(X0)
% 7.98/1.49      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 7.98/1.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_2,plain,
% 7.98/1.49      ( k2_subset_1(X0) = X0 ),
% 7.98/1.49      inference(cnf_transformation,[],[f49]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_738,plain,
% 7.98/1.49      ( k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = X0
% 7.98/1.49      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 7.98/1.49      inference(light_normalisation,[status(thm)],[c_709,c_2]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_1454,plain,
% 7.98/1.49      ( k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = X0
% 7.98/1.49      | r1_tarski(X1,X0) != iProver_top ),
% 7.98/1.49      inference(superposition,[status(thm)],[c_708,c_738]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_2941,plain,
% 7.98/1.49      ( k4_subset_1(sK1,k1_tops_1(sK0,sK1),k3_subset_1(sK1,k1_tops_1(sK0,sK1))) = sK1 ),
% 7.98/1.49      inference(superposition,[status(thm)],[c_2935,c_1454]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_7685,plain,
% 7.98/1.49      ( k4_subset_1(sK1,k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) = sK1
% 7.98/1.49      | k2_pre_topc(sK0,sK1) = sK1 ),
% 7.98/1.49      inference(superposition,[status(thm)],[c_6653,c_2941]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_4,plain,
% 7.98/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.98/1.49      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 7.98/1.49      inference(cnf_transformation,[],[f51]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_712,plain,
% 7.98/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.98/1.49      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 7.98/1.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_7683,plain,
% 7.98/1.49      ( k2_pre_topc(sK0,sK1) = sK1
% 7.98/1.49      | m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) != iProver_top
% 7.98/1.49      | m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) = iProver_top ),
% 7.98/1.49      inference(superposition,[status(thm)],[c_6653,c_712]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_1096,plain,
% 7.98/1.49      ( ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
% 7.98/1.49      | m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) ),
% 7.98/1.49      inference(instantiation,[status(thm)],[c_8]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_1097,plain,
% 7.98/1.49      ( r1_tarski(k1_tops_1(sK0,sK1),sK1) != iProver_top
% 7.98/1.49      | m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) = iProver_top ),
% 7.98/1.49      inference(predicate_to_equality,[status(thm)],[c_1096]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_9840,plain,
% 7.98/1.49      ( k2_pre_topc(sK0,sK1) = sK1
% 7.98/1.49      | m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) = iProver_top ),
% 7.98/1.49      inference(global_propositional_subsumption,
% 7.98/1.49                [status(thm)],
% 7.98/1.49                [c_7683,c_22,c_23,c_891,c_1097]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_5,plain,
% 7.98/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.98/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 7.98/1.49      | k4_subset_1(X1,X0,X2) = k3_tarski(k2_tarski(X0,X2)) ),
% 7.98/1.49      inference(cnf_transformation,[],[f72]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_711,plain,
% 7.98/1.49      ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
% 7.98/1.49      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 7.98/1.49      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
% 7.98/1.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_6515,plain,
% 7.98/1.49      ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
% 7.98/1.49      | r1_tarski(X1,X0) != iProver_top
% 7.98/1.49      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
% 7.98/1.49      inference(superposition,[status(thm)],[c_708,c_711]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_13749,plain,
% 7.98/1.49      ( k4_subset_1(sK1,X0,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(X0,k2_tops_1(sK0,sK1)))
% 7.98/1.49      | k2_pre_topc(sK0,sK1) = sK1
% 7.98/1.49      | r1_tarski(X0,sK1) != iProver_top ),
% 7.98/1.49      inference(superposition,[status(thm)],[c_9840,c_6515]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_16166,plain,
% 7.98/1.49      ( k4_subset_1(sK1,k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)))
% 7.98/1.49      | k2_pre_topc(sK0,sK1) = sK1 ),
% 7.98/1.49      inference(superposition,[status(thm)],[c_2935,c_13749]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_17109,plain,
% 7.98/1.49      ( k2_pre_topc(sK0,sK1) = sK1
% 7.98/1.49      | k3_tarski(k2_tarski(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))) = sK1 ),
% 7.98/1.49      inference(superposition,[status(thm)],[c_7685,c_16166]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_0,plain,
% 7.98/1.49      ( k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(X0,X1)) ),
% 7.98/1.49      inference(cnf_transformation,[],[f70]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_17262,plain,
% 7.98/1.49      ( k2_pre_topc(sK0,sK1) = sK1
% 7.98/1.49      | k3_tarski(k2_tarski(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))) = k3_tarski(k2_tarski(k1_tops_1(sK0,sK1),sK1)) ),
% 7.98/1.49      inference(superposition,[status(thm)],[c_17109,c_0]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_18070,plain,
% 7.98/1.49      ( k2_pre_topc(sK0,sK1) = sK1
% 7.98/1.49      | k3_tarski(k2_tarski(k1_tops_1(sK0,sK1),sK1)) = sK1 ),
% 7.98/1.49      inference(superposition,[status(thm)],[c_17262,c_17109]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_1,plain,
% 7.98/1.49      ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
% 7.98/1.49      inference(cnf_transformation,[],[f47]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_1020,plain,
% 7.98/1.49      ( k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X1,X0)))) = k3_tarski(k2_tarski(X0,X1)) ),
% 7.98/1.49      inference(superposition,[status(thm)],[c_1,c_0]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_1157,plain,
% 7.98/1.49      ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X0)) ),
% 7.98/1.49      inference(superposition,[status(thm)],[c_0,c_1020]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_2027,plain,
% 7.98/1.49      ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(k3_tarski(k2_tarski(X1,X0)),X1)) ),
% 7.98/1.49      inference(superposition,[status(thm)],[c_1,c_1157]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_2233,plain,
% 7.98/1.49      ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X0)) = k3_tarski(k2_tarski(k3_tarski(k2_tarski(X1,X0)),X1)) ),
% 7.98/1.49      inference(superposition,[status(thm)],[c_2027,c_1157]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_4301,plain,
% 7.98/1.49      ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X0)) = k3_tarski(k2_tarski(X1,k3_tarski(k2_tarski(X1,X0)))) ),
% 7.98/1.49      inference(superposition,[status(thm)],[c_1,c_2233]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_4403,plain,
% 7.98/1.49      ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X0)) = k3_tarski(k2_tarski(X1,X0)) ),
% 7.98/1.49      inference(demodulation,[status(thm)],[c_4301,c_0]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_4499,plain,
% 7.98/1.49      ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X1)) = k3_tarski(k2_tarski(X0,X1)) ),
% 7.98/1.49      inference(superposition,[status(thm)],[c_1,c_4403]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_18058,plain,
% 7.98/1.49      ( k2_pre_topc(sK0,sK1) = sK1
% 7.98/1.49      | k3_tarski(k2_tarski(k3_tarski(k2_tarski(k1_tops_1(sK0,sK1),sK1)),k2_tops_1(sK0,sK1))) = k3_tarski(k2_tarski(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))) ),
% 7.98/1.49      inference(superposition,[status(thm)],[c_17262,c_4499]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_24319,plain,
% 7.98/1.49      ( k2_pre_topc(sK0,sK1) = sK1
% 7.98/1.49      | k3_tarski(k2_tarski(k3_tarski(k2_tarski(k1_tops_1(sK0,sK1),sK1)),k3_tarski(k2_tarski(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))))) = k3_tarski(k2_tarski(k3_tarski(k2_tarski(k1_tops_1(sK0,sK1),sK1)),k2_tops_1(sK0,sK1))) ),
% 7.98/1.49      inference(superposition,[status(thm)],[c_18058,c_0]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_24388,plain,
% 7.98/1.49      ( k2_pre_topc(sK0,sK1) = sK1
% 7.98/1.49      | k3_tarski(k2_tarski(k3_tarski(k2_tarski(k1_tops_1(sK0,sK1),sK1)),k2_tops_1(sK0,sK1))) = k3_tarski(k2_tarski(k3_tarski(k2_tarski(k1_tops_1(sK0,sK1),sK1)),sK1)) ),
% 7.98/1.49      inference(superposition,[status(thm)],[c_17109,c_24319]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_24463,plain,
% 7.98/1.49      ( k2_pre_topc(sK0,sK1) = sK1
% 7.98/1.49      | k3_tarski(k2_tarski(k3_tarski(k2_tarski(k1_tops_1(sK0,sK1),sK1)),k2_tops_1(sK0,sK1))) = k3_tarski(k2_tarski(k1_tops_1(sK0,sK1),sK1)) ),
% 7.98/1.49      inference(demodulation,[status(thm)],[c_24388,c_4499]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_28991,plain,
% 7.98/1.49      ( k2_pre_topc(sK0,sK1) = sK1
% 7.98/1.49      | k3_tarski(k2_tarski(k1_tops_1(sK0,sK1),sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
% 7.98/1.49      inference(superposition,[status(thm)],[c_18070,c_24463]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_11,plain,
% 7.98/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.98/1.49      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.98/1.49      | ~ l1_pre_topc(X1) ),
% 7.98/1.49      inference(cnf_transformation,[],[f59]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_705,plain,
% 7.98/1.49      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 7.98/1.49      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 7.98/1.49      | l1_pre_topc(X1) != iProver_top ),
% 7.98/1.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_6518,plain,
% 7.98/1.49      ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k3_tarski(k2_tarski(sK1,X0))
% 7.98/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.98/1.49      inference(superposition,[status(thm)],[c_698,c_711]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_6659,plain,
% 7.98/1.49      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0)))
% 7.98/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.98/1.49      | l1_pre_topc(sK0) != iProver_top ),
% 7.98/1.49      inference(superposition,[status(thm)],[c_705,c_6518]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_7175,plain,
% 7.98/1.49      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.98/1.49      | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0))) ),
% 7.98/1.49      inference(global_propositional_subsumption,
% 7.98/1.49                [status(thm)],
% 7.98/1.49                [c_6659,c_22]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_7176,plain,
% 7.98/1.49      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0)))
% 7.98/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.98/1.49      inference(renaming,[status(thm)],[c_7175]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_7186,plain,
% 7.98/1.49      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
% 7.98/1.49      inference(superposition,[status(thm)],[c_698,c_7176]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_15,plain,
% 7.98/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.98/1.49      | ~ l1_pre_topc(X1)
% 7.98/1.49      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
% 7.98/1.49      inference(cnf_transformation,[],[f63]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_701,plain,
% 7.98/1.49      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
% 7.98/1.49      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.98/1.49      | l1_pre_topc(X0) != iProver_top ),
% 7.98/1.49      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_1154,plain,
% 7.98/1.49      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
% 7.98/1.49      | l1_pre_topc(sK0) != iProver_top ),
% 7.98/1.49      inference(superposition,[status(thm)],[c_698,c_701]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_970,plain,
% 7.98/1.49      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.98/1.49      | ~ l1_pre_topc(sK0)
% 7.98/1.49      | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 7.98/1.49      inference(instantiation,[status(thm)],[c_15]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_1617,plain,
% 7.98/1.49      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 7.98/1.49      inference(global_propositional_subsumption,
% 7.98/1.49                [status(thm)],
% 7.98/1.49                [c_1154,c_19,c_18,c_970]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_7188,plain,
% 7.98/1.49      ( k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k2_pre_topc(sK0,sK1) ),
% 7.98/1.49      inference(light_normalisation,[status(thm)],[c_7186,c_1617]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_29050,plain,
% 7.98/1.49      ( k2_pre_topc(sK0,sK1) = sK1
% 7.98/1.49      | k3_tarski(k2_tarski(k1_tops_1(sK0,sK1),sK1)) = k2_pre_topc(sK0,sK1) ),
% 7.98/1.49      inference(light_normalisation,[status(thm)],[c_28991,c_7188]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_29494,plain,
% 7.98/1.49      ( k2_pre_topc(sK0,sK1) = sK1 ),
% 7.98/1.49      inference(superposition,[status(thm)],[c_29050,c_18070]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_13,plain,
% 7.98/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.98/1.49      | ~ l1_pre_topc(X1)
% 7.98/1.49      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
% 7.98/1.49      inference(cnf_transformation,[],[f61]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_703,plain,
% 7.98/1.49      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
% 7.98/1.49      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.98/1.49      | l1_pre_topc(X0) != iProver_top ),
% 7.98/1.49      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_3300,plain,
% 7.98/1.49      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 7.98/1.49      | l1_pre_topc(sK0) != iProver_top ),
% 7.98/1.49      inference(superposition,[status(thm)],[c_698,c_703]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_973,plain,
% 7.98/1.49      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.98/1.49      | ~ l1_pre_topc(sK0)
% 7.98/1.49      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 7.98/1.49      inference(instantiation,[status(thm)],[c_13]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_3976,plain,
% 7.98/1.49      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 7.98/1.49      inference(global_propositional_subsumption,
% 7.98/1.49                [status(thm)],
% 7.98/1.49                [c_3300,c_19,c_18,c_973]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_29509,plain,
% 7.98/1.49      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 7.98/1.49      inference(demodulation,[status(thm)],[c_29494,c_3976]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_9,plain,
% 7.98/1.49      ( v4_pre_topc(X0,X1)
% 7.98/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.98/1.49      | ~ l1_pre_topc(X1)
% 7.98/1.49      | ~ v2_pre_topc(X1)
% 7.98/1.49      | k2_pre_topc(X1,X0) != X0 ),
% 7.98/1.49      inference(cnf_transformation,[],[f58]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_967,plain,
% 7.98/1.49      ( v4_pre_topc(sK1,sK0)
% 7.98/1.49      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.98/1.49      | ~ l1_pre_topc(sK0)
% 7.98/1.49      | ~ v2_pre_topc(sK0)
% 7.98/1.49      | k2_pre_topc(sK0,sK1) != sK1 ),
% 7.98/1.49      inference(instantiation,[status(thm)],[c_9]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_16,negated_conjecture,
% 7.98/1.49      ( ~ v4_pre_topc(sK1,sK0)
% 7.98/1.49      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
% 7.98/1.49      inference(cnf_transformation,[],[f68]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(c_20,negated_conjecture,
% 7.98/1.49      ( v2_pre_topc(sK0) ),
% 7.98/1.49      inference(cnf_transformation,[],[f64]) ).
% 7.98/1.49  
% 7.98/1.49  cnf(contradiction,plain,
% 7.98/1.49      ( $false ),
% 7.98/1.49      inference(minisat,
% 7.98/1.49                [status(thm)],
% 7.98/1.49                [c_29509,c_29494,c_967,c_16,c_18,c_19,c_20]) ).
% 7.98/1.49  
% 7.98/1.49  
% 7.98/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.98/1.49  
% 7.98/1.49  ------                               Statistics
% 7.98/1.49  
% 7.98/1.49  ------ Selected
% 7.98/1.49  
% 7.98/1.49  total_time:                             0.992
% 7.98/1.49  
%------------------------------------------------------------------------------
