%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:14:40 EST 2020

% Result     : Theorem 7.97s
% Output     : CNFRefutation 7.97s
% Verified   : 
% Statistics : Number of formulae       :  153 (2168 expanded)
%              Number of clauses        :   88 ( 660 expanded)
%              Number of leaves         :   19 ( 474 expanded)
%              Depth                    :   21
%              Number of atoms          :  368 (9131 expanded)
%              Number of equality atoms :  185 (2928 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   2 average)

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f37])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1)
            | ~ v4_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f38])).

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
    inference(flattening,[],[f39])).

fof(f42,plain,(
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

fof(f41,plain,
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

fof(f43,plain,
    ( ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f40,f42,f41])).

fof(f65,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f64,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f43])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f12])).

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
    inference(flattening,[],[f28])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f63,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f67,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f45,f53])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f51,f67])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f11])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f48,f67])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f7,axiom,(
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
    inference(ennf_transformation,[],[f7])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f23])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f57,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) != X1
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f66,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f62,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_17,negated_conjecture,
    ( v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_694,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_693,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_10,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_701,plain,
    ( k2_pre_topc(X0,X1) = X1
    | v4_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4862,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | v4_pre_topc(sK1,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_693,c_701])).

cnf(c_19,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_22,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_5249,plain,
    ( v4_pre_topc(sK1,sK0) != iProver_top
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4862,c_22])).

cnf(c_5250,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5249])).

cnf(c_5255,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_694,c_5250])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2))) = k7_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_705,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X2,X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3522,plain,
    ( k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0))) = k7_subset_1(u1_struct_0(sK0),sK1,X0) ),
    inference(superposition,[status(thm)],[c_693,c_705])).

cnf(c_14,plain,
    ( r1_tarski(k1_tops_1(X0,X1),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_697,plain,
    ( r1_tarski(k1_tops_1(X0,X1),X1) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2231,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_693,c_697])).

cnf(c_23,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_885,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_886,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_885])).

cnf(c_3009,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2231,c_22,c_23,c_886])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_703,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_708,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k3_subset_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3445,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k3_subset_1(X0,X1)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_703,c_708])).

cnf(c_7263,plain,
    ( k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1)))) = k3_subset_1(sK1,k1_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_3009,c_3445])).

cnf(c_7866,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k3_subset_1(sK1,k1_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_3522,c_7263])).

cnf(c_7881,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k3_subset_1(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_5255,c_7866])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_707,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_706,plain,
    ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3651,plain,
    ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
    | r1_tarski(X1,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_703,c_706])).

cnf(c_9294,plain,
    ( k4_subset_1(X0,X1,k3_subset_1(X0,X2)) = k2_xboole_0(X1,k3_subset_1(X0,X2))
    | r1_tarski(X1,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_707,c_3651])).

cnf(c_14624,plain,
    ( k4_subset_1(X0,X1,k3_subset_1(X0,X2)) = k2_xboole_0(X1,k3_subset_1(X0,X2))
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_703,c_9294])).

cnf(c_15537,plain,
    ( k4_subset_1(sK1,k1_tops_1(sK0,sK1),k3_subset_1(sK1,X0)) = k2_xboole_0(k1_tops_1(sK0,sK1),k3_subset_1(sK1,X0))
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3009,c_14624])).

cnf(c_16418,plain,
    ( k4_subset_1(sK1,k1_tops_1(sK0,sK1),k3_subset_1(sK1,k1_tops_1(sK0,sK1))) = k2_xboole_0(k1_tops_1(sK0,sK1),k3_subset_1(sK1,k1_tops_1(sK0,sK1))) ),
    inference(superposition,[status(thm)],[c_3009,c_15537])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X0,k3_subset_1(X1,X0)) = k2_subset_1(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_704,plain,
    ( k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = k2_subset_1(X0)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_733,plain,
    ( k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = X0
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_704,c_2])).

cnf(c_2725,plain,
    ( k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = X0
    | r1_tarski(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_703,c_733])).

cnf(c_6301,plain,
    ( k4_subset_1(sK1,k1_tops_1(sK0,sK1),k3_subset_1(sK1,k1_tops_1(sK0,sK1))) = sK1 ),
    inference(superposition,[status(thm)],[c_3009,c_2725])).

cnf(c_16427,plain,
    ( k2_xboole_0(k1_tops_1(sK0,sK1),k3_subset_1(sK1,k1_tops_1(sK0,sK1))) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_16418,c_6301])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1057,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_0,c_1])).

cnf(c_1170,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(k2_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_1,c_1057])).

cnf(c_1317,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(k2_xboole_0(X1,X0),X1) ),
    inference(superposition,[status(thm)],[c_0,c_1170])).

cnf(c_1534,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(k2_xboole_0(X1,X0),X1) ),
    inference(superposition,[status(thm)],[c_1317,c_1170])).

cnf(c_1683,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_xboole_0(X1,X0),X1) ),
    inference(superposition,[status(thm)],[c_1534,c_0])).

cnf(c_1685,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_1683,c_1])).

cnf(c_1733,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_1685,c_0])).

cnf(c_2059,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_1733])).

cnf(c_18006,plain,
    ( k2_xboole_0(k1_tops_1(sK0,sK1),k3_subset_1(sK1,k1_tops_1(sK0,sK1))) = k2_xboole_0(k3_subset_1(sK1,k1_tops_1(sK0,sK1)),sK1) ),
    inference(superposition,[status(thm)],[c_16427,c_2059])).

cnf(c_18010,plain,
    ( k2_xboole_0(k3_subset_1(sK1,k1_tops_1(sK0,sK1)),sK1) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_18006,c_16427])).

cnf(c_28781,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k2_xboole_0(k2_tops_1(sK0,sK1),sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_7881,c_18010])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_700,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3654,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k2_xboole_0(sK1,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_693,c_706])).

cnf(c_3776,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_700,c_3654])).

cnf(c_5849,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3776,c_22])).

cnf(c_5850,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_5849])).

cnf(c_5860,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_693,c_5850])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_696,plain,
    ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1165,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_693,c_696])).

cnf(c_965,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1555,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1165,c_19,c_18,c_965])).

cnf(c_5862,plain,
    ( k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_5860,c_1555])).

cnf(c_5967,plain,
    ( k2_xboole_0(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_5862,c_2059])).

cnf(c_5968,plain,
    ( k2_xboole_0(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1)) = k2_xboole_0(k2_tops_1(sK0,sK1),sK1) ),
    inference(superposition,[status(thm)],[c_5862,c_1057])).

cnf(c_5971,plain,
    ( k2_xboole_0(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_5967,c_5862,c_5968])).

cnf(c_5973,plain,
    ( k2_xboole_0(k2_tops_1(sK0,sK1),sK1) = k2_pre_topc(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_5971,c_5968])).

cnf(c_28814,plain,
    ( k2_pre_topc(sK0,sK1) = sK1 ),
    inference(demodulation,[status(thm)],[c_28781,c_5973])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_698,plain,
    ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3418,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_693,c_698])).

cnf(c_968,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_4088,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3418,c_19,c_18,c_968])).

cnf(c_28830,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_28814,c_4088])).

cnf(c_9,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | k2_pre_topc(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_962,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | k2_pre_topc(sK0,sK1) != sK1 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_16,negated_conjecture,
    ( ~ v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_20,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f62])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_28830,c_28814,c_962,c_16,c_18,c_19,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:49:14 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 7.97/1.51  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.97/1.51  
% 7.97/1.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.97/1.51  
% 7.97/1.51  ------  iProver source info
% 7.97/1.51  
% 7.97/1.51  git: date: 2020-06-30 10:37:57 +0100
% 7.97/1.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.97/1.51  git: non_committed_changes: false
% 7.97/1.51  git: last_make_outside_of_git: false
% 7.97/1.51  
% 7.97/1.51  ------ 
% 7.97/1.51  ------ Parsing...
% 7.97/1.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.97/1.51  
% 7.97/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 7.97/1.51  
% 7.97/1.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.97/1.51  
% 7.97/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.97/1.51  ------ Proving...
% 7.97/1.51  ------ Problem Properties 
% 7.97/1.51  
% 7.97/1.51  
% 7.97/1.51  clauses                                 21
% 7.97/1.51  conjectures                             5
% 7.97/1.51  EPR                                     2
% 7.97/1.51  Horn                                    20
% 7.97/1.51  unary                                   6
% 7.97/1.51  binary                                  7
% 7.97/1.51  lits                                    48
% 7.97/1.51  lits eq                                 13
% 7.97/1.51  fd_pure                                 0
% 7.97/1.51  fd_pseudo                               0
% 7.97/1.51  fd_cond                                 0
% 7.97/1.51  fd_pseudo_cond                          0
% 7.97/1.51  AC symbols                              0
% 7.97/1.51  
% 7.97/1.51  ------ Input Options Time Limit: Unbounded
% 7.97/1.51  
% 7.97/1.51  
% 7.97/1.51  ------ 
% 7.97/1.51  Current options:
% 7.97/1.51  ------ 
% 7.97/1.51  
% 7.97/1.51  
% 7.97/1.51  
% 7.97/1.51  
% 7.97/1.51  ------ Proving...
% 7.97/1.51  
% 7.97/1.51  
% 7.97/1.51  % SZS status Theorem for theBenchmark.p
% 7.97/1.51  
% 7.97/1.51  % SZS output start CNFRefutation for theBenchmark.p
% 7.97/1.51  
% 7.97/1.51  fof(f18,conjecture,(
% 7.97/1.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 7.97/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.97/1.51  
% 7.97/1.51  fof(f19,negated_conjecture,(
% 7.97/1.51    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 7.97/1.51    inference(negated_conjecture,[],[f18])).
% 7.97/1.51  
% 7.97/1.51  fof(f37,plain,(
% 7.97/1.51    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 7.97/1.51    inference(ennf_transformation,[],[f19])).
% 7.97/1.51  
% 7.97/1.51  fof(f38,plain,(
% 7.97/1.51    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 7.97/1.51    inference(flattening,[],[f37])).
% 7.97/1.51  
% 7.97/1.51  fof(f39,plain,(
% 7.97/1.51    ? [X0] : (? [X1] : (((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 7.97/1.51    inference(nnf_transformation,[],[f38])).
% 7.97/1.51  
% 7.97/1.51  fof(f40,plain,(
% 7.97/1.51    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 7.97/1.51    inference(flattening,[],[f39])).
% 7.97/1.51  
% 7.97/1.51  fof(f42,plain,(
% 7.97/1.51    ( ! [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) != k2_tops_1(X0,sK1) | ~v4_pre_topc(sK1,X0)) & (k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) = k2_tops_1(X0,sK1) | v4_pre_topc(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 7.97/1.51    introduced(choice_axiom,[])).
% 7.97/1.51  
% 7.97/1.51  fof(f41,plain,(
% 7.97/1.51    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) != k2_tops_1(sK0,X1) | ~v4_pre_topc(X1,sK0)) & (k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) = k2_tops_1(sK0,X1) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 7.97/1.51    introduced(choice_axiom,[])).
% 7.97/1.51  
% 7.97/1.51  fof(f43,plain,(
% 7.97/1.51    ((k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)) & (k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 7.97/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f40,f42,f41])).
% 7.97/1.51  
% 7.97/1.51  fof(f65,plain,(
% 7.97/1.51    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)),
% 7.97/1.51    inference(cnf_transformation,[],[f43])).
% 7.97/1.51  
% 7.97/1.51  fof(f64,plain,(
% 7.97/1.51    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 7.97/1.51    inference(cnf_transformation,[],[f43])).
% 7.97/1.51  
% 7.97/1.51  fof(f12,axiom,(
% 7.97/1.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 7.97/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.97/1.51  
% 7.97/1.51  fof(f28,plain,(
% 7.97/1.51    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.97/1.51    inference(ennf_transformation,[],[f12])).
% 7.97/1.51  
% 7.97/1.51  fof(f29,plain,(
% 7.97/1.51    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.97/1.51    inference(flattening,[],[f28])).
% 7.97/1.51  
% 7.97/1.51  fof(f55,plain,(
% 7.97/1.51    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.97/1.51    inference(cnf_transformation,[],[f29])).
% 7.97/1.51  
% 7.97/1.51  fof(f63,plain,(
% 7.97/1.51    l1_pre_topc(sK0)),
% 7.97/1.51    inference(cnf_transformation,[],[f43])).
% 7.97/1.51  
% 7.97/1.51  fof(f8,axiom,(
% 7.97/1.51    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 7.97/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.97/1.51  
% 7.97/1.51  fof(f25,plain,(
% 7.97/1.51    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.97/1.51    inference(ennf_transformation,[],[f8])).
% 7.97/1.51  
% 7.97/1.51  fof(f51,plain,(
% 7.97/1.51    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.97/1.51    inference(cnf_transformation,[],[f25])).
% 7.97/1.51  
% 7.97/1.51  fof(f2,axiom,(
% 7.97/1.51    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 7.97/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.97/1.51  
% 7.97/1.51  fof(f45,plain,(
% 7.97/1.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 7.97/1.51    inference(cnf_transformation,[],[f2])).
% 7.97/1.51  
% 7.97/1.51  fof(f10,axiom,(
% 7.97/1.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 7.97/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.97/1.51  
% 7.97/1.51  fof(f53,plain,(
% 7.97/1.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 7.97/1.51    inference(cnf_transformation,[],[f10])).
% 7.97/1.51  
% 7.97/1.51  fof(f67,plain,(
% 7.97/1.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 7.97/1.51    inference(definition_unfolding,[],[f45,f53])).
% 7.97/1.51  
% 7.97/1.51  fof(f69,plain,(
% 7.97/1.51    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.97/1.51    inference(definition_unfolding,[],[f51,f67])).
% 7.97/1.51  
% 7.97/1.51  fof(f16,axiom,(
% 7.97/1.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 7.97/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.97/1.51  
% 7.97/1.51  fof(f35,plain,(
% 7.97/1.51    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.97/1.51    inference(ennf_transformation,[],[f16])).
% 7.97/1.51  
% 7.97/1.51  fof(f60,plain,(
% 7.97/1.51    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.97/1.51    inference(cnf_transformation,[],[f35])).
% 7.97/1.51  
% 7.97/1.51  fof(f11,axiom,(
% 7.97/1.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.97/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.97/1.51  
% 7.97/1.51  fof(f20,plain,(
% 7.97/1.51    ! [X0,X1] : (r1_tarski(X0,X1) => m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 7.97/1.51    inference(unused_predicate_definition_removal,[],[f11])).
% 7.97/1.51  
% 7.97/1.51  fof(f27,plain,(
% 7.97/1.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 7.97/1.51    inference(ennf_transformation,[],[f20])).
% 7.97/1.51  
% 7.97/1.51  fof(f54,plain,(
% 7.97/1.51    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.97/1.51    inference(cnf_transformation,[],[f27])).
% 7.97/1.51  
% 7.97/1.51  fof(f5,axiom,(
% 7.97/1.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 7.97/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.97/1.51  
% 7.97/1.51  fof(f21,plain,(
% 7.97/1.51    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.97/1.51    inference(ennf_transformation,[],[f5])).
% 7.97/1.51  
% 7.97/1.51  fof(f48,plain,(
% 7.97/1.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.97/1.51    inference(cnf_transformation,[],[f21])).
% 7.97/1.51  
% 7.97/1.51  fof(f68,plain,(
% 7.97/1.51    ( ! [X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.97/1.51    inference(definition_unfolding,[],[f48,f67])).
% 7.97/1.51  
% 7.97/1.51  fof(f6,axiom,(
% 7.97/1.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 7.97/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.97/1.51  
% 7.97/1.51  fof(f22,plain,(
% 7.97/1.51    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.97/1.51    inference(ennf_transformation,[],[f6])).
% 7.97/1.51  
% 7.97/1.51  fof(f49,plain,(
% 7.97/1.51    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.97/1.51    inference(cnf_transformation,[],[f22])).
% 7.97/1.51  
% 7.97/1.51  fof(f7,axiom,(
% 7.97/1.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 7.97/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.97/1.51  
% 7.97/1.51  fof(f23,plain,(
% 7.97/1.51    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 7.97/1.51    inference(ennf_transformation,[],[f7])).
% 7.97/1.51  
% 7.97/1.51  fof(f24,plain,(
% 7.97/1.51    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.97/1.51    inference(flattening,[],[f23])).
% 7.97/1.51  
% 7.97/1.51  fof(f50,plain,(
% 7.97/1.51    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.97/1.51    inference(cnf_transformation,[],[f24])).
% 7.97/1.51  
% 7.97/1.51  fof(f9,axiom,(
% 7.97/1.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 7.97/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.97/1.51  
% 7.97/1.51  fof(f26,plain,(
% 7.97/1.51    ! [X0,X1] : (k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.97/1.51    inference(ennf_transformation,[],[f9])).
% 7.97/1.51  
% 7.97/1.51  fof(f52,plain,(
% 7.97/1.51    ( ! [X0,X1] : (k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.97/1.51    inference(cnf_transformation,[],[f26])).
% 7.97/1.51  
% 7.97/1.51  fof(f4,axiom,(
% 7.97/1.51    ! [X0] : k2_subset_1(X0) = X0),
% 7.97/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.97/1.51  
% 7.97/1.51  fof(f47,plain,(
% 7.97/1.51    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 7.97/1.51    inference(cnf_transformation,[],[f4])).
% 7.97/1.51  
% 7.97/1.51  fof(f1,axiom,(
% 7.97/1.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 7.97/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.97/1.51  
% 7.97/1.51  fof(f44,plain,(
% 7.97/1.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 7.97/1.51    inference(cnf_transformation,[],[f1])).
% 7.97/1.51  
% 7.97/1.51  fof(f3,axiom,(
% 7.97/1.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))),
% 7.97/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.97/1.51  
% 7.97/1.51  fof(f46,plain,(
% 7.97/1.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 7.97/1.51    inference(cnf_transformation,[],[f3])).
% 7.97/1.51  
% 7.97/1.51  fof(f13,axiom,(
% 7.97/1.51    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 7.97/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.97/1.51  
% 7.97/1.51  fof(f30,plain,(
% 7.97/1.51    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 7.97/1.51    inference(ennf_transformation,[],[f13])).
% 7.97/1.51  
% 7.97/1.51  fof(f31,plain,(
% 7.97/1.51    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 7.97/1.51    inference(flattening,[],[f30])).
% 7.97/1.51  
% 7.97/1.51  fof(f57,plain,(
% 7.97/1.51    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.97/1.51    inference(cnf_transformation,[],[f31])).
% 7.97/1.51  
% 7.97/1.51  fof(f17,axiom,(
% 7.97/1.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)))),
% 7.97/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.97/1.51  
% 7.97/1.51  fof(f36,plain,(
% 7.97/1.51    ! [X0] : (! [X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.97/1.51    inference(ennf_transformation,[],[f17])).
% 7.97/1.51  
% 7.97/1.51  fof(f61,plain,(
% 7.97/1.51    ( ! [X0,X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.97/1.51    inference(cnf_transformation,[],[f36])).
% 7.97/1.51  
% 7.97/1.51  fof(f15,axiom,(
% 7.97/1.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)))),
% 7.97/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.97/1.51  
% 7.97/1.51  fof(f34,plain,(
% 7.97/1.51    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.97/1.51    inference(ennf_transformation,[],[f15])).
% 7.97/1.51  
% 7.97/1.51  fof(f59,plain,(
% 7.97/1.51    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.97/1.51    inference(cnf_transformation,[],[f34])).
% 7.97/1.51  
% 7.97/1.51  fof(f56,plain,(
% 7.97/1.51    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.97/1.51    inference(cnf_transformation,[],[f29])).
% 7.97/1.51  
% 7.97/1.51  fof(f66,plain,(
% 7.97/1.51    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)),
% 7.97/1.51    inference(cnf_transformation,[],[f43])).
% 7.97/1.51  
% 7.97/1.51  fof(f62,plain,(
% 7.97/1.51    v2_pre_topc(sK0)),
% 7.97/1.51    inference(cnf_transformation,[],[f43])).
% 7.97/1.51  
% 7.97/1.51  cnf(c_17,negated_conjecture,
% 7.97/1.51      ( v4_pre_topc(sK1,sK0)
% 7.97/1.51      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 7.97/1.51      inference(cnf_transformation,[],[f65]) ).
% 7.97/1.51  
% 7.97/1.51  cnf(c_694,plain,
% 7.97/1.51      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 7.97/1.51      | v4_pre_topc(sK1,sK0) = iProver_top ),
% 7.97/1.51      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.97/1.51  
% 7.97/1.51  cnf(c_18,negated_conjecture,
% 7.97/1.51      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.97/1.51      inference(cnf_transformation,[],[f64]) ).
% 7.97/1.51  
% 7.97/1.51  cnf(c_693,plain,
% 7.97/1.51      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 7.97/1.51      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.97/1.51  
% 7.97/1.51  cnf(c_10,plain,
% 7.97/1.51      ( ~ v4_pre_topc(X0,X1)
% 7.97/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.97/1.51      | ~ l1_pre_topc(X1)
% 7.97/1.51      | k2_pre_topc(X1,X0) = X0 ),
% 7.97/1.51      inference(cnf_transformation,[],[f55]) ).
% 7.97/1.51  
% 7.97/1.51  cnf(c_701,plain,
% 7.97/1.51      ( k2_pre_topc(X0,X1) = X1
% 7.97/1.51      | v4_pre_topc(X1,X0) != iProver_top
% 7.97/1.51      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.97/1.51      | l1_pre_topc(X0) != iProver_top ),
% 7.97/1.51      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.97/1.51  
% 7.97/1.51  cnf(c_4862,plain,
% 7.97/1.51      ( k2_pre_topc(sK0,sK1) = sK1
% 7.97/1.51      | v4_pre_topc(sK1,sK0) != iProver_top
% 7.97/1.51      | l1_pre_topc(sK0) != iProver_top ),
% 7.97/1.51      inference(superposition,[status(thm)],[c_693,c_701]) ).
% 7.97/1.51  
% 7.97/1.51  cnf(c_19,negated_conjecture,
% 7.97/1.51      ( l1_pre_topc(sK0) ),
% 7.97/1.51      inference(cnf_transformation,[],[f63]) ).
% 7.97/1.51  
% 7.97/1.51  cnf(c_22,plain,
% 7.97/1.51      ( l1_pre_topc(sK0) = iProver_top ),
% 7.97/1.51      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.97/1.51  
% 7.97/1.51  cnf(c_5249,plain,
% 7.97/1.51      ( v4_pre_topc(sK1,sK0) != iProver_top
% 7.97/1.51      | k2_pre_topc(sK0,sK1) = sK1 ),
% 7.97/1.51      inference(global_propositional_subsumption,
% 7.97/1.51                [status(thm)],
% 7.97/1.51                [c_4862,c_22]) ).
% 7.97/1.51  
% 7.97/1.51  cnf(c_5250,plain,
% 7.97/1.51      ( k2_pre_topc(sK0,sK1) = sK1
% 7.97/1.51      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 7.97/1.51      inference(renaming,[status(thm)],[c_5249]) ).
% 7.97/1.51  
% 7.97/1.51  cnf(c_5255,plain,
% 7.97/1.51      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 7.97/1.51      | k2_pre_topc(sK0,sK1) = sK1 ),
% 7.97/1.51      inference(superposition,[status(thm)],[c_694,c_5250]) ).
% 7.97/1.51  
% 7.97/1.51  cnf(c_6,plain,
% 7.97/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.97/1.51      | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2))) = k7_subset_1(X1,X0,X2) ),
% 7.97/1.51      inference(cnf_transformation,[],[f69]) ).
% 7.97/1.51  
% 7.97/1.51  cnf(c_705,plain,
% 7.97/1.51      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X2,X0,X1)
% 7.97/1.51      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
% 7.97/1.51      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.97/1.51  
% 7.97/1.51  cnf(c_3522,plain,
% 7.97/1.51      ( k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0))) = k7_subset_1(u1_struct_0(sK0),sK1,X0) ),
% 7.97/1.51      inference(superposition,[status(thm)],[c_693,c_705]) ).
% 7.97/1.51  
% 7.97/1.51  cnf(c_14,plain,
% 7.97/1.51      ( r1_tarski(k1_tops_1(X0,X1),X1)
% 7.97/1.51      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 7.97/1.51      | ~ l1_pre_topc(X0) ),
% 7.97/1.51      inference(cnf_transformation,[],[f60]) ).
% 7.97/1.51  
% 7.97/1.51  cnf(c_697,plain,
% 7.97/1.51      ( r1_tarski(k1_tops_1(X0,X1),X1) = iProver_top
% 7.97/1.51      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.97/1.51      | l1_pre_topc(X0) != iProver_top ),
% 7.97/1.51      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.97/1.51  
% 7.97/1.51  cnf(c_2231,plain,
% 7.97/1.51      ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top
% 7.97/1.51      | l1_pre_topc(sK0) != iProver_top ),
% 7.97/1.51      inference(superposition,[status(thm)],[c_693,c_697]) ).
% 7.97/1.51  
% 7.97/1.51  cnf(c_23,plain,
% 7.97/1.51      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 7.97/1.51      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.97/1.51  
% 7.97/1.51  cnf(c_885,plain,
% 7.97/1.51      ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
% 7.97/1.51      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.97/1.51      | ~ l1_pre_topc(sK0) ),
% 7.97/1.51      inference(instantiation,[status(thm)],[c_14]) ).
% 7.97/1.51  
% 7.97/1.51  cnf(c_886,plain,
% 7.97/1.51      ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top
% 7.97/1.51      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.97/1.51      | l1_pre_topc(sK0) != iProver_top ),
% 7.97/1.51      inference(predicate_to_equality,[status(thm)],[c_885]) ).
% 7.97/1.51  
% 7.97/1.51  cnf(c_3009,plain,
% 7.97/1.51      ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
% 7.97/1.51      inference(global_propositional_subsumption,
% 7.97/1.51                [status(thm)],
% 7.97/1.51                [c_2231,c_22,c_23,c_886]) ).
% 7.97/1.51  
% 7.97/1.51  cnf(c_8,plain,
% 7.97/1.51      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 7.97/1.51      inference(cnf_transformation,[],[f54]) ).
% 7.97/1.51  
% 7.97/1.51  cnf(c_703,plain,
% 7.97/1.51      ( r1_tarski(X0,X1) != iProver_top
% 7.97/1.51      | m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top ),
% 7.97/1.51      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.97/1.51  
% 7.97/1.51  cnf(c_3,plain,
% 7.97/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.97/1.51      | k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))) = k3_subset_1(X1,X0) ),
% 7.97/1.51      inference(cnf_transformation,[],[f68]) ).
% 7.97/1.51  
% 7.97/1.51  cnf(c_708,plain,
% 7.97/1.51      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k3_subset_1(X0,X1)
% 7.97/1.51      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 7.97/1.51      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.97/1.51  
% 7.97/1.51  cnf(c_3445,plain,
% 7.97/1.51      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k3_subset_1(X0,X1)
% 7.97/1.51      | r1_tarski(X1,X0) != iProver_top ),
% 7.97/1.51      inference(superposition,[status(thm)],[c_703,c_708]) ).
% 7.97/1.51  
% 7.97/1.51  cnf(c_7263,plain,
% 7.97/1.51      ( k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1)))) = k3_subset_1(sK1,k1_tops_1(sK0,sK1)) ),
% 7.97/1.51      inference(superposition,[status(thm)],[c_3009,c_3445]) ).
% 7.97/1.51  
% 7.97/1.51  cnf(c_7866,plain,
% 7.97/1.51      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k3_subset_1(sK1,k1_tops_1(sK0,sK1)) ),
% 7.97/1.51      inference(superposition,[status(thm)],[c_3522,c_7263]) ).
% 7.97/1.51  
% 7.97/1.51  cnf(c_7881,plain,
% 7.97/1.51      ( k2_pre_topc(sK0,sK1) = sK1
% 7.97/1.51      | k3_subset_1(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 7.97/1.51      inference(superposition,[status(thm)],[c_5255,c_7866]) ).
% 7.97/1.51  
% 7.97/1.51  cnf(c_4,plain,
% 7.97/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.97/1.51      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 7.97/1.51      inference(cnf_transformation,[],[f49]) ).
% 7.97/1.51  
% 7.97/1.51  cnf(c_707,plain,
% 7.97/1.51      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.97/1.51      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 7.97/1.51      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.97/1.51  
% 7.97/1.51  cnf(c_5,plain,
% 7.97/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.97/1.51      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 7.97/1.51      | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
% 7.97/1.51      inference(cnf_transformation,[],[f50]) ).
% 7.97/1.51  
% 7.97/1.51  cnf(c_706,plain,
% 7.97/1.51      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
% 7.97/1.51      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 7.97/1.51      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
% 7.97/1.51      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.97/1.51  
% 7.97/1.51  cnf(c_3651,plain,
% 7.97/1.51      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
% 7.97/1.51      | r1_tarski(X1,X0) != iProver_top
% 7.97/1.51      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
% 7.97/1.51      inference(superposition,[status(thm)],[c_703,c_706]) ).
% 7.97/1.51  
% 7.97/1.51  cnf(c_9294,plain,
% 7.97/1.51      ( k4_subset_1(X0,X1,k3_subset_1(X0,X2)) = k2_xboole_0(X1,k3_subset_1(X0,X2))
% 7.97/1.51      | r1_tarski(X1,X0) != iProver_top
% 7.97/1.51      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
% 7.97/1.51      inference(superposition,[status(thm)],[c_707,c_3651]) ).
% 7.97/1.51  
% 7.97/1.51  cnf(c_14624,plain,
% 7.97/1.51      ( k4_subset_1(X0,X1,k3_subset_1(X0,X2)) = k2_xboole_0(X1,k3_subset_1(X0,X2))
% 7.97/1.51      | r1_tarski(X2,X0) != iProver_top
% 7.97/1.51      | r1_tarski(X1,X0) != iProver_top ),
% 7.97/1.51      inference(superposition,[status(thm)],[c_703,c_9294]) ).
% 7.97/1.51  
% 7.97/1.51  cnf(c_15537,plain,
% 7.97/1.51      ( k4_subset_1(sK1,k1_tops_1(sK0,sK1),k3_subset_1(sK1,X0)) = k2_xboole_0(k1_tops_1(sK0,sK1),k3_subset_1(sK1,X0))
% 7.97/1.51      | r1_tarski(X0,sK1) != iProver_top ),
% 7.97/1.51      inference(superposition,[status(thm)],[c_3009,c_14624]) ).
% 7.97/1.51  
% 7.97/1.51  cnf(c_16418,plain,
% 7.97/1.51      ( k4_subset_1(sK1,k1_tops_1(sK0,sK1),k3_subset_1(sK1,k1_tops_1(sK0,sK1))) = k2_xboole_0(k1_tops_1(sK0,sK1),k3_subset_1(sK1,k1_tops_1(sK0,sK1))) ),
% 7.97/1.51      inference(superposition,[status(thm)],[c_3009,c_15537]) ).
% 7.97/1.51  
% 7.97/1.51  cnf(c_7,plain,
% 7.97/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.97/1.51      | k4_subset_1(X1,X0,k3_subset_1(X1,X0)) = k2_subset_1(X1) ),
% 7.97/1.51      inference(cnf_transformation,[],[f52]) ).
% 7.97/1.51  
% 7.97/1.51  cnf(c_704,plain,
% 7.97/1.51      ( k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = k2_subset_1(X0)
% 7.97/1.51      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 7.97/1.51      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.97/1.51  
% 7.97/1.51  cnf(c_2,plain,
% 7.97/1.51      ( k2_subset_1(X0) = X0 ),
% 7.97/1.51      inference(cnf_transformation,[],[f47]) ).
% 7.97/1.51  
% 7.97/1.51  cnf(c_733,plain,
% 7.97/1.51      ( k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = X0
% 7.97/1.51      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 7.97/1.51      inference(light_normalisation,[status(thm)],[c_704,c_2]) ).
% 7.97/1.51  
% 7.97/1.51  cnf(c_2725,plain,
% 7.97/1.51      ( k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = X0
% 7.97/1.51      | r1_tarski(X1,X0) != iProver_top ),
% 7.97/1.51      inference(superposition,[status(thm)],[c_703,c_733]) ).
% 7.97/1.51  
% 7.97/1.51  cnf(c_6301,plain,
% 7.97/1.51      ( k4_subset_1(sK1,k1_tops_1(sK0,sK1),k3_subset_1(sK1,k1_tops_1(sK0,sK1))) = sK1 ),
% 7.97/1.51      inference(superposition,[status(thm)],[c_3009,c_2725]) ).
% 7.97/1.51  
% 7.97/1.51  cnf(c_16427,plain,
% 7.97/1.51      ( k2_xboole_0(k1_tops_1(sK0,sK1),k3_subset_1(sK1,k1_tops_1(sK0,sK1))) = sK1 ),
% 7.97/1.51      inference(light_normalisation,[status(thm)],[c_16418,c_6301]) ).
% 7.97/1.51  
% 7.97/1.51  cnf(c_0,plain,
% 7.97/1.51      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 7.97/1.51      inference(cnf_transformation,[],[f44]) ).
% 7.97/1.51  
% 7.97/1.51  cnf(c_1,plain,
% 7.97/1.51      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
% 7.97/1.51      inference(cnf_transformation,[],[f46]) ).
% 7.97/1.51  
% 7.97/1.51  cnf(c_1057,plain,
% 7.97/1.51      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 7.97/1.51      inference(superposition,[status(thm)],[c_0,c_1]) ).
% 7.97/1.51  
% 7.97/1.51  cnf(c_1170,plain,
% 7.97/1.51      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(k2_xboole_0(X0,X1),X0) ),
% 7.97/1.51      inference(superposition,[status(thm)],[c_1,c_1057]) ).
% 7.97/1.51  
% 7.97/1.51  cnf(c_1317,plain,
% 7.97/1.51      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(k2_xboole_0(X1,X0),X1) ),
% 7.97/1.51      inference(superposition,[status(thm)],[c_0,c_1170]) ).
% 7.97/1.51  
% 7.97/1.51  cnf(c_1534,plain,
% 7.97/1.51      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(k2_xboole_0(X1,X0),X1) ),
% 7.97/1.51      inference(superposition,[status(thm)],[c_1317,c_1170]) ).
% 7.97/1.51  
% 7.97/1.51  cnf(c_1683,plain,
% 7.97/1.51      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_xboole_0(X1,X0),X1) ),
% 7.97/1.51      inference(superposition,[status(thm)],[c_1534,c_0]) ).
% 7.97/1.51  
% 7.97/1.51  cnf(c_1685,plain,
% 7.97/1.51      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X1,X0) ),
% 7.97/1.51      inference(light_normalisation,[status(thm)],[c_1683,c_1]) ).
% 7.97/1.51  
% 7.97/1.51  cnf(c_1733,plain,
% 7.97/1.51      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
% 7.97/1.51      inference(superposition,[status(thm)],[c_1685,c_0]) ).
% 7.97/1.51  
% 7.97/1.51  cnf(c_2059,plain,
% 7.97/1.51      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 7.97/1.51      inference(superposition,[status(thm)],[c_0,c_1733]) ).
% 7.97/1.51  
% 7.97/1.51  cnf(c_18006,plain,
% 7.97/1.51      ( k2_xboole_0(k1_tops_1(sK0,sK1),k3_subset_1(sK1,k1_tops_1(sK0,sK1))) = k2_xboole_0(k3_subset_1(sK1,k1_tops_1(sK0,sK1)),sK1) ),
% 7.97/1.51      inference(superposition,[status(thm)],[c_16427,c_2059]) ).
% 7.97/1.51  
% 7.97/1.51  cnf(c_18010,plain,
% 7.97/1.51      ( k2_xboole_0(k3_subset_1(sK1,k1_tops_1(sK0,sK1)),sK1) = sK1 ),
% 7.97/1.51      inference(light_normalisation,[status(thm)],[c_18006,c_16427]) ).
% 7.97/1.51  
% 7.97/1.51  cnf(c_28781,plain,
% 7.97/1.51      ( k2_pre_topc(sK0,sK1) = sK1
% 7.97/1.51      | k2_xboole_0(k2_tops_1(sK0,sK1),sK1) = sK1 ),
% 7.97/1.51      inference(superposition,[status(thm)],[c_7881,c_18010]) ).
% 7.97/1.51  
% 7.97/1.51  cnf(c_11,plain,
% 7.97/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.97/1.51      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.97/1.51      | ~ l1_pre_topc(X1) ),
% 7.97/1.51      inference(cnf_transformation,[],[f57]) ).
% 7.97/1.51  
% 7.97/1.51  cnf(c_700,plain,
% 7.97/1.51      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 7.97/1.51      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 7.97/1.51      | l1_pre_topc(X1) != iProver_top ),
% 7.97/1.51      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.97/1.51  
% 7.97/1.51  cnf(c_3654,plain,
% 7.97/1.51      ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k2_xboole_0(sK1,X0)
% 7.97/1.51      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.97/1.51      inference(superposition,[status(thm)],[c_693,c_706]) ).
% 7.97/1.51  
% 7.97/1.51  cnf(c_3776,plain,
% 7.97/1.51      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0))
% 7.97/1.51      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.97/1.51      | l1_pre_topc(sK0) != iProver_top ),
% 7.97/1.51      inference(superposition,[status(thm)],[c_700,c_3654]) ).
% 7.97/1.51  
% 7.97/1.51  cnf(c_5849,plain,
% 7.97/1.51      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.97/1.51      | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0)) ),
% 7.97/1.51      inference(global_propositional_subsumption,
% 7.97/1.51                [status(thm)],
% 7.97/1.51                [c_3776,c_22]) ).
% 7.97/1.51  
% 7.97/1.51  cnf(c_5850,plain,
% 7.97/1.51      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0))
% 7.97/1.51      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.97/1.51      inference(renaming,[status(thm)],[c_5849]) ).
% 7.97/1.51  
% 7.97/1.51  cnf(c_5860,plain,
% 7.97/1.51      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
% 7.97/1.51      inference(superposition,[status(thm)],[c_693,c_5850]) ).
% 7.97/1.51  
% 7.97/1.51  cnf(c_15,plain,
% 7.97/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.97/1.51      | ~ l1_pre_topc(X1)
% 7.97/1.51      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
% 7.97/1.51      inference(cnf_transformation,[],[f61]) ).
% 7.97/1.51  
% 7.97/1.51  cnf(c_696,plain,
% 7.97/1.51      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
% 7.97/1.51      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.97/1.51      | l1_pre_topc(X0) != iProver_top ),
% 7.97/1.51      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.97/1.51  
% 7.97/1.51  cnf(c_1165,plain,
% 7.97/1.51      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
% 7.97/1.51      | l1_pre_topc(sK0) != iProver_top ),
% 7.97/1.51      inference(superposition,[status(thm)],[c_693,c_696]) ).
% 7.97/1.51  
% 7.97/1.51  cnf(c_965,plain,
% 7.97/1.51      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.97/1.51      | ~ l1_pre_topc(sK0)
% 7.97/1.51      | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 7.97/1.51      inference(instantiation,[status(thm)],[c_15]) ).
% 7.97/1.51  
% 7.97/1.51  cnf(c_1555,plain,
% 7.97/1.51      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 7.97/1.51      inference(global_propositional_subsumption,
% 7.97/1.51                [status(thm)],
% 7.97/1.51                [c_1165,c_19,c_18,c_965]) ).
% 7.97/1.51  
% 7.97/1.51  cnf(c_5862,plain,
% 7.97/1.51      ( k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 7.97/1.51      inference(light_normalisation,[status(thm)],[c_5860,c_1555]) ).
% 7.97/1.51  
% 7.97/1.51  cnf(c_5967,plain,
% 7.97/1.51      ( k2_xboole_0(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
% 7.97/1.51      inference(superposition,[status(thm)],[c_5862,c_2059]) ).
% 7.97/1.51  
% 7.97/1.51  cnf(c_5968,plain,
% 7.97/1.51      ( k2_xboole_0(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1)) = k2_xboole_0(k2_tops_1(sK0,sK1),sK1) ),
% 7.97/1.51      inference(superposition,[status(thm)],[c_5862,c_1057]) ).
% 7.97/1.51  
% 7.97/1.51  cnf(c_5971,plain,
% 7.97/1.51      ( k2_xboole_0(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 7.97/1.51      inference(light_normalisation,[status(thm)],[c_5967,c_5862,c_5968]) ).
% 7.97/1.51  
% 7.97/1.51  cnf(c_5973,plain,
% 7.97/1.51      ( k2_xboole_0(k2_tops_1(sK0,sK1),sK1) = k2_pre_topc(sK0,sK1) ),
% 7.97/1.51      inference(demodulation,[status(thm)],[c_5971,c_5968]) ).
% 7.97/1.51  
% 7.97/1.51  cnf(c_28814,plain,
% 7.97/1.51      ( k2_pre_topc(sK0,sK1) = sK1 ),
% 7.97/1.51      inference(demodulation,[status(thm)],[c_28781,c_5973]) ).
% 7.97/1.51  
% 7.97/1.51  cnf(c_13,plain,
% 7.97/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.97/1.51      | ~ l1_pre_topc(X1)
% 7.97/1.51      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
% 7.97/1.51      inference(cnf_transformation,[],[f59]) ).
% 7.97/1.51  
% 7.97/1.51  cnf(c_698,plain,
% 7.97/1.51      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
% 7.97/1.51      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.97/1.51      | l1_pre_topc(X0) != iProver_top ),
% 7.97/1.51      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.97/1.51  
% 7.97/1.51  cnf(c_3418,plain,
% 7.97/1.51      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 7.97/1.51      | l1_pre_topc(sK0) != iProver_top ),
% 7.97/1.51      inference(superposition,[status(thm)],[c_693,c_698]) ).
% 7.97/1.51  
% 7.97/1.51  cnf(c_968,plain,
% 7.97/1.51      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.97/1.51      | ~ l1_pre_topc(sK0)
% 7.97/1.51      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 7.97/1.51      inference(instantiation,[status(thm)],[c_13]) ).
% 7.97/1.51  
% 7.97/1.51  cnf(c_4088,plain,
% 7.97/1.51      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 7.97/1.51      inference(global_propositional_subsumption,
% 7.97/1.51                [status(thm)],
% 7.97/1.51                [c_3418,c_19,c_18,c_968]) ).
% 7.97/1.51  
% 7.97/1.51  cnf(c_28830,plain,
% 7.97/1.51      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 7.97/1.51      inference(demodulation,[status(thm)],[c_28814,c_4088]) ).
% 7.97/1.51  
% 7.97/1.51  cnf(c_9,plain,
% 7.97/1.51      ( v4_pre_topc(X0,X1)
% 7.97/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.97/1.51      | ~ l1_pre_topc(X1)
% 7.97/1.51      | ~ v2_pre_topc(X1)
% 7.97/1.51      | k2_pre_topc(X1,X0) != X0 ),
% 7.97/1.51      inference(cnf_transformation,[],[f56]) ).
% 7.97/1.51  
% 7.97/1.51  cnf(c_962,plain,
% 7.97/1.51      ( v4_pre_topc(sK1,sK0)
% 7.97/1.51      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.97/1.51      | ~ l1_pre_topc(sK0)
% 7.97/1.51      | ~ v2_pre_topc(sK0)
% 7.97/1.51      | k2_pre_topc(sK0,sK1) != sK1 ),
% 7.97/1.51      inference(instantiation,[status(thm)],[c_9]) ).
% 7.97/1.51  
% 7.97/1.51  cnf(c_16,negated_conjecture,
% 7.97/1.51      ( ~ v4_pre_topc(sK1,sK0)
% 7.97/1.51      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
% 7.97/1.51      inference(cnf_transformation,[],[f66]) ).
% 7.97/1.51  
% 7.97/1.51  cnf(c_20,negated_conjecture,
% 7.97/1.51      ( v2_pre_topc(sK0) ),
% 7.97/1.51      inference(cnf_transformation,[],[f62]) ).
% 7.97/1.51  
% 7.97/1.51  cnf(contradiction,plain,
% 7.97/1.51      ( $false ),
% 7.97/1.51      inference(minisat,
% 7.97/1.51                [status(thm)],
% 7.97/1.51                [c_28830,c_28814,c_962,c_16,c_18,c_19,c_20]) ).
% 7.97/1.51  
% 7.97/1.51  
% 7.97/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 7.97/1.51  
% 7.97/1.51  ------                               Statistics
% 7.97/1.51  
% 7.97/1.51  ------ Selected
% 7.97/1.51  
% 7.97/1.51  total_time:                             1.012
% 7.97/1.51  
%------------------------------------------------------------------------------
