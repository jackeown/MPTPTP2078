%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:14:48 EST 2020

% Result     : Theorem 39.50s
% Output     : CNFRefutation 39.50s
% Verified   : 
% Statistics : Number of formulae       :  183 (2143 expanded)
%              Number of clauses        :  105 ( 716 expanded)
%              Number of leaves         :   21 ( 472 expanded)
%              Depth                    :   21
%              Number of atoms          :  437 (6673 expanded)
%              Number of equality atoms :  222 (2366 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   2 average)

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

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

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
    inference(nnf_transformation,[],[f36])).

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

fof(f67,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f43])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f75,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f51,f46])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f74,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f50,f46])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f56,f46])).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f66,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f53,f46])).

fof(f69,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f15,axiom,(
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
    inference(ennf_transformation,[],[f15])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f11,axiom,(
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
    inference(ennf_transformation,[],[f11])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f24])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f8,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f70,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f52,f46])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f55,f70])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f68,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => r1_tarski(k2_tops_1(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_tops_1(X0,X1),X1)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f45,f46])).

fof(f65,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f43])).

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
    inference(ennf_transformation,[],[f14])).

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

fof(f60,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) != X1
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f73,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
    inference(definition_unfolding,[],[f47,f70])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f44,f46])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_848,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_857,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2222,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_848,c_857])).

cnf(c_6,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_5,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_859,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1455,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_859])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X0,k3_xboole_0(X0,X2)) = k7_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_11,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_164,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_11])).

cnf(c_165,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_164])).

cnf(c_209,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X2)) = k7_subset_1(X1,X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_10,c_165])).

cnf(c_842,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k7_subset_1(X2,X0,X1)
    | r1_tarski(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_209])).

cnf(c_1467,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k7_subset_1(X0,X0,X1) ),
    inference(superposition,[status(thm)],[c_1455,c_842])).

cnf(c_1963,plain,
    ( k7_subset_1(X0,X0,X1) = k7_subset_1(X2,X0,X1)
    | r1_tarski(X0,X2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1467,c_842])).

cnf(c_6685,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) ),
    inference(superposition,[status(thm)],[c_2222,c_1963])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_851,plain,
    ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3577,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_848,c_851])).

cnf(c_22,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1178,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_3815,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3577,c_22,c_21,c_1178])).

cnf(c_7046,plain,
    ( k7_subset_1(sK1,sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_6685,c_3815])).

cnf(c_1962,plain,
    ( r1_tarski(k7_subset_1(X0,X0,X1),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1467,c_859])).

cnf(c_7607,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_7046,c_1962])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_206,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_7,c_165])).

cnf(c_845,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_206])).

cnf(c_6708,plain,
    ( k7_subset_1(X0,X0,X1) = k3_subset_1(X0,X1)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_845,c_1467])).

cnf(c_11826,plain,
    ( k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) = k3_subset_1(sK1,k1_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_7607,c_6708])).

cnf(c_19,negated_conjecture,
    ( ~ v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_850,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_7023,plain,
    ( k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6685,c_850])).

cnf(c_138896,plain,
    ( k3_subset_1(sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11826,c_7023])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_854,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k5_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X0))) = k4_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_208,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,X1)
    | k5_xboole_0(X2,k5_xboole_0(X0,k3_xboole_0(X0,X2))) = k4_subset_1(X1,X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_9,c_165])).

cnf(c_843,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k4_subset_1(X2,X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
    | r1_tarski(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_208])).

cnf(c_2104,plain,
    ( k5_xboole_0(X0,k7_subset_1(X1,X1,X0)) = k4_subset_1(X2,X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
    | r1_tarski(X0,X2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_843,c_1467])).

cnf(c_3393,plain,
    ( k5_xboole_0(X0,k7_subset_1(k2_tops_1(X1,X2),k2_tops_1(X1,X2),X0)) = k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X2))
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(X0,u1_struct_0(X1)) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_854,c_2104])).

cnf(c_13925,plain,
    ( k5_xboole_0(X0,k7_subset_1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),X0)) = k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,sK1))
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_848,c_3393])).

cnf(c_25,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_14661,plain,
    ( r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
    | k5_xboole_0(X0,k7_subset_1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),X0)) = k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13925,c_25])).

cnf(c_14662,plain,
    ( k5_xboole_0(X0,k7_subset_1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),X0)) = k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,sK1))
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_14661])).

cnf(c_14672,plain,
    ( k5_xboole_0(sK1,k7_subset_1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),sK1)) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_2222,c_14662])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_853,plain,
    ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3607,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_848,c_853])).

cnf(c_1175,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_3893,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3607,c_22,c_21,c_1175])).

cnf(c_20,negated_conjecture,
    ( v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_849,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_7022,plain,
    ( k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6685,c_849])).

cnf(c_17,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k2_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_852,plain,
    ( v4_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(k2_tops_1(X1,X0),X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3368,plain,
    ( v4_pre_topc(sK1,sK0) != iProver_top
    | r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_848,c_852])).

cnf(c_4088,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3368,c_25])).

cnf(c_4089,plain,
    ( v4_pre_topc(sK1,sK0) != iProver_top
    | r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(renaming,[status(thm)],[c_4088])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_863,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2384,plain,
    ( k7_subset_1(X0,X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_863,c_1467])).

cnf(c_4094,plain,
    ( k7_subset_1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),sK1) = k1_xboole_0
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4089,c_2384])).

cnf(c_7334,plain,
    ( k7_subset_1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),sK1) = k1_xboole_0
    | k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_7022,c_4094])).

cnf(c_23,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_24,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_26,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_13,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | k2_pre_topc(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1172,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | k2_pre_topc(sK0,sK1) != sK1 ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1173,plain,
    ( k2_pre_topc(sK0,sK1) != sK1
    | v4_pre_topc(sK1,sK0) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1172])).

cnf(c_14,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_855,plain,
    ( k2_pre_topc(X0,X1) = X1
    | v4_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3784,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | v4_pre_topc(sK1,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_848,c_855])).

cnf(c_3897,plain,
    ( v4_pre_topc(sK1,sK0) != iProver_top
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3784,c_25])).

cnf(c_3898,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3897])).

cnf(c_3903,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_849,c_3898])).

cnf(c_7045,plain,
    ( k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_6685,c_3903])).

cnf(c_4671,plain,
    ( k7_subset_1(k7_subset_1(X0,X0,X1),k7_subset_1(X0,X0,X1),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1962,c_2384])).

cnf(c_8630,plain,
    ( k7_subset_1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),sK1) = k1_xboole_0
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_7045,c_4671])).

cnf(c_10630,plain,
    ( k7_subset_1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7334,c_24,c_25,c_26,c_1173,c_4094,c_8630])).

cnf(c_14683,plain,
    ( k2_pre_topc(sK0,sK1) = k5_xboole_0(sK1,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_14672,c_3893,c_10630])).

cnf(c_4,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_860,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_861,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1591,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_860,c_861])).

cnf(c_2,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1604,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) = X0 ),
    inference(demodulation,[status(thm)],[c_1591,c_2])).

cnf(c_1193,plain,
    ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6,c_2])).

cnf(c_1605,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1604,c_1193])).

cnf(c_14684,plain,
    ( k2_pre_topc(sK0,sK1) = sK1 ),
    inference(demodulation,[status(thm)],[c_14683,c_1605])).

cnf(c_1,plain,
    ( r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_862,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2370,plain,
    ( k7_subset_1(X0,X0,X1) != k1_xboole_0
    | r1_tarski(X0,X1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_862,c_1467])).

cnf(c_10650,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_10630,c_2370])).

cnf(c_11863,plain,
    ( k7_subset_1(sK1,sK1,k2_tops_1(sK0,sK1)) = k3_subset_1(sK1,k2_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_10650,c_6708])).

cnf(c_11882,plain,
    ( k3_subset_1(sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_11863,c_7046])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_207,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(bin_hyper_res,[status(thm)],[c_8,c_165])).

cnf(c_844,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_207])).

cnf(c_11864,plain,
    ( k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1))) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_10650,c_844])).

cnf(c_11883,plain,
    ( k3_subset_1(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_11882,c_11864])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_138896,c_14684,c_11883,c_1173,c_26,c_25,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:18:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 39.50/5.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 39.50/5.49  
% 39.50/5.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 39.50/5.49  
% 39.50/5.49  ------  iProver source info
% 39.50/5.49  
% 39.50/5.49  git: date: 2020-06-30 10:37:57 +0100
% 39.50/5.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 39.50/5.49  git: non_committed_changes: false
% 39.50/5.49  git: last_make_outside_of_git: false
% 39.50/5.49  
% 39.50/5.49  ------ 
% 39.50/5.49  ------ Parsing...
% 39.50/5.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 39.50/5.49  
% 39.50/5.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 39.50/5.49  
% 39.50/5.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 39.50/5.49  
% 39.50/5.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 39.50/5.49  ------ Proving...
% 39.50/5.49  ------ Problem Properties 
% 39.50/5.49  
% 39.50/5.49  
% 39.50/5.49  clauses                                 24
% 39.50/5.49  conjectures                             5
% 39.50/5.49  EPR                                     3
% 39.50/5.49  Horn                                    23
% 39.50/5.49  unary                                   7
% 39.50/5.49  binary                                  10
% 39.50/5.49  lits                                    52
% 39.50/5.49  lits eq                                 15
% 39.50/5.49  fd_pure                                 0
% 39.50/5.49  fd_pseudo                               0
% 39.50/5.49  fd_cond                                 0
% 39.50/5.49  fd_pseudo_cond                          0
% 39.50/5.49  AC symbols                              0
% 39.50/5.49  
% 39.50/5.49  ------ Input Options Time Limit: Unbounded
% 39.50/5.49  
% 39.50/5.49  
% 39.50/5.49  ------ 
% 39.50/5.49  Current options:
% 39.50/5.49  ------ 
% 39.50/5.49  
% 39.50/5.49  
% 39.50/5.49  
% 39.50/5.49  
% 39.50/5.49  ------ Proving...
% 39.50/5.49  
% 39.50/5.49  
% 39.50/5.49  % SZS status Theorem for theBenchmark.p
% 39.50/5.49  
% 39.50/5.49  % SZS output start CNFRefutation for theBenchmark.p
% 39.50/5.49  
% 39.50/5.49  fof(f19,conjecture,(
% 39.50/5.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 39.50/5.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.50/5.49  
% 39.50/5.49  fof(f20,negated_conjecture,(
% 39.50/5.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 39.50/5.49    inference(negated_conjecture,[],[f19])).
% 39.50/5.49  
% 39.50/5.49  fof(f35,plain,(
% 39.50/5.49    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 39.50/5.49    inference(ennf_transformation,[],[f20])).
% 39.50/5.49  
% 39.50/5.49  fof(f36,plain,(
% 39.50/5.49    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 39.50/5.49    inference(flattening,[],[f35])).
% 39.50/5.49  
% 39.50/5.49  fof(f39,plain,(
% 39.50/5.49    ? [X0] : (? [X1] : (((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 39.50/5.49    inference(nnf_transformation,[],[f36])).
% 39.50/5.49  
% 39.50/5.49  fof(f40,plain,(
% 39.50/5.49    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 39.50/5.49    inference(flattening,[],[f39])).
% 39.50/5.49  
% 39.50/5.49  fof(f42,plain,(
% 39.50/5.49    ( ! [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) != k2_tops_1(X0,sK1) | ~v4_pre_topc(sK1,X0)) & (k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) = k2_tops_1(X0,sK1) | v4_pre_topc(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 39.50/5.49    introduced(choice_axiom,[])).
% 39.50/5.49  
% 39.50/5.49  fof(f41,plain,(
% 39.50/5.49    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) != k2_tops_1(sK0,X1) | ~v4_pre_topc(X1,sK0)) & (k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) = k2_tops_1(sK0,X1) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 39.50/5.49    introduced(choice_axiom,[])).
% 39.50/5.49  
% 39.50/5.49  fof(f43,plain,(
% 39.50/5.49    ((k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)) & (k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 39.50/5.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f40,f42,f41])).
% 39.50/5.49  
% 39.50/5.49  fof(f67,plain,(
% 39.50/5.49    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 39.50/5.49    inference(cnf_transformation,[],[f43])).
% 39.50/5.49  
% 39.50/5.49  fof(f13,axiom,(
% 39.50/5.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 39.50/5.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.50/5.49  
% 39.50/5.49  fof(f38,plain,(
% 39.50/5.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 39.50/5.49    inference(nnf_transformation,[],[f13])).
% 39.50/5.49  
% 39.50/5.49  fof(f57,plain,(
% 39.50/5.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 39.50/5.49    inference(cnf_transformation,[],[f38])).
% 39.50/5.49  
% 39.50/5.49  fof(f7,axiom,(
% 39.50/5.49    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 39.50/5.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.50/5.49  
% 39.50/5.49  fof(f51,plain,(
% 39.50/5.49    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 39.50/5.49    inference(cnf_transformation,[],[f7])).
% 39.50/5.49  
% 39.50/5.49  fof(f2,axiom,(
% 39.50/5.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 39.50/5.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.50/5.49  
% 39.50/5.49  fof(f46,plain,(
% 39.50/5.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 39.50/5.49    inference(cnf_transformation,[],[f2])).
% 39.50/5.49  
% 39.50/5.49  fof(f75,plain,(
% 39.50/5.49    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 39.50/5.49    inference(definition_unfolding,[],[f51,f46])).
% 39.50/5.49  
% 39.50/5.49  fof(f6,axiom,(
% 39.50/5.49    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 39.50/5.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.50/5.49  
% 39.50/5.49  fof(f50,plain,(
% 39.50/5.49    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 39.50/5.49    inference(cnf_transformation,[],[f6])).
% 39.50/5.49  
% 39.50/5.49  fof(f74,plain,(
% 39.50/5.49    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 39.50/5.49    inference(definition_unfolding,[],[f50,f46])).
% 39.50/5.49  
% 39.50/5.49  fof(f12,axiom,(
% 39.50/5.49    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 39.50/5.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.50/5.49  
% 39.50/5.49  fof(f26,plain,(
% 39.50/5.49    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 39.50/5.49    inference(ennf_transformation,[],[f12])).
% 39.50/5.49  
% 39.50/5.49  fof(f56,plain,(
% 39.50/5.49    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 39.50/5.49    inference(cnf_transformation,[],[f26])).
% 39.50/5.49  
% 39.50/5.49  fof(f78,plain,(
% 39.50/5.49    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 39.50/5.49    inference(definition_unfolding,[],[f56,f46])).
% 39.50/5.49  
% 39.50/5.49  fof(f58,plain,(
% 39.50/5.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 39.50/5.49    inference(cnf_transformation,[],[f38])).
% 39.50/5.49  
% 39.50/5.49  fof(f18,axiom,(
% 39.50/5.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)))),
% 39.50/5.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.50/5.49  
% 39.50/5.49  fof(f34,plain,(
% 39.50/5.49    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 39.50/5.49    inference(ennf_transformation,[],[f18])).
% 39.50/5.49  
% 39.50/5.49  fof(f64,plain,(
% 39.50/5.49    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 39.50/5.49    inference(cnf_transformation,[],[f34])).
% 39.50/5.49  
% 39.50/5.49  fof(f66,plain,(
% 39.50/5.49    l1_pre_topc(sK0)),
% 39.50/5.49    inference(cnf_transformation,[],[f43])).
% 39.50/5.49  
% 39.50/5.49  fof(f9,axiom,(
% 39.50/5.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 39.50/5.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.50/5.49  
% 39.50/5.49  fof(f22,plain,(
% 39.50/5.49    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 39.50/5.49    inference(ennf_transformation,[],[f9])).
% 39.50/5.49  
% 39.50/5.49  fof(f53,plain,(
% 39.50/5.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 39.50/5.49    inference(cnf_transformation,[],[f22])).
% 39.50/5.49  
% 39.50/5.49  fof(f76,plain,(
% 39.50/5.49    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 39.50/5.49    inference(definition_unfolding,[],[f53,f46])).
% 39.50/5.49  
% 39.50/5.49  fof(f69,plain,(
% 39.50/5.49    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)),
% 39.50/5.49    inference(cnf_transformation,[],[f43])).
% 39.50/5.49  
% 39.50/5.49  fof(f15,axiom,(
% 39.50/5.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 39.50/5.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.50/5.49  
% 39.50/5.49  fof(f29,plain,(
% 39.50/5.49    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 39.50/5.49    inference(ennf_transformation,[],[f15])).
% 39.50/5.49  
% 39.50/5.49  fof(f30,plain,(
% 39.50/5.49    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 39.50/5.49    inference(flattening,[],[f29])).
% 39.50/5.49  
% 39.50/5.49  fof(f61,plain,(
% 39.50/5.49    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 39.50/5.49    inference(cnf_transformation,[],[f30])).
% 39.50/5.49  
% 39.50/5.49  fof(f11,axiom,(
% 39.50/5.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 39.50/5.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.50/5.49  
% 39.50/5.49  fof(f24,plain,(
% 39.50/5.49    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 39.50/5.49    inference(ennf_transformation,[],[f11])).
% 39.50/5.49  
% 39.50/5.49  fof(f25,plain,(
% 39.50/5.49    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 39.50/5.49    inference(flattening,[],[f24])).
% 39.50/5.49  
% 39.50/5.49  fof(f55,plain,(
% 39.50/5.49    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 39.50/5.49    inference(cnf_transformation,[],[f25])).
% 39.50/5.49  
% 39.50/5.49  fof(f8,axiom,(
% 39.50/5.49    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 39.50/5.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.50/5.49  
% 39.50/5.49  fof(f52,plain,(
% 39.50/5.49    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 39.50/5.49    inference(cnf_transformation,[],[f8])).
% 39.50/5.49  
% 39.50/5.49  fof(f70,plain,(
% 39.50/5.49    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 39.50/5.49    inference(definition_unfolding,[],[f52,f46])).
% 39.50/5.49  
% 39.50/5.49  fof(f77,plain,(
% 39.50/5.49    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 39.50/5.49    inference(definition_unfolding,[],[f55,f70])).
% 39.50/5.49  
% 39.50/5.49  fof(f16,axiom,(
% 39.50/5.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)))),
% 39.50/5.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.50/5.49  
% 39.50/5.49  fof(f31,plain,(
% 39.50/5.49    ! [X0] : (! [X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 39.50/5.49    inference(ennf_transformation,[],[f16])).
% 39.50/5.49  
% 39.50/5.49  fof(f62,plain,(
% 39.50/5.49    ( ! [X0,X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 39.50/5.49    inference(cnf_transformation,[],[f31])).
% 39.50/5.49  
% 39.50/5.49  fof(f68,plain,(
% 39.50/5.49    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)),
% 39.50/5.49    inference(cnf_transformation,[],[f43])).
% 39.50/5.49  
% 39.50/5.49  fof(f17,axiom,(
% 39.50/5.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => r1_tarski(k2_tops_1(X0,X1),X1))))),
% 39.50/5.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.50/5.49  
% 39.50/5.49  fof(f32,plain,(
% 39.50/5.49    ! [X0] : (! [X1] : ((r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 39.50/5.49    inference(ennf_transformation,[],[f17])).
% 39.50/5.49  
% 39.50/5.49  fof(f33,plain,(
% 39.50/5.49    ! [X0] : (! [X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 39.50/5.49    inference(flattening,[],[f32])).
% 39.50/5.49  
% 39.50/5.49  fof(f63,plain,(
% 39.50/5.49    ( ! [X0,X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 39.50/5.49    inference(cnf_transformation,[],[f33])).
% 39.50/5.49  
% 39.50/5.49  fof(f1,axiom,(
% 39.50/5.49    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 39.50/5.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.50/5.49  
% 39.50/5.49  fof(f37,plain,(
% 39.50/5.49    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 39.50/5.49    inference(nnf_transformation,[],[f1])).
% 39.50/5.49  
% 39.50/5.49  fof(f45,plain,(
% 39.50/5.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 39.50/5.49    inference(cnf_transformation,[],[f37])).
% 39.50/5.49  
% 39.50/5.49  fof(f71,plain,(
% 39.50/5.49    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) | ~r1_tarski(X0,X1)) )),
% 39.50/5.49    inference(definition_unfolding,[],[f45,f46])).
% 39.50/5.49  
% 39.50/5.49  fof(f65,plain,(
% 39.50/5.49    v2_pre_topc(sK0)),
% 39.50/5.49    inference(cnf_transformation,[],[f43])).
% 39.50/5.49  
% 39.50/5.49  fof(f14,axiom,(
% 39.50/5.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 39.50/5.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.50/5.49  
% 39.50/5.49  fof(f27,plain,(
% 39.50/5.49    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 39.50/5.49    inference(ennf_transformation,[],[f14])).
% 39.50/5.49  
% 39.50/5.49  fof(f28,plain,(
% 39.50/5.49    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 39.50/5.49    inference(flattening,[],[f27])).
% 39.50/5.49  
% 39.50/5.49  fof(f60,plain,(
% 39.50/5.49    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 39.50/5.49    inference(cnf_transformation,[],[f28])).
% 39.50/5.49  
% 39.50/5.49  fof(f59,plain,(
% 39.50/5.49    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 39.50/5.49    inference(cnf_transformation,[],[f28])).
% 39.50/5.49  
% 39.50/5.49  fof(f5,axiom,(
% 39.50/5.49    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 39.50/5.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.50/5.49  
% 39.50/5.49  fof(f49,plain,(
% 39.50/5.49    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 39.50/5.49    inference(cnf_transformation,[],[f5])).
% 39.50/5.49  
% 39.50/5.49  fof(f4,axiom,(
% 39.50/5.49    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 39.50/5.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.50/5.49  
% 39.50/5.49  fof(f21,plain,(
% 39.50/5.49    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 39.50/5.49    inference(ennf_transformation,[],[f4])).
% 39.50/5.49  
% 39.50/5.49  fof(f48,plain,(
% 39.50/5.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 39.50/5.49    inference(cnf_transformation,[],[f21])).
% 39.50/5.49  
% 39.50/5.49  fof(f3,axiom,(
% 39.50/5.49    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 39.50/5.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.50/5.49  
% 39.50/5.49  fof(f47,plain,(
% 39.50/5.49    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 39.50/5.49    inference(cnf_transformation,[],[f3])).
% 39.50/5.49  
% 39.50/5.49  fof(f73,plain,(
% 39.50/5.49    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0) )),
% 39.50/5.49    inference(definition_unfolding,[],[f47,f70])).
% 39.50/5.49  
% 39.50/5.49  fof(f44,plain,(
% 39.50/5.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 39.50/5.49    inference(cnf_transformation,[],[f37])).
% 39.50/5.49  
% 39.50/5.49  fof(f72,plain,(
% 39.50/5.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 39.50/5.49    inference(definition_unfolding,[],[f44,f46])).
% 39.50/5.49  
% 39.50/5.49  fof(f10,axiom,(
% 39.50/5.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 39.50/5.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.50/5.49  
% 39.50/5.49  fof(f23,plain,(
% 39.50/5.49    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 39.50/5.49    inference(ennf_transformation,[],[f10])).
% 39.50/5.49  
% 39.50/5.49  fof(f54,plain,(
% 39.50/5.49    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 39.50/5.49    inference(cnf_transformation,[],[f23])).
% 39.50/5.49  
% 39.50/5.49  cnf(c_21,negated_conjecture,
% 39.50/5.49      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 39.50/5.49      inference(cnf_transformation,[],[f67]) ).
% 39.50/5.49  
% 39.50/5.49  cnf(c_848,plain,
% 39.50/5.49      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 39.50/5.49      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 39.50/5.49  
% 39.50/5.49  cnf(c_12,plain,
% 39.50/5.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 39.50/5.49      inference(cnf_transformation,[],[f57]) ).
% 39.50/5.49  
% 39.50/5.49  cnf(c_857,plain,
% 39.50/5.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 39.50/5.49      | r1_tarski(X0,X1) = iProver_top ),
% 39.50/5.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 39.50/5.49  
% 39.50/5.49  cnf(c_2222,plain,
% 39.50/5.49      ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
% 39.50/5.49      inference(superposition,[status(thm)],[c_848,c_857]) ).
% 39.50/5.49  
% 39.50/5.49  cnf(c_6,plain,
% 39.50/5.49      ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
% 39.50/5.49      inference(cnf_transformation,[],[f75]) ).
% 39.50/5.49  
% 39.50/5.49  cnf(c_5,plain,
% 39.50/5.49      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
% 39.50/5.49      inference(cnf_transformation,[],[f74]) ).
% 39.50/5.49  
% 39.50/5.49  cnf(c_859,plain,
% 39.50/5.49      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
% 39.50/5.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 39.50/5.49  
% 39.50/5.49  cnf(c_1455,plain,
% 39.50/5.49      ( r1_tarski(X0,X0) = iProver_top ),
% 39.50/5.49      inference(superposition,[status(thm)],[c_6,c_859]) ).
% 39.50/5.49  
% 39.50/5.49  cnf(c_10,plain,
% 39.50/5.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 39.50/5.49      | k5_xboole_0(X0,k3_xboole_0(X0,X2)) = k7_subset_1(X1,X0,X2) ),
% 39.50/5.49      inference(cnf_transformation,[],[f78]) ).
% 39.50/5.49  
% 39.50/5.49  cnf(c_11,plain,
% 39.50/5.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 39.50/5.49      inference(cnf_transformation,[],[f58]) ).
% 39.50/5.49  
% 39.50/5.49  cnf(c_164,plain,
% 39.50/5.49      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 39.50/5.49      inference(prop_impl,[status(thm)],[c_11]) ).
% 39.50/5.49  
% 39.50/5.49  cnf(c_165,plain,
% 39.50/5.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 39.50/5.49      inference(renaming,[status(thm)],[c_164]) ).
% 39.50/5.49  
% 39.50/5.49  cnf(c_209,plain,
% 39.50/5.49      ( ~ r1_tarski(X0,X1)
% 39.50/5.49      | k5_xboole_0(X0,k3_xboole_0(X0,X2)) = k7_subset_1(X1,X0,X2) ),
% 39.50/5.49      inference(bin_hyper_res,[status(thm)],[c_10,c_165]) ).
% 39.50/5.49  
% 39.50/5.49  cnf(c_842,plain,
% 39.50/5.49      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k7_subset_1(X2,X0,X1)
% 39.50/5.49      | r1_tarski(X0,X2) != iProver_top ),
% 39.50/5.49      inference(predicate_to_equality,[status(thm)],[c_209]) ).
% 39.50/5.49  
% 39.50/5.49  cnf(c_1467,plain,
% 39.50/5.49      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k7_subset_1(X0,X0,X1) ),
% 39.50/5.49      inference(superposition,[status(thm)],[c_1455,c_842]) ).
% 39.50/5.49  
% 39.50/5.49  cnf(c_1963,plain,
% 39.50/5.49      ( k7_subset_1(X0,X0,X1) = k7_subset_1(X2,X0,X1)
% 39.50/5.49      | r1_tarski(X0,X2) != iProver_top ),
% 39.50/5.49      inference(demodulation,[status(thm)],[c_1467,c_842]) ).
% 39.50/5.49  
% 39.50/5.49  cnf(c_6685,plain,
% 39.50/5.49      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) ),
% 39.50/5.49      inference(superposition,[status(thm)],[c_2222,c_1963]) ).
% 39.50/5.49  
% 39.50/5.49  cnf(c_18,plain,
% 39.50/5.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 39.50/5.49      | ~ l1_pre_topc(X1)
% 39.50/5.49      | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
% 39.50/5.49      inference(cnf_transformation,[],[f64]) ).
% 39.50/5.49  
% 39.50/5.49  cnf(c_851,plain,
% 39.50/5.49      ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
% 39.50/5.49      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 39.50/5.49      | l1_pre_topc(X0) != iProver_top ),
% 39.50/5.49      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 39.50/5.49  
% 39.50/5.49  cnf(c_3577,plain,
% 39.50/5.49      ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1)
% 39.50/5.49      | l1_pre_topc(sK0) != iProver_top ),
% 39.50/5.49      inference(superposition,[status(thm)],[c_848,c_851]) ).
% 39.50/5.49  
% 39.50/5.49  cnf(c_22,negated_conjecture,
% 39.50/5.49      ( l1_pre_topc(sK0) ),
% 39.50/5.49      inference(cnf_transformation,[],[f66]) ).
% 39.50/5.49  
% 39.50/5.49  cnf(c_1178,plain,
% 39.50/5.49      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 39.50/5.49      | ~ l1_pre_topc(sK0)
% 39.50/5.49      | k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
% 39.50/5.49      inference(instantiation,[status(thm)],[c_18]) ).
% 39.50/5.49  
% 39.50/5.49  cnf(c_3815,plain,
% 39.50/5.49      ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
% 39.50/5.49      inference(global_propositional_subsumption,
% 39.50/5.49                [status(thm)],
% 39.50/5.49                [c_3577,c_22,c_21,c_1178]) ).
% 39.50/5.49  
% 39.50/5.49  cnf(c_7046,plain,
% 39.50/5.49      ( k7_subset_1(sK1,sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
% 39.50/5.49      inference(superposition,[status(thm)],[c_6685,c_3815]) ).
% 39.50/5.49  
% 39.50/5.49  cnf(c_1962,plain,
% 39.50/5.49      ( r1_tarski(k7_subset_1(X0,X0,X1),X0) = iProver_top ),
% 39.50/5.49      inference(demodulation,[status(thm)],[c_1467,c_859]) ).
% 39.50/5.49  
% 39.50/5.49  cnf(c_7607,plain,
% 39.50/5.49      ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
% 39.50/5.49      inference(superposition,[status(thm)],[c_7046,c_1962]) ).
% 39.50/5.49  
% 39.50/5.49  cnf(c_7,plain,
% 39.50/5.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 39.50/5.49      | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
% 39.50/5.49      inference(cnf_transformation,[],[f76]) ).
% 39.50/5.49  
% 39.50/5.49  cnf(c_206,plain,
% 39.50/5.49      ( ~ r1_tarski(X0,X1)
% 39.50/5.49      | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
% 39.50/5.49      inference(bin_hyper_res,[status(thm)],[c_7,c_165]) ).
% 39.50/5.49  
% 39.50/5.49  cnf(c_845,plain,
% 39.50/5.49      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
% 39.50/5.49      | r1_tarski(X1,X0) != iProver_top ),
% 39.50/5.49      inference(predicate_to_equality,[status(thm)],[c_206]) ).
% 39.50/5.49  
% 39.50/5.49  cnf(c_6708,plain,
% 39.50/5.49      ( k7_subset_1(X0,X0,X1) = k3_subset_1(X0,X1)
% 39.50/5.49      | r1_tarski(X1,X0) != iProver_top ),
% 39.50/5.49      inference(demodulation,[status(thm)],[c_845,c_1467]) ).
% 39.50/5.49  
% 39.50/5.49  cnf(c_11826,plain,
% 39.50/5.49      ( k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) = k3_subset_1(sK1,k1_tops_1(sK0,sK1)) ),
% 39.50/5.49      inference(superposition,[status(thm)],[c_7607,c_6708]) ).
% 39.50/5.49  
% 39.50/5.49  cnf(c_19,negated_conjecture,
% 39.50/5.49      ( ~ v4_pre_topc(sK1,sK0)
% 39.50/5.49      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
% 39.50/5.49      inference(cnf_transformation,[],[f69]) ).
% 39.50/5.49  
% 39.50/5.49  cnf(c_850,plain,
% 39.50/5.49      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
% 39.50/5.49      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 39.50/5.49      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 39.50/5.49  
% 39.50/5.49  cnf(c_7023,plain,
% 39.50/5.49      ( k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
% 39.50/5.49      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 39.50/5.49      inference(demodulation,[status(thm)],[c_6685,c_850]) ).
% 39.50/5.49  
% 39.50/5.49  cnf(c_138896,plain,
% 39.50/5.49      ( k3_subset_1(sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
% 39.50/5.49      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 39.50/5.49      inference(demodulation,[status(thm)],[c_11826,c_7023]) ).
% 39.50/5.49  
% 39.50/5.49  cnf(c_15,plain,
% 39.50/5.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 39.50/5.49      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 39.50/5.49      | ~ l1_pre_topc(X1) ),
% 39.50/5.49      inference(cnf_transformation,[],[f61]) ).
% 39.50/5.49  
% 39.50/5.49  cnf(c_854,plain,
% 39.50/5.49      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 39.50/5.49      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 39.50/5.49      | l1_pre_topc(X1) != iProver_top ),
% 39.50/5.49      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 39.50/5.49  
% 39.50/5.49  cnf(c_9,plain,
% 39.50/5.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 39.50/5.49      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 39.50/5.49      | k5_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X0))) = k4_subset_1(X1,X0,X2) ),
% 39.50/5.49      inference(cnf_transformation,[],[f77]) ).
% 39.50/5.49  
% 39.50/5.49  cnf(c_208,plain,
% 39.50/5.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 39.50/5.49      | ~ r1_tarski(X2,X1)
% 39.50/5.49      | k5_xboole_0(X2,k5_xboole_0(X0,k3_xboole_0(X0,X2))) = k4_subset_1(X1,X2,X0) ),
% 39.50/5.49      inference(bin_hyper_res,[status(thm)],[c_9,c_165]) ).
% 39.50/5.49  
% 39.50/5.49  cnf(c_843,plain,
% 39.50/5.49      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k4_subset_1(X2,X0,X1)
% 39.50/5.49      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
% 39.50/5.49      | r1_tarski(X0,X2) != iProver_top ),
% 39.50/5.49      inference(predicate_to_equality,[status(thm)],[c_208]) ).
% 39.50/5.49  
% 39.50/5.49  cnf(c_2104,plain,
% 39.50/5.49      ( k5_xboole_0(X0,k7_subset_1(X1,X1,X0)) = k4_subset_1(X2,X0,X1)
% 39.50/5.49      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
% 39.50/5.49      | r1_tarski(X0,X2) != iProver_top ),
% 39.50/5.49      inference(demodulation,[status(thm)],[c_843,c_1467]) ).
% 39.50/5.49  
% 39.50/5.49  cnf(c_3393,plain,
% 39.50/5.49      ( k5_xboole_0(X0,k7_subset_1(k2_tops_1(X1,X2),k2_tops_1(X1,X2),X0)) = k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X2))
% 39.50/5.49      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 39.50/5.49      | r1_tarski(X0,u1_struct_0(X1)) != iProver_top
% 39.50/5.49      | l1_pre_topc(X1) != iProver_top ),
% 39.50/5.49      inference(superposition,[status(thm)],[c_854,c_2104]) ).
% 39.50/5.49  
% 39.50/5.49  cnf(c_13925,plain,
% 39.50/5.49      ( k5_xboole_0(X0,k7_subset_1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),X0)) = k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,sK1))
% 39.50/5.49      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
% 39.50/5.49      | l1_pre_topc(sK0) != iProver_top ),
% 39.50/5.49      inference(superposition,[status(thm)],[c_848,c_3393]) ).
% 39.50/5.49  
% 39.50/5.49  cnf(c_25,plain,
% 39.50/5.49      ( l1_pre_topc(sK0) = iProver_top ),
% 39.50/5.49      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 39.50/5.49  
% 39.50/5.49  cnf(c_14661,plain,
% 39.50/5.49      ( r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
% 39.50/5.49      | k5_xboole_0(X0,k7_subset_1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),X0)) = k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,sK1)) ),
% 39.50/5.49      inference(global_propositional_subsumption,
% 39.50/5.49                [status(thm)],
% 39.50/5.49                [c_13925,c_25]) ).
% 39.50/5.49  
% 39.50/5.49  cnf(c_14662,plain,
% 39.50/5.49      ( k5_xboole_0(X0,k7_subset_1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),X0)) = k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,sK1))
% 39.50/5.49      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
% 39.50/5.49      inference(renaming,[status(thm)],[c_14661]) ).
% 39.50/5.49  
% 39.50/5.49  cnf(c_14672,plain,
% 39.50/5.49      ( k5_xboole_0(sK1,k7_subset_1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),sK1)) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
% 39.50/5.49      inference(superposition,[status(thm)],[c_2222,c_14662]) ).
% 39.50/5.49  
% 39.50/5.49  cnf(c_16,plain,
% 39.50/5.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 39.50/5.49      | ~ l1_pre_topc(X1)
% 39.50/5.49      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
% 39.50/5.49      inference(cnf_transformation,[],[f62]) ).
% 39.50/5.49  
% 39.50/5.49  cnf(c_853,plain,
% 39.50/5.49      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
% 39.50/5.49      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 39.50/5.49      | l1_pre_topc(X0) != iProver_top ),
% 39.50/5.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 39.50/5.49  
% 39.50/5.49  cnf(c_3607,plain,
% 39.50/5.49      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
% 39.50/5.49      | l1_pre_topc(sK0) != iProver_top ),
% 39.50/5.49      inference(superposition,[status(thm)],[c_848,c_853]) ).
% 39.50/5.49  
% 39.50/5.49  cnf(c_1175,plain,
% 39.50/5.49      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 39.50/5.49      | ~ l1_pre_topc(sK0)
% 39.50/5.49      | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 39.50/5.49      inference(instantiation,[status(thm)],[c_16]) ).
% 39.50/5.49  
% 39.50/5.49  cnf(c_3893,plain,
% 39.50/5.49      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 39.50/5.49      inference(global_propositional_subsumption,
% 39.50/5.49                [status(thm)],
% 39.50/5.49                [c_3607,c_22,c_21,c_1175]) ).
% 39.50/5.49  
% 39.50/5.49  cnf(c_20,negated_conjecture,
% 39.50/5.49      ( v4_pre_topc(sK1,sK0)
% 39.50/5.49      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 39.50/5.49      inference(cnf_transformation,[],[f68]) ).
% 39.50/5.49  
% 39.50/5.49  cnf(c_849,plain,
% 39.50/5.49      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 39.50/5.49      | v4_pre_topc(sK1,sK0) = iProver_top ),
% 39.50/5.49      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 39.50/5.49  
% 39.50/5.49  cnf(c_7022,plain,
% 39.50/5.49      ( k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 39.50/5.49      | v4_pre_topc(sK1,sK0) = iProver_top ),
% 39.50/5.49      inference(demodulation,[status(thm)],[c_6685,c_849]) ).
% 39.50/5.49  
% 39.50/5.49  cnf(c_17,plain,
% 39.50/5.49      ( ~ v4_pre_topc(X0,X1)
% 39.50/5.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 39.50/5.49      | r1_tarski(k2_tops_1(X1,X0),X0)
% 39.50/5.49      | ~ l1_pre_topc(X1) ),
% 39.50/5.49      inference(cnf_transformation,[],[f63]) ).
% 39.50/5.49  
% 39.50/5.49  cnf(c_852,plain,
% 39.50/5.49      ( v4_pre_topc(X0,X1) != iProver_top
% 39.50/5.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 39.50/5.49      | r1_tarski(k2_tops_1(X1,X0),X0) = iProver_top
% 39.50/5.49      | l1_pre_topc(X1) != iProver_top ),
% 39.50/5.49      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 39.50/5.49  
% 39.50/5.49  cnf(c_3368,plain,
% 39.50/5.49      ( v4_pre_topc(sK1,sK0) != iProver_top
% 39.50/5.49      | r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top
% 39.50/5.49      | l1_pre_topc(sK0) != iProver_top ),
% 39.50/5.49      inference(superposition,[status(thm)],[c_848,c_852]) ).
% 39.50/5.49  
% 39.50/5.49  cnf(c_4088,plain,
% 39.50/5.49      ( r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top
% 39.50/5.49      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 39.50/5.49      inference(global_propositional_subsumption,
% 39.50/5.49                [status(thm)],
% 39.50/5.49                [c_3368,c_25]) ).
% 39.50/5.49  
% 39.50/5.49  cnf(c_4089,plain,
% 39.50/5.49      ( v4_pre_topc(sK1,sK0) != iProver_top
% 39.50/5.49      | r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top ),
% 39.50/5.49      inference(renaming,[status(thm)],[c_4088]) ).
% 39.50/5.49  
% 39.50/5.49  cnf(c_0,plain,
% 39.50/5.49      ( ~ r1_tarski(X0,X1)
% 39.50/5.49      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
% 39.50/5.49      inference(cnf_transformation,[],[f71]) ).
% 39.50/5.49  
% 39.50/5.49  cnf(c_863,plain,
% 39.50/5.49      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
% 39.50/5.49      | r1_tarski(X0,X1) != iProver_top ),
% 39.50/5.49      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 39.50/5.49  
% 39.50/5.49  cnf(c_2384,plain,
% 39.50/5.49      ( k7_subset_1(X0,X0,X1) = k1_xboole_0
% 39.50/5.49      | r1_tarski(X0,X1) != iProver_top ),
% 39.50/5.49      inference(demodulation,[status(thm)],[c_863,c_1467]) ).
% 39.50/5.49  
% 39.50/5.49  cnf(c_4094,plain,
% 39.50/5.49      ( k7_subset_1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),sK1) = k1_xboole_0
% 39.50/5.49      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 39.50/5.49      inference(superposition,[status(thm)],[c_4089,c_2384]) ).
% 39.50/5.49  
% 39.50/5.49  cnf(c_7334,plain,
% 39.50/5.49      ( k7_subset_1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),sK1) = k1_xboole_0
% 39.50/5.49      | k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 39.50/5.49      inference(superposition,[status(thm)],[c_7022,c_4094]) ).
% 39.50/5.49  
% 39.50/5.49  cnf(c_23,negated_conjecture,
% 39.50/5.49      ( v2_pre_topc(sK0) ),
% 39.50/5.49      inference(cnf_transformation,[],[f65]) ).
% 39.50/5.49  
% 39.50/5.49  cnf(c_24,plain,
% 39.50/5.49      ( v2_pre_topc(sK0) = iProver_top ),
% 39.50/5.49      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 39.50/5.49  
% 39.50/5.49  cnf(c_26,plain,
% 39.50/5.49      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 39.50/5.49      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 39.50/5.49  
% 39.50/5.49  cnf(c_13,plain,
% 39.50/5.49      ( v4_pre_topc(X0,X1)
% 39.50/5.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 39.50/5.49      | ~ l1_pre_topc(X1)
% 39.50/5.49      | ~ v2_pre_topc(X1)
% 39.50/5.49      | k2_pre_topc(X1,X0) != X0 ),
% 39.50/5.49      inference(cnf_transformation,[],[f60]) ).
% 39.50/5.49  
% 39.50/5.49  cnf(c_1172,plain,
% 39.50/5.49      ( v4_pre_topc(sK1,sK0)
% 39.50/5.49      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 39.50/5.49      | ~ l1_pre_topc(sK0)
% 39.50/5.49      | ~ v2_pre_topc(sK0)
% 39.50/5.49      | k2_pre_topc(sK0,sK1) != sK1 ),
% 39.50/5.49      inference(instantiation,[status(thm)],[c_13]) ).
% 39.50/5.49  
% 39.50/5.49  cnf(c_1173,plain,
% 39.50/5.49      ( k2_pre_topc(sK0,sK1) != sK1
% 39.50/5.49      | v4_pre_topc(sK1,sK0) = iProver_top
% 39.50/5.49      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 39.50/5.49      | l1_pre_topc(sK0) != iProver_top
% 39.50/5.49      | v2_pre_topc(sK0) != iProver_top ),
% 39.50/5.49      inference(predicate_to_equality,[status(thm)],[c_1172]) ).
% 39.50/5.49  
% 39.50/5.49  cnf(c_14,plain,
% 39.50/5.49      ( ~ v4_pre_topc(X0,X1)
% 39.50/5.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 39.50/5.49      | ~ l1_pre_topc(X1)
% 39.50/5.49      | k2_pre_topc(X1,X0) = X0 ),
% 39.50/5.49      inference(cnf_transformation,[],[f59]) ).
% 39.50/5.49  
% 39.50/5.49  cnf(c_855,plain,
% 39.50/5.49      ( k2_pre_topc(X0,X1) = X1
% 39.50/5.49      | v4_pre_topc(X1,X0) != iProver_top
% 39.50/5.49      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 39.50/5.49      | l1_pre_topc(X0) != iProver_top ),
% 39.50/5.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 39.50/5.49  
% 39.50/5.49  cnf(c_3784,plain,
% 39.50/5.49      ( k2_pre_topc(sK0,sK1) = sK1
% 39.50/5.49      | v4_pre_topc(sK1,sK0) != iProver_top
% 39.50/5.49      | l1_pre_topc(sK0) != iProver_top ),
% 39.50/5.49      inference(superposition,[status(thm)],[c_848,c_855]) ).
% 39.50/5.49  
% 39.50/5.49  cnf(c_3897,plain,
% 39.50/5.49      ( v4_pre_topc(sK1,sK0) != iProver_top
% 39.50/5.49      | k2_pre_topc(sK0,sK1) = sK1 ),
% 39.50/5.49      inference(global_propositional_subsumption,
% 39.50/5.49                [status(thm)],
% 39.50/5.49                [c_3784,c_25]) ).
% 39.50/5.49  
% 39.50/5.49  cnf(c_3898,plain,
% 39.50/5.49      ( k2_pre_topc(sK0,sK1) = sK1
% 39.50/5.49      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 39.50/5.49      inference(renaming,[status(thm)],[c_3897]) ).
% 39.50/5.49  
% 39.50/5.49  cnf(c_3903,plain,
% 39.50/5.49      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 39.50/5.49      | k2_pre_topc(sK0,sK1) = sK1 ),
% 39.50/5.49      inference(superposition,[status(thm)],[c_849,c_3898]) ).
% 39.50/5.49  
% 39.50/5.49  cnf(c_7045,plain,
% 39.50/5.49      ( k7_subset_1(sK1,sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 39.50/5.49      | k2_pre_topc(sK0,sK1) = sK1 ),
% 39.50/5.49      inference(superposition,[status(thm)],[c_6685,c_3903]) ).
% 39.50/5.49  
% 39.50/5.49  cnf(c_4671,plain,
% 39.50/5.49      ( k7_subset_1(k7_subset_1(X0,X0,X1),k7_subset_1(X0,X0,X1),X0) = k1_xboole_0 ),
% 39.50/5.49      inference(superposition,[status(thm)],[c_1962,c_2384]) ).
% 39.50/5.49  
% 39.50/5.49  cnf(c_8630,plain,
% 39.50/5.49      ( k7_subset_1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),sK1) = k1_xboole_0
% 39.50/5.49      | k2_pre_topc(sK0,sK1) = sK1 ),
% 39.50/5.49      inference(superposition,[status(thm)],[c_7045,c_4671]) ).
% 39.50/5.49  
% 39.50/5.49  cnf(c_10630,plain,
% 39.50/5.49      ( k7_subset_1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),sK1) = k1_xboole_0 ),
% 39.50/5.49      inference(global_propositional_subsumption,
% 39.50/5.49                [status(thm)],
% 39.50/5.49                [c_7334,c_24,c_25,c_26,c_1173,c_4094,c_8630]) ).
% 39.50/5.49  
% 39.50/5.49  cnf(c_14683,plain,
% 39.50/5.49      ( k2_pre_topc(sK0,sK1) = k5_xboole_0(sK1,k1_xboole_0) ),
% 39.50/5.49      inference(light_normalisation,
% 39.50/5.49                [status(thm)],
% 39.50/5.49                [c_14672,c_3893,c_10630]) ).
% 39.50/5.49  
% 39.50/5.49  cnf(c_4,plain,
% 39.50/5.49      ( r1_tarski(k1_xboole_0,X0) ),
% 39.50/5.49      inference(cnf_transformation,[],[f49]) ).
% 39.50/5.49  
% 39.50/5.49  cnf(c_860,plain,
% 39.50/5.49      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 39.50/5.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 39.50/5.49  
% 39.50/5.49  cnf(c_3,plain,
% 39.50/5.49      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 39.50/5.49      inference(cnf_transformation,[],[f48]) ).
% 39.50/5.49  
% 39.50/5.49  cnf(c_861,plain,
% 39.50/5.49      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 39.50/5.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 39.50/5.49  
% 39.50/5.49  cnf(c_1591,plain,
% 39.50/5.49      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 39.50/5.49      inference(superposition,[status(thm)],[c_860,c_861]) ).
% 39.50/5.49  
% 39.50/5.49  cnf(c_2,plain,
% 39.50/5.49      ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
% 39.50/5.49      inference(cnf_transformation,[],[f73]) ).
% 39.50/5.49  
% 39.50/5.49  cnf(c_1604,plain,
% 39.50/5.49      ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) = X0 ),
% 39.50/5.49      inference(demodulation,[status(thm)],[c_1591,c_2]) ).
% 39.50/5.49  
% 39.50/5.49  cnf(c_1193,plain,
% 39.50/5.49      ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 39.50/5.49      inference(superposition,[status(thm)],[c_6,c_2]) ).
% 39.50/5.49  
% 39.50/5.49  cnf(c_1605,plain,
% 39.50/5.49      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 39.50/5.49      inference(light_normalisation,[status(thm)],[c_1604,c_1193]) ).
% 39.50/5.49  
% 39.50/5.49  cnf(c_14684,plain,
% 39.50/5.49      ( k2_pre_topc(sK0,sK1) = sK1 ),
% 39.50/5.49      inference(demodulation,[status(thm)],[c_14683,c_1605]) ).
% 39.50/5.49  
% 39.50/5.49  cnf(c_1,plain,
% 39.50/5.49      ( r1_tarski(X0,X1)
% 39.50/5.49      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0 ),
% 39.50/5.49      inference(cnf_transformation,[],[f72]) ).
% 39.50/5.49  
% 39.50/5.49  cnf(c_862,plain,
% 39.50/5.49      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0
% 39.50/5.49      | r1_tarski(X0,X1) = iProver_top ),
% 39.50/5.49      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 39.50/5.49  
% 39.50/5.49  cnf(c_2370,plain,
% 39.50/5.49      ( k7_subset_1(X0,X0,X1) != k1_xboole_0
% 39.50/5.49      | r1_tarski(X0,X1) = iProver_top ),
% 39.50/5.49      inference(light_normalisation,[status(thm)],[c_862,c_1467]) ).
% 39.50/5.49  
% 39.50/5.49  cnf(c_10650,plain,
% 39.50/5.49      ( r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top ),
% 39.50/5.49      inference(superposition,[status(thm)],[c_10630,c_2370]) ).
% 39.50/5.49  
% 39.50/5.49  cnf(c_11863,plain,
% 39.50/5.49      ( k7_subset_1(sK1,sK1,k2_tops_1(sK0,sK1)) = k3_subset_1(sK1,k2_tops_1(sK0,sK1)) ),
% 39.50/5.49      inference(superposition,[status(thm)],[c_10650,c_6708]) ).
% 39.50/5.49  
% 39.50/5.49  cnf(c_11882,plain,
% 39.50/5.49      ( k3_subset_1(sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
% 39.50/5.49      inference(light_normalisation,[status(thm)],[c_11863,c_7046]) ).
% 39.50/5.50  
% 39.50/5.50  cnf(c_8,plain,
% 39.50/5.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 39.50/5.50      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 39.50/5.50      inference(cnf_transformation,[],[f54]) ).
% 39.50/5.50  
% 39.50/5.50  cnf(c_207,plain,
% 39.50/5.50      ( ~ r1_tarski(X0,X1) | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 39.50/5.50      inference(bin_hyper_res,[status(thm)],[c_8,c_165]) ).
% 39.50/5.50  
% 39.50/5.50  cnf(c_844,plain,
% 39.50/5.50      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 39.50/5.50      | r1_tarski(X1,X0) != iProver_top ),
% 39.50/5.50      inference(predicate_to_equality,[status(thm)],[c_207]) ).
% 39.50/5.50  
% 39.50/5.50  cnf(c_11864,plain,
% 39.50/5.50      ( k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1))) = k2_tops_1(sK0,sK1) ),
% 39.50/5.50      inference(superposition,[status(thm)],[c_10650,c_844]) ).
% 39.50/5.50  
% 39.50/5.50  cnf(c_11883,plain,
% 39.50/5.50      ( k3_subset_1(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 39.50/5.50      inference(demodulation,[status(thm)],[c_11882,c_11864]) ).
% 39.50/5.50  
% 39.50/5.50  cnf(contradiction,plain,
% 39.50/5.50      ( $false ),
% 39.50/5.50      inference(minisat,
% 39.50/5.50                [status(thm)],
% 39.50/5.50                [c_138896,c_14684,c_11883,c_1173,c_26,c_25,c_24]) ).
% 39.50/5.50  
% 39.50/5.50  
% 39.50/5.50  % SZS output end CNFRefutation for theBenchmark.p
% 39.50/5.50  
% 39.50/5.50  ------                               Statistics
% 39.50/5.50  
% 39.50/5.50  ------ Selected
% 39.50/5.50  
% 39.50/5.50  total_time:                             4.564
% 39.50/5.50  
%------------------------------------------------------------------------------
