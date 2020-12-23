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
% DateTime   : Thu Dec  3 12:14:41 EST 2020

% Result     : Theorem 11.83s
% Output     : CNFRefutation 11.83s
% Verified   : 
% Statistics : Number of formulae       :  134 (1058 expanded)
%              Number of clauses        :   68 ( 292 expanded)
%              Number of leaves         :   19 ( 244 expanded)
%              Depth                    :   21
%              Number of atoms          :  329 (3637 expanded)
%              Number of equality atoms :  160 (1322 expanded)
%              Maximal formula depth    :    9 (   4 average)
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

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

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
    inference(nnf_transformation,[],[f36])).

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

fof(f63,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f62,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f41])).

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
    inference(ennf_transformation,[],[f13])).

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

fof(f54,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f61,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f65,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f43,f52])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f50,f65])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f67,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0) ),
    inference(definition_unfolding,[],[f44,f65])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f12])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f8,axiom,(
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
    inference(ennf_transformation,[],[f8])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f22])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k2_tarski(X1,X2)) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f49,f46])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f6,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f68,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) ),
    inference(definition_unfolding,[],[f45,f46,f46,f46])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f66,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(definition_unfolding,[],[f42,f46,f46])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) != X1
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f64,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f60,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_16,negated_conjecture,
    ( v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_672,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_671,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_10,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_678,plain,
    ( k2_pre_topc(X0,X1) = X1
    | v4_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4810,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | v4_pre_topc(sK1,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_671,c_678])).

cnf(c_18,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_21,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_5094,plain,
    ( v4_pre_topc(sK1,sK0) != iProver_top
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4810,c_21])).

cnf(c_5095,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5094])).

cnf(c_5100,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_672,c_5095])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2))) = k7_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_682,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X2,X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3440,plain,
    ( k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0))) = k7_subset_1(u1_struct_0(sK0),sK1,X0) ),
    inference(superposition,[status(thm)],[c_671,c_682])).

cnf(c_1,plain,
    ( r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_685,plain,
    ( r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3461,plain,
    ( r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,X0),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3440,c_685])).

cnf(c_8,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_680,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_684,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X0,X2) = k3_tarski(k2_tarski(X0,X2)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_683,plain,
    ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4591,plain,
    ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_680,c_683])).

cnf(c_9122,plain,
    ( k4_subset_1(X0,X1,k3_subset_1(X0,X2)) = k3_tarski(k2_tarski(X1,k3_subset_1(X0,X2)))
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_684,c_4591])).

cnf(c_19607,plain,
    ( k4_subset_1(X0,X1,k3_subset_1(X0,X2)) = k3_tarski(k2_tarski(X1,k3_subset_1(X0,X2)))
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_680,c_9122])).

cnf(c_21327,plain,
    ( k4_subset_1(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0),k3_subset_1(sK1,X1)) = k3_tarski(k2_tarski(k7_subset_1(u1_struct_0(sK0),sK1,X0),k3_subset_1(sK1,X1)))
    | r1_tarski(X1,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3461,c_19607])).

cnf(c_21679,plain,
    ( k4_subset_1(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0),k3_subset_1(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X1))) = k3_tarski(k2_tarski(k7_subset_1(u1_struct_0(sK0),sK1,X0),k3_subset_1(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X1)))) ),
    inference(superposition,[status(thm)],[c_3461,c_21327])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X0,k3_subset_1(X1,X0)) = k2_subset_1(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_681,plain,
    ( k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = k2_subset_1(X0)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_712,plain,
    ( k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = X0
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_681,c_3])).

cnf(c_1589,plain,
    ( k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = X0
    | r1_tarski(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_680,c_712])).

cnf(c_1673,plain,
    ( k4_subset_1(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),k3_subset_1(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))) = X0 ),
    inference(superposition,[status(thm)],[c_685,c_1589])).

cnf(c_3459,plain,
    ( k4_subset_1(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0),k3_subset_1(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0))) = sK1 ),
    inference(superposition,[status(thm)],[c_3440,c_1673])).

cnf(c_21695,plain,
    ( k3_tarski(k2_tarski(k7_subset_1(u1_struct_0(sK0),sK1,X0),k3_subset_1(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0)))) = sK1 ),
    inference(superposition,[status(thm)],[c_21679,c_3459])).

cnf(c_2,plain,
    ( k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_31375,plain,
    ( k3_tarski(k2_tarski(k7_subset_1(u1_struct_0(sK0),sK1,X0),k3_subset_1(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0)))) = k3_tarski(k2_tarski(k7_subset_1(u1_struct_0(sK0),sK1,X0),sK1)) ),
    inference(superposition,[status(thm)],[c_21695,c_2])).

cnf(c_31402,plain,
    ( k3_tarski(k2_tarski(k7_subset_1(u1_struct_0(sK0),sK1,X0),sK1)) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_31375,c_21695])).

cnf(c_34404,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_5100,c_31402])).

cnf(c_0,plain,
    ( k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_34461,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = sK1 ),
    inference(superposition,[status(thm)],[c_34404,c_0])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_677,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_4594,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k3_tarski(k2_tarski(sK1,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_671,c_683])).

cnf(c_5106,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_677,c_4594])).

cnf(c_5907,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5106,c_21])).

cnf(c_5908,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_5907])).

cnf(c_5918,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
    inference(superposition,[status(thm)],[c_671,c_5908])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_674,plain,
    ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1112,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_671,c_674])).

cnf(c_936,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1417,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1112,c_18,c_17,c_936])).

cnf(c_5920,plain,
    ( k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k2_pre_topc(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_5918,c_1417])).

cnf(c_34464,plain,
    ( k2_pre_topc(sK0,sK1) = sK1 ),
    inference(demodulation,[status(thm)],[c_34461,c_5920])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_675,plain,
    ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2189,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_671,c_675])).

cnf(c_939,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_2653,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2189,c_18,c_17,c_939])).

cnf(c_34671,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_34464,c_2653])).

cnf(c_9,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | k2_pre_topc(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_933,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | k2_pre_topc(sK0,sK1) != sK1 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_15,negated_conjecture,
    ( ~ v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_19,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f60])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_34671,c_34464,c_933,c_15,c_17,c_18,c_19])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:29:39 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 11.83/1.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.83/1.99  
% 11.83/1.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.83/1.99  
% 11.83/1.99  ------  iProver source info
% 11.83/1.99  
% 11.83/1.99  git: date: 2020-06-30 10:37:57 +0100
% 11.83/1.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.83/1.99  git: non_committed_changes: false
% 11.83/1.99  git: last_make_outside_of_git: false
% 11.83/1.99  
% 11.83/1.99  ------ 
% 11.83/1.99  ------ Parsing...
% 11.83/1.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.83/1.99  
% 11.83/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 11.83/1.99  
% 11.83/1.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.83/1.99  
% 11.83/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.83/1.99  ------ Proving...
% 11.83/1.99  ------ Problem Properties 
% 11.83/1.99  
% 11.83/1.99  
% 11.83/1.99  clauses                                 20
% 11.83/1.99  conjectures                             5
% 11.83/1.99  EPR                                     2
% 11.83/1.99  Horn                                    19
% 11.83/1.99  unary                                   7
% 11.83/1.99  binary                                  6
% 11.83/1.99  lits                                    44
% 11.83/1.99  lits eq                                 12
% 11.83/1.99  fd_pure                                 0
% 11.83/1.99  fd_pseudo                               0
% 11.83/1.99  fd_cond                                 0
% 11.83/1.99  fd_pseudo_cond                          0
% 11.83/1.99  AC symbols                              0
% 11.83/1.99  
% 11.83/1.99  ------ Input Options Time Limit: Unbounded
% 11.83/1.99  
% 11.83/1.99  
% 11.83/1.99  ------ 
% 11.83/1.99  Current options:
% 11.83/1.99  ------ 
% 11.83/1.99  
% 11.83/1.99  
% 11.83/1.99  
% 11.83/1.99  
% 11.83/1.99  ------ Proving...
% 11.83/1.99  
% 11.83/1.99  
% 11.83/1.99  % SZS status Theorem for theBenchmark.p
% 11.83/1.99  
% 11.83/1.99  % SZS output start CNFRefutation for theBenchmark.p
% 11.83/1.99  
% 11.83/1.99  fof(f18,conjecture,(
% 11.83/1.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 11.83/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.83/1.99  
% 11.83/1.99  fof(f19,negated_conjecture,(
% 11.83/1.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 11.83/1.99    inference(negated_conjecture,[],[f18])).
% 11.83/1.99  
% 11.83/1.99  fof(f35,plain,(
% 11.83/1.99    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 11.83/1.99    inference(ennf_transformation,[],[f19])).
% 11.83/1.99  
% 11.83/1.99  fof(f36,plain,(
% 11.83/1.99    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 11.83/1.99    inference(flattening,[],[f35])).
% 11.83/1.99  
% 11.83/1.99  fof(f37,plain,(
% 11.83/1.99    ? [X0] : (? [X1] : (((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 11.83/1.99    inference(nnf_transformation,[],[f36])).
% 11.83/1.99  
% 11.83/1.99  fof(f38,plain,(
% 11.83/1.99    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 11.83/1.99    inference(flattening,[],[f37])).
% 11.83/1.99  
% 11.83/1.99  fof(f40,plain,(
% 11.83/1.99    ( ! [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) != k2_tops_1(X0,sK1) | ~v4_pre_topc(sK1,X0)) & (k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) = k2_tops_1(X0,sK1) | v4_pre_topc(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 11.83/1.99    introduced(choice_axiom,[])).
% 11.83/1.99  
% 11.83/1.99  fof(f39,plain,(
% 11.83/1.99    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) != k2_tops_1(sK0,X1) | ~v4_pre_topc(X1,sK0)) & (k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) = k2_tops_1(sK0,X1) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 11.83/1.99    introduced(choice_axiom,[])).
% 11.83/1.99  
% 11.83/1.99  fof(f41,plain,(
% 11.83/1.99    ((k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)) & (k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 11.83/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f38,f40,f39])).
% 11.83/1.99  
% 11.83/1.99  fof(f63,plain,(
% 11.83/1.99    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)),
% 11.83/1.99    inference(cnf_transformation,[],[f41])).
% 11.83/1.99  
% 11.83/1.99  fof(f62,plain,(
% 11.83/1.99    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 11.83/1.99    inference(cnf_transformation,[],[f41])).
% 11.83/1.99  
% 11.83/1.99  fof(f13,axiom,(
% 11.83/1.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 11.83/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.83/1.99  
% 11.83/1.99  fof(f27,plain,(
% 11.83/1.99    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.83/1.99    inference(ennf_transformation,[],[f13])).
% 11.83/1.99  
% 11.83/1.99  fof(f28,plain,(
% 11.83/1.99    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.83/1.99    inference(flattening,[],[f27])).
% 11.83/1.99  
% 11.83/1.99  fof(f54,plain,(
% 11.83/1.99    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.83/1.99    inference(cnf_transformation,[],[f28])).
% 11.83/1.99  
% 11.83/1.99  fof(f61,plain,(
% 11.83/1.99    l1_pre_topc(sK0)),
% 11.83/1.99    inference(cnf_transformation,[],[f41])).
% 11.83/1.99  
% 11.83/1.99  fof(f9,axiom,(
% 11.83/1.99    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 11.83/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.83/1.99  
% 11.83/1.99  fof(f24,plain,(
% 11.83/1.99    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.83/1.99    inference(ennf_transformation,[],[f9])).
% 11.83/1.99  
% 11.83/1.99  fof(f50,plain,(
% 11.83/1.99    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.83/1.99    inference(cnf_transformation,[],[f24])).
% 11.83/1.99  
% 11.83/1.99  fof(f2,axiom,(
% 11.83/1.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 11.83/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.83/1.99  
% 11.83/1.99  fof(f43,plain,(
% 11.83/1.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 11.83/1.99    inference(cnf_transformation,[],[f2])).
% 11.83/1.99  
% 11.83/1.99  fof(f11,axiom,(
% 11.83/1.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 11.83/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.83/1.99  
% 11.83/1.99  fof(f52,plain,(
% 11.83/1.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 11.83/1.99    inference(cnf_transformation,[],[f11])).
% 11.83/1.99  
% 11.83/1.99  fof(f65,plain,(
% 11.83/1.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 11.83/1.99    inference(definition_unfolding,[],[f43,f52])).
% 11.83/1.99  
% 11.83/1.99  fof(f70,plain,(
% 11.83/1.99    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.83/1.99    inference(definition_unfolding,[],[f50,f65])).
% 11.83/1.99  
% 11.83/1.99  fof(f3,axiom,(
% 11.83/1.99    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 11.83/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.83/1.99  
% 11.83/1.99  fof(f44,plain,(
% 11.83/1.99    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 11.83/1.99    inference(cnf_transformation,[],[f3])).
% 11.83/1.99  
% 11.83/1.99  fof(f67,plain,(
% 11.83/1.99    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0)) )),
% 11.83/1.99    inference(definition_unfolding,[],[f44,f65])).
% 11.83/1.99  
% 11.83/1.99  fof(f12,axiom,(
% 11.83/1.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 11.83/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.83/1.99  
% 11.83/1.99  fof(f20,plain,(
% 11.83/1.99    ! [X0,X1] : (r1_tarski(X0,X1) => m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 11.83/1.99    inference(unused_predicate_definition_removal,[],[f12])).
% 11.83/1.99  
% 11.83/1.99  fof(f26,plain,(
% 11.83/1.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 11.83/1.99    inference(ennf_transformation,[],[f20])).
% 11.83/1.99  
% 11.83/1.99  fof(f53,plain,(
% 11.83/1.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 11.83/1.99    inference(cnf_transformation,[],[f26])).
% 11.83/1.99  
% 11.83/1.99  fof(f7,axiom,(
% 11.83/1.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 11.83/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.83/1.99  
% 11.83/1.99  fof(f21,plain,(
% 11.83/1.99    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.83/1.99    inference(ennf_transformation,[],[f7])).
% 11.83/1.99  
% 11.83/1.99  fof(f48,plain,(
% 11.83/1.99    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.83/1.99    inference(cnf_transformation,[],[f21])).
% 11.83/1.99  
% 11.83/1.99  fof(f8,axiom,(
% 11.83/1.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 11.83/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.83/1.99  
% 11.83/1.99  fof(f22,plain,(
% 11.83/1.99    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 11.83/1.99    inference(ennf_transformation,[],[f8])).
% 11.83/1.99  
% 11.83/1.99  fof(f23,plain,(
% 11.83/1.99    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.83/1.99    inference(flattening,[],[f22])).
% 11.83/1.99  
% 11.83/1.99  fof(f49,plain,(
% 11.83/1.99    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.83/1.99    inference(cnf_transformation,[],[f23])).
% 11.83/1.99  
% 11.83/1.99  fof(f5,axiom,(
% 11.83/1.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 11.83/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.83/1.99  
% 11.83/1.99  fof(f46,plain,(
% 11.83/1.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 11.83/1.99    inference(cnf_transformation,[],[f5])).
% 11.83/1.99  
% 11.83/1.99  fof(f69,plain,(
% 11.83/1.99    ( ! [X2,X0,X1] : (k3_tarski(k2_tarski(X1,X2)) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.83/1.99    inference(definition_unfolding,[],[f49,f46])).
% 11.83/1.99  
% 11.83/1.99  fof(f10,axiom,(
% 11.83/1.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 11.83/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.83/1.99  
% 11.83/1.99  fof(f25,plain,(
% 11.83/1.99    ! [X0,X1] : (k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.83/1.99    inference(ennf_transformation,[],[f10])).
% 11.83/1.99  
% 11.83/1.99  fof(f51,plain,(
% 11.83/1.99    ( ! [X0,X1] : (k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.83/1.99    inference(cnf_transformation,[],[f25])).
% 11.83/1.99  
% 11.83/1.99  fof(f6,axiom,(
% 11.83/1.99    ! [X0] : k2_subset_1(X0) = X0),
% 11.83/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.83/1.99  
% 11.83/1.99  fof(f47,plain,(
% 11.83/1.99    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 11.83/1.99    inference(cnf_transformation,[],[f6])).
% 11.83/1.99  
% 11.83/1.99  fof(f4,axiom,(
% 11.83/1.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))),
% 11.83/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.83/1.99  
% 11.83/1.99  fof(f45,plain,(
% 11.83/1.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 11.83/1.99    inference(cnf_transformation,[],[f4])).
% 11.83/1.99  
% 11.83/1.99  fof(f68,plain,(
% 11.83/1.99    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1))))) )),
% 11.83/1.99    inference(definition_unfolding,[],[f45,f46,f46,f46])).
% 11.83/1.99  
% 11.83/1.99  fof(f1,axiom,(
% 11.83/1.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 11.83/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.83/1.99  
% 11.83/1.99  fof(f42,plain,(
% 11.83/1.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 11.83/1.99    inference(cnf_transformation,[],[f1])).
% 11.83/1.99  
% 11.83/1.99  fof(f66,plain,(
% 11.83/1.99    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X1,X0))) )),
% 11.83/1.99    inference(definition_unfolding,[],[f42,f46,f46])).
% 11.83/1.99  
% 11.83/1.99  fof(f14,axiom,(
% 11.83/1.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 11.83/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.83/1.99  
% 11.83/1.99  fof(f29,plain,(
% 11.83/1.99    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 11.83/1.99    inference(ennf_transformation,[],[f14])).
% 11.83/1.99  
% 11.83/1.99  fof(f30,plain,(
% 11.83/1.99    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 11.83/1.99    inference(flattening,[],[f29])).
% 11.83/1.99  
% 11.83/1.99  fof(f56,plain,(
% 11.83/1.99    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.83/1.99    inference(cnf_transformation,[],[f30])).
% 11.83/1.99  
% 11.83/1.99  fof(f17,axiom,(
% 11.83/1.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)))),
% 11.83/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.83/1.99  
% 11.83/1.99  fof(f34,plain,(
% 11.83/1.99    ! [X0] : (! [X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.83/1.99    inference(ennf_transformation,[],[f17])).
% 11.83/1.99  
% 11.83/1.99  fof(f59,plain,(
% 11.83/1.99    ( ! [X0,X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.83/1.99    inference(cnf_transformation,[],[f34])).
% 11.83/1.99  
% 11.83/1.99  fof(f16,axiom,(
% 11.83/1.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)))),
% 11.83/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.83/1.99  
% 11.83/1.99  fof(f33,plain,(
% 11.83/1.99    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.83/1.99    inference(ennf_transformation,[],[f16])).
% 11.83/1.99  
% 11.83/1.99  fof(f58,plain,(
% 11.83/1.99    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.83/1.99    inference(cnf_transformation,[],[f33])).
% 11.83/1.99  
% 11.83/1.99  fof(f55,plain,(
% 11.83/1.99    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.83/1.99    inference(cnf_transformation,[],[f28])).
% 11.83/1.99  
% 11.83/1.99  fof(f64,plain,(
% 11.83/1.99    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)),
% 11.83/1.99    inference(cnf_transformation,[],[f41])).
% 11.83/1.99  
% 11.83/1.99  fof(f60,plain,(
% 11.83/1.99    v2_pre_topc(sK0)),
% 11.83/1.99    inference(cnf_transformation,[],[f41])).
% 11.83/1.99  
% 11.83/1.99  cnf(c_16,negated_conjecture,
% 11.83/1.99      ( v4_pre_topc(sK1,sK0)
% 11.83/1.99      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 11.83/1.99      inference(cnf_transformation,[],[f63]) ).
% 11.83/1.99  
% 11.83/1.99  cnf(c_672,plain,
% 11.83/1.99      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 11.83/1.99      | v4_pre_topc(sK1,sK0) = iProver_top ),
% 11.83/1.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 11.83/1.99  
% 11.83/1.99  cnf(c_17,negated_conjecture,
% 11.83/1.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 11.83/1.99      inference(cnf_transformation,[],[f62]) ).
% 11.83/1.99  
% 11.83/1.99  cnf(c_671,plain,
% 11.83/1.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 11.83/1.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 11.83/1.99  
% 11.83/1.99  cnf(c_10,plain,
% 11.83/1.99      ( ~ v4_pre_topc(X0,X1)
% 11.83/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.83/1.99      | ~ l1_pre_topc(X1)
% 11.83/1.99      | k2_pre_topc(X1,X0) = X0 ),
% 11.83/1.99      inference(cnf_transformation,[],[f54]) ).
% 11.83/1.99  
% 11.83/1.99  cnf(c_678,plain,
% 11.83/1.99      ( k2_pre_topc(X0,X1) = X1
% 11.83/1.99      | v4_pre_topc(X1,X0) != iProver_top
% 11.83/1.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 11.83/1.99      | l1_pre_topc(X0) != iProver_top ),
% 11.83/1.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 11.83/1.99  
% 11.83/1.99  cnf(c_4810,plain,
% 11.83/1.99      ( k2_pre_topc(sK0,sK1) = sK1
% 11.83/1.99      | v4_pre_topc(sK1,sK0) != iProver_top
% 11.83/1.99      | l1_pre_topc(sK0) != iProver_top ),
% 11.83/1.99      inference(superposition,[status(thm)],[c_671,c_678]) ).
% 11.83/1.99  
% 11.83/1.99  cnf(c_18,negated_conjecture,
% 11.83/1.99      ( l1_pre_topc(sK0) ),
% 11.83/1.99      inference(cnf_transformation,[],[f61]) ).
% 11.83/1.99  
% 11.83/1.99  cnf(c_21,plain,
% 11.83/1.99      ( l1_pre_topc(sK0) = iProver_top ),
% 11.83/1.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 11.83/1.99  
% 11.83/1.99  cnf(c_5094,plain,
% 11.83/1.99      ( v4_pre_topc(sK1,sK0) != iProver_top
% 11.83/1.99      | k2_pre_topc(sK0,sK1) = sK1 ),
% 11.83/1.99      inference(global_propositional_subsumption,
% 11.83/1.99                [status(thm)],
% 11.83/1.99                [c_4810,c_21]) ).
% 11.83/1.99  
% 11.83/1.99  cnf(c_5095,plain,
% 11.83/1.99      ( k2_pre_topc(sK0,sK1) = sK1
% 11.83/1.99      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 11.83/1.99      inference(renaming,[status(thm)],[c_5094]) ).
% 11.83/1.99  
% 11.83/1.99  cnf(c_5100,plain,
% 11.83/1.99      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 11.83/1.99      | k2_pre_topc(sK0,sK1) = sK1 ),
% 11.83/1.99      inference(superposition,[status(thm)],[c_672,c_5095]) ).
% 11.83/1.99  
% 11.83/1.99  cnf(c_6,plain,
% 11.83/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.83/1.99      | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2))) = k7_subset_1(X1,X0,X2) ),
% 11.83/1.99      inference(cnf_transformation,[],[f70]) ).
% 11.83/1.99  
% 11.83/1.99  cnf(c_682,plain,
% 11.83/1.99      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X2,X0,X1)
% 11.83/1.99      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
% 11.83/1.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 11.83/1.99  
% 11.83/1.99  cnf(c_3440,plain,
% 11.83/1.99      ( k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0))) = k7_subset_1(u1_struct_0(sK0),sK1,X0) ),
% 11.83/1.99      inference(superposition,[status(thm)],[c_671,c_682]) ).
% 11.83/1.99  
% 11.83/1.99  cnf(c_1,plain,
% 11.83/1.99      ( r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0) ),
% 11.83/1.99      inference(cnf_transformation,[],[f67]) ).
% 11.83/1.99  
% 11.83/1.99  cnf(c_685,plain,
% 11.83/1.99      ( r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0) = iProver_top ),
% 11.83/1.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 11.83/1.99  
% 11.83/1.99  cnf(c_3461,plain,
% 11.83/1.99      ( r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,X0),sK1) = iProver_top ),
% 11.83/1.99      inference(superposition,[status(thm)],[c_3440,c_685]) ).
% 11.83/1.99  
% 11.83/1.99  cnf(c_8,plain,
% 11.83/1.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 11.83/1.99      inference(cnf_transformation,[],[f53]) ).
% 11.83/1.99  
% 11.83/1.99  cnf(c_680,plain,
% 11.83/1.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 11.83/1.99      | r1_tarski(X0,X1) != iProver_top ),
% 11.83/1.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 11.83/1.99  
% 11.83/1.99  cnf(c_4,plain,
% 11.83/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.83/1.99      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 11.83/1.99      inference(cnf_transformation,[],[f48]) ).
% 11.83/1.99  
% 11.83/1.99  cnf(c_684,plain,
% 11.83/1.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 11.83/1.99      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 11.83/1.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 11.83/1.99  
% 11.83/1.99  cnf(c_5,plain,
% 11.83/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.83/1.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 11.83/1.99      | k4_subset_1(X1,X0,X2) = k3_tarski(k2_tarski(X0,X2)) ),
% 11.83/1.99      inference(cnf_transformation,[],[f69]) ).
% 11.83/1.99  
% 11.83/1.99  cnf(c_683,plain,
% 11.83/1.99      ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
% 11.83/1.99      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 11.83/1.99      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
% 11.83/1.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 11.83/1.99  
% 11.83/1.99  cnf(c_4591,plain,
% 11.83/1.99      ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
% 11.83/1.99      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
% 11.83/1.99      | r1_tarski(X1,X0) != iProver_top ),
% 11.83/1.99      inference(superposition,[status(thm)],[c_680,c_683]) ).
% 11.83/1.99  
% 11.83/1.99  cnf(c_9122,plain,
% 11.83/1.99      ( k4_subset_1(X0,X1,k3_subset_1(X0,X2)) = k3_tarski(k2_tarski(X1,k3_subset_1(X0,X2)))
% 11.83/1.99      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
% 11.83/1.99      | r1_tarski(X1,X0) != iProver_top ),
% 11.83/1.99      inference(superposition,[status(thm)],[c_684,c_4591]) ).
% 11.83/1.99  
% 11.83/1.99  cnf(c_19607,plain,
% 11.83/1.99      ( k4_subset_1(X0,X1,k3_subset_1(X0,X2)) = k3_tarski(k2_tarski(X1,k3_subset_1(X0,X2)))
% 11.83/1.99      | r1_tarski(X2,X0) != iProver_top
% 11.83/1.99      | r1_tarski(X1,X0) != iProver_top ),
% 11.83/1.99      inference(superposition,[status(thm)],[c_680,c_9122]) ).
% 11.83/1.99  
% 11.83/1.99  cnf(c_21327,plain,
% 11.83/1.99      ( k4_subset_1(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0),k3_subset_1(sK1,X1)) = k3_tarski(k2_tarski(k7_subset_1(u1_struct_0(sK0),sK1,X0),k3_subset_1(sK1,X1)))
% 11.83/1.99      | r1_tarski(X1,sK1) != iProver_top ),
% 11.83/1.99      inference(superposition,[status(thm)],[c_3461,c_19607]) ).
% 11.83/1.99  
% 11.83/1.99  cnf(c_21679,plain,
% 11.83/1.99      ( k4_subset_1(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0),k3_subset_1(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X1))) = k3_tarski(k2_tarski(k7_subset_1(u1_struct_0(sK0),sK1,X0),k3_subset_1(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X1)))) ),
% 11.83/1.99      inference(superposition,[status(thm)],[c_3461,c_21327]) ).
% 11.83/1.99  
% 11.83/1.99  cnf(c_7,plain,
% 11.83/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.83/1.99      | k4_subset_1(X1,X0,k3_subset_1(X1,X0)) = k2_subset_1(X1) ),
% 11.83/1.99      inference(cnf_transformation,[],[f51]) ).
% 11.83/1.99  
% 11.83/1.99  cnf(c_681,plain,
% 11.83/1.99      ( k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = k2_subset_1(X0)
% 11.83/1.99      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 11.83/1.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 11.83/1.99  
% 11.83/1.99  cnf(c_3,plain,
% 11.83/1.99      ( k2_subset_1(X0) = X0 ),
% 11.83/1.99      inference(cnf_transformation,[],[f47]) ).
% 11.83/1.99  
% 11.83/1.99  cnf(c_712,plain,
% 11.83/1.99      ( k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = X0
% 11.83/1.99      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 11.83/1.99      inference(light_normalisation,[status(thm)],[c_681,c_3]) ).
% 11.83/1.99  
% 11.83/1.99  cnf(c_1589,plain,
% 11.83/1.99      ( k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = X0
% 11.83/1.99      | r1_tarski(X1,X0) != iProver_top ),
% 11.83/1.99      inference(superposition,[status(thm)],[c_680,c_712]) ).
% 11.83/1.99  
% 11.83/1.99  cnf(c_1673,plain,
% 11.83/1.99      ( k4_subset_1(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),k3_subset_1(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))) = X0 ),
% 11.83/1.99      inference(superposition,[status(thm)],[c_685,c_1589]) ).
% 11.83/1.99  
% 11.83/1.99  cnf(c_3459,plain,
% 11.83/1.99      ( k4_subset_1(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0),k3_subset_1(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0))) = sK1 ),
% 11.83/1.99      inference(superposition,[status(thm)],[c_3440,c_1673]) ).
% 11.83/1.99  
% 11.83/1.99  cnf(c_21695,plain,
% 11.83/1.99      ( k3_tarski(k2_tarski(k7_subset_1(u1_struct_0(sK0),sK1,X0),k3_subset_1(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0)))) = sK1 ),
% 11.83/1.99      inference(superposition,[status(thm)],[c_21679,c_3459]) ).
% 11.83/1.99  
% 11.83/1.99  cnf(c_2,plain,
% 11.83/1.99      ( k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(X0,X1)) ),
% 11.83/1.99      inference(cnf_transformation,[],[f68]) ).
% 11.83/1.99  
% 11.83/1.99  cnf(c_31375,plain,
% 11.83/1.99      ( k3_tarski(k2_tarski(k7_subset_1(u1_struct_0(sK0),sK1,X0),k3_subset_1(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0)))) = k3_tarski(k2_tarski(k7_subset_1(u1_struct_0(sK0),sK1,X0),sK1)) ),
% 11.83/1.99      inference(superposition,[status(thm)],[c_21695,c_2]) ).
% 11.83/1.99  
% 11.83/1.99  cnf(c_31402,plain,
% 11.83/1.99      ( k3_tarski(k2_tarski(k7_subset_1(u1_struct_0(sK0),sK1,X0),sK1)) = sK1 ),
% 11.83/1.99      inference(light_normalisation,[status(thm)],[c_31375,c_21695]) ).
% 11.83/1.99  
% 11.83/1.99  cnf(c_34404,plain,
% 11.83/1.99      ( k2_pre_topc(sK0,sK1) = sK1
% 11.83/1.99      | k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),sK1)) = sK1 ),
% 11.83/1.99      inference(superposition,[status(thm)],[c_5100,c_31402]) ).
% 11.83/1.99  
% 11.83/1.99  cnf(c_0,plain,
% 11.83/1.99      ( k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X1,X0)) ),
% 11.83/1.99      inference(cnf_transformation,[],[f66]) ).
% 11.83/1.99  
% 11.83/1.99  cnf(c_34461,plain,
% 11.83/1.99      ( k2_pre_topc(sK0,sK1) = sK1
% 11.83/1.99      | k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = sK1 ),
% 11.83/1.99      inference(superposition,[status(thm)],[c_34404,c_0]) ).
% 11.83/1.99  
% 11.83/1.99  cnf(c_11,plain,
% 11.83/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.83/1.99      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 11.83/1.99      | ~ l1_pre_topc(X1) ),
% 11.83/1.99      inference(cnf_transformation,[],[f56]) ).
% 11.83/1.99  
% 11.83/1.99  cnf(c_677,plain,
% 11.83/1.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 11.83/1.99      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 11.83/1.99      | l1_pre_topc(X1) != iProver_top ),
% 11.83/1.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 11.83/1.99  
% 11.83/1.99  cnf(c_4594,plain,
% 11.83/1.99      ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k3_tarski(k2_tarski(sK1,X0))
% 11.83/1.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 11.83/1.99      inference(superposition,[status(thm)],[c_671,c_683]) ).
% 11.83/1.99  
% 11.83/1.99  cnf(c_5106,plain,
% 11.83/1.99      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0)))
% 11.83/1.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.83/1.99      | l1_pre_topc(sK0) != iProver_top ),
% 11.83/1.99      inference(superposition,[status(thm)],[c_677,c_4594]) ).
% 11.83/1.99  
% 11.83/1.99  cnf(c_5907,plain,
% 11.83/1.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.83/1.99      | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0))) ),
% 11.83/1.99      inference(global_propositional_subsumption,
% 11.83/1.99                [status(thm)],
% 11.83/1.99                [c_5106,c_21]) ).
% 11.83/1.99  
% 11.83/1.99  cnf(c_5908,plain,
% 11.83/1.99      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0)))
% 11.83/1.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 11.83/1.99      inference(renaming,[status(thm)],[c_5907]) ).
% 11.83/1.99  
% 11.83/1.99  cnf(c_5918,plain,
% 11.83/1.99      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
% 11.83/1.99      inference(superposition,[status(thm)],[c_671,c_5908]) ).
% 11.83/1.99  
% 11.83/1.99  cnf(c_14,plain,
% 11.83/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.83/1.99      | ~ l1_pre_topc(X1)
% 11.83/1.99      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
% 11.83/1.99      inference(cnf_transformation,[],[f59]) ).
% 11.83/1.99  
% 11.83/1.99  cnf(c_674,plain,
% 11.83/1.99      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
% 11.83/1.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 11.83/1.99      | l1_pre_topc(X0) != iProver_top ),
% 11.83/1.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 11.83/1.99  
% 11.83/1.99  cnf(c_1112,plain,
% 11.83/1.99      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
% 11.83/1.99      | l1_pre_topc(sK0) != iProver_top ),
% 11.83/1.99      inference(superposition,[status(thm)],[c_671,c_674]) ).
% 11.83/1.99  
% 11.83/1.99  cnf(c_936,plain,
% 11.83/1.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.83/1.99      | ~ l1_pre_topc(sK0)
% 11.83/1.99      | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 11.83/1.99      inference(instantiation,[status(thm)],[c_14]) ).
% 11.83/1.99  
% 11.83/1.99  cnf(c_1417,plain,
% 11.83/1.99      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 11.83/1.99      inference(global_propositional_subsumption,
% 11.83/1.99                [status(thm)],
% 11.83/1.99                [c_1112,c_18,c_17,c_936]) ).
% 11.83/1.99  
% 11.83/1.99  cnf(c_5920,plain,
% 11.83/1.99      ( k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k2_pre_topc(sK0,sK1) ),
% 11.83/1.99      inference(light_normalisation,[status(thm)],[c_5918,c_1417]) ).
% 11.83/1.99  
% 11.83/1.99  cnf(c_34464,plain,
% 11.83/1.99      ( k2_pre_topc(sK0,sK1) = sK1 ),
% 11.83/1.99      inference(demodulation,[status(thm)],[c_34461,c_5920]) ).
% 11.83/1.99  
% 11.83/1.99  cnf(c_13,plain,
% 11.83/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.83/1.99      | ~ l1_pre_topc(X1)
% 11.83/1.99      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
% 11.83/1.99      inference(cnf_transformation,[],[f58]) ).
% 11.83/1.99  
% 11.83/1.99  cnf(c_675,plain,
% 11.83/1.99      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
% 11.83/1.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 11.83/1.99      | l1_pre_topc(X0) != iProver_top ),
% 11.83/1.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 11.83/1.99  
% 11.83/1.99  cnf(c_2189,plain,
% 11.83/1.99      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 11.83/1.99      | l1_pre_topc(sK0) != iProver_top ),
% 11.83/1.99      inference(superposition,[status(thm)],[c_671,c_675]) ).
% 11.83/1.99  
% 11.83/1.99  cnf(c_939,plain,
% 11.83/1.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.83/1.99      | ~ l1_pre_topc(sK0)
% 11.83/1.99      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 11.83/1.99      inference(instantiation,[status(thm)],[c_13]) ).
% 11.83/1.99  
% 11.83/1.99  cnf(c_2653,plain,
% 11.83/1.99      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 11.83/1.99      inference(global_propositional_subsumption,
% 11.83/1.99                [status(thm)],
% 11.83/1.99                [c_2189,c_18,c_17,c_939]) ).
% 11.83/1.99  
% 11.83/1.99  cnf(c_34671,plain,
% 11.83/1.99      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 11.83/1.99      inference(demodulation,[status(thm)],[c_34464,c_2653]) ).
% 11.83/1.99  
% 11.83/1.99  cnf(c_9,plain,
% 11.83/1.99      ( v4_pre_topc(X0,X1)
% 11.83/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.83/1.99      | ~ l1_pre_topc(X1)
% 11.83/1.99      | ~ v2_pre_topc(X1)
% 11.83/1.99      | k2_pre_topc(X1,X0) != X0 ),
% 11.83/1.99      inference(cnf_transformation,[],[f55]) ).
% 11.83/1.99  
% 11.83/1.99  cnf(c_933,plain,
% 11.83/1.99      ( v4_pre_topc(sK1,sK0)
% 11.83/1.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.83/1.99      | ~ l1_pre_topc(sK0)
% 11.83/1.99      | ~ v2_pre_topc(sK0)
% 11.83/1.99      | k2_pre_topc(sK0,sK1) != sK1 ),
% 11.83/1.99      inference(instantiation,[status(thm)],[c_9]) ).
% 11.83/1.99  
% 11.83/1.99  cnf(c_15,negated_conjecture,
% 11.83/1.99      ( ~ v4_pre_topc(sK1,sK0)
% 11.83/1.99      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
% 11.83/1.99      inference(cnf_transformation,[],[f64]) ).
% 11.83/1.99  
% 11.83/1.99  cnf(c_19,negated_conjecture,
% 11.83/1.99      ( v2_pre_topc(sK0) ),
% 11.83/1.99      inference(cnf_transformation,[],[f60]) ).
% 11.83/1.99  
% 11.83/1.99  cnf(contradiction,plain,
% 11.83/1.99      ( $false ),
% 11.83/1.99      inference(minisat,
% 11.83/1.99                [status(thm)],
% 11.83/1.99                [c_34671,c_34464,c_933,c_15,c_17,c_18,c_19]) ).
% 11.83/1.99  
% 11.83/1.99  
% 11.83/1.99  % SZS output end CNFRefutation for theBenchmark.p
% 11.83/1.99  
% 11.83/1.99  ------                               Statistics
% 11.83/1.99  
% 11.83/1.99  ------ Selected
% 11.83/1.99  
% 11.83/1.99  total_time:                             1.201
% 11.83/1.99  
%------------------------------------------------------------------------------
