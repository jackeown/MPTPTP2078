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
% DateTime   : Thu Dec  3 12:14:31 EST 2020

% Result     : Theorem 39.50s
% Output     : CNFRefutation 39.50s
% Verified   : 
% Statistics : Number of formulae       :  142 (2970 expanded)
%              Number of clauses        :   79 ( 794 expanded)
%              Number of leaves         :   19 ( 700 expanded)
%              Depth                    :   23
%              Number of atoms          :  333 (11995 expanded)
%              Number of equality atoms :  175 (4322 expanded)
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

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f35,plain,(
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
    inference(flattening,[],[f35])).

fof(f38,plain,(
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

fof(f37,plain,
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

fof(f39,plain,
    ( ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f36,f38,f37])).

fof(f60,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f39])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f63,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f40,f51])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f49,f63])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f66,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k6_subset_1(X0,X1) ),
    inference(definition_unfolding,[],[f48,f63])).

fof(f61,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f39])).

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

fof(f25,plain,(
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
    inference(flattening,[],[f25])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f59,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f7,axiom,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f5,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f21])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k2_tarski(X1,X2)) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f47,f43])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f64,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) ),
    inference(definition_unfolding,[],[f41,f43,f43,f43])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) != X1
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f62,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f58,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_627,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2))) = k7_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_637,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X2,X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_6,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_674,plain,
    ( k7_subset_1(X0,X1,X2) = k6_subset_1(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_637,c_6])).

cnf(c_1905,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k6_subset_1(sK1,X0) ),
    inference(superposition,[status(thm)],[c_627,c_674])).

cnf(c_16,negated_conjecture,
    ( v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_628,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1920,plain,
    ( k6_subset_1(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1905,c_628])).

cnf(c_10,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_634,plain,
    ( k2_pre_topc(X0,X1) = X1
    | v4_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_5667,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | v4_pre_topc(sK1,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_627,c_634])).

cnf(c_18,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_21,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_5753,plain,
    ( v4_pre_topc(sK1,sK0) != iProver_top
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5667,c_21])).

cnf(c_5754,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5753])).

cnf(c_5759,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k6_subset_1(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_1920,c_5754])).

cnf(c_4,plain,
    ( m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_639,plain,
    ( m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X0,k3_subset_1(X1,X0)) = k2_subset_1(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_636,plain,
    ( k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = k2_subset_1(X0)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_665,plain,
    ( k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = X0
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_636,c_2])).

cnf(c_1576,plain,
    ( k4_subset_1(X0,k6_subset_1(X0,X1),k3_subset_1(X0,k6_subset_1(X0,X1))) = X0 ),
    inference(superposition,[status(thm)],[c_639,c_665])).

cnf(c_6678,plain,
    ( k4_subset_1(sK1,k2_tops_1(sK0,sK1),k3_subset_1(sK1,k2_tops_1(sK0,sK1))) = sK1
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_5759,c_1576])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_640,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X0,X2) = k3_tarski(k2_tarski(X0,X2)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_638,plain,
    ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_5622,plain,
    ( k4_subset_1(X0,k6_subset_1(X0,X1),X2) = k3_tarski(k2_tarski(k6_subset_1(X0,X1),X2))
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_639,c_638])).

cnf(c_9933,plain,
    ( k4_subset_1(X0,k6_subset_1(X0,X1),k3_subset_1(X0,X2)) = k3_tarski(k2_tarski(k6_subset_1(X0,X1),k3_subset_1(X0,X2)))
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_640,c_5622])).

cnf(c_17381,plain,
    ( k4_subset_1(X0,k6_subset_1(X0,X1),k3_subset_1(X0,k6_subset_1(X0,X2))) = k3_tarski(k2_tarski(k6_subset_1(X0,X1),k3_subset_1(X0,k6_subset_1(X0,X2)))) ),
    inference(superposition,[status(thm)],[c_639,c_9933])).

cnf(c_17656,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k3_tarski(k2_tarski(k6_subset_1(sK1,k1_tops_1(sK0,sK1)),k3_subset_1(sK1,k6_subset_1(sK1,X0)))) = k4_subset_1(sK1,k2_tops_1(sK0,sK1),k3_subset_1(sK1,k6_subset_1(sK1,X0))) ),
    inference(superposition,[status(thm)],[c_5759,c_17381])).

cnf(c_18194,plain,
    ( k4_subset_1(sK1,k2_tops_1(sK0,sK1),k3_subset_1(sK1,k6_subset_1(sK1,X0))) = k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),k3_subset_1(sK1,k6_subset_1(sK1,X0))))
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_5759,c_17656])).

cnf(c_18473,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),k3_subset_1(sK1,k6_subset_1(sK1,k1_tops_1(sK0,sK1))))) = k4_subset_1(sK1,k2_tops_1(sK0,sK1),k3_subset_1(sK1,k2_tops_1(sK0,sK1))) ),
    inference(superposition,[status(thm)],[c_5759,c_18194])).

cnf(c_18743,plain,
    ( k4_subset_1(sK1,k2_tops_1(sK0,sK1),k3_subset_1(sK1,k2_tops_1(sK0,sK1))) = k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),k3_subset_1(sK1,k2_tops_1(sK0,sK1))))
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_5759,c_18473])).

cnf(c_18822,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),k3_subset_1(sK1,k2_tops_1(sK0,sK1)))) = sK1 ),
    inference(superposition,[status(thm)],[c_6678,c_18743])).

cnf(c_0,plain,
    ( k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_20620,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),k3_subset_1(sK1,k2_tops_1(sK0,sK1)))) = k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),sK1)) ),
    inference(superposition,[status(thm)],[c_18822,c_0])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_633,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_5624,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k3_tarski(k2_tarski(sK1,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_627,c_638])).

cnf(c_5765,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_633,c_5624])).

cnf(c_6212,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5765,c_21])).

cnf(c_6213,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_6212])).

cnf(c_6223,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
    inference(superposition,[status(thm)],[c_627,c_6213])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_630,plain,
    ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1141,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_627,c_630])).

cnf(c_918,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1524,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1141,c_18,c_17,c_918])).

cnf(c_6225,plain,
    ( k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k2_pre_topc(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_6223,c_1524])).

cnf(c_1,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1341,plain,
    ( k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X1,X0)))) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(superposition,[status(thm)],[c_1,c_0])).

cnf(c_1510,plain,
    ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X0)) ),
    inference(superposition,[status(thm)],[c_0,c_1341])).

cnf(c_2294,plain,
    ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(k3_tarski(k2_tarski(X1,X0)),X1)) ),
    inference(superposition,[status(thm)],[c_1,c_1510])).

cnf(c_2329,plain,
    ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X0)) = k3_tarski(k2_tarski(k3_tarski(k2_tarski(X1,X0)),X1)) ),
    inference(superposition,[status(thm)],[c_2294,c_1510])).

cnf(c_3054,plain,
    ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X0)) = k3_tarski(k2_tarski(X1,k3_tarski(k2_tarski(X1,X0)))) ),
    inference(superposition,[status(thm)],[c_1,c_2329])).

cnf(c_3116,plain,
    ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X0)) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_3054,c_0])).

cnf(c_3216,plain,
    ( k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(superposition,[status(thm)],[c_1,c_3116])).

cnf(c_3434,plain,
    ( k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X1,X0)))) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(superposition,[status(thm)],[c_1,c_3216])).

cnf(c_6261,plain,
    ( k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1))) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
    inference(superposition,[status(thm)],[c_6225,c_3434])).

cnf(c_6262,plain,
    ( k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1))) = k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),sK1)) ),
    inference(superposition,[status(thm)],[c_6225,c_1341])).

cnf(c_6265,plain,
    ( k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1))) = k2_pre_topc(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_6261,c_6225,c_6262])).

cnf(c_6267,plain,
    ( k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_6265,c_6262])).

cnf(c_20643,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),k3_subset_1(sK1,k2_tops_1(sK0,sK1)))) = k2_pre_topc(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_20620,c_6267])).

cnf(c_22704,plain,
    ( k2_pre_topc(sK0,sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_20643,c_18822])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_631,plain,
    ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2129,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_627,c_631])).

cnf(c_923,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_2922,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2129,c_18,c_17,c_923])).

cnf(c_79940,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_22704,c_2922])).

cnf(c_9,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | k2_pre_topc(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_913,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | k2_pre_topc(sK0,sK1) != sK1 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_15,negated_conjecture,
    ( ~ v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_19,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f58])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_79940,c_22704,c_913,c_15,c_17,c_18,c_19])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:00:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 39.50/5.52  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 39.50/5.52  
% 39.50/5.52  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 39.50/5.52  
% 39.50/5.52  ------  iProver source info
% 39.50/5.52  
% 39.50/5.52  git: date: 2020-06-30 10:37:57 +0100
% 39.50/5.52  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 39.50/5.52  git: non_committed_changes: false
% 39.50/5.52  git: last_make_outside_of_git: false
% 39.50/5.52  
% 39.50/5.52  ------ 
% 39.50/5.52  ------ Parsing...
% 39.50/5.52  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 39.50/5.52  
% 39.50/5.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 39.50/5.52  
% 39.50/5.52  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 39.50/5.52  
% 39.50/5.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 39.50/5.52  ------ Proving...
% 39.50/5.52  ------ Problem Properties 
% 39.50/5.52  
% 39.50/5.52  
% 39.50/5.52  clauses                                 20
% 39.50/5.52  conjectures                             5
% 39.50/5.52  EPR                                     2
% 39.50/5.52  Horn                                    19
% 39.50/5.52  unary                                   8
% 39.50/5.52  binary                                  5
% 39.50/5.52  lits                                    43
% 39.50/5.52  lits eq                                 13
% 39.50/5.52  fd_pure                                 0
% 39.50/5.52  fd_pseudo                               0
% 39.50/5.52  fd_cond                                 0
% 39.50/5.52  fd_pseudo_cond                          0
% 39.50/5.52  AC symbols                              0
% 39.50/5.52  
% 39.50/5.52  ------ Input Options Time Limit: Unbounded
% 39.50/5.52  
% 39.50/5.52  
% 39.50/5.52  ------ 
% 39.50/5.52  Current options:
% 39.50/5.52  ------ 
% 39.50/5.52  
% 39.50/5.52  
% 39.50/5.52  
% 39.50/5.52  
% 39.50/5.52  ------ Proving...
% 39.50/5.52  
% 39.50/5.52  
% 39.50/5.52  % SZS status Theorem for theBenchmark.p
% 39.50/5.52  
% 39.50/5.52  % SZS output start CNFRefutation for theBenchmark.p
% 39.50/5.52  
% 39.50/5.52  fof(f18,conjecture,(
% 39.50/5.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 39.50/5.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.50/5.52  
% 39.50/5.52  fof(f19,negated_conjecture,(
% 39.50/5.52    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 39.50/5.52    inference(negated_conjecture,[],[f18])).
% 39.50/5.52  
% 39.50/5.52  fof(f33,plain,(
% 39.50/5.52    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 39.50/5.52    inference(ennf_transformation,[],[f19])).
% 39.50/5.52  
% 39.50/5.52  fof(f34,plain,(
% 39.50/5.52    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 39.50/5.52    inference(flattening,[],[f33])).
% 39.50/5.52  
% 39.50/5.52  fof(f35,plain,(
% 39.50/5.52    ? [X0] : (? [X1] : (((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 39.50/5.52    inference(nnf_transformation,[],[f34])).
% 39.50/5.52  
% 39.50/5.52  fof(f36,plain,(
% 39.50/5.52    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 39.50/5.52    inference(flattening,[],[f35])).
% 39.50/5.52  
% 39.50/5.52  fof(f38,plain,(
% 39.50/5.52    ( ! [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) != k2_tops_1(X0,sK1) | ~v4_pre_topc(sK1,X0)) & (k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) = k2_tops_1(X0,sK1) | v4_pre_topc(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 39.50/5.52    introduced(choice_axiom,[])).
% 39.50/5.52  
% 39.50/5.52  fof(f37,plain,(
% 39.50/5.52    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) != k2_tops_1(sK0,X1) | ~v4_pre_topc(X1,sK0)) & (k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) = k2_tops_1(sK0,X1) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 39.50/5.52    introduced(choice_axiom,[])).
% 39.50/5.52  
% 39.50/5.52  fof(f39,plain,(
% 39.50/5.52    ((k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)) & (k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 39.50/5.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f36,f38,f37])).
% 39.50/5.52  
% 39.50/5.52  fof(f60,plain,(
% 39.50/5.52    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 39.50/5.52    inference(cnf_transformation,[],[f39])).
% 39.50/5.52  
% 39.50/5.52  fof(f10,axiom,(
% 39.50/5.52    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 39.50/5.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.50/5.52  
% 39.50/5.52  fof(f23,plain,(
% 39.50/5.52    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 39.50/5.52    inference(ennf_transformation,[],[f10])).
% 39.50/5.52  
% 39.50/5.52  fof(f49,plain,(
% 39.50/5.52    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 39.50/5.52    inference(cnf_transformation,[],[f23])).
% 39.50/5.52  
% 39.50/5.52  fof(f1,axiom,(
% 39.50/5.52    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 39.50/5.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.50/5.52  
% 39.50/5.52  fof(f40,plain,(
% 39.50/5.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 39.50/5.52    inference(cnf_transformation,[],[f1])).
% 39.50/5.52  
% 39.50/5.52  fof(f12,axiom,(
% 39.50/5.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 39.50/5.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.50/5.52  
% 39.50/5.52  fof(f51,plain,(
% 39.50/5.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 39.50/5.52    inference(cnf_transformation,[],[f12])).
% 39.50/5.52  
% 39.50/5.52  fof(f63,plain,(
% 39.50/5.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 39.50/5.52    inference(definition_unfolding,[],[f40,f51])).
% 39.50/5.52  
% 39.50/5.52  fof(f67,plain,(
% 39.50/5.52    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 39.50/5.52    inference(definition_unfolding,[],[f49,f63])).
% 39.50/5.52  
% 39.50/5.52  fof(f9,axiom,(
% 39.50/5.52    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 39.50/5.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.50/5.52  
% 39.50/5.52  fof(f48,plain,(
% 39.50/5.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 39.50/5.52    inference(cnf_transformation,[],[f9])).
% 39.50/5.52  
% 39.50/5.52  fof(f66,plain,(
% 39.50/5.52    ( ! [X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k6_subset_1(X0,X1)) )),
% 39.50/5.52    inference(definition_unfolding,[],[f48,f63])).
% 39.50/5.52  
% 39.50/5.52  fof(f61,plain,(
% 39.50/5.52    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)),
% 39.50/5.52    inference(cnf_transformation,[],[f39])).
% 39.50/5.52  
% 39.50/5.52  fof(f13,axiom,(
% 39.50/5.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 39.50/5.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.50/5.52  
% 39.50/5.52  fof(f25,plain,(
% 39.50/5.52    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 39.50/5.52    inference(ennf_transformation,[],[f13])).
% 39.50/5.52  
% 39.50/5.52  fof(f26,plain,(
% 39.50/5.52    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 39.50/5.52    inference(flattening,[],[f25])).
% 39.50/5.52  
% 39.50/5.52  fof(f52,plain,(
% 39.50/5.52    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 39.50/5.52    inference(cnf_transformation,[],[f26])).
% 39.50/5.52  
% 39.50/5.52  fof(f59,plain,(
% 39.50/5.52    l1_pre_topc(sK0)),
% 39.50/5.52    inference(cnf_transformation,[],[f39])).
% 39.50/5.52  
% 39.50/5.52  fof(f7,axiom,(
% 39.50/5.52    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))),
% 39.50/5.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.50/5.52  
% 39.50/5.52  fof(f46,plain,(
% 39.50/5.52    ( ! [X0,X1] : (m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 39.50/5.52    inference(cnf_transformation,[],[f7])).
% 39.50/5.52  
% 39.50/5.52  fof(f11,axiom,(
% 39.50/5.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 39.50/5.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.50/5.52  
% 39.50/5.52  fof(f24,plain,(
% 39.50/5.52    ! [X0,X1] : (k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 39.50/5.52    inference(ennf_transformation,[],[f11])).
% 39.50/5.52  
% 39.50/5.52  fof(f50,plain,(
% 39.50/5.52    ( ! [X0,X1] : (k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 39.50/5.52    inference(cnf_transformation,[],[f24])).
% 39.50/5.52  
% 39.50/5.52  fof(f5,axiom,(
% 39.50/5.52    ! [X0] : k2_subset_1(X0) = X0),
% 39.50/5.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.50/5.52  
% 39.50/5.52  fof(f44,plain,(
% 39.50/5.52    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 39.50/5.52    inference(cnf_transformation,[],[f5])).
% 39.50/5.52  
% 39.50/5.52  fof(f6,axiom,(
% 39.50/5.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 39.50/5.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.50/5.52  
% 39.50/5.52  fof(f20,plain,(
% 39.50/5.52    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 39.50/5.52    inference(ennf_transformation,[],[f6])).
% 39.50/5.52  
% 39.50/5.52  fof(f45,plain,(
% 39.50/5.52    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 39.50/5.52    inference(cnf_transformation,[],[f20])).
% 39.50/5.52  
% 39.50/5.52  fof(f8,axiom,(
% 39.50/5.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 39.50/5.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.50/5.52  
% 39.50/5.52  fof(f21,plain,(
% 39.50/5.52    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 39.50/5.52    inference(ennf_transformation,[],[f8])).
% 39.50/5.52  
% 39.50/5.52  fof(f22,plain,(
% 39.50/5.52    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 39.50/5.52    inference(flattening,[],[f21])).
% 39.50/5.52  
% 39.50/5.52  fof(f47,plain,(
% 39.50/5.52    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 39.50/5.52    inference(cnf_transformation,[],[f22])).
% 39.50/5.52  
% 39.50/5.52  fof(f4,axiom,(
% 39.50/5.52    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 39.50/5.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.50/5.52  
% 39.50/5.52  fof(f43,plain,(
% 39.50/5.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 39.50/5.52    inference(cnf_transformation,[],[f4])).
% 39.50/5.52  
% 39.50/5.52  fof(f65,plain,(
% 39.50/5.52    ( ! [X2,X0,X1] : (k3_tarski(k2_tarski(X1,X2)) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 39.50/5.52    inference(definition_unfolding,[],[f47,f43])).
% 39.50/5.52  
% 39.50/5.52  fof(f2,axiom,(
% 39.50/5.52    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))),
% 39.50/5.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.50/5.52  
% 39.50/5.52  fof(f41,plain,(
% 39.50/5.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 39.50/5.52    inference(cnf_transformation,[],[f2])).
% 39.50/5.52  
% 39.50/5.52  fof(f64,plain,(
% 39.50/5.52    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1))))) )),
% 39.50/5.52    inference(definition_unfolding,[],[f41,f43,f43,f43])).
% 39.50/5.52  
% 39.50/5.52  fof(f14,axiom,(
% 39.50/5.52    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 39.50/5.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.50/5.52  
% 39.50/5.52  fof(f27,plain,(
% 39.50/5.52    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 39.50/5.52    inference(ennf_transformation,[],[f14])).
% 39.50/5.52  
% 39.50/5.52  fof(f28,plain,(
% 39.50/5.52    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 39.50/5.52    inference(flattening,[],[f27])).
% 39.50/5.52  
% 39.50/5.52  fof(f54,plain,(
% 39.50/5.52    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 39.50/5.52    inference(cnf_transformation,[],[f28])).
% 39.50/5.52  
% 39.50/5.52  fof(f17,axiom,(
% 39.50/5.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)))),
% 39.50/5.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.50/5.52  
% 39.50/5.52  fof(f32,plain,(
% 39.50/5.52    ! [X0] : (! [X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 39.50/5.52    inference(ennf_transformation,[],[f17])).
% 39.50/5.52  
% 39.50/5.52  fof(f57,plain,(
% 39.50/5.52    ( ! [X0,X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 39.50/5.52    inference(cnf_transformation,[],[f32])).
% 39.50/5.52  
% 39.50/5.52  fof(f3,axiom,(
% 39.50/5.52    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 39.50/5.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.50/5.52  
% 39.50/5.52  fof(f42,plain,(
% 39.50/5.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 39.50/5.52    inference(cnf_transformation,[],[f3])).
% 39.50/5.52  
% 39.50/5.52  fof(f16,axiom,(
% 39.50/5.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)))),
% 39.50/5.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.50/5.52  
% 39.50/5.52  fof(f31,plain,(
% 39.50/5.52    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 39.50/5.52    inference(ennf_transformation,[],[f16])).
% 39.50/5.52  
% 39.50/5.52  fof(f56,plain,(
% 39.50/5.52    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 39.50/5.52    inference(cnf_transformation,[],[f31])).
% 39.50/5.52  
% 39.50/5.52  fof(f53,plain,(
% 39.50/5.52    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 39.50/5.52    inference(cnf_transformation,[],[f26])).
% 39.50/5.52  
% 39.50/5.52  fof(f62,plain,(
% 39.50/5.52    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)),
% 39.50/5.52    inference(cnf_transformation,[],[f39])).
% 39.50/5.52  
% 39.50/5.52  fof(f58,plain,(
% 39.50/5.52    v2_pre_topc(sK0)),
% 39.50/5.52    inference(cnf_transformation,[],[f39])).
% 39.50/5.52  
% 39.50/5.52  cnf(c_17,negated_conjecture,
% 39.50/5.52      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 39.50/5.52      inference(cnf_transformation,[],[f60]) ).
% 39.50/5.52  
% 39.50/5.52  cnf(c_627,plain,
% 39.50/5.52      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 39.50/5.52      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 39.50/5.52  
% 39.50/5.52  cnf(c_7,plain,
% 39.50/5.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 39.50/5.52      | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2))) = k7_subset_1(X1,X0,X2) ),
% 39.50/5.52      inference(cnf_transformation,[],[f67]) ).
% 39.50/5.52  
% 39.50/5.52  cnf(c_637,plain,
% 39.50/5.52      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X2,X0,X1)
% 39.50/5.52      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
% 39.50/5.52      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 39.50/5.52  
% 39.50/5.52  cnf(c_6,plain,
% 39.50/5.52      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k6_subset_1(X0,X1) ),
% 39.50/5.52      inference(cnf_transformation,[],[f66]) ).
% 39.50/5.52  
% 39.50/5.52  cnf(c_674,plain,
% 39.50/5.52      ( k7_subset_1(X0,X1,X2) = k6_subset_1(X1,X2)
% 39.50/5.52      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 39.50/5.52      inference(light_normalisation,[status(thm)],[c_637,c_6]) ).
% 39.50/5.52  
% 39.50/5.52  cnf(c_1905,plain,
% 39.50/5.52      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k6_subset_1(sK1,X0) ),
% 39.50/5.52      inference(superposition,[status(thm)],[c_627,c_674]) ).
% 39.50/5.52  
% 39.50/5.52  cnf(c_16,negated_conjecture,
% 39.50/5.52      ( v4_pre_topc(sK1,sK0)
% 39.50/5.52      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 39.50/5.52      inference(cnf_transformation,[],[f61]) ).
% 39.50/5.52  
% 39.50/5.52  cnf(c_628,plain,
% 39.50/5.52      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 39.50/5.52      | v4_pre_topc(sK1,sK0) = iProver_top ),
% 39.50/5.52      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 39.50/5.52  
% 39.50/5.52  cnf(c_1920,plain,
% 39.50/5.52      ( k6_subset_1(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 39.50/5.52      | v4_pre_topc(sK1,sK0) = iProver_top ),
% 39.50/5.52      inference(demodulation,[status(thm)],[c_1905,c_628]) ).
% 39.50/5.52  
% 39.50/5.52  cnf(c_10,plain,
% 39.50/5.52      ( ~ v4_pre_topc(X0,X1)
% 39.50/5.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 39.50/5.52      | ~ l1_pre_topc(X1)
% 39.50/5.52      | k2_pre_topc(X1,X0) = X0 ),
% 39.50/5.52      inference(cnf_transformation,[],[f52]) ).
% 39.50/5.52  
% 39.50/5.52  cnf(c_634,plain,
% 39.50/5.52      ( k2_pre_topc(X0,X1) = X1
% 39.50/5.52      | v4_pre_topc(X1,X0) != iProver_top
% 39.50/5.52      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 39.50/5.52      | l1_pre_topc(X0) != iProver_top ),
% 39.50/5.52      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 39.50/5.52  
% 39.50/5.52  cnf(c_5667,plain,
% 39.50/5.52      ( k2_pre_topc(sK0,sK1) = sK1
% 39.50/5.52      | v4_pre_topc(sK1,sK0) != iProver_top
% 39.50/5.52      | l1_pre_topc(sK0) != iProver_top ),
% 39.50/5.52      inference(superposition,[status(thm)],[c_627,c_634]) ).
% 39.50/5.52  
% 39.50/5.52  cnf(c_18,negated_conjecture,
% 39.50/5.52      ( l1_pre_topc(sK0) ),
% 39.50/5.52      inference(cnf_transformation,[],[f59]) ).
% 39.50/5.52  
% 39.50/5.52  cnf(c_21,plain,
% 39.50/5.52      ( l1_pre_topc(sK0) = iProver_top ),
% 39.50/5.52      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 39.50/5.52  
% 39.50/5.52  cnf(c_5753,plain,
% 39.50/5.52      ( v4_pre_topc(sK1,sK0) != iProver_top
% 39.50/5.52      | k2_pre_topc(sK0,sK1) = sK1 ),
% 39.50/5.52      inference(global_propositional_subsumption,
% 39.50/5.52                [status(thm)],
% 39.50/5.52                [c_5667,c_21]) ).
% 39.50/5.52  
% 39.50/5.52  cnf(c_5754,plain,
% 39.50/5.52      ( k2_pre_topc(sK0,sK1) = sK1
% 39.50/5.52      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 39.50/5.52      inference(renaming,[status(thm)],[c_5753]) ).
% 39.50/5.52  
% 39.50/5.52  cnf(c_5759,plain,
% 39.50/5.52      ( k2_pre_topc(sK0,sK1) = sK1
% 39.50/5.52      | k6_subset_1(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 39.50/5.52      inference(superposition,[status(thm)],[c_1920,c_5754]) ).
% 39.50/5.52  
% 39.50/5.52  cnf(c_4,plain,
% 39.50/5.52      ( m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
% 39.50/5.52      inference(cnf_transformation,[],[f46]) ).
% 39.50/5.52  
% 39.50/5.52  cnf(c_639,plain,
% 39.50/5.52      ( m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) = iProver_top ),
% 39.50/5.52      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 39.50/5.52  
% 39.50/5.52  cnf(c_8,plain,
% 39.50/5.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 39.50/5.52      | k4_subset_1(X1,X0,k3_subset_1(X1,X0)) = k2_subset_1(X1) ),
% 39.50/5.52      inference(cnf_transformation,[],[f50]) ).
% 39.50/5.52  
% 39.50/5.52  cnf(c_636,plain,
% 39.50/5.52      ( k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = k2_subset_1(X0)
% 39.50/5.52      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 39.50/5.52      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 39.50/5.52  
% 39.50/5.52  cnf(c_2,plain,
% 39.50/5.52      ( k2_subset_1(X0) = X0 ),
% 39.50/5.52      inference(cnf_transformation,[],[f44]) ).
% 39.50/5.52  
% 39.50/5.52  cnf(c_665,plain,
% 39.50/5.52      ( k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = X0
% 39.50/5.52      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 39.50/5.52      inference(light_normalisation,[status(thm)],[c_636,c_2]) ).
% 39.50/5.52  
% 39.50/5.52  cnf(c_1576,plain,
% 39.50/5.52      ( k4_subset_1(X0,k6_subset_1(X0,X1),k3_subset_1(X0,k6_subset_1(X0,X1))) = X0 ),
% 39.50/5.52      inference(superposition,[status(thm)],[c_639,c_665]) ).
% 39.50/5.52  
% 39.50/5.52  cnf(c_6678,plain,
% 39.50/5.52      ( k4_subset_1(sK1,k2_tops_1(sK0,sK1),k3_subset_1(sK1,k2_tops_1(sK0,sK1))) = sK1
% 39.50/5.52      | k2_pre_topc(sK0,sK1) = sK1 ),
% 39.50/5.52      inference(superposition,[status(thm)],[c_5759,c_1576]) ).
% 39.50/5.52  
% 39.50/5.52  cnf(c_3,plain,
% 39.50/5.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 39.50/5.52      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 39.50/5.52      inference(cnf_transformation,[],[f45]) ).
% 39.50/5.52  
% 39.50/5.52  cnf(c_640,plain,
% 39.50/5.52      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 39.50/5.52      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 39.50/5.52      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 39.50/5.52  
% 39.50/5.52  cnf(c_5,plain,
% 39.50/5.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 39.50/5.52      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 39.50/5.52      | k4_subset_1(X1,X0,X2) = k3_tarski(k2_tarski(X0,X2)) ),
% 39.50/5.52      inference(cnf_transformation,[],[f65]) ).
% 39.50/5.52  
% 39.50/5.52  cnf(c_638,plain,
% 39.50/5.52      ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
% 39.50/5.52      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 39.50/5.52      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
% 39.50/5.52      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 39.50/5.52  
% 39.50/5.52  cnf(c_5622,plain,
% 39.50/5.52      ( k4_subset_1(X0,k6_subset_1(X0,X1),X2) = k3_tarski(k2_tarski(k6_subset_1(X0,X1),X2))
% 39.50/5.52      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
% 39.50/5.52      inference(superposition,[status(thm)],[c_639,c_638]) ).
% 39.50/5.52  
% 39.50/5.52  cnf(c_9933,plain,
% 39.50/5.52      ( k4_subset_1(X0,k6_subset_1(X0,X1),k3_subset_1(X0,X2)) = k3_tarski(k2_tarski(k6_subset_1(X0,X1),k3_subset_1(X0,X2)))
% 39.50/5.52      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
% 39.50/5.52      inference(superposition,[status(thm)],[c_640,c_5622]) ).
% 39.50/5.52  
% 39.50/5.52  cnf(c_17381,plain,
% 39.50/5.52      ( k4_subset_1(X0,k6_subset_1(X0,X1),k3_subset_1(X0,k6_subset_1(X0,X2))) = k3_tarski(k2_tarski(k6_subset_1(X0,X1),k3_subset_1(X0,k6_subset_1(X0,X2)))) ),
% 39.50/5.52      inference(superposition,[status(thm)],[c_639,c_9933]) ).
% 39.50/5.52  
% 39.50/5.52  cnf(c_17656,plain,
% 39.50/5.52      ( k2_pre_topc(sK0,sK1) = sK1
% 39.50/5.52      | k3_tarski(k2_tarski(k6_subset_1(sK1,k1_tops_1(sK0,sK1)),k3_subset_1(sK1,k6_subset_1(sK1,X0)))) = k4_subset_1(sK1,k2_tops_1(sK0,sK1),k3_subset_1(sK1,k6_subset_1(sK1,X0))) ),
% 39.50/5.52      inference(superposition,[status(thm)],[c_5759,c_17381]) ).
% 39.50/5.52  
% 39.50/5.52  cnf(c_18194,plain,
% 39.50/5.52      ( k4_subset_1(sK1,k2_tops_1(sK0,sK1),k3_subset_1(sK1,k6_subset_1(sK1,X0))) = k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),k3_subset_1(sK1,k6_subset_1(sK1,X0))))
% 39.50/5.52      | k2_pre_topc(sK0,sK1) = sK1 ),
% 39.50/5.52      inference(superposition,[status(thm)],[c_5759,c_17656]) ).
% 39.50/5.52  
% 39.50/5.52  cnf(c_18473,plain,
% 39.50/5.52      ( k2_pre_topc(sK0,sK1) = sK1
% 39.50/5.52      | k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),k3_subset_1(sK1,k6_subset_1(sK1,k1_tops_1(sK0,sK1))))) = k4_subset_1(sK1,k2_tops_1(sK0,sK1),k3_subset_1(sK1,k2_tops_1(sK0,sK1))) ),
% 39.50/5.52      inference(superposition,[status(thm)],[c_5759,c_18194]) ).
% 39.50/5.52  
% 39.50/5.52  cnf(c_18743,plain,
% 39.50/5.52      ( k4_subset_1(sK1,k2_tops_1(sK0,sK1),k3_subset_1(sK1,k2_tops_1(sK0,sK1))) = k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),k3_subset_1(sK1,k2_tops_1(sK0,sK1))))
% 39.50/5.52      | k2_pre_topc(sK0,sK1) = sK1 ),
% 39.50/5.52      inference(superposition,[status(thm)],[c_5759,c_18473]) ).
% 39.50/5.52  
% 39.50/5.52  cnf(c_18822,plain,
% 39.50/5.52      ( k2_pre_topc(sK0,sK1) = sK1
% 39.50/5.52      | k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),k3_subset_1(sK1,k2_tops_1(sK0,sK1)))) = sK1 ),
% 39.50/5.52      inference(superposition,[status(thm)],[c_6678,c_18743]) ).
% 39.50/5.52  
% 39.50/5.52  cnf(c_0,plain,
% 39.50/5.52      ( k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(X0,X1)) ),
% 39.50/5.52      inference(cnf_transformation,[],[f64]) ).
% 39.50/5.52  
% 39.50/5.52  cnf(c_20620,plain,
% 39.50/5.52      ( k2_pre_topc(sK0,sK1) = sK1
% 39.50/5.52      | k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),k3_subset_1(sK1,k2_tops_1(sK0,sK1)))) = k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),sK1)) ),
% 39.50/5.52      inference(superposition,[status(thm)],[c_18822,c_0]) ).
% 39.50/5.52  
% 39.50/5.52  cnf(c_11,plain,
% 39.50/5.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 39.50/5.52      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 39.50/5.52      | ~ l1_pre_topc(X1) ),
% 39.50/5.52      inference(cnf_transformation,[],[f54]) ).
% 39.50/5.52  
% 39.50/5.52  cnf(c_633,plain,
% 39.50/5.52      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 39.50/5.52      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 39.50/5.52      | l1_pre_topc(X1) != iProver_top ),
% 39.50/5.52      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 39.50/5.52  
% 39.50/5.52  cnf(c_5624,plain,
% 39.50/5.52      ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k3_tarski(k2_tarski(sK1,X0))
% 39.50/5.52      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 39.50/5.52      inference(superposition,[status(thm)],[c_627,c_638]) ).
% 39.50/5.52  
% 39.50/5.52  cnf(c_5765,plain,
% 39.50/5.52      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0)))
% 39.50/5.52      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 39.50/5.52      | l1_pre_topc(sK0) != iProver_top ),
% 39.50/5.52      inference(superposition,[status(thm)],[c_633,c_5624]) ).
% 39.50/5.52  
% 39.50/5.52  cnf(c_6212,plain,
% 39.50/5.52      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 39.50/5.52      | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0))) ),
% 39.50/5.52      inference(global_propositional_subsumption,
% 39.50/5.52                [status(thm)],
% 39.50/5.52                [c_5765,c_21]) ).
% 39.50/5.52  
% 39.50/5.52  cnf(c_6213,plain,
% 39.50/5.52      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0)))
% 39.50/5.52      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 39.50/5.52      inference(renaming,[status(thm)],[c_6212]) ).
% 39.50/5.52  
% 39.50/5.52  cnf(c_6223,plain,
% 39.50/5.52      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
% 39.50/5.52      inference(superposition,[status(thm)],[c_627,c_6213]) ).
% 39.50/5.52  
% 39.50/5.52  cnf(c_14,plain,
% 39.50/5.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 39.50/5.52      | ~ l1_pre_topc(X1)
% 39.50/5.52      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
% 39.50/5.52      inference(cnf_transformation,[],[f57]) ).
% 39.50/5.52  
% 39.50/5.52  cnf(c_630,plain,
% 39.50/5.52      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
% 39.50/5.52      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 39.50/5.52      | l1_pre_topc(X0) != iProver_top ),
% 39.50/5.52      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 39.50/5.52  
% 39.50/5.52  cnf(c_1141,plain,
% 39.50/5.52      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
% 39.50/5.52      | l1_pre_topc(sK0) != iProver_top ),
% 39.50/5.52      inference(superposition,[status(thm)],[c_627,c_630]) ).
% 39.50/5.52  
% 39.50/5.52  cnf(c_918,plain,
% 39.50/5.52      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 39.50/5.52      | ~ l1_pre_topc(sK0)
% 39.50/5.52      | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 39.50/5.52      inference(instantiation,[status(thm)],[c_14]) ).
% 39.50/5.52  
% 39.50/5.52  cnf(c_1524,plain,
% 39.50/5.52      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 39.50/5.52      inference(global_propositional_subsumption,
% 39.50/5.52                [status(thm)],
% 39.50/5.52                [c_1141,c_18,c_17,c_918]) ).
% 39.50/5.52  
% 39.50/5.52  cnf(c_6225,plain,
% 39.50/5.52      ( k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k2_pre_topc(sK0,sK1) ),
% 39.50/5.52      inference(light_normalisation,[status(thm)],[c_6223,c_1524]) ).
% 39.50/5.52  
% 39.50/5.52  cnf(c_1,plain,
% 39.50/5.52      ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
% 39.50/5.52      inference(cnf_transformation,[],[f42]) ).
% 39.50/5.52  
% 39.50/5.52  cnf(c_1341,plain,
% 39.50/5.52      ( k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X1,X0)))) = k3_tarski(k2_tarski(X0,X1)) ),
% 39.50/5.52      inference(superposition,[status(thm)],[c_1,c_0]) ).
% 39.50/5.52  
% 39.50/5.52  cnf(c_1510,plain,
% 39.50/5.52      ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X0)) ),
% 39.50/5.52      inference(superposition,[status(thm)],[c_0,c_1341]) ).
% 39.50/5.52  
% 39.50/5.52  cnf(c_2294,plain,
% 39.50/5.52      ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(k3_tarski(k2_tarski(X1,X0)),X1)) ),
% 39.50/5.52      inference(superposition,[status(thm)],[c_1,c_1510]) ).
% 39.50/5.52  
% 39.50/5.52  cnf(c_2329,plain,
% 39.50/5.52      ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X0)) = k3_tarski(k2_tarski(k3_tarski(k2_tarski(X1,X0)),X1)) ),
% 39.50/5.52      inference(superposition,[status(thm)],[c_2294,c_1510]) ).
% 39.50/5.52  
% 39.50/5.52  cnf(c_3054,plain,
% 39.50/5.52      ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X0)) = k3_tarski(k2_tarski(X1,k3_tarski(k2_tarski(X1,X0)))) ),
% 39.50/5.52      inference(superposition,[status(thm)],[c_1,c_2329]) ).
% 39.50/5.52  
% 39.50/5.52  cnf(c_3116,plain,
% 39.50/5.52      ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X0)) = k3_tarski(k2_tarski(X1,X0)) ),
% 39.50/5.52      inference(demodulation,[status(thm)],[c_3054,c_0]) ).
% 39.50/5.52  
% 39.50/5.52  cnf(c_3216,plain,
% 39.50/5.52      ( k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(X1,X0)) ),
% 39.50/5.52      inference(superposition,[status(thm)],[c_1,c_3116]) ).
% 39.50/5.52  
% 39.50/5.52  cnf(c_3434,plain,
% 39.50/5.52      ( k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X1,X0)))) = k3_tarski(k2_tarski(X1,X0)) ),
% 39.50/5.52      inference(superposition,[status(thm)],[c_1,c_3216]) ).
% 39.50/5.52  
% 39.50/5.52  cnf(c_6261,plain,
% 39.50/5.52      ( k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1))) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
% 39.50/5.52      inference(superposition,[status(thm)],[c_6225,c_3434]) ).
% 39.50/5.52  
% 39.50/5.52  cnf(c_6262,plain,
% 39.50/5.52      ( k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1))) = k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),sK1)) ),
% 39.50/5.52      inference(superposition,[status(thm)],[c_6225,c_1341]) ).
% 39.50/5.52  
% 39.50/5.52  cnf(c_6265,plain,
% 39.50/5.52      ( k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1))) = k2_pre_topc(sK0,sK1) ),
% 39.50/5.52      inference(light_normalisation,[status(thm)],[c_6261,c_6225,c_6262]) ).
% 39.50/5.52  
% 39.50/5.52  cnf(c_6267,plain,
% 39.50/5.52      ( k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),sK1)) = k2_pre_topc(sK0,sK1) ),
% 39.50/5.52      inference(demodulation,[status(thm)],[c_6265,c_6262]) ).
% 39.50/5.52  
% 39.50/5.52  cnf(c_20643,plain,
% 39.50/5.52      ( k2_pre_topc(sK0,sK1) = sK1
% 39.50/5.52      | k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),k3_subset_1(sK1,k2_tops_1(sK0,sK1)))) = k2_pre_topc(sK0,sK1) ),
% 39.50/5.52      inference(light_normalisation,[status(thm)],[c_20620,c_6267]) ).
% 39.50/5.52  
% 39.50/5.52  cnf(c_22704,plain,
% 39.50/5.52      ( k2_pre_topc(sK0,sK1) = sK1 ),
% 39.50/5.52      inference(superposition,[status(thm)],[c_20643,c_18822]) ).
% 39.50/5.52  
% 39.50/5.52  cnf(c_13,plain,
% 39.50/5.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 39.50/5.52      | ~ l1_pre_topc(X1)
% 39.50/5.52      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
% 39.50/5.52      inference(cnf_transformation,[],[f56]) ).
% 39.50/5.52  
% 39.50/5.52  cnf(c_631,plain,
% 39.50/5.52      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
% 39.50/5.52      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 39.50/5.52      | l1_pre_topc(X0) != iProver_top ),
% 39.50/5.52      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 39.50/5.52  
% 39.50/5.52  cnf(c_2129,plain,
% 39.50/5.52      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 39.50/5.52      | l1_pre_topc(sK0) != iProver_top ),
% 39.50/5.52      inference(superposition,[status(thm)],[c_627,c_631]) ).
% 39.50/5.52  
% 39.50/5.52  cnf(c_923,plain,
% 39.50/5.52      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 39.50/5.52      | ~ l1_pre_topc(sK0)
% 39.50/5.52      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 39.50/5.52      inference(instantiation,[status(thm)],[c_13]) ).
% 39.50/5.52  
% 39.50/5.52  cnf(c_2922,plain,
% 39.50/5.52      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 39.50/5.52      inference(global_propositional_subsumption,
% 39.50/5.52                [status(thm)],
% 39.50/5.52                [c_2129,c_18,c_17,c_923]) ).
% 39.50/5.52  
% 39.50/5.52  cnf(c_79940,plain,
% 39.50/5.52      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 39.50/5.52      inference(demodulation,[status(thm)],[c_22704,c_2922]) ).
% 39.50/5.52  
% 39.50/5.52  cnf(c_9,plain,
% 39.50/5.52      ( v4_pre_topc(X0,X1)
% 39.50/5.52      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 39.50/5.52      | ~ l1_pre_topc(X1)
% 39.50/5.52      | ~ v2_pre_topc(X1)
% 39.50/5.52      | k2_pre_topc(X1,X0) != X0 ),
% 39.50/5.52      inference(cnf_transformation,[],[f53]) ).
% 39.50/5.52  
% 39.50/5.52  cnf(c_913,plain,
% 39.50/5.52      ( v4_pre_topc(sK1,sK0)
% 39.50/5.52      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 39.50/5.52      | ~ l1_pre_topc(sK0)
% 39.50/5.52      | ~ v2_pre_topc(sK0)
% 39.50/5.52      | k2_pre_topc(sK0,sK1) != sK1 ),
% 39.50/5.52      inference(instantiation,[status(thm)],[c_9]) ).
% 39.50/5.52  
% 39.50/5.52  cnf(c_15,negated_conjecture,
% 39.50/5.52      ( ~ v4_pre_topc(sK1,sK0)
% 39.50/5.52      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
% 39.50/5.52      inference(cnf_transformation,[],[f62]) ).
% 39.50/5.52  
% 39.50/5.52  cnf(c_19,negated_conjecture,
% 39.50/5.52      ( v2_pre_topc(sK0) ),
% 39.50/5.52      inference(cnf_transformation,[],[f58]) ).
% 39.50/5.52  
% 39.50/5.52  cnf(contradiction,plain,
% 39.50/5.52      ( $false ),
% 39.50/5.52      inference(minisat,
% 39.50/5.52                [status(thm)],
% 39.50/5.52                [c_79940,c_22704,c_913,c_15,c_17,c_18,c_19]) ).
% 39.50/5.52  
% 39.50/5.52  
% 39.50/5.52  % SZS output end CNFRefutation for theBenchmark.p
% 39.50/5.52  
% 39.50/5.52  ------                               Statistics
% 39.50/5.52  
% 39.50/5.52  ------ Selected
% 39.50/5.52  
% 39.50/5.52  total_time:                             4.726
% 39.50/5.52  
%------------------------------------------------------------------------------
