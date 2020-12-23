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
% DateTime   : Thu Dec  3 12:14:36 EST 2020

% Result     : Theorem 11.72s
% Output     : CNFRefutation 11.72s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 327 expanded)
%              Number of clauses        :   75 (  93 expanded)
%              Number of leaves         :   20 (  82 expanded)
%              Depth                    :   20
%              Number of atoms          :  350 (1349 expanded)
%              Number of equality atoms :  183 ( 489 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1)
            | ~ v4_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1)
            | ~ v4_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f31,plain,(
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

fof(f30,plain,
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

fof(f32,plain,
    ( ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f29,f31,f30])).

fof(f51,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f11,axiom,(
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

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f49,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f50,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f32])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f53,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f33,f42])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f41,f53])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f57,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))) = X0 ),
    inference(definition_unfolding,[],[f37,f39,f42,f53])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f56,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1))))) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f36,f53,f39])).

fof(f2,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f54,plain,(
    ! [X0] : k3_tarski(k2_tarski(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f34,f39])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f55,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,k1_setfam_1(k2_tarski(X0,X1)))) = X0 ),
    inference(definition_unfolding,[],[f35,f39,f42])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f17])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k2_tarski(X1,X2)) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f40,f39])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f52,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) != X1
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f48,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_13,negated_conjecture,
    ( v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_101,plain,
    ( v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(prop_impl,[status(thm)],[c_13])).

cnf(c_8,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_15,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_245,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,X0) = X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_15])).

cnf(c_246,plain,
    ( ~ v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_245])).

cnf(c_275,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,X0) = X0
    | sK1 != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_101,c_246])).

cnf(c_276,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(unflattening,[status(thm)],[c_275])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_278,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_276,c_14])).

cnf(c_325,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(prop_impl,[status(thm)],[c_278])).

cnf(c_326,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(renaming,[status(thm)],[c_325])).

cnf(c_614,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2))) = k7_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_615,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X2,X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3310,plain,
    ( k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0))) = k7_subset_1(u1_struct_0(sK0),sK1,X0) ),
    inference(superposition,[status(thm)],[c_614,c_615])).

cnf(c_3,plain,
    ( k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))) = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_4,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_2,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1))))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2405,plain,
    ( k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))),k1_xboole_0)) = X0 ),
    inference(superposition,[status(thm)],[c_2,c_3])).

cnf(c_0,plain,
    ( k3_tarski(k2_tarski(X0,k1_xboole_0)) = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_6650,plain,
    ( k1_setfam_1(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) = X0 ),
    inference(superposition,[status(thm)],[c_2405,c_0])).

cnf(c_6999,plain,
    ( k1_setfam_1(k2_tarski(X0,k3_tarski(k2_tarski(X1,X0)))) = X0 ),
    inference(superposition,[status(thm)],[c_4,c_6650])).

cnf(c_7039,plain,
    ( k1_setfam_1(k2_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0)) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(superposition,[status(thm)],[c_3,c_6999])).

cnf(c_1,plain,
    ( k3_tarski(k2_tarski(X0,k1_setfam_1(k2_tarski(X0,X1)))) = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1134,plain,
    ( k3_tarski(k2_tarski(X0,k1_setfam_1(k2_tarski(X1,X0)))) = X0 ),
    inference(superposition,[status(thm)],[c_4,c_1])).

cnf(c_12928,plain,
    ( k3_tarski(k2_tarski(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))) = X0 ),
    inference(superposition,[status(thm)],[c_7039,c_1134])).

cnf(c_26438,plain,
    ( k3_tarski(k2_tarski(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0))) = sK1 ),
    inference(superposition,[status(thm)],[c_3310,c_12928])).

cnf(c_27207,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = sK1 ),
    inference(superposition,[status(thm)],[c_326,c_26438])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_233,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_15])).

cnf(c_234,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_233])).

cnf(c_611,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_234])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X2,X0) = k3_tarski(k2_tarski(X2,X0)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_616,plain,
    ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_16808,plain,
    ( k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X1)) = k3_tarski(k2_tarski(X0,k2_tops_1(sK0,X1)))
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_611,c_616])).

cnf(c_18778,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_614,c_16808])).

cnf(c_18799,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
    inference(superposition,[status(thm)],[c_614,c_18778])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_209,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_15])).

cnf(c_210,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_209])).

cnf(c_613,plain,
    ( k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_210])).

cnf(c_722,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_614,c_613])).

cnf(c_18806,plain,
    ( k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k2_pre_topc(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_18799,c_722])).

cnf(c_27224,plain,
    ( k2_pre_topc(sK0,sK1) = sK1 ),
    inference(demodulation,[status(thm)],[c_27207,c_18806])).

cnf(c_390,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | k7_subset_1(X0,X2,X4) = k7_subset_1(X1,X3,X5) ),
    theory(equality)).

cnf(c_382,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2560,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | X6 != k7_subset_1(X1,X3,X5)
    | k7_subset_1(X0,X2,X4) = X6 ),
    inference(resolution,[status(thm)],[c_390,c_382])).

cnf(c_381,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_897,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_382,c_381])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_221,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_15])).

cnf(c_222,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_221])).

cnf(c_3379,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) ),
    inference(resolution,[status(thm)],[c_897,c_222])).

cnf(c_14362,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | X1 != k1_tops_1(sK0,X0)
    | X2 != k2_pre_topc(sK0,X0)
    | X3 != u1_struct_0(sK0)
    | k7_subset_1(X3,X2,X1) = k2_tops_1(sK0,X0) ),
    inference(resolution,[status(thm)],[c_2560,c_3379])).

cnf(c_12,negated_conjecture,
    ( ~ v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_99,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
    inference(prop_impl,[status(thm)],[c_12])).

cnf(c_7,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | k2_pre_topc(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_16,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_184,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_16])).

cnf(c_185,plain,
    ( v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k2_pre_topc(sK0,X0) != X0 ),
    inference(unflattening,[status(thm)],[c_184])).

cnf(c_189,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(X0,sK0)
    | k2_pre_topc(sK0,X0) != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_185,c_15])).

cnf(c_190,plain,
    ( v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,X0) != X0 ),
    inference(renaming,[status(thm)],[c_189])).

cnf(c_286,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,X0) != X0
    | sK1 != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_99,c_190])).

cnf(c_287,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,sK1) != sK1 ),
    inference(unflattening,[status(thm)],[c_286])).

cnf(c_289,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,sK1) != sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_287,c_14])).

cnf(c_323,plain,
    ( k2_pre_topc(sK0,sK1) != sK1
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
    inference(prop_impl,[status(thm)],[c_289])).

cnf(c_324,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,sK1) != sK1 ),
    inference(renaming,[status(thm)],[c_323])).

cnf(c_22858,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,sK1) != k1_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,sK1) != sK1
    | u1_struct_0(sK0) != u1_struct_0(sK0)
    | sK1 != k2_pre_topc(sK0,sK1) ),
    inference(resolution,[status(thm)],[c_14362,c_324])).

cnf(c_22859,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,sK1) != sK1
    | sK1 != k2_pre_topc(sK0,sK1) ),
    inference(equality_resolution_simp,[status(thm)],[c_22858])).

cnf(c_832,plain,
    ( X0 != X1
    | sK1 != X1
    | sK1 = X0 ),
    inference(instantiation,[status(thm)],[c_382])).

cnf(c_1104,plain,
    ( X0 != sK1
    | sK1 = X0
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_832])).

cnf(c_3167,plain,
    ( k2_pre_topc(sK0,sK1) != sK1
    | sK1 = k2_pre_topc(sK0,sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1104])).

cnf(c_824,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_381])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_27224,c_22859,c_3167,c_824,c_14])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 12:03:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 11.72/1.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.72/1.99  
% 11.72/1.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.72/1.99  
% 11.72/1.99  ------  iProver source info
% 11.72/1.99  
% 11.72/1.99  git: date: 2020-06-30 10:37:57 +0100
% 11.72/1.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.72/1.99  git: non_committed_changes: false
% 11.72/1.99  git: last_make_outside_of_git: false
% 11.72/1.99  
% 11.72/1.99  ------ 
% 11.72/1.99  ------ Parsing...
% 11.72/1.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.72/1.99  
% 11.72/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 11.72/1.99  
% 11.72/1.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.72/1.99  
% 11.72/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.72/1.99  ------ Proving...
% 11.72/1.99  ------ Problem Properties 
% 11.72/1.99  
% 11.72/1.99  
% 11.72/1.99  clauses                                 13
% 11.72/1.99  conjectures                             1
% 11.72/1.99  EPR                                     0
% 11.72/1.99  Horn                                    12
% 11.72/1.99  unary                                   6
% 11.72/1.99  binary                                  6
% 11.72/1.99  lits                                    21
% 11.72/1.99  lits eq                                 13
% 11.72/1.99  fd_pure                                 0
% 11.72/1.99  fd_pseudo                               0
% 11.72/1.99  fd_cond                                 0
% 11.72/1.99  fd_pseudo_cond                          0
% 11.72/1.99  AC symbols                              0
% 11.72/1.99  
% 11.72/1.99  ------ Input Options Time Limit: Unbounded
% 11.72/1.99  
% 11.72/1.99  
% 11.72/1.99  ------ 
% 11.72/1.99  Current options:
% 11.72/1.99  ------ 
% 11.72/1.99  
% 11.72/1.99  
% 11.72/1.99  
% 11.72/1.99  
% 11.72/1.99  ------ Proving...
% 11.72/1.99  
% 11.72/1.99  
% 11.72/1.99  % SZS status Theorem for theBenchmark.p
% 11.72/1.99  
% 11.72/1.99  % SZS output start CNFRefutation for theBenchmark.p
% 11.72/1.99  
% 11.72/1.99  fof(f15,conjecture,(
% 11.72/1.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 11.72/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.72/1.99  
% 11.72/1.99  fof(f16,negated_conjecture,(
% 11.72/1.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 11.72/1.99    inference(negated_conjecture,[],[f15])).
% 11.72/1.99  
% 11.72/1.99  fof(f26,plain,(
% 11.72/1.99    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 11.72/1.99    inference(ennf_transformation,[],[f16])).
% 11.72/1.99  
% 11.72/1.99  fof(f27,plain,(
% 11.72/1.99    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 11.72/1.99    inference(flattening,[],[f26])).
% 11.72/1.99  
% 11.72/1.99  fof(f28,plain,(
% 11.72/1.99    ? [X0] : (? [X1] : (((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 11.72/1.99    inference(nnf_transformation,[],[f27])).
% 11.72/1.99  
% 11.72/1.99  fof(f29,plain,(
% 11.72/1.99    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 11.72/1.99    inference(flattening,[],[f28])).
% 11.72/1.99  
% 11.72/1.99  fof(f31,plain,(
% 11.72/1.99    ( ! [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) != k2_tops_1(X0,sK1) | ~v4_pre_topc(sK1,X0)) & (k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) = k2_tops_1(X0,sK1) | v4_pre_topc(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 11.72/1.99    introduced(choice_axiom,[])).
% 11.72/1.99  
% 11.72/1.99  fof(f30,plain,(
% 11.72/1.99    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) != k2_tops_1(sK0,X1) | ~v4_pre_topc(X1,sK0)) & (k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) = k2_tops_1(sK0,X1) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 11.72/1.99    introduced(choice_axiom,[])).
% 11.72/1.99  
% 11.72/1.99  fof(f32,plain,(
% 11.72/1.99    ((k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)) & (k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 11.72/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f29,f31,f30])).
% 11.72/1.99  
% 11.72/1.99  fof(f51,plain,(
% 11.72/1.99    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)),
% 11.72/1.99    inference(cnf_transformation,[],[f32])).
% 11.72/1.99  
% 11.72/1.99  fof(f11,axiom,(
% 11.72/1.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 11.72/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.72/1.99  
% 11.72/1.99  fof(f20,plain,(
% 11.72/1.99    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.72/1.99    inference(ennf_transformation,[],[f11])).
% 11.72/1.99  
% 11.72/1.99  fof(f21,plain,(
% 11.72/1.99    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.72/1.99    inference(flattening,[],[f20])).
% 11.72/1.99  
% 11.72/1.99  fof(f43,plain,(
% 11.72/1.99    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.72/1.99    inference(cnf_transformation,[],[f21])).
% 11.72/1.99  
% 11.72/1.99  fof(f49,plain,(
% 11.72/1.99    l1_pre_topc(sK0)),
% 11.72/1.99    inference(cnf_transformation,[],[f32])).
% 11.72/1.99  
% 11.72/1.99  fof(f50,plain,(
% 11.72/1.99    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 11.72/1.99    inference(cnf_transformation,[],[f32])).
% 11.72/1.99  
% 11.72/1.99  fof(f9,axiom,(
% 11.72/1.99    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 11.72/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.72/1.99  
% 11.72/1.99  fof(f19,plain,(
% 11.72/1.99    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.72/1.99    inference(ennf_transformation,[],[f9])).
% 11.72/1.99  
% 11.72/1.99  fof(f41,plain,(
% 11.72/1.99    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.72/1.99    inference(cnf_transformation,[],[f19])).
% 11.72/1.99  
% 11.72/1.99  fof(f1,axiom,(
% 11.72/1.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 11.72/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.72/1.99  
% 11.72/1.99  fof(f33,plain,(
% 11.72/1.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 11.72/1.99    inference(cnf_transformation,[],[f1])).
% 11.72/1.99  
% 11.72/1.99  fof(f10,axiom,(
% 11.72/1.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 11.72/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.72/1.99  
% 11.72/1.99  fof(f42,plain,(
% 11.72/1.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 11.72/1.99    inference(cnf_transformation,[],[f10])).
% 11.72/1.99  
% 11.72/1.99  fof(f53,plain,(
% 11.72/1.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 11.72/1.99    inference(definition_unfolding,[],[f33,f42])).
% 11.72/1.99  
% 11.72/1.99  fof(f59,plain,(
% 11.72/1.99    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.72/1.99    inference(definition_unfolding,[],[f41,f53])).
% 11.72/1.99  
% 11.72/1.99  fof(f5,axiom,(
% 11.72/1.99    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 11.72/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.72/1.99  
% 11.72/1.99  fof(f37,plain,(
% 11.72/1.99    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 11.72/1.99    inference(cnf_transformation,[],[f5])).
% 11.72/1.99  
% 11.72/1.99  fof(f7,axiom,(
% 11.72/1.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 11.72/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.72/1.99  
% 11.72/1.99  fof(f39,plain,(
% 11.72/1.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 11.72/1.99    inference(cnf_transformation,[],[f7])).
% 11.72/1.99  
% 11.72/1.99  fof(f57,plain,(
% 11.72/1.99    ( ! [X0,X1] : (k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))) = X0) )),
% 11.72/1.99    inference(definition_unfolding,[],[f37,f39,f42,f53])).
% 11.72/1.99  
% 11.72/1.99  fof(f6,axiom,(
% 11.72/1.99    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 11.72/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.72/1.99  
% 11.72/1.99  fof(f38,plain,(
% 11.72/1.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 11.72/1.99    inference(cnf_transformation,[],[f6])).
% 11.72/1.99  
% 11.72/1.99  fof(f4,axiom,(
% 11.72/1.99    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 11.72/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.72/1.99  
% 11.72/1.99  fof(f36,plain,(
% 11.72/1.99    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 11.72/1.99    inference(cnf_transformation,[],[f4])).
% 11.72/1.99  
% 11.72/1.99  fof(f56,plain,(
% 11.72/1.99    ( ! [X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1))))) = k1_xboole_0) )),
% 11.72/1.99    inference(definition_unfolding,[],[f36,f53,f39])).
% 11.72/1.99  
% 11.72/1.99  fof(f2,axiom,(
% 11.72/1.99    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 11.72/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.72/1.99  
% 11.72/1.99  fof(f34,plain,(
% 11.72/1.99    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 11.72/1.99    inference(cnf_transformation,[],[f2])).
% 11.72/1.99  
% 11.72/1.99  fof(f54,plain,(
% 11.72/1.99    ( ! [X0] : (k3_tarski(k2_tarski(X0,k1_xboole_0)) = X0) )),
% 11.72/1.99    inference(definition_unfolding,[],[f34,f39])).
% 11.72/1.99  
% 11.72/1.99  fof(f3,axiom,(
% 11.72/1.99    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 11.72/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.72/1.99  
% 11.72/1.99  fof(f35,plain,(
% 11.72/1.99    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 11.72/1.99    inference(cnf_transformation,[],[f3])).
% 11.72/1.99  
% 11.72/1.99  fof(f55,plain,(
% 11.72/1.99    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,k1_setfam_1(k2_tarski(X0,X1)))) = X0) )),
% 11.72/1.99    inference(definition_unfolding,[],[f35,f39,f42])).
% 11.72/1.99  
% 11.72/1.99  fof(f12,axiom,(
% 11.72/1.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 11.72/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.72/1.99  
% 11.72/1.99  fof(f22,plain,(
% 11.72/1.99    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 11.72/1.99    inference(ennf_transformation,[],[f12])).
% 11.72/1.99  
% 11.72/1.99  fof(f23,plain,(
% 11.72/1.99    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 11.72/1.99    inference(flattening,[],[f22])).
% 11.72/1.99  
% 11.72/1.99  fof(f45,plain,(
% 11.72/1.99    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.72/1.99    inference(cnf_transformation,[],[f23])).
% 11.72/1.99  
% 11.72/1.99  fof(f8,axiom,(
% 11.72/1.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 11.72/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.72/1.99  
% 11.72/1.99  fof(f17,plain,(
% 11.72/1.99    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 11.72/1.99    inference(ennf_transformation,[],[f8])).
% 11.72/1.99  
% 11.72/1.99  fof(f18,plain,(
% 11.72/1.99    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.72/1.99    inference(flattening,[],[f17])).
% 11.72/1.99  
% 11.72/1.99  fof(f40,plain,(
% 11.72/1.99    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.72/1.99    inference(cnf_transformation,[],[f18])).
% 11.72/1.99  
% 11.72/1.99  fof(f58,plain,(
% 11.72/1.99    ( ! [X2,X0,X1] : (k3_tarski(k2_tarski(X1,X2)) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.72/1.99    inference(definition_unfolding,[],[f40,f39])).
% 11.72/1.99  
% 11.72/1.99  fof(f14,axiom,(
% 11.72/1.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)))),
% 11.72/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.72/1.99  
% 11.72/1.99  fof(f25,plain,(
% 11.72/1.99    ! [X0] : (! [X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.72/1.99    inference(ennf_transformation,[],[f14])).
% 11.72/1.99  
% 11.72/1.99  fof(f47,plain,(
% 11.72/1.99    ( ! [X0,X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.72/1.99    inference(cnf_transformation,[],[f25])).
% 11.72/1.99  
% 11.72/1.99  fof(f13,axiom,(
% 11.72/1.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)))),
% 11.72/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.72/1.99  
% 11.72/1.99  fof(f24,plain,(
% 11.72/1.99    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.72/1.99    inference(ennf_transformation,[],[f13])).
% 11.72/1.99  
% 11.72/1.99  fof(f46,plain,(
% 11.72/1.99    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.72/1.99    inference(cnf_transformation,[],[f24])).
% 11.72/1.99  
% 11.72/1.99  fof(f52,plain,(
% 11.72/1.99    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)),
% 11.72/1.99    inference(cnf_transformation,[],[f32])).
% 11.72/1.99  
% 11.72/1.99  fof(f44,plain,(
% 11.72/1.99    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.72/1.99    inference(cnf_transformation,[],[f21])).
% 11.72/1.99  
% 11.72/1.99  fof(f48,plain,(
% 11.72/1.99    v2_pre_topc(sK0)),
% 11.72/1.99    inference(cnf_transformation,[],[f32])).
% 11.72/1.99  
% 11.72/1.99  cnf(c_13,negated_conjecture,
% 11.72/1.99      ( v4_pre_topc(sK1,sK0)
% 11.72/1.99      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 11.72/1.99      inference(cnf_transformation,[],[f51]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_101,plain,
% 11.72/1.99      ( v4_pre_topc(sK1,sK0)
% 11.72/1.99      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 11.72/1.99      inference(prop_impl,[status(thm)],[c_13]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_8,plain,
% 11.72/1.99      ( ~ v4_pre_topc(X0,X1)
% 11.72/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.72/1.99      | ~ l1_pre_topc(X1)
% 11.72/1.99      | k2_pre_topc(X1,X0) = X0 ),
% 11.72/1.99      inference(cnf_transformation,[],[f43]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_15,negated_conjecture,
% 11.72/1.99      ( l1_pre_topc(sK0) ),
% 11.72/1.99      inference(cnf_transformation,[],[f49]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_245,plain,
% 11.72/1.99      ( ~ v4_pre_topc(X0,X1)
% 11.72/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.72/1.99      | k2_pre_topc(X1,X0) = X0
% 11.72/1.99      | sK0 != X1 ),
% 11.72/1.99      inference(resolution_lifted,[status(thm)],[c_8,c_15]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_246,plain,
% 11.72/1.99      ( ~ v4_pre_topc(X0,sK0)
% 11.72/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.72/1.99      | k2_pre_topc(sK0,X0) = X0 ),
% 11.72/1.99      inference(unflattening,[status(thm)],[c_245]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_275,plain,
% 11.72/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.72/1.99      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 11.72/1.99      | k2_pre_topc(sK0,X0) = X0
% 11.72/1.99      | sK1 != X0
% 11.72/1.99      | sK0 != sK0 ),
% 11.72/1.99      inference(resolution_lifted,[status(thm)],[c_101,c_246]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_276,plain,
% 11.72/1.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.72/1.99      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 11.72/1.99      | k2_pre_topc(sK0,sK1) = sK1 ),
% 11.72/1.99      inference(unflattening,[status(thm)],[c_275]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_14,negated_conjecture,
% 11.72/1.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 11.72/1.99      inference(cnf_transformation,[],[f50]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_278,plain,
% 11.72/1.99      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 11.72/1.99      | k2_pre_topc(sK0,sK1) = sK1 ),
% 11.72/1.99      inference(global_propositional_subsumption,
% 11.72/1.99                [status(thm)],
% 11.72/1.99                [c_276,c_14]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_325,plain,
% 11.72/1.99      ( k2_pre_topc(sK0,sK1) = sK1
% 11.72/1.99      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 11.72/1.99      inference(prop_impl,[status(thm)],[c_278]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_326,plain,
% 11.72/1.99      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 11.72/1.99      | k2_pre_topc(sK0,sK1) = sK1 ),
% 11.72/1.99      inference(renaming,[status(thm)],[c_325]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_614,plain,
% 11.72/1.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 11.72/1.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_6,plain,
% 11.72/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.72/1.99      | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2))) = k7_subset_1(X1,X0,X2) ),
% 11.72/1.99      inference(cnf_transformation,[],[f59]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_615,plain,
% 11.72/1.99      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X2,X0,X1)
% 11.72/1.99      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
% 11.72/1.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_3310,plain,
% 11.72/1.99      ( k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0))) = k7_subset_1(u1_struct_0(sK0),sK1,X0) ),
% 11.72/1.99      inference(superposition,[status(thm)],[c_614,c_615]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_3,plain,
% 11.72/1.99      ( k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))) = X0 ),
% 11.72/1.99      inference(cnf_transformation,[],[f57]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_4,plain,
% 11.72/1.99      ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
% 11.72/1.99      inference(cnf_transformation,[],[f38]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_2,plain,
% 11.72/1.99      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1))))) = k1_xboole_0 ),
% 11.72/1.99      inference(cnf_transformation,[],[f56]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_2405,plain,
% 11.72/1.99      ( k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))),k1_xboole_0)) = X0 ),
% 11.72/1.99      inference(superposition,[status(thm)],[c_2,c_3]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_0,plain,
% 11.72/1.99      ( k3_tarski(k2_tarski(X0,k1_xboole_0)) = X0 ),
% 11.72/1.99      inference(cnf_transformation,[],[f54]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_6650,plain,
% 11.72/1.99      ( k1_setfam_1(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) = X0 ),
% 11.72/1.99      inference(superposition,[status(thm)],[c_2405,c_0]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_6999,plain,
% 11.72/1.99      ( k1_setfam_1(k2_tarski(X0,k3_tarski(k2_tarski(X1,X0)))) = X0 ),
% 11.72/1.99      inference(superposition,[status(thm)],[c_4,c_6650]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_7039,plain,
% 11.72/1.99      ( k1_setfam_1(k2_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0)) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
% 11.72/1.99      inference(superposition,[status(thm)],[c_3,c_6999]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_1,plain,
% 11.72/1.99      ( k3_tarski(k2_tarski(X0,k1_setfam_1(k2_tarski(X0,X1)))) = X0 ),
% 11.72/1.99      inference(cnf_transformation,[],[f55]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_1134,plain,
% 11.72/1.99      ( k3_tarski(k2_tarski(X0,k1_setfam_1(k2_tarski(X1,X0)))) = X0 ),
% 11.72/1.99      inference(superposition,[status(thm)],[c_4,c_1]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_12928,plain,
% 11.72/1.99      ( k3_tarski(k2_tarski(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))) = X0 ),
% 11.72/1.99      inference(superposition,[status(thm)],[c_7039,c_1134]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_26438,plain,
% 11.72/1.99      ( k3_tarski(k2_tarski(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0))) = sK1 ),
% 11.72/1.99      inference(superposition,[status(thm)],[c_3310,c_12928]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_27207,plain,
% 11.72/1.99      ( k2_pre_topc(sK0,sK1) = sK1
% 11.72/1.99      | k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = sK1 ),
% 11.72/1.99      inference(superposition,[status(thm)],[c_326,c_26438]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_9,plain,
% 11.72/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.72/1.99      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 11.72/1.99      | ~ l1_pre_topc(X1) ),
% 11.72/1.99      inference(cnf_transformation,[],[f45]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_233,plain,
% 11.72/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.72/1.99      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 11.72/1.99      | sK0 != X1 ),
% 11.72/1.99      inference(resolution_lifted,[status(thm)],[c_9,c_15]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_234,plain,
% 11.72/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.72/1.99      | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 11.72/1.99      inference(unflattening,[status(thm)],[c_233]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_611,plain,
% 11.72/1.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.72/1.99      | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 11.72/1.99      inference(predicate_to_equality,[status(thm)],[c_234]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_5,plain,
% 11.72/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.72/1.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 11.72/1.99      | k4_subset_1(X1,X2,X0) = k3_tarski(k2_tarski(X2,X0)) ),
% 11.72/1.99      inference(cnf_transformation,[],[f58]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_616,plain,
% 11.72/1.99      ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
% 11.72/1.99      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
% 11.72/1.99      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 11.72/1.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_16808,plain,
% 11.72/1.99      ( k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X1)) = k3_tarski(k2_tarski(X0,k2_tops_1(sK0,X1)))
% 11.72/1.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.72/1.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 11.72/1.99      inference(superposition,[status(thm)],[c_611,c_616]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_18778,plain,
% 11.72/1.99      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0)))
% 11.72/1.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 11.72/1.99      inference(superposition,[status(thm)],[c_614,c_16808]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_18799,plain,
% 11.72/1.99      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
% 11.72/1.99      inference(superposition,[status(thm)],[c_614,c_18778]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_11,plain,
% 11.72/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.72/1.99      | ~ l1_pre_topc(X1)
% 11.72/1.99      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
% 11.72/1.99      inference(cnf_transformation,[],[f47]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_209,plain,
% 11.72/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.72/1.99      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0)
% 11.72/1.99      | sK0 != X1 ),
% 11.72/1.99      inference(resolution_lifted,[status(thm)],[c_11,c_15]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_210,plain,
% 11.72/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.72/1.99      | k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0) ),
% 11.72/1.99      inference(unflattening,[status(thm)],[c_209]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_613,plain,
% 11.72/1.99      ( k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0)
% 11.72/1.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 11.72/1.99      inference(predicate_to_equality,[status(thm)],[c_210]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_722,plain,
% 11.72/1.99      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 11.72/1.99      inference(superposition,[status(thm)],[c_614,c_613]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_18806,plain,
% 11.72/1.99      ( k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k2_pre_topc(sK0,sK1) ),
% 11.72/1.99      inference(light_normalisation,[status(thm)],[c_18799,c_722]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_27224,plain,
% 11.72/1.99      ( k2_pre_topc(sK0,sK1) = sK1 ),
% 11.72/1.99      inference(demodulation,[status(thm)],[c_27207,c_18806]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_390,plain,
% 11.72/1.99      ( X0 != X1
% 11.72/1.99      | X2 != X3
% 11.72/1.99      | X4 != X5
% 11.72/1.99      | k7_subset_1(X0,X2,X4) = k7_subset_1(X1,X3,X5) ),
% 11.72/1.99      theory(equality) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_382,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_2560,plain,
% 11.72/1.99      ( X0 != X1
% 11.72/1.99      | X2 != X3
% 11.72/1.99      | X4 != X5
% 11.72/1.99      | X6 != k7_subset_1(X1,X3,X5)
% 11.72/1.99      | k7_subset_1(X0,X2,X4) = X6 ),
% 11.72/1.99      inference(resolution,[status(thm)],[c_390,c_382]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_381,plain,( X0 = X0 ),theory(equality) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_897,plain,
% 11.72/1.99      ( X0 != X1 | X1 = X0 ),
% 11.72/1.99      inference(resolution,[status(thm)],[c_382,c_381]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_10,plain,
% 11.72/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.72/1.99      | ~ l1_pre_topc(X1)
% 11.72/1.99      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
% 11.72/1.99      inference(cnf_transformation,[],[f46]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_221,plain,
% 11.72/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.72/1.99      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0)
% 11.72/1.99      | sK0 != X1 ),
% 11.72/1.99      inference(resolution_lifted,[status(thm)],[c_10,c_15]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_222,plain,
% 11.72/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.72/1.99      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
% 11.72/1.99      inference(unflattening,[status(thm)],[c_221]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_3379,plain,
% 11.72/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.72/1.99      | k2_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) ),
% 11.72/1.99      inference(resolution,[status(thm)],[c_897,c_222]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_14362,plain,
% 11.72/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.72/1.99      | X1 != k1_tops_1(sK0,X0)
% 11.72/1.99      | X2 != k2_pre_topc(sK0,X0)
% 11.72/1.99      | X3 != u1_struct_0(sK0)
% 11.72/1.99      | k7_subset_1(X3,X2,X1) = k2_tops_1(sK0,X0) ),
% 11.72/1.99      inference(resolution,[status(thm)],[c_2560,c_3379]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_12,negated_conjecture,
% 11.72/1.99      ( ~ v4_pre_topc(sK1,sK0)
% 11.72/1.99      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
% 11.72/1.99      inference(cnf_transformation,[],[f52]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_99,plain,
% 11.72/1.99      ( ~ v4_pre_topc(sK1,sK0)
% 11.72/1.99      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
% 11.72/1.99      inference(prop_impl,[status(thm)],[c_12]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_7,plain,
% 11.72/1.99      ( v4_pre_topc(X0,X1)
% 11.72/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.72/1.99      | ~ l1_pre_topc(X1)
% 11.72/1.99      | ~ v2_pre_topc(X1)
% 11.72/1.99      | k2_pre_topc(X1,X0) != X0 ),
% 11.72/1.99      inference(cnf_transformation,[],[f44]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_16,negated_conjecture,
% 11.72/1.99      ( v2_pre_topc(sK0) ),
% 11.72/1.99      inference(cnf_transformation,[],[f48]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_184,plain,
% 11.72/1.99      ( v4_pre_topc(X0,X1)
% 11.72/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.72/1.99      | ~ l1_pre_topc(X1)
% 11.72/1.99      | k2_pre_topc(X1,X0) != X0
% 11.72/1.99      | sK0 != X1 ),
% 11.72/1.99      inference(resolution_lifted,[status(thm)],[c_7,c_16]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_185,plain,
% 11.72/1.99      ( v4_pre_topc(X0,sK0)
% 11.72/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.72/1.99      | ~ l1_pre_topc(sK0)
% 11.72/1.99      | k2_pre_topc(sK0,X0) != X0 ),
% 11.72/1.99      inference(unflattening,[status(thm)],[c_184]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_189,plain,
% 11.72/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.72/1.99      | v4_pre_topc(X0,sK0)
% 11.72/1.99      | k2_pre_topc(sK0,X0) != X0 ),
% 11.72/1.99      inference(global_propositional_subsumption,
% 11.72/1.99                [status(thm)],
% 11.72/1.99                [c_185,c_15]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_190,plain,
% 11.72/1.99      ( v4_pre_topc(X0,sK0)
% 11.72/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.72/1.99      | k2_pre_topc(sK0,X0) != X0 ),
% 11.72/1.99      inference(renaming,[status(thm)],[c_189]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_286,plain,
% 11.72/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.72/1.99      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
% 11.72/1.99      | k2_pre_topc(sK0,X0) != X0
% 11.72/1.99      | sK1 != X0
% 11.72/1.99      | sK0 != sK0 ),
% 11.72/1.99      inference(resolution_lifted,[status(thm)],[c_99,c_190]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_287,plain,
% 11.72/1.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.72/1.99      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
% 11.72/1.99      | k2_pre_topc(sK0,sK1) != sK1 ),
% 11.72/1.99      inference(unflattening,[status(thm)],[c_286]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_289,plain,
% 11.72/1.99      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
% 11.72/1.99      | k2_pre_topc(sK0,sK1) != sK1 ),
% 11.72/1.99      inference(global_propositional_subsumption,
% 11.72/1.99                [status(thm)],
% 11.72/1.99                [c_287,c_14]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_323,plain,
% 11.72/1.99      ( k2_pre_topc(sK0,sK1) != sK1
% 11.72/1.99      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
% 11.72/1.99      inference(prop_impl,[status(thm)],[c_289]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_324,plain,
% 11.72/1.99      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
% 11.72/1.99      | k2_pre_topc(sK0,sK1) != sK1 ),
% 11.72/1.99      inference(renaming,[status(thm)],[c_323]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_22858,plain,
% 11.72/1.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.72/1.99      | k1_tops_1(sK0,sK1) != k1_tops_1(sK0,sK1)
% 11.72/1.99      | k2_pre_topc(sK0,sK1) != sK1
% 11.72/1.99      | u1_struct_0(sK0) != u1_struct_0(sK0)
% 11.72/1.99      | sK1 != k2_pre_topc(sK0,sK1) ),
% 11.72/1.99      inference(resolution,[status(thm)],[c_14362,c_324]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_22859,plain,
% 11.72/1.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.72/1.99      | k2_pre_topc(sK0,sK1) != sK1
% 11.72/1.99      | sK1 != k2_pre_topc(sK0,sK1) ),
% 11.72/1.99      inference(equality_resolution_simp,[status(thm)],[c_22858]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_832,plain,
% 11.72/1.99      ( X0 != X1 | sK1 != X1 | sK1 = X0 ),
% 11.72/1.99      inference(instantiation,[status(thm)],[c_382]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_1104,plain,
% 11.72/1.99      ( X0 != sK1 | sK1 = X0 | sK1 != sK1 ),
% 11.72/1.99      inference(instantiation,[status(thm)],[c_832]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_3167,plain,
% 11.72/1.99      ( k2_pre_topc(sK0,sK1) != sK1
% 11.72/1.99      | sK1 = k2_pre_topc(sK0,sK1)
% 11.72/1.99      | sK1 != sK1 ),
% 11.72/1.99      inference(instantiation,[status(thm)],[c_1104]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(c_824,plain,
% 11.72/1.99      ( sK1 = sK1 ),
% 11.72/1.99      inference(instantiation,[status(thm)],[c_381]) ).
% 11.72/1.99  
% 11.72/1.99  cnf(contradiction,plain,
% 11.72/1.99      ( $false ),
% 11.72/1.99      inference(minisat,[status(thm)],[c_27224,c_22859,c_3167,c_824,c_14]) ).
% 11.72/1.99  
% 11.72/1.99  
% 11.72/1.99  % SZS output end CNFRefutation for theBenchmark.p
% 11.72/1.99  
% 11.72/1.99  ------                               Statistics
% 11.72/1.99  
% 11.72/1.99  ------ Selected
% 11.72/1.99  
% 11.72/1.99  total_time:                             1.03
% 11.72/1.99  
%------------------------------------------------------------------------------
