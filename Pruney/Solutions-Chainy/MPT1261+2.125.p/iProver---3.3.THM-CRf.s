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
% DateTime   : Thu Dec  3 12:14:42 EST 2020

% Result     : Theorem 27.34s
% Output     : CNFRefutation 27.34s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 323 expanded)
%              Number of clauses        :   73 (  91 expanded)
%              Number of leaves         :   19 (  82 expanded)
%              Depth                    :   20
%              Number of atoms          :  346 (1345 expanded)
%              Number of equality atoms :  179 ( 485 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1)
            | ~ v4_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f26])).

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
    inference(flattening,[],[f27])).

fof(f30,plain,(
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

fof(f29,plain,
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

fof(f31,plain,
    ( ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f28,f30,f29])).

fof(f48,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f31])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f47,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f16])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k2_tarski(X1,X2)) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f38,f37])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f49,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f10,axiom,(
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

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

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
    inference(flattening,[],[f19])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f51,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f33,f40])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f39,f51])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f53,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,k1_setfam_1(k2_tarski(X0,X1)))) = X0 ),
    inference(definition_unfolding,[],[f34,f37,f40])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f55,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(k5_xboole_0(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))) ),
    inference(definition_unfolding,[],[f36,f37,f37,f40])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f54,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) ),
    inference(definition_unfolding,[],[f35,f37,f37,f37])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f52,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(definition_unfolding,[],[f32,f37,f37])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f50,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) != X1
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f46,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_609,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_14,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_230,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_14])).

cnf(c_231,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_230])).

cnf(c_606,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_231])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X2,X0) = k3_tarski(k2_tarski(X2,X0)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_611,plain,
    ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_57953,plain,
    ( k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X1)) = k3_tarski(k2_tarski(X0,k2_tops_1(sK0,X1)))
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_606,c_611])).

cnf(c_62776,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_609,c_57953])).

cnf(c_62797,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
    inference(superposition,[status(thm)],[c_609,c_62776])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_206,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_14])).

cnf(c_207,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_206])).

cnf(c_608,plain,
    ( k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_207])).

cnf(c_720,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_609,c_608])).

cnf(c_62804,plain,
    ( k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k2_pre_topc(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_62797,c_720])).

cnf(c_12,negated_conjecture,
    ( v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_99,plain,
    ( v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(prop_impl,[status(thm)],[c_12])).

cnf(c_7,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_242,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,X0) = X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_14])).

cnf(c_243,plain,
    ( ~ v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_242])).

cnf(c_272,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,X0) = X0
    | sK1 != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_99,c_243])).

cnf(c_273,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(unflattening,[status(thm)],[c_272])).

cnf(c_275,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_273,c_13])).

cnf(c_322,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(prop_impl,[status(thm)],[c_275])).

cnf(c_323,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(renaming,[status(thm)],[c_322])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2))) = k7_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_610,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X2,X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3405,plain,
    ( k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0))) = k7_subset_1(u1_struct_0(sK0),sK1,X0) ),
    inference(superposition,[status(thm)],[c_609,c_610])).

cnf(c_1,plain,
    ( k3_tarski(k2_tarski(X0,k1_setfam_1(k2_tarski(X0,X1)))) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_3,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2,plain,
    ( k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1207,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(X0,X1),k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(k5_xboole_0(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))) ),
    inference(superposition,[status(thm)],[c_3,c_2])).

cnf(c_1208,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(X0,X1),k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_1207,c_3])).

cnf(c_2433,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0)) = k3_tarski(k2_tarski(X0,k1_setfam_1(k2_tarski(X0,X1)))) ),
    inference(superposition,[status(thm)],[c_1,c_1208])).

cnf(c_2460,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_2433,c_1])).

cnf(c_0,plain,
    ( k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2476,plain,
    ( k3_tarski(k2_tarski(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))) = X0 ),
    inference(superposition,[status(thm)],[c_2460,c_0])).

cnf(c_4052,plain,
    ( k3_tarski(k2_tarski(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0))) = sK1 ),
    inference(superposition,[status(thm)],[c_3405,c_2476])).

cnf(c_4479,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = sK1 ),
    inference(superposition,[status(thm)],[c_323,c_4052])).

cnf(c_63085,plain,
    ( k2_pre_topc(sK0,sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_62804,c_4479])).

cnf(c_386,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | k7_subset_1(X0,X2,X4) = k7_subset_1(X1,X3,X5) ),
    theory(equality)).

cnf(c_378,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2494,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | X6 != k7_subset_1(X1,X3,X5)
    | k7_subset_1(X0,X2,X4) = X6 ),
    inference(resolution,[status(thm)],[c_386,c_378])).

cnf(c_377,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_870,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_378,c_377])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_218,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_14])).

cnf(c_219,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_218])).

cnf(c_3476,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) ),
    inference(resolution,[status(thm)],[c_870,c_219])).

cnf(c_18128,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | X1 != k1_tops_1(sK0,X0)
    | X2 != k2_pre_topc(sK0,X0)
    | X3 != u1_struct_0(sK0)
    | k7_subset_1(X3,X2,X1) = k2_tops_1(sK0,X0) ),
    inference(resolution,[status(thm)],[c_2494,c_3476])).

cnf(c_11,negated_conjecture,
    ( ~ v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_97,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
    inference(prop_impl,[status(thm)],[c_11])).

cnf(c_6,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | k2_pre_topc(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_15,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_181,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_15])).

cnf(c_182,plain,
    ( v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k2_pre_topc(sK0,X0) != X0 ),
    inference(unflattening,[status(thm)],[c_181])).

cnf(c_186,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(X0,sK0)
    | k2_pre_topc(sK0,X0) != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_182,c_14])).

cnf(c_187,plain,
    ( v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,X0) != X0 ),
    inference(renaming,[status(thm)],[c_186])).

cnf(c_283,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,X0) != X0
    | sK1 != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_97,c_187])).

cnf(c_284,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,sK1) != sK1 ),
    inference(unflattening,[status(thm)],[c_283])).

cnf(c_286,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,sK1) != sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_284,c_13])).

cnf(c_320,plain,
    ( k2_pre_topc(sK0,sK1) != sK1
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
    inference(prop_impl,[status(thm)],[c_286])).

cnf(c_321,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,sK1) != sK1 ),
    inference(renaming,[status(thm)],[c_320])).

cnf(c_20641,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,sK1) != k1_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,sK1) != sK1
    | u1_struct_0(sK0) != u1_struct_0(sK0)
    | sK1 != k2_pre_topc(sK0,sK1) ),
    inference(resolution,[status(thm)],[c_18128,c_321])).

cnf(c_20642,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,sK1) != sK1
    | sK1 != k2_pre_topc(sK0,sK1) ),
    inference(equality_resolution_simp,[status(thm)],[c_20641])).

cnf(c_812,plain,
    ( X0 != X1
    | sK1 != X1
    | sK1 = X0 ),
    inference(instantiation,[status(thm)],[c_378])).

cnf(c_1083,plain,
    ( X0 != sK1
    | sK1 = X0
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_812])).

cnf(c_1959,plain,
    ( k2_pre_topc(sK0,sK1) != sK1
    | sK1 = k2_pre_topc(sK0,sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1083])).

cnf(c_804,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_377])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_63085,c_20642,c_1959,c_804,c_13])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:27:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 27.34/4.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 27.34/4.00  
% 27.34/4.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 27.34/4.00  
% 27.34/4.00  ------  iProver source info
% 27.34/4.00  
% 27.34/4.00  git: date: 2020-06-30 10:37:57 +0100
% 27.34/4.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 27.34/4.00  git: non_committed_changes: false
% 27.34/4.00  git: last_make_outside_of_git: false
% 27.34/4.00  
% 27.34/4.00  ------ 
% 27.34/4.00  ------ Parsing...
% 27.34/4.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 27.34/4.00  
% 27.34/4.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 27.34/4.00  
% 27.34/4.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 27.34/4.00  
% 27.34/4.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.34/4.00  ------ Proving...
% 27.34/4.00  ------ Problem Properties 
% 27.34/4.00  
% 27.34/4.00  
% 27.34/4.00  clauses                                 12
% 27.34/4.00  conjectures                             1
% 27.34/4.00  EPR                                     0
% 27.34/4.00  Horn                                    11
% 27.34/4.00  unary                                   5
% 27.34/4.00  binary                                  6
% 27.34/4.00  lits                                    20
% 27.34/4.00  lits eq                                 12
% 27.34/4.00  fd_pure                                 0
% 27.34/4.00  fd_pseudo                               0
% 27.34/4.00  fd_cond                                 0
% 27.34/4.00  fd_pseudo_cond                          0
% 27.34/4.00  AC symbols                              0
% 27.34/4.00  
% 27.34/4.00  ------ Input Options Time Limit: Unbounded
% 27.34/4.00  
% 27.34/4.00  
% 27.34/4.00  ------ 
% 27.34/4.00  Current options:
% 27.34/4.00  ------ 
% 27.34/4.00  
% 27.34/4.00  
% 27.34/4.00  
% 27.34/4.00  
% 27.34/4.00  ------ Proving...
% 27.34/4.00  
% 27.34/4.00  
% 27.34/4.00  % SZS status Theorem for theBenchmark.p
% 27.34/4.00  
% 27.34/4.00  % SZS output start CNFRefutation for theBenchmark.p
% 27.34/4.00  
% 27.34/4.00  fof(f14,conjecture,(
% 27.34/4.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 27.34/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.34/4.00  
% 27.34/4.00  fof(f15,negated_conjecture,(
% 27.34/4.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 27.34/4.00    inference(negated_conjecture,[],[f14])).
% 27.34/4.00  
% 27.34/4.00  fof(f25,plain,(
% 27.34/4.00    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 27.34/4.00    inference(ennf_transformation,[],[f15])).
% 27.34/4.00  
% 27.34/4.00  fof(f26,plain,(
% 27.34/4.00    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 27.34/4.00    inference(flattening,[],[f25])).
% 27.34/4.00  
% 27.34/4.00  fof(f27,plain,(
% 27.34/4.00    ? [X0] : (? [X1] : (((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 27.34/4.00    inference(nnf_transformation,[],[f26])).
% 27.34/4.00  
% 27.34/4.00  fof(f28,plain,(
% 27.34/4.00    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 27.34/4.00    inference(flattening,[],[f27])).
% 27.34/4.00  
% 27.34/4.00  fof(f30,plain,(
% 27.34/4.00    ( ! [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) != k2_tops_1(X0,sK1) | ~v4_pre_topc(sK1,X0)) & (k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) = k2_tops_1(X0,sK1) | v4_pre_topc(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 27.34/4.00    introduced(choice_axiom,[])).
% 27.34/4.00  
% 27.34/4.00  fof(f29,plain,(
% 27.34/4.00    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) != k2_tops_1(sK0,X1) | ~v4_pre_topc(X1,sK0)) & (k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) = k2_tops_1(sK0,X1) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 27.34/4.00    introduced(choice_axiom,[])).
% 27.34/4.00  
% 27.34/4.00  fof(f31,plain,(
% 27.34/4.00    ((k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)) & (k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 27.34/4.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f28,f30,f29])).
% 27.34/4.00  
% 27.34/4.00  fof(f48,plain,(
% 27.34/4.00    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 27.34/4.00    inference(cnf_transformation,[],[f31])).
% 27.34/4.00  
% 27.34/4.00  fof(f11,axiom,(
% 27.34/4.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 27.34/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.34/4.00  
% 27.34/4.00  fof(f21,plain,(
% 27.34/4.00    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 27.34/4.00    inference(ennf_transformation,[],[f11])).
% 27.34/4.00  
% 27.34/4.00  fof(f22,plain,(
% 27.34/4.00    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 27.34/4.00    inference(flattening,[],[f21])).
% 27.34/4.00  
% 27.34/4.00  fof(f43,plain,(
% 27.34/4.00    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 27.34/4.00    inference(cnf_transformation,[],[f22])).
% 27.34/4.00  
% 27.34/4.00  fof(f47,plain,(
% 27.34/4.00    l1_pre_topc(sK0)),
% 27.34/4.00    inference(cnf_transformation,[],[f31])).
% 27.34/4.00  
% 27.34/4.00  fof(f7,axiom,(
% 27.34/4.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 27.34/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.34/4.00  
% 27.34/4.00  fof(f16,plain,(
% 27.34/4.00    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 27.34/4.00    inference(ennf_transformation,[],[f7])).
% 27.34/4.00  
% 27.34/4.00  fof(f17,plain,(
% 27.34/4.00    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 27.34/4.00    inference(flattening,[],[f16])).
% 27.34/4.00  
% 27.34/4.00  fof(f38,plain,(
% 27.34/4.00    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 27.34/4.00    inference(cnf_transformation,[],[f17])).
% 27.34/4.00  
% 27.34/4.00  fof(f6,axiom,(
% 27.34/4.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 27.34/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.34/4.00  
% 27.34/4.00  fof(f37,plain,(
% 27.34/4.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 27.34/4.00    inference(cnf_transformation,[],[f6])).
% 27.34/4.00  
% 27.34/4.00  fof(f56,plain,(
% 27.34/4.00    ( ! [X2,X0,X1] : (k3_tarski(k2_tarski(X1,X2)) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 27.34/4.00    inference(definition_unfolding,[],[f38,f37])).
% 27.34/4.00  
% 27.34/4.00  fof(f13,axiom,(
% 27.34/4.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)))),
% 27.34/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.34/4.00  
% 27.34/4.00  fof(f24,plain,(
% 27.34/4.00    ! [X0] : (! [X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 27.34/4.00    inference(ennf_transformation,[],[f13])).
% 27.34/4.00  
% 27.34/4.00  fof(f45,plain,(
% 27.34/4.00    ( ! [X0,X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 27.34/4.00    inference(cnf_transformation,[],[f24])).
% 27.34/4.00  
% 27.34/4.00  fof(f49,plain,(
% 27.34/4.00    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)),
% 27.34/4.00    inference(cnf_transformation,[],[f31])).
% 27.34/4.00  
% 27.34/4.00  fof(f10,axiom,(
% 27.34/4.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 27.34/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.34/4.00  
% 27.34/4.00  fof(f19,plain,(
% 27.34/4.00    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 27.34/4.00    inference(ennf_transformation,[],[f10])).
% 27.34/4.00  
% 27.34/4.00  fof(f20,plain,(
% 27.34/4.00    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 27.34/4.00    inference(flattening,[],[f19])).
% 27.34/4.00  
% 27.34/4.00  fof(f41,plain,(
% 27.34/4.00    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 27.34/4.00    inference(cnf_transformation,[],[f20])).
% 27.34/4.00  
% 27.34/4.00  fof(f8,axiom,(
% 27.34/4.00    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 27.34/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.34/4.00  
% 27.34/4.00  fof(f18,plain,(
% 27.34/4.00    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 27.34/4.00    inference(ennf_transformation,[],[f8])).
% 27.34/4.00  
% 27.34/4.00  fof(f39,plain,(
% 27.34/4.00    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 27.34/4.00    inference(cnf_transformation,[],[f18])).
% 27.34/4.00  
% 27.34/4.00  fof(f2,axiom,(
% 27.34/4.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 27.34/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.34/4.00  
% 27.34/4.00  fof(f33,plain,(
% 27.34/4.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 27.34/4.00    inference(cnf_transformation,[],[f2])).
% 27.34/4.00  
% 27.34/4.00  fof(f9,axiom,(
% 27.34/4.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 27.34/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.34/4.00  
% 27.34/4.00  fof(f40,plain,(
% 27.34/4.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 27.34/4.00    inference(cnf_transformation,[],[f9])).
% 27.34/4.00  
% 27.34/4.00  fof(f51,plain,(
% 27.34/4.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 27.34/4.00    inference(definition_unfolding,[],[f33,f40])).
% 27.34/4.00  
% 27.34/4.00  fof(f57,plain,(
% 27.34/4.00    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 27.34/4.00    inference(definition_unfolding,[],[f39,f51])).
% 27.34/4.00  
% 27.34/4.00  fof(f3,axiom,(
% 27.34/4.00    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 27.34/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.34/4.00  
% 27.34/4.00  fof(f34,plain,(
% 27.34/4.00    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 27.34/4.00    inference(cnf_transformation,[],[f3])).
% 27.34/4.00  
% 27.34/4.00  fof(f53,plain,(
% 27.34/4.00    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,k1_setfam_1(k2_tarski(X0,X1)))) = X0) )),
% 27.34/4.00    inference(definition_unfolding,[],[f34,f37,f40])).
% 27.34/4.00  
% 27.34/4.00  fof(f5,axiom,(
% 27.34/4.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 27.34/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.34/4.00  
% 27.34/4.00  fof(f36,plain,(
% 27.34/4.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 27.34/4.00    inference(cnf_transformation,[],[f5])).
% 27.34/4.00  
% 27.34/4.00  fof(f55,plain,(
% 27.34/4.00    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(k5_xboole_0(X0,X1),k1_setfam_1(k2_tarski(X0,X1))))) )),
% 27.34/4.00    inference(definition_unfolding,[],[f36,f37,f37,f40])).
% 27.34/4.00  
% 27.34/4.00  fof(f4,axiom,(
% 27.34/4.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))),
% 27.34/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.34/4.00  
% 27.34/4.00  fof(f35,plain,(
% 27.34/4.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 27.34/4.00    inference(cnf_transformation,[],[f4])).
% 27.34/4.00  
% 27.34/4.00  fof(f54,plain,(
% 27.34/4.00    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1))))) )),
% 27.34/4.00    inference(definition_unfolding,[],[f35,f37,f37,f37])).
% 27.34/4.00  
% 27.34/4.00  fof(f1,axiom,(
% 27.34/4.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 27.34/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.34/4.00  
% 27.34/4.00  fof(f32,plain,(
% 27.34/4.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 27.34/4.00    inference(cnf_transformation,[],[f1])).
% 27.34/4.00  
% 27.34/4.00  fof(f52,plain,(
% 27.34/4.00    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X1,X0))) )),
% 27.34/4.00    inference(definition_unfolding,[],[f32,f37,f37])).
% 27.34/4.00  
% 27.34/4.00  fof(f12,axiom,(
% 27.34/4.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)))),
% 27.34/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.34/4.00  
% 27.34/4.00  fof(f23,plain,(
% 27.34/4.00    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 27.34/4.00    inference(ennf_transformation,[],[f12])).
% 27.34/4.00  
% 27.34/4.00  fof(f44,plain,(
% 27.34/4.00    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 27.34/4.00    inference(cnf_transformation,[],[f23])).
% 27.34/4.00  
% 27.34/4.00  fof(f50,plain,(
% 27.34/4.00    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)),
% 27.34/4.00    inference(cnf_transformation,[],[f31])).
% 27.34/4.00  
% 27.34/4.00  fof(f42,plain,(
% 27.34/4.00    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 27.34/4.00    inference(cnf_transformation,[],[f20])).
% 27.34/4.00  
% 27.34/4.00  fof(f46,plain,(
% 27.34/4.00    v2_pre_topc(sK0)),
% 27.34/4.00    inference(cnf_transformation,[],[f31])).
% 27.34/4.00  
% 27.34/4.00  cnf(c_13,negated_conjecture,
% 27.34/4.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 27.34/4.00      inference(cnf_transformation,[],[f48]) ).
% 27.34/4.00  
% 27.34/4.00  cnf(c_609,plain,
% 27.34/4.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 27.34/4.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 27.34/4.00  
% 27.34/4.00  cnf(c_8,plain,
% 27.34/4.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.34/4.00      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 27.34/4.00      | ~ l1_pre_topc(X1) ),
% 27.34/4.00      inference(cnf_transformation,[],[f43]) ).
% 27.34/4.00  
% 27.34/4.00  cnf(c_14,negated_conjecture,
% 27.34/4.00      ( l1_pre_topc(sK0) ),
% 27.34/4.00      inference(cnf_transformation,[],[f47]) ).
% 27.34/4.00  
% 27.34/4.00  cnf(c_230,plain,
% 27.34/4.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.34/4.00      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 27.34/4.00      | sK0 != X1 ),
% 27.34/4.00      inference(resolution_lifted,[status(thm)],[c_8,c_14]) ).
% 27.34/4.00  
% 27.34/4.00  cnf(c_231,plain,
% 27.34/4.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.34/4.00      | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 27.34/4.00      inference(unflattening,[status(thm)],[c_230]) ).
% 27.34/4.00  
% 27.34/4.00  cnf(c_606,plain,
% 27.34/4.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 27.34/4.00      | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 27.34/4.00      inference(predicate_to_equality,[status(thm)],[c_231]) ).
% 27.34/4.00  
% 27.34/4.00  cnf(c_4,plain,
% 27.34/4.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 27.34/4.00      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 27.34/4.00      | k4_subset_1(X1,X2,X0) = k3_tarski(k2_tarski(X2,X0)) ),
% 27.34/4.00      inference(cnf_transformation,[],[f56]) ).
% 27.34/4.00  
% 27.34/4.00  cnf(c_611,plain,
% 27.34/4.00      ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
% 27.34/4.00      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
% 27.34/4.00      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 27.34/4.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 27.34/4.00  
% 27.34/4.00  cnf(c_57953,plain,
% 27.34/4.00      ( k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X1)) = k3_tarski(k2_tarski(X0,k2_tops_1(sK0,X1)))
% 27.34/4.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 27.34/4.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 27.34/4.00      inference(superposition,[status(thm)],[c_606,c_611]) ).
% 27.34/4.00  
% 27.34/4.00  cnf(c_62776,plain,
% 27.34/4.00      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0)))
% 27.34/4.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 27.34/4.00      inference(superposition,[status(thm)],[c_609,c_57953]) ).
% 27.34/4.00  
% 27.34/4.00  cnf(c_62797,plain,
% 27.34/4.00      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
% 27.34/4.00      inference(superposition,[status(thm)],[c_609,c_62776]) ).
% 27.34/4.00  
% 27.34/4.00  cnf(c_10,plain,
% 27.34/4.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.34/4.00      | ~ l1_pre_topc(X1)
% 27.34/4.00      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
% 27.34/4.00      inference(cnf_transformation,[],[f45]) ).
% 27.34/4.00  
% 27.34/4.00  cnf(c_206,plain,
% 27.34/4.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.34/4.00      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0)
% 27.34/4.00      | sK0 != X1 ),
% 27.34/4.00      inference(resolution_lifted,[status(thm)],[c_10,c_14]) ).
% 27.34/4.00  
% 27.34/4.00  cnf(c_207,plain,
% 27.34/4.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.34/4.00      | k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0) ),
% 27.34/4.00      inference(unflattening,[status(thm)],[c_206]) ).
% 27.34/4.00  
% 27.34/4.00  cnf(c_608,plain,
% 27.34/4.00      ( k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0)
% 27.34/4.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 27.34/4.00      inference(predicate_to_equality,[status(thm)],[c_207]) ).
% 27.34/4.00  
% 27.34/4.00  cnf(c_720,plain,
% 27.34/4.00      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 27.34/4.00      inference(superposition,[status(thm)],[c_609,c_608]) ).
% 27.34/4.00  
% 27.34/4.00  cnf(c_62804,plain,
% 27.34/4.00      ( k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k2_pre_topc(sK0,sK1) ),
% 27.34/4.00      inference(light_normalisation,[status(thm)],[c_62797,c_720]) ).
% 27.34/4.00  
% 27.34/4.00  cnf(c_12,negated_conjecture,
% 27.34/4.00      ( v4_pre_topc(sK1,sK0)
% 27.34/4.00      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 27.34/4.00      inference(cnf_transformation,[],[f49]) ).
% 27.34/4.00  
% 27.34/4.00  cnf(c_99,plain,
% 27.34/4.00      ( v4_pre_topc(sK1,sK0)
% 27.34/4.00      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 27.34/4.00      inference(prop_impl,[status(thm)],[c_12]) ).
% 27.34/4.00  
% 27.34/4.00  cnf(c_7,plain,
% 27.34/4.00      ( ~ v4_pre_topc(X0,X1)
% 27.34/4.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.34/4.00      | ~ l1_pre_topc(X1)
% 27.34/4.00      | k2_pre_topc(X1,X0) = X0 ),
% 27.34/4.00      inference(cnf_transformation,[],[f41]) ).
% 27.34/4.00  
% 27.34/4.00  cnf(c_242,plain,
% 27.34/4.00      ( ~ v4_pre_topc(X0,X1)
% 27.34/4.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.34/4.00      | k2_pre_topc(X1,X0) = X0
% 27.34/4.00      | sK0 != X1 ),
% 27.34/4.00      inference(resolution_lifted,[status(thm)],[c_7,c_14]) ).
% 27.34/4.00  
% 27.34/4.00  cnf(c_243,plain,
% 27.34/4.00      ( ~ v4_pre_topc(X0,sK0)
% 27.34/4.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.34/4.00      | k2_pre_topc(sK0,X0) = X0 ),
% 27.34/4.00      inference(unflattening,[status(thm)],[c_242]) ).
% 27.34/4.00  
% 27.34/4.00  cnf(c_272,plain,
% 27.34/4.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.34/4.00      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 27.34/4.00      | k2_pre_topc(sK0,X0) = X0
% 27.34/4.00      | sK1 != X0
% 27.34/4.00      | sK0 != sK0 ),
% 27.34/4.00      inference(resolution_lifted,[status(thm)],[c_99,c_243]) ).
% 27.34/4.00  
% 27.34/4.00  cnf(c_273,plain,
% 27.34/4.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.34/4.00      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 27.34/4.00      | k2_pre_topc(sK0,sK1) = sK1 ),
% 27.34/4.00      inference(unflattening,[status(thm)],[c_272]) ).
% 27.34/4.00  
% 27.34/4.00  cnf(c_275,plain,
% 27.34/4.00      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 27.34/4.00      | k2_pre_topc(sK0,sK1) = sK1 ),
% 27.34/4.00      inference(global_propositional_subsumption,
% 27.34/4.00                [status(thm)],
% 27.34/4.00                [c_273,c_13]) ).
% 27.34/4.00  
% 27.34/4.00  cnf(c_322,plain,
% 27.34/4.00      ( k2_pre_topc(sK0,sK1) = sK1
% 27.34/4.00      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 27.34/4.00      inference(prop_impl,[status(thm)],[c_275]) ).
% 27.34/4.00  
% 27.34/4.00  cnf(c_323,plain,
% 27.34/4.00      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 27.34/4.00      | k2_pre_topc(sK0,sK1) = sK1 ),
% 27.34/4.00      inference(renaming,[status(thm)],[c_322]) ).
% 27.34/4.00  
% 27.34/4.00  cnf(c_5,plain,
% 27.34/4.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 27.34/4.00      | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2))) = k7_subset_1(X1,X0,X2) ),
% 27.34/4.00      inference(cnf_transformation,[],[f57]) ).
% 27.34/4.00  
% 27.34/4.00  cnf(c_610,plain,
% 27.34/4.00      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X2,X0,X1)
% 27.34/4.00      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
% 27.34/4.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 27.34/4.00  
% 27.34/4.00  cnf(c_3405,plain,
% 27.34/4.00      ( k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0))) = k7_subset_1(u1_struct_0(sK0),sK1,X0) ),
% 27.34/4.00      inference(superposition,[status(thm)],[c_609,c_610]) ).
% 27.34/4.00  
% 27.34/4.00  cnf(c_1,plain,
% 27.34/4.00      ( k3_tarski(k2_tarski(X0,k1_setfam_1(k2_tarski(X0,X1)))) = X0 ),
% 27.34/4.00      inference(cnf_transformation,[],[f53]) ).
% 27.34/4.00  
% 27.34/4.00  cnf(c_3,plain,
% 27.34/4.00      ( k3_tarski(k2_tarski(k5_xboole_0(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(X0,X1)) ),
% 27.34/4.00      inference(cnf_transformation,[],[f55]) ).
% 27.34/4.00  
% 27.34/4.00  cnf(c_2,plain,
% 27.34/4.00      ( k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(X0,X1)) ),
% 27.34/4.00      inference(cnf_transformation,[],[f54]) ).
% 27.34/4.00  
% 27.34/4.00  cnf(c_1207,plain,
% 27.34/4.00      ( k3_tarski(k2_tarski(k5_xboole_0(X0,X1),k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(k5_xboole_0(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))) ),
% 27.34/4.00      inference(superposition,[status(thm)],[c_3,c_2]) ).
% 27.34/4.00  
% 27.34/4.00  cnf(c_1208,plain,
% 27.34/4.00      ( k3_tarski(k2_tarski(k5_xboole_0(X0,X1),k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(X0,X1)) ),
% 27.34/4.00      inference(light_normalisation,[status(thm)],[c_1207,c_3]) ).
% 27.34/4.00  
% 27.34/4.00  cnf(c_2433,plain,
% 27.34/4.00      ( k3_tarski(k2_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0)) = k3_tarski(k2_tarski(X0,k1_setfam_1(k2_tarski(X0,X1)))) ),
% 27.34/4.00      inference(superposition,[status(thm)],[c_1,c_1208]) ).
% 27.34/4.00  
% 27.34/4.00  cnf(c_2460,plain,
% 27.34/4.00      ( k3_tarski(k2_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0)) = X0 ),
% 27.34/4.00      inference(light_normalisation,[status(thm)],[c_2433,c_1]) ).
% 27.34/4.00  
% 27.34/4.00  cnf(c_0,plain,
% 27.34/4.00      ( k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X1,X0)) ),
% 27.34/4.00      inference(cnf_transformation,[],[f52]) ).
% 27.34/4.00  
% 27.34/4.00  cnf(c_2476,plain,
% 27.34/4.00      ( k3_tarski(k2_tarski(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))) = X0 ),
% 27.34/4.00      inference(superposition,[status(thm)],[c_2460,c_0]) ).
% 27.34/4.00  
% 27.34/4.00  cnf(c_4052,plain,
% 27.34/4.00      ( k3_tarski(k2_tarski(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0))) = sK1 ),
% 27.34/4.00      inference(superposition,[status(thm)],[c_3405,c_2476]) ).
% 27.34/4.00  
% 27.34/4.00  cnf(c_4479,plain,
% 27.34/4.00      ( k2_pre_topc(sK0,sK1) = sK1
% 27.34/4.00      | k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = sK1 ),
% 27.34/4.00      inference(superposition,[status(thm)],[c_323,c_4052]) ).
% 27.34/4.00  
% 27.34/4.00  cnf(c_63085,plain,
% 27.34/4.00      ( k2_pre_topc(sK0,sK1) = sK1 ),
% 27.34/4.00      inference(superposition,[status(thm)],[c_62804,c_4479]) ).
% 27.34/4.00  
% 27.34/4.00  cnf(c_386,plain,
% 27.34/4.00      ( X0 != X1
% 27.34/4.00      | X2 != X3
% 27.34/4.00      | X4 != X5
% 27.34/4.00      | k7_subset_1(X0,X2,X4) = k7_subset_1(X1,X3,X5) ),
% 27.34/4.00      theory(equality) ).
% 27.34/4.00  
% 27.34/4.00  cnf(c_378,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 27.34/4.00  
% 27.34/4.00  cnf(c_2494,plain,
% 27.34/4.00      ( X0 != X1
% 27.34/4.00      | X2 != X3
% 27.34/4.00      | X4 != X5
% 27.34/4.00      | X6 != k7_subset_1(X1,X3,X5)
% 27.34/4.00      | k7_subset_1(X0,X2,X4) = X6 ),
% 27.34/4.00      inference(resolution,[status(thm)],[c_386,c_378]) ).
% 27.34/4.00  
% 27.34/4.00  cnf(c_377,plain,( X0 = X0 ),theory(equality) ).
% 27.34/4.00  
% 27.34/4.00  cnf(c_870,plain,
% 27.34/4.00      ( X0 != X1 | X1 = X0 ),
% 27.34/4.00      inference(resolution,[status(thm)],[c_378,c_377]) ).
% 27.34/4.00  
% 27.34/4.00  cnf(c_9,plain,
% 27.34/4.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.34/4.00      | ~ l1_pre_topc(X1)
% 27.34/4.00      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
% 27.34/4.00      inference(cnf_transformation,[],[f44]) ).
% 27.34/4.00  
% 27.34/4.00  cnf(c_218,plain,
% 27.34/4.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.34/4.00      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0)
% 27.34/4.00      | sK0 != X1 ),
% 27.34/4.00      inference(resolution_lifted,[status(thm)],[c_9,c_14]) ).
% 27.34/4.00  
% 27.34/4.00  cnf(c_219,plain,
% 27.34/4.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.34/4.00      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
% 27.34/4.00      inference(unflattening,[status(thm)],[c_218]) ).
% 27.34/4.00  
% 27.34/4.00  cnf(c_3476,plain,
% 27.34/4.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.34/4.00      | k2_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) ),
% 27.34/4.00      inference(resolution,[status(thm)],[c_870,c_219]) ).
% 27.34/4.00  
% 27.34/4.00  cnf(c_18128,plain,
% 27.34/4.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.34/4.00      | X1 != k1_tops_1(sK0,X0)
% 27.34/4.00      | X2 != k2_pre_topc(sK0,X0)
% 27.34/4.00      | X3 != u1_struct_0(sK0)
% 27.34/4.00      | k7_subset_1(X3,X2,X1) = k2_tops_1(sK0,X0) ),
% 27.34/4.00      inference(resolution,[status(thm)],[c_2494,c_3476]) ).
% 27.34/4.00  
% 27.34/4.00  cnf(c_11,negated_conjecture,
% 27.34/4.00      ( ~ v4_pre_topc(sK1,sK0)
% 27.34/4.00      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
% 27.34/4.00      inference(cnf_transformation,[],[f50]) ).
% 27.34/4.00  
% 27.34/4.00  cnf(c_97,plain,
% 27.34/4.00      ( ~ v4_pre_topc(sK1,sK0)
% 27.34/4.00      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
% 27.34/4.00      inference(prop_impl,[status(thm)],[c_11]) ).
% 27.34/4.00  
% 27.34/4.00  cnf(c_6,plain,
% 27.34/4.00      ( v4_pre_topc(X0,X1)
% 27.34/4.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.34/4.00      | ~ l1_pre_topc(X1)
% 27.34/4.00      | ~ v2_pre_topc(X1)
% 27.34/4.00      | k2_pre_topc(X1,X0) != X0 ),
% 27.34/4.00      inference(cnf_transformation,[],[f42]) ).
% 27.34/4.00  
% 27.34/4.00  cnf(c_15,negated_conjecture,
% 27.34/4.00      ( v2_pre_topc(sK0) ),
% 27.34/4.00      inference(cnf_transformation,[],[f46]) ).
% 27.34/4.00  
% 27.34/4.00  cnf(c_181,plain,
% 27.34/4.00      ( v4_pre_topc(X0,X1)
% 27.34/4.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.34/4.00      | ~ l1_pre_topc(X1)
% 27.34/4.00      | k2_pre_topc(X1,X0) != X0
% 27.34/4.00      | sK0 != X1 ),
% 27.34/4.00      inference(resolution_lifted,[status(thm)],[c_6,c_15]) ).
% 27.34/4.00  
% 27.34/4.00  cnf(c_182,plain,
% 27.34/4.00      ( v4_pre_topc(X0,sK0)
% 27.34/4.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.34/4.00      | ~ l1_pre_topc(sK0)
% 27.34/4.00      | k2_pre_topc(sK0,X0) != X0 ),
% 27.34/4.00      inference(unflattening,[status(thm)],[c_181]) ).
% 27.34/4.00  
% 27.34/4.00  cnf(c_186,plain,
% 27.34/4.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.34/4.00      | v4_pre_topc(X0,sK0)
% 27.34/4.00      | k2_pre_topc(sK0,X0) != X0 ),
% 27.34/4.00      inference(global_propositional_subsumption,
% 27.34/4.00                [status(thm)],
% 27.34/4.00                [c_182,c_14]) ).
% 27.34/4.00  
% 27.34/4.00  cnf(c_187,plain,
% 27.34/4.00      ( v4_pre_topc(X0,sK0)
% 27.34/4.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.34/4.00      | k2_pre_topc(sK0,X0) != X0 ),
% 27.34/4.00      inference(renaming,[status(thm)],[c_186]) ).
% 27.34/4.00  
% 27.34/4.00  cnf(c_283,plain,
% 27.34/4.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.34/4.00      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
% 27.34/4.00      | k2_pre_topc(sK0,X0) != X0
% 27.34/4.00      | sK1 != X0
% 27.34/4.00      | sK0 != sK0 ),
% 27.34/4.00      inference(resolution_lifted,[status(thm)],[c_97,c_187]) ).
% 27.34/4.00  
% 27.34/4.00  cnf(c_284,plain,
% 27.34/4.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.34/4.00      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
% 27.34/4.00      | k2_pre_topc(sK0,sK1) != sK1 ),
% 27.34/4.00      inference(unflattening,[status(thm)],[c_283]) ).
% 27.34/4.00  
% 27.34/4.00  cnf(c_286,plain,
% 27.34/4.00      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
% 27.34/4.00      | k2_pre_topc(sK0,sK1) != sK1 ),
% 27.34/4.00      inference(global_propositional_subsumption,
% 27.34/4.00                [status(thm)],
% 27.34/4.00                [c_284,c_13]) ).
% 27.34/4.00  
% 27.34/4.00  cnf(c_320,plain,
% 27.34/4.00      ( k2_pre_topc(sK0,sK1) != sK1
% 27.34/4.00      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
% 27.34/4.00      inference(prop_impl,[status(thm)],[c_286]) ).
% 27.34/4.00  
% 27.34/4.00  cnf(c_321,plain,
% 27.34/4.00      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
% 27.34/4.00      | k2_pre_topc(sK0,sK1) != sK1 ),
% 27.34/4.00      inference(renaming,[status(thm)],[c_320]) ).
% 27.34/4.00  
% 27.34/4.00  cnf(c_20641,plain,
% 27.34/4.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.34/4.00      | k1_tops_1(sK0,sK1) != k1_tops_1(sK0,sK1)
% 27.34/4.00      | k2_pre_topc(sK0,sK1) != sK1
% 27.34/4.00      | u1_struct_0(sK0) != u1_struct_0(sK0)
% 27.34/4.00      | sK1 != k2_pre_topc(sK0,sK1) ),
% 27.34/4.00      inference(resolution,[status(thm)],[c_18128,c_321]) ).
% 27.34/4.00  
% 27.34/4.00  cnf(c_20642,plain,
% 27.34/4.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.34/4.00      | k2_pre_topc(sK0,sK1) != sK1
% 27.34/4.00      | sK1 != k2_pre_topc(sK0,sK1) ),
% 27.34/4.00      inference(equality_resolution_simp,[status(thm)],[c_20641]) ).
% 27.34/4.00  
% 27.34/4.00  cnf(c_812,plain,
% 27.34/4.00      ( X0 != X1 | sK1 != X1 | sK1 = X0 ),
% 27.34/4.00      inference(instantiation,[status(thm)],[c_378]) ).
% 27.34/4.00  
% 27.34/4.00  cnf(c_1083,plain,
% 27.34/4.00      ( X0 != sK1 | sK1 = X0 | sK1 != sK1 ),
% 27.34/4.00      inference(instantiation,[status(thm)],[c_812]) ).
% 27.34/4.00  
% 27.34/4.00  cnf(c_1959,plain,
% 27.34/4.00      ( k2_pre_topc(sK0,sK1) != sK1
% 27.34/4.00      | sK1 = k2_pre_topc(sK0,sK1)
% 27.34/4.00      | sK1 != sK1 ),
% 27.34/4.00      inference(instantiation,[status(thm)],[c_1083]) ).
% 27.34/4.00  
% 27.34/4.00  cnf(c_804,plain,
% 27.34/4.00      ( sK1 = sK1 ),
% 27.34/4.00      inference(instantiation,[status(thm)],[c_377]) ).
% 27.34/4.00  
% 27.34/4.00  cnf(contradiction,plain,
% 27.34/4.00      ( $false ),
% 27.34/4.00      inference(minisat,[status(thm)],[c_63085,c_20642,c_1959,c_804,c_13]) ).
% 27.34/4.00  
% 27.34/4.00  
% 27.34/4.00  % SZS output end CNFRefutation for theBenchmark.p
% 27.34/4.00  
% 27.34/4.00  ------                               Statistics
% 27.34/4.00  
% 27.34/4.00  ------ Selected
% 27.34/4.00  
% 27.34/4.00  total_time:                             3.014
% 27.34/4.00  
%------------------------------------------------------------------------------
