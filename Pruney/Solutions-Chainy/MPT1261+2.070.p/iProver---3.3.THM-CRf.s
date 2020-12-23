%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:14:34 EST 2020

% Result     : Theorem 3.91s
% Output     : CNFRefutation 3.91s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 615 expanded)
%              Number of clauses        :   65 ( 164 expanded)
%              Number of leaves         :   17 ( 142 expanded)
%              Depth                    :   20
%              Number of atoms          :  309 (2674 expanded)
%              Number of equality atoms :  151 ( 884 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1)
            | ~ v4_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1)
            | ~ v4_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f35,plain,(
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

fof(f34,plain,
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

fof(f36,plain,
    ( ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f33,f35,f34])).

fof(f54,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f36])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f47,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f19])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k2_tarski(X1,X2)) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f44,f43])).

fof(f53,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f45,f37])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f57,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) ),
    inference(definition_unfolding,[],[f41,f37,f37])).

fof(f55,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => r1_tarski(k2_tops_1(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_tops_1(X0,X1),X1)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f58,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,k3_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f38,f43])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f52,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f56,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_593,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_600,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X2,X0) = k3_tarski(k2_tarski(X2,X0)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_602,plain,
    ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4783,plain,
    ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X2)) = k3_tarski(k2_tarski(X1,k2_tops_1(X0,X2)))
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_600,c_602])).

cnf(c_12904,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_593,c_4783])).

cnf(c_16,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_19,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_13502,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12904,c_19])).

cnf(c_13503,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_13502])).

cnf(c_13511,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
    inference(superposition,[status(thm)],[c_593,c_13503])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_598,plain,
    ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2998,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_593,c_598])).

cnf(c_821,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_3298,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2998,c_16,c_15,c_821])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X0,k3_xboole_0(X0,X2)) = k7_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_601,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k7_subset_1(X2,X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_4565,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k3_xboole_0(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_593,c_601])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_596,plain,
    ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_950,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_593,c_596])).

cnf(c_824,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1209,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_950,c_16,c_15,c_824])).

cnf(c_4819,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,k2_tops_1(sK0,sK1))) = k1_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_4565,c_1209])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_5342,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tops_1(sK0,sK1))) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_4819,c_0])).

cnf(c_14,negated_conjecture,
    ( v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_594,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_4804,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tops_1(sK0,sK1))) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4565,c_594])).

cnf(c_5763,plain,
    ( k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5342,c_4804])).

cnf(c_11,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k2_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_597,plain,
    ( v4_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(k2_tops_1(X1,X0),X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1750,plain,
    ( v4_pre_topc(sK1,sK0) != iProver_top
    | r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_593,c_597])).

cnf(c_2237,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1750,c_19])).

cnf(c_2238,plain,
    ( v4_pre_topc(sK1,sK0) != iProver_top
    | r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(renaming,[status(thm)],[c_2237])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_604,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2243,plain,
    ( k3_xboole_0(k2_tops_1(sK0,sK1),sK1) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2238,c_604])).

cnf(c_6148,plain,
    ( k3_xboole_0(k2_tops_1(sK0,sK1),sK1) = k2_tops_1(sK0,sK1)
    | k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_5763,c_2243])).

cnf(c_4,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_7,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_864,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_4,c_7])).

cnf(c_1078,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_864,c_7])).

cnf(c_6351,plain,
    ( k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_6148,c_1078])).

cnf(c_1,plain,
    ( k3_tarski(k2_tarski(X0,k3_xboole_0(X0,X1))) = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_6502,plain,
    ( k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = sK1 ),
    inference(superposition,[status(thm)],[c_6351,c_1])).

cnf(c_13513,plain,
    ( k2_pre_topc(sK0,sK1) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_13511,c_3298,c_6502])).

cnf(c_9,plain,
    ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_599,plain,
    ( v4_pre_topc(k2_pre_topc(X0,X1),X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4463,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) = iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_593,c_599])).

cnf(c_17,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_18,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_20,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_754,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_755,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_754])).

cnf(c_5027,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4463,c_18,c_19,c_20,c_755])).

cnf(c_13681,plain,
    ( v4_pre_topc(sK1,sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_13513,c_5027])).

cnf(c_13,negated_conjecture,
    ( ~ v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_595,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_4805,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tops_1(sK0,sK1))) != k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4565,c_595])).

cnf(c_5764,plain,
    ( k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5342,c_4805])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13681,c_6351,c_5764])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:46:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.91/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.91/1.00  
% 3.91/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.91/1.00  
% 3.91/1.00  ------  iProver source info
% 3.91/1.00  
% 3.91/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.91/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.91/1.00  git: non_committed_changes: false
% 3.91/1.00  git: last_make_outside_of_git: false
% 3.91/1.00  
% 3.91/1.00  ------ 
% 3.91/1.00  ------ Parsing...
% 3.91/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.91/1.00  
% 3.91/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.91/1.00  
% 3.91/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.91/1.00  
% 3.91/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.91/1.00  ------ Proving...
% 3.91/1.00  ------ Problem Properties 
% 3.91/1.00  
% 3.91/1.00  
% 3.91/1.00  clauses                                 18
% 3.91/1.00  conjectures                             5
% 3.91/1.00  EPR                                     2
% 3.91/1.00  Horn                                    17
% 3.91/1.00  unary                                   8
% 3.91/1.00  binary                                  4
% 3.91/1.00  lits                                    36
% 3.91/1.00  lits eq                                 11
% 3.91/1.00  fd_pure                                 0
% 3.91/1.00  fd_pseudo                               0
% 3.91/1.00  fd_cond                                 0
% 3.91/1.00  fd_pseudo_cond                          0
% 3.91/1.00  AC symbols                              0
% 3.91/1.00  
% 3.91/1.00  ------ Input Options Time Limit: Unbounded
% 3.91/1.00  
% 3.91/1.00  
% 3.91/1.00  ------ 
% 3.91/1.00  Current options:
% 3.91/1.00  ------ 
% 3.91/1.00  
% 3.91/1.00  
% 3.91/1.00  
% 3.91/1.00  
% 3.91/1.00  ------ Proving...
% 3.91/1.00  
% 3.91/1.00  
% 3.91/1.00  % SZS status Theorem for theBenchmark.p
% 3.91/1.00  
% 3.91/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.91/1.00  
% 3.91/1.00  fof(f16,conjecture,(
% 3.91/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 3.91/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.91/1.00  
% 3.91/1.00  fof(f17,negated_conjecture,(
% 3.91/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 3.91/1.00    inference(negated_conjecture,[],[f16])).
% 3.91/1.00  
% 3.91/1.00  fof(f30,plain,(
% 3.91/1.00    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 3.91/1.00    inference(ennf_transformation,[],[f17])).
% 3.91/1.00  
% 3.91/1.00  fof(f31,plain,(
% 3.91/1.00    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.91/1.00    inference(flattening,[],[f30])).
% 3.91/1.00  
% 3.91/1.00  fof(f32,plain,(
% 3.91/1.00    ? [X0] : (? [X1] : (((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.91/1.00    inference(nnf_transformation,[],[f31])).
% 3.91/1.00  
% 3.91/1.00  fof(f33,plain,(
% 3.91/1.00    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.91/1.00    inference(flattening,[],[f32])).
% 3.91/1.00  
% 3.91/1.00  fof(f35,plain,(
% 3.91/1.00    ( ! [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) != k2_tops_1(X0,sK1) | ~v4_pre_topc(sK1,X0)) & (k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) = k2_tops_1(X0,sK1) | v4_pre_topc(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.91/1.00    introduced(choice_axiom,[])).
% 3.91/1.00  
% 3.91/1.00  fof(f34,plain,(
% 3.91/1.00    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) != k2_tops_1(sK0,X1) | ~v4_pre_topc(X1,sK0)) & (k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) = k2_tops_1(sK0,X1) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 3.91/1.00    introduced(choice_axiom,[])).
% 3.91/1.00  
% 3.91/1.00  fof(f36,plain,(
% 3.91/1.00    ((k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)) & (k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 3.91/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f33,f35,f34])).
% 3.91/1.00  
% 3.91/1.00  fof(f54,plain,(
% 3.91/1.00    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.91/1.00    inference(cnf_transformation,[],[f36])).
% 3.91/1.00  
% 3.91/1.00  fof(f11,axiom,(
% 3.91/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.91/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.91/1.00  
% 3.91/1.00  fof(f22,plain,(
% 3.91/1.00    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.91/1.00    inference(ennf_transformation,[],[f11])).
% 3.91/1.00  
% 3.91/1.00  fof(f23,plain,(
% 3.91/1.00    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.91/1.00    inference(flattening,[],[f22])).
% 3.91/1.00  
% 3.91/1.00  fof(f47,plain,(
% 3.91/1.00    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.91/1.00    inference(cnf_transformation,[],[f23])).
% 3.91/1.00  
% 3.91/1.00  fof(f8,axiom,(
% 3.91/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 3.91/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.91/1.00  
% 3.91/1.00  fof(f19,plain,(
% 3.91/1.00    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 3.91/1.00    inference(ennf_transformation,[],[f8])).
% 3.91/1.00  
% 3.91/1.00  fof(f20,plain,(
% 3.91/1.00    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.91/1.00    inference(flattening,[],[f19])).
% 3.91/1.00  
% 3.91/1.00  fof(f44,plain,(
% 3.91/1.00    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.91/1.00    inference(cnf_transformation,[],[f20])).
% 3.91/1.00  
% 3.91/1.00  fof(f7,axiom,(
% 3.91/1.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.91/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.91/1.00  
% 3.91/1.00  fof(f43,plain,(
% 3.91/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.91/1.00    inference(cnf_transformation,[],[f7])).
% 3.91/1.00  
% 3.91/1.00  fof(f60,plain,(
% 3.91/1.00    ( ! [X2,X0,X1] : (k3_tarski(k2_tarski(X1,X2)) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.91/1.00    inference(definition_unfolding,[],[f44,f43])).
% 3.91/1.00  
% 3.91/1.00  fof(f53,plain,(
% 3.91/1.00    l1_pre_topc(sK0)),
% 3.91/1.00    inference(cnf_transformation,[],[f36])).
% 3.91/1.00  
% 3.91/1.00  fof(f13,axiom,(
% 3.91/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)))),
% 3.91/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.91/1.00  
% 3.91/1.00  fof(f26,plain,(
% 3.91/1.00    ! [X0] : (! [X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.91/1.00    inference(ennf_transformation,[],[f13])).
% 3.91/1.00  
% 3.91/1.00  fof(f49,plain,(
% 3.91/1.00    ( ! [X0,X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.91/1.00    inference(cnf_transformation,[],[f26])).
% 3.91/1.00  
% 3.91/1.00  fof(f9,axiom,(
% 3.91/1.00    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 3.91/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.91/1.00  
% 3.91/1.00  fof(f21,plain,(
% 3.91/1.00    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.91/1.00    inference(ennf_transformation,[],[f9])).
% 3.91/1.00  
% 3.91/1.00  fof(f45,plain,(
% 3.91/1.00    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.91/1.00    inference(cnf_transformation,[],[f21])).
% 3.91/1.00  
% 3.91/1.00  fof(f1,axiom,(
% 3.91/1.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.91/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.91/1.00  
% 3.91/1.00  fof(f37,plain,(
% 3.91/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.91/1.00    inference(cnf_transformation,[],[f1])).
% 3.91/1.00  
% 3.91/1.00  fof(f61,plain,(
% 3.91/1.00    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.91/1.00    inference(definition_unfolding,[],[f45,f37])).
% 3.91/1.00  
% 3.91/1.00  fof(f15,axiom,(
% 3.91/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)))),
% 3.91/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.91/1.00  
% 3.91/1.00  fof(f29,plain,(
% 3.91/1.00    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.91/1.00    inference(ennf_transformation,[],[f15])).
% 3.91/1.00  
% 3.91/1.00  fof(f51,plain,(
% 3.91/1.00    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.91/1.00    inference(cnf_transformation,[],[f29])).
% 3.91/1.00  
% 3.91/1.00  fof(f5,axiom,(
% 3.91/1.00    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 3.91/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.91/1.00  
% 3.91/1.00  fof(f41,plain,(
% 3.91/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 3.91/1.00    inference(cnf_transformation,[],[f5])).
% 3.91/1.00  
% 3.91/1.00  fof(f57,plain,(
% 3.91/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) )),
% 3.91/1.00    inference(definition_unfolding,[],[f41,f37,f37])).
% 3.91/1.00  
% 3.91/1.00  fof(f55,plain,(
% 3.91/1.00    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)),
% 3.91/1.00    inference(cnf_transformation,[],[f36])).
% 3.91/1.00  
% 3.91/1.00  fof(f14,axiom,(
% 3.91/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => r1_tarski(k2_tops_1(X0,X1),X1))))),
% 3.91/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.91/1.00  
% 3.91/1.00  fof(f27,plain,(
% 3.91/1.00    ! [X0] : (! [X1] : ((r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.91/1.00    inference(ennf_transformation,[],[f14])).
% 3.91/1.00  
% 3.91/1.00  fof(f28,plain,(
% 3.91/1.00    ! [X0] : (! [X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.91/1.00    inference(flattening,[],[f27])).
% 3.91/1.00  
% 3.91/1.00  fof(f50,plain,(
% 3.91/1.00    ( ! [X0,X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.91/1.00    inference(cnf_transformation,[],[f28])).
% 3.91/1.00  
% 3.91/1.00  fof(f3,axiom,(
% 3.91/1.00    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.91/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.91/1.00  
% 3.91/1.00  fof(f18,plain,(
% 3.91/1.00    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.91/1.00    inference(ennf_transformation,[],[f3])).
% 3.91/1.00  
% 3.91/1.00  fof(f39,plain,(
% 3.91/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.91/1.00    inference(cnf_transformation,[],[f18])).
% 3.91/1.00  
% 3.91/1.00  fof(f6,axiom,(
% 3.91/1.00    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 3.91/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.91/1.00  
% 3.91/1.00  fof(f42,plain,(
% 3.91/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 3.91/1.00    inference(cnf_transformation,[],[f6])).
% 3.91/1.00  
% 3.91/1.00  fof(f10,axiom,(
% 3.91/1.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.91/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.91/1.00  
% 3.91/1.00  fof(f46,plain,(
% 3.91/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.91/1.00    inference(cnf_transformation,[],[f10])).
% 3.91/1.00  
% 3.91/1.00  fof(f2,axiom,(
% 3.91/1.00    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 3.91/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.91/1.00  
% 3.91/1.00  fof(f38,plain,(
% 3.91/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 3.91/1.00    inference(cnf_transformation,[],[f2])).
% 3.91/1.00  
% 3.91/1.00  fof(f58,plain,(
% 3.91/1.00    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,k3_xboole_0(X0,X1))) = X0) )),
% 3.91/1.00    inference(definition_unfolding,[],[f38,f43])).
% 3.91/1.00  
% 3.91/1.00  fof(f12,axiom,(
% 3.91/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_pre_topc(X0,X1),X0))),
% 3.91/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.91/1.00  
% 3.91/1.00  fof(f24,plain,(
% 3.91/1.00    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.91/1.00    inference(ennf_transformation,[],[f12])).
% 3.91/1.00  
% 3.91/1.00  fof(f25,plain,(
% 3.91/1.00    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.91/1.00    inference(flattening,[],[f24])).
% 3.91/1.00  
% 3.91/1.00  fof(f48,plain,(
% 3.91/1.00    ( ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.91/1.00    inference(cnf_transformation,[],[f25])).
% 3.91/1.00  
% 3.91/1.00  fof(f52,plain,(
% 3.91/1.00    v2_pre_topc(sK0)),
% 3.91/1.00    inference(cnf_transformation,[],[f36])).
% 3.91/1.00  
% 3.91/1.00  fof(f56,plain,(
% 3.91/1.00    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)),
% 3.91/1.00    inference(cnf_transformation,[],[f36])).
% 3.91/1.00  
% 3.91/1.00  cnf(c_15,negated_conjecture,
% 3.91/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.91/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_593,plain,
% 3.91/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.91/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_8,plain,
% 3.91/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.91/1.00      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.91/1.00      | ~ l1_pre_topc(X1) ),
% 3.91/1.00      inference(cnf_transformation,[],[f47]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_600,plain,
% 3.91/1.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.91/1.00      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 3.91/1.00      | l1_pre_topc(X1) != iProver_top ),
% 3.91/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_5,plain,
% 3.91/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.91/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.91/1.00      | k4_subset_1(X1,X2,X0) = k3_tarski(k2_tarski(X2,X0)) ),
% 3.91/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_602,plain,
% 3.91/1.00      ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
% 3.91/1.00      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
% 3.91/1.00      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.91/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_4783,plain,
% 3.91/1.00      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X2)) = k3_tarski(k2_tarski(X1,k2_tops_1(X0,X2)))
% 3.91/1.00      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.91/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.91/1.00      | l1_pre_topc(X0) != iProver_top ),
% 3.91/1.00      inference(superposition,[status(thm)],[c_600,c_602]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_12904,plain,
% 3.91/1.00      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0)))
% 3.91/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.91/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 3.91/1.00      inference(superposition,[status(thm)],[c_593,c_4783]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_16,negated_conjecture,
% 3.91/1.00      ( l1_pre_topc(sK0) ),
% 3.91/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_19,plain,
% 3.91/1.00      ( l1_pre_topc(sK0) = iProver_top ),
% 3.91/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_13502,plain,
% 3.91/1.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.91/1.00      | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0))) ),
% 3.91/1.00      inference(global_propositional_subsumption,
% 3.91/1.00                [status(thm)],
% 3.91/1.00                [c_12904,c_19]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_13503,plain,
% 3.91/1.00      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0)))
% 3.91/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.91/1.00      inference(renaming,[status(thm)],[c_13502]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_13511,plain,
% 3.91/1.00      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
% 3.91/1.00      inference(superposition,[status(thm)],[c_593,c_13503]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_10,plain,
% 3.91/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.91/1.00      | ~ l1_pre_topc(X1)
% 3.91/1.00      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
% 3.91/1.00      inference(cnf_transformation,[],[f49]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_598,plain,
% 3.91/1.00      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
% 3.91/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.91/1.00      | l1_pre_topc(X0) != iProver_top ),
% 3.91/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_2998,plain,
% 3.91/1.00      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
% 3.91/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 3.91/1.00      inference(superposition,[status(thm)],[c_593,c_598]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_821,plain,
% 3.91/1.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.91/1.00      | ~ l1_pre_topc(sK0)
% 3.91/1.00      | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 3.91/1.00      inference(instantiation,[status(thm)],[c_10]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_3298,plain,
% 3.91/1.00      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 3.91/1.00      inference(global_propositional_subsumption,
% 3.91/1.00                [status(thm)],
% 3.91/1.00                [c_2998,c_16,c_15,c_821]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_6,plain,
% 3.91/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.91/1.00      | k5_xboole_0(X0,k3_xboole_0(X0,X2)) = k7_subset_1(X1,X0,X2) ),
% 3.91/1.00      inference(cnf_transformation,[],[f61]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_601,plain,
% 3.91/1.00      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k7_subset_1(X2,X0,X1)
% 3.91/1.00      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
% 3.91/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_4565,plain,
% 3.91/1.00      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k3_xboole_0(sK1,X0)) ),
% 3.91/1.00      inference(superposition,[status(thm)],[c_593,c_601]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_12,plain,
% 3.91/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.91/1.00      | ~ l1_pre_topc(X1)
% 3.91/1.00      | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
% 3.91/1.00      inference(cnf_transformation,[],[f51]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_596,plain,
% 3.91/1.00      ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
% 3.91/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.91/1.00      | l1_pre_topc(X0) != iProver_top ),
% 3.91/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_950,plain,
% 3.91/1.00      ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1)
% 3.91/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 3.91/1.00      inference(superposition,[status(thm)],[c_593,c_596]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_824,plain,
% 3.91/1.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.91/1.00      | ~ l1_pre_topc(sK0)
% 3.91/1.00      | k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
% 3.91/1.00      inference(instantiation,[status(thm)],[c_12]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_1209,plain,
% 3.91/1.00      ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
% 3.91/1.00      inference(global_propositional_subsumption,
% 3.91/1.00                [status(thm)],
% 3.91/1.00                [c_950,c_16,c_15,c_824]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_4819,plain,
% 3.91/1.00      ( k5_xboole_0(sK1,k3_xboole_0(sK1,k2_tops_1(sK0,sK1))) = k1_tops_1(sK0,sK1) ),
% 3.91/1.00      inference(superposition,[status(thm)],[c_4565,c_1209]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_0,plain,
% 3.91/1.00      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,X1) ),
% 3.91/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_5342,plain,
% 3.91/1.00      ( k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tops_1(sK0,sK1))) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
% 3.91/1.00      inference(superposition,[status(thm)],[c_4819,c_0]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_14,negated_conjecture,
% 3.91/1.00      ( v4_pre_topc(sK1,sK0)
% 3.91/1.00      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 3.91/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_594,plain,
% 3.91/1.00      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 3.91/1.00      | v4_pre_topc(sK1,sK0) = iProver_top ),
% 3.91/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_4804,plain,
% 3.91/1.00      ( k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tops_1(sK0,sK1))) = k2_tops_1(sK0,sK1)
% 3.91/1.00      | v4_pre_topc(sK1,sK0) = iProver_top ),
% 3.91/1.00      inference(demodulation,[status(thm)],[c_4565,c_594]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_5763,plain,
% 3.91/1.00      ( k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 3.91/1.00      | v4_pre_topc(sK1,sK0) = iProver_top ),
% 3.91/1.00      inference(demodulation,[status(thm)],[c_5342,c_4804]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_11,plain,
% 3.91/1.00      ( ~ v4_pre_topc(X0,X1)
% 3.91/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.91/1.00      | r1_tarski(k2_tops_1(X1,X0),X0)
% 3.91/1.00      | ~ l1_pre_topc(X1) ),
% 3.91/1.00      inference(cnf_transformation,[],[f50]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_597,plain,
% 3.91/1.00      ( v4_pre_topc(X0,X1) != iProver_top
% 3.91/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.91/1.00      | r1_tarski(k2_tops_1(X1,X0),X0) = iProver_top
% 3.91/1.00      | l1_pre_topc(X1) != iProver_top ),
% 3.91/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_1750,plain,
% 3.91/1.00      ( v4_pre_topc(sK1,sK0) != iProver_top
% 3.91/1.00      | r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top
% 3.91/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 3.91/1.00      inference(superposition,[status(thm)],[c_593,c_597]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_2237,plain,
% 3.91/1.00      ( r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top
% 3.91/1.00      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 3.91/1.00      inference(global_propositional_subsumption,
% 3.91/1.00                [status(thm)],
% 3.91/1.00                [c_1750,c_19]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_2238,plain,
% 3.91/1.00      ( v4_pre_topc(sK1,sK0) != iProver_top
% 3.91/1.00      | r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top ),
% 3.91/1.00      inference(renaming,[status(thm)],[c_2237]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_2,plain,
% 3.91/1.00      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 3.91/1.00      inference(cnf_transformation,[],[f39]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_604,plain,
% 3.91/1.00      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 3.91/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_2243,plain,
% 3.91/1.00      ( k3_xboole_0(k2_tops_1(sK0,sK1),sK1) = k2_tops_1(sK0,sK1)
% 3.91/1.00      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 3.91/1.00      inference(superposition,[status(thm)],[c_2238,c_604]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_6148,plain,
% 3.91/1.00      ( k3_xboole_0(k2_tops_1(sK0,sK1),sK1) = k2_tops_1(sK0,sK1)
% 3.91/1.00      | k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 3.91/1.00      inference(superposition,[status(thm)],[c_5763,c_2243]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_4,plain,
% 3.91/1.00      ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
% 3.91/1.00      inference(cnf_transformation,[],[f42]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_7,plain,
% 3.91/1.00      ( k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
% 3.91/1.00      inference(cnf_transformation,[],[f46]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_864,plain,
% 3.91/1.00      ( k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X1,X0) ),
% 3.91/1.00      inference(superposition,[status(thm)],[c_4,c_7]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_1078,plain,
% 3.91/1.00      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 3.91/1.00      inference(superposition,[status(thm)],[c_864,c_7]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_6351,plain,
% 3.91/1.00      ( k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 3.91/1.00      inference(superposition,[status(thm)],[c_6148,c_1078]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_1,plain,
% 3.91/1.00      ( k3_tarski(k2_tarski(X0,k3_xboole_0(X0,X1))) = X0 ),
% 3.91/1.00      inference(cnf_transformation,[],[f58]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_6502,plain,
% 3.91/1.00      ( k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = sK1 ),
% 3.91/1.00      inference(superposition,[status(thm)],[c_6351,c_1]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_13513,plain,
% 3.91/1.00      ( k2_pre_topc(sK0,sK1) = sK1 ),
% 3.91/1.00      inference(light_normalisation,
% 3.91/1.00                [status(thm)],
% 3.91/1.00                [c_13511,c_3298,c_6502]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_9,plain,
% 3.91/1.00      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
% 3.91/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.91/1.00      | ~ v2_pre_topc(X0)
% 3.91/1.00      | ~ l1_pre_topc(X0) ),
% 3.91/1.00      inference(cnf_transformation,[],[f48]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_599,plain,
% 3.91/1.00      ( v4_pre_topc(k2_pre_topc(X0,X1),X0) = iProver_top
% 3.91/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.91/1.00      | v2_pre_topc(X0) != iProver_top
% 3.91/1.00      | l1_pre_topc(X0) != iProver_top ),
% 3.91/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_4463,plain,
% 3.91/1.00      ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) = iProver_top
% 3.91/1.00      | v2_pre_topc(sK0) != iProver_top
% 3.91/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 3.91/1.00      inference(superposition,[status(thm)],[c_593,c_599]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_17,negated_conjecture,
% 3.91/1.00      ( v2_pre_topc(sK0) ),
% 3.91/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_18,plain,
% 3.91/1.00      ( v2_pre_topc(sK0) = iProver_top ),
% 3.91/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_20,plain,
% 3.91/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.91/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_754,plain,
% 3.91/1.00      ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0)
% 3.91/1.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.91/1.00      | ~ v2_pre_topc(sK0)
% 3.91/1.00      | ~ l1_pre_topc(sK0) ),
% 3.91/1.00      inference(instantiation,[status(thm)],[c_9]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_755,plain,
% 3.91/1.00      ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) = iProver_top
% 3.91/1.00      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.91/1.00      | v2_pre_topc(sK0) != iProver_top
% 3.91/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 3.91/1.00      inference(predicate_to_equality,[status(thm)],[c_754]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_5027,plain,
% 3.91/1.00      ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) = iProver_top ),
% 3.91/1.00      inference(global_propositional_subsumption,
% 3.91/1.00                [status(thm)],
% 3.91/1.00                [c_4463,c_18,c_19,c_20,c_755]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_13681,plain,
% 3.91/1.00      ( v4_pre_topc(sK1,sK0) = iProver_top ),
% 3.91/1.00      inference(demodulation,[status(thm)],[c_13513,c_5027]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_13,negated_conjecture,
% 3.91/1.00      ( ~ v4_pre_topc(sK1,sK0)
% 3.91/1.00      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
% 3.91/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_595,plain,
% 3.91/1.00      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
% 3.91/1.00      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 3.91/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_4805,plain,
% 3.91/1.00      ( k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tops_1(sK0,sK1))) != k2_tops_1(sK0,sK1)
% 3.91/1.00      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 3.91/1.00      inference(demodulation,[status(thm)],[c_4565,c_595]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(c_5764,plain,
% 3.91/1.00      ( k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
% 3.91/1.00      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 3.91/1.00      inference(demodulation,[status(thm)],[c_5342,c_4805]) ).
% 3.91/1.00  
% 3.91/1.00  cnf(contradiction,plain,
% 3.91/1.00      ( $false ),
% 3.91/1.00      inference(minisat,[status(thm)],[c_13681,c_6351,c_5764]) ).
% 3.91/1.00  
% 3.91/1.00  
% 3.91/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.91/1.00  
% 3.91/1.00  ------                               Statistics
% 3.91/1.00  
% 3.91/1.00  ------ Selected
% 3.91/1.00  
% 3.91/1.00  total_time:                             0.49
% 3.91/1.00  
%------------------------------------------------------------------------------
