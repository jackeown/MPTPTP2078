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
% DateTime   : Thu Dec  3 12:14:10 EST 2020

% Result     : Theorem 15.20s
% Output     : CNFRefutation 15.20s
% Verified   : 
% Statistics : Number of formulae       :  172 ( 887 expanded)
%              Number of clauses        :  103 ( 350 expanded)
%              Number of leaves         :   22 ( 191 expanded)
%              Depth                    :   22
%              Number of atoms          :  352 (2409 expanded)
%              Number of equality atoms :  175 ( 454 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f21,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => r1_tarski(k2_tops_1(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
             => r1_tarski(k2_tops_1(X0,X1),X1) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(X0,X1),X1)
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(X0,X1),X1)
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f45,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(X0,X1),X1)
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_tarski(k2_tops_1(X0,sK1),sK1)
        & v4_pre_topc(sK1,X0)
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k2_tops_1(X0,X1),X1)
            & v4_pre_topc(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(sK0,X1),X1)
          & v4_pre_topc(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),sK1)
    & v4_pre_topc(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f41,f45,f44])).

fof(f68,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f65,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f63,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f69,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f46])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k2_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k2_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k2_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f19,axiom,(
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

fof(f23,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => k2_pre_topc(X0,X1) = X1 ) ) ) ),
    inference(pure_predicate_removal,[],[f19])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = X1
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = X1
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f37])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f70,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f13,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f29])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f64,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X2,X0,X1] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f71,plain,(
    ~ r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_24,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_857,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_18,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_863,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1206,plain,
    ( l1_struct_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_857,c_863])).

cnf(c_16,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_865,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1478,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_1206,c_865])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_858,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_1747,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1478,c_858])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_866,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2040,plain,
    ( r1_tarski(sK1,k2_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1747,c_866])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X0,X2) = k9_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_14,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_176,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_14])).

cnf(c_177,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_176])).

cnf(c_213,plain,
    ( ~ r1_tarski(X0,X1)
    | k9_subset_1(X1,X0,X2) = k9_subset_1(X1,X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_6,c_177])).

cnf(c_856,plain,
    ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_213])).

cnf(c_10626,plain,
    ( k9_subset_1(k2_struct_0(sK0),sK1,X0) = k9_subset_1(k2_struct_0(sK0),X0,sK1) ),
    inference(superposition,[status(thm)],[c_2040,c_856])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_218,plain,
    ( ~ r1_tarski(X0,X1)
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_11,c_177])).

cnf(c_851,plain,
    ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_218])).

cnf(c_2598,plain,
    ( k9_subset_1(k2_struct_0(sK0),X0,sK1) = k3_xboole_0(X0,sK1) ),
    inference(superposition,[status(thm)],[c_2040,c_851])).

cnf(c_10649,plain,
    ( k9_subset_1(k2_struct_0(sK0),sK1,X0) = k3_xboole_0(X0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_10626,c_2598])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_861,plain,
    ( k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k2_tops_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_13017,plain,
    ( k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k2_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1478,c_861])).

cnf(c_13021,plain,
    ( k9_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,X0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) = k2_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_13017,c_1478])).

cnf(c_25,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_14083,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | k9_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,X0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) = k2_tops_1(sK0,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13021,c_25])).

cnf(c_14084,plain,
    ( k9_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,X0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) = k2_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_14083])).

cnf(c_14093,plain,
    ( k9_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_1747,c_14084])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_214,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_7,c_177])).

cnf(c_855,plain,
    ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_214])).

cnf(c_9022,plain,
    ( k3_subset_1(k2_struct_0(sK0),sK1) = k4_xboole_0(k2_struct_0(sK0),sK1) ),
    inference(superposition,[status(thm)],[c_2040,c_855])).

cnf(c_19,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_862,plain,
    ( k2_pre_topc(X0,X1) = X1
    | v4_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_10942,plain,
    ( k2_pre_topc(sK0,X0) = X0
    | v4_pre_topc(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1478,c_862])).

cnf(c_11856,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | v4_pre_topc(X0,sK0) != iProver_top
    | k2_pre_topc(sK0,X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10942,c_25])).

cnf(c_11857,plain,
    ( k2_pre_topc(sK0,X0) = X0
    | v4_pre_topc(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_11856])).

cnf(c_11867,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1747,c_11857])).

cnf(c_22,negated_conjecture,
    ( v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1128,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_11894,plain,
    ( k2_pre_topc(sK0,sK1) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_11867,c_24,c_23,c_22,c_1128])).

cnf(c_14099,plain,
    ( k9_subset_1(k2_struct_0(sK0),sK1,k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))) = k2_tops_1(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_14093,c_9022,c_11894])).

cnf(c_14345,plain,
    ( k3_xboole_0(k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)),sK1) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_10649,c_14099])).

cnf(c_13,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_868,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_216,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,X1)
    | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_9,c_177])).

cnf(c_853,plain,
    ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_216])).

cnf(c_5034,plain,
    ( k4_subset_1(X0,k1_xboole_0,X1) = k2_xboole_0(k1_xboole_0,X1)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_868,c_853])).

cnf(c_47627,plain,
    ( k4_subset_1(k2_struct_0(sK0),k1_xboole_0,sK1) = k2_xboole_0(k1_xboole_0,sK1) ),
    inference(superposition,[status(thm)],[c_2040,c_5034])).

cnf(c_17,plain,
    ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_864,plain,
    ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2180,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
    | l1_struct_0(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1478,c_864])).

cnf(c_35,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_37,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | l1_struct_0(sK0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_35])).

cnf(c_2924,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2180,c_25,c_37])).

cnf(c_2929,plain,
    ( r1_tarski(k2_struct_0(sK0),k2_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2924,c_866])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_217,plain,
    ( ~ r1_tarski(X0,X1)
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_10,c_177])).

cnf(c_852,plain,
    ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_217])).

cnf(c_3664,plain,
    ( k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),X0) = k4_xboole_0(k2_struct_0(sK0),X0) ),
    inference(superposition,[status(thm)],[c_2929,c_852])).

cnf(c_9026,plain,
    ( k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)) = k4_xboole_0(k2_struct_0(sK0),k2_struct_0(sK0)) ),
    inference(superposition,[status(thm)],[c_2929,c_855])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_872,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2596,plain,
    ( k2_xboole_0(sK1,k2_struct_0(sK0)) = k2_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_2040,c_872])).

cnf(c_5,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2762,plain,
    ( k4_xboole_0(k2_struct_0(sK0),k2_struct_0(sK0)) = k4_xboole_0(sK1,k2_struct_0(sK0)) ),
    inference(superposition,[status(thm)],[c_2596,c_5])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_870,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2597,plain,
    ( k4_xboole_0(sK1,k2_struct_0(sK0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2040,c_870])).

cnf(c_2776,plain,
    ( k4_xboole_0(k2_struct_0(sK0),k2_struct_0(sK0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2762,c_2597])).

cnf(c_9037,plain,
    ( k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_9026,c_2776])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,k3_subset_1(X1,X2),X0) = k3_subset_1(X1,k7_subset_1(X1,X2,X0)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_219,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,X1)
    | k4_subset_1(X1,k3_subset_1(X1,X0),X2) = k3_subset_1(X1,k7_subset_1(X1,X0,X2)) ),
    inference(bin_hyper_res,[status(thm)],[c_12,c_177])).

cnf(c_850,plain,
    ( k4_subset_1(X0,k3_subset_1(X0,X1),X2) = k3_subset_1(X0,k7_subset_1(X0,X1,X2))
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_219])).

cnf(c_2930,plain,
    ( k4_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)),X0) = k3_subset_1(k2_struct_0(sK0),k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),X0))
    | r1_tarski(X0,k2_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2924,c_850])).

cnf(c_8873,plain,
    ( k4_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)),sK1) = k3_subset_1(k2_struct_0(sK0),k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1)) ),
    inference(superposition,[status(thm)],[c_2040,c_2930])).

cnf(c_10610,plain,
    ( k3_subset_1(k2_struct_0(sK0),k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1)) = k4_subset_1(k2_struct_0(sK0),k1_xboole_0,sK1) ),
    inference(demodulation,[status(thm)],[c_9037,c_8873])).

cnf(c_18024,plain,
    ( k3_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1)) = k4_subset_1(k2_struct_0(sK0),k1_xboole_0,sK1) ),
    inference(demodulation,[status(thm)],[c_3664,c_10610])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_215,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(bin_hyper_res,[status(thm)],[c_8,c_177])).

cnf(c_854,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_215])).

cnf(c_7199,plain,
    ( k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_2040,c_854])).

cnf(c_9855,plain,
    ( k3_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1)) = sK1 ),
    inference(demodulation,[status(thm)],[c_9022,c_7199])).

cnf(c_18025,plain,
    ( k4_subset_1(k2_struct_0(sK0),k1_xboole_0,sK1) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_18024,c_9855])).

cnf(c_47750,plain,
    ( k2_xboole_0(k1_xboole_0,sK1) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_47627,c_18025])).

cnf(c_1,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_2,plain,
    ( r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_871,plain,
    ( r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_916,plain,
    ( r1_tarski(k3_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X1,X2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1,c_871])).

cnf(c_1846,plain,
    ( k4_xboole_0(k3_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_916,c_870])).

cnf(c_48522,plain,
    ( k4_xboole_0(k3_xboole_0(X0,sK1),sK1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_47750,c_1846])).

cnf(c_49241,plain,
    ( k4_xboole_0(k2_tops_1(sK0,sK1),sK1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_14345,c_48522])).

cnf(c_4,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_18350,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | k4_xboole_0(k2_tops_1(sK0,sK1),sK1) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_21,negated_conjecture,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f71])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_49241,c_18350,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:21:53 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 15.20/2.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.20/2.49  
% 15.20/2.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.20/2.49  
% 15.20/2.49  ------  iProver source info
% 15.20/2.49  
% 15.20/2.49  git: date: 2020-06-30 10:37:57 +0100
% 15.20/2.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.20/2.49  git: non_committed_changes: false
% 15.20/2.49  git: last_make_outside_of_git: false
% 15.20/2.49  
% 15.20/2.49  ------ 
% 15.20/2.49  ------ Parsing...
% 15.20/2.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.20/2.49  
% 15.20/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 15.20/2.49  
% 15.20/2.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.20/2.49  
% 15.20/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.20/2.49  ------ Proving...
% 15.20/2.49  ------ Problem Properties 
% 15.20/2.49  
% 15.20/2.49  
% 15.20/2.49  clauses                                 25
% 15.20/2.49  conjectures                             4
% 15.20/2.49  EPR                                     3
% 15.20/2.49  Horn                                    25
% 15.20/2.49  unary                                   8
% 15.20/2.49  binary                                  13
% 15.20/2.49  lits                                    47
% 15.20/2.49  lits eq                                 15
% 15.20/2.49  fd_pure                                 0
% 15.20/2.49  fd_pseudo                               0
% 15.20/2.49  fd_cond                                 0
% 15.20/2.49  fd_pseudo_cond                          0
% 15.20/2.49  AC symbols                              0
% 15.20/2.49  
% 15.20/2.49  ------ Input Options Time Limit: Unbounded
% 15.20/2.49  
% 15.20/2.49  
% 15.20/2.49  ------ 
% 15.20/2.49  Current options:
% 15.20/2.49  ------ 
% 15.20/2.49  
% 15.20/2.49  
% 15.20/2.49  
% 15.20/2.49  
% 15.20/2.49  ------ Proving...
% 15.20/2.49  
% 15.20/2.49  
% 15.20/2.49  % SZS status Theorem for theBenchmark.p
% 15.20/2.49  
% 15.20/2.49  % SZS output start CNFRefutation for theBenchmark.p
% 15.20/2.49  
% 15.20/2.49  fof(f21,conjecture,(
% 15.20/2.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => r1_tarski(k2_tops_1(X0,X1),X1))))),
% 15.20/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.20/2.49  
% 15.20/2.49  fof(f22,negated_conjecture,(
% 15.20/2.49    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => r1_tarski(k2_tops_1(X0,X1),X1))))),
% 15.20/2.49    inference(negated_conjecture,[],[f21])).
% 15.20/2.49  
% 15.20/2.49  fof(f40,plain,(
% 15.20/2.49    ? [X0] : (? [X1] : ((~r1_tarski(k2_tops_1(X0,X1),X1) & v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 15.20/2.49    inference(ennf_transformation,[],[f22])).
% 15.20/2.49  
% 15.20/2.49  fof(f41,plain,(
% 15.20/2.49    ? [X0] : (? [X1] : (~r1_tarski(k2_tops_1(X0,X1),X1) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 15.20/2.49    inference(flattening,[],[f40])).
% 15.20/2.49  
% 15.20/2.49  fof(f45,plain,(
% 15.20/2.49    ( ! [X0] : (? [X1] : (~r1_tarski(k2_tops_1(X0,X1),X1) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~r1_tarski(k2_tops_1(X0,sK1),sK1) & v4_pre_topc(sK1,X0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 15.20/2.49    introduced(choice_axiom,[])).
% 15.20/2.49  
% 15.20/2.49  fof(f44,plain,(
% 15.20/2.49    ? [X0] : (? [X1] : (~r1_tarski(k2_tops_1(X0,X1),X1) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (~r1_tarski(k2_tops_1(sK0,X1),X1) & v4_pre_topc(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 15.20/2.49    introduced(choice_axiom,[])).
% 15.20/2.49  
% 15.20/2.49  fof(f46,plain,(
% 15.20/2.49    (~r1_tarski(k2_tops_1(sK0,sK1),sK1) & v4_pre_topc(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 15.20/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f41,f45,f44])).
% 15.20/2.49  
% 15.20/2.49  fof(f68,plain,(
% 15.20/2.49    l1_pre_topc(sK0)),
% 15.20/2.49    inference(cnf_transformation,[],[f46])).
% 15.20/2.49  
% 15.20/2.49  fof(f18,axiom,(
% 15.20/2.49    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 15.20/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.20/2.49  
% 15.20/2.49  fof(f36,plain,(
% 15.20/2.49    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 15.20/2.49    inference(ennf_transformation,[],[f18])).
% 15.20/2.49  
% 15.20/2.49  fof(f65,plain,(
% 15.20/2.49    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 15.20/2.49    inference(cnf_transformation,[],[f36])).
% 15.20/2.49  
% 15.20/2.49  fof(f16,axiom,(
% 15.20/2.49    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 15.20/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.20/2.49  
% 15.20/2.49  fof(f34,plain,(
% 15.20/2.49    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 15.20/2.49    inference(ennf_transformation,[],[f16])).
% 15.20/2.49  
% 15.20/2.49  fof(f63,plain,(
% 15.20/2.49    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 15.20/2.49    inference(cnf_transformation,[],[f34])).
% 15.20/2.49  
% 15.20/2.49  fof(f69,plain,(
% 15.20/2.49    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 15.20/2.49    inference(cnf_transformation,[],[f46])).
% 15.20/2.49  
% 15.20/2.49  fof(f14,axiom,(
% 15.20/2.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 15.20/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.20/2.49  
% 15.20/2.49  fof(f43,plain,(
% 15.20/2.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 15.20/2.49    inference(nnf_transformation,[],[f14])).
% 15.20/2.49  
% 15.20/2.49  fof(f61,plain,(
% 15.20/2.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 15.20/2.49    inference(cnf_transformation,[],[f43])).
% 15.20/2.49  
% 15.20/2.49  fof(f6,axiom,(
% 15.20/2.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1))),
% 15.20/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.20/2.49  
% 15.20/2.49  fof(f26,plain,(
% 15.20/2.49    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 15.20/2.49    inference(ennf_transformation,[],[f6])).
% 15.20/2.49  
% 15.20/2.49  fof(f53,plain,(
% 15.20/2.49    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 15.20/2.49    inference(cnf_transformation,[],[f26])).
% 15.20/2.49  
% 15.20/2.49  fof(f62,plain,(
% 15.20/2.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 15.20/2.49    inference(cnf_transformation,[],[f43])).
% 15.20/2.49  
% 15.20/2.49  fof(f11,axiom,(
% 15.20/2.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 15.20/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.20/2.49  
% 15.20/2.49  fof(f32,plain,(
% 15.20/2.49    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 15.20/2.49    inference(ennf_transformation,[],[f11])).
% 15.20/2.49  
% 15.20/2.49  fof(f58,plain,(
% 15.20/2.49    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 15.20/2.49    inference(cnf_transformation,[],[f32])).
% 15.20/2.49  
% 15.20/2.49  fof(f20,axiom,(
% 15.20/2.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k2_tops_1(X0,X1)))),
% 15.20/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.20/2.49  
% 15.20/2.49  fof(f39,plain,(
% 15.20/2.49    ! [X0] : (! [X1] : (k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 15.20/2.49    inference(ennf_transformation,[],[f20])).
% 15.20/2.49  
% 15.20/2.49  fof(f67,plain,(
% 15.20/2.49    ( ! [X0,X1] : (k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 15.20/2.49    inference(cnf_transformation,[],[f39])).
% 15.20/2.49  
% 15.20/2.49  fof(f7,axiom,(
% 15.20/2.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 15.20/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.20/2.49  
% 15.20/2.49  fof(f27,plain,(
% 15.20/2.49    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 15.20/2.49    inference(ennf_transformation,[],[f7])).
% 15.20/2.49  
% 15.20/2.49  fof(f54,plain,(
% 15.20/2.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 15.20/2.49    inference(cnf_transformation,[],[f27])).
% 15.20/2.49  
% 15.20/2.49  fof(f19,axiom,(
% 15.20/2.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 15.20/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.20/2.49  
% 15.20/2.49  fof(f23,plain,(
% 15.20/2.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1)))),
% 15.20/2.49    inference(pure_predicate_removal,[],[f19])).
% 15.20/2.49  
% 15.20/2.49  fof(f37,plain,(
% 15.20/2.49    ! [X0] : (! [X1] : ((k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 15.20/2.49    inference(ennf_transformation,[],[f23])).
% 15.20/2.49  
% 15.20/2.49  fof(f38,plain,(
% 15.20/2.49    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 15.20/2.49    inference(flattening,[],[f37])).
% 15.20/2.49  
% 15.20/2.49  fof(f66,plain,(
% 15.20/2.49    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 15.20/2.49    inference(cnf_transformation,[],[f38])).
% 15.20/2.49  
% 15.20/2.49  fof(f70,plain,(
% 15.20/2.49    v4_pre_topc(sK1,sK0)),
% 15.20/2.49    inference(cnf_transformation,[],[f46])).
% 15.20/2.49  
% 15.20/2.49  fof(f13,axiom,(
% 15.20/2.49    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 15.20/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.20/2.49  
% 15.20/2.49  fof(f60,plain,(
% 15.20/2.49    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 15.20/2.49    inference(cnf_transformation,[],[f13])).
% 15.20/2.49  
% 15.20/2.49  fof(f9,axiom,(
% 15.20/2.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 15.20/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.20/2.49  
% 15.20/2.49  fof(f29,plain,(
% 15.20/2.49    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 15.20/2.49    inference(ennf_transformation,[],[f9])).
% 15.20/2.49  
% 15.20/2.49  fof(f30,plain,(
% 15.20/2.49    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 15.20/2.49    inference(flattening,[],[f29])).
% 15.20/2.49  
% 15.20/2.49  fof(f56,plain,(
% 15.20/2.49    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 15.20/2.49    inference(cnf_transformation,[],[f30])).
% 15.20/2.49  
% 15.20/2.49  fof(f17,axiom,(
% 15.20/2.49    ! [X0] : (l1_struct_0(X0) => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))))),
% 15.20/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.20/2.49  
% 15.20/2.49  fof(f35,plain,(
% 15.20/2.49    ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0))),
% 15.20/2.49    inference(ennf_transformation,[],[f17])).
% 15.20/2.49  
% 15.20/2.49  fof(f64,plain,(
% 15.20/2.49    ( ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0)) )),
% 15.20/2.49    inference(cnf_transformation,[],[f35])).
% 15.20/2.49  
% 15.20/2.49  fof(f10,axiom,(
% 15.20/2.49    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 15.20/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.20/2.49  
% 15.20/2.49  fof(f31,plain,(
% 15.20/2.49    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 15.20/2.49    inference(ennf_transformation,[],[f10])).
% 15.20/2.49  
% 15.20/2.49  fof(f57,plain,(
% 15.20/2.49    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 15.20/2.49    inference(cnf_transformation,[],[f31])).
% 15.20/2.49  
% 15.20/2.49  fof(f1,axiom,(
% 15.20/2.49    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 15.20/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.20/2.49  
% 15.20/2.49  fof(f25,plain,(
% 15.20/2.49    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 15.20/2.49    inference(ennf_transformation,[],[f1])).
% 15.20/2.49  
% 15.20/2.49  fof(f47,plain,(
% 15.20/2.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 15.20/2.49    inference(cnf_transformation,[],[f25])).
% 15.20/2.49  
% 15.20/2.49  fof(f5,axiom,(
% 15.20/2.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 15.20/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.20/2.49  
% 15.20/2.49  fof(f52,plain,(
% 15.20/2.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 15.20/2.49    inference(cnf_transformation,[],[f5])).
% 15.20/2.49  
% 15.20/2.49  fof(f4,axiom,(
% 15.20/2.49    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 15.20/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.20/2.49  
% 15.20/2.49  fof(f42,plain,(
% 15.20/2.49    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 15.20/2.49    inference(nnf_transformation,[],[f4])).
% 15.20/2.49  
% 15.20/2.49  fof(f51,plain,(
% 15.20/2.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 15.20/2.49    inference(cnf_transformation,[],[f42])).
% 15.20/2.49  
% 15.20/2.49  fof(f12,axiom,(
% 15.20/2.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)))),
% 15.20/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.20/2.49  
% 15.20/2.49  fof(f33,plain,(
% 15.20/2.49    ! [X0,X1] : (! [X2] : (k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 15.20/2.49    inference(ennf_transformation,[],[f12])).
% 15.20/2.49  
% 15.20/2.49  fof(f59,plain,(
% 15.20/2.49    ( ! [X2,X0,X1] : (k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 15.20/2.49    inference(cnf_transformation,[],[f33])).
% 15.20/2.49  
% 15.20/2.49  fof(f8,axiom,(
% 15.20/2.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 15.20/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.20/2.49  
% 15.20/2.49  fof(f28,plain,(
% 15.20/2.49    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 15.20/2.49    inference(ennf_transformation,[],[f8])).
% 15.20/2.49  
% 15.20/2.49  fof(f55,plain,(
% 15.20/2.49    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 15.20/2.49    inference(cnf_transformation,[],[f28])).
% 15.20/2.49  
% 15.20/2.49  fof(f2,axiom,(
% 15.20/2.49    ! [X0,X1,X2] : k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2))),
% 15.20/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.20/2.49  
% 15.20/2.49  fof(f48,plain,(
% 15.20/2.49    ( ! [X2,X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 15.20/2.49    inference(cnf_transformation,[],[f2])).
% 15.20/2.49  
% 15.20/2.49  fof(f3,axiom,(
% 15.20/2.49    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))),
% 15.20/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.20/2.49  
% 15.20/2.49  fof(f49,plain,(
% 15.20/2.49    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))) )),
% 15.20/2.49    inference(cnf_transformation,[],[f3])).
% 15.20/2.49  
% 15.20/2.49  fof(f50,plain,(
% 15.20/2.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 15.20/2.49    inference(cnf_transformation,[],[f42])).
% 15.20/2.49  
% 15.20/2.49  fof(f71,plain,(
% 15.20/2.49    ~r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 15.20/2.49    inference(cnf_transformation,[],[f46])).
% 15.20/2.49  
% 15.20/2.49  cnf(c_24,negated_conjecture,
% 15.20/2.49      ( l1_pre_topc(sK0) ),
% 15.20/2.49      inference(cnf_transformation,[],[f68]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_857,plain,
% 15.20/2.49      ( l1_pre_topc(sK0) = iProver_top ),
% 15.20/2.49      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_18,plain,
% 15.20/2.49      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 15.20/2.49      inference(cnf_transformation,[],[f65]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_863,plain,
% 15.20/2.49      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 15.20/2.49      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_1206,plain,
% 15.20/2.49      ( l1_struct_0(sK0) = iProver_top ),
% 15.20/2.49      inference(superposition,[status(thm)],[c_857,c_863]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_16,plain,
% 15.20/2.49      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 15.20/2.49      inference(cnf_transformation,[],[f63]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_865,plain,
% 15.20/2.49      ( u1_struct_0(X0) = k2_struct_0(X0)
% 15.20/2.49      | l1_struct_0(X0) != iProver_top ),
% 15.20/2.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_1478,plain,
% 15.20/2.49      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 15.20/2.49      inference(superposition,[status(thm)],[c_1206,c_865]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_23,negated_conjecture,
% 15.20/2.49      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 15.20/2.49      inference(cnf_transformation,[],[f69]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_858,plain,
% 15.20/2.49      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 15.20/2.49      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_1747,plain,
% 15.20/2.49      ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
% 15.20/2.49      inference(demodulation,[status(thm)],[c_1478,c_858]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_15,plain,
% 15.20/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 15.20/2.49      inference(cnf_transformation,[],[f61]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_866,plain,
% 15.20/2.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 15.20/2.49      | r1_tarski(X0,X1) = iProver_top ),
% 15.20/2.49      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_2040,plain,
% 15.20/2.49      ( r1_tarski(sK1,k2_struct_0(sK0)) = iProver_top ),
% 15.20/2.49      inference(superposition,[status(thm)],[c_1747,c_866]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_6,plain,
% 15.20/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.20/2.49      | k9_subset_1(X1,X0,X2) = k9_subset_1(X1,X2,X0) ),
% 15.20/2.49      inference(cnf_transformation,[],[f53]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_14,plain,
% 15.20/2.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 15.20/2.49      inference(cnf_transformation,[],[f62]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_176,plain,
% 15.20/2.49      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 15.20/2.49      inference(prop_impl,[status(thm)],[c_14]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_177,plain,
% 15.20/2.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 15.20/2.49      inference(renaming,[status(thm)],[c_176]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_213,plain,
% 15.20/2.49      ( ~ r1_tarski(X0,X1)
% 15.20/2.49      | k9_subset_1(X1,X0,X2) = k9_subset_1(X1,X2,X0) ),
% 15.20/2.49      inference(bin_hyper_res,[status(thm)],[c_6,c_177]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_856,plain,
% 15.20/2.49      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
% 15.20/2.49      | r1_tarski(X1,X0) != iProver_top ),
% 15.20/2.49      inference(predicate_to_equality,[status(thm)],[c_213]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_10626,plain,
% 15.20/2.49      ( k9_subset_1(k2_struct_0(sK0),sK1,X0) = k9_subset_1(k2_struct_0(sK0),X0,sK1) ),
% 15.20/2.49      inference(superposition,[status(thm)],[c_2040,c_856]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_11,plain,
% 15.20/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.20/2.49      | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 15.20/2.49      inference(cnf_transformation,[],[f58]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_218,plain,
% 15.20/2.49      ( ~ r1_tarski(X0,X1) | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 15.20/2.49      inference(bin_hyper_res,[status(thm)],[c_11,c_177]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_851,plain,
% 15.20/2.49      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
% 15.20/2.49      | r1_tarski(X2,X0) != iProver_top ),
% 15.20/2.49      inference(predicate_to_equality,[status(thm)],[c_218]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_2598,plain,
% 15.20/2.49      ( k9_subset_1(k2_struct_0(sK0),X0,sK1) = k3_xboole_0(X0,sK1) ),
% 15.20/2.49      inference(superposition,[status(thm)],[c_2040,c_851]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_10649,plain,
% 15.20/2.49      ( k9_subset_1(k2_struct_0(sK0),sK1,X0) = k3_xboole_0(X0,sK1) ),
% 15.20/2.49      inference(light_normalisation,[status(thm)],[c_10626,c_2598]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_20,plain,
% 15.20/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.20/2.49      | ~ l1_pre_topc(X1)
% 15.20/2.49      | k9_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k2_tops_1(X1,X0) ),
% 15.20/2.49      inference(cnf_transformation,[],[f67]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_861,plain,
% 15.20/2.49      ( k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k2_tops_1(X0,X1)
% 15.20/2.49      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 15.20/2.49      | l1_pre_topc(X0) != iProver_top ),
% 15.20/2.49      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_13017,plain,
% 15.20/2.49      ( k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k2_tops_1(sK0,X0)
% 15.20/2.49      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 15.20/2.49      | l1_pre_topc(sK0) != iProver_top ),
% 15.20/2.49      inference(superposition,[status(thm)],[c_1478,c_861]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_13021,plain,
% 15.20/2.49      ( k9_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,X0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) = k2_tops_1(sK0,X0)
% 15.20/2.49      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 15.20/2.49      | l1_pre_topc(sK0) != iProver_top ),
% 15.20/2.49      inference(light_normalisation,[status(thm)],[c_13017,c_1478]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_25,plain,
% 15.20/2.49      ( l1_pre_topc(sK0) = iProver_top ),
% 15.20/2.49      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_14083,plain,
% 15.20/2.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 15.20/2.49      | k9_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,X0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) = k2_tops_1(sK0,X0) ),
% 15.20/2.49      inference(global_propositional_subsumption,
% 15.20/2.49                [status(thm)],
% 15.20/2.49                [c_13021,c_25]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_14084,plain,
% 15.20/2.49      ( k9_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,X0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) = k2_tops_1(sK0,X0)
% 15.20/2.49      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 15.20/2.49      inference(renaming,[status(thm)],[c_14083]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_14093,plain,
% 15.20/2.49      ( k9_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))) = k2_tops_1(sK0,sK1) ),
% 15.20/2.49      inference(superposition,[status(thm)],[c_1747,c_14084]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_7,plain,
% 15.20/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.20/2.49      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 15.20/2.49      inference(cnf_transformation,[],[f54]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_214,plain,
% 15.20/2.49      ( ~ r1_tarski(X0,X1) | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 15.20/2.49      inference(bin_hyper_res,[status(thm)],[c_7,c_177]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_855,plain,
% 15.20/2.49      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
% 15.20/2.49      | r1_tarski(X1,X0) != iProver_top ),
% 15.20/2.49      inference(predicate_to_equality,[status(thm)],[c_214]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_9022,plain,
% 15.20/2.49      ( k3_subset_1(k2_struct_0(sK0),sK1) = k4_xboole_0(k2_struct_0(sK0),sK1) ),
% 15.20/2.49      inference(superposition,[status(thm)],[c_2040,c_855]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_19,plain,
% 15.20/2.49      ( ~ v4_pre_topc(X0,X1)
% 15.20/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.20/2.49      | ~ l1_pre_topc(X1)
% 15.20/2.49      | k2_pre_topc(X1,X0) = X0 ),
% 15.20/2.49      inference(cnf_transformation,[],[f66]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_862,plain,
% 15.20/2.49      ( k2_pre_topc(X0,X1) = X1
% 15.20/2.49      | v4_pre_topc(X1,X0) != iProver_top
% 15.20/2.49      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 15.20/2.49      | l1_pre_topc(X0) != iProver_top ),
% 15.20/2.49      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_10942,plain,
% 15.20/2.49      ( k2_pre_topc(sK0,X0) = X0
% 15.20/2.49      | v4_pre_topc(X0,sK0) != iProver_top
% 15.20/2.49      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 15.20/2.49      | l1_pre_topc(sK0) != iProver_top ),
% 15.20/2.49      inference(superposition,[status(thm)],[c_1478,c_862]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_11856,plain,
% 15.20/2.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 15.20/2.49      | v4_pre_topc(X0,sK0) != iProver_top
% 15.20/2.49      | k2_pre_topc(sK0,X0) = X0 ),
% 15.20/2.49      inference(global_propositional_subsumption,
% 15.20/2.49                [status(thm)],
% 15.20/2.49                [c_10942,c_25]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_11857,plain,
% 15.20/2.49      ( k2_pre_topc(sK0,X0) = X0
% 15.20/2.49      | v4_pre_topc(X0,sK0) != iProver_top
% 15.20/2.49      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 15.20/2.49      inference(renaming,[status(thm)],[c_11856]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_11867,plain,
% 15.20/2.49      ( k2_pre_topc(sK0,sK1) = sK1
% 15.20/2.49      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 15.20/2.49      inference(superposition,[status(thm)],[c_1747,c_11857]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_22,negated_conjecture,
% 15.20/2.49      ( v4_pre_topc(sK1,sK0) ),
% 15.20/2.49      inference(cnf_transformation,[],[f70]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_1128,plain,
% 15.20/2.49      ( ~ v4_pre_topc(sK1,sK0)
% 15.20/2.49      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.20/2.49      | ~ l1_pre_topc(sK0)
% 15.20/2.49      | k2_pre_topc(sK0,sK1) = sK1 ),
% 15.20/2.49      inference(instantiation,[status(thm)],[c_19]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_11894,plain,
% 15.20/2.49      ( k2_pre_topc(sK0,sK1) = sK1 ),
% 15.20/2.49      inference(global_propositional_subsumption,
% 15.20/2.49                [status(thm)],
% 15.20/2.49                [c_11867,c_24,c_23,c_22,c_1128]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_14099,plain,
% 15.20/2.49      ( k9_subset_1(k2_struct_0(sK0),sK1,k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1))) = k2_tops_1(sK0,sK1) ),
% 15.20/2.49      inference(light_normalisation,
% 15.20/2.49                [status(thm)],
% 15.20/2.49                [c_14093,c_9022,c_11894]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_14345,plain,
% 15.20/2.49      ( k3_xboole_0(k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)),sK1) = k2_tops_1(sK0,sK1) ),
% 15.20/2.49      inference(superposition,[status(thm)],[c_10649,c_14099]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_13,plain,
% 15.20/2.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 15.20/2.49      inference(cnf_transformation,[],[f60]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_868,plain,
% 15.20/2.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 15.20/2.49      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_9,plain,
% 15.20/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.20/2.49      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 15.20/2.49      | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
% 15.20/2.49      inference(cnf_transformation,[],[f56]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_216,plain,
% 15.20/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.20/2.49      | ~ r1_tarski(X2,X1)
% 15.20/2.49      | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
% 15.20/2.49      inference(bin_hyper_res,[status(thm)],[c_9,c_177]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_853,plain,
% 15.20/2.49      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
% 15.20/2.49      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 15.20/2.49      | r1_tarski(X2,X0) != iProver_top ),
% 15.20/2.49      inference(predicate_to_equality,[status(thm)],[c_216]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_5034,plain,
% 15.20/2.49      ( k4_subset_1(X0,k1_xboole_0,X1) = k2_xboole_0(k1_xboole_0,X1)
% 15.20/2.49      | r1_tarski(X1,X0) != iProver_top ),
% 15.20/2.49      inference(superposition,[status(thm)],[c_868,c_853]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_47627,plain,
% 15.20/2.49      ( k4_subset_1(k2_struct_0(sK0),k1_xboole_0,sK1) = k2_xboole_0(k1_xboole_0,sK1) ),
% 15.20/2.49      inference(superposition,[status(thm)],[c_2040,c_5034]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_17,plain,
% 15.20/2.49      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 15.20/2.49      | ~ l1_struct_0(X0) ),
% 15.20/2.49      inference(cnf_transformation,[],[f64]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_864,plain,
% 15.20/2.49      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 15.20/2.49      | l1_struct_0(X0) != iProver_top ),
% 15.20/2.49      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_2180,plain,
% 15.20/2.49      ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
% 15.20/2.49      | l1_struct_0(sK0) != iProver_top ),
% 15.20/2.49      inference(superposition,[status(thm)],[c_1478,c_864]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_35,plain,
% 15.20/2.49      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 15.20/2.49      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_37,plain,
% 15.20/2.49      ( l1_pre_topc(sK0) != iProver_top
% 15.20/2.49      | l1_struct_0(sK0) = iProver_top ),
% 15.20/2.49      inference(instantiation,[status(thm)],[c_35]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_2924,plain,
% 15.20/2.49      ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
% 15.20/2.49      inference(global_propositional_subsumption,
% 15.20/2.49                [status(thm)],
% 15.20/2.49                [c_2180,c_25,c_37]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_2929,plain,
% 15.20/2.49      ( r1_tarski(k2_struct_0(sK0),k2_struct_0(sK0)) = iProver_top ),
% 15.20/2.49      inference(superposition,[status(thm)],[c_2924,c_866]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_10,plain,
% 15.20/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.20/2.49      | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 15.20/2.49      inference(cnf_transformation,[],[f57]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_217,plain,
% 15.20/2.49      ( ~ r1_tarski(X0,X1) | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 15.20/2.49      inference(bin_hyper_res,[status(thm)],[c_10,c_177]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_852,plain,
% 15.20/2.49      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
% 15.20/2.49      | r1_tarski(X1,X0) != iProver_top ),
% 15.20/2.49      inference(predicate_to_equality,[status(thm)],[c_217]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_3664,plain,
% 15.20/2.49      ( k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),X0) = k4_xboole_0(k2_struct_0(sK0),X0) ),
% 15.20/2.49      inference(superposition,[status(thm)],[c_2929,c_852]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_9026,plain,
% 15.20/2.49      ( k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)) = k4_xboole_0(k2_struct_0(sK0),k2_struct_0(sK0)) ),
% 15.20/2.49      inference(superposition,[status(thm)],[c_2929,c_855]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_0,plain,
% 15.20/2.49      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 15.20/2.49      inference(cnf_transformation,[],[f47]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_872,plain,
% 15.20/2.49      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 15.20/2.49      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_2596,plain,
% 15.20/2.49      ( k2_xboole_0(sK1,k2_struct_0(sK0)) = k2_struct_0(sK0) ),
% 15.20/2.49      inference(superposition,[status(thm)],[c_2040,c_872]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_5,plain,
% 15.20/2.49      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 15.20/2.49      inference(cnf_transformation,[],[f52]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_2762,plain,
% 15.20/2.49      ( k4_xboole_0(k2_struct_0(sK0),k2_struct_0(sK0)) = k4_xboole_0(sK1,k2_struct_0(sK0)) ),
% 15.20/2.49      inference(superposition,[status(thm)],[c_2596,c_5]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_3,plain,
% 15.20/2.49      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 15.20/2.49      inference(cnf_transformation,[],[f51]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_870,plain,
% 15.20/2.49      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 15.20/2.49      | r1_tarski(X0,X1) != iProver_top ),
% 15.20/2.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_2597,plain,
% 15.20/2.49      ( k4_xboole_0(sK1,k2_struct_0(sK0)) = k1_xboole_0 ),
% 15.20/2.49      inference(superposition,[status(thm)],[c_2040,c_870]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_2776,plain,
% 15.20/2.49      ( k4_xboole_0(k2_struct_0(sK0),k2_struct_0(sK0)) = k1_xboole_0 ),
% 15.20/2.49      inference(light_normalisation,[status(thm)],[c_2762,c_2597]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_9037,plain,
% 15.20/2.49      ( k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)) = k1_xboole_0 ),
% 15.20/2.49      inference(light_normalisation,[status(thm)],[c_9026,c_2776]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_12,plain,
% 15.20/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.20/2.49      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 15.20/2.49      | k4_subset_1(X1,k3_subset_1(X1,X2),X0) = k3_subset_1(X1,k7_subset_1(X1,X2,X0)) ),
% 15.20/2.49      inference(cnf_transformation,[],[f59]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_219,plain,
% 15.20/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.20/2.49      | ~ r1_tarski(X2,X1)
% 15.20/2.49      | k4_subset_1(X1,k3_subset_1(X1,X0),X2) = k3_subset_1(X1,k7_subset_1(X1,X0,X2)) ),
% 15.20/2.49      inference(bin_hyper_res,[status(thm)],[c_12,c_177]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_850,plain,
% 15.20/2.49      ( k4_subset_1(X0,k3_subset_1(X0,X1),X2) = k3_subset_1(X0,k7_subset_1(X0,X1,X2))
% 15.20/2.49      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 15.20/2.49      | r1_tarski(X2,X0) != iProver_top ),
% 15.20/2.49      inference(predicate_to_equality,[status(thm)],[c_219]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_2930,plain,
% 15.20/2.49      ( k4_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)),X0) = k3_subset_1(k2_struct_0(sK0),k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),X0))
% 15.20/2.49      | r1_tarski(X0,k2_struct_0(sK0)) != iProver_top ),
% 15.20/2.49      inference(superposition,[status(thm)],[c_2924,c_850]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_8873,plain,
% 15.20/2.49      ( k4_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)),sK1) = k3_subset_1(k2_struct_0(sK0),k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1)) ),
% 15.20/2.49      inference(superposition,[status(thm)],[c_2040,c_2930]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_10610,plain,
% 15.20/2.49      ( k3_subset_1(k2_struct_0(sK0),k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1)) = k4_subset_1(k2_struct_0(sK0),k1_xboole_0,sK1) ),
% 15.20/2.49      inference(demodulation,[status(thm)],[c_9037,c_8873]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_18024,plain,
% 15.20/2.49      ( k3_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1)) = k4_subset_1(k2_struct_0(sK0),k1_xboole_0,sK1) ),
% 15.20/2.49      inference(demodulation,[status(thm)],[c_3664,c_10610]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_8,plain,
% 15.20/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.20/2.49      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 15.20/2.49      inference(cnf_transformation,[],[f55]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_215,plain,
% 15.20/2.49      ( ~ r1_tarski(X0,X1) | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 15.20/2.49      inference(bin_hyper_res,[status(thm)],[c_8,c_177]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_854,plain,
% 15.20/2.49      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 15.20/2.49      | r1_tarski(X1,X0) != iProver_top ),
% 15.20/2.49      inference(predicate_to_equality,[status(thm)],[c_215]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_7199,plain,
% 15.20/2.49      ( k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1)) = sK1 ),
% 15.20/2.49      inference(superposition,[status(thm)],[c_2040,c_854]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_9855,plain,
% 15.20/2.49      ( k3_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1)) = sK1 ),
% 15.20/2.49      inference(demodulation,[status(thm)],[c_9022,c_7199]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_18025,plain,
% 15.20/2.49      ( k4_subset_1(k2_struct_0(sK0),k1_xboole_0,sK1) = sK1 ),
% 15.20/2.49      inference(light_normalisation,[status(thm)],[c_18024,c_9855]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_47750,plain,
% 15.20/2.49      ( k2_xboole_0(k1_xboole_0,sK1) = sK1 ),
% 15.20/2.49      inference(light_normalisation,[status(thm)],[c_47627,c_18025]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_1,plain,
% 15.20/2.49      ( k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 15.20/2.49      inference(cnf_transformation,[],[f48]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_2,plain,
% 15.20/2.49      ( r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
% 15.20/2.49      inference(cnf_transformation,[],[f49]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_871,plain,
% 15.20/2.49      ( r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) = iProver_top ),
% 15.20/2.49      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_916,plain,
% 15.20/2.49      ( r1_tarski(k3_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X1,X2)) = iProver_top ),
% 15.20/2.49      inference(demodulation,[status(thm)],[c_1,c_871]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_1846,plain,
% 15.20/2.49      ( k4_xboole_0(k3_xboole_0(X0,k2_xboole_0(X1,X2)),k2_xboole_0(X1,X2)) = k1_xboole_0 ),
% 15.20/2.49      inference(superposition,[status(thm)],[c_916,c_870]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_48522,plain,
% 15.20/2.49      ( k4_xboole_0(k3_xboole_0(X0,sK1),sK1) = k1_xboole_0 ),
% 15.20/2.49      inference(superposition,[status(thm)],[c_47750,c_1846]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_49241,plain,
% 15.20/2.49      ( k4_xboole_0(k2_tops_1(sK0,sK1),sK1) = k1_xboole_0 ),
% 15.20/2.49      inference(superposition,[status(thm)],[c_14345,c_48522]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_4,plain,
% 15.20/2.49      ( r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0 ),
% 15.20/2.49      inference(cnf_transformation,[],[f50]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_18350,plain,
% 15.20/2.49      ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
% 15.20/2.49      | k4_xboole_0(k2_tops_1(sK0,sK1),sK1) != k1_xboole_0 ),
% 15.20/2.49      inference(instantiation,[status(thm)],[c_4]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_21,negated_conjecture,
% 15.20/2.49      ( ~ r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
% 15.20/2.49      inference(cnf_transformation,[],[f71]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(contradiction,plain,
% 15.20/2.49      ( $false ),
% 15.20/2.49      inference(minisat,[status(thm)],[c_49241,c_18350,c_21]) ).
% 15.20/2.49  
% 15.20/2.49  
% 15.20/2.49  % SZS output end CNFRefutation for theBenchmark.p
% 15.20/2.49  
% 15.20/2.49  ------                               Statistics
% 15.20/2.49  
% 15.20/2.49  ------ Selected
% 15.20/2.49  
% 15.20/2.49  total_time:                             1.566
% 15.20/2.49  
%------------------------------------------------------------------------------
