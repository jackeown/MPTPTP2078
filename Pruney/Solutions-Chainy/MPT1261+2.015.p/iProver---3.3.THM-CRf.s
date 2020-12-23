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
% DateTime   : Thu Dec  3 12:14:27 EST 2020

% Result     : Theorem 34.91s
% Output     : CNFRefutation 34.91s
% Verified   : 
% Statistics : Number of formulae       :  201 (6770 expanded)
%              Number of clauses        :  131 (1565 expanded)
%              Number of leaves         :   21 (2274 expanded)
%              Depth                    :   38
%              Number of atoms          :  451 (8857 expanded)
%              Number of equality atoms :  215 (7016 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    9 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

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
    inference(nnf_transformation,[],[f32])).

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

fof(f61,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f60,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f39])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X2,X1)
                  & v4_pre_topc(X1,X0) )
               => r1_tarski(k2_pre_topc(X0,X2),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X2),X1)
              | ~ r1_tarski(X2,X1)
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X2),X1)
              | ~ r1_tarski(X2,X1)
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_pre_topc(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f59,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f33])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f69,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f41])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f42,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f63,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f43,f51])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f50,f63])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f64,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,k1_setfam_1(k2_tarski(X0,X1)))) = X0 ),
    inference(definition_unfolding,[],[f44,f48,f51])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f66,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(k5_xboole_0(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))) ),
    inference(definition_unfolding,[],[f46,f48,f48,f51])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f65,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) ),
    inference(definition_unfolding,[],[f45,f48,f48,f48])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k2_tarski(X1,X2)) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f49,f48])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f58,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f70,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f40])).

fof(f62,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_16,negated_conjecture,
    ( v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_999,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_998,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_13,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | r1_tarski(k2_pre_topc(X1,X2),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_18,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_261,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | r1_tarski(k2_pre_topc(X1,X2),X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_18])).

cnf(c_262,plain,
    ( ~ v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X1,X0)
    | r1_tarski(k2_pre_topc(sK0,X1),X0) ),
    inference(unflattening,[status(thm)],[c_261])).

cnf(c_995,plain,
    ( v4_pre_topc(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_262])).

cnf(c_1692,plain,
    ( v4_pre_topc(sK1,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,X0),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_998,c_995])).

cnf(c_1701,plain,
    ( v4_pre_topc(sK1,sK0) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,sK1),sK1) = iProver_top
    | r1_tarski(sK1,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_998,c_1692])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1375,plain,
    ( r1_tarski(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1376,plain,
    ( r1_tarski(sK1,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1375])).

cnf(c_1786,plain,
    ( r1_tarski(k2_pre_topc(sK0,sK1),sK1) = iProver_top
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1701,c_1376])).

cnf(c_1787,plain,
    ( v4_pre_topc(sK1,sK0) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,sK1),sK1) = iProver_top ),
    inference(renaming,[status(thm)],[c_1786])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_306,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,X0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_18])).

cnf(c_307,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(X0,k2_pre_topc(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_306])).

cnf(c_992,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_307])).

cnf(c_1113,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_998,c_992])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1004,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4036,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | r1_tarski(k2_pre_topc(sK0,sK1),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1113,c_1004])).

cnf(c_4240,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1787,c_4036])).

cnf(c_4243,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_999,c_4240])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2))) = k7_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1001,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X2,X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1841,plain,
    ( k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0))) = k7_subset_1(u1_struct_0(sK0),sK1,X0) ),
    inference(superposition,[status(thm)],[c_998,c_1001])).

cnf(c_6,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_3,plain,
    ( k3_tarski(k2_tarski(X0,k1_setfam_1(k2_tarski(X0,X1)))) = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_5,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_4,plain,
    ( k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1432,plain,
    ( k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X1,X0)))) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(superposition,[status(thm)],[c_6,c_4])).

cnf(c_2064,plain,
    ( k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),k5_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_5,c_1432])).

cnf(c_5516,plain,
    ( k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X1,X0)),k5_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_6,c_2064])).

cnf(c_5644,plain,
    ( k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),k5_xboole_0(X0,X1))),k5_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),k5_xboole_0(X0,X1)))) = k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(k5_xboole_0(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))),k3_tarski(k2_tarski(X0,X1)))) ),
    inference(superposition,[status(thm)],[c_5,c_5516])).

cnf(c_5494,plain,
    ( k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(k5_xboole_0(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))),k5_xboole_0(k5_xboole_0(X0,X1),k1_setfam_1(k2_tarski(X0,X1))))) = k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(k5_xboole_0(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))),k3_tarski(k2_tarski(X0,X1)))) ),
    inference(superposition,[status(thm)],[c_5,c_2064])).

cnf(c_5643,plain,
    ( k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X0)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0))) = k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))),k3_tarski(k2_tarski(X0,X1)))) ),
    inference(superposition,[status(thm)],[c_4,c_5516])).

cnf(c_1519,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(X0,X1),k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(k5_xboole_0(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))) ),
    inference(superposition,[status(thm)],[c_5,c_4])).

cnf(c_1520,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(X0,X1),k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_1519,c_5])).

cnf(c_3054,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(X0,k3_tarski(k2_tarski(X0,X1))),k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) ),
    inference(superposition,[status(thm)],[c_4,c_1520])).

cnf(c_3072,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(X0,k3_tarski(k2_tarski(X0,X1))),k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_3054,c_4])).

cnf(c_4086,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(X0,k3_tarski(k2_tarski(X1,X0))),k3_tarski(k2_tarski(X1,X0)))) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(superposition,[status(thm)],[c_6,c_3072])).

cnf(c_4574,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1))),k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),k5_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_5,c_4086])).

cnf(c_9974,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(k1_setfam_1(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))),k3_tarski(k2_tarski(X0,X1))),k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))),k5_xboole_0(X0,k3_tarski(k2_tarski(X0,X1))))) ),
    inference(superposition,[status(thm)],[c_4,c_4574])).

cnf(c_5493,plain,
    ( k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))),k5_xboole_0(X0,k3_tarski(k2_tarski(X0,X1))))) = k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))),k3_tarski(k2_tarski(X0,X1)))) ),
    inference(superposition,[status(thm)],[c_4,c_2064])).

cnf(c_10103,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(k1_setfam_1(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))),k3_tarski(k2_tarski(X0,X1))),k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))),k3_tarski(k2_tarski(X0,X1)))) ),
    inference(light_normalisation,[status(thm)],[c_9974,c_5493])).

cnf(c_3061,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(X0,X1),k3_tarski(k2_tarski(X1,X0)))) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(superposition,[status(thm)],[c_6,c_1520])).

cnf(c_3217,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),X0),X0)) = k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)) ),
    inference(superposition,[status(thm)],[c_3,c_3061])).

cnf(c_4530,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),X1),X1)) = k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X1,X0)),X1)) ),
    inference(superposition,[status(thm)],[c_6,c_3217])).

cnf(c_1429,plain,
    ( k3_tarski(k2_tarski(X0,k1_setfam_1(k2_tarski(X1,X0)))) = X0 ),
    inference(superposition,[status(thm)],[c_6,c_3])).

cnf(c_3220,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),X1),X1)) = k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),X1)) ),
    inference(superposition,[status(thm)],[c_1429,c_3061])).

cnf(c_4528,plain,
    ( k3_tarski(k2_tarski(X0,k5_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),X0))) = k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)) ),
    inference(superposition,[status(thm)],[c_6,c_3217])).

cnf(c_4537,plain,
    ( k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)))) = k3_tarski(k2_tarski(X0,k5_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),X0))) ),
    inference(superposition,[status(thm)],[c_3217,c_1432])).

cnf(c_4538,plain,
    ( k3_tarski(k2_tarski(X0,k5_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),X0))) = X0 ),
    inference(demodulation,[status(thm)],[c_4537,c_3,c_1432])).

cnf(c_4543,plain,
    ( k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)) = X0 ),
    inference(demodulation,[status(thm)],[c_4528,c_4538])).

cnf(c_4627,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),X1),X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_4530,c_3220,c_4543])).

cnf(c_10104,plain,
    ( k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))),k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_10103,c_4627])).

cnf(c_15987,plain,
    ( k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X0)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0))) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_5643,c_5643,c_10104])).

cnf(c_15991,plain,
    ( k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0))) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(superposition,[status(thm)],[c_6,c_15987])).

cnf(c_16415,plain,
    ( k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X0,k3_tarski(k2_tarski(X1,X0)))),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0))) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(superposition,[status(thm)],[c_6,c_15991])).

cnf(c_17023,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k1_setfam_1(k2_tarski(X1,k3_tarski(k2_tarski(X0,X1)))))) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(superposition,[status(thm)],[c_6,c_16415])).

cnf(c_17372,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k1_setfam_1(k2_tarski(X0,X1))),k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)))))) = k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),k5_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_5,c_17023])).

cnf(c_20462,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k1_setfam_1(k2_tarski(k5_xboole_0(X0,X1),k1_setfam_1(k2_tarski(X0,X1))))),k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(k5_xboole_0(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))),k3_tarski(k2_tarski(X0,X1)))))) = k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(k5_xboole_0(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))),k5_xboole_0(k5_xboole_0(X0,X1),k1_setfam_1(k2_tarski(X0,X1))))) ),
    inference(superposition,[status(thm)],[c_5,c_17372])).

cnf(c_20739,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k1_setfam_1(k2_tarski(k5_xboole_0(X0,X1),k1_setfam_1(k2_tarski(X0,X1))))),k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(k5_xboole_0(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))),k3_tarski(k2_tarski(X0,X1)))))) = k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(k5_xboole_0(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))),k3_tarski(k2_tarski(X0,X1)))) ),
    inference(light_normalisation,[status(thm)],[c_20462,c_5494])).

cnf(c_1517,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(X0,X1),k1_setfam_1(k2_tarski(X1,X0)))) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(superposition,[status(thm)],[c_6,c_5])).

cnf(c_20740,plain,
    ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),k1_setfam_1(k2_tarski(k5_xboole_0(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))))) = k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(k5_xboole_0(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))),k3_tarski(k2_tarski(X0,X1)))) ),
    inference(demodulation,[status(thm)],[c_20739,c_1517])).

cnf(c_28481,plain,
    ( k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(k5_xboole_0(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))),k5_xboole_0(k5_xboole_0(X0,X1),k1_setfam_1(k2_tarski(X0,X1))))) = k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),k1_setfam_1(k2_tarski(k5_xboole_0(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))))) ),
    inference(light_normalisation,[status(thm)],[c_5494,c_5494,c_20740])).

cnf(c_28573,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(k1_setfam_1(k2_tarski(k5_xboole_0(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))),k5_xboole_0(k5_xboole_0(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))),k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),k1_setfam_1(k2_tarski(k5_xboole_0(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))))))) = k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(k5_xboole_0(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))),k5_xboole_0(k5_xboole_0(X0,X1),k1_setfam_1(k2_tarski(X0,X1))))) ),
    inference(superposition,[status(thm)],[c_28481,c_1520])).

cnf(c_3219,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),k5_xboole_0(X0,X1)),k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),k5_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_5,c_3061])).

cnf(c_6760,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(k1_setfam_1(k2_tarski(k5_xboole_0(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))),k5_xboole_0(k5_xboole_0(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))),k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(k5_xboole_0(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))),k5_xboole_0(k5_xboole_0(X0,X1),k1_setfam_1(k2_tarski(X0,X1))))) ),
    inference(superposition,[status(thm)],[c_5,c_3219])).

cnf(c_6843,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(k1_setfam_1(k2_tarski(k5_xboole_0(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))),k5_xboole_0(k5_xboole_0(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))),k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(k5_xboole_0(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))),k3_tarski(k2_tarski(X0,X1)))) ),
    inference(light_normalisation,[status(thm)],[c_6760,c_5494])).

cnf(c_28483,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(k5_xboole_0(X0,X1),k1_setfam_1(k2_tarski(X0,X1))),k1_setfam_1(k2_tarski(k5_xboole_0(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))))) = k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),k1_setfam_1(k2_tarski(k5_xboole_0(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))))) ),
    inference(superposition,[status(thm)],[c_6,c_28481])).

cnf(c_28668,plain,
    ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),k1_setfam_1(k2_tarski(k5_xboole_0(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))))) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_28483,c_5])).

cnf(c_28707,plain,
    ( k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(k5_xboole_0(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))),k5_xboole_0(k5_xboole_0(X0,X1),k1_setfam_1(k2_tarski(X0,X1))))) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_28668,c_28481])).

cnf(c_28862,plain,
    ( k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(k5_xboole_0(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))),k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_28573,c_6843,c_28668,c_28707])).

cnf(c_43755,plain,
    ( k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),k5_xboole_0(X0,X1))),k5_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),k5_xboole_0(X0,X1)))) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_5644,c_5644,c_28862])).

cnf(c_43757,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),k5_xboole_0(X0,X1)),k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),k5_xboole_0(X0,X1))))) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(superposition,[status(thm)],[c_6,c_43755])).

cnf(c_44150,plain,
    ( k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),k5_xboole_0(X0,X1))) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(superposition,[status(thm)],[c_43757,c_5])).

cnf(c_44345,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(X0,X1)),k1_setfam_1(k2_tarski(k5_xboole_0(X0,X1),k3_tarski(k2_tarski(X0,X1)))))) = k3_tarski(k2_tarski(k5_xboole_0(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))) ),
    inference(superposition,[status(thm)],[c_44150,c_17023])).

cnf(c_44392,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(X0,X1)),k1_setfam_1(k2_tarski(k5_xboole_0(X0,X1),k3_tarski(k2_tarski(X0,X1)))))) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_44345,c_5])).

cnf(c_49869,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))),k1_setfam_1(k2_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0)))) = k3_tarski(k2_tarski(X0,k1_setfam_1(k2_tarski(X0,X1)))) ),
    inference(superposition,[status(thm)],[c_3,c_44392])).

cnf(c_50222,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))),k1_setfam_1(k2_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0)))) = X0 ),
    inference(light_normalisation,[status(thm)],[c_49869,c_3])).

cnf(c_50524,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))),k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))))) = X0 ),
    inference(superposition,[status(thm)],[c_6,c_50222])).

cnf(c_50687,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0)),k1_setfam_1(k2_tarski(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0))))) = sK1 ),
    inference(superposition,[status(thm)],[c_1841,c_50524])).

cnf(c_51040,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k3_tarski(k2_tarski(k5_xboole_0(sK1,k2_tops_1(sK0,sK1)),k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))))) = sK1 ),
    inference(superposition,[status(thm)],[c_4243,c_50687])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_294,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_18])).

cnf(c_295,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_294])).

cnf(c_993,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_295])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X2,X0) = k3_tarski(k2_tarski(X2,X0)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1002,plain,
    ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_9879,plain,
    ( k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X1)) = k3_tarski(k2_tarski(X0,k2_tops_1(sK0,X1)))
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_993,c_1002])).

cnf(c_13075,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_998,c_9879])).

cnf(c_13113,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
    inference(superposition,[status(thm)],[c_998,c_13075])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_249,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_18])).

cnf(c_250,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_249])).

cnf(c_996,plain,
    ( k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_250])).

cnf(c_1600,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_998,c_996])).

cnf(c_13115,plain,
    ( k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k2_pre_topc(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_13113,c_1600])).

cnf(c_51139,plain,
    ( k2_pre_topc(sK0,sK1) = sK1 ),
    inference(demodulation,[status(thm)],[c_51040,c_5,c_13115])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_282,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_18])).

cnf(c_283,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_282])).

cnf(c_994,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_283])).

cnf(c_1365,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_998,c_994])).

cnf(c_52342,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_51139,c_1365])).

cnf(c_619,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1095,plain,
    ( X0 != X1
    | sK1 != X1
    | sK1 = X0 ),
    inference(instantiation,[status(thm)],[c_619])).

cnf(c_1263,plain,
    ( X0 != sK1
    | sK1 = X0
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1095])).

cnf(c_49403,plain,
    ( k2_pre_topc(sK0,sK1) != sK1
    | sK1 = k2_pre_topc(sK0,sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1263])).

cnf(c_632,plain,
    ( ~ v4_pre_topc(X0,X1)
    | v4_pre_topc(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1027,plain,
    ( ~ v4_pre_topc(X0,X1)
    | v4_pre_topc(sK1,sK0)
    | sK1 != X0
    | sK0 != X1 ),
    inference(instantiation,[status(thm)],[c_632])).

cnf(c_49328,plain,
    ( ~ v4_pre_topc(k2_pre_topc(sK0,sK1),X0)
    | v4_pre_topc(sK1,sK0)
    | sK1 != k2_pre_topc(sK0,sK1)
    | sK0 != X0 ),
    inference(instantiation,[status(thm)],[c_1027])).

cnf(c_49330,plain,
    ( ~ v4_pre_topc(k2_pre_topc(sK0,sK1),sK0)
    | v4_pre_topc(sK1,sK0)
    | sK1 != k2_pre_topc(sK0,sK1)
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_49328])).

cnf(c_1087,plain,
    ( ~ r1_tarski(X0,sK1)
    | ~ r1_tarski(sK1,X0)
    | sK1 = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1242,plain,
    ( ~ r1_tarski(sK1,sK1)
    | sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_1087])).

cnf(c_11,plain,
    ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_19,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_228,plain,
    ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_19])).

cnf(c_229,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_228])).

cnf(c_233,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(k2_pre_topc(sK0,X0),sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_229,c_18])).

cnf(c_234,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(renaming,[status(thm)],[c_233])).

cnf(c_1032,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_234])).

cnf(c_58,plain,
    ( ~ r1_tarski(sK0,sK0)
    | sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_54,plain,
    ( r1_tarski(sK0,sK0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_15,negated_conjecture,
    ( ~ v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f62])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_52342,c_51139,c_49403,c_49330,c_1375,c_1242,c_1032,c_58,c_54,c_15,c_17])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:41:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 34.91/5.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 34.91/5.00  
% 34.91/5.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 34.91/5.00  
% 34.91/5.00  ------  iProver source info
% 34.91/5.00  
% 34.91/5.00  git: date: 2020-06-30 10:37:57 +0100
% 34.91/5.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 34.91/5.00  git: non_committed_changes: false
% 34.91/5.00  git: last_make_outside_of_git: false
% 34.91/5.00  
% 34.91/5.00  ------ 
% 34.91/5.00  
% 34.91/5.00  ------ Input Options
% 34.91/5.00  
% 34.91/5.00  --out_options                           all
% 34.91/5.00  --tptp_safe_out                         true
% 34.91/5.00  --problem_path                          ""
% 34.91/5.00  --include_path                          ""
% 34.91/5.00  --clausifier                            res/vclausify_rel
% 34.91/5.00  --clausifier_options                    ""
% 34.91/5.00  --stdin                                 false
% 34.91/5.00  --stats_out                             all
% 34.91/5.00  
% 34.91/5.00  ------ General Options
% 34.91/5.00  
% 34.91/5.00  --fof                                   false
% 34.91/5.00  --time_out_real                         305.
% 34.91/5.00  --time_out_virtual                      -1.
% 34.91/5.00  --symbol_type_check                     false
% 34.91/5.00  --clausify_out                          false
% 34.91/5.00  --sig_cnt_out                           false
% 34.91/5.00  --trig_cnt_out                          false
% 34.91/5.00  --trig_cnt_out_tolerance                1.
% 34.91/5.00  --trig_cnt_out_sk_spl                   false
% 34.91/5.00  --abstr_cl_out                          false
% 34.91/5.00  
% 34.91/5.00  ------ Global Options
% 34.91/5.00  
% 34.91/5.00  --schedule                              default
% 34.91/5.00  --add_important_lit                     false
% 34.91/5.00  --prop_solver_per_cl                    1000
% 34.91/5.00  --min_unsat_core                        false
% 34.91/5.00  --soft_assumptions                      false
% 34.91/5.00  --soft_lemma_size                       3
% 34.91/5.00  --prop_impl_unit_size                   0
% 34.91/5.00  --prop_impl_unit                        []
% 34.91/5.00  --share_sel_clauses                     true
% 34.91/5.00  --reset_solvers                         false
% 34.91/5.00  --bc_imp_inh                            [conj_cone]
% 34.91/5.00  --conj_cone_tolerance                   3.
% 34.91/5.00  --extra_neg_conj                        none
% 34.91/5.00  --large_theory_mode                     true
% 34.91/5.00  --prolific_symb_bound                   200
% 34.91/5.00  --lt_threshold                          2000
% 34.91/5.00  --clause_weak_htbl                      true
% 34.91/5.00  --gc_record_bc_elim                     false
% 34.91/5.00  
% 34.91/5.00  ------ Preprocessing Options
% 34.91/5.00  
% 34.91/5.00  --preprocessing_flag                    true
% 34.91/5.00  --time_out_prep_mult                    0.1
% 34.91/5.00  --splitting_mode                        input
% 34.91/5.00  --splitting_grd                         true
% 34.91/5.00  --splitting_cvd                         false
% 34.91/5.00  --splitting_cvd_svl                     false
% 34.91/5.00  --splitting_nvd                         32
% 34.91/5.00  --sub_typing                            true
% 34.91/5.00  --prep_gs_sim                           true
% 34.91/5.00  --prep_unflatten                        true
% 34.91/5.00  --prep_res_sim                          true
% 34.91/5.00  --prep_upred                            true
% 34.91/5.00  --prep_sem_filter                       exhaustive
% 34.91/5.00  --prep_sem_filter_out                   false
% 34.91/5.00  --pred_elim                             true
% 34.91/5.00  --res_sim_input                         true
% 34.91/5.00  --eq_ax_congr_red                       true
% 34.91/5.00  --pure_diseq_elim                       true
% 34.91/5.00  --brand_transform                       false
% 34.91/5.00  --non_eq_to_eq                          false
% 34.91/5.00  --prep_def_merge                        true
% 34.91/5.00  --prep_def_merge_prop_impl              false
% 34.91/5.00  --prep_def_merge_mbd                    true
% 34.91/5.00  --prep_def_merge_tr_red                 false
% 34.91/5.00  --prep_def_merge_tr_cl                  false
% 34.91/5.00  --smt_preprocessing                     true
% 34.91/5.00  --smt_ac_axioms                         fast
% 34.91/5.00  --preprocessed_out                      false
% 34.91/5.00  --preprocessed_stats                    false
% 34.91/5.00  
% 34.91/5.00  ------ Abstraction refinement Options
% 34.91/5.00  
% 34.91/5.00  --abstr_ref                             []
% 34.91/5.00  --abstr_ref_prep                        false
% 34.91/5.00  --abstr_ref_until_sat                   false
% 34.91/5.00  --abstr_ref_sig_restrict                funpre
% 34.91/5.00  --abstr_ref_af_restrict_to_split_sk     false
% 34.91/5.00  --abstr_ref_under                       []
% 34.91/5.00  
% 34.91/5.00  ------ SAT Options
% 34.91/5.00  
% 34.91/5.00  --sat_mode                              false
% 34.91/5.00  --sat_fm_restart_options                ""
% 34.91/5.00  --sat_gr_def                            false
% 34.91/5.00  --sat_epr_types                         true
% 34.91/5.00  --sat_non_cyclic_types                  false
% 34.91/5.00  --sat_finite_models                     false
% 34.91/5.00  --sat_fm_lemmas                         false
% 34.91/5.00  --sat_fm_prep                           false
% 34.91/5.00  --sat_fm_uc_incr                        true
% 34.91/5.00  --sat_out_model                         small
% 34.91/5.00  --sat_out_clauses                       false
% 34.91/5.00  
% 34.91/5.00  ------ QBF Options
% 34.91/5.00  
% 34.91/5.00  --qbf_mode                              false
% 34.91/5.00  --qbf_elim_univ                         false
% 34.91/5.00  --qbf_dom_inst                          none
% 34.91/5.00  --qbf_dom_pre_inst                      false
% 34.91/5.00  --qbf_sk_in                             false
% 34.91/5.00  --qbf_pred_elim                         true
% 34.91/5.00  --qbf_split                             512
% 34.91/5.00  
% 34.91/5.00  ------ BMC1 Options
% 34.91/5.00  
% 34.91/5.00  --bmc1_incremental                      false
% 34.91/5.00  --bmc1_axioms                           reachable_all
% 34.91/5.00  --bmc1_min_bound                        0
% 34.91/5.00  --bmc1_max_bound                        -1
% 34.91/5.00  --bmc1_max_bound_default                -1
% 34.91/5.00  --bmc1_symbol_reachability              true
% 34.91/5.00  --bmc1_property_lemmas                  false
% 34.91/5.00  --bmc1_k_induction                      false
% 34.91/5.00  --bmc1_non_equiv_states                 false
% 34.91/5.00  --bmc1_deadlock                         false
% 34.91/5.00  --bmc1_ucm                              false
% 34.91/5.00  --bmc1_add_unsat_core                   none
% 34.91/5.00  --bmc1_unsat_core_children              false
% 34.91/5.00  --bmc1_unsat_core_extrapolate_axioms    false
% 34.91/5.00  --bmc1_out_stat                         full
% 34.91/5.00  --bmc1_ground_init                      false
% 34.91/5.00  --bmc1_pre_inst_next_state              false
% 34.91/5.00  --bmc1_pre_inst_state                   false
% 34.91/5.00  --bmc1_pre_inst_reach_state             false
% 34.91/5.00  --bmc1_out_unsat_core                   false
% 34.91/5.00  --bmc1_aig_witness_out                  false
% 34.91/5.00  --bmc1_verbose                          false
% 34.91/5.00  --bmc1_dump_clauses_tptp                false
% 34.91/5.00  --bmc1_dump_unsat_core_tptp             false
% 34.91/5.00  --bmc1_dump_file                        -
% 34.91/5.00  --bmc1_ucm_expand_uc_limit              128
% 34.91/5.00  --bmc1_ucm_n_expand_iterations          6
% 34.91/5.00  --bmc1_ucm_extend_mode                  1
% 34.91/5.00  --bmc1_ucm_init_mode                    2
% 34.91/5.00  --bmc1_ucm_cone_mode                    none
% 34.91/5.00  --bmc1_ucm_reduced_relation_type        0
% 34.91/5.00  --bmc1_ucm_relax_model                  4
% 34.91/5.00  --bmc1_ucm_full_tr_after_sat            true
% 34.91/5.00  --bmc1_ucm_expand_neg_assumptions       false
% 34.91/5.00  --bmc1_ucm_layered_model                none
% 34.91/5.00  --bmc1_ucm_max_lemma_size               10
% 34.91/5.00  
% 34.91/5.00  ------ AIG Options
% 34.91/5.00  
% 34.91/5.00  --aig_mode                              false
% 34.91/5.00  
% 34.91/5.00  ------ Instantiation Options
% 34.91/5.00  
% 34.91/5.00  --instantiation_flag                    true
% 34.91/5.00  --inst_sos_flag                         true
% 34.91/5.00  --inst_sos_phase                        true
% 34.91/5.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 34.91/5.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 34.91/5.00  --inst_lit_sel_side                     num_symb
% 34.91/5.00  --inst_solver_per_active                1400
% 34.91/5.00  --inst_solver_calls_frac                1.
% 34.91/5.00  --inst_passive_queue_type               priority_queues
% 34.91/5.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 34.91/5.00  --inst_passive_queues_freq              [25;2]
% 34.91/5.00  --inst_dismatching                      true
% 34.91/5.00  --inst_eager_unprocessed_to_passive     true
% 34.91/5.00  --inst_prop_sim_given                   true
% 34.91/5.00  --inst_prop_sim_new                     false
% 34.91/5.00  --inst_subs_new                         false
% 34.91/5.00  --inst_eq_res_simp                      false
% 34.91/5.00  --inst_subs_given                       false
% 34.91/5.00  --inst_orphan_elimination               true
% 34.91/5.00  --inst_learning_loop_flag               true
% 34.91/5.00  --inst_learning_start                   3000
% 34.91/5.00  --inst_learning_factor                  2
% 34.91/5.00  --inst_start_prop_sim_after_learn       3
% 34.91/5.00  --inst_sel_renew                        solver
% 34.91/5.00  --inst_lit_activity_flag                true
% 34.91/5.00  --inst_restr_to_given                   false
% 34.91/5.00  --inst_activity_threshold               500
% 34.91/5.00  --inst_out_proof                        true
% 34.91/5.00  
% 34.91/5.00  ------ Resolution Options
% 34.91/5.00  
% 34.91/5.00  --resolution_flag                       true
% 34.91/5.00  --res_lit_sel                           adaptive
% 34.91/5.00  --res_lit_sel_side                      none
% 34.91/5.00  --res_ordering                          kbo
% 34.91/5.00  --res_to_prop_solver                    active
% 34.91/5.00  --res_prop_simpl_new                    false
% 34.91/5.00  --res_prop_simpl_given                  true
% 34.91/5.00  --res_passive_queue_type                priority_queues
% 34.91/5.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 34.91/5.00  --res_passive_queues_freq               [15;5]
% 34.91/5.00  --res_forward_subs                      full
% 34.91/5.00  --res_backward_subs                     full
% 34.91/5.00  --res_forward_subs_resolution           true
% 34.91/5.00  --res_backward_subs_resolution          true
% 34.91/5.00  --res_orphan_elimination                true
% 34.91/5.00  --res_time_limit                        2.
% 34.91/5.00  --res_out_proof                         true
% 34.91/5.00  
% 34.91/5.00  ------ Superposition Options
% 34.91/5.00  
% 34.91/5.00  --superposition_flag                    true
% 34.91/5.00  --sup_passive_queue_type                priority_queues
% 34.91/5.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 34.91/5.00  --sup_passive_queues_freq               [8;1;4]
% 34.91/5.00  --demod_completeness_check              fast
% 34.91/5.00  --demod_use_ground                      true
% 34.91/5.00  --sup_to_prop_solver                    passive
% 34.91/5.00  --sup_prop_simpl_new                    true
% 34.91/5.00  --sup_prop_simpl_given                  true
% 34.91/5.00  --sup_fun_splitting                     true
% 34.91/5.00  --sup_smt_interval                      50000
% 34.91/5.00  
% 34.91/5.00  ------ Superposition Simplification Setup
% 34.91/5.00  
% 34.91/5.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 34.91/5.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 34.91/5.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 34.91/5.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 34.91/5.00  --sup_full_triv                         [TrivRules;PropSubs]
% 34.91/5.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 34.91/5.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 34.91/5.00  --sup_immed_triv                        [TrivRules]
% 34.91/5.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 34.91/5.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 34.91/5.00  --sup_immed_bw_main                     []
% 34.91/5.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 34.91/5.00  --sup_input_triv                        [Unflattening;TrivRules]
% 34.91/5.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 34.91/5.00  --sup_input_bw                          []
% 34.91/5.00  
% 34.91/5.00  ------ Combination Options
% 34.91/5.00  
% 34.91/5.00  --comb_res_mult                         3
% 34.91/5.00  --comb_sup_mult                         2
% 34.91/5.00  --comb_inst_mult                        10
% 34.91/5.00  
% 34.91/5.00  ------ Debug Options
% 34.91/5.00  
% 34.91/5.00  --dbg_backtrace                         false
% 34.91/5.00  --dbg_dump_prop_clauses                 false
% 34.91/5.00  --dbg_dump_prop_clauses_file            -
% 34.91/5.00  --dbg_out_stat                          false
% 34.91/5.00  ------ Parsing...
% 34.91/5.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 34.91/5.00  
% 34.91/5.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 34.91/5.00  
% 34.91/5.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 34.91/5.00  
% 34.91/5.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 34.91/5.00  ------ Proving...
% 34.91/5.00  ------ Problem Properties 
% 34.91/5.00  
% 34.91/5.00  
% 34.91/5.00  clauses                                 17
% 34.91/5.00  conjectures                             3
% 34.91/5.00  EPR                                     2
% 34.91/5.00  Horn                                    16
% 34.91/5.00  unary                                   6
% 34.91/5.00  binary                                  8
% 34.91/5.00  lits                                    33
% 34.91/5.00  lits eq                                 11
% 34.91/5.00  fd_pure                                 0
% 34.91/5.00  fd_pseudo                               0
% 34.91/5.00  fd_cond                                 0
% 34.91/5.00  fd_pseudo_cond                          1
% 34.91/5.00  AC symbols                              0
% 34.91/5.00  
% 34.91/5.00  ------ Schedule dynamic 5 is on 
% 34.91/5.00  
% 34.91/5.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 34.91/5.00  
% 34.91/5.00  
% 34.91/5.00  ------ 
% 34.91/5.00  Current options:
% 34.91/5.00  ------ 
% 34.91/5.00  
% 34.91/5.00  ------ Input Options
% 34.91/5.00  
% 34.91/5.00  --out_options                           all
% 34.91/5.00  --tptp_safe_out                         true
% 34.91/5.00  --problem_path                          ""
% 34.91/5.00  --include_path                          ""
% 34.91/5.00  --clausifier                            res/vclausify_rel
% 34.91/5.00  --clausifier_options                    ""
% 34.91/5.00  --stdin                                 false
% 34.91/5.00  --stats_out                             all
% 34.91/5.00  
% 34.91/5.00  ------ General Options
% 34.91/5.00  
% 34.91/5.00  --fof                                   false
% 34.91/5.00  --time_out_real                         305.
% 34.91/5.00  --time_out_virtual                      -1.
% 34.91/5.00  --symbol_type_check                     false
% 34.91/5.00  --clausify_out                          false
% 34.91/5.00  --sig_cnt_out                           false
% 34.91/5.00  --trig_cnt_out                          false
% 34.91/5.00  --trig_cnt_out_tolerance                1.
% 34.91/5.00  --trig_cnt_out_sk_spl                   false
% 34.91/5.00  --abstr_cl_out                          false
% 34.91/5.00  
% 34.91/5.00  ------ Global Options
% 34.91/5.00  
% 34.91/5.00  --schedule                              default
% 34.91/5.00  --add_important_lit                     false
% 34.91/5.00  --prop_solver_per_cl                    1000
% 34.91/5.00  --min_unsat_core                        false
% 34.91/5.00  --soft_assumptions                      false
% 34.91/5.00  --soft_lemma_size                       3
% 34.91/5.00  --prop_impl_unit_size                   0
% 34.91/5.00  --prop_impl_unit                        []
% 34.91/5.00  --share_sel_clauses                     true
% 34.91/5.00  --reset_solvers                         false
% 34.91/5.00  --bc_imp_inh                            [conj_cone]
% 34.91/5.00  --conj_cone_tolerance                   3.
% 34.91/5.00  --extra_neg_conj                        none
% 34.91/5.00  --large_theory_mode                     true
% 34.91/5.00  --prolific_symb_bound                   200
% 34.91/5.00  --lt_threshold                          2000
% 34.91/5.00  --clause_weak_htbl                      true
% 34.91/5.00  --gc_record_bc_elim                     false
% 34.91/5.00  
% 34.91/5.00  ------ Preprocessing Options
% 34.91/5.00  
% 34.91/5.00  --preprocessing_flag                    true
% 34.91/5.00  --time_out_prep_mult                    0.1
% 34.91/5.00  --splitting_mode                        input
% 34.91/5.00  --splitting_grd                         true
% 34.91/5.00  --splitting_cvd                         false
% 34.91/5.00  --splitting_cvd_svl                     false
% 34.91/5.00  --splitting_nvd                         32
% 34.91/5.00  --sub_typing                            true
% 34.91/5.00  --prep_gs_sim                           true
% 34.91/5.00  --prep_unflatten                        true
% 34.91/5.00  --prep_res_sim                          true
% 34.91/5.00  --prep_upred                            true
% 34.91/5.00  --prep_sem_filter                       exhaustive
% 34.91/5.00  --prep_sem_filter_out                   false
% 34.91/5.00  --pred_elim                             true
% 34.91/5.00  --res_sim_input                         true
% 34.91/5.00  --eq_ax_congr_red                       true
% 34.91/5.00  --pure_diseq_elim                       true
% 34.91/5.00  --brand_transform                       false
% 34.91/5.00  --non_eq_to_eq                          false
% 34.91/5.00  --prep_def_merge                        true
% 34.91/5.00  --prep_def_merge_prop_impl              false
% 34.91/5.00  --prep_def_merge_mbd                    true
% 34.91/5.00  --prep_def_merge_tr_red                 false
% 34.91/5.00  --prep_def_merge_tr_cl                  false
% 34.91/5.00  --smt_preprocessing                     true
% 34.91/5.00  --smt_ac_axioms                         fast
% 34.91/5.00  --preprocessed_out                      false
% 34.91/5.00  --preprocessed_stats                    false
% 34.91/5.00  
% 34.91/5.00  ------ Abstraction refinement Options
% 34.91/5.00  
% 34.91/5.00  --abstr_ref                             []
% 34.91/5.00  --abstr_ref_prep                        false
% 34.91/5.00  --abstr_ref_until_sat                   false
% 34.91/5.00  --abstr_ref_sig_restrict                funpre
% 34.91/5.00  --abstr_ref_af_restrict_to_split_sk     false
% 34.91/5.00  --abstr_ref_under                       []
% 34.91/5.00  
% 34.91/5.00  ------ SAT Options
% 34.91/5.00  
% 34.91/5.00  --sat_mode                              false
% 34.91/5.00  --sat_fm_restart_options                ""
% 34.91/5.00  --sat_gr_def                            false
% 34.91/5.00  --sat_epr_types                         true
% 34.91/5.00  --sat_non_cyclic_types                  false
% 34.91/5.00  --sat_finite_models                     false
% 34.91/5.00  --sat_fm_lemmas                         false
% 34.91/5.00  --sat_fm_prep                           false
% 34.91/5.00  --sat_fm_uc_incr                        true
% 34.91/5.00  --sat_out_model                         small
% 34.91/5.00  --sat_out_clauses                       false
% 34.91/5.00  
% 34.91/5.00  ------ QBF Options
% 34.91/5.00  
% 34.91/5.00  --qbf_mode                              false
% 34.91/5.00  --qbf_elim_univ                         false
% 34.91/5.00  --qbf_dom_inst                          none
% 34.91/5.00  --qbf_dom_pre_inst                      false
% 34.91/5.00  --qbf_sk_in                             false
% 34.91/5.00  --qbf_pred_elim                         true
% 34.91/5.00  --qbf_split                             512
% 34.91/5.00  
% 34.91/5.00  ------ BMC1 Options
% 34.91/5.00  
% 34.91/5.00  --bmc1_incremental                      false
% 34.91/5.00  --bmc1_axioms                           reachable_all
% 34.91/5.00  --bmc1_min_bound                        0
% 34.91/5.00  --bmc1_max_bound                        -1
% 34.91/5.00  --bmc1_max_bound_default                -1
% 34.91/5.00  --bmc1_symbol_reachability              true
% 34.91/5.00  --bmc1_property_lemmas                  false
% 34.91/5.00  --bmc1_k_induction                      false
% 34.91/5.00  --bmc1_non_equiv_states                 false
% 34.91/5.00  --bmc1_deadlock                         false
% 34.91/5.00  --bmc1_ucm                              false
% 34.91/5.00  --bmc1_add_unsat_core                   none
% 34.91/5.00  --bmc1_unsat_core_children              false
% 34.91/5.00  --bmc1_unsat_core_extrapolate_axioms    false
% 34.91/5.00  --bmc1_out_stat                         full
% 34.91/5.00  --bmc1_ground_init                      false
% 34.91/5.00  --bmc1_pre_inst_next_state              false
% 34.91/5.00  --bmc1_pre_inst_state                   false
% 34.91/5.00  --bmc1_pre_inst_reach_state             false
% 34.91/5.00  --bmc1_out_unsat_core                   false
% 34.91/5.00  --bmc1_aig_witness_out                  false
% 34.91/5.00  --bmc1_verbose                          false
% 34.91/5.00  --bmc1_dump_clauses_tptp                false
% 34.91/5.00  --bmc1_dump_unsat_core_tptp             false
% 34.91/5.00  --bmc1_dump_file                        -
% 34.91/5.00  --bmc1_ucm_expand_uc_limit              128
% 34.91/5.00  --bmc1_ucm_n_expand_iterations          6
% 34.91/5.00  --bmc1_ucm_extend_mode                  1
% 34.91/5.00  --bmc1_ucm_init_mode                    2
% 34.91/5.00  --bmc1_ucm_cone_mode                    none
% 34.91/5.00  --bmc1_ucm_reduced_relation_type        0
% 34.91/5.00  --bmc1_ucm_relax_model                  4
% 34.91/5.00  --bmc1_ucm_full_tr_after_sat            true
% 34.91/5.00  --bmc1_ucm_expand_neg_assumptions       false
% 34.91/5.00  --bmc1_ucm_layered_model                none
% 34.91/5.00  --bmc1_ucm_max_lemma_size               10
% 34.91/5.00  
% 34.91/5.00  ------ AIG Options
% 34.91/5.00  
% 34.91/5.00  --aig_mode                              false
% 34.91/5.00  
% 34.91/5.00  ------ Instantiation Options
% 34.91/5.00  
% 34.91/5.00  --instantiation_flag                    true
% 34.91/5.00  --inst_sos_flag                         true
% 34.91/5.00  --inst_sos_phase                        true
% 34.91/5.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 34.91/5.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 34.91/5.00  --inst_lit_sel_side                     none
% 34.91/5.00  --inst_solver_per_active                1400
% 34.91/5.00  --inst_solver_calls_frac                1.
% 34.91/5.00  --inst_passive_queue_type               priority_queues
% 34.91/5.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 34.91/5.00  --inst_passive_queues_freq              [25;2]
% 34.91/5.00  --inst_dismatching                      true
% 34.91/5.00  --inst_eager_unprocessed_to_passive     true
% 34.91/5.00  --inst_prop_sim_given                   true
% 34.91/5.00  --inst_prop_sim_new                     false
% 34.91/5.00  --inst_subs_new                         false
% 34.91/5.00  --inst_eq_res_simp                      false
% 34.91/5.00  --inst_subs_given                       false
% 34.91/5.00  --inst_orphan_elimination               true
% 34.91/5.00  --inst_learning_loop_flag               true
% 34.91/5.00  --inst_learning_start                   3000
% 34.91/5.00  --inst_learning_factor                  2
% 34.91/5.00  --inst_start_prop_sim_after_learn       3
% 34.91/5.00  --inst_sel_renew                        solver
% 34.91/5.00  --inst_lit_activity_flag                true
% 34.91/5.00  --inst_restr_to_given                   false
% 34.91/5.00  --inst_activity_threshold               500
% 34.91/5.00  --inst_out_proof                        true
% 34.91/5.00  
% 34.91/5.00  ------ Resolution Options
% 34.91/5.00  
% 34.91/5.00  --resolution_flag                       false
% 34.91/5.00  --res_lit_sel                           adaptive
% 34.91/5.00  --res_lit_sel_side                      none
% 34.91/5.00  --res_ordering                          kbo
% 34.91/5.00  --res_to_prop_solver                    active
% 34.91/5.00  --res_prop_simpl_new                    false
% 34.91/5.00  --res_prop_simpl_given                  true
% 34.91/5.00  --res_passive_queue_type                priority_queues
% 34.91/5.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 34.91/5.00  --res_passive_queues_freq               [15;5]
% 34.91/5.00  --res_forward_subs                      full
% 34.91/5.00  --res_backward_subs                     full
% 34.91/5.00  --res_forward_subs_resolution           true
% 34.91/5.00  --res_backward_subs_resolution          true
% 34.91/5.00  --res_orphan_elimination                true
% 34.91/5.00  --res_time_limit                        2.
% 34.91/5.00  --res_out_proof                         true
% 34.91/5.00  
% 34.91/5.00  ------ Superposition Options
% 34.91/5.00  
% 34.91/5.00  --superposition_flag                    true
% 34.91/5.00  --sup_passive_queue_type                priority_queues
% 34.91/5.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 34.91/5.00  --sup_passive_queues_freq               [8;1;4]
% 34.91/5.00  --demod_completeness_check              fast
% 34.91/5.00  --demod_use_ground                      true
% 34.91/5.00  --sup_to_prop_solver                    passive
% 34.91/5.00  --sup_prop_simpl_new                    true
% 34.91/5.00  --sup_prop_simpl_given                  true
% 34.91/5.00  --sup_fun_splitting                     true
% 34.91/5.00  --sup_smt_interval                      50000
% 34.91/5.00  
% 34.91/5.00  ------ Superposition Simplification Setup
% 34.91/5.00  
% 34.91/5.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 34.91/5.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 34.91/5.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 34.91/5.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 34.91/5.00  --sup_full_triv                         [TrivRules;PropSubs]
% 34.91/5.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 34.91/5.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 34.91/5.00  --sup_immed_triv                        [TrivRules]
% 34.91/5.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 34.91/5.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 34.91/5.00  --sup_immed_bw_main                     []
% 34.91/5.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 34.91/5.00  --sup_input_triv                        [Unflattening;TrivRules]
% 34.91/5.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 34.91/5.00  --sup_input_bw                          []
% 34.91/5.00  
% 34.91/5.00  ------ Combination Options
% 34.91/5.00  
% 34.91/5.00  --comb_res_mult                         3
% 34.91/5.00  --comb_sup_mult                         2
% 34.91/5.00  --comb_inst_mult                        10
% 34.91/5.00  
% 34.91/5.00  ------ Debug Options
% 34.91/5.00  
% 34.91/5.00  --dbg_backtrace                         false
% 34.91/5.00  --dbg_dump_prop_clauses                 false
% 34.91/5.00  --dbg_dump_prop_clauses_file            -
% 34.91/5.00  --dbg_out_stat                          false
% 34.91/5.00  
% 34.91/5.00  
% 34.91/5.00  
% 34.91/5.00  
% 34.91/5.00  ------ Proving...
% 34.91/5.00  
% 34.91/5.00  
% 34.91/5.00  % SZS status Theorem for theBenchmark.p
% 34.91/5.00  
% 34.91/5.00  % SZS output start CNFRefutation for theBenchmark.p
% 34.91/5.00  
% 34.91/5.00  fof(f17,conjecture,(
% 34.91/5.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 34.91/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 34.91/5.00  
% 34.91/5.00  fof(f18,negated_conjecture,(
% 34.91/5.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 34.91/5.00    inference(negated_conjecture,[],[f17])).
% 34.91/5.00  
% 34.91/5.00  fof(f31,plain,(
% 34.91/5.00    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 34.91/5.00    inference(ennf_transformation,[],[f18])).
% 34.91/5.00  
% 34.91/5.00  fof(f32,plain,(
% 34.91/5.00    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 34.91/5.00    inference(flattening,[],[f31])).
% 34.91/5.00  
% 34.91/5.00  fof(f35,plain,(
% 34.91/5.00    ? [X0] : (? [X1] : (((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 34.91/5.00    inference(nnf_transformation,[],[f32])).
% 34.91/5.00  
% 34.91/5.00  fof(f36,plain,(
% 34.91/5.00    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 34.91/5.00    inference(flattening,[],[f35])).
% 34.91/5.00  
% 34.91/5.00  fof(f38,plain,(
% 34.91/5.00    ( ! [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) != k2_tops_1(X0,sK1) | ~v4_pre_topc(sK1,X0)) & (k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) = k2_tops_1(X0,sK1) | v4_pre_topc(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 34.91/5.00    introduced(choice_axiom,[])).
% 34.91/5.00  
% 34.91/5.00  fof(f37,plain,(
% 34.91/5.00    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) != k2_tops_1(sK0,X1) | ~v4_pre_topc(X1,sK0)) & (k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) = k2_tops_1(sK0,X1) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 34.91/5.00    introduced(choice_axiom,[])).
% 34.91/5.00  
% 34.91/5.00  fof(f39,plain,(
% 34.91/5.00    ((k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)) & (k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 34.91/5.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f36,f38,f37])).
% 34.91/5.00  
% 34.91/5.00  fof(f61,plain,(
% 34.91/5.00    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)),
% 34.91/5.00    inference(cnf_transformation,[],[f39])).
% 34.91/5.00  
% 34.91/5.00  fof(f60,plain,(
% 34.91/5.00    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 34.91/5.00    inference(cnf_transformation,[],[f39])).
% 34.91/5.00  
% 34.91/5.00  fof(f15,axiom,(
% 34.91/5.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X2,X1) & v4_pre_topc(X1,X0)) => r1_tarski(k2_pre_topc(X0,X2),X1)))))),
% 34.91/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 34.91/5.00  
% 34.91/5.00  fof(f28,plain,(
% 34.91/5.00    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k2_pre_topc(X0,X2),X1) | (~r1_tarski(X2,X1) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 34.91/5.00    inference(ennf_transformation,[],[f15])).
% 34.91/5.00  
% 34.91/5.00  fof(f29,plain,(
% 34.91/5.00    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k2_pre_topc(X0,X2),X1) | ~r1_tarski(X2,X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 34.91/5.00    inference(flattening,[],[f28])).
% 34.91/5.00  
% 34.91/5.00  fof(f56,plain,(
% 34.91/5.00    ( ! [X2,X0,X1] : (r1_tarski(k2_pre_topc(X0,X2),X1) | ~r1_tarski(X2,X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 34.91/5.00    inference(cnf_transformation,[],[f29])).
% 34.91/5.00  
% 34.91/5.00  fof(f59,plain,(
% 34.91/5.00    l1_pre_topc(sK0)),
% 34.91/5.00    inference(cnf_transformation,[],[f39])).
% 34.91/5.00  
% 34.91/5.00  fof(f1,axiom,(
% 34.91/5.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 34.91/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 34.91/5.00  
% 34.91/5.00  fof(f33,plain,(
% 34.91/5.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 34.91/5.00    inference(nnf_transformation,[],[f1])).
% 34.91/5.00  
% 34.91/5.00  fof(f34,plain,(
% 34.91/5.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 34.91/5.00    inference(flattening,[],[f33])).
% 34.91/5.00  
% 34.91/5.00  fof(f41,plain,(
% 34.91/5.00    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 34.91/5.00    inference(cnf_transformation,[],[f34])).
% 34.91/5.00  
% 34.91/5.00  fof(f69,plain,(
% 34.91/5.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 34.91/5.00    inference(equality_resolution,[],[f41])).
% 34.91/5.00  
% 34.91/5.00  fof(f11,axiom,(
% 34.91/5.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 34.91/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 34.91/5.00  
% 34.91/5.00  fof(f22,plain,(
% 34.91/5.00    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 34.91/5.00    inference(ennf_transformation,[],[f11])).
% 34.91/5.00  
% 34.91/5.00  fof(f52,plain,(
% 34.91/5.00    ( ! [X0,X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 34.91/5.00    inference(cnf_transformation,[],[f22])).
% 34.91/5.00  
% 34.91/5.00  fof(f42,plain,(
% 34.91/5.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 34.91/5.00    inference(cnf_transformation,[],[f34])).
% 34.91/5.00  
% 34.91/5.00  fof(f9,axiom,(
% 34.91/5.00    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 34.91/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 34.91/5.00  
% 34.91/5.00  fof(f21,plain,(
% 34.91/5.00    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 34.91/5.00    inference(ennf_transformation,[],[f9])).
% 34.91/5.00  
% 34.91/5.00  fof(f50,plain,(
% 34.91/5.00    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 34.91/5.00    inference(cnf_transformation,[],[f21])).
% 34.91/5.00  
% 34.91/5.00  fof(f2,axiom,(
% 34.91/5.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 34.91/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 34.91/5.00  
% 34.91/5.00  fof(f43,plain,(
% 34.91/5.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 34.91/5.00    inference(cnf_transformation,[],[f2])).
% 34.91/5.00  
% 34.91/5.00  fof(f10,axiom,(
% 34.91/5.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 34.91/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 34.91/5.00  
% 34.91/5.00  fof(f51,plain,(
% 34.91/5.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 34.91/5.00    inference(cnf_transformation,[],[f10])).
% 34.91/5.00  
% 34.91/5.00  fof(f63,plain,(
% 34.91/5.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 34.91/5.00    inference(definition_unfolding,[],[f43,f51])).
% 34.91/5.00  
% 34.91/5.00  fof(f68,plain,(
% 34.91/5.00    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 34.91/5.00    inference(definition_unfolding,[],[f50,f63])).
% 34.91/5.00  
% 34.91/5.00  fof(f6,axiom,(
% 34.91/5.00    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 34.91/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 34.91/5.00  
% 34.91/5.00  fof(f47,plain,(
% 34.91/5.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 34.91/5.00    inference(cnf_transformation,[],[f6])).
% 34.91/5.00  
% 34.91/5.00  fof(f3,axiom,(
% 34.91/5.00    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 34.91/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 34.91/5.00  
% 34.91/5.00  fof(f44,plain,(
% 34.91/5.00    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 34.91/5.00    inference(cnf_transformation,[],[f3])).
% 34.91/5.00  
% 34.91/5.00  fof(f7,axiom,(
% 34.91/5.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 34.91/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 34.91/5.00  
% 34.91/5.00  fof(f48,plain,(
% 34.91/5.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 34.91/5.00    inference(cnf_transformation,[],[f7])).
% 34.91/5.00  
% 34.91/5.00  fof(f64,plain,(
% 34.91/5.00    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,k1_setfam_1(k2_tarski(X0,X1)))) = X0) )),
% 34.91/5.00    inference(definition_unfolding,[],[f44,f48,f51])).
% 34.91/5.00  
% 34.91/5.00  fof(f5,axiom,(
% 34.91/5.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 34.91/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 34.91/5.00  
% 34.91/5.00  fof(f46,plain,(
% 34.91/5.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 34.91/5.00    inference(cnf_transformation,[],[f5])).
% 34.91/5.00  
% 34.91/5.00  fof(f66,plain,(
% 34.91/5.00    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(k5_xboole_0(X0,X1),k1_setfam_1(k2_tarski(X0,X1))))) )),
% 34.91/5.00    inference(definition_unfolding,[],[f46,f48,f48,f51])).
% 34.91/5.00  
% 34.91/5.00  fof(f4,axiom,(
% 34.91/5.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))),
% 34.91/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 34.91/5.00  
% 34.91/5.00  fof(f45,plain,(
% 34.91/5.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 34.91/5.00    inference(cnf_transformation,[],[f4])).
% 34.91/5.00  
% 34.91/5.00  fof(f65,plain,(
% 34.91/5.00    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1))))) )),
% 34.91/5.00    inference(definition_unfolding,[],[f45,f48,f48,f48])).
% 34.91/5.00  
% 34.91/5.00  fof(f12,axiom,(
% 34.91/5.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 34.91/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 34.91/5.00  
% 34.91/5.00  fof(f23,plain,(
% 34.91/5.00    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 34.91/5.00    inference(ennf_transformation,[],[f12])).
% 34.91/5.00  
% 34.91/5.00  fof(f24,plain,(
% 34.91/5.00    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 34.91/5.00    inference(flattening,[],[f23])).
% 34.91/5.00  
% 34.91/5.00  fof(f53,plain,(
% 34.91/5.00    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 34.91/5.00    inference(cnf_transformation,[],[f24])).
% 34.91/5.00  
% 34.91/5.00  fof(f8,axiom,(
% 34.91/5.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 34.91/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 34.91/5.00  
% 34.91/5.00  fof(f19,plain,(
% 34.91/5.00    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 34.91/5.00    inference(ennf_transformation,[],[f8])).
% 34.91/5.00  
% 34.91/5.00  fof(f20,plain,(
% 34.91/5.00    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 34.91/5.00    inference(flattening,[],[f19])).
% 34.91/5.00  
% 34.91/5.00  fof(f49,plain,(
% 34.91/5.00    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 34.91/5.00    inference(cnf_transformation,[],[f20])).
% 34.91/5.00  
% 34.91/5.00  fof(f67,plain,(
% 34.91/5.00    ( ! [X2,X0,X1] : (k3_tarski(k2_tarski(X1,X2)) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 34.91/5.00    inference(definition_unfolding,[],[f49,f48])).
% 34.91/5.00  
% 34.91/5.00  fof(f16,axiom,(
% 34.91/5.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)))),
% 34.91/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 34.91/5.00  
% 34.91/5.00  fof(f30,plain,(
% 34.91/5.00    ! [X0] : (! [X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 34.91/5.00    inference(ennf_transformation,[],[f16])).
% 34.91/5.00  
% 34.91/5.00  fof(f57,plain,(
% 34.91/5.00    ( ! [X0,X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 34.91/5.00    inference(cnf_transformation,[],[f30])).
% 34.91/5.00  
% 34.91/5.00  fof(f14,axiom,(
% 34.91/5.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)))),
% 34.91/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 34.91/5.00  
% 34.91/5.00  fof(f27,plain,(
% 34.91/5.00    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 34.91/5.00    inference(ennf_transformation,[],[f14])).
% 34.91/5.00  
% 34.91/5.00  fof(f55,plain,(
% 34.91/5.00    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 34.91/5.00    inference(cnf_transformation,[],[f27])).
% 34.91/5.00  
% 34.91/5.00  fof(f13,axiom,(
% 34.91/5.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_pre_topc(X0,X1),X0))),
% 34.91/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 34.91/5.00  
% 34.91/5.00  fof(f25,plain,(
% 34.91/5.00    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 34.91/5.00    inference(ennf_transformation,[],[f13])).
% 34.91/5.00  
% 34.91/5.00  fof(f26,plain,(
% 34.91/5.00    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 34.91/5.00    inference(flattening,[],[f25])).
% 34.91/5.00  
% 34.91/5.00  fof(f54,plain,(
% 34.91/5.00    ( ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 34.91/5.00    inference(cnf_transformation,[],[f26])).
% 34.91/5.00  
% 34.91/5.00  fof(f58,plain,(
% 34.91/5.00    v2_pre_topc(sK0)),
% 34.91/5.00    inference(cnf_transformation,[],[f39])).
% 34.91/5.00  
% 34.91/5.00  fof(f40,plain,(
% 34.91/5.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 34.91/5.00    inference(cnf_transformation,[],[f34])).
% 34.91/5.00  
% 34.91/5.00  fof(f70,plain,(
% 34.91/5.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 34.91/5.00    inference(equality_resolution,[],[f40])).
% 34.91/5.00  
% 34.91/5.00  fof(f62,plain,(
% 34.91/5.00    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)),
% 34.91/5.00    inference(cnf_transformation,[],[f39])).
% 34.91/5.00  
% 34.91/5.00  cnf(c_16,negated_conjecture,
% 34.91/5.00      ( v4_pre_topc(sK1,sK0)
% 34.91/5.00      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 34.91/5.00      inference(cnf_transformation,[],[f61]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_999,plain,
% 34.91/5.00      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 34.91/5.00      | v4_pre_topc(sK1,sK0) = iProver_top ),
% 34.91/5.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_17,negated_conjecture,
% 34.91/5.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 34.91/5.00      inference(cnf_transformation,[],[f60]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_998,plain,
% 34.91/5.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 34.91/5.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_13,plain,
% 34.91/5.00      ( ~ v4_pre_topc(X0,X1)
% 34.91/5.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 34.91/5.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 34.91/5.00      | ~ r1_tarski(X2,X0)
% 34.91/5.00      | r1_tarski(k2_pre_topc(X1,X2),X0)
% 34.91/5.00      | ~ l1_pre_topc(X1) ),
% 34.91/5.00      inference(cnf_transformation,[],[f56]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_18,negated_conjecture,
% 34.91/5.00      ( l1_pre_topc(sK0) ),
% 34.91/5.00      inference(cnf_transformation,[],[f59]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_261,plain,
% 34.91/5.00      ( ~ v4_pre_topc(X0,X1)
% 34.91/5.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 34.91/5.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 34.91/5.00      | ~ r1_tarski(X2,X0)
% 34.91/5.00      | r1_tarski(k2_pre_topc(X1,X2),X0)
% 34.91/5.00      | sK0 != X1 ),
% 34.91/5.00      inference(resolution_lifted,[status(thm)],[c_13,c_18]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_262,plain,
% 34.91/5.00      ( ~ v4_pre_topc(X0,sK0)
% 34.91/5.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 34.91/5.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 34.91/5.00      | ~ r1_tarski(X1,X0)
% 34.91/5.00      | r1_tarski(k2_pre_topc(sK0,X1),X0) ),
% 34.91/5.00      inference(unflattening,[status(thm)],[c_261]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_995,plain,
% 34.91/5.00      ( v4_pre_topc(X0,sK0) != iProver_top
% 34.91/5.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 34.91/5.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 34.91/5.00      | r1_tarski(X1,X0) != iProver_top
% 34.91/5.00      | r1_tarski(k2_pre_topc(sK0,X1),X0) = iProver_top ),
% 34.91/5.00      inference(predicate_to_equality,[status(thm)],[c_262]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_1692,plain,
% 34.91/5.00      ( v4_pre_topc(sK1,sK0) != iProver_top
% 34.91/5.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 34.91/5.00      | r1_tarski(X0,sK1) != iProver_top
% 34.91/5.00      | r1_tarski(k2_pre_topc(sK0,X0),sK1) = iProver_top ),
% 34.91/5.00      inference(superposition,[status(thm)],[c_998,c_995]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_1701,plain,
% 34.91/5.00      ( v4_pre_topc(sK1,sK0) != iProver_top
% 34.91/5.00      | r1_tarski(k2_pre_topc(sK0,sK1),sK1) = iProver_top
% 34.91/5.00      | r1_tarski(sK1,sK1) != iProver_top ),
% 34.91/5.00      inference(superposition,[status(thm)],[c_998,c_1692]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_1,plain,
% 34.91/5.00      ( r1_tarski(X0,X0) ),
% 34.91/5.00      inference(cnf_transformation,[],[f69]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_1375,plain,
% 34.91/5.00      ( r1_tarski(sK1,sK1) ),
% 34.91/5.00      inference(instantiation,[status(thm)],[c_1]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_1376,plain,
% 34.91/5.00      ( r1_tarski(sK1,sK1) = iProver_top ),
% 34.91/5.00      inference(predicate_to_equality,[status(thm)],[c_1375]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_1786,plain,
% 34.91/5.00      ( r1_tarski(k2_pre_topc(sK0,sK1),sK1) = iProver_top
% 34.91/5.00      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 34.91/5.00      inference(global_propositional_subsumption,
% 34.91/5.00                [status(thm)],
% 34.91/5.00                [c_1701,c_1376]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_1787,plain,
% 34.91/5.00      ( v4_pre_topc(sK1,sK0) != iProver_top
% 34.91/5.00      | r1_tarski(k2_pre_topc(sK0,sK1),sK1) = iProver_top ),
% 34.91/5.00      inference(renaming,[status(thm)],[c_1786]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_9,plain,
% 34.91/5.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 34.91/5.00      | r1_tarski(X0,k2_pre_topc(X1,X0))
% 34.91/5.00      | ~ l1_pre_topc(X1) ),
% 34.91/5.00      inference(cnf_transformation,[],[f52]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_306,plain,
% 34.91/5.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 34.91/5.00      | r1_tarski(X0,k2_pre_topc(X1,X0))
% 34.91/5.00      | sK0 != X1 ),
% 34.91/5.00      inference(resolution_lifted,[status(thm)],[c_9,c_18]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_307,plain,
% 34.91/5.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 34.91/5.00      | r1_tarski(X0,k2_pre_topc(sK0,X0)) ),
% 34.91/5.00      inference(unflattening,[status(thm)],[c_306]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_992,plain,
% 34.91/5.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 34.91/5.00      | r1_tarski(X0,k2_pre_topc(sK0,X0)) = iProver_top ),
% 34.91/5.00      inference(predicate_to_equality,[status(thm)],[c_307]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_1113,plain,
% 34.91/5.00      ( r1_tarski(sK1,k2_pre_topc(sK0,sK1)) = iProver_top ),
% 34.91/5.00      inference(superposition,[status(thm)],[c_998,c_992]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_0,plain,
% 34.91/5.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 34.91/5.00      inference(cnf_transformation,[],[f42]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_1004,plain,
% 34.91/5.00      ( X0 = X1
% 34.91/5.00      | r1_tarski(X0,X1) != iProver_top
% 34.91/5.00      | r1_tarski(X1,X0) != iProver_top ),
% 34.91/5.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_4036,plain,
% 34.91/5.00      ( k2_pre_topc(sK0,sK1) = sK1
% 34.91/5.00      | r1_tarski(k2_pre_topc(sK0,sK1),sK1) != iProver_top ),
% 34.91/5.00      inference(superposition,[status(thm)],[c_1113,c_1004]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_4240,plain,
% 34.91/5.00      ( k2_pre_topc(sK0,sK1) = sK1
% 34.91/5.00      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 34.91/5.00      inference(superposition,[status(thm)],[c_1787,c_4036]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_4243,plain,
% 34.91/5.00      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 34.91/5.00      | k2_pre_topc(sK0,sK1) = sK1 ),
% 34.91/5.00      inference(superposition,[status(thm)],[c_999,c_4240]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_8,plain,
% 34.91/5.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 34.91/5.00      | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2))) = k7_subset_1(X1,X0,X2) ),
% 34.91/5.00      inference(cnf_transformation,[],[f68]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_1001,plain,
% 34.91/5.00      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X2,X0,X1)
% 34.91/5.00      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
% 34.91/5.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_1841,plain,
% 34.91/5.00      ( k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0))) = k7_subset_1(u1_struct_0(sK0),sK1,X0) ),
% 34.91/5.00      inference(superposition,[status(thm)],[c_998,c_1001]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_6,plain,
% 34.91/5.00      ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
% 34.91/5.00      inference(cnf_transformation,[],[f47]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_3,plain,
% 34.91/5.00      ( k3_tarski(k2_tarski(X0,k1_setfam_1(k2_tarski(X0,X1)))) = X0 ),
% 34.91/5.00      inference(cnf_transformation,[],[f64]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_5,plain,
% 34.91/5.00      ( k3_tarski(k2_tarski(k5_xboole_0(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(X0,X1)) ),
% 34.91/5.00      inference(cnf_transformation,[],[f66]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_4,plain,
% 34.91/5.00      ( k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(X0,X1)) ),
% 34.91/5.00      inference(cnf_transformation,[],[f65]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_1432,plain,
% 34.91/5.00      ( k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X1,X0)))) = k3_tarski(k2_tarski(X0,X1)) ),
% 34.91/5.00      inference(superposition,[status(thm)],[c_6,c_4]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_2064,plain,
% 34.91/5.00      ( k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),k5_xboole_0(X0,X1))) ),
% 34.91/5.00      inference(superposition,[status(thm)],[c_5,c_1432]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_5516,plain,
% 34.91/5.00      ( k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X1,X0)),k5_xboole_0(X1,X0))) ),
% 34.91/5.00      inference(superposition,[status(thm)],[c_6,c_2064]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_5644,plain,
% 34.91/5.00      ( k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),k5_xboole_0(X0,X1))),k5_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),k5_xboole_0(X0,X1)))) = k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(k5_xboole_0(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))),k3_tarski(k2_tarski(X0,X1)))) ),
% 34.91/5.00      inference(superposition,[status(thm)],[c_5,c_5516]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_5494,plain,
% 34.91/5.00      ( k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(k5_xboole_0(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))),k5_xboole_0(k5_xboole_0(X0,X1),k1_setfam_1(k2_tarski(X0,X1))))) = k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(k5_xboole_0(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))),k3_tarski(k2_tarski(X0,X1)))) ),
% 34.91/5.00      inference(superposition,[status(thm)],[c_5,c_2064]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_5643,plain,
% 34.91/5.00      ( k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X0)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0))) = k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))),k3_tarski(k2_tarski(X0,X1)))) ),
% 34.91/5.00      inference(superposition,[status(thm)],[c_4,c_5516]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_1519,plain,
% 34.91/5.00      ( k3_tarski(k2_tarski(k5_xboole_0(X0,X1),k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(k5_xboole_0(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))) ),
% 34.91/5.00      inference(superposition,[status(thm)],[c_5,c_4]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_1520,plain,
% 34.91/5.00      ( k3_tarski(k2_tarski(k5_xboole_0(X0,X1),k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(X0,X1)) ),
% 34.91/5.00      inference(demodulation,[status(thm)],[c_1519,c_5]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_3054,plain,
% 34.91/5.00      ( k3_tarski(k2_tarski(k5_xboole_0(X0,k3_tarski(k2_tarski(X0,X1))),k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) ),
% 34.91/5.00      inference(superposition,[status(thm)],[c_4,c_1520]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_3072,plain,
% 34.91/5.00      ( k3_tarski(k2_tarski(k5_xboole_0(X0,k3_tarski(k2_tarski(X0,X1))),k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(X0,X1)) ),
% 34.91/5.00      inference(light_normalisation,[status(thm)],[c_3054,c_4]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_4086,plain,
% 34.91/5.00      ( k3_tarski(k2_tarski(k5_xboole_0(X0,k3_tarski(k2_tarski(X1,X0))),k3_tarski(k2_tarski(X1,X0)))) = k3_tarski(k2_tarski(X0,X1)) ),
% 34.91/5.00      inference(superposition,[status(thm)],[c_6,c_3072]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_4574,plain,
% 34.91/5.00      ( k3_tarski(k2_tarski(k5_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1))),k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),k5_xboole_0(X0,X1))) ),
% 34.91/5.00      inference(superposition,[status(thm)],[c_5,c_4086]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_9974,plain,
% 34.91/5.00      ( k3_tarski(k2_tarski(k5_xboole_0(k1_setfam_1(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))),k3_tarski(k2_tarski(X0,X1))),k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))),k5_xboole_0(X0,k3_tarski(k2_tarski(X0,X1))))) ),
% 34.91/5.00      inference(superposition,[status(thm)],[c_4,c_4574]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_5493,plain,
% 34.91/5.00      ( k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))),k5_xboole_0(X0,k3_tarski(k2_tarski(X0,X1))))) = k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))),k3_tarski(k2_tarski(X0,X1)))) ),
% 34.91/5.00      inference(superposition,[status(thm)],[c_4,c_2064]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_10103,plain,
% 34.91/5.00      ( k3_tarski(k2_tarski(k5_xboole_0(k1_setfam_1(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))),k3_tarski(k2_tarski(X0,X1))),k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))),k3_tarski(k2_tarski(X0,X1)))) ),
% 34.91/5.00      inference(light_normalisation,[status(thm)],[c_9974,c_5493]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_3061,plain,
% 34.91/5.00      ( k3_tarski(k2_tarski(k5_xboole_0(X0,X1),k3_tarski(k2_tarski(X1,X0)))) = k3_tarski(k2_tarski(X0,X1)) ),
% 34.91/5.00      inference(superposition,[status(thm)],[c_6,c_1520]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_3217,plain,
% 34.91/5.00      ( k3_tarski(k2_tarski(k5_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),X0),X0)) = k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)) ),
% 34.91/5.00      inference(superposition,[status(thm)],[c_3,c_3061]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_4530,plain,
% 34.91/5.00      ( k3_tarski(k2_tarski(k5_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),X1),X1)) = k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X1,X0)),X1)) ),
% 34.91/5.00      inference(superposition,[status(thm)],[c_6,c_3217]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_1429,plain,
% 34.91/5.00      ( k3_tarski(k2_tarski(X0,k1_setfam_1(k2_tarski(X1,X0)))) = X0 ),
% 34.91/5.00      inference(superposition,[status(thm)],[c_6,c_3]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_3220,plain,
% 34.91/5.00      ( k3_tarski(k2_tarski(k5_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),X1),X1)) = k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),X1)) ),
% 34.91/5.00      inference(superposition,[status(thm)],[c_1429,c_3061]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_4528,plain,
% 34.91/5.00      ( k3_tarski(k2_tarski(X0,k5_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),X0))) = k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)) ),
% 34.91/5.00      inference(superposition,[status(thm)],[c_6,c_3217]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_4537,plain,
% 34.91/5.00      ( k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)))) = k3_tarski(k2_tarski(X0,k5_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),X0))) ),
% 34.91/5.00      inference(superposition,[status(thm)],[c_3217,c_1432]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_4538,plain,
% 34.91/5.00      ( k3_tarski(k2_tarski(X0,k5_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),X0))) = X0 ),
% 34.91/5.00      inference(demodulation,[status(thm)],[c_4537,c_3,c_1432]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_4543,plain,
% 34.91/5.00      ( k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)) = X0 ),
% 34.91/5.00      inference(demodulation,[status(thm)],[c_4528,c_4538]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_4627,plain,
% 34.91/5.00      ( k3_tarski(k2_tarski(k5_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),X1),X1)) = X1 ),
% 34.91/5.00      inference(demodulation,[status(thm)],[c_4530,c_3220,c_4543]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_10104,plain,
% 34.91/5.00      ( k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))),k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(X0,X1)) ),
% 34.91/5.00      inference(demodulation,[status(thm)],[c_10103,c_4627]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_15987,plain,
% 34.91/5.00      ( k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X0)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0))) = k3_tarski(k2_tarski(X0,X1)) ),
% 34.91/5.00      inference(light_normalisation,
% 34.91/5.00                [status(thm)],
% 34.91/5.00                [c_5643,c_5643,c_10104]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_15991,plain,
% 34.91/5.00      ( k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0))) = k3_tarski(k2_tarski(X0,X1)) ),
% 34.91/5.00      inference(superposition,[status(thm)],[c_6,c_15987]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_16415,plain,
% 34.91/5.00      ( k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X0,k3_tarski(k2_tarski(X1,X0)))),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0))) = k3_tarski(k2_tarski(X0,X1)) ),
% 34.91/5.00      inference(superposition,[status(thm)],[c_6,c_15991]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_17023,plain,
% 34.91/5.00      ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k1_setfam_1(k2_tarski(X1,k3_tarski(k2_tarski(X0,X1)))))) = k3_tarski(k2_tarski(X1,X0)) ),
% 34.91/5.00      inference(superposition,[status(thm)],[c_6,c_16415]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_17372,plain,
% 34.91/5.00      ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k1_setfam_1(k2_tarski(X0,X1))),k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)))))) = k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),k5_xboole_0(X0,X1))) ),
% 34.91/5.00      inference(superposition,[status(thm)],[c_5,c_17023]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_20462,plain,
% 34.91/5.00      ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k1_setfam_1(k2_tarski(k5_xboole_0(X0,X1),k1_setfam_1(k2_tarski(X0,X1))))),k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(k5_xboole_0(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))),k3_tarski(k2_tarski(X0,X1)))))) = k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(k5_xboole_0(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))),k5_xboole_0(k5_xboole_0(X0,X1),k1_setfam_1(k2_tarski(X0,X1))))) ),
% 34.91/5.00      inference(superposition,[status(thm)],[c_5,c_17372]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_20739,plain,
% 34.91/5.00      ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k1_setfam_1(k2_tarski(k5_xboole_0(X0,X1),k1_setfam_1(k2_tarski(X0,X1))))),k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(k5_xboole_0(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))),k3_tarski(k2_tarski(X0,X1)))))) = k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(k5_xboole_0(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))),k3_tarski(k2_tarski(X0,X1)))) ),
% 34.91/5.00      inference(light_normalisation,[status(thm)],[c_20462,c_5494]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_1517,plain,
% 34.91/5.00      ( k3_tarski(k2_tarski(k5_xboole_0(X0,X1),k1_setfam_1(k2_tarski(X1,X0)))) = k3_tarski(k2_tarski(X0,X1)) ),
% 34.91/5.00      inference(superposition,[status(thm)],[c_6,c_5]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_20740,plain,
% 34.91/5.00      ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),k1_setfam_1(k2_tarski(k5_xboole_0(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))))) = k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(k5_xboole_0(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))),k3_tarski(k2_tarski(X0,X1)))) ),
% 34.91/5.00      inference(demodulation,[status(thm)],[c_20739,c_1517]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_28481,plain,
% 34.91/5.00      ( k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(k5_xboole_0(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))),k5_xboole_0(k5_xboole_0(X0,X1),k1_setfam_1(k2_tarski(X0,X1))))) = k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),k1_setfam_1(k2_tarski(k5_xboole_0(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))))) ),
% 34.91/5.00      inference(light_normalisation,
% 34.91/5.00                [status(thm)],
% 34.91/5.00                [c_5494,c_5494,c_20740]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_28573,plain,
% 34.91/5.00      ( k3_tarski(k2_tarski(k5_xboole_0(k1_setfam_1(k2_tarski(k5_xboole_0(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))),k5_xboole_0(k5_xboole_0(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))),k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),k1_setfam_1(k2_tarski(k5_xboole_0(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))))))) = k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(k5_xboole_0(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))),k5_xboole_0(k5_xboole_0(X0,X1),k1_setfam_1(k2_tarski(X0,X1))))) ),
% 34.91/5.00      inference(superposition,[status(thm)],[c_28481,c_1520]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_3219,plain,
% 34.91/5.00      ( k3_tarski(k2_tarski(k5_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),k5_xboole_0(X0,X1)),k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),k5_xboole_0(X0,X1))) ),
% 34.91/5.00      inference(superposition,[status(thm)],[c_5,c_3061]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_6760,plain,
% 34.91/5.00      ( k3_tarski(k2_tarski(k5_xboole_0(k1_setfam_1(k2_tarski(k5_xboole_0(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))),k5_xboole_0(k5_xboole_0(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))),k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(k5_xboole_0(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))),k5_xboole_0(k5_xboole_0(X0,X1),k1_setfam_1(k2_tarski(X0,X1))))) ),
% 34.91/5.00      inference(superposition,[status(thm)],[c_5,c_3219]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_6843,plain,
% 34.91/5.00      ( k3_tarski(k2_tarski(k5_xboole_0(k1_setfam_1(k2_tarski(k5_xboole_0(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))),k5_xboole_0(k5_xboole_0(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))),k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(k5_xboole_0(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))),k3_tarski(k2_tarski(X0,X1)))) ),
% 34.91/5.00      inference(light_normalisation,[status(thm)],[c_6760,c_5494]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_28483,plain,
% 34.91/5.00      ( k3_tarski(k2_tarski(k5_xboole_0(k5_xboole_0(X0,X1),k1_setfam_1(k2_tarski(X0,X1))),k1_setfam_1(k2_tarski(k5_xboole_0(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))))) = k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),k1_setfam_1(k2_tarski(k5_xboole_0(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))))) ),
% 34.91/5.00      inference(superposition,[status(thm)],[c_6,c_28481]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_28668,plain,
% 34.91/5.00      ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),k1_setfam_1(k2_tarski(k5_xboole_0(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))))) = k3_tarski(k2_tarski(X0,X1)) ),
% 34.91/5.00      inference(demodulation,[status(thm)],[c_28483,c_5]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_28707,plain,
% 34.91/5.00      ( k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(k5_xboole_0(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))),k5_xboole_0(k5_xboole_0(X0,X1),k1_setfam_1(k2_tarski(X0,X1))))) = k3_tarski(k2_tarski(X0,X1)) ),
% 34.91/5.00      inference(demodulation,[status(thm)],[c_28668,c_28481]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_28862,plain,
% 34.91/5.00      ( k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(k5_xboole_0(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))),k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(X0,X1)) ),
% 34.91/5.00      inference(light_normalisation,
% 34.91/5.00                [status(thm)],
% 34.91/5.00                [c_28573,c_6843,c_28668,c_28707]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_43755,plain,
% 34.91/5.00      ( k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),k5_xboole_0(X0,X1))),k5_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),k5_xboole_0(X0,X1)))) = k3_tarski(k2_tarski(X0,X1)) ),
% 34.91/5.00      inference(light_normalisation,
% 34.91/5.00                [status(thm)],
% 34.91/5.00                [c_5644,c_5644,c_28862]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_43757,plain,
% 34.91/5.00      ( k3_tarski(k2_tarski(k5_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),k5_xboole_0(X0,X1)),k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),k5_xboole_0(X0,X1))))) = k3_tarski(k2_tarski(X0,X1)) ),
% 34.91/5.00      inference(superposition,[status(thm)],[c_6,c_43755]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_44150,plain,
% 34.91/5.00      ( k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),k5_xboole_0(X0,X1))) = k3_tarski(k2_tarski(X0,X1)) ),
% 34.91/5.00      inference(superposition,[status(thm)],[c_43757,c_5]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_44345,plain,
% 34.91/5.00      ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(X0,X1)),k1_setfam_1(k2_tarski(k5_xboole_0(X0,X1),k3_tarski(k2_tarski(X0,X1)))))) = k3_tarski(k2_tarski(k5_xboole_0(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))) ),
% 34.91/5.00      inference(superposition,[status(thm)],[c_44150,c_17023]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_44392,plain,
% 34.91/5.00      ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(X0,X1)),k1_setfam_1(k2_tarski(k5_xboole_0(X0,X1),k3_tarski(k2_tarski(X0,X1)))))) = k3_tarski(k2_tarski(X0,X1)) ),
% 34.91/5.00      inference(light_normalisation,[status(thm)],[c_44345,c_5]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_49869,plain,
% 34.91/5.00      ( k3_tarski(k2_tarski(k5_xboole_0(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))),k1_setfam_1(k2_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0)))) = k3_tarski(k2_tarski(X0,k1_setfam_1(k2_tarski(X0,X1)))) ),
% 34.91/5.00      inference(superposition,[status(thm)],[c_3,c_44392]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_50222,plain,
% 34.91/5.00      ( k3_tarski(k2_tarski(k5_xboole_0(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))),k1_setfam_1(k2_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0)))) = X0 ),
% 34.91/5.00      inference(light_normalisation,[status(thm)],[c_49869,c_3]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_50524,plain,
% 34.91/5.00      ( k3_tarski(k2_tarski(k5_xboole_0(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))),k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))))) = X0 ),
% 34.91/5.00      inference(superposition,[status(thm)],[c_6,c_50222]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_50687,plain,
% 34.91/5.00      ( k3_tarski(k2_tarski(k5_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0)),k1_setfam_1(k2_tarski(sK1,k7_subset_1(u1_struct_0(sK0),sK1,X0))))) = sK1 ),
% 34.91/5.00      inference(superposition,[status(thm)],[c_1841,c_50524]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_51040,plain,
% 34.91/5.00      ( k2_pre_topc(sK0,sK1) = sK1
% 34.91/5.00      | k3_tarski(k2_tarski(k5_xboole_0(sK1,k2_tops_1(sK0,sK1)),k1_setfam_1(k2_tarski(sK1,k2_tops_1(sK0,sK1))))) = sK1 ),
% 34.91/5.00      inference(superposition,[status(thm)],[c_4243,c_50687]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_10,plain,
% 34.91/5.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 34.91/5.00      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 34.91/5.00      | ~ l1_pre_topc(X1) ),
% 34.91/5.00      inference(cnf_transformation,[],[f53]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_294,plain,
% 34.91/5.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 34.91/5.00      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 34.91/5.00      | sK0 != X1 ),
% 34.91/5.00      inference(resolution_lifted,[status(thm)],[c_10,c_18]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_295,plain,
% 34.91/5.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 34.91/5.00      | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 34.91/5.00      inference(unflattening,[status(thm)],[c_294]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_993,plain,
% 34.91/5.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 34.91/5.00      | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 34.91/5.00      inference(predicate_to_equality,[status(thm)],[c_295]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_7,plain,
% 34.91/5.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 34.91/5.00      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 34.91/5.00      | k4_subset_1(X1,X2,X0) = k3_tarski(k2_tarski(X2,X0)) ),
% 34.91/5.00      inference(cnf_transformation,[],[f67]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_1002,plain,
% 34.91/5.00      ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
% 34.91/5.00      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
% 34.91/5.00      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 34.91/5.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_9879,plain,
% 34.91/5.00      ( k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X1)) = k3_tarski(k2_tarski(X0,k2_tops_1(sK0,X1)))
% 34.91/5.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 34.91/5.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 34.91/5.00      inference(superposition,[status(thm)],[c_993,c_1002]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_13075,plain,
% 34.91/5.00      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,X0)))
% 34.91/5.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 34.91/5.00      inference(superposition,[status(thm)],[c_998,c_9879]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_13113,plain,
% 34.91/5.00      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
% 34.91/5.00      inference(superposition,[status(thm)],[c_998,c_13075]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_14,plain,
% 34.91/5.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 34.91/5.00      | ~ l1_pre_topc(X1)
% 34.91/5.00      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
% 34.91/5.00      inference(cnf_transformation,[],[f57]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_249,plain,
% 34.91/5.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 34.91/5.00      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0)
% 34.91/5.00      | sK0 != X1 ),
% 34.91/5.00      inference(resolution_lifted,[status(thm)],[c_14,c_18]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_250,plain,
% 34.91/5.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 34.91/5.00      | k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0) ),
% 34.91/5.00      inference(unflattening,[status(thm)],[c_249]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_996,plain,
% 34.91/5.00      ( k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0)
% 34.91/5.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 34.91/5.00      inference(predicate_to_equality,[status(thm)],[c_250]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_1600,plain,
% 34.91/5.00      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 34.91/5.00      inference(superposition,[status(thm)],[c_998,c_996]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_13115,plain,
% 34.91/5.00      ( k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k2_pre_topc(sK0,sK1) ),
% 34.91/5.00      inference(light_normalisation,[status(thm)],[c_13113,c_1600]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_51139,plain,
% 34.91/5.00      ( k2_pre_topc(sK0,sK1) = sK1 ),
% 34.91/5.00      inference(demodulation,[status(thm)],[c_51040,c_5,c_13115]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_12,plain,
% 34.91/5.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 34.91/5.00      | ~ l1_pre_topc(X1)
% 34.91/5.00      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
% 34.91/5.00      inference(cnf_transformation,[],[f55]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_282,plain,
% 34.91/5.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 34.91/5.00      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0)
% 34.91/5.00      | sK0 != X1 ),
% 34.91/5.00      inference(resolution_lifted,[status(thm)],[c_12,c_18]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_283,plain,
% 34.91/5.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 34.91/5.00      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
% 34.91/5.00      inference(unflattening,[status(thm)],[c_282]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_994,plain,
% 34.91/5.00      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0)
% 34.91/5.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 34.91/5.00      inference(predicate_to_equality,[status(thm)],[c_283]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_1365,plain,
% 34.91/5.00      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 34.91/5.00      inference(superposition,[status(thm)],[c_998,c_994]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_52342,plain,
% 34.91/5.00      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 34.91/5.00      inference(demodulation,[status(thm)],[c_51139,c_1365]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_619,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_1095,plain,
% 34.91/5.00      ( X0 != X1 | sK1 != X1 | sK1 = X0 ),
% 34.91/5.00      inference(instantiation,[status(thm)],[c_619]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_1263,plain,
% 34.91/5.00      ( X0 != sK1 | sK1 = X0 | sK1 != sK1 ),
% 34.91/5.00      inference(instantiation,[status(thm)],[c_1095]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_49403,plain,
% 34.91/5.00      ( k2_pre_topc(sK0,sK1) != sK1
% 34.91/5.00      | sK1 = k2_pre_topc(sK0,sK1)
% 34.91/5.00      | sK1 != sK1 ),
% 34.91/5.00      inference(instantiation,[status(thm)],[c_1263]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_632,plain,
% 34.91/5.00      ( ~ v4_pre_topc(X0,X1) | v4_pre_topc(X2,X3) | X2 != X0 | X3 != X1 ),
% 34.91/5.00      theory(equality) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_1027,plain,
% 34.91/5.00      ( ~ v4_pre_topc(X0,X1)
% 34.91/5.00      | v4_pre_topc(sK1,sK0)
% 34.91/5.00      | sK1 != X0
% 34.91/5.00      | sK0 != X1 ),
% 34.91/5.00      inference(instantiation,[status(thm)],[c_632]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_49328,plain,
% 34.91/5.00      ( ~ v4_pre_topc(k2_pre_topc(sK0,sK1),X0)
% 34.91/5.00      | v4_pre_topc(sK1,sK0)
% 34.91/5.00      | sK1 != k2_pre_topc(sK0,sK1)
% 34.91/5.00      | sK0 != X0 ),
% 34.91/5.00      inference(instantiation,[status(thm)],[c_1027]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_49330,plain,
% 34.91/5.00      ( ~ v4_pre_topc(k2_pre_topc(sK0,sK1),sK0)
% 34.91/5.00      | v4_pre_topc(sK1,sK0)
% 34.91/5.00      | sK1 != k2_pre_topc(sK0,sK1)
% 34.91/5.00      | sK0 != sK0 ),
% 34.91/5.00      inference(instantiation,[status(thm)],[c_49328]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_1087,plain,
% 34.91/5.00      ( ~ r1_tarski(X0,sK1) | ~ r1_tarski(sK1,X0) | sK1 = X0 ),
% 34.91/5.00      inference(instantiation,[status(thm)],[c_0]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_1242,plain,
% 34.91/5.00      ( ~ r1_tarski(sK1,sK1) | sK1 = sK1 ),
% 34.91/5.00      inference(instantiation,[status(thm)],[c_1087]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_11,plain,
% 34.91/5.00      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
% 34.91/5.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 34.91/5.00      | ~ v2_pre_topc(X0)
% 34.91/5.00      | ~ l1_pre_topc(X0) ),
% 34.91/5.00      inference(cnf_transformation,[],[f54]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_19,negated_conjecture,
% 34.91/5.00      ( v2_pre_topc(sK0) ),
% 34.91/5.00      inference(cnf_transformation,[],[f58]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_228,plain,
% 34.91/5.00      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
% 34.91/5.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 34.91/5.00      | ~ l1_pre_topc(X0)
% 34.91/5.00      | sK0 != X0 ),
% 34.91/5.00      inference(resolution_lifted,[status(thm)],[c_11,c_19]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_229,plain,
% 34.91/5.00      ( v4_pre_topc(k2_pre_topc(sK0,X0),sK0)
% 34.91/5.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 34.91/5.00      | ~ l1_pre_topc(sK0) ),
% 34.91/5.00      inference(unflattening,[status(thm)],[c_228]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_233,plain,
% 34.91/5.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 34.91/5.00      | v4_pre_topc(k2_pre_topc(sK0,X0),sK0) ),
% 34.91/5.00      inference(global_propositional_subsumption,
% 34.91/5.00                [status(thm)],
% 34.91/5.00                [c_229,c_18]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_234,plain,
% 34.91/5.00      ( v4_pre_topc(k2_pre_topc(sK0,X0),sK0)
% 34.91/5.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 34.91/5.00      inference(renaming,[status(thm)],[c_233]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_1032,plain,
% 34.91/5.00      ( v4_pre_topc(k2_pre_topc(sK0,sK1),sK0)
% 34.91/5.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 34.91/5.00      inference(instantiation,[status(thm)],[c_234]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_58,plain,
% 34.91/5.00      ( ~ r1_tarski(sK0,sK0) | sK0 = sK0 ),
% 34.91/5.00      inference(instantiation,[status(thm)],[c_0]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_2,plain,
% 34.91/5.00      ( r1_tarski(X0,X0) ),
% 34.91/5.00      inference(cnf_transformation,[],[f70]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_54,plain,
% 34.91/5.00      ( r1_tarski(sK0,sK0) ),
% 34.91/5.00      inference(instantiation,[status(thm)],[c_2]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(c_15,negated_conjecture,
% 34.91/5.00      ( ~ v4_pre_topc(sK1,sK0)
% 34.91/5.00      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
% 34.91/5.00      inference(cnf_transformation,[],[f62]) ).
% 34.91/5.00  
% 34.91/5.00  cnf(contradiction,plain,
% 34.91/5.00      ( $false ),
% 34.91/5.00      inference(minisat,
% 34.91/5.00                [status(thm)],
% 34.91/5.00                [c_52342,c_51139,c_49403,c_49330,c_1375,c_1242,c_1032,
% 34.91/5.00                 c_58,c_54,c_15,c_17]) ).
% 34.91/5.00  
% 34.91/5.00  
% 34.91/5.00  % SZS output end CNFRefutation for theBenchmark.p
% 34.91/5.00  
% 34.91/5.00  ------                               Statistics
% 34.91/5.00  
% 34.91/5.00  ------ General
% 34.91/5.00  
% 34.91/5.00  abstr_ref_over_cycles:                  0
% 34.91/5.00  abstr_ref_under_cycles:                 0
% 34.91/5.00  gc_basic_clause_elim:                   0
% 34.91/5.00  forced_gc_time:                         0
% 34.91/5.00  parsing_time:                           0.01
% 34.91/5.00  unif_index_cands_time:                  0.
% 34.91/5.00  unif_index_add_time:                    0.
% 34.91/5.00  orderings_time:                         0.
% 34.91/5.00  out_proof_time:                         0.02
% 34.91/5.00  total_time:                             4.209
% 34.91/5.00  num_of_symbols:                         49
% 34.91/5.00  num_of_terms:                           99423
% 34.91/5.00  
% 34.91/5.00  ------ Preprocessing
% 34.91/5.00  
% 34.91/5.00  num_of_splits:                          0
% 34.91/5.00  num_of_split_atoms:                     0
% 34.91/5.00  num_of_reused_defs:                     0
% 34.91/5.00  num_eq_ax_congr_red:                    10
% 34.91/5.00  num_of_sem_filtered_clauses:            1
% 34.91/5.00  num_of_subtypes:                        0
% 34.91/5.00  monotx_restored_types:                  0
% 34.91/5.00  sat_num_of_epr_types:                   0
% 34.91/5.00  sat_num_of_non_cyclic_types:            0
% 34.91/5.00  sat_guarded_non_collapsed_types:        0
% 34.91/5.00  num_pure_diseq_elim:                    0
% 34.91/5.00  simp_replaced_by:                       0
% 34.91/5.00  res_preprocessed:                       103
% 34.91/5.00  prep_upred:                             0
% 34.91/5.00  prep_unflattend:                        10
% 34.91/5.00  smt_new_axioms:                         0
% 34.91/5.00  pred_elim_cands:                        3
% 34.91/5.00  pred_elim:                              2
% 34.91/5.00  pred_elim_cl:                           2
% 34.91/5.00  pred_elim_cycles:                       4
% 34.91/5.00  merged_defs:                            8
% 34.91/5.00  merged_defs_ncl:                        0
% 34.91/5.00  bin_hyper_res:                          8
% 34.91/5.00  prep_cycles:                            4
% 34.91/5.00  pred_elim_time:                         0.005
% 34.91/5.00  splitting_time:                         0.
% 34.91/5.00  sem_filter_time:                        0.
% 34.91/5.00  monotx_time:                            0.
% 34.91/5.00  subtype_inf_time:                       0.
% 34.91/5.00  
% 34.91/5.00  ------ Problem properties
% 34.91/5.00  
% 34.91/5.00  clauses:                                17
% 34.91/5.00  conjectures:                            3
% 34.91/5.00  epr:                                    2
% 34.91/5.00  horn:                                   16
% 34.91/5.00  ground:                                 3
% 34.91/5.00  unary:                                  6
% 34.91/5.00  binary:                                 8
% 34.91/5.00  lits:                                   33
% 34.91/5.00  lits_eq:                                11
% 34.91/5.00  fd_pure:                                0
% 34.91/5.00  fd_pseudo:                              0
% 34.91/5.00  fd_cond:                                0
% 34.91/5.00  fd_pseudo_cond:                         1
% 34.91/5.00  ac_symbols:                             0
% 34.91/5.00  
% 34.91/5.00  ------ Propositional Solver
% 34.91/5.00  
% 34.91/5.00  prop_solver_calls:                      34
% 34.91/5.00  prop_fast_solver_calls:                 1050
% 34.91/5.00  smt_solver_calls:                       0
% 34.91/5.00  smt_fast_solver_calls:                  0
% 34.91/5.00  prop_num_of_clauses:                    21729
% 34.91/5.00  prop_preprocess_simplified:             24267
% 34.91/5.00  prop_fo_subsumed:                       6
% 34.91/5.00  prop_solver_time:                       0.
% 34.91/5.00  smt_solver_time:                        0.
% 34.91/5.00  smt_fast_solver_time:                   0.
% 34.91/5.00  prop_fast_solver_time:                  0.
% 34.91/5.00  prop_unsat_core_time:                   0.002
% 34.91/5.00  
% 34.91/5.00  ------ QBF
% 34.91/5.00  
% 34.91/5.00  qbf_q_res:                              0
% 34.91/5.00  qbf_num_tautologies:                    0
% 34.91/5.00  qbf_prep_cycles:                        0
% 34.91/5.00  
% 34.91/5.00  ------ BMC1
% 34.91/5.00  
% 34.91/5.00  bmc1_current_bound:                     -1
% 34.91/5.00  bmc1_last_solved_bound:                 -1
% 34.91/5.00  bmc1_unsat_core_size:                   -1
% 34.91/5.00  bmc1_unsat_core_parents_size:           -1
% 34.91/5.00  bmc1_merge_next_fun:                    0
% 34.91/5.00  bmc1_unsat_core_clauses_time:           0.
% 34.91/5.00  
% 34.91/5.00  ------ Instantiation
% 34.91/5.00  
% 34.91/5.00  inst_num_of_clauses:                    3584
% 34.91/5.00  inst_num_in_passive:                    1667
% 34.91/5.00  inst_num_in_active:                     1691
% 34.91/5.00  inst_num_in_unprocessed:                226
% 34.91/5.00  inst_num_of_loops:                      1880
% 34.91/5.00  inst_num_of_learning_restarts:          0
% 34.91/5.00  inst_num_moves_active_passive:          184
% 34.91/5.00  inst_lit_activity:                      0
% 34.91/5.00  inst_lit_activity_moves:                1
% 34.91/5.00  inst_num_tautologies:                   0
% 34.91/5.00  inst_num_prop_implied:                  0
% 34.91/5.00  inst_num_existing_simplified:           0
% 34.91/5.00  inst_num_eq_res_simplified:             0
% 34.91/5.00  inst_num_child_elim:                    0
% 34.91/5.00  inst_num_of_dismatching_blockings:      2233
% 34.91/5.00  inst_num_of_non_proper_insts:           4362
% 34.91/5.00  inst_num_of_duplicates:                 0
% 34.91/5.00  inst_inst_num_from_inst_to_res:         0
% 34.91/5.00  inst_dismatching_checking_time:         0.
% 34.91/5.00  
% 34.91/5.00  ------ Resolution
% 34.91/5.00  
% 34.91/5.00  res_num_of_clauses:                     0
% 34.91/5.00  res_num_in_passive:                     0
% 34.91/5.00  res_num_in_active:                      0
% 34.91/5.00  res_num_of_loops:                       107
% 34.91/5.00  res_forward_subset_subsumed:            201
% 34.91/5.00  res_backward_subset_subsumed:           0
% 34.91/5.00  res_forward_subsumed:                   0
% 34.91/5.00  res_backward_subsumed:                  0
% 34.91/5.00  res_forward_subsumption_resolution:     0
% 34.91/5.00  res_backward_subsumption_resolution:    0
% 34.91/5.00  res_clause_to_clause_subsumption:       104890
% 34.91/5.00  res_orphan_elimination:                 0
% 34.91/5.00  res_tautology_del:                      340
% 34.91/5.00  res_num_eq_res_simplified:              0
% 34.91/5.00  res_num_sel_changes:                    0
% 34.91/5.00  res_moves_from_active_to_pass:          0
% 34.91/5.00  
% 34.91/5.00  ------ Superposition
% 34.91/5.00  
% 34.91/5.00  sup_time_total:                         0.
% 34.91/5.00  sup_time_generating:                    0.
% 34.91/5.00  sup_time_sim_full:                      0.
% 34.91/5.00  sup_time_sim_immed:                     0.
% 34.91/5.00  
% 34.91/5.00  sup_num_of_clauses:                     6700
% 34.91/5.00  sup_num_in_active:                      337
% 34.91/5.00  sup_num_in_passive:                     6363
% 34.91/5.00  sup_num_of_loops:                       375
% 34.91/5.00  sup_fw_superposition:                   8628
% 34.91/5.00  sup_bw_superposition:                   8209
% 34.91/5.00  sup_immediate_simplified:               9243
% 34.91/5.00  sup_given_eliminated:                   2
% 34.91/5.00  comparisons_done:                       0
% 34.91/5.00  comparisons_avoided:                    3
% 34.91/5.00  
% 34.91/5.00  ------ Simplifications
% 34.91/5.00  
% 34.91/5.00  
% 34.91/5.00  sim_fw_subset_subsumed:                 0
% 34.91/5.00  sim_bw_subset_subsumed:                 33
% 34.91/5.00  sim_fw_subsumed:                        309
% 34.91/5.00  sim_bw_subsumed:                        73
% 34.91/5.00  sim_fw_subsumption_res:                 0
% 34.91/5.00  sim_bw_subsumption_res:                 0
% 34.91/5.00  sim_tautology_del:                      0
% 34.91/5.00  sim_eq_tautology_del:                   1438
% 34.91/5.00  sim_eq_res_simp:                        0
% 34.91/5.00  sim_fw_demodulated:                     5016
% 34.91/5.00  sim_bw_demodulated:                     346
% 34.91/5.00  sim_light_normalised:                   4366
% 34.91/5.00  sim_joinable_taut:                      0
% 34.91/5.00  sim_joinable_simp:                      0
% 34.91/5.00  sim_ac_normalised:                      0
% 34.91/5.00  sim_smt_subsumption:                    0
% 34.91/5.00  
%------------------------------------------------------------------------------
