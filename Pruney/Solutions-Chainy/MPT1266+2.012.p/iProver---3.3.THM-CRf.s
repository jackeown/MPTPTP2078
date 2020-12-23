%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:14:59 EST 2020

% Result     : Theorem 15.33s
% Output     : CNFRefutation 15.33s
% Verified   : 
% Statistics : Number of formulae       :  184 (1240 expanded)
%              Number of clauses        :  111 ( 458 expanded)
%              Number of leaves         :   22 ( 258 expanded)
%              Depth                    :   27
%              Number of atoms          :  477 (4233 expanded)
%              Number of equality atoms :  262 (1520 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f57,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f31])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f32,f33])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f52,f49])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f48,f49])).

fof(f17,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tops_1(X1,X0)
            <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_1(X1,X0)
          <~> k1_xboole_0 = k1_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k1_xboole_0 != k1_tops_1(X0,X1)
            | ~ v2_tops_1(X1,X0) )
          & ( k1_xboole_0 = k1_tops_1(X0,X1)
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k1_xboole_0 != k1_tops_1(X0,X1)
            | ~ v2_tops_1(X1,X0) )
          & ( k1_xboole_0 = k1_tops_1(X0,X1)
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f39])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( k1_xboole_0 != k1_tops_1(X0,X1)
            | ~ v2_tops_1(X1,X0) )
          & ( k1_xboole_0 = k1_tops_1(X0,X1)
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( k1_xboole_0 != k1_tops_1(X0,sK2)
          | ~ v2_tops_1(sK2,X0) )
        & ( k1_xboole_0 = k1_tops_1(X0,sK2)
          | v2_tops_1(sK2,X0) )
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k1_xboole_0 != k1_tops_1(X0,X1)
              | ~ v2_tops_1(X1,X0) )
            & ( k1_xboole_0 = k1_tops_1(X0,X1)
              | v2_tops_1(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k1_xboole_0 != k1_tops_1(sK1,X1)
            | ~ v2_tops_1(X1,sK1) )
          & ( k1_xboole_0 = k1_tops_1(sK1,X1)
            | v2_tops_1(X1,sK1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) )
      & l1_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ( k1_xboole_0 != k1_tops_1(sK1,sK2)
      | ~ v2_tops_1(sK2,sK1) )
    & ( k1_xboole_0 = k1_tops_1(sK1,sK2)
      | v2_tops_1(sK2,sK1) )
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    & l1_pre_topc(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f40,f42,f41])).

fof(f68,plain,
    ( k1_xboole_0 = k1_tops_1(sK1,sK2)
    | v2_tops_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f66,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f60,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f58,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f67,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f43])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

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

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f47,f49])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v1_tops_1(X1,X0)
      | k2_struct_0(X0) != k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f5,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f9,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f70,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f55,f50])).

fof(f73,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f51,f70])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v2_tops_1(X1,X0)
      | ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f69,plain,
    ( k1_xboole_0 != k1_tops_1(sK1,sK2)
    | ~ v2_tops_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_9,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_849,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_853,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_854,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1890,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_853,c_854])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_165,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_9])).

cnf(c_166,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_165])).

cnf(c_210,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_6,c_166])).

cnf(c_835,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_210])).

cnf(c_4944,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k3_subset_1(X0,X0) ),
    inference(superposition,[status(thm)],[c_1890,c_835])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_851,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3581,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1890,c_851])).

cnf(c_4960,plain,
    ( k3_subset_1(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4944,c_3581])).

cnf(c_20,negated_conjecture,
    ( v2_tops_1(sK2,sK1)
    | k1_xboole_0 = k1_tops_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_838,plain,
    ( k1_xboole_0 = k1_tops_1(sK1,sK2)
    | v2_tops_1(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_22,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_836,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_13,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_845,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1080,plain,
    ( l1_struct_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_836,c_845])).

cnf(c_11,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_847,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1154,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(superposition,[status(thm)],[c_1080,c_847])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_837,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_848,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1263,plain,
    ( r1_tarski(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_837,c_848])).

cnf(c_1544,plain,
    ( r1_tarski(sK2,k2_struct_0(sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1154,c_1263])).

cnf(c_18,plain,
    ( ~ v2_tops_1(X0,X1)
    | v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_840,plain,
    ( v2_tops_1(X0,X1) != iProver_top
    | v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1552,plain,
    ( v2_tops_1(X0,sK1) != iProver_top
    | v1_tops_1(k3_subset_1(k2_struct_0(sK1),X0),sK1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1154,c_840])).

cnf(c_1553,plain,
    ( v2_tops_1(X0,sK1) != iProver_top
    | v1_tops_1(k3_subset_1(k2_struct_0(sK1),X0),sK1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1552,c_1154])).

cnf(c_23,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1611,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | v1_tops_1(k3_subset_1(k2_struct_0(sK1),X0),sK1) = iProver_top
    | v2_tops_1(X0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1553,c_23])).

cnf(c_1612,plain,
    ( v2_tops_1(X0,sK1) != iProver_top
    | v1_tops_1(k3_subset_1(k2_struct_0(sK1),X0),sK1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_1611])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_211,plain,
    ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
    | ~ r1_tarski(X1,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_7,c_166])).

cnf(c_834,plain,
    ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) = iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_211])).

cnf(c_16,plain,
    ( ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = k2_struct_0(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_842,plain,
    ( k2_pre_topc(X0,X1) = k2_struct_0(X0)
    | v1_tops_1(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2624,plain,
    ( k2_pre_topc(sK1,X0) = k2_struct_0(sK1)
    | v1_tops_1(X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1154,c_842])).

cnf(c_2996,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | v1_tops_1(X0,sK1) != iProver_top
    | k2_pre_topc(sK1,X0) = k2_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2624,c_23])).

cnf(c_2997,plain,
    ( k2_pre_topc(sK1,X0) = k2_struct_0(sK1)
    | v1_tops_1(X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2996])).

cnf(c_3854,plain,
    ( k2_pre_topc(sK1,k3_subset_1(k2_struct_0(sK1),X0)) = k2_struct_0(sK1)
    | v1_tops_1(k3_subset_1(k2_struct_0(sK1),X0),sK1) != iProver_top
    | r1_tarski(X0,k2_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_834,c_2997])).

cnf(c_7519,plain,
    ( k2_pre_topc(sK1,k3_subset_1(k2_struct_0(sK1),X0)) = k2_struct_0(sK1)
    | v2_tops_1(X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | r1_tarski(X0,k2_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1612,c_3854])).

cnf(c_9127,plain,
    ( k2_pre_topc(sK1,k3_subset_1(k2_struct_0(sK1),X0)) = k2_struct_0(sK1)
    | v2_tops_1(X0,sK1) != iProver_top
    | r1_tarski(X0,k2_struct_0(sK1)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_7519,c_849])).

cnf(c_9133,plain,
    ( k2_pre_topc(sK1,k3_subset_1(k2_struct_0(sK1),sK2)) = k2_struct_0(sK1)
    | v2_tops_1(sK2,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1544,c_9127])).

cnf(c_9211,plain,
    ( k1_tops_1(sK1,sK2) = k1_xboole_0
    | k2_pre_topc(sK1,k3_subset_1(k2_struct_0(sK1),sK2)) = k2_struct_0(sK1) ),
    inference(superposition,[status(thm)],[c_838,c_9133])).

cnf(c_1545,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1154,c_837])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_844,plain,
    ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2741,plain,
    ( k3_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),X0))) = k1_tops_1(sK1,X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1154,c_844])).

cnf(c_2745,plain,
    ( k3_subset_1(k2_struct_0(sK1),k2_pre_topc(sK1,k3_subset_1(k2_struct_0(sK1),X0))) = k1_tops_1(sK1,X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2741,c_1154])).

cnf(c_3159,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | k3_subset_1(k2_struct_0(sK1),k2_pre_topc(sK1,k3_subset_1(k2_struct_0(sK1),X0))) = k1_tops_1(sK1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2745,c_23])).

cnf(c_3160,plain,
    ( k3_subset_1(k2_struct_0(sK1),k2_pre_topc(sK1,k3_subset_1(k2_struct_0(sK1),X0))) = k1_tops_1(sK1,X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_3159])).

cnf(c_3168,plain,
    ( k3_subset_1(k2_struct_0(sK1),k2_pre_topc(sK1,k3_subset_1(k2_struct_0(sK1),sK2))) = k1_tops_1(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_1545,c_3160])).

cnf(c_9306,plain,
    ( k1_tops_1(sK1,sK2) = k1_xboole_0
    | k3_subset_1(k2_struct_0(sK1),k2_struct_0(sK1)) = k1_tops_1(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_9211,c_3168])).

cnf(c_34147,plain,
    ( k1_tops_1(sK1,sK2) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4960,c_9306])).

cnf(c_3850,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k3_subset_1(X1,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_834,c_848])).

cnf(c_4911,plain,
    ( k5_xboole_0(k3_subset_1(X0,X1),k3_xboole_0(k3_subset_1(X0,X1),X0)) = k1_xboole_0
    | r1_tarski(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3850,c_851])).

cnf(c_5944,plain,
    ( k5_xboole_0(k3_subset_1(k2_struct_0(sK1),sK2),k3_xboole_0(k3_subset_1(k2_struct_0(sK1),sK2),k2_struct_0(sK1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1544,c_4911])).

cnf(c_4,plain,
    ( r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_850,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_6298,plain,
    ( r1_tarski(k3_subset_1(k2_struct_0(sK1),sK2),k2_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5944,c_850])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_846,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1954,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(k2_pre_topc(X1,X0),u1_struct_0(X1)) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_846,c_848])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_212,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(bin_hyper_res,[status(thm)],[c_8,c_166])).

cnf(c_833,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_212])).

cnf(c_3684,plain,
    ( k3_subset_1(u1_struct_0(X0),k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1))) = k2_pre_topc(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1954,c_833])).

cnf(c_14123,plain,
    ( k3_subset_1(u1_struct_0(X0),k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1))) = k2_pre_topc(X0,X1)
    | r1_tarski(X1,u1_struct_0(X0)) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_849,c_3684])).

cnf(c_14273,plain,
    ( k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,X0))) = k2_pre_topc(sK1,X0)
    | r1_tarski(X0,k2_struct_0(sK1)) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1154,c_14123])).

cnf(c_14277,plain,
    ( k3_subset_1(k2_struct_0(sK1),k3_subset_1(k2_struct_0(sK1),k2_pre_topc(sK1,X0))) = k2_pre_topc(sK1,X0)
    | r1_tarski(X0,k2_struct_0(sK1)) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_14273,c_1154])).

cnf(c_14870,plain,
    ( r1_tarski(X0,k2_struct_0(sK1)) != iProver_top
    | k3_subset_1(k2_struct_0(sK1),k3_subset_1(k2_struct_0(sK1),k2_pre_topc(sK1,X0))) = k2_pre_topc(sK1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14277,c_23])).

cnf(c_14871,plain,
    ( k3_subset_1(k2_struct_0(sK1),k3_subset_1(k2_struct_0(sK1),k2_pre_topc(sK1,X0))) = k2_pre_topc(sK1,X0)
    | r1_tarski(X0,k2_struct_0(sK1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_14870])).

cnf(c_14884,plain,
    ( k3_subset_1(k2_struct_0(sK1),k3_subset_1(k2_struct_0(sK1),k2_pre_topc(sK1,k3_subset_1(k2_struct_0(sK1),sK2)))) = k2_pre_topc(sK1,k3_subset_1(k2_struct_0(sK1),sK2)) ),
    inference(superposition,[status(thm)],[c_6298,c_14871])).

cnf(c_14901,plain,
    ( k2_pre_topc(sK1,k3_subset_1(k2_struct_0(sK1),sK2)) = k3_subset_1(k2_struct_0(sK1),k1_tops_1(sK1,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_14884,c_3168])).

cnf(c_15,plain,
    ( v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) != k2_struct_0(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_843,plain,
    ( k2_pre_topc(X0,X1) != k2_struct_0(X0)
    | v1_tops_1(X1,X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_14985,plain,
    ( k3_subset_1(k2_struct_0(sK1),k1_tops_1(sK1,sK2)) != k2_struct_0(sK1)
    | v1_tops_1(k3_subset_1(k2_struct_0(sK1),sK2),sK1) = iProver_top
    | m1_subset_1(k3_subset_1(k2_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_14901,c_843])).

cnf(c_15023,plain,
    ( k3_subset_1(k2_struct_0(sK1),k1_tops_1(sK1,sK2)) != k2_struct_0(sK1)
    | v1_tops_1(k3_subset_1(k2_struct_0(sK1),sK2),sK1) = iProver_top
    | m1_subset_1(k3_subset_1(k2_struct_0(sK1),sK2),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_14985,c_1154])).

cnf(c_15241,plain,
    ( m1_subset_1(k3_subset_1(k2_struct_0(sK1),sK2),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | v1_tops_1(k3_subset_1(k2_struct_0(sK1),sK2),sK1) = iProver_top
    | k3_subset_1(k2_struct_0(sK1),k1_tops_1(sK1,sK2)) != k2_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_15023,c_23])).

cnf(c_15242,plain,
    ( k3_subset_1(k2_struct_0(sK1),k1_tops_1(sK1,sK2)) != k2_struct_0(sK1)
    | v1_tops_1(k3_subset_1(k2_struct_0(sK1),sK2),sK1) = iProver_top
    | m1_subset_1(k3_subset_1(k2_struct_0(sK1),sK2),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_15241])).

cnf(c_35171,plain,
    ( k3_subset_1(k2_struct_0(sK1),k1_xboole_0) != k2_struct_0(sK1)
    | v1_tops_1(k3_subset_1(k2_struct_0(sK1),sK2),sK1) = iProver_top
    | m1_subset_1(k3_subset_1(k2_struct_0(sK1),sK2),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_34147,c_15242])).

cnf(c_5,plain,
    ( k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_35198,plain,
    ( k2_struct_0(sK1) != k2_struct_0(sK1)
    | v1_tops_1(k3_subset_1(k2_struct_0(sK1),sK2),sK1) = iProver_top
    | m1_subset_1(k3_subset_1(k2_struct_0(sK1),sK2),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_35171,c_5])).

cnf(c_35199,plain,
    ( v1_tops_1(k3_subset_1(k2_struct_0(sK1),sK2),sK1) = iProver_top
    | m1_subset_1(k3_subset_1(k2_struct_0(sK1),sK2),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_35198])).

cnf(c_53281,plain,
    ( v1_tops_1(k3_subset_1(k2_struct_0(sK1),sK2),sK1) = iProver_top
    | r1_tarski(k3_subset_1(k2_struct_0(sK1),sK2),k2_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_849,c_35199])).

cnf(c_55738,plain,
    ( v1_tops_1(k3_subset_1(k2_struct_0(sK1),sK2),sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_53281,c_6298])).

cnf(c_17,plain,
    ( v2_tops_1(X0,X1)
    | ~ v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_841,plain,
    ( v2_tops_1(X0,X1) = iProver_top
    | v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1786,plain,
    ( v2_tops_1(X0,sK1) = iProver_top
    | v1_tops_1(k3_subset_1(k2_struct_0(sK1),X0),sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1154,c_841])).

cnf(c_1791,plain,
    ( v2_tops_1(X0,sK1) = iProver_top
    | v1_tops_1(k3_subset_1(k2_struct_0(sK1),X0),sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1786,c_1154])).

cnf(c_2144,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | v1_tops_1(k3_subset_1(k2_struct_0(sK1),X0),sK1) != iProver_top
    | v2_tops_1(X0,sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1791,c_23])).

cnf(c_2145,plain,
    ( v2_tops_1(X0,sK1) = iProver_top
    | v1_tops_1(k3_subset_1(k2_struct_0(sK1),X0),sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2144])).

cnf(c_55744,plain,
    ( v2_tops_1(sK2,sK1) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_55738,c_2145])).

cnf(c_283,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2565,plain,
    ( X0 != X1
    | k1_xboole_0 != X1
    | k1_xboole_0 = X0 ),
    inference(instantiation,[status(thm)],[c_283])).

cnf(c_4532,plain,
    ( X0 != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2565])).

cnf(c_14074,plain,
    ( k1_tops_1(sK1,sK2) != k1_xboole_0
    | k1_xboole_0 = k1_tops_1(sK1,sK2)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4532])).

cnf(c_282,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2467,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_282])).

cnf(c_19,negated_conjecture,
    ( ~ v2_tops_1(sK2,sK1)
    | k1_xboole_0 != k1_tops_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_26,plain,
    ( k1_xboole_0 != k1_tops_1(sK1,sK2)
    | v2_tops_1(sK2,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_55744,c_34147,c_14074,c_2467,c_1545,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:55:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 15.33/2.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.33/2.49  
% 15.33/2.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.33/2.49  
% 15.33/2.49  ------  iProver source info
% 15.33/2.49  
% 15.33/2.49  git: date: 2020-06-30 10:37:57 +0100
% 15.33/2.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.33/2.49  git: non_committed_changes: false
% 15.33/2.49  git: last_make_outside_of_git: false
% 15.33/2.49  
% 15.33/2.49  ------ 
% 15.33/2.49  ------ Parsing...
% 15.33/2.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.33/2.49  
% 15.33/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 15.33/2.49  
% 15.33/2.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.33/2.49  
% 15.33/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.33/2.49  ------ Proving...
% 15.33/2.49  ------ Problem Properties 
% 15.33/2.49  
% 15.33/2.49  
% 15.33/2.49  clauses                                 23
% 15.33/2.49  conjectures                             4
% 15.33/2.49  EPR                                     3
% 15.33/2.49  Horn                                    21
% 15.33/2.49  unary                                   3
% 15.33/2.49  binary                                  13
% 15.33/2.49  lits                                    54
% 15.33/2.49  lits eq                                 11
% 15.33/2.49  fd_pure                                 0
% 15.33/2.49  fd_pseudo                               0
% 15.33/2.49  fd_cond                                 0
% 15.33/2.49  fd_pseudo_cond                          0
% 15.33/2.49  AC symbols                              0
% 15.33/2.49  
% 15.33/2.49  ------ Input Options Time Limit: Unbounded
% 15.33/2.49  
% 15.33/2.49  
% 15.33/2.49  ------ 
% 15.33/2.49  Current options:
% 15.33/2.49  ------ 
% 15.33/2.49  
% 15.33/2.49  
% 15.33/2.49  
% 15.33/2.49  
% 15.33/2.49  ------ Proving...
% 15.33/2.49  
% 15.33/2.49  
% 15.33/2.49  % SZS status Theorem for theBenchmark.p
% 15.33/2.49  
% 15.33/2.49  % SZS output start CNFRefutation for theBenchmark.p
% 15.33/2.49  
% 15.33/2.49  fof(f10,axiom,(
% 15.33/2.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 15.33/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.33/2.49  
% 15.33/2.49  fof(f36,plain,(
% 15.33/2.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 15.33/2.49    inference(nnf_transformation,[],[f10])).
% 15.33/2.49  
% 15.33/2.49  fof(f57,plain,(
% 15.33/2.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 15.33/2.49    inference(cnf_transformation,[],[f36])).
% 15.33/2.49  
% 15.33/2.49  fof(f1,axiom,(
% 15.33/2.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 15.33/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.33/2.49  
% 15.33/2.49  fof(f19,plain,(
% 15.33/2.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 15.33/2.49    inference(ennf_transformation,[],[f1])).
% 15.33/2.49  
% 15.33/2.49  fof(f31,plain,(
% 15.33/2.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 15.33/2.49    inference(nnf_transformation,[],[f19])).
% 15.33/2.49  
% 15.33/2.49  fof(f32,plain,(
% 15.33/2.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 15.33/2.49    inference(rectify,[],[f31])).
% 15.33/2.49  
% 15.33/2.49  fof(f33,plain,(
% 15.33/2.49    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 15.33/2.49    introduced(choice_axiom,[])).
% 15.33/2.49  
% 15.33/2.49  fof(f34,plain,(
% 15.33/2.49    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 15.33/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f32,f33])).
% 15.33/2.49  
% 15.33/2.49  fof(f45,plain,(
% 15.33/2.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 15.33/2.49    inference(cnf_transformation,[],[f34])).
% 15.33/2.49  
% 15.33/2.49  fof(f46,plain,(
% 15.33/2.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 15.33/2.49    inference(cnf_transformation,[],[f34])).
% 15.33/2.49  
% 15.33/2.49  fof(f6,axiom,(
% 15.33/2.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 15.33/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.33/2.49  
% 15.33/2.49  fof(f20,plain,(
% 15.33/2.49    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 15.33/2.49    inference(ennf_transformation,[],[f6])).
% 15.33/2.49  
% 15.33/2.49  fof(f52,plain,(
% 15.33/2.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 15.33/2.49    inference(cnf_transformation,[],[f20])).
% 15.33/2.49  
% 15.33/2.49  fof(f3,axiom,(
% 15.33/2.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 15.33/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.33/2.49  
% 15.33/2.49  fof(f49,plain,(
% 15.33/2.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 15.33/2.49    inference(cnf_transformation,[],[f3])).
% 15.33/2.49  
% 15.33/2.49  fof(f74,plain,(
% 15.33/2.49    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 15.33/2.49    inference(definition_unfolding,[],[f52,f49])).
% 15.33/2.49  
% 15.33/2.49  fof(f2,axiom,(
% 15.33/2.49    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 15.33/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.33/2.49  
% 15.33/2.49  fof(f35,plain,(
% 15.33/2.49    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 15.33/2.49    inference(nnf_transformation,[],[f2])).
% 15.33/2.49  
% 15.33/2.49  fof(f48,plain,(
% 15.33/2.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 15.33/2.49    inference(cnf_transformation,[],[f35])).
% 15.33/2.49  
% 15.33/2.49  fof(f71,plain,(
% 15.33/2.49    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) | ~r1_tarski(X0,X1)) )),
% 15.33/2.49    inference(definition_unfolding,[],[f48,f49])).
% 15.33/2.49  
% 15.33/2.49  fof(f17,conjecture,(
% 15.33/2.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 15.33/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.33/2.49  
% 15.33/2.49  fof(f18,negated_conjecture,(
% 15.33/2.49    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 15.33/2.49    inference(negated_conjecture,[],[f17])).
% 15.33/2.49  
% 15.33/2.49  fof(f30,plain,(
% 15.33/2.49    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> k1_xboole_0 = k1_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 15.33/2.49    inference(ennf_transformation,[],[f18])).
% 15.33/2.49  
% 15.33/2.49  fof(f39,plain,(
% 15.33/2.49    ? [X0] : (? [X1] : (((k1_xboole_0 != k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) & (k1_xboole_0 = k1_tops_1(X0,X1) | v2_tops_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 15.33/2.49    inference(nnf_transformation,[],[f30])).
% 15.33/2.49  
% 15.33/2.49  fof(f40,plain,(
% 15.33/2.49    ? [X0] : (? [X1] : ((k1_xboole_0 != k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) & (k1_xboole_0 = k1_tops_1(X0,X1) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 15.33/2.49    inference(flattening,[],[f39])).
% 15.33/2.49  
% 15.33/2.49  fof(f42,plain,(
% 15.33/2.49    ( ! [X0] : (? [X1] : ((k1_xboole_0 != k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) & (k1_xboole_0 = k1_tops_1(X0,X1) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((k1_xboole_0 != k1_tops_1(X0,sK2) | ~v2_tops_1(sK2,X0)) & (k1_xboole_0 = k1_tops_1(X0,sK2) | v2_tops_1(sK2,X0)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 15.33/2.49    introduced(choice_axiom,[])).
% 15.33/2.49  
% 15.33/2.49  fof(f41,plain,(
% 15.33/2.49    ? [X0] : (? [X1] : ((k1_xboole_0 != k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) & (k1_xboole_0 = k1_tops_1(X0,X1) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((k1_xboole_0 != k1_tops_1(sK1,X1) | ~v2_tops_1(X1,sK1)) & (k1_xboole_0 = k1_tops_1(sK1,X1) | v2_tops_1(X1,sK1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1))),
% 15.33/2.49    introduced(choice_axiom,[])).
% 15.33/2.49  
% 15.33/2.49  fof(f43,plain,(
% 15.33/2.49    ((k1_xboole_0 != k1_tops_1(sK1,sK2) | ~v2_tops_1(sK2,sK1)) & (k1_xboole_0 = k1_tops_1(sK1,sK2) | v2_tops_1(sK2,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1)),
% 15.33/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f40,f42,f41])).
% 15.33/2.49  
% 15.33/2.49  fof(f68,plain,(
% 15.33/2.49    k1_xboole_0 = k1_tops_1(sK1,sK2) | v2_tops_1(sK2,sK1)),
% 15.33/2.49    inference(cnf_transformation,[],[f43])).
% 15.33/2.49  
% 15.33/2.49  fof(f66,plain,(
% 15.33/2.49    l1_pre_topc(sK1)),
% 15.33/2.49    inference(cnf_transformation,[],[f43])).
% 15.33/2.49  
% 15.33/2.49  fof(f13,axiom,(
% 15.33/2.49    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 15.33/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.33/2.49  
% 15.33/2.49  fof(f26,plain,(
% 15.33/2.49    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 15.33/2.49    inference(ennf_transformation,[],[f13])).
% 15.33/2.49  
% 15.33/2.49  fof(f60,plain,(
% 15.33/2.49    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 15.33/2.49    inference(cnf_transformation,[],[f26])).
% 15.33/2.49  
% 15.33/2.49  fof(f11,axiom,(
% 15.33/2.49    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 15.33/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.33/2.49  
% 15.33/2.49  fof(f23,plain,(
% 15.33/2.49    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 15.33/2.49    inference(ennf_transformation,[],[f11])).
% 15.33/2.49  
% 15.33/2.49  fof(f58,plain,(
% 15.33/2.49    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 15.33/2.49    inference(cnf_transformation,[],[f23])).
% 15.33/2.49  
% 15.33/2.49  fof(f67,plain,(
% 15.33/2.49    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))),
% 15.33/2.49    inference(cnf_transformation,[],[f43])).
% 15.33/2.49  
% 15.33/2.49  fof(f56,plain,(
% 15.33/2.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 15.33/2.49    inference(cnf_transformation,[],[f36])).
% 15.33/2.49  
% 15.33/2.49  fof(f16,axiom,(
% 15.33/2.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 15.33/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.33/2.49  
% 15.33/2.49  fof(f29,plain,(
% 15.33/2.49    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 15.33/2.49    inference(ennf_transformation,[],[f16])).
% 15.33/2.49  
% 15.33/2.49  fof(f38,plain,(
% 15.33/2.49    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | ~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 15.33/2.49    inference(nnf_transformation,[],[f29])).
% 15.33/2.49  
% 15.33/2.49  fof(f64,plain,(
% 15.33/2.49    ( ! [X0,X1] : (v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 15.33/2.49    inference(cnf_transformation,[],[f38])).
% 15.33/2.49  
% 15.33/2.49  fof(f7,axiom,(
% 15.33/2.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 15.33/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.33/2.49  
% 15.33/2.49  fof(f21,plain,(
% 15.33/2.49    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 15.33/2.49    inference(ennf_transformation,[],[f7])).
% 15.33/2.49  
% 15.33/2.49  fof(f53,plain,(
% 15.33/2.49    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 15.33/2.49    inference(cnf_transformation,[],[f21])).
% 15.33/2.49  
% 15.33/2.49  fof(f15,axiom,(
% 15.33/2.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 15.33/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.33/2.49  
% 15.33/2.49  fof(f28,plain,(
% 15.33/2.49    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 15.33/2.49    inference(ennf_transformation,[],[f15])).
% 15.33/2.49  
% 15.33/2.49  fof(f37,plain,(
% 15.33/2.49    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | k2_struct_0(X0) != k2_pre_topc(X0,X1)) & (k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 15.33/2.49    inference(nnf_transformation,[],[f28])).
% 15.33/2.49  
% 15.33/2.49  fof(f62,plain,(
% 15.33/2.49    ( ! [X0,X1] : (k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 15.33/2.49    inference(cnf_transformation,[],[f37])).
% 15.33/2.49  
% 15.33/2.49  fof(f14,axiom,(
% 15.33/2.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)))),
% 15.33/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.33/2.49  
% 15.33/2.49  fof(f27,plain,(
% 15.33/2.49    ! [X0] : (! [X1] : (k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 15.33/2.49    inference(ennf_transformation,[],[f14])).
% 15.33/2.49  
% 15.33/2.49  fof(f61,plain,(
% 15.33/2.49    ( ! [X0,X1] : (k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 15.33/2.49    inference(cnf_transformation,[],[f27])).
% 15.33/2.49  
% 15.33/2.49  fof(f47,plain,(
% 15.33/2.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 15.33/2.49    inference(cnf_transformation,[],[f35])).
% 15.33/2.49  
% 15.33/2.49  fof(f72,plain,(
% 15.33/2.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 15.33/2.49    inference(definition_unfolding,[],[f47,f49])).
% 15.33/2.49  
% 15.33/2.49  fof(f12,axiom,(
% 15.33/2.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 15.33/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.33/2.49  
% 15.33/2.49  fof(f24,plain,(
% 15.33/2.49    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 15.33/2.49    inference(ennf_transformation,[],[f12])).
% 15.33/2.49  
% 15.33/2.49  fof(f25,plain,(
% 15.33/2.49    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 15.33/2.49    inference(flattening,[],[f24])).
% 15.33/2.49  
% 15.33/2.49  fof(f59,plain,(
% 15.33/2.49    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 15.33/2.49    inference(cnf_transformation,[],[f25])).
% 15.33/2.49  
% 15.33/2.49  fof(f8,axiom,(
% 15.33/2.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 15.33/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.33/2.49  
% 15.33/2.49  fof(f22,plain,(
% 15.33/2.49    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 15.33/2.49    inference(ennf_transformation,[],[f8])).
% 15.33/2.49  
% 15.33/2.49  fof(f54,plain,(
% 15.33/2.49    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 15.33/2.49    inference(cnf_transformation,[],[f22])).
% 15.33/2.49  
% 15.33/2.49  fof(f63,plain,(
% 15.33/2.49    ( ! [X0,X1] : (v1_tops_1(X1,X0) | k2_struct_0(X0) != k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 15.33/2.49    inference(cnf_transformation,[],[f37])).
% 15.33/2.49  
% 15.33/2.49  fof(f5,axiom,(
% 15.33/2.49    ! [X0] : k2_subset_1(X0) = X0),
% 15.33/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.33/2.49  
% 15.33/2.49  fof(f51,plain,(
% 15.33/2.49    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 15.33/2.49    inference(cnf_transformation,[],[f5])).
% 15.33/2.49  
% 15.33/2.49  fof(f9,axiom,(
% 15.33/2.49    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 15.33/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.33/2.49  
% 15.33/2.49  fof(f55,plain,(
% 15.33/2.49    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 15.33/2.49    inference(cnf_transformation,[],[f9])).
% 15.33/2.49  
% 15.33/2.49  fof(f4,axiom,(
% 15.33/2.49    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 15.33/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.33/2.49  
% 15.33/2.49  fof(f50,plain,(
% 15.33/2.49    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 15.33/2.49    inference(cnf_transformation,[],[f4])).
% 15.33/2.49  
% 15.33/2.49  fof(f70,plain,(
% 15.33/2.49    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 15.33/2.49    inference(definition_unfolding,[],[f55,f50])).
% 15.33/2.49  
% 15.33/2.49  fof(f73,plain,(
% 15.33/2.49    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 15.33/2.49    inference(definition_unfolding,[],[f51,f70])).
% 15.33/2.49  
% 15.33/2.49  fof(f65,plain,(
% 15.33/2.49    ( ! [X0,X1] : (v2_tops_1(X1,X0) | ~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 15.33/2.49    inference(cnf_transformation,[],[f38])).
% 15.33/2.49  
% 15.33/2.49  fof(f69,plain,(
% 15.33/2.49    k1_xboole_0 != k1_tops_1(sK1,sK2) | ~v2_tops_1(sK2,sK1)),
% 15.33/2.49    inference(cnf_transformation,[],[f43])).
% 15.33/2.49  
% 15.33/2.49  cnf(c_9,plain,
% 15.33/2.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 15.33/2.49      inference(cnf_transformation,[],[f57]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_849,plain,
% 15.33/2.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 15.33/2.49      | r1_tarski(X0,X1) != iProver_top ),
% 15.33/2.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_1,plain,
% 15.33/2.49      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 15.33/2.49      inference(cnf_transformation,[],[f45]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_853,plain,
% 15.33/2.49      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 15.33/2.49      | r1_tarski(X0,X1) = iProver_top ),
% 15.33/2.49      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_0,plain,
% 15.33/2.49      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 15.33/2.49      inference(cnf_transformation,[],[f46]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_854,plain,
% 15.33/2.49      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 15.33/2.49      | r1_tarski(X0,X1) = iProver_top ),
% 15.33/2.49      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_1890,plain,
% 15.33/2.49      ( r1_tarski(X0,X0) = iProver_top ),
% 15.33/2.49      inference(superposition,[status(thm)],[c_853,c_854]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_6,plain,
% 15.33/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.33/2.49      | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
% 15.33/2.49      inference(cnf_transformation,[],[f74]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_165,plain,
% 15.33/2.49      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 15.33/2.49      inference(prop_impl,[status(thm)],[c_9]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_166,plain,
% 15.33/2.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 15.33/2.49      inference(renaming,[status(thm)],[c_165]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_210,plain,
% 15.33/2.49      ( ~ r1_tarski(X0,X1)
% 15.33/2.49      | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
% 15.33/2.49      inference(bin_hyper_res,[status(thm)],[c_6,c_166]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_835,plain,
% 15.33/2.49      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
% 15.33/2.49      | r1_tarski(X1,X0) != iProver_top ),
% 15.33/2.49      inference(predicate_to_equality,[status(thm)],[c_210]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_4944,plain,
% 15.33/2.49      ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k3_subset_1(X0,X0) ),
% 15.33/2.49      inference(superposition,[status(thm)],[c_1890,c_835]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_3,plain,
% 15.33/2.49      ( ~ r1_tarski(X0,X1)
% 15.33/2.49      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
% 15.33/2.49      inference(cnf_transformation,[],[f71]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_851,plain,
% 15.33/2.49      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
% 15.33/2.49      | r1_tarski(X0,X1) != iProver_top ),
% 15.33/2.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_3581,plain,
% 15.33/2.49      ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k1_xboole_0 ),
% 15.33/2.49      inference(superposition,[status(thm)],[c_1890,c_851]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_4960,plain,
% 15.33/2.49      ( k3_subset_1(X0,X0) = k1_xboole_0 ),
% 15.33/2.49      inference(light_normalisation,[status(thm)],[c_4944,c_3581]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_20,negated_conjecture,
% 15.33/2.49      ( v2_tops_1(sK2,sK1) | k1_xboole_0 = k1_tops_1(sK1,sK2) ),
% 15.33/2.49      inference(cnf_transformation,[],[f68]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_838,plain,
% 15.33/2.49      ( k1_xboole_0 = k1_tops_1(sK1,sK2)
% 15.33/2.49      | v2_tops_1(sK2,sK1) = iProver_top ),
% 15.33/2.49      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_22,negated_conjecture,
% 15.33/2.49      ( l1_pre_topc(sK1) ),
% 15.33/2.49      inference(cnf_transformation,[],[f66]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_836,plain,
% 15.33/2.49      ( l1_pre_topc(sK1) = iProver_top ),
% 15.33/2.49      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_13,plain,
% 15.33/2.49      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 15.33/2.49      inference(cnf_transformation,[],[f60]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_845,plain,
% 15.33/2.49      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 15.33/2.49      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_1080,plain,
% 15.33/2.49      ( l1_struct_0(sK1) = iProver_top ),
% 15.33/2.49      inference(superposition,[status(thm)],[c_836,c_845]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_11,plain,
% 15.33/2.49      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 15.33/2.49      inference(cnf_transformation,[],[f58]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_847,plain,
% 15.33/2.49      ( u1_struct_0(X0) = k2_struct_0(X0)
% 15.33/2.49      | l1_struct_0(X0) != iProver_top ),
% 15.33/2.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_1154,plain,
% 15.33/2.49      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 15.33/2.49      inference(superposition,[status(thm)],[c_1080,c_847]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_21,negated_conjecture,
% 15.33/2.49      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 15.33/2.49      inference(cnf_transformation,[],[f67]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_837,plain,
% 15.33/2.49      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 15.33/2.49      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_10,plain,
% 15.33/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 15.33/2.49      inference(cnf_transformation,[],[f56]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_848,plain,
% 15.33/2.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 15.33/2.49      | r1_tarski(X0,X1) = iProver_top ),
% 15.33/2.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_1263,plain,
% 15.33/2.49      ( r1_tarski(sK2,u1_struct_0(sK1)) = iProver_top ),
% 15.33/2.49      inference(superposition,[status(thm)],[c_837,c_848]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_1544,plain,
% 15.33/2.49      ( r1_tarski(sK2,k2_struct_0(sK1)) = iProver_top ),
% 15.33/2.49      inference(demodulation,[status(thm)],[c_1154,c_1263]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_18,plain,
% 15.33/2.49      ( ~ v2_tops_1(X0,X1)
% 15.33/2.49      | v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1)
% 15.33/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.33/2.49      | ~ l1_pre_topc(X1) ),
% 15.33/2.49      inference(cnf_transformation,[],[f64]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_840,plain,
% 15.33/2.49      ( v2_tops_1(X0,X1) != iProver_top
% 15.33/2.49      | v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1) = iProver_top
% 15.33/2.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 15.33/2.49      | l1_pre_topc(X1) != iProver_top ),
% 15.33/2.49      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_1552,plain,
% 15.33/2.49      ( v2_tops_1(X0,sK1) != iProver_top
% 15.33/2.49      | v1_tops_1(k3_subset_1(k2_struct_0(sK1),X0),sK1) = iProver_top
% 15.33/2.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 15.33/2.49      | l1_pre_topc(sK1) != iProver_top ),
% 15.33/2.49      inference(superposition,[status(thm)],[c_1154,c_840]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_1553,plain,
% 15.33/2.49      ( v2_tops_1(X0,sK1) != iProver_top
% 15.33/2.49      | v1_tops_1(k3_subset_1(k2_struct_0(sK1),X0),sK1) = iProver_top
% 15.33/2.49      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 15.33/2.49      | l1_pre_topc(sK1) != iProver_top ),
% 15.33/2.49      inference(light_normalisation,[status(thm)],[c_1552,c_1154]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_23,plain,
% 15.33/2.49      ( l1_pre_topc(sK1) = iProver_top ),
% 15.33/2.49      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_1611,plain,
% 15.33/2.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 15.33/2.49      | v1_tops_1(k3_subset_1(k2_struct_0(sK1),X0),sK1) = iProver_top
% 15.33/2.49      | v2_tops_1(X0,sK1) != iProver_top ),
% 15.33/2.49      inference(global_propositional_subsumption,
% 15.33/2.49                [status(thm)],
% 15.33/2.49                [c_1553,c_23]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_1612,plain,
% 15.33/2.49      ( v2_tops_1(X0,sK1) != iProver_top
% 15.33/2.49      | v1_tops_1(k3_subset_1(k2_struct_0(sK1),X0),sK1) = iProver_top
% 15.33/2.49      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
% 15.33/2.49      inference(renaming,[status(thm)],[c_1611]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_7,plain,
% 15.33/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.33/2.49      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 15.33/2.49      inference(cnf_transformation,[],[f53]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_211,plain,
% 15.33/2.49      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
% 15.33/2.49      | ~ r1_tarski(X1,X0) ),
% 15.33/2.49      inference(bin_hyper_res,[status(thm)],[c_7,c_166]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_834,plain,
% 15.33/2.49      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) = iProver_top
% 15.33/2.49      | r1_tarski(X1,X0) != iProver_top ),
% 15.33/2.49      inference(predicate_to_equality,[status(thm)],[c_211]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_16,plain,
% 15.33/2.49      ( ~ v1_tops_1(X0,X1)
% 15.33/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.33/2.49      | ~ l1_pre_topc(X1)
% 15.33/2.49      | k2_pre_topc(X1,X0) = k2_struct_0(X1) ),
% 15.33/2.49      inference(cnf_transformation,[],[f62]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_842,plain,
% 15.33/2.49      ( k2_pre_topc(X0,X1) = k2_struct_0(X0)
% 15.33/2.49      | v1_tops_1(X1,X0) != iProver_top
% 15.33/2.49      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 15.33/2.49      | l1_pre_topc(X0) != iProver_top ),
% 15.33/2.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_2624,plain,
% 15.33/2.49      ( k2_pre_topc(sK1,X0) = k2_struct_0(sK1)
% 15.33/2.49      | v1_tops_1(X0,sK1) != iProver_top
% 15.33/2.49      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 15.33/2.49      | l1_pre_topc(sK1) != iProver_top ),
% 15.33/2.49      inference(superposition,[status(thm)],[c_1154,c_842]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_2996,plain,
% 15.33/2.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 15.33/2.49      | v1_tops_1(X0,sK1) != iProver_top
% 15.33/2.49      | k2_pre_topc(sK1,X0) = k2_struct_0(sK1) ),
% 15.33/2.49      inference(global_propositional_subsumption,
% 15.33/2.49                [status(thm)],
% 15.33/2.49                [c_2624,c_23]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_2997,plain,
% 15.33/2.49      ( k2_pre_topc(sK1,X0) = k2_struct_0(sK1)
% 15.33/2.49      | v1_tops_1(X0,sK1) != iProver_top
% 15.33/2.49      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
% 15.33/2.49      inference(renaming,[status(thm)],[c_2996]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_3854,plain,
% 15.33/2.49      ( k2_pre_topc(sK1,k3_subset_1(k2_struct_0(sK1),X0)) = k2_struct_0(sK1)
% 15.33/2.49      | v1_tops_1(k3_subset_1(k2_struct_0(sK1),X0),sK1) != iProver_top
% 15.33/2.49      | r1_tarski(X0,k2_struct_0(sK1)) != iProver_top ),
% 15.33/2.49      inference(superposition,[status(thm)],[c_834,c_2997]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_7519,plain,
% 15.33/2.49      ( k2_pre_topc(sK1,k3_subset_1(k2_struct_0(sK1),X0)) = k2_struct_0(sK1)
% 15.33/2.49      | v2_tops_1(X0,sK1) != iProver_top
% 15.33/2.49      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 15.33/2.49      | r1_tarski(X0,k2_struct_0(sK1)) != iProver_top ),
% 15.33/2.49      inference(superposition,[status(thm)],[c_1612,c_3854]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_9127,plain,
% 15.33/2.49      ( k2_pre_topc(sK1,k3_subset_1(k2_struct_0(sK1),X0)) = k2_struct_0(sK1)
% 15.33/2.49      | v2_tops_1(X0,sK1) != iProver_top
% 15.33/2.49      | r1_tarski(X0,k2_struct_0(sK1)) != iProver_top ),
% 15.33/2.49      inference(forward_subsumption_resolution,
% 15.33/2.49                [status(thm)],
% 15.33/2.49                [c_7519,c_849]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_9133,plain,
% 15.33/2.49      ( k2_pre_topc(sK1,k3_subset_1(k2_struct_0(sK1),sK2)) = k2_struct_0(sK1)
% 15.33/2.49      | v2_tops_1(sK2,sK1) != iProver_top ),
% 15.33/2.49      inference(superposition,[status(thm)],[c_1544,c_9127]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_9211,plain,
% 15.33/2.49      ( k1_tops_1(sK1,sK2) = k1_xboole_0
% 15.33/2.49      | k2_pre_topc(sK1,k3_subset_1(k2_struct_0(sK1),sK2)) = k2_struct_0(sK1) ),
% 15.33/2.49      inference(superposition,[status(thm)],[c_838,c_9133]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_1545,plain,
% 15.33/2.49      ( m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top ),
% 15.33/2.49      inference(demodulation,[status(thm)],[c_1154,c_837]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_14,plain,
% 15.33/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.33/2.49      | ~ l1_pre_topc(X1)
% 15.33/2.49      | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0) ),
% 15.33/2.49      inference(cnf_transformation,[],[f61]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_844,plain,
% 15.33/2.49      ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
% 15.33/2.49      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 15.33/2.49      | l1_pre_topc(X0) != iProver_top ),
% 15.33/2.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_2741,plain,
% 15.33/2.49      ( k3_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),X0))) = k1_tops_1(sK1,X0)
% 15.33/2.49      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 15.33/2.49      | l1_pre_topc(sK1) != iProver_top ),
% 15.33/2.49      inference(superposition,[status(thm)],[c_1154,c_844]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_2745,plain,
% 15.33/2.49      ( k3_subset_1(k2_struct_0(sK1),k2_pre_topc(sK1,k3_subset_1(k2_struct_0(sK1),X0))) = k1_tops_1(sK1,X0)
% 15.33/2.49      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 15.33/2.49      | l1_pre_topc(sK1) != iProver_top ),
% 15.33/2.49      inference(light_normalisation,[status(thm)],[c_2741,c_1154]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_3159,plain,
% 15.33/2.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 15.33/2.49      | k3_subset_1(k2_struct_0(sK1),k2_pre_topc(sK1,k3_subset_1(k2_struct_0(sK1),X0))) = k1_tops_1(sK1,X0) ),
% 15.33/2.49      inference(global_propositional_subsumption,
% 15.33/2.49                [status(thm)],
% 15.33/2.49                [c_2745,c_23]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_3160,plain,
% 15.33/2.49      ( k3_subset_1(k2_struct_0(sK1),k2_pre_topc(sK1,k3_subset_1(k2_struct_0(sK1),X0))) = k1_tops_1(sK1,X0)
% 15.33/2.49      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
% 15.33/2.49      inference(renaming,[status(thm)],[c_3159]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_3168,plain,
% 15.33/2.49      ( k3_subset_1(k2_struct_0(sK1),k2_pre_topc(sK1,k3_subset_1(k2_struct_0(sK1),sK2))) = k1_tops_1(sK1,sK2) ),
% 15.33/2.49      inference(superposition,[status(thm)],[c_1545,c_3160]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_9306,plain,
% 15.33/2.49      ( k1_tops_1(sK1,sK2) = k1_xboole_0
% 15.33/2.49      | k3_subset_1(k2_struct_0(sK1),k2_struct_0(sK1)) = k1_tops_1(sK1,sK2) ),
% 15.33/2.49      inference(superposition,[status(thm)],[c_9211,c_3168]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_34147,plain,
% 15.33/2.49      ( k1_tops_1(sK1,sK2) = k1_xboole_0 ),
% 15.33/2.49      inference(demodulation,[status(thm)],[c_4960,c_9306]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_3850,plain,
% 15.33/2.49      ( r1_tarski(X0,X1) != iProver_top
% 15.33/2.49      | r1_tarski(k3_subset_1(X1,X0),X1) = iProver_top ),
% 15.33/2.49      inference(superposition,[status(thm)],[c_834,c_848]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_4911,plain,
% 15.33/2.49      ( k5_xboole_0(k3_subset_1(X0,X1),k3_xboole_0(k3_subset_1(X0,X1),X0)) = k1_xboole_0
% 15.33/2.49      | r1_tarski(X1,X0) != iProver_top ),
% 15.33/2.49      inference(superposition,[status(thm)],[c_3850,c_851]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_5944,plain,
% 15.33/2.49      ( k5_xboole_0(k3_subset_1(k2_struct_0(sK1),sK2),k3_xboole_0(k3_subset_1(k2_struct_0(sK1),sK2),k2_struct_0(sK1))) = k1_xboole_0 ),
% 15.33/2.49      inference(superposition,[status(thm)],[c_1544,c_4911]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_4,plain,
% 15.33/2.49      ( r1_tarski(X0,X1)
% 15.33/2.49      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0 ),
% 15.33/2.49      inference(cnf_transformation,[],[f72]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_850,plain,
% 15.33/2.49      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0
% 15.33/2.49      | r1_tarski(X0,X1) = iProver_top ),
% 15.33/2.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_6298,plain,
% 15.33/2.49      ( r1_tarski(k3_subset_1(k2_struct_0(sK1),sK2),k2_struct_0(sK1)) = iProver_top ),
% 15.33/2.49      inference(superposition,[status(thm)],[c_5944,c_850]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_12,plain,
% 15.33/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.33/2.49      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 15.33/2.49      | ~ l1_pre_topc(X1) ),
% 15.33/2.49      inference(cnf_transformation,[],[f59]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_846,plain,
% 15.33/2.49      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 15.33/2.49      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 15.33/2.49      | l1_pre_topc(X1) != iProver_top ),
% 15.33/2.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_1954,plain,
% 15.33/2.49      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 15.33/2.49      | r1_tarski(k2_pre_topc(X1,X0),u1_struct_0(X1)) = iProver_top
% 15.33/2.49      | l1_pre_topc(X1) != iProver_top ),
% 15.33/2.49      inference(superposition,[status(thm)],[c_846,c_848]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_8,plain,
% 15.33/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.33/2.49      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 15.33/2.49      inference(cnf_transformation,[],[f54]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_212,plain,
% 15.33/2.49      ( ~ r1_tarski(X0,X1) | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 15.33/2.49      inference(bin_hyper_res,[status(thm)],[c_8,c_166]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_833,plain,
% 15.33/2.49      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 15.33/2.49      | r1_tarski(X1,X0) != iProver_top ),
% 15.33/2.49      inference(predicate_to_equality,[status(thm)],[c_212]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_3684,plain,
% 15.33/2.49      ( k3_subset_1(u1_struct_0(X0),k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1))) = k2_pre_topc(X0,X1)
% 15.33/2.49      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 15.33/2.49      | l1_pre_topc(X0) != iProver_top ),
% 15.33/2.49      inference(superposition,[status(thm)],[c_1954,c_833]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_14123,plain,
% 15.33/2.49      ( k3_subset_1(u1_struct_0(X0),k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1))) = k2_pre_topc(X0,X1)
% 15.33/2.49      | r1_tarski(X1,u1_struct_0(X0)) != iProver_top
% 15.33/2.49      | l1_pre_topc(X0) != iProver_top ),
% 15.33/2.49      inference(superposition,[status(thm)],[c_849,c_3684]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_14273,plain,
% 15.33/2.49      ( k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,X0))) = k2_pre_topc(sK1,X0)
% 15.33/2.49      | r1_tarski(X0,k2_struct_0(sK1)) != iProver_top
% 15.33/2.49      | l1_pre_topc(sK1) != iProver_top ),
% 15.33/2.49      inference(superposition,[status(thm)],[c_1154,c_14123]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_14277,plain,
% 15.33/2.49      ( k3_subset_1(k2_struct_0(sK1),k3_subset_1(k2_struct_0(sK1),k2_pre_topc(sK1,X0))) = k2_pre_topc(sK1,X0)
% 15.33/2.49      | r1_tarski(X0,k2_struct_0(sK1)) != iProver_top
% 15.33/2.49      | l1_pre_topc(sK1) != iProver_top ),
% 15.33/2.49      inference(light_normalisation,[status(thm)],[c_14273,c_1154]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_14870,plain,
% 15.33/2.49      ( r1_tarski(X0,k2_struct_0(sK1)) != iProver_top
% 15.33/2.49      | k3_subset_1(k2_struct_0(sK1),k3_subset_1(k2_struct_0(sK1),k2_pre_topc(sK1,X0))) = k2_pre_topc(sK1,X0) ),
% 15.33/2.49      inference(global_propositional_subsumption,
% 15.33/2.49                [status(thm)],
% 15.33/2.49                [c_14277,c_23]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_14871,plain,
% 15.33/2.49      ( k3_subset_1(k2_struct_0(sK1),k3_subset_1(k2_struct_0(sK1),k2_pre_topc(sK1,X0))) = k2_pre_topc(sK1,X0)
% 15.33/2.49      | r1_tarski(X0,k2_struct_0(sK1)) != iProver_top ),
% 15.33/2.49      inference(renaming,[status(thm)],[c_14870]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_14884,plain,
% 15.33/2.49      ( k3_subset_1(k2_struct_0(sK1),k3_subset_1(k2_struct_0(sK1),k2_pre_topc(sK1,k3_subset_1(k2_struct_0(sK1),sK2)))) = k2_pre_topc(sK1,k3_subset_1(k2_struct_0(sK1),sK2)) ),
% 15.33/2.49      inference(superposition,[status(thm)],[c_6298,c_14871]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_14901,plain,
% 15.33/2.49      ( k2_pre_topc(sK1,k3_subset_1(k2_struct_0(sK1),sK2)) = k3_subset_1(k2_struct_0(sK1),k1_tops_1(sK1,sK2)) ),
% 15.33/2.49      inference(light_normalisation,[status(thm)],[c_14884,c_3168]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_15,plain,
% 15.33/2.49      ( v1_tops_1(X0,X1)
% 15.33/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.33/2.49      | ~ l1_pre_topc(X1)
% 15.33/2.49      | k2_pre_topc(X1,X0) != k2_struct_0(X1) ),
% 15.33/2.49      inference(cnf_transformation,[],[f63]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_843,plain,
% 15.33/2.49      ( k2_pre_topc(X0,X1) != k2_struct_0(X0)
% 15.33/2.49      | v1_tops_1(X1,X0) = iProver_top
% 15.33/2.49      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 15.33/2.49      | l1_pre_topc(X0) != iProver_top ),
% 15.33/2.49      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_14985,plain,
% 15.33/2.49      ( k3_subset_1(k2_struct_0(sK1),k1_tops_1(sK1,sK2)) != k2_struct_0(sK1)
% 15.33/2.49      | v1_tops_1(k3_subset_1(k2_struct_0(sK1),sK2),sK1) = iProver_top
% 15.33/2.49      | m1_subset_1(k3_subset_1(k2_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 15.33/2.49      | l1_pre_topc(sK1) != iProver_top ),
% 15.33/2.49      inference(superposition,[status(thm)],[c_14901,c_843]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_15023,plain,
% 15.33/2.49      ( k3_subset_1(k2_struct_0(sK1),k1_tops_1(sK1,sK2)) != k2_struct_0(sK1)
% 15.33/2.49      | v1_tops_1(k3_subset_1(k2_struct_0(sK1),sK2),sK1) = iProver_top
% 15.33/2.49      | m1_subset_1(k3_subset_1(k2_struct_0(sK1),sK2),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 15.33/2.49      | l1_pre_topc(sK1) != iProver_top ),
% 15.33/2.49      inference(light_normalisation,[status(thm)],[c_14985,c_1154]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_15241,plain,
% 15.33/2.49      ( m1_subset_1(k3_subset_1(k2_struct_0(sK1),sK2),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 15.33/2.49      | v1_tops_1(k3_subset_1(k2_struct_0(sK1),sK2),sK1) = iProver_top
% 15.33/2.49      | k3_subset_1(k2_struct_0(sK1),k1_tops_1(sK1,sK2)) != k2_struct_0(sK1) ),
% 15.33/2.49      inference(global_propositional_subsumption,
% 15.33/2.49                [status(thm)],
% 15.33/2.49                [c_15023,c_23]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_15242,plain,
% 15.33/2.49      ( k3_subset_1(k2_struct_0(sK1),k1_tops_1(sK1,sK2)) != k2_struct_0(sK1)
% 15.33/2.49      | v1_tops_1(k3_subset_1(k2_struct_0(sK1),sK2),sK1) = iProver_top
% 15.33/2.49      | m1_subset_1(k3_subset_1(k2_struct_0(sK1),sK2),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
% 15.33/2.49      inference(renaming,[status(thm)],[c_15241]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_35171,plain,
% 15.33/2.49      ( k3_subset_1(k2_struct_0(sK1),k1_xboole_0) != k2_struct_0(sK1)
% 15.33/2.49      | v1_tops_1(k3_subset_1(k2_struct_0(sK1),sK2),sK1) = iProver_top
% 15.33/2.49      | m1_subset_1(k3_subset_1(k2_struct_0(sK1),sK2),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
% 15.33/2.49      inference(demodulation,[status(thm)],[c_34147,c_15242]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_5,plain,
% 15.33/2.49      ( k3_subset_1(X0,k1_xboole_0) = X0 ),
% 15.33/2.49      inference(cnf_transformation,[],[f73]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_35198,plain,
% 15.33/2.49      ( k2_struct_0(sK1) != k2_struct_0(sK1)
% 15.33/2.49      | v1_tops_1(k3_subset_1(k2_struct_0(sK1),sK2),sK1) = iProver_top
% 15.33/2.49      | m1_subset_1(k3_subset_1(k2_struct_0(sK1),sK2),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
% 15.33/2.49      inference(demodulation,[status(thm)],[c_35171,c_5]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_35199,plain,
% 15.33/2.49      ( v1_tops_1(k3_subset_1(k2_struct_0(sK1),sK2),sK1) = iProver_top
% 15.33/2.49      | m1_subset_1(k3_subset_1(k2_struct_0(sK1),sK2),k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
% 15.33/2.49      inference(equality_resolution_simp,[status(thm)],[c_35198]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_53281,plain,
% 15.33/2.49      ( v1_tops_1(k3_subset_1(k2_struct_0(sK1),sK2),sK1) = iProver_top
% 15.33/2.49      | r1_tarski(k3_subset_1(k2_struct_0(sK1),sK2),k2_struct_0(sK1)) != iProver_top ),
% 15.33/2.49      inference(superposition,[status(thm)],[c_849,c_35199]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_55738,plain,
% 15.33/2.49      ( v1_tops_1(k3_subset_1(k2_struct_0(sK1),sK2),sK1) = iProver_top ),
% 15.33/2.49      inference(global_propositional_subsumption,
% 15.33/2.49                [status(thm)],
% 15.33/2.49                [c_53281,c_6298]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_17,plain,
% 15.33/2.49      ( v2_tops_1(X0,X1)
% 15.33/2.49      | ~ v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1)
% 15.33/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.33/2.49      | ~ l1_pre_topc(X1) ),
% 15.33/2.49      inference(cnf_transformation,[],[f65]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_841,plain,
% 15.33/2.49      ( v2_tops_1(X0,X1) = iProver_top
% 15.33/2.49      | v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1) != iProver_top
% 15.33/2.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 15.33/2.49      | l1_pre_topc(X1) != iProver_top ),
% 15.33/2.49      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_1786,plain,
% 15.33/2.49      ( v2_tops_1(X0,sK1) = iProver_top
% 15.33/2.49      | v1_tops_1(k3_subset_1(k2_struct_0(sK1),X0),sK1) != iProver_top
% 15.33/2.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 15.33/2.49      | l1_pre_topc(sK1) != iProver_top ),
% 15.33/2.49      inference(superposition,[status(thm)],[c_1154,c_841]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_1791,plain,
% 15.33/2.49      ( v2_tops_1(X0,sK1) = iProver_top
% 15.33/2.49      | v1_tops_1(k3_subset_1(k2_struct_0(sK1),X0),sK1) != iProver_top
% 15.33/2.49      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 15.33/2.49      | l1_pre_topc(sK1) != iProver_top ),
% 15.33/2.49      inference(light_normalisation,[status(thm)],[c_1786,c_1154]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_2144,plain,
% 15.33/2.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 15.33/2.49      | v1_tops_1(k3_subset_1(k2_struct_0(sK1),X0),sK1) != iProver_top
% 15.33/2.49      | v2_tops_1(X0,sK1) = iProver_top ),
% 15.33/2.49      inference(global_propositional_subsumption,
% 15.33/2.49                [status(thm)],
% 15.33/2.49                [c_1791,c_23]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_2145,plain,
% 15.33/2.49      ( v2_tops_1(X0,sK1) = iProver_top
% 15.33/2.49      | v1_tops_1(k3_subset_1(k2_struct_0(sK1),X0),sK1) != iProver_top
% 15.33/2.49      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
% 15.33/2.49      inference(renaming,[status(thm)],[c_2144]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_55744,plain,
% 15.33/2.49      ( v2_tops_1(sK2,sK1) = iProver_top
% 15.33/2.49      | m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
% 15.33/2.49      inference(superposition,[status(thm)],[c_55738,c_2145]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_283,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_2565,plain,
% 15.33/2.49      ( X0 != X1 | k1_xboole_0 != X1 | k1_xboole_0 = X0 ),
% 15.33/2.49      inference(instantiation,[status(thm)],[c_283]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_4532,plain,
% 15.33/2.49      ( X0 != k1_xboole_0
% 15.33/2.49      | k1_xboole_0 = X0
% 15.33/2.49      | k1_xboole_0 != k1_xboole_0 ),
% 15.33/2.49      inference(instantiation,[status(thm)],[c_2565]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_14074,plain,
% 15.33/2.49      ( k1_tops_1(sK1,sK2) != k1_xboole_0
% 15.33/2.49      | k1_xboole_0 = k1_tops_1(sK1,sK2)
% 15.33/2.49      | k1_xboole_0 != k1_xboole_0 ),
% 15.33/2.49      inference(instantiation,[status(thm)],[c_4532]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_282,plain,( X0 = X0 ),theory(equality) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_2467,plain,
% 15.33/2.49      ( k1_xboole_0 = k1_xboole_0 ),
% 15.33/2.49      inference(instantiation,[status(thm)],[c_282]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_19,negated_conjecture,
% 15.33/2.49      ( ~ v2_tops_1(sK2,sK1) | k1_xboole_0 != k1_tops_1(sK1,sK2) ),
% 15.33/2.49      inference(cnf_transformation,[],[f69]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(c_26,plain,
% 15.33/2.49      ( k1_xboole_0 != k1_tops_1(sK1,sK2)
% 15.33/2.49      | v2_tops_1(sK2,sK1) != iProver_top ),
% 15.33/2.49      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 15.33/2.49  
% 15.33/2.49  cnf(contradiction,plain,
% 15.33/2.49      ( $false ),
% 15.33/2.49      inference(minisat,
% 15.33/2.49                [status(thm)],
% 15.33/2.49                [c_55744,c_34147,c_14074,c_2467,c_1545,c_26]) ).
% 15.33/2.49  
% 15.33/2.49  
% 15.33/2.49  % SZS output end CNFRefutation for theBenchmark.p
% 15.33/2.49  
% 15.33/2.49  ------                               Statistics
% 15.33/2.49  
% 15.33/2.49  ------ Selected
% 15.33/2.49  
% 15.33/2.49  total_time:                             1.903
% 15.33/2.49  
%------------------------------------------------------------------------------
