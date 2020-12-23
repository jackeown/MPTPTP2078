%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:14:47 EST 2020

% Result     : Theorem 3.22s
% Output     : CNFRefutation 3.22s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 714 expanded)
%              Number of clauses        :   75 ( 207 expanded)
%              Number of leaves         :   17 ( 154 expanded)
%              Depth                    :   23
%              Number of atoms          :  356 (2941 expanded)
%              Number of equality atoms :  163 ( 976 expanded)
%              Maximal formula depth    :    9 (   4 average)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(nnf_transformation,[],[f31])).

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

fof(f62,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f39])).

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

fof(f22,plain,(
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

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f60,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f61,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f39])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f52,f45])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f68,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f49,f45])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f44,f45])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f9,axiom,(
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
    inference(ennf_transformation,[],[f9])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f19])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f8,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f64,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f50,f45])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f51,f64])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f32])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f71,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f41])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f67,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
    inference(definition_unfolding,[],[f46,f64])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f63,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) != X1
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f59,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_18,negated_conjecture,
    ( v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_169,plain,
    ( v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(prop_impl,[status(thm)],[c_18])).

cnf(c_12,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_20,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_369,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,X0) = X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_20])).

cnf(c_370,plain,
    ( ~ v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_369])).

cnf(c_419,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,X0) = X0
    | sK1 != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_169,c_370])).

cnf(c_420,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(unflattening,[status(thm)],[c_419])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_422,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_420,c_19])).

cnf(c_526,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(prop_impl,[status(thm)],[c_422])).

cnf(c_527,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(renaming,[status(thm)],[c_526])).

cnf(c_1022,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X0,k3_xboole_0(X0,X2)) = k7_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1023,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k7_subset_1(X2,X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2676,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k3_xboole_0(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_1022,c_1023])).

cnf(c_2761,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tops_1(sK0,sK1))) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_527,c_2676])).

cnf(c_8,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1025,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_4806,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2761,c_1025])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1029,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_4828,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k5_xboole_0(k2_tops_1(sK0,sK1),k3_xboole_0(k2_tops_1(sK0,sK1),sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4806,c_1029])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_357,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_20])).

cnf(c_358,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_357])).

cnf(c_1019,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_358])).

cnf(c_2677,plain,
    ( k5_xboole_0(k2_tops_1(sK0,X0),k3_xboole_0(k2_tops_1(sK0,X0),X1)) = k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,X0),X1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1019,c_1023])).

cnf(c_2975,plain,
    ( k5_xboole_0(k2_tops_1(sK0,sK1),k3_xboole_0(k2_tops_1(sK0,sK1),X0)) = k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),X0) ),
    inference(superposition,[status(thm)],[c_1022,c_2677])).

cnf(c_4836,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),sK1) = k1_xboole_0
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(demodulation,[status(thm)],[c_4828,c_2975])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k5_xboole_0(X2,k5_xboole_0(X0,k3_xboole_0(X0,X2))) = k4_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1024,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k4_subset_1(X2,X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2692,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(X0,k3_xboole_0(X0,sK1))) = k4_subset_1(u1_struct_0(sK0),sK1,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1022,c_1024])).

cnf(c_2785,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(k2_tops_1(sK0,X0),k3_xboole_0(k2_tops_1(sK0,X0),sK1))) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1019,c_2692])).

cnf(c_3640,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(k2_tops_1(sK0,sK1),k3_xboole_0(k2_tops_1(sK0,sK1),sK1))) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_1022,c_2785])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_333,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_20])).

cnf(c_334,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_333])).

cnf(c_1021,plain,
    ( k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_334])).

cnf(c_1165,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_1022,c_1021])).

cnf(c_3647,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(k2_tops_1(sK0,sK1),k3_xboole_0(k2_tops_1(sK0,sK1),sK1))) = k2_pre_topc(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_3640,c_1165])).

cnf(c_3648,plain,
    ( k5_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_3647,c_2975])).

cnf(c_8921,plain,
    ( k2_pre_topc(sK0,sK1) = k5_xboole_0(sK1,k1_xboole_0)
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_4836,c_3648])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1030,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2145,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1030,c_1029])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1027,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1997,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_1030,c_1027])).

cnf(c_3424,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2145,c_1997])).

cnf(c_7,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1026,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1998,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1026,c_1027])).

cnf(c_5,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_2752,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) = X0 ),
    inference(demodulation,[status(thm)],[c_1998,c_5])).

cnf(c_3427,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(demodulation,[status(thm)],[c_3424,c_2752])).

cnf(c_8924,plain,
    ( k2_pre_topc(sK0,sK1) = sK1 ),
    inference(demodulation,[status(thm)],[c_8921,c_3427])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_345,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_20])).

cnf(c_346,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_345])).

cnf(c_1020,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_346])).

cnf(c_1190,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_1022,c_1020])).

cnf(c_8941,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_8924,c_1190])).

cnf(c_17,negated_conjecture,
    ( ~ v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_167,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
    inference(prop_impl,[status(thm)],[c_17])).

cnf(c_11,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | k2_pre_topc(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_21,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_305,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_21])).

cnf(c_306,plain,
    ( v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k2_pre_topc(sK0,X0) != X0 ),
    inference(unflattening,[status(thm)],[c_305])).

cnf(c_310,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(X0,sK0)
    | k2_pre_topc(sK0,X0) != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_306,c_20])).

cnf(c_311,plain,
    ( v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,X0) != X0 ),
    inference(renaming,[status(thm)],[c_310])).

cnf(c_430,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,X0) != X0
    | sK1 != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_167,c_311])).

cnf(c_431,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,sK1) != sK1 ),
    inference(unflattening,[status(thm)],[c_430])).

cnf(c_433,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,sK1) != sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_431,c_19])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8941,c_8924,c_433])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.32  % Computer   : n003.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 11:39:42 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  % Running in FOF mode
% 3.22/0.96  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.22/0.96  
% 3.22/0.96  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.22/0.96  
% 3.22/0.96  ------  iProver source info
% 3.22/0.96  
% 3.22/0.96  git: date: 2020-06-30 10:37:57 +0100
% 3.22/0.96  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.22/0.96  git: non_committed_changes: false
% 3.22/0.96  git: last_make_outside_of_git: false
% 3.22/0.96  
% 3.22/0.96  ------ 
% 3.22/0.96  
% 3.22/0.96  ------ Input Options
% 3.22/0.96  
% 3.22/0.96  --out_options                           all
% 3.22/0.96  --tptp_safe_out                         true
% 3.22/0.96  --problem_path                          ""
% 3.22/0.96  --include_path                          ""
% 3.22/0.96  --clausifier                            res/vclausify_rel
% 3.22/0.96  --clausifier_options                    --mode clausify
% 3.22/0.96  --stdin                                 false
% 3.22/0.96  --stats_out                             all
% 3.22/0.96  
% 3.22/0.96  ------ General Options
% 3.22/0.96  
% 3.22/0.96  --fof                                   false
% 3.22/0.96  --time_out_real                         305.
% 3.22/0.96  --time_out_virtual                      -1.
% 3.22/0.96  --symbol_type_check                     false
% 3.22/0.96  --clausify_out                          false
% 3.22/0.96  --sig_cnt_out                           false
% 3.22/0.96  --trig_cnt_out                          false
% 3.22/0.96  --trig_cnt_out_tolerance                1.
% 3.22/0.96  --trig_cnt_out_sk_spl                   false
% 3.22/0.96  --abstr_cl_out                          false
% 3.22/0.96  
% 3.22/0.96  ------ Global Options
% 3.22/0.96  
% 3.22/0.96  --schedule                              default
% 3.22/0.96  --add_important_lit                     false
% 3.22/0.96  --prop_solver_per_cl                    1000
% 3.22/0.96  --min_unsat_core                        false
% 3.22/0.96  --soft_assumptions                      false
% 3.22/0.96  --soft_lemma_size                       3
% 3.22/0.96  --prop_impl_unit_size                   0
% 3.22/0.96  --prop_impl_unit                        []
% 3.22/0.96  --share_sel_clauses                     true
% 3.22/0.96  --reset_solvers                         false
% 3.22/0.96  --bc_imp_inh                            [conj_cone]
% 3.22/0.96  --conj_cone_tolerance                   3.
% 3.22/0.96  --extra_neg_conj                        none
% 3.22/0.96  --large_theory_mode                     true
% 3.22/0.96  --prolific_symb_bound                   200
% 3.22/0.96  --lt_threshold                          2000
% 3.22/0.96  --clause_weak_htbl                      true
% 3.22/0.96  --gc_record_bc_elim                     false
% 3.22/0.96  
% 3.22/0.96  ------ Preprocessing Options
% 3.22/0.96  
% 3.22/0.96  --preprocessing_flag                    true
% 3.22/0.96  --time_out_prep_mult                    0.1
% 3.22/0.96  --splitting_mode                        input
% 3.22/0.96  --splitting_grd                         true
% 3.22/0.96  --splitting_cvd                         false
% 3.22/0.96  --splitting_cvd_svl                     false
% 3.22/0.96  --splitting_nvd                         32
% 3.22/0.96  --sub_typing                            true
% 3.22/0.96  --prep_gs_sim                           true
% 3.22/0.96  --prep_unflatten                        true
% 3.22/0.96  --prep_res_sim                          true
% 3.22/0.96  --prep_upred                            true
% 3.22/0.96  --prep_sem_filter                       exhaustive
% 3.22/0.96  --prep_sem_filter_out                   false
% 3.22/0.96  --pred_elim                             true
% 3.22/0.96  --res_sim_input                         true
% 3.22/0.96  --eq_ax_congr_red                       true
% 3.22/0.96  --pure_diseq_elim                       true
% 3.22/0.96  --brand_transform                       false
% 3.22/0.96  --non_eq_to_eq                          false
% 3.22/0.96  --prep_def_merge                        true
% 3.22/0.96  --prep_def_merge_prop_impl              false
% 3.22/0.96  --prep_def_merge_mbd                    true
% 3.22/0.96  --prep_def_merge_tr_red                 false
% 3.22/0.96  --prep_def_merge_tr_cl                  false
% 3.22/0.96  --smt_preprocessing                     true
% 3.22/0.96  --smt_ac_axioms                         fast
% 3.22/0.96  --preprocessed_out                      false
% 3.22/0.96  --preprocessed_stats                    false
% 3.22/0.96  
% 3.22/0.96  ------ Abstraction refinement Options
% 3.22/0.96  
% 3.22/0.96  --abstr_ref                             []
% 3.22/0.96  --abstr_ref_prep                        false
% 3.22/0.96  --abstr_ref_until_sat                   false
% 3.22/0.96  --abstr_ref_sig_restrict                funpre
% 3.22/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 3.22/0.96  --abstr_ref_under                       []
% 3.22/0.96  
% 3.22/0.96  ------ SAT Options
% 3.22/0.96  
% 3.22/0.96  --sat_mode                              false
% 3.22/0.96  --sat_fm_restart_options                ""
% 3.22/0.96  --sat_gr_def                            false
% 3.22/0.96  --sat_epr_types                         true
% 3.22/0.96  --sat_non_cyclic_types                  false
% 3.22/0.96  --sat_finite_models                     false
% 3.22/0.96  --sat_fm_lemmas                         false
% 3.22/0.96  --sat_fm_prep                           false
% 3.22/0.96  --sat_fm_uc_incr                        true
% 3.22/0.96  --sat_out_model                         small
% 3.22/0.96  --sat_out_clauses                       false
% 3.22/0.96  
% 3.22/0.96  ------ QBF Options
% 3.22/0.96  
% 3.22/0.96  --qbf_mode                              false
% 3.22/0.96  --qbf_elim_univ                         false
% 3.22/0.96  --qbf_dom_inst                          none
% 3.22/0.96  --qbf_dom_pre_inst                      false
% 3.22/0.96  --qbf_sk_in                             false
% 3.22/0.96  --qbf_pred_elim                         true
% 3.22/0.96  --qbf_split                             512
% 3.22/0.96  
% 3.22/0.96  ------ BMC1 Options
% 3.22/0.96  
% 3.22/0.96  --bmc1_incremental                      false
% 3.22/0.96  --bmc1_axioms                           reachable_all
% 3.22/0.96  --bmc1_min_bound                        0
% 3.22/0.96  --bmc1_max_bound                        -1
% 3.22/0.96  --bmc1_max_bound_default                -1
% 3.22/0.96  --bmc1_symbol_reachability              true
% 3.22/0.96  --bmc1_property_lemmas                  false
% 3.22/0.96  --bmc1_k_induction                      false
% 3.22/0.96  --bmc1_non_equiv_states                 false
% 3.22/0.96  --bmc1_deadlock                         false
% 3.22/0.96  --bmc1_ucm                              false
% 3.22/0.96  --bmc1_add_unsat_core                   none
% 3.22/0.96  --bmc1_unsat_core_children              false
% 3.22/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 3.22/0.96  --bmc1_out_stat                         full
% 3.22/0.96  --bmc1_ground_init                      false
% 3.22/0.96  --bmc1_pre_inst_next_state              false
% 3.22/0.96  --bmc1_pre_inst_state                   false
% 3.22/0.96  --bmc1_pre_inst_reach_state             false
% 3.22/0.96  --bmc1_out_unsat_core                   false
% 3.22/0.96  --bmc1_aig_witness_out                  false
% 3.22/0.96  --bmc1_verbose                          false
% 3.22/0.96  --bmc1_dump_clauses_tptp                false
% 3.22/0.96  --bmc1_dump_unsat_core_tptp             false
% 3.22/0.96  --bmc1_dump_file                        -
% 3.22/0.96  --bmc1_ucm_expand_uc_limit              128
% 3.22/0.96  --bmc1_ucm_n_expand_iterations          6
% 3.22/0.96  --bmc1_ucm_extend_mode                  1
% 3.22/0.96  --bmc1_ucm_init_mode                    2
% 3.22/0.96  --bmc1_ucm_cone_mode                    none
% 3.22/0.96  --bmc1_ucm_reduced_relation_type        0
% 3.22/0.96  --bmc1_ucm_relax_model                  4
% 3.22/0.96  --bmc1_ucm_full_tr_after_sat            true
% 3.22/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 3.22/0.96  --bmc1_ucm_layered_model                none
% 3.22/0.96  --bmc1_ucm_max_lemma_size               10
% 3.22/0.96  
% 3.22/0.96  ------ AIG Options
% 3.22/0.96  
% 3.22/0.96  --aig_mode                              false
% 3.22/0.96  
% 3.22/0.96  ------ Instantiation Options
% 3.22/0.96  
% 3.22/0.96  --instantiation_flag                    true
% 3.22/0.96  --inst_sos_flag                         false
% 3.22/0.96  --inst_sos_phase                        true
% 3.22/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.22/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.22/0.96  --inst_lit_sel_side                     num_symb
% 3.22/0.96  --inst_solver_per_active                1400
% 3.22/0.96  --inst_solver_calls_frac                1.
% 3.22/0.96  --inst_passive_queue_type               priority_queues
% 3.22/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.22/0.96  --inst_passive_queues_freq              [25;2]
% 3.22/0.96  --inst_dismatching                      true
% 3.22/0.96  --inst_eager_unprocessed_to_passive     true
% 3.22/0.96  --inst_prop_sim_given                   true
% 3.22/0.96  --inst_prop_sim_new                     false
% 3.22/0.96  --inst_subs_new                         false
% 3.22/0.96  --inst_eq_res_simp                      false
% 3.22/0.96  --inst_subs_given                       false
% 3.22/0.96  --inst_orphan_elimination               true
% 3.22/0.96  --inst_learning_loop_flag               true
% 3.22/0.96  --inst_learning_start                   3000
% 3.22/0.96  --inst_learning_factor                  2
% 3.22/0.96  --inst_start_prop_sim_after_learn       3
% 3.22/0.96  --inst_sel_renew                        solver
% 3.22/0.96  --inst_lit_activity_flag                true
% 3.22/0.96  --inst_restr_to_given                   false
% 3.22/0.96  --inst_activity_threshold               500
% 3.22/0.96  --inst_out_proof                        true
% 3.22/0.96  
% 3.22/0.96  ------ Resolution Options
% 3.22/0.96  
% 3.22/0.96  --resolution_flag                       true
% 3.22/0.96  --res_lit_sel                           adaptive
% 3.22/0.96  --res_lit_sel_side                      none
% 3.22/0.96  --res_ordering                          kbo
% 3.22/0.96  --res_to_prop_solver                    active
% 3.22/0.96  --res_prop_simpl_new                    false
% 3.22/0.96  --res_prop_simpl_given                  true
% 3.22/0.96  --res_passive_queue_type                priority_queues
% 3.22/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.22/0.96  --res_passive_queues_freq               [15;5]
% 3.22/0.96  --res_forward_subs                      full
% 3.22/0.96  --res_backward_subs                     full
% 3.22/0.96  --res_forward_subs_resolution           true
% 3.22/0.96  --res_backward_subs_resolution          true
% 3.22/0.96  --res_orphan_elimination                true
% 3.22/0.96  --res_time_limit                        2.
% 3.22/0.96  --res_out_proof                         true
% 3.22/0.96  
% 3.22/0.96  ------ Superposition Options
% 3.22/0.96  
% 3.22/0.96  --superposition_flag                    true
% 3.22/0.96  --sup_passive_queue_type                priority_queues
% 3.22/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.22/0.96  --sup_passive_queues_freq               [8;1;4]
% 3.22/0.96  --demod_completeness_check              fast
% 3.22/0.96  --demod_use_ground                      true
% 3.22/0.96  --sup_to_prop_solver                    passive
% 3.22/0.96  --sup_prop_simpl_new                    true
% 3.22/0.96  --sup_prop_simpl_given                  true
% 3.22/0.96  --sup_fun_splitting                     false
% 3.22/0.96  --sup_smt_interval                      50000
% 3.22/0.96  
% 3.22/0.96  ------ Superposition Simplification Setup
% 3.22/0.96  
% 3.22/0.96  --sup_indices_passive                   []
% 3.22/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.22/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.22/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.22/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 3.22/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.22/0.96  --sup_full_bw                           [BwDemod]
% 3.22/0.96  --sup_immed_triv                        [TrivRules]
% 3.22/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.22/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.22/0.96  --sup_immed_bw_main                     []
% 3.22/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.22/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 3.22/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.22/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.22/0.96  
% 3.22/0.96  ------ Combination Options
% 3.22/0.96  
% 3.22/0.96  --comb_res_mult                         3
% 3.22/0.96  --comb_sup_mult                         2
% 3.22/0.96  --comb_inst_mult                        10
% 3.22/0.96  
% 3.22/0.96  ------ Debug Options
% 3.22/0.96  
% 3.22/0.96  --dbg_backtrace                         false
% 3.22/0.96  --dbg_dump_prop_clauses                 false
% 3.22/0.96  --dbg_dump_prop_clauses_file            -
% 3.22/0.96  --dbg_out_stat                          false
% 3.22/0.96  ------ Parsing...
% 3.22/0.96  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.22/0.96  
% 3.22/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.22/0.96  
% 3.22/0.96  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.22/0.96  
% 3.22/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.22/0.96  ------ Proving...
% 3.22/0.96  ------ Problem Properties 
% 3.22/0.96  
% 3.22/0.96  
% 3.22/0.96  clauses                                 18
% 3.22/0.96  conjectures                             1
% 3.22/0.96  EPR                                     3
% 3.22/0.96  Horn                                    17
% 3.22/0.96  unary                                   5
% 3.22/0.96  binary                                  9
% 3.22/0.96  lits                                    35
% 3.22/0.96  lits eq                                 16
% 3.22/0.96  fd_pure                                 0
% 3.22/0.96  fd_pseudo                               0
% 3.22/0.96  fd_cond                                 0
% 3.22/0.96  fd_pseudo_cond                          1
% 3.22/0.96  AC symbols                              0
% 3.22/0.96  
% 3.22/0.96  ------ Schedule dynamic 5 is on 
% 3.22/0.96  
% 3.22/0.96  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.22/0.96  
% 3.22/0.96  
% 3.22/0.96  ------ 
% 3.22/0.96  Current options:
% 3.22/0.96  ------ 
% 3.22/0.96  
% 3.22/0.96  ------ Input Options
% 3.22/0.96  
% 3.22/0.96  --out_options                           all
% 3.22/0.96  --tptp_safe_out                         true
% 3.22/0.96  --problem_path                          ""
% 3.22/0.96  --include_path                          ""
% 3.22/0.96  --clausifier                            res/vclausify_rel
% 3.22/0.96  --clausifier_options                    --mode clausify
% 3.22/0.96  --stdin                                 false
% 3.22/0.96  --stats_out                             all
% 3.22/0.96  
% 3.22/0.96  ------ General Options
% 3.22/0.96  
% 3.22/0.96  --fof                                   false
% 3.22/0.96  --time_out_real                         305.
% 3.22/0.96  --time_out_virtual                      -1.
% 3.22/0.96  --symbol_type_check                     false
% 3.22/0.96  --clausify_out                          false
% 3.22/0.96  --sig_cnt_out                           false
% 3.22/0.96  --trig_cnt_out                          false
% 3.22/0.96  --trig_cnt_out_tolerance                1.
% 3.22/0.96  --trig_cnt_out_sk_spl                   false
% 3.22/0.96  --abstr_cl_out                          false
% 3.22/0.96  
% 3.22/0.96  ------ Global Options
% 3.22/0.96  
% 3.22/0.96  --schedule                              default
% 3.22/0.96  --add_important_lit                     false
% 3.22/0.96  --prop_solver_per_cl                    1000
% 3.22/0.96  --min_unsat_core                        false
% 3.22/0.96  --soft_assumptions                      false
% 3.22/0.96  --soft_lemma_size                       3
% 3.22/0.96  --prop_impl_unit_size                   0
% 3.22/0.96  --prop_impl_unit                        []
% 3.22/0.96  --share_sel_clauses                     true
% 3.22/0.96  --reset_solvers                         false
% 3.22/0.96  --bc_imp_inh                            [conj_cone]
% 3.22/0.96  --conj_cone_tolerance                   3.
% 3.22/0.96  --extra_neg_conj                        none
% 3.22/0.96  --large_theory_mode                     true
% 3.22/0.96  --prolific_symb_bound                   200
% 3.22/0.96  --lt_threshold                          2000
% 3.22/0.96  --clause_weak_htbl                      true
% 3.22/0.96  --gc_record_bc_elim                     false
% 3.22/0.96  
% 3.22/0.96  ------ Preprocessing Options
% 3.22/0.96  
% 3.22/0.96  --preprocessing_flag                    true
% 3.22/0.96  --time_out_prep_mult                    0.1
% 3.22/0.96  --splitting_mode                        input
% 3.22/0.96  --splitting_grd                         true
% 3.22/0.96  --splitting_cvd                         false
% 3.22/0.96  --splitting_cvd_svl                     false
% 3.22/0.96  --splitting_nvd                         32
% 3.22/0.96  --sub_typing                            true
% 3.22/0.96  --prep_gs_sim                           true
% 3.22/0.96  --prep_unflatten                        true
% 3.22/0.96  --prep_res_sim                          true
% 3.22/0.96  --prep_upred                            true
% 3.22/0.96  --prep_sem_filter                       exhaustive
% 3.22/0.96  --prep_sem_filter_out                   false
% 3.22/0.96  --pred_elim                             true
% 3.22/0.96  --res_sim_input                         true
% 3.22/0.97  --eq_ax_congr_red                       true
% 3.22/0.97  --pure_diseq_elim                       true
% 3.22/0.97  --brand_transform                       false
% 3.22/0.97  --non_eq_to_eq                          false
% 3.22/0.97  --prep_def_merge                        true
% 3.22/0.97  --prep_def_merge_prop_impl              false
% 3.22/0.97  --prep_def_merge_mbd                    true
% 3.22/0.97  --prep_def_merge_tr_red                 false
% 3.22/0.97  --prep_def_merge_tr_cl                  false
% 3.22/0.97  --smt_preprocessing                     true
% 3.22/0.97  --smt_ac_axioms                         fast
% 3.22/0.97  --preprocessed_out                      false
% 3.22/0.97  --preprocessed_stats                    false
% 3.22/0.97  
% 3.22/0.97  ------ Abstraction refinement Options
% 3.22/0.97  
% 3.22/0.97  --abstr_ref                             []
% 3.22/0.97  --abstr_ref_prep                        false
% 3.22/0.97  --abstr_ref_until_sat                   false
% 3.22/0.97  --abstr_ref_sig_restrict                funpre
% 3.22/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 3.22/0.97  --abstr_ref_under                       []
% 3.22/0.97  
% 3.22/0.97  ------ SAT Options
% 3.22/0.97  
% 3.22/0.97  --sat_mode                              false
% 3.22/0.97  --sat_fm_restart_options                ""
% 3.22/0.97  --sat_gr_def                            false
% 3.22/0.97  --sat_epr_types                         true
% 3.22/0.97  --sat_non_cyclic_types                  false
% 3.22/0.97  --sat_finite_models                     false
% 3.22/0.97  --sat_fm_lemmas                         false
% 3.22/0.97  --sat_fm_prep                           false
% 3.22/0.97  --sat_fm_uc_incr                        true
% 3.22/0.97  --sat_out_model                         small
% 3.22/0.97  --sat_out_clauses                       false
% 3.22/0.97  
% 3.22/0.97  ------ QBF Options
% 3.22/0.97  
% 3.22/0.97  --qbf_mode                              false
% 3.22/0.97  --qbf_elim_univ                         false
% 3.22/0.97  --qbf_dom_inst                          none
% 3.22/0.97  --qbf_dom_pre_inst                      false
% 3.22/0.97  --qbf_sk_in                             false
% 3.22/0.97  --qbf_pred_elim                         true
% 3.22/0.97  --qbf_split                             512
% 3.22/0.97  
% 3.22/0.97  ------ BMC1 Options
% 3.22/0.97  
% 3.22/0.97  --bmc1_incremental                      false
% 3.22/0.97  --bmc1_axioms                           reachable_all
% 3.22/0.97  --bmc1_min_bound                        0
% 3.22/0.97  --bmc1_max_bound                        -1
% 3.22/0.97  --bmc1_max_bound_default                -1
% 3.22/0.97  --bmc1_symbol_reachability              true
% 3.22/0.97  --bmc1_property_lemmas                  false
% 3.22/0.97  --bmc1_k_induction                      false
% 3.22/0.97  --bmc1_non_equiv_states                 false
% 3.22/0.97  --bmc1_deadlock                         false
% 3.22/0.97  --bmc1_ucm                              false
% 3.22/0.97  --bmc1_add_unsat_core                   none
% 3.22/0.97  --bmc1_unsat_core_children              false
% 3.22/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 3.22/0.97  --bmc1_out_stat                         full
% 3.22/0.97  --bmc1_ground_init                      false
% 3.22/0.97  --bmc1_pre_inst_next_state              false
% 3.22/0.97  --bmc1_pre_inst_state                   false
% 3.22/0.97  --bmc1_pre_inst_reach_state             false
% 3.22/0.97  --bmc1_out_unsat_core                   false
% 3.22/0.97  --bmc1_aig_witness_out                  false
% 3.22/0.97  --bmc1_verbose                          false
% 3.22/0.97  --bmc1_dump_clauses_tptp                false
% 3.22/0.97  --bmc1_dump_unsat_core_tptp             false
% 3.22/0.97  --bmc1_dump_file                        -
% 3.22/0.97  --bmc1_ucm_expand_uc_limit              128
% 3.22/0.97  --bmc1_ucm_n_expand_iterations          6
% 3.22/0.97  --bmc1_ucm_extend_mode                  1
% 3.22/0.97  --bmc1_ucm_init_mode                    2
% 3.22/0.97  --bmc1_ucm_cone_mode                    none
% 3.22/0.97  --bmc1_ucm_reduced_relation_type        0
% 3.22/0.97  --bmc1_ucm_relax_model                  4
% 3.22/0.97  --bmc1_ucm_full_tr_after_sat            true
% 3.22/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 3.22/0.97  --bmc1_ucm_layered_model                none
% 3.22/0.97  --bmc1_ucm_max_lemma_size               10
% 3.22/0.97  
% 3.22/0.97  ------ AIG Options
% 3.22/0.97  
% 3.22/0.97  --aig_mode                              false
% 3.22/0.97  
% 3.22/0.97  ------ Instantiation Options
% 3.22/0.97  
% 3.22/0.97  --instantiation_flag                    true
% 3.22/0.97  --inst_sos_flag                         false
% 3.22/0.97  --inst_sos_phase                        true
% 3.22/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.22/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.22/0.97  --inst_lit_sel_side                     none
% 3.22/0.97  --inst_solver_per_active                1400
% 3.22/0.97  --inst_solver_calls_frac                1.
% 3.22/0.97  --inst_passive_queue_type               priority_queues
% 3.22/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.22/0.97  --inst_passive_queues_freq              [25;2]
% 3.22/0.97  --inst_dismatching                      true
% 3.22/0.97  --inst_eager_unprocessed_to_passive     true
% 3.22/0.97  --inst_prop_sim_given                   true
% 3.22/0.97  --inst_prop_sim_new                     false
% 3.22/0.97  --inst_subs_new                         false
% 3.22/0.97  --inst_eq_res_simp                      false
% 3.22/0.97  --inst_subs_given                       false
% 3.22/0.97  --inst_orphan_elimination               true
% 3.22/0.97  --inst_learning_loop_flag               true
% 3.22/0.97  --inst_learning_start                   3000
% 3.22/0.97  --inst_learning_factor                  2
% 3.22/0.97  --inst_start_prop_sim_after_learn       3
% 3.22/0.97  --inst_sel_renew                        solver
% 3.22/0.97  --inst_lit_activity_flag                true
% 3.22/0.97  --inst_restr_to_given                   false
% 3.22/0.97  --inst_activity_threshold               500
% 3.22/0.97  --inst_out_proof                        true
% 3.22/0.97  
% 3.22/0.97  ------ Resolution Options
% 3.22/0.97  
% 3.22/0.97  --resolution_flag                       false
% 3.22/0.97  --res_lit_sel                           adaptive
% 3.22/0.97  --res_lit_sel_side                      none
% 3.22/0.97  --res_ordering                          kbo
% 3.22/0.97  --res_to_prop_solver                    active
% 3.22/0.97  --res_prop_simpl_new                    false
% 3.22/0.97  --res_prop_simpl_given                  true
% 3.22/0.97  --res_passive_queue_type                priority_queues
% 3.22/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.22/0.97  --res_passive_queues_freq               [15;5]
% 3.22/0.97  --res_forward_subs                      full
% 3.22/0.97  --res_backward_subs                     full
% 3.22/0.97  --res_forward_subs_resolution           true
% 3.22/0.97  --res_backward_subs_resolution          true
% 3.22/0.97  --res_orphan_elimination                true
% 3.22/0.97  --res_time_limit                        2.
% 3.22/0.97  --res_out_proof                         true
% 3.22/0.97  
% 3.22/0.97  ------ Superposition Options
% 3.22/0.97  
% 3.22/0.97  --superposition_flag                    true
% 3.22/0.97  --sup_passive_queue_type                priority_queues
% 3.22/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.22/0.97  --sup_passive_queues_freq               [8;1;4]
% 3.22/0.97  --demod_completeness_check              fast
% 3.22/0.97  --demod_use_ground                      true
% 3.22/0.97  --sup_to_prop_solver                    passive
% 3.22/0.97  --sup_prop_simpl_new                    true
% 3.22/0.97  --sup_prop_simpl_given                  true
% 3.22/0.97  --sup_fun_splitting                     false
% 3.22/0.97  --sup_smt_interval                      50000
% 3.22/0.97  
% 3.22/0.97  ------ Superposition Simplification Setup
% 3.22/0.97  
% 3.22/0.97  --sup_indices_passive                   []
% 3.22/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.22/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.22/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.22/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 3.22/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.22/0.97  --sup_full_bw                           [BwDemod]
% 3.22/0.97  --sup_immed_triv                        [TrivRules]
% 3.22/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.22/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.22/0.97  --sup_immed_bw_main                     []
% 3.22/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.22/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 3.22/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.22/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.22/0.97  
% 3.22/0.97  ------ Combination Options
% 3.22/0.97  
% 3.22/0.97  --comb_res_mult                         3
% 3.22/0.97  --comb_sup_mult                         2
% 3.22/0.97  --comb_inst_mult                        10
% 3.22/0.97  
% 3.22/0.97  ------ Debug Options
% 3.22/0.97  
% 3.22/0.97  --dbg_backtrace                         false
% 3.22/0.97  --dbg_dump_prop_clauses                 false
% 3.22/0.97  --dbg_dump_prop_clauses_file            -
% 3.22/0.97  --dbg_out_stat                          false
% 3.22/0.97  
% 3.22/0.97  
% 3.22/0.97  
% 3.22/0.97  
% 3.22/0.97  ------ Proving...
% 3.22/0.97  
% 3.22/0.97  
% 3.22/0.97  % SZS status Theorem for theBenchmark.p
% 3.22/0.97  
% 3.22/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 3.22/0.97  
% 3.22/0.97  fof(f16,conjecture,(
% 3.22/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 3.22/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.22/0.97  
% 3.22/0.97  fof(f17,negated_conjecture,(
% 3.22/0.97    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 3.22/0.97    inference(negated_conjecture,[],[f16])).
% 3.22/0.97  
% 3.22/0.97  fof(f30,plain,(
% 3.22/0.97    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 3.22/0.97    inference(ennf_transformation,[],[f17])).
% 3.22/0.97  
% 3.22/0.97  fof(f31,plain,(
% 3.22/0.97    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.22/0.97    inference(flattening,[],[f30])).
% 3.22/0.97  
% 3.22/0.97  fof(f35,plain,(
% 3.22/0.97    ? [X0] : (? [X1] : (((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.22/0.97    inference(nnf_transformation,[],[f31])).
% 3.22/0.97  
% 3.22/0.97  fof(f36,plain,(
% 3.22/0.97    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.22/0.97    inference(flattening,[],[f35])).
% 3.22/0.97  
% 3.22/0.97  fof(f38,plain,(
% 3.22/0.97    ( ! [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) != k2_tops_1(X0,sK1) | ~v4_pre_topc(sK1,X0)) & (k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) = k2_tops_1(X0,sK1) | v4_pre_topc(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.22/0.97    introduced(choice_axiom,[])).
% 3.22/0.97  
% 3.22/0.97  fof(f37,plain,(
% 3.22/0.97    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) != k2_tops_1(sK0,X1) | ~v4_pre_topc(X1,sK0)) & (k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) = k2_tops_1(sK0,X1) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 3.22/0.97    introduced(choice_axiom,[])).
% 3.22/0.97  
% 3.22/0.97  fof(f39,plain,(
% 3.22/0.97    ((k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)) & (k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 3.22/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f36,f38,f37])).
% 3.22/0.97  
% 3.22/0.97  fof(f62,plain,(
% 3.22/0.97    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)),
% 3.22/0.97    inference(cnf_transformation,[],[f39])).
% 3.22/0.97  
% 3.22/0.97  fof(f11,axiom,(
% 3.22/0.97    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 3.22/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.22/0.97  
% 3.22/0.97  fof(f22,plain,(
% 3.22/0.97    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.22/0.97    inference(ennf_transformation,[],[f11])).
% 3.22/0.97  
% 3.22/0.97  fof(f23,plain,(
% 3.22/0.97    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.22/0.97    inference(flattening,[],[f22])).
% 3.22/0.97  
% 3.22/0.97  fof(f53,plain,(
% 3.22/0.97    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.22/0.97    inference(cnf_transformation,[],[f23])).
% 3.22/0.97  
% 3.22/0.97  fof(f60,plain,(
% 3.22/0.97    l1_pre_topc(sK0)),
% 3.22/0.97    inference(cnf_transformation,[],[f39])).
% 3.22/0.97  
% 3.22/0.97  fof(f61,plain,(
% 3.22/0.97    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.22/0.97    inference(cnf_transformation,[],[f39])).
% 3.22/0.97  
% 3.22/0.97  fof(f10,axiom,(
% 3.22/0.97    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 3.22/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.22/0.97  
% 3.22/0.97  fof(f21,plain,(
% 3.22/0.97    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.22/0.97    inference(ennf_transformation,[],[f10])).
% 3.22/0.97  
% 3.22/0.97  fof(f52,plain,(
% 3.22/0.97    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.22/0.97    inference(cnf_transformation,[],[f21])).
% 3.22/0.97  
% 3.22/0.97  fof(f3,axiom,(
% 3.22/0.97    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.22/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.22/0.97  
% 3.22/0.97  fof(f45,plain,(
% 3.22/0.97    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.22/0.97    inference(cnf_transformation,[],[f3])).
% 3.22/0.97  
% 3.22/0.97  fof(f70,plain,(
% 3.22/0.97    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.22/0.97    inference(definition_unfolding,[],[f52,f45])).
% 3.22/0.97  
% 3.22/0.97  fof(f7,axiom,(
% 3.22/0.97    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 3.22/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.22/0.97  
% 3.22/0.97  fof(f49,plain,(
% 3.22/0.97    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 3.22/0.97    inference(cnf_transformation,[],[f7])).
% 3.22/0.97  
% 3.22/0.97  fof(f68,plain,(
% 3.22/0.97    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 3.22/0.97    inference(definition_unfolding,[],[f49,f45])).
% 3.22/0.97  
% 3.22/0.97  fof(f2,axiom,(
% 3.22/0.97    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 3.22/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.22/0.97  
% 3.22/0.97  fof(f34,plain,(
% 3.22/0.97    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 3.22/0.97    inference(nnf_transformation,[],[f2])).
% 3.22/0.97  
% 3.22/0.97  fof(f44,plain,(
% 3.22/0.97    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 3.22/0.97    inference(cnf_transformation,[],[f34])).
% 3.22/0.97  
% 3.22/0.97  fof(f65,plain,(
% 3.22/0.97    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) | ~r1_tarski(X0,X1)) )),
% 3.22/0.97    inference(definition_unfolding,[],[f44,f45])).
% 3.22/0.97  
% 3.22/0.97  fof(f12,axiom,(
% 3.22/0.97    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.22/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.22/0.97  
% 3.22/0.97  fof(f24,plain,(
% 3.22/0.97    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.22/0.97    inference(ennf_transformation,[],[f12])).
% 3.22/0.97  
% 3.22/0.97  fof(f25,plain,(
% 3.22/0.97    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.22/0.97    inference(flattening,[],[f24])).
% 3.22/0.97  
% 3.22/0.97  fof(f55,plain,(
% 3.22/0.97    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.22/0.97    inference(cnf_transformation,[],[f25])).
% 3.22/0.97  
% 3.22/0.97  fof(f9,axiom,(
% 3.22/0.97    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 3.22/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.22/0.97  
% 3.22/0.97  fof(f19,plain,(
% 3.22/0.97    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 3.22/0.97    inference(ennf_transformation,[],[f9])).
% 3.22/0.97  
% 3.22/0.97  fof(f20,plain,(
% 3.22/0.97    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.22/0.97    inference(flattening,[],[f19])).
% 3.22/0.97  
% 3.22/0.97  fof(f51,plain,(
% 3.22/0.97    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.22/0.97    inference(cnf_transformation,[],[f20])).
% 3.22/0.97  
% 3.22/0.97  fof(f8,axiom,(
% 3.22/0.97    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 3.22/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.22/0.97  
% 3.22/0.97  fof(f50,plain,(
% 3.22/0.97    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 3.22/0.97    inference(cnf_transformation,[],[f8])).
% 3.22/0.97  
% 3.22/0.97  fof(f64,plain,(
% 3.22/0.97    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 3.22/0.97    inference(definition_unfolding,[],[f50,f45])).
% 3.22/0.97  
% 3.22/0.97  fof(f69,plain,(
% 3.22/0.97    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.22/0.97    inference(definition_unfolding,[],[f51,f64])).
% 3.22/0.97  
% 3.22/0.97  fof(f15,axiom,(
% 3.22/0.97    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)))),
% 3.22/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.22/0.97  
% 3.22/0.97  fof(f29,plain,(
% 3.22/0.97    ! [X0] : (! [X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.22/0.97    inference(ennf_transformation,[],[f15])).
% 3.22/0.97  
% 3.22/0.97  fof(f58,plain,(
% 3.22/0.97    ( ! [X0,X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.22/0.97    inference(cnf_transformation,[],[f29])).
% 3.22/0.97  
% 3.22/0.97  fof(f1,axiom,(
% 3.22/0.97    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.22/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.22/0.97  
% 3.22/0.97  fof(f32,plain,(
% 3.22/0.97    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.22/0.97    inference(nnf_transformation,[],[f1])).
% 3.22/0.97  
% 3.22/0.97  fof(f33,plain,(
% 3.22/0.97    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.22/0.97    inference(flattening,[],[f32])).
% 3.22/0.97  
% 3.22/0.97  fof(f41,plain,(
% 3.22/0.97    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.22/0.97    inference(cnf_transformation,[],[f33])).
% 3.22/0.97  
% 3.22/0.97  fof(f71,plain,(
% 3.22/0.97    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.22/0.97    inference(equality_resolution,[],[f41])).
% 3.22/0.97  
% 3.22/0.97  fof(f5,axiom,(
% 3.22/0.97    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.22/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.22/0.97  
% 3.22/0.97  fof(f18,plain,(
% 3.22/0.97    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.22/0.97    inference(ennf_transformation,[],[f5])).
% 3.22/0.97  
% 3.22/0.97  fof(f47,plain,(
% 3.22/0.97    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.22/0.97    inference(cnf_transformation,[],[f18])).
% 3.22/0.97  
% 3.22/0.97  fof(f6,axiom,(
% 3.22/0.97    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.22/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.22/0.97  
% 3.22/0.97  fof(f48,plain,(
% 3.22/0.97    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.22/0.97    inference(cnf_transformation,[],[f6])).
% 3.22/0.97  
% 3.22/0.97  fof(f4,axiom,(
% 3.22/0.97    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 3.22/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.22/0.97  
% 3.22/0.97  fof(f46,plain,(
% 3.22/0.97    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.22/0.97    inference(cnf_transformation,[],[f4])).
% 3.22/0.97  
% 3.22/0.97  fof(f67,plain,(
% 3.22/0.97    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0) )),
% 3.22/0.97    inference(definition_unfolding,[],[f46,f64])).
% 3.22/0.97  
% 3.22/0.97  fof(f14,axiom,(
% 3.22/0.97    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)))),
% 3.22/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.22/0.97  
% 3.22/0.97  fof(f28,plain,(
% 3.22/0.97    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.22/0.97    inference(ennf_transformation,[],[f14])).
% 3.22/0.97  
% 3.22/0.97  fof(f57,plain,(
% 3.22/0.97    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.22/0.97    inference(cnf_transformation,[],[f28])).
% 3.22/0.97  
% 3.22/0.97  fof(f63,plain,(
% 3.22/0.97    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)),
% 3.22/0.97    inference(cnf_transformation,[],[f39])).
% 3.22/0.97  
% 3.22/0.97  fof(f54,plain,(
% 3.22/0.97    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.22/0.97    inference(cnf_transformation,[],[f23])).
% 3.22/0.97  
% 3.22/0.97  fof(f59,plain,(
% 3.22/0.97    v2_pre_topc(sK0)),
% 3.22/0.97    inference(cnf_transformation,[],[f39])).
% 3.22/0.97  
% 3.22/0.97  cnf(c_18,negated_conjecture,
% 3.22/0.97      ( v4_pre_topc(sK1,sK0)
% 3.22/0.97      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 3.22/0.97      inference(cnf_transformation,[],[f62]) ).
% 3.22/0.97  
% 3.22/0.97  cnf(c_169,plain,
% 3.22/0.97      ( v4_pre_topc(sK1,sK0)
% 3.22/0.97      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 3.22/0.97      inference(prop_impl,[status(thm)],[c_18]) ).
% 3.22/0.97  
% 3.22/0.97  cnf(c_12,plain,
% 3.22/0.97      ( ~ v4_pre_topc(X0,X1)
% 3.22/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.22/0.97      | ~ l1_pre_topc(X1)
% 3.22/0.97      | k2_pre_topc(X1,X0) = X0 ),
% 3.22/0.97      inference(cnf_transformation,[],[f53]) ).
% 3.22/0.97  
% 3.22/0.97  cnf(c_20,negated_conjecture,
% 3.22/0.97      ( l1_pre_topc(sK0) ),
% 3.22/0.97      inference(cnf_transformation,[],[f60]) ).
% 3.22/0.97  
% 3.22/0.97  cnf(c_369,plain,
% 3.22/0.97      ( ~ v4_pre_topc(X0,X1)
% 3.22/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.22/0.97      | k2_pre_topc(X1,X0) = X0
% 3.22/0.97      | sK0 != X1 ),
% 3.22/0.97      inference(resolution_lifted,[status(thm)],[c_12,c_20]) ).
% 3.22/0.97  
% 3.22/0.97  cnf(c_370,plain,
% 3.22/0.97      ( ~ v4_pre_topc(X0,sK0)
% 3.22/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.22/0.97      | k2_pre_topc(sK0,X0) = X0 ),
% 3.22/0.97      inference(unflattening,[status(thm)],[c_369]) ).
% 3.22/0.97  
% 3.22/0.97  cnf(c_419,plain,
% 3.22/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.22/0.97      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 3.22/0.97      | k2_pre_topc(sK0,X0) = X0
% 3.22/0.97      | sK1 != X0
% 3.22/0.97      | sK0 != sK0 ),
% 3.22/0.97      inference(resolution_lifted,[status(thm)],[c_169,c_370]) ).
% 3.22/0.97  
% 3.22/0.97  cnf(c_420,plain,
% 3.22/0.97      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.22/0.97      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 3.22/0.97      | k2_pre_topc(sK0,sK1) = sK1 ),
% 3.22/0.97      inference(unflattening,[status(thm)],[c_419]) ).
% 3.22/0.97  
% 3.22/0.97  cnf(c_19,negated_conjecture,
% 3.22/0.97      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.22/0.97      inference(cnf_transformation,[],[f61]) ).
% 3.22/0.97  
% 3.22/0.97  cnf(c_422,plain,
% 3.22/0.97      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 3.22/0.97      | k2_pre_topc(sK0,sK1) = sK1 ),
% 3.22/0.97      inference(global_propositional_subsumption,
% 3.22/0.97                [status(thm)],
% 3.22/0.97                [c_420,c_19]) ).
% 3.22/0.97  
% 3.22/0.97  cnf(c_526,plain,
% 3.22/0.97      ( k2_pre_topc(sK0,sK1) = sK1
% 3.22/0.97      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 3.22/0.97      inference(prop_impl,[status(thm)],[c_422]) ).
% 3.22/0.97  
% 3.22/0.97  cnf(c_527,plain,
% 3.22/0.97      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 3.22/0.97      | k2_pre_topc(sK0,sK1) = sK1 ),
% 3.22/0.97      inference(renaming,[status(thm)],[c_526]) ).
% 3.22/0.97  
% 3.22/0.97  cnf(c_1022,plain,
% 3.22/0.97      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.22/0.97      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.22/0.97  
% 3.22/0.97  cnf(c_10,plain,
% 3.22/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.22/0.97      | k5_xboole_0(X0,k3_xboole_0(X0,X2)) = k7_subset_1(X1,X0,X2) ),
% 3.22/0.97      inference(cnf_transformation,[],[f70]) ).
% 3.22/0.97  
% 3.22/0.97  cnf(c_1023,plain,
% 3.22/0.97      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k7_subset_1(X2,X0,X1)
% 3.22/0.97      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
% 3.22/0.97      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.22/0.97  
% 3.22/0.97  cnf(c_2676,plain,
% 3.22/0.97      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k3_xboole_0(sK1,X0)) ),
% 3.22/0.97      inference(superposition,[status(thm)],[c_1022,c_1023]) ).
% 3.22/0.97  
% 3.22/0.97  cnf(c_2761,plain,
% 3.22/0.97      ( k2_pre_topc(sK0,sK1) = sK1
% 3.22/0.97      | k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tops_1(sK0,sK1))) = k2_tops_1(sK0,sK1) ),
% 3.22/0.97      inference(superposition,[status(thm)],[c_527,c_2676]) ).
% 3.22/0.97  
% 3.22/0.97  cnf(c_8,plain,
% 3.22/0.97      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
% 3.22/0.97      inference(cnf_transformation,[],[f68]) ).
% 3.22/0.97  
% 3.22/0.97  cnf(c_1025,plain,
% 3.22/0.97      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
% 3.22/0.97      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.22/0.97  
% 3.22/0.97  cnf(c_4806,plain,
% 3.22/0.97      ( k2_pre_topc(sK0,sK1) = sK1
% 3.22/0.97      | r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top ),
% 3.22/0.97      inference(superposition,[status(thm)],[c_2761,c_1025]) ).
% 3.22/0.97  
% 3.22/0.97  cnf(c_3,plain,
% 3.22/0.97      ( ~ r1_tarski(X0,X1)
% 3.22/0.97      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
% 3.22/0.97      inference(cnf_transformation,[],[f65]) ).
% 3.22/0.97  
% 3.22/0.97  cnf(c_1029,plain,
% 3.22/0.97      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
% 3.22/0.97      | r1_tarski(X0,X1) != iProver_top ),
% 3.22/0.97      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.22/0.97  
% 3.22/0.97  cnf(c_4828,plain,
% 3.22/0.97      ( k2_pre_topc(sK0,sK1) = sK1
% 3.22/0.97      | k5_xboole_0(k2_tops_1(sK0,sK1),k3_xboole_0(k2_tops_1(sK0,sK1),sK1)) = k1_xboole_0 ),
% 3.22/0.97      inference(superposition,[status(thm)],[c_4806,c_1029]) ).
% 3.22/0.97  
% 3.22/0.97  cnf(c_13,plain,
% 3.22/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.22/0.97      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.22/0.97      | ~ l1_pre_topc(X1) ),
% 3.22/0.97      inference(cnf_transformation,[],[f55]) ).
% 3.22/0.97  
% 3.22/0.97  cnf(c_357,plain,
% 3.22/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.22/0.97      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.22/0.97      | sK0 != X1 ),
% 3.22/0.97      inference(resolution_lifted,[status(thm)],[c_13,c_20]) ).
% 3.22/0.97  
% 3.22/0.97  cnf(c_358,plain,
% 3.22/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.22/0.97      | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.22/0.97      inference(unflattening,[status(thm)],[c_357]) ).
% 3.22/0.97  
% 3.22/0.97  cnf(c_1019,plain,
% 3.22/0.97      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.22/0.97      | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.22/0.97      inference(predicate_to_equality,[status(thm)],[c_358]) ).
% 3.22/0.97  
% 3.22/0.97  cnf(c_2677,plain,
% 3.22/0.97      ( k5_xboole_0(k2_tops_1(sK0,X0),k3_xboole_0(k2_tops_1(sK0,X0),X1)) = k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,X0),X1)
% 3.22/0.97      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.22/0.97      inference(superposition,[status(thm)],[c_1019,c_1023]) ).
% 3.22/0.97  
% 3.22/0.97  cnf(c_2975,plain,
% 3.22/0.97      ( k5_xboole_0(k2_tops_1(sK0,sK1),k3_xboole_0(k2_tops_1(sK0,sK1),X0)) = k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),X0) ),
% 3.22/0.97      inference(superposition,[status(thm)],[c_1022,c_2677]) ).
% 3.22/0.97  
% 3.22/0.97  cnf(c_4836,plain,
% 3.22/0.97      ( k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),sK1) = k1_xboole_0
% 3.22/0.97      | k2_pre_topc(sK0,sK1) = sK1 ),
% 3.22/0.97      inference(demodulation,[status(thm)],[c_4828,c_2975]) ).
% 3.22/0.97  
% 3.22/0.97  cnf(c_9,plain,
% 3.22/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.22/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.22/0.97      | k5_xboole_0(X2,k5_xboole_0(X0,k3_xboole_0(X0,X2))) = k4_subset_1(X1,X2,X0) ),
% 3.22/0.97      inference(cnf_transformation,[],[f69]) ).
% 3.22/0.97  
% 3.22/0.97  cnf(c_1024,plain,
% 3.22/0.97      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k4_subset_1(X2,X0,X1)
% 3.22/0.97      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
% 3.22/0.97      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
% 3.22/0.97      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.22/0.97  
% 3.22/0.97  cnf(c_2692,plain,
% 3.22/0.97      ( k5_xboole_0(sK1,k5_xboole_0(X0,k3_xboole_0(X0,sK1))) = k4_subset_1(u1_struct_0(sK0),sK1,X0)
% 3.22/0.97      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.22/0.97      inference(superposition,[status(thm)],[c_1022,c_1024]) ).
% 3.22/0.97  
% 3.22/0.97  cnf(c_2785,plain,
% 3.22/0.97      ( k5_xboole_0(sK1,k5_xboole_0(k2_tops_1(sK0,X0),k3_xboole_0(k2_tops_1(sK0,X0),sK1))) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0))
% 3.22/0.97      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.22/0.97      inference(superposition,[status(thm)],[c_1019,c_2692]) ).
% 3.22/0.97  
% 3.22/0.97  cnf(c_3640,plain,
% 3.22/0.97      ( k5_xboole_0(sK1,k5_xboole_0(k2_tops_1(sK0,sK1),k3_xboole_0(k2_tops_1(sK0,sK1),sK1))) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
% 3.22/0.97      inference(superposition,[status(thm)],[c_1022,c_2785]) ).
% 3.22/0.97  
% 3.22/0.97  cnf(c_16,plain,
% 3.22/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.22/0.97      | ~ l1_pre_topc(X1)
% 3.22/0.97      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
% 3.22/0.97      inference(cnf_transformation,[],[f58]) ).
% 3.22/0.97  
% 3.22/0.97  cnf(c_333,plain,
% 3.22/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.22/0.97      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0)
% 3.22/0.97      | sK0 != X1 ),
% 3.22/0.97      inference(resolution_lifted,[status(thm)],[c_16,c_20]) ).
% 3.22/0.97  
% 3.22/0.97  cnf(c_334,plain,
% 3.22/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.22/0.97      | k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0) ),
% 3.22/0.97      inference(unflattening,[status(thm)],[c_333]) ).
% 3.22/0.97  
% 3.22/0.97  cnf(c_1021,plain,
% 3.22/0.97      ( k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0)
% 3.22/0.97      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.22/0.97      inference(predicate_to_equality,[status(thm)],[c_334]) ).
% 3.22/0.97  
% 3.22/0.97  cnf(c_1165,plain,
% 3.22/0.97      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 3.22/0.97      inference(superposition,[status(thm)],[c_1022,c_1021]) ).
% 3.22/0.97  
% 3.22/0.97  cnf(c_3647,plain,
% 3.22/0.97      ( k5_xboole_0(sK1,k5_xboole_0(k2_tops_1(sK0,sK1),k3_xboole_0(k2_tops_1(sK0,sK1),sK1))) = k2_pre_topc(sK0,sK1) ),
% 3.22/0.97      inference(light_normalisation,[status(thm)],[c_3640,c_1165]) ).
% 3.22/0.97  
% 3.22/0.97  cnf(c_3648,plain,
% 3.22/0.97      ( k5_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),sK1)) = k2_pre_topc(sK0,sK1) ),
% 3.22/0.97      inference(demodulation,[status(thm)],[c_3647,c_2975]) ).
% 3.22/0.97  
% 3.22/0.97  cnf(c_8921,plain,
% 3.22/0.97      ( k2_pre_topc(sK0,sK1) = k5_xboole_0(sK1,k1_xboole_0)
% 3.22/0.97      | k2_pre_topc(sK0,sK1) = sK1 ),
% 3.22/0.97      inference(superposition,[status(thm)],[c_4836,c_3648]) ).
% 3.22/0.97  
% 3.22/0.97  cnf(c_1,plain,
% 3.22/0.97      ( r1_tarski(X0,X0) ),
% 3.22/0.97      inference(cnf_transformation,[],[f71]) ).
% 3.22/0.97  
% 3.22/0.97  cnf(c_1030,plain,
% 3.22/0.97      ( r1_tarski(X0,X0) = iProver_top ),
% 3.22/0.97      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.22/0.97  
% 3.22/0.97  cnf(c_2145,plain,
% 3.22/0.97      ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k1_xboole_0 ),
% 3.22/0.97      inference(superposition,[status(thm)],[c_1030,c_1029]) ).
% 3.22/0.97  
% 3.22/0.97  cnf(c_6,plain,
% 3.22/0.97      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 3.22/0.97      inference(cnf_transformation,[],[f47]) ).
% 3.22/0.97  
% 3.22/0.97  cnf(c_1027,plain,
% 3.22/0.97      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 3.22/0.97      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.22/0.97  
% 3.22/0.97  cnf(c_1997,plain,
% 3.22/0.97      ( k3_xboole_0(X0,X0) = X0 ),
% 3.22/0.97      inference(superposition,[status(thm)],[c_1030,c_1027]) ).
% 3.22/0.97  
% 3.22/0.97  cnf(c_3424,plain,
% 3.22/0.97      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.22/0.97      inference(light_normalisation,[status(thm)],[c_2145,c_1997]) ).
% 3.22/0.97  
% 3.22/0.97  cnf(c_7,plain,
% 3.22/0.97      ( r1_tarski(k1_xboole_0,X0) ),
% 3.22/0.97      inference(cnf_transformation,[],[f48]) ).
% 3.22/0.97  
% 3.22/0.97  cnf(c_1026,plain,
% 3.22/0.97      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.22/0.97      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.22/0.97  
% 3.22/0.97  cnf(c_1998,plain,
% 3.22/0.97      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.22/0.97      inference(superposition,[status(thm)],[c_1026,c_1027]) ).
% 3.22/0.97  
% 3.22/0.97  cnf(c_5,plain,
% 3.22/0.97      ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
% 3.22/0.97      inference(cnf_transformation,[],[f67]) ).
% 3.22/0.97  
% 3.22/0.97  cnf(c_2752,plain,
% 3.22/0.97      ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) = X0 ),
% 3.22/0.97      inference(demodulation,[status(thm)],[c_1998,c_5]) ).
% 3.22/0.97  
% 3.22/0.97  cnf(c_3427,plain,
% 3.22/0.97      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.22/0.97      inference(demodulation,[status(thm)],[c_3424,c_2752]) ).
% 3.22/0.97  
% 3.22/0.97  cnf(c_8924,plain,
% 3.22/0.97      ( k2_pre_topc(sK0,sK1) = sK1 ),
% 3.22/0.97      inference(demodulation,[status(thm)],[c_8921,c_3427]) ).
% 3.22/0.97  
% 3.22/0.97  cnf(c_15,plain,
% 3.22/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.22/0.97      | ~ l1_pre_topc(X1)
% 3.22/0.97      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
% 3.22/0.97      inference(cnf_transformation,[],[f57]) ).
% 3.22/0.97  
% 3.22/0.97  cnf(c_345,plain,
% 3.22/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.22/0.97      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0)
% 3.22/0.97      | sK0 != X1 ),
% 3.22/0.97      inference(resolution_lifted,[status(thm)],[c_15,c_20]) ).
% 3.22/0.97  
% 3.22/0.97  cnf(c_346,plain,
% 3.22/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.22/0.97      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
% 3.22/0.97      inference(unflattening,[status(thm)],[c_345]) ).
% 3.22/0.97  
% 3.22/0.97  cnf(c_1020,plain,
% 3.22/0.97      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0)
% 3.22/0.97      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.22/0.97      inference(predicate_to_equality,[status(thm)],[c_346]) ).
% 3.22/0.97  
% 3.22/0.97  cnf(c_1190,plain,
% 3.22/0.97      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 3.22/0.97      inference(superposition,[status(thm)],[c_1022,c_1020]) ).
% 3.22/0.97  
% 3.22/0.97  cnf(c_8941,plain,
% 3.22/0.97      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 3.22/0.97      inference(demodulation,[status(thm)],[c_8924,c_1190]) ).
% 3.22/0.97  
% 3.22/0.97  cnf(c_17,negated_conjecture,
% 3.22/0.97      ( ~ v4_pre_topc(sK1,sK0)
% 3.22/0.97      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
% 3.22/0.97      inference(cnf_transformation,[],[f63]) ).
% 3.22/0.97  
% 3.22/0.97  cnf(c_167,plain,
% 3.22/0.97      ( ~ v4_pre_topc(sK1,sK0)
% 3.22/0.97      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
% 3.22/0.97      inference(prop_impl,[status(thm)],[c_17]) ).
% 3.22/0.97  
% 3.22/0.97  cnf(c_11,plain,
% 3.22/0.97      ( v4_pre_topc(X0,X1)
% 3.22/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.22/0.97      | ~ l1_pre_topc(X1)
% 3.22/0.97      | ~ v2_pre_topc(X1)
% 3.22/0.97      | k2_pre_topc(X1,X0) != X0 ),
% 3.22/0.97      inference(cnf_transformation,[],[f54]) ).
% 3.22/0.97  
% 3.22/0.97  cnf(c_21,negated_conjecture,
% 3.22/0.97      ( v2_pre_topc(sK0) ),
% 3.22/0.97      inference(cnf_transformation,[],[f59]) ).
% 3.22/0.97  
% 3.22/0.97  cnf(c_305,plain,
% 3.22/0.97      ( v4_pre_topc(X0,X1)
% 3.22/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.22/0.97      | ~ l1_pre_topc(X1)
% 3.22/0.97      | k2_pre_topc(X1,X0) != X0
% 3.22/0.97      | sK0 != X1 ),
% 3.22/0.97      inference(resolution_lifted,[status(thm)],[c_11,c_21]) ).
% 3.22/0.97  
% 3.22/0.97  cnf(c_306,plain,
% 3.22/0.97      ( v4_pre_topc(X0,sK0)
% 3.22/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.22/0.97      | ~ l1_pre_topc(sK0)
% 3.22/0.97      | k2_pre_topc(sK0,X0) != X0 ),
% 3.22/0.97      inference(unflattening,[status(thm)],[c_305]) ).
% 3.22/0.97  
% 3.22/0.97  cnf(c_310,plain,
% 3.22/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.22/0.97      | v4_pre_topc(X0,sK0)
% 3.22/0.97      | k2_pre_topc(sK0,X0) != X0 ),
% 3.22/0.97      inference(global_propositional_subsumption,
% 3.22/0.97                [status(thm)],
% 3.22/0.97                [c_306,c_20]) ).
% 3.22/0.97  
% 3.22/0.97  cnf(c_311,plain,
% 3.22/0.97      ( v4_pre_topc(X0,sK0)
% 3.22/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.22/0.97      | k2_pre_topc(sK0,X0) != X0 ),
% 3.22/0.97      inference(renaming,[status(thm)],[c_310]) ).
% 3.22/0.97  
% 3.22/0.97  cnf(c_430,plain,
% 3.22/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.22/0.97      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
% 3.22/0.97      | k2_pre_topc(sK0,X0) != X0
% 3.22/0.97      | sK1 != X0
% 3.22/0.97      | sK0 != sK0 ),
% 3.22/0.97      inference(resolution_lifted,[status(thm)],[c_167,c_311]) ).
% 3.22/0.97  
% 3.22/0.97  cnf(c_431,plain,
% 3.22/0.97      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.22/0.97      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
% 3.22/0.97      | k2_pre_topc(sK0,sK1) != sK1 ),
% 3.22/0.97      inference(unflattening,[status(thm)],[c_430]) ).
% 3.22/0.97  
% 3.22/0.97  cnf(c_433,plain,
% 3.22/0.97      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
% 3.22/0.97      | k2_pre_topc(sK0,sK1) != sK1 ),
% 3.22/0.97      inference(global_propositional_subsumption,
% 3.22/0.97                [status(thm)],
% 3.22/0.97                [c_431,c_19]) ).
% 3.22/0.97  
% 3.22/0.97  cnf(contradiction,plain,
% 3.22/0.97      ( $false ),
% 3.22/0.97      inference(minisat,[status(thm)],[c_8941,c_8924,c_433]) ).
% 3.22/0.97  
% 3.22/0.97  
% 3.22/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 3.22/0.97  
% 3.22/0.97  ------                               Statistics
% 3.22/0.97  
% 3.22/0.97  ------ General
% 3.22/0.97  
% 3.22/0.97  abstr_ref_over_cycles:                  0
% 3.22/0.97  abstr_ref_under_cycles:                 0
% 3.22/0.97  gc_basic_clause_elim:                   0
% 3.22/0.97  forced_gc_time:                         0
% 3.22/0.97  parsing_time:                           0.009
% 3.22/0.97  unif_index_cands_time:                  0.
% 3.22/0.97  unif_index_add_time:                    0.
% 3.22/0.97  orderings_time:                         0.
% 3.22/0.97  out_proof_time:                         0.007
% 3.22/0.97  total_time:                             0.308
% 3.22/0.97  num_of_symbols:                         48
% 3.22/0.97  num_of_terms:                           8748
% 3.22/0.97  
% 3.22/0.97  ------ Preprocessing
% 3.22/0.97  
% 3.22/0.97  num_of_splits:                          0
% 3.22/0.97  num_of_split_atoms:                     0
% 3.22/0.97  num_of_reused_defs:                     0
% 3.22/0.97  num_eq_ax_congr_red:                    11
% 3.22/0.97  num_of_sem_filtered_clauses:            1
% 3.22/0.97  num_of_subtypes:                        0
% 3.22/0.97  monotx_restored_types:                  0
% 3.22/0.97  sat_num_of_epr_types:                   0
% 3.22/0.97  sat_num_of_non_cyclic_types:            0
% 3.22/0.97  sat_guarded_non_collapsed_types:        0
% 3.22/0.97  num_pure_diseq_elim:                    0
% 3.22/0.97  simp_replaced_by:                       0
% 3.22/0.97  res_preprocessed:                       102
% 3.22/0.97  prep_upred:                             0
% 3.22/0.97  prep_unflattend:                        9
% 3.22/0.97  smt_new_axioms:                         0
% 3.22/0.97  pred_elim_cands:                        2
% 3.22/0.97  pred_elim:                              3
% 3.22/0.97  pred_elim_cl:                           3
% 3.22/0.97  pred_elim_cycles:                       5
% 3.22/0.97  merged_defs:                            16
% 3.22/0.97  merged_defs_ncl:                        0
% 3.22/0.97  bin_hyper_res:                          17
% 3.22/0.97  prep_cycles:                            4
% 3.22/0.97  pred_elim_time:                         0.004
% 3.22/0.97  splitting_time:                         0.
% 3.22/0.97  sem_filter_time:                        0.
% 3.22/0.97  monotx_time:                            0.
% 3.22/0.97  subtype_inf_time:                       0.
% 3.22/0.97  
% 3.22/0.97  ------ Problem properties
% 3.22/0.97  
% 3.22/0.97  clauses:                                18
% 3.22/0.97  conjectures:                            1
% 3.22/0.97  epr:                                    3
% 3.22/0.97  horn:                                   17
% 3.22/0.97  ground:                                 3
% 3.22/0.97  unary:                                  5
% 3.22/0.97  binary:                                 9
% 3.22/0.97  lits:                                   35
% 3.22/0.97  lits_eq:                                16
% 3.22/0.97  fd_pure:                                0
% 3.22/0.97  fd_pseudo:                              0
% 3.22/0.97  fd_cond:                                0
% 3.22/0.97  fd_pseudo_cond:                         1
% 3.22/0.97  ac_symbols:                             0
% 3.22/0.97  
% 3.22/0.97  ------ Propositional Solver
% 3.22/0.97  
% 3.22/0.97  prop_solver_calls:                      30
% 3.22/0.97  prop_fast_solver_calls:                 709
% 3.22/0.97  smt_solver_calls:                       0
% 3.22/0.97  smt_fast_solver_calls:                  0
% 3.22/0.97  prop_num_of_clauses:                    3829
% 3.22/0.97  prop_preprocess_simplified:             9336
% 3.22/0.97  prop_fo_subsumed:                       5
% 3.22/0.97  prop_solver_time:                       0.
% 3.22/0.97  smt_solver_time:                        0.
% 3.22/0.97  smt_fast_solver_time:                   0.
% 3.22/0.97  prop_fast_solver_time:                  0.
% 3.22/0.97  prop_unsat_core_time:                   0.
% 3.22/0.97  
% 3.22/0.97  ------ QBF
% 3.22/0.97  
% 3.22/0.97  qbf_q_res:                              0
% 3.22/0.97  qbf_num_tautologies:                    0
% 3.22/0.97  qbf_prep_cycles:                        0
% 3.22/0.97  
% 3.22/0.97  ------ BMC1
% 3.22/0.97  
% 3.22/0.97  bmc1_current_bound:                     -1
% 3.22/0.97  bmc1_last_solved_bound:                 -1
% 3.22/0.97  bmc1_unsat_core_size:                   -1
% 3.22/0.97  bmc1_unsat_core_parents_size:           -1
% 3.22/0.97  bmc1_merge_next_fun:                    0
% 3.22/0.97  bmc1_unsat_core_clauses_time:           0.
% 3.22/0.97  
% 3.22/0.97  ------ Instantiation
% 3.22/0.97  
% 3.22/0.97  inst_num_of_clauses:                    1317
% 3.22/0.97  inst_num_in_passive:                    588
% 3.22/0.97  inst_num_in_active:                     608
% 3.22/0.97  inst_num_in_unprocessed:                121
% 3.22/0.97  inst_num_of_loops:                      660
% 3.22/0.97  inst_num_of_learning_restarts:          0
% 3.22/0.97  inst_num_moves_active_passive:          48
% 3.22/0.97  inst_lit_activity:                      0
% 3.22/0.97  inst_lit_activity_moves:                1
% 3.22/0.97  inst_num_tautologies:                   0
% 3.22/0.97  inst_num_prop_implied:                  0
% 3.22/0.97  inst_num_existing_simplified:           0
% 3.22/0.97  inst_num_eq_res_simplified:             0
% 3.22/0.97  inst_num_child_elim:                    0
% 3.22/0.97  inst_num_of_dismatching_blockings:      184
% 3.22/0.97  inst_num_of_non_proper_insts:           1071
% 3.22/0.97  inst_num_of_duplicates:                 0
% 3.22/0.97  inst_inst_num_from_inst_to_res:         0
% 3.22/0.97  inst_dismatching_checking_time:         0.
% 3.22/0.97  
% 3.22/0.97  ------ Resolution
% 3.22/0.97  
% 3.22/0.97  res_num_of_clauses:                     0
% 3.22/0.97  res_num_in_passive:                     0
% 3.22/0.97  res_num_in_active:                      0
% 3.22/0.97  res_num_of_loops:                       106
% 3.22/0.97  res_forward_subset_subsumed:            63
% 3.22/0.97  res_backward_subset_subsumed:           0
% 3.22/0.97  res_forward_subsumed:                   0
% 3.22/0.97  res_backward_subsumed:                  0
% 3.22/0.97  res_forward_subsumption_resolution:     0
% 3.22/0.97  res_backward_subsumption_resolution:    0
% 3.22/0.97  res_clause_to_clause_subsumption:       575
% 3.22/0.97  res_orphan_elimination:                 0
% 3.22/0.97  res_tautology_del:                      90
% 3.22/0.97  res_num_eq_res_simplified:              0
% 3.22/0.97  res_num_sel_changes:                    0
% 3.22/0.97  res_moves_from_active_to_pass:          0
% 3.22/0.97  
% 3.22/0.97  ------ Superposition
% 3.22/0.97  
% 3.22/0.97  sup_time_total:                         0.
% 3.22/0.97  sup_time_generating:                    0.
% 3.22/0.97  sup_time_sim_full:                      0.
% 3.22/0.97  sup_time_sim_immed:                     0.
% 3.22/0.97  
% 3.22/0.97  sup_num_of_clauses:                     145
% 3.22/0.97  sup_num_in_active:                      110
% 3.22/0.97  sup_num_in_passive:                     35
% 3.22/0.97  sup_num_of_loops:                       130
% 3.22/0.97  sup_fw_superposition:                   113
% 3.22/0.97  sup_bw_superposition:                   84
% 3.22/0.97  sup_immediate_simplified:               95
% 3.22/0.97  sup_given_eliminated:                   1
% 3.22/0.97  comparisons_done:                       0
% 3.22/0.97  comparisons_avoided:                    12
% 3.22/0.97  
% 3.22/0.97  ------ Simplifications
% 3.22/0.97  
% 3.22/0.97  
% 3.22/0.97  sim_fw_subset_subsumed:                 13
% 3.22/0.97  sim_bw_subset_subsumed:                 6
% 3.22/0.97  sim_fw_subsumed:                        21
% 3.22/0.97  sim_bw_subsumed:                        1
% 3.22/0.97  sim_fw_subsumption_res:                 0
% 3.22/0.97  sim_bw_subsumption_res:                 0
% 3.22/0.97  sim_tautology_del:                      1
% 3.22/0.97  sim_eq_tautology_del:                   13
% 3.22/0.97  sim_eq_res_simp:                        2
% 3.22/0.97  sim_fw_demodulated:                     53
% 3.22/0.97  sim_bw_demodulated:                     16
% 3.22/0.97  sim_light_normalised:                   36
% 3.22/0.97  sim_joinable_taut:                      0
% 3.22/0.97  sim_joinable_simp:                      0
% 3.22/0.97  sim_ac_normalised:                      0
% 3.22/0.97  sim_smt_subsumption:                    0
% 3.22/0.97  
%------------------------------------------------------------------------------
