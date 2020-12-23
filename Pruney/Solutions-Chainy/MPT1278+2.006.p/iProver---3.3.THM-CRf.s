%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:15:33 EST 2020

% Result     : Theorem 2.97s
% Output     : CNFRefutation 2.97s
% Verified   : 
% Statistics : Number of formulae       :  176 (1410 expanded)
%              Number of clauses        :  110 ( 409 expanded)
%              Number of leaves         :   21 ( 359 expanded)
%              Depth                    :   20
%              Number of atoms          :  469 (6626 expanded)
%              Number of equality atoms :  172 (1402 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v3_tops_1(X1,X0)
              & v3_pre_topc(X1,X0) )
           => k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ( v3_tops_1(X1,X0)
                & v3_pre_topc(X1,X0) )
             => k1_xboole_0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f42,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 != X1
          & v3_tops_1(X1,X0)
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f43,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 != X1
          & v3_tops_1(X1,X0)
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f42])).

fof(f48,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k1_xboole_0 != X1
          & v3_tops_1(X1,X0)
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k1_xboole_0 != sK1
        & v3_tops_1(sK1,X0)
        & v3_pre_topc(sK1,X0)
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k1_xboole_0 != X1
            & v3_tops_1(X1,X0)
            & v3_pre_topc(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( k1_xboole_0 != X1
          & v3_tops_1(X1,sK0)
          & v3_pre_topc(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( k1_xboole_0 != sK1
    & v3_tops_1(sK1,sK0)
    & v3_pre_topc(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f43,f48,f47])).

fof(f72,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f49])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f71,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | k1_xboole_0 != k1_tops_1(X0,X1) )
            & ( k1_xboole_0 = k1_tops_1(X0,X1)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_tops_1(X0,X1)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tops_1(X1,X0)
           => v2_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tops_1(X1,X0)
          | ~ v3_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tops_1(X1,X0)
          | ~ v3_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f69,plain,(
    ! [X0,X1] :
      ( v2_tops_1(X1,X0)
      | ~ v3_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f74,plain,(
    v3_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
           => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,X1)))
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,X1)))
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,X1)))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f73,plain,(
    v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f57,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tops_1(X1,X0)
          <=> v2_tops_1(k2_pre_topc(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tops_1(X1,X0)
          <=> v2_tops_1(k2_pre_topc(X0,X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tops_1(X1,X0)
              | ~ v2_tops_1(k2_pre_topc(X0,X1),X0) )
            & ( v2_tops_1(k2_pre_topc(X0,X1),X0)
              | ~ v3_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v2_tops_1(k2_pre_topc(X0,X1),X0)
      | ~ v3_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_xboole_0(X1)
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f70,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f37])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) )
            & ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f4,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f53,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f75,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_921,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_24,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_524,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_24])).

cnf(c_525,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_524])).

cnf(c_912,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_525])).

cnf(c_1678,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_921,c_912])).

cnf(c_18,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_470,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,X0) = k1_xboole_0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_24])).

cnf(c_471,plain,
    ( ~ v2_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_470])).

cnf(c_916,plain,
    ( k1_tops_1(sK0,X0) = k1_xboole_0
    | v2_tops_1(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_471])).

cnf(c_1542,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0
    | v2_tops_1(sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_921,c_916])).

cnf(c_19,plain,
    ( v2_tops_1(X0,X1)
    | ~ v3_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_21,negated_conjecture,
    ( v3_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_435,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK0 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_21])).

cnf(c_436,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_435])).

cnf(c_1022,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,sK1) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_471])).

cnf(c_1664,plain,
    ( k1_tops_1(sK0,sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1542,c_24,c_23,c_436,c_1022])).

cnf(c_1685,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_xboole_0) = k2_tops_1(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_1678,c_1664])).

cnf(c_13,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k1_tops_1(X1,k2_pre_topc(X1,X0))) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_22,negated_conjecture,
    ( v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_281,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k1_tops_1(X1,k2_pre_topc(X1,X0))) = k2_pre_topc(X1,X0)
    | sK0 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_22])).

cnf(c_282,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) = k2_pre_topc(sK0,sK1) ),
    inference(unflattening,[status(thm)],[c_281])).

cnf(c_284,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) = k2_pre_topc(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_282,c_24,c_23])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_536,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_24])).

cnf(c_537,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_536])).

cnf(c_911,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_537])).

cnf(c_1085,plain,
    ( m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_284,c_911])).

cnf(c_28,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_1012,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_537])).

cnf(c_1013,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1012])).

cnf(c_1855,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1085,c_28,c_1013])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_923,plain,
    ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1860,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X0) = k4_xboole_0(k2_pre_topc(sK0,sK1),X0) ),
    inference(superposition,[status(thm)],[c_1855,c_923])).

cnf(c_2213,plain,
    ( k4_xboole_0(k2_pre_topc(sK0,sK1),k1_xboole_0) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_1685,c_1860])).

cnf(c_2,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2215,plain,
    ( k2_tops_1(sK0,sK1) = k2_pre_topc(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_2213,c_2])).

cnf(c_2538,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_xboole_0) = k2_pre_topc(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_2215,c_1685])).

cnf(c_5,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_922,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1677,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_xboole_0),k1_tops_1(sK0,k1_xboole_0)) = k2_tops_1(sK0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_922,c_912])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,k1_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_512,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,k1_tops_1(X1,X0)) = k1_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_24])).

cnf(c_513,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,k1_tops_1(sK0,X0)) = k1_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_512])).

cnf(c_913,plain,
    ( k1_tops_1(sK0,k1_tops_1(sK0,X0)) = k1_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_513])).

cnf(c_1135,plain,
    ( k1_tops_1(sK0,k1_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_921,c_913])).

cnf(c_1668,plain,
    ( k1_tops_1(sK0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1664,c_1135])).

cnf(c_2153,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_xboole_0),k1_xboole_0) = k2_tops_1(sK0,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_1677,c_1668])).

cnf(c_1862,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_xboole_0
    | v2_tops_1(k2_pre_topc(sK0,sK1),sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1855,c_916])).

cnf(c_9,plain,
    ( v2_tops_1(k2_pre_topc(X0,X1),X0)
    | ~ v3_tops_1(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_424,plain,
    ( v2_tops_1(k2_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | sK0 != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_21])).

cnf(c_425,plain,
    ( v2_tops_1(k2_pre_topc(sK0,sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_424])).

cnf(c_1019,plain,
    ( ~ v2_tops_1(k2_pre_topc(sK0,sK1),sK0)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_471])).

cnf(c_3078,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1862,c_24,c_23,c_425,c_1012,c_1019])).

cnf(c_3082,plain,
    ( k2_pre_topc(sK0,k1_xboole_0) = k2_pre_topc(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_3078,c_284])).

cnf(c_3313,plain,
    ( k2_tops_1(sK0,k1_xboole_0) = k2_pre_topc(sK0,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_2538,c_2153,c_3082])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_6,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_290,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k1_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_6])).

cnf(c_291,plain,
    ( v4_pre_topc(k1_xboole_0,X0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(unflattening,[status(thm)],[c_290])).

cnf(c_303,plain,
    ( v4_pre_topc(k1_xboole_0,X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_291,c_5])).

cnf(c_25,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_314,plain,
    ( v4_pre_topc(k1_xboole_0,X0)
    | ~ l1_pre_topc(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_303,c_25])).

cnf(c_315,plain,
    ( v4_pre_topc(k1_xboole_0,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_314])).

cnf(c_317,plain,
    ( v4_pre_topc(k1_xboole_0,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_315,c_24])).

cnf(c_16,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),X0,k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_325,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),X0,k1_tops_1(X1,X0)) = k2_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_25])).

cnf(c_326,plain,
    ( ~ v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k7_subset_1(u1_struct_0(sK0),X0,k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_325])).

cnf(c_330,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_pre_topc(X0,sK0)
    | k7_subset_1(u1_struct_0(sK0),X0,k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_326,c_24])).

cnf(c_331,plain,
    ( ~ v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),X0,k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
    inference(renaming,[status(thm)],[c_330])).

cnf(c_395,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),X0,k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0)
    | sK0 != sK0
    | k1_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_317,c_331])).

cnf(c_396,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),k1_xboole_0,k1_tops_1(sK0,k1_xboole_0)) = k2_tops_1(sK0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_395])).

cnf(c_402,plain,
    ( k7_subset_1(u1_struct_0(sK0),k1_xboole_0,k1_tops_1(sK0,k1_xboole_0)) = k2_tops_1(sK0,k1_xboole_0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_396,c_5])).

cnf(c_2067,plain,
    ( k7_subset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0) = k2_tops_1(sK0,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_1668,c_402])).

cnf(c_3315,plain,
    ( k7_subset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0) = k2_pre_topc(sK0,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_3313,c_2067])).

cnf(c_1277,plain,
    ( k7_subset_1(X0,k1_xboole_0,X1) = k4_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_922,c_923])).

cnf(c_1,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_274,plain,
    ( k4_xboole_0(X0,X1) != X2
    | k1_xboole_0 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_3])).

cnf(c_275,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(unflattening,[status(thm)],[c_274])).

cnf(c_1287,plain,
    ( k7_subset_1(X0,k1_xboole_0,X1) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1277,c_275])).

cnf(c_3845,plain,
    ( k2_pre_topc(sK0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3315,c_1287])).

cnf(c_1278,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
    inference(superposition,[status(thm)],[c_921,c_923])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_500,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_24])).

cnf(c_501,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k1_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_500])).

cnf(c_914,plain,
    ( k7_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k1_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_501])).

cnf(c_1445,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_921,c_914])).

cnf(c_1459,plain,
    ( k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_1278,c_1445])).

cnf(c_2128,plain,
    ( k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1459,c_1664])).

cnf(c_2540,plain,
    ( k4_xboole_0(sK1,k2_pre_topc(sK0,sK1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2215,c_2128])).

cnf(c_3091,plain,
    ( k4_xboole_0(sK1,k2_pre_topc(sK0,k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3082,c_2540])).

cnf(c_3853,plain,
    ( k4_xboole_0(sK1,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3845,c_3091])).

cnf(c_670,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2077,plain,
    ( k4_xboole_0(sK1,k1_xboole_0) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k4_xboole_0(sK1,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_670])).

cnf(c_2078,plain,
    ( k4_xboole_0(sK1,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k4_xboole_0(sK1,k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2077])).

cnf(c_1062,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_670])).

cnf(c_1563,plain,
    ( sK1 != k4_xboole_0(sK1,k1_xboole_0)
    | k1_xboole_0 != k4_xboole_0(sK1,k1_xboole_0)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_1062])).

cnf(c_1109,plain,
    ( X0 != X1
    | sK1 != X1
    | sK1 = X0 ),
    inference(instantiation,[status(thm)],[c_670])).

cnf(c_1249,plain,
    ( X0 != sK1
    | sK1 = X0
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1109])).

cnf(c_1394,plain,
    ( k4_xboole_0(sK1,k1_xboole_0) != sK1
    | sK1 = k4_xboole_0(sK1,k1_xboole_0)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1249])).

cnf(c_669,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1117,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_669])).

cnf(c_1111,plain,
    ( k4_xboole_0(sK1,k1_xboole_0) = sK1 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_690,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_669])).

cnf(c_20,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f75])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3853,c_2078,c_1563,c_1394,c_1117,c_1111,c_690,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 21:04:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.97/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.97/1.02  
% 2.97/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.97/1.02  
% 2.97/1.02  ------  iProver source info
% 2.97/1.02  
% 2.97/1.02  git: date: 2020-06-30 10:37:57 +0100
% 2.97/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.97/1.02  git: non_committed_changes: false
% 2.97/1.02  git: last_make_outside_of_git: false
% 2.97/1.02  
% 2.97/1.02  ------ 
% 2.97/1.02  
% 2.97/1.02  ------ Input Options
% 2.97/1.02  
% 2.97/1.02  --out_options                           all
% 2.97/1.02  --tptp_safe_out                         true
% 2.97/1.02  --problem_path                          ""
% 2.97/1.02  --include_path                          ""
% 2.97/1.02  --clausifier                            res/vclausify_rel
% 2.97/1.02  --clausifier_options                    --mode clausify
% 2.97/1.02  --stdin                                 false
% 2.97/1.02  --stats_out                             all
% 2.97/1.02  
% 2.97/1.02  ------ General Options
% 2.97/1.02  
% 2.97/1.02  --fof                                   false
% 2.97/1.02  --time_out_real                         305.
% 2.97/1.02  --time_out_virtual                      -1.
% 2.97/1.02  --symbol_type_check                     false
% 2.97/1.02  --clausify_out                          false
% 2.97/1.02  --sig_cnt_out                           false
% 2.97/1.02  --trig_cnt_out                          false
% 2.97/1.02  --trig_cnt_out_tolerance                1.
% 2.97/1.02  --trig_cnt_out_sk_spl                   false
% 2.97/1.02  --abstr_cl_out                          false
% 2.97/1.02  
% 2.97/1.02  ------ Global Options
% 2.97/1.02  
% 2.97/1.02  --schedule                              default
% 2.97/1.02  --add_important_lit                     false
% 2.97/1.02  --prop_solver_per_cl                    1000
% 2.97/1.02  --min_unsat_core                        false
% 2.97/1.02  --soft_assumptions                      false
% 2.97/1.02  --soft_lemma_size                       3
% 2.97/1.02  --prop_impl_unit_size                   0
% 2.97/1.02  --prop_impl_unit                        []
% 2.97/1.02  --share_sel_clauses                     true
% 2.97/1.02  --reset_solvers                         false
% 2.97/1.02  --bc_imp_inh                            [conj_cone]
% 2.97/1.02  --conj_cone_tolerance                   3.
% 2.97/1.02  --extra_neg_conj                        none
% 2.97/1.02  --large_theory_mode                     true
% 2.97/1.02  --prolific_symb_bound                   200
% 2.97/1.02  --lt_threshold                          2000
% 2.97/1.02  --clause_weak_htbl                      true
% 2.97/1.02  --gc_record_bc_elim                     false
% 2.97/1.02  
% 2.97/1.02  ------ Preprocessing Options
% 2.97/1.02  
% 2.97/1.02  --preprocessing_flag                    true
% 2.97/1.02  --time_out_prep_mult                    0.1
% 2.97/1.02  --splitting_mode                        input
% 2.97/1.02  --splitting_grd                         true
% 2.97/1.02  --splitting_cvd                         false
% 2.97/1.02  --splitting_cvd_svl                     false
% 2.97/1.02  --splitting_nvd                         32
% 2.97/1.02  --sub_typing                            true
% 2.97/1.02  --prep_gs_sim                           true
% 2.97/1.02  --prep_unflatten                        true
% 2.97/1.02  --prep_res_sim                          true
% 2.97/1.02  --prep_upred                            true
% 2.97/1.02  --prep_sem_filter                       exhaustive
% 2.97/1.02  --prep_sem_filter_out                   false
% 2.97/1.02  --pred_elim                             true
% 2.97/1.02  --res_sim_input                         true
% 2.97/1.02  --eq_ax_congr_red                       true
% 2.97/1.02  --pure_diseq_elim                       true
% 2.97/1.02  --brand_transform                       false
% 2.97/1.02  --non_eq_to_eq                          false
% 2.97/1.02  --prep_def_merge                        true
% 2.97/1.02  --prep_def_merge_prop_impl              false
% 2.97/1.02  --prep_def_merge_mbd                    true
% 2.97/1.02  --prep_def_merge_tr_red                 false
% 2.97/1.02  --prep_def_merge_tr_cl                  false
% 2.97/1.02  --smt_preprocessing                     true
% 2.97/1.02  --smt_ac_axioms                         fast
% 2.97/1.02  --preprocessed_out                      false
% 2.97/1.02  --preprocessed_stats                    false
% 2.97/1.02  
% 2.97/1.02  ------ Abstraction refinement Options
% 2.97/1.02  
% 2.97/1.02  --abstr_ref                             []
% 2.97/1.02  --abstr_ref_prep                        false
% 2.97/1.02  --abstr_ref_until_sat                   false
% 2.97/1.02  --abstr_ref_sig_restrict                funpre
% 2.97/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.97/1.02  --abstr_ref_under                       []
% 2.97/1.02  
% 2.97/1.02  ------ SAT Options
% 2.97/1.02  
% 2.97/1.02  --sat_mode                              false
% 2.97/1.02  --sat_fm_restart_options                ""
% 2.97/1.02  --sat_gr_def                            false
% 2.97/1.02  --sat_epr_types                         true
% 2.97/1.02  --sat_non_cyclic_types                  false
% 2.97/1.02  --sat_finite_models                     false
% 2.97/1.02  --sat_fm_lemmas                         false
% 2.97/1.02  --sat_fm_prep                           false
% 2.97/1.02  --sat_fm_uc_incr                        true
% 2.97/1.02  --sat_out_model                         small
% 2.97/1.02  --sat_out_clauses                       false
% 2.97/1.02  
% 2.97/1.02  ------ QBF Options
% 2.97/1.02  
% 2.97/1.02  --qbf_mode                              false
% 2.97/1.02  --qbf_elim_univ                         false
% 2.97/1.02  --qbf_dom_inst                          none
% 2.97/1.02  --qbf_dom_pre_inst                      false
% 2.97/1.02  --qbf_sk_in                             false
% 2.97/1.02  --qbf_pred_elim                         true
% 2.97/1.02  --qbf_split                             512
% 2.97/1.02  
% 2.97/1.02  ------ BMC1 Options
% 2.97/1.02  
% 2.97/1.02  --bmc1_incremental                      false
% 2.97/1.02  --bmc1_axioms                           reachable_all
% 2.97/1.02  --bmc1_min_bound                        0
% 2.97/1.02  --bmc1_max_bound                        -1
% 2.97/1.02  --bmc1_max_bound_default                -1
% 2.97/1.02  --bmc1_symbol_reachability              true
% 2.97/1.02  --bmc1_property_lemmas                  false
% 2.97/1.02  --bmc1_k_induction                      false
% 2.97/1.02  --bmc1_non_equiv_states                 false
% 2.97/1.02  --bmc1_deadlock                         false
% 2.97/1.02  --bmc1_ucm                              false
% 2.97/1.02  --bmc1_add_unsat_core                   none
% 2.97/1.02  --bmc1_unsat_core_children              false
% 2.97/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.97/1.02  --bmc1_out_stat                         full
% 2.97/1.02  --bmc1_ground_init                      false
% 2.97/1.02  --bmc1_pre_inst_next_state              false
% 2.97/1.02  --bmc1_pre_inst_state                   false
% 2.97/1.02  --bmc1_pre_inst_reach_state             false
% 2.97/1.02  --bmc1_out_unsat_core                   false
% 2.97/1.02  --bmc1_aig_witness_out                  false
% 2.97/1.02  --bmc1_verbose                          false
% 2.97/1.02  --bmc1_dump_clauses_tptp                false
% 2.97/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.97/1.02  --bmc1_dump_file                        -
% 2.97/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.97/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.97/1.02  --bmc1_ucm_extend_mode                  1
% 2.97/1.02  --bmc1_ucm_init_mode                    2
% 2.97/1.02  --bmc1_ucm_cone_mode                    none
% 2.97/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.97/1.02  --bmc1_ucm_relax_model                  4
% 2.97/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.97/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.97/1.02  --bmc1_ucm_layered_model                none
% 2.97/1.02  --bmc1_ucm_max_lemma_size               10
% 2.97/1.02  
% 2.97/1.02  ------ AIG Options
% 2.97/1.02  
% 2.97/1.02  --aig_mode                              false
% 2.97/1.02  
% 2.97/1.02  ------ Instantiation Options
% 2.97/1.02  
% 2.97/1.02  --instantiation_flag                    true
% 2.97/1.02  --inst_sos_flag                         false
% 2.97/1.02  --inst_sos_phase                        true
% 2.97/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.97/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.97/1.02  --inst_lit_sel_side                     num_symb
% 2.97/1.02  --inst_solver_per_active                1400
% 2.97/1.02  --inst_solver_calls_frac                1.
% 2.97/1.02  --inst_passive_queue_type               priority_queues
% 2.97/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.97/1.02  --inst_passive_queues_freq              [25;2]
% 2.97/1.02  --inst_dismatching                      true
% 2.97/1.02  --inst_eager_unprocessed_to_passive     true
% 2.97/1.02  --inst_prop_sim_given                   true
% 2.97/1.02  --inst_prop_sim_new                     false
% 2.97/1.02  --inst_subs_new                         false
% 2.97/1.02  --inst_eq_res_simp                      false
% 2.97/1.02  --inst_subs_given                       false
% 2.97/1.02  --inst_orphan_elimination               true
% 2.97/1.02  --inst_learning_loop_flag               true
% 2.97/1.02  --inst_learning_start                   3000
% 2.97/1.02  --inst_learning_factor                  2
% 2.97/1.02  --inst_start_prop_sim_after_learn       3
% 2.97/1.02  --inst_sel_renew                        solver
% 2.97/1.02  --inst_lit_activity_flag                true
% 2.97/1.02  --inst_restr_to_given                   false
% 2.97/1.02  --inst_activity_threshold               500
% 2.97/1.02  --inst_out_proof                        true
% 2.97/1.02  
% 2.97/1.02  ------ Resolution Options
% 2.97/1.02  
% 2.97/1.02  --resolution_flag                       true
% 2.97/1.02  --res_lit_sel                           adaptive
% 2.97/1.02  --res_lit_sel_side                      none
% 2.97/1.02  --res_ordering                          kbo
% 2.97/1.02  --res_to_prop_solver                    active
% 2.97/1.02  --res_prop_simpl_new                    false
% 2.97/1.02  --res_prop_simpl_given                  true
% 2.97/1.02  --res_passive_queue_type                priority_queues
% 2.97/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.97/1.02  --res_passive_queues_freq               [15;5]
% 2.97/1.02  --res_forward_subs                      full
% 2.97/1.02  --res_backward_subs                     full
% 2.97/1.02  --res_forward_subs_resolution           true
% 2.97/1.02  --res_backward_subs_resolution          true
% 2.97/1.02  --res_orphan_elimination                true
% 2.97/1.02  --res_time_limit                        2.
% 2.97/1.02  --res_out_proof                         true
% 2.97/1.02  
% 2.97/1.02  ------ Superposition Options
% 2.97/1.02  
% 2.97/1.02  --superposition_flag                    true
% 2.97/1.02  --sup_passive_queue_type                priority_queues
% 2.97/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.97/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.97/1.02  --demod_completeness_check              fast
% 2.97/1.02  --demod_use_ground                      true
% 2.97/1.02  --sup_to_prop_solver                    passive
% 2.97/1.02  --sup_prop_simpl_new                    true
% 2.97/1.02  --sup_prop_simpl_given                  true
% 2.97/1.02  --sup_fun_splitting                     false
% 2.97/1.02  --sup_smt_interval                      50000
% 2.97/1.02  
% 2.97/1.02  ------ Superposition Simplification Setup
% 2.97/1.02  
% 2.97/1.02  --sup_indices_passive                   []
% 2.97/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.97/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/1.02  --sup_full_bw                           [BwDemod]
% 2.97/1.02  --sup_immed_triv                        [TrivRules]
% 2.97/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.97/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/1.02  --sup_immed_bw_main                     []
% 2.97/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.97/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.97/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.97/1.02  
% 2.97/1.02  ------ Combination Options
% 2.97/1.02  
% 2.97/1.02  --comb_res_mult                         3
% 2.97/1.02  --comb_sup_mult                         2
% 2.97/1.02  --comb_inst_mult                        10
% 2.97/1.02  
% 2.97/1.02  ------ Debug Options
% 2.97/1.02  
% 2.97/1.02  --dbg_backtrace                         false
% 2.97/1.02  --dbg_dump_prop_clauses                 false
% 2.97/1.02  --dbg_dump_prop_clauses_file            -
% 2.97/1.02  --dbg_out_stat                          false
% 2.97/1.02  ------ Parsing...
% 2.97/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.97/1.02  
% 2.97/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 2.97/1.02  
% 2.97/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.97/1.02  
% 2.97/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.97/1.02  ------ Proving...
% 2.97/1.02  ------ Problem Properties 
% 2.97/1.02  
% 2.97/1.02  
% 2.97/1.02  clauses                                 18
% 2.97/1.02  conjectures                             2
% 2.97/1.02  EPR                                     2
% 2.97/1.02  Horn                                    18
% 2.97/1.02  unary                                   9
% 2.97/1.02  binary                                  6
% 2.97/1.02  lits                                    30
% 2.97/1.02  lits eq                                 12
% 2.97/1.02  fd_pure                                 0
% 2.97/1.02  fd_pseudo                               0
% 2.97/1.02  fd_cond                                 0
% 2.97/1.02  fd_pseudo_cond                          0
% 2.97/1.02  AC symbols                              0
% 2.97/1.02  
% 2.97/1.02  ------ Schedule dynamic 5 is on 
% 2.97/1.02  
% 2.97/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.97/1.02  
% 2.97/1.02  
% 2.97/1.02  ------ 
% 2.97/1.02  Current options:
% 2.97/1.02  ------ 
% 2.97/1.02  
% 2.97/1.02  ------ Input Options
% 2.97/1.02  
% 2.97/1.02  --out_options                           all
% 2.97/1.02  --tptp_safe_out                         true
% 2.97/1.02  --problem_path                          ""
% 2.97/1.02  --include_path                          ""
% 2.97/1.02  --clausifier                            res/vclausify_rel
% 2.97/1.02  --clausifier_options                    --mode clausify
% 2.97/1.02  --stdin                                 false
% 2.97/1.02  --stats_out                             all
% 2.97/1.02  
% 2.97/1.02  ------ General Options
% 2.97/1.02  
% 2.97/1.02  --fof                                   false
% 2.97/1.02  --time_out_real                         305.
% 2.97/1.02  --time_out_virtual                      -1.
% 2.97/1.02  --symbol_type_check                     false
% 2.97/1.02  --clausify_out                          false
% 2.97/1.02  --sig_cnt_out                           false
% 2.97/1.02  --trig_cnt_out                          false
% 2.97/1.02  --trig_cnt_out_tolerance                1.
% 2.97/1.02  --trig_cnt_out_sk_spl                   false
% 2.97/1.02  --abstr_cl_out                          false
% 2.97/1.02  
% 2.97/1.02  ------ Global Options
% 2.97/1.02  
% 2.97/1.02  --schedule                              default
% 2.97/1.02  --add_important_lit                     false
% 2.97/1.02  --prop_solver_per_cl                    1000
% 2.97/1.02  --min_unsat_core                        false
% 2.97/1.02  --soft_assumptions                      false
% 2.97/1.02  --soft_lemma_size                       3
% 2.97/1.02  --prop_impl_unit_size                   0
% 2.97/1.02  --prop_impl_unit                        []
% 2.97/1.02  --share_sel_clauses                     true
% 2.97/1.02  --reset_solvers                         false
% 2.97/1.02  --bc_imp_inh                            [conj_cone]
% 2.97/1.02  --conj_cone_tolerance                   3.
% 2.97/1.02  --extra_neg_conj                        none
% 2.97/1.02  --large_theory_mode                     true
% 2.97/1.02  --prolific_symb_bound                   200
% 2.97/1.02  --lt_threshold                          2000
% 2.97/1.02  --clause_weak_htbl                      true
% 2.97/1.02  --gc_record_bc_elim                     false
% 2.97/1.02  
% 2.97/1.02  ------ Preprocessing Options
% 2.97/1.02  
% 2.97/1.02  --preprocessing_flag                    true
% 2.97/1.02  --time_out_prep_mult                    0.1
% 2.97/1.02  --splitting_mode                        input
% 2.97/1.02  --splitting_grd                         true
% 2.97/1.02  --splitting_cvd                         false
% 2.97/1.02  --splitting_cvd_svl                     false
% 2.97/1.02  --splitting_nvd                         32
% 2.97/1.02  --sub_typing                            true
% 2.97/1.02  --prep_gs_sim                           true
% 2.97/1.02  --prep_unflatten                        true
% 2.97/1.02  --prep_res_sim                          true
% 2.97/1.02  --prep_upred                            true
% 2.97/1.02  --prep_sem_filter                       exhaustive
% 2.97/1.02  --prep_sem_filter_out                   false
% 2.97/1.02  --pred_elim                             true
% 2.97/1.02  --res_sim_input                         true
% 2.97/1.02  --eq_ax_congr_red                       true
% 2.97/1.02  --pure_diseq_elim                       true
% 2.97/1.02  --brand_transform                       false
% 2.97/1.02  --non_eq_to_eq                          false
% 2.97/1.02  --prep_def_merge                        true
% 2.97/1.02  --prep_def_merge_prop_impl              false
% 2.97/1.02  --prep_def_merge_mbd                    true
% 2.97/1.02  --prep_def_merge_tr_red                 false
% 2.97/1.02  --prep_def_merge_tr_cl                  false
% 2.97/1.02  --smt_preprocessing                     true
% 2.97/1.02  --smt_ac_axioms                         fast
% 2.97/1.02  --preprocessed_out                      false
% 2.97/1.02  --preprocessed_stats                    false
% 2.97/1.02  
% 2.97/1.02  ------ Abstraction refinement Options
% 2.97/1.02  
% 2.97/1.02  --abstr_ref                             []
% 2.97/1.02  --abstr_ref_prep                        false
% 2.97/1.02  --abstr_ref_until_sat                   false
% 2.97/1.02  --abstr_ref_sig_restrict                funpre
% 2.97/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.97/1.02  --abstr_ref_under                       []
% 2.97/1.02  
% 2.97/1.02  ------ SAT Options
% 2.97/1.02  
% 2.97/1.02  --sat_mode                              false
% 2.97/1.02  --sat_fm_restart_options                ""
% 2.97/1.02  --sat_gr_def                            false
% 2.97/1.02  --sat_epr_types                         true
% 2.97/1.02  --sat_non_cyclic_types                  false
% 2.97/1.02  --sat_finite_models                     false
% 2.97/1.02  --sat_fm_lemmas                         false
% 2.97/1.02  --sat_fm_prep                           false
% 2.97/1.02  --sat_fm_uc_incr                        true
% 2.97/1.02  --sat_out_model                         small
% 2.97/1.02  --sat_out_clauses                       false
% 2.97/1.02  
% 2.97/1.02  ------ QBF Options
% 2.97/1.02  
% 2.97/1.02  --qbf_mode                              false
% 2.97/1.02  --qbf_elim_univ                         false
% 2.97/1.02  --qbf_dom_inst                          none
% 2.97/1.02  --qbf_dom_pre_inst                      false
% 2.97/1.02  --qbf_sk_in                             false
% 2.97/1.02  --qbf_pred_elim                         true
% 2.97/1.02  --qbf_split                             512
% 2.97/1.02  
% 2.97/1.02  ------ BMC1 Options
% 2.97/1.02  
% 2.97/1.02  --bmc1_incremental                      false
% 2.97/1.02  --bmc1_axioms                           reachable_all
% 2.97/1.02  --bmc1_min_bound                        0
% 2.97/1.02  --bmc1_max_bound                        -1
% 2.97/1.02  --bmc1_max_bound_default                -1
% 2.97/1.02  --bmc1_symbol_reachability              true
% 2.97/1.02  --bmc1_property_lemmas                  false
% 2.97/1.02  --bmc1_k_induction                      false
% 2.97/1.02  --bmc1_non_equiv_states                 false
% 2.97/1.02  --bmc1_deadlock                         false
% 2.97/1.02  --bmc1_ucm                              false
% 2.97/1.02  --bmc1_add_unsat_core                   none
% 2.97/1.02  --bmc1_unsat_core_children              false
% 2.97/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.97/1.02  --bmc1_out_stat                         full
% 2.97/1.02  --bmc1_ground_init                      false
% 2.97/1.02  --bmc1_pre_inst_next_state              false
% 2.97/1.02  --bmc1_pre_inst_state                   false
% 2.97/1.02  --bmc1_pre_inst_reach_state             false
% 2.97/1.02  --bmc1_out_unsat_core                   false
% 2.97/1.02  --bmc1_aig_witness_out                  false
% 2.97/1.02  --bmc1_verbose                          false
% 2.97/1.02  --bmc1_dump_clauses_tptp                false
% 2.97/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.97/1.02  --bmc1_dump_file                        -
% 2.97/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.97/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.97/1.02  --bmc1_ucm_extend_mode                  1
% 2.97/1.02  --bmc1_ucm_init_mode                    2
% 2.97/1.02  --bmc1_ucm_cone_mode                    none
% 2.97/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.97/1.02  --bmc1_ucm_relax_model                  4
% 2.97/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.97/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.97/1.02  --bmc1_ucm_layered_model                none
% 2.97/1.02  --bmc1_ucm_max_lemma_size               10
% 2.97/1.02  
% 2.97/1.02  ------ AIG Options
% 2.97/1.02  
% 2.97/1.02  --aig_mode                              false
% 2.97/1.02  
% 2.97/1.02  ------ Instantiation Options
% 2.97/1.02  
% 2.97/1.02  --instantiation_flag                    true
% 2.97/1.02  --inst_sos_flag                         false
% 2.97/1.02  --inst_sos_phase                        true
% 2.97/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.97/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.97/1.02  --inst_lit_sel_side                     none
% 2.97/1.02  --inst_solver_per_active                1400
% 2.97/1.02  --inst_solver_calls_frac                1.
% 2.97/1.02  --inst_passive_queue_type               priority_queues
% 2.97/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.97/1.02  --inst_passive_queues_freq              [25;2]
% 2.97/1.02  --inst_dismatching                      true
% 2.97/1.02  --inst_eager_unprocessed_to_passive     true
% 2.97/1.02  --inst_prop_sim_given                   true
% 2.97/1.02  --inst_prop_sim_new                     false
% 2.97/1.02  --inst_subs_new                         false
% 2.97/1.02  --inst_eq_res_simp                      false
% 2.97/1.02  --inst_subs_given                       false
% 2.97/1.02  --inst_orphan_elimination               true
% 2.97/1.02  --inst_learning_loop_flag               true
% 2.97/1.02  --inst_learning_start                   3000
% 2.97/1.02  --inst_learning_factor                  2
% 2.97/1.02  --inst_start_prop_sim_after_learn       3
% 2.97/1.02  --inst_sel_renew                        solver
% 2.97/1.02  --inst_lit_activity_flag                true
% 2.97/1.02  --inst_restr_to_given                   false
% 2.97/1.02  --inst_activity_threshold               500
% 2.97/1.02  --inst_out_proof                        true
% 2.97/1.02  
% 2.97/1.02  ------ Resolution Options
% 2.97/1.02  
% 2.97/1.02  --resolution_flag                       false
% 2.97/1.02  --res_lit_sel                           adaptive
% 2.97/1.02  --res_lit_sel_side                      none
% 2.97/1.02  --res_ordering                          kbo
% 2.97/1.02  --res_to_prop_solver                    active
% 2.97/1.02  --res_prop_simpl_new                    false
% 2.97/1.02  --res_prop_simpl_given                  true
% 2.97/1.02  --res_passive_queue_type                priority_queues
% 2.97/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.97/1.02  --res_passive_queues_freq               [15;5]
% 2.97/1.02  --res_forward_subs                      full
% 2.97/1.02  --res_backward_subs                     full
% 2.97/1.02  --res_forward_subs_resolution           true
% 2.97/1.02  --res_backward_subs_resolution          true
% 2.97/1.02  --res_orphan_elimination                true
% 2.97/1.02  --res_time_limit                        2.
% 2.97/1.02  --res_out_proof                         true
% 2.97/1.02  
% 2.97/1.02  ------ Superposition Options
% 2.97/1.02  
% 2.97/1.02  --superposition_flag                    true
% 2.97/1.02  --sup_passive_queue_type                priority_queues
% 2.97/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.97/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.97/1.02  --demod_completeness_check              fast
% 2.97/1.02  --demod_use_ground                      true
% 2.97/1.02  --sup_to_prop_solver                    passive
% 2.97/1.02  --sup_prop_simpl_new                    true
% 2.97/1.02  --sup_prop_simpl_given                  true
% 2.97/1.02  --sup_fun_splitting                     false
% 2.97/1.02  --sup_smt_interval                      50000
% 2.97/1.02  
% 2.97/1.02  ------ Superposition Simplification Setup
% 2.97/1.02  
% 2.97/1.02  --sup_indices_passive                   []
% 2.97/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.97/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/1.02  --sup_full_bw                           [BwDemod]
% 2.97/1.02  --sup_immed_triv                        [TrivRules]
% 2.97/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.97/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/1.02  --sup_immed_bw_main                     []
% 2.97/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.97/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.97/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.97/1.02  
% 2.97/1.02  ------ Combination Options
% 2.97/1.02  
% 2.97/1.02  --comb_res_mult                         3
% 2.97/1.02  --comb_sup_mult                         2
% 2.97/1.02  --comb_inst_mult                        10
% 2.97/1.02  
% 2.97/1.02  ------ Debug Options
% 2.97/1.02  
% 2.97/1.02  --dbg_backtrace                         false
% 2.97/1.02  --dbg_dump_prop_clauses                 false
% 2.97/1.02  --dbg_dump_prop_clauses_file            -
% 2.97/1.02  --dbg_out_stat                          false
% 2.97/1.02  
% 2.97/1.02  
% 2.97/1.02  
% 2.97/1.02  
% 2.97/1.02  ------ Proving...
% 2.97/1.02  
% 2.97/1.02  
% 2.97/1.02  % SZS status Theorem for theBenchmark.p
% 2.97/1.02  
% 2.97/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 2.97/1.02  
% 2.97/1.02  fof(f19,conjecture,(
% 2.97/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_tops_1(X1,X0) & v3_pre_topc(X1,X0)) => k1_xboole_0 = X1)))),
% 2.97/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/1.02  
% 2.97/1.02  fof(f20,negated_conjecture,(
% 2.97/1.02    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_tops_1(X1,X0) & v3_pre_topc(X1,X0)) => k1_xboole_0 = X1)))),
% 2.97/1.02    inference(negated_conjecture,[],[f19])).
% 2.97/1.02  
% 2.97/1.02  fof(f42,plain,(
% 2.97/1.02    ? [X0] : (? [X1] : ((k1_xboole_0 != X1 & (v3_tops_1(X1,X0) & v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.97/1.02    inference(ennf_transformation,[],[f20])).
% 2.97/1.02  
% 2.97/1.02  fof(f43,plain,(
% 2.97/1.02    ? [X0] : (? [X1] : (k1_xboole_0 != X1 & v3_tops_1(X1,X0) & v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.97/1.02    inference(flattening,[],[f42])).
% 2.97/1.02  
% 2.97/1.02  fof(f48,plain,(
% 2.97/1.02    ( ! [X0] : (? [X1] : (k1_xboole_0 != X1 & v3_tops_1(X1,X0) & v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (k1_xboole_0 != sK1 & v3_tops_1(sK1,X0) & v3_pre_topc(sK1,X0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.97/1.02    introduced(choice_axiom,[])).
% 2.97/1.02  
% 2.97/1.02  fof(f47,plain,(
% 2.97/1.02    ? [X0] : (? [X1] : (k1_xboole_0 != X1 & v3_tops_1(X1,X0) & v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (k1_xboole_0 != X1 & v3_tops_1(X1,sK0) & v3_pre_topc(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 2.97/1.02    introduced(choice_axiom,[])).
% 2.97/1.02  
% 2.97/1.02  fof(f49,plain,(
% 2.97/1.02    (k1_xboole_0 != sK1 & v3_tops_1(sK1,sK0) & v3_pre_topc(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 2.97/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f43,f48,f47])).
% 2.97/1.02  
% 2.97/1.02  fof(f72,plain,(
% 2.97/1.02    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.97/1.02    inference(cnf_transformation,[],[f49])).
% 2.97/1.02  
% 2.97/1.02  fof(f11,axiom,(
% 2.97/1.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)))),
% 2.97/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/1.02  
% 2.97/1.02  fof(f29,plain,(
% 2.97/1.02    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.97/1.02    inference(ennf_transformation,[],[f11])).
% 2.97/1.02  
% 2.97/1.02  fof(f60,plain,(
% 2.97/1.02    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.97/1.02    inference(cnf_transformation,[],[f29])).
% 2.97/1.02  
% 2.97/1.02  fof(f71,plain,(
% 2.97/1.02    l1_pre_topc(sK0)),
% 2.97/1.02    inference(cnf_transformation,[],[f49])).
% 2.97/1.02  
% 2.97/1.02  fof(f17,axiom,(
% 2.97/1.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 2.97/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/1.02  
% 2.97/1.02  fof(f39,plain,(
% 2.97/1.02    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.97/1.02    inference(ennf_transformation,[],[f17])).
% 2.97/1.02  
% 2.97/1.02  fof(f46,plain,(
% 2.97/1.02    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1)) & (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.97/1.02    inference(nnf_transformation,[],[f39])).
% 2.97/1.02  
% 2.97/1.02  fof(f67,plain,(
% 2.97/1.02    ( ! [X0,X1] : (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.97/1.02    inference(cnf_transformation,[],[f46])).
% 2.97/1.02  
% 2.97/1.02  fof(f18,axiom,(
% 2.97/1.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tops_1(X1,X0) => v2_tops_1(X1,X0))))),
% 2.97/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/1.02  
% 2.97/1.02  fof(f40,plain,(
% 2.97/1.02    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) | ~v3_tops_1(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.97/1.02    inference(ennf_transformation,[],[f18])).
% 2.97/1.02  
% 2.97/1.02  fof(f41,plain,(
% 2.97/1.02    ! [X0] : (! [X1] : (v2_tops_1(X1,X0) | ~v3_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.97/1.02    inference(flattening,[],[f40])).
% 2.97/1.02  
% 2.97/1.02  fof(f69,plain,(
% 2.97/1.02    ( ! [X0,X1] : (v2_tops_1(X1,X0) | ~v3_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.97/1.02    inference(cnf_transformation,[],[f41])).
% 2.97/1.02  
% 2.97/1.02  fof(f74,plain,(
% 2.97/1.02    v3_tops_1(sK1,sK0)),
% 2.97/1.02    inference(cnf_transformation,[],[f49])).
% 2.97/1.02  
% 2.97/1.02  fof(f14,axiom,(
% 2.97/1.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,X1))))))),
% 2.97/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/1.02  
% 2.97/1.02  fof(f34,plain,(
% 2.97/1.02    ! [X0] : (! [X1] : ((k2_pre_topc(X0,X1) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,X1))) | ~v3_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.97/1.02    inference(ennf_transformation,[],[f14])).
% 2.97/1.02  
% 2.97/1.02  fof(f35,plain,(
% 2.97/1.02    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,X1))) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.97/1.02    inference(flattening,[],[f34])).
% 2.97/1.02  
% 2.97/1.02  fof(f63,plain,(
% 2.97/1.02    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,X1))) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.97/1.02    inference(cnf_transformation,[],[f35])).
% 2.97/1.02  
% 2.97/1.02  fof(f73,plain,(
% 2.97/1.02    v3_pre_topc(sK1,sK0)),
% 2.97/1.02    inference(cnf_transformation,[],[f49])).
% 2.97/1.02  
% 2.97/1.02  fof(f9,axiom,(
% 2.97/1.02    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.97/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/1.02  
% 2.97/1.02  fof(f26,plain,(
% 2.97/1.02    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.97/1.02    inference(ennf_transformation,[],[f9])).
% 2.97/1.02  
% 2.97/1.02  fof(f27,plain,(
% 2.97/1.02    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.97/1.02    inference(flattening,[],[f26])).
% 2.97/1.02  
% 2.97/1.02  fof(f57,plain,(
% 2.97/1.02    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.97/1.02    inference(cnf_transformation,[],[f27])).
% 2.97/1.02  
% 2.97/1.02  fof(f5,axiom,(
% 2.97/1.02    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 2.97/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/1.02  
% 2.97/1.02  fof(f23,plain,(
% 2.97/1.02    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.97/1.02    inference(ennf_transformation,[],[f5])).
% 2.97/1.02  
% 2.97/1.02  fof(f54,plain,(
% 2.97/1.02    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.97/1.02    inference(cnf_transformation,[],[f23])).
% 2.97/1.02  
% 2.97/1.02  fof(f3,axiom,(
% 2.97/1.02    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.97/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/1.02  
% 2.97/1.02  fof(f52,plain,(
% 2.97/1.02    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.97/1.02    inference(cnf_transformation,[],[f3])).
% 2.97/1.02  
% 2.97/1.02  fof(f6,axiom,(
% 2.97/1.02    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.97/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/1.02  
% 2.97/1.02  fof(f55,plain,(
% 2.97/1.02    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.97/1.02    inference(cnf_transformation,[],[f6])).
% 2.97/1.02  
% 2.97/1.02  fof(f13,axiom,(
% 2.97/1.02    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)))),
% 2.97/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/1.02  
% 2.97/1.02  fof(f32,plain,(
% 2.97/1.02    ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.97/1.02    inference(ennf_transformation,[],[f13])).
% 2.97/1.02  
% 2.97/1.02  fof(f33,plain,(
% 2.97/1.02    ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.97/1.02    inference(flattening,[],[f32])).
% 2.97/1.02  
% 2.97/1.02  fof(f62,plain,(
% 2.97/1.02    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.97/1.02    inference(cnf_transformation,[],[f33])).
% 2.97/1.02  
% 2.97/1.02  fof(f10,axiom,(
% 2.97/1.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tops_1(X1,X0) <=> v2_tops_1(k2_pre_topc(X0,X1),X0))))),
% 2.97/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/1.02  
% 2.97/1.02  fof(f28,plain,(
% 2.97/1.02    ! [X0] : (! [X1] : ((v3_tops_1(X1,X0) <=> v2_tops_1(k2_pre_topc(X0,X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.97/1.02    inference(ennf_transformation,[],[f10])).
% 2.97/1.02  
% 2.97/1.02  fof(f44,plain,(
% 2.97/1.02    ! [X0] : (! [X1] : (((v3_tops_1(X1,X0) | ~v2_tops_1(k2_pre_topc(X0,X1),X0)) & (v2_tops_1(k2_pre_topc(X0,X1),X0) | ~v3_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.97/1.02    inference(nnf_transformation,[],[f28])).
% 2.97/1.02  
% 2.97/1.02  fof(f58,plain,(
% 2.97/1.02    ( ! [X0,X1] : (v2_tops_1(k2_pre_topc(X0,X1),X0) | ~v3_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.97/1.02    inference(cnf_transformation,[],[f44])).
% 2.97/1.02  
% 2.97/1.02  fof(f1,axiom,(
% 2.97/1.02    v1_xboole_0(k1_xboole_0)),
% 2.97/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/1.02  
% 2.97/1.02  fof(f50,plain,(
% 2.97/1.02    v1_xboole_0(k1_xboole_0)),
% 2.97/1.02    inference(cnf_transformation,[],[f1])).
% 2.97/1.02  
% 2.97/1.02  fof(f8,axiom,(
% 2.97/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_xboole_0(X1) => v4_pre_topc(X1,X0))))),
% 2.97/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/1.02  
% 2.97/1.02  fof(f24,plain,(
% 2.97/1.02    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) | ~v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.97/1.02    inference(ennf_transformation,[],[f8])).
% 2.97/1.02  
% 2.97/1.02  fof(f25,plain,(
% 2.97/1.02    ! [X0] : (! [X1] : (v4_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.97/1.02    inference(flattening,[],[f24])).
% 2.97/1.02  
% 2.97/1.02  fof(f56,plain,(
% 2.97/1.02    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.97/1.02    inference(cnf_transformation,[],[f25])).
% 2.97/1.02  
% 2.97/1.02  fof(f70,plain,(
% 2.97/1.02    v2_pre_topc(sK0)),
% 2.97/1.02    inference(cnf_transformation,[],[f49])).
% 2.97/1.02  
% 2.97/1.02  fof(f16,axiom,(
% 2.97/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 2.97/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/1.02  
% 2.97/1.02  fof(f37,plain,(
% 2.97/1.02    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.97/1.02    inference(ennf_transformation,[],[f16])).
% 2.97/1.02  
% 2.97/1.02  fof(f38,plain,(
% 2.97/1.02    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.97/1.02    inference(flattening,[],[f37])).
% 2.97/1.02  
% 2.97/1.02  fof(f45,plain,(
% 2.97/1.02    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.97/1.02    inference(nnf_transformation,[],[f38])).
% 2.97/1.02  
% 2.97/1.02  fof(f65,plain,(
% 2.97/1.02    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.97/1.02    inference(cnf_transformation,[],[f45])).
% 2.97/1.02  
% 2.97/1.02  fof(f2,axiom,(
% 2.97/1.02    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.97/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/1.02  
% 2.97/1.02  fof(f51,plain,(
% 2.97/1.02    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.97/1.02    inference(cnf_transformation,[],[f2])).
% 2.97/1.02  
% 2.97/1.02  fof(f4,axiom,(
% 2.97/1.02    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 2.97/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/1.02  
% 2.97/1.02  fof(f22,plain,(
% 2.97/1.02    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 2.97/1.02    inference(ennf_transformation,[],[f4])).
% 2.97/1.02  
% 2.97/1.02  fof(f53,plain,(
% 2.97/1.02    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 2.97/1.02    inference(cnf_transformation,[],[f22])).
% 2.97/1.02  
% 2.97/1.02  fof(f15,axiom,(
% 2.97/1.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)))),
% 2.97/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.97/1.02  
% 2.97/1.02  fof(f36,plain,(
% 2.97/1.02    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.97/1.02    inference(ennf_transformation,[],[f15])).
% 2.97/1.02  
% 2.97/1.02  fof(f64,plain,(
% 2.97/1.02    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.97/1.02    inference(cnf_transformation,[],[f36])).
% 2.97/1.02  
% 2.97/1.02  fof(f75,plain,(
% 2.97/1.02    k1_xboole_0 != sK1),
% 2.97/1.02    inference(cnf_transformation,[],[f49])).
% 2.97/1.02  
% 2.97/1.02  cnf(c_23,negated_conjecture,
% 2.97/1.02      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.97/1.02      inference(cnf_transformation,[],[f72]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_921,plain,
% 2.97/1.02      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.97/1.02      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_10,plain,
% 2.97/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.97/1.02      | ~ l1_pre_topc(X1)
% 2.97/1.02      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
% 2.97/1.02      inference(cnf_transformation,[],[f60]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_24,negated_conjecture,
% 2.97/1.02      ( l1_pre_topc(sK0) ),
% 2.97/1.02      inference(cnf_transformation,[],[f71]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_524,plain,
% 2.97/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.97/1.02      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0)
% 2.97/1.02      | sK0 != X1 ),
% 2.97/1.02      inference(resolution_lifted,[status(thm)],[c_10,c_24]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_525,plain,
% 2.97/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.97/1.02      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
% 2.97/1.02      inference(unflattening,[status(thm)],[c_524]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_912,plain,
% 2.97/1.02      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0)
% 2.97/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.97/1.02      inference(predicate_to_equality,[status(thm)],[c_525]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_1678,plain,
% 2.97/1.02      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 2.97/1.02      inference(superposition,[status(thm)],[c_921,c_912]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_18,plain,
% 2.97/1.02      ( ~ v2_tops_1(X0,X1)
% 2.97/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.97/1.02      | ~ l1_pre_topc(X1)
% 2.97/1.02      | k1_tops_1(X1,X0) = k1_xboole_0 ),
% 2.97/1.02      inference(cnf_transformation,[],[f67]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_470,plain,
% 2.97/1.02      ( ~ v2_tops_1(X0,X1)
% 2.97/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.97/1.02      | k1_tops_1(X1,X0) = k1_xboole_0
% 2.97/1.02      | sK0 != X1 ),
% 2.97/1.02      inference(resolution_lifted,[status(thm)],[c_18,c_24]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_471,plain,
% 2.97/1.02      ( ~ v2_tops_1(X0,sK0)
% 2.97/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.97/1.02      | k1_tops_1(sK0,X0) = k1_xboole_0 ),
% 2.97/1.02      inference(unflattening,[status(thm)],[c_470]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_916,plain,
% 2.97/1.02      ( k1_tops_1(sK0,X0) = k1_xboole_0
% 2.97/1.02      | v2_tops_1(X0,sK0) != iProver_top
% 2.97/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.97/1.02      inference(predicate_to_equality,[status(thm)],[c_471]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_1542,plain,
% 2.97/1.02      ( k1_tops_1(sK0,sK1) = k1_xboole_0
% 2.97/1.02      | v2_tops_1(sK1,sK0) != iProver_top ),
% 2.97/1.02      inference(superposition,[status(thm)],[c_921,c_916]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_19,plain,
% 2.97/1.02      ( v2_tops_1(X0,X1)
% 2.97/1.02      | ~ v3_tops_1(X0,X1)
% 2.97/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.97/1.02      | ~ l1_pre_topc(X1) ),
% 2.97/1.02      inference(cnf_transformation,[],[f69]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_21,negated_conjecture,
% 2.97/1.02      ( v3_tops_1(sK1,sK0) ),
% 2.97/1.02      inference(cnf_transformation,[],[f74]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_435,plain,
% 2.97/1.02      ( v2_tops_1(X0,X1)
% 2.97/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.97/1.02      | ~ l1_pre_topc(X1)
% 2.97/1.02      | sK0 != X1
% 2.97/1.02      | sK1 != X0 ),
% 2.97/1.02      inference(resolution_lifted,[status(thm)],[c_19,c_21]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_436,plain,
% 2.97/1.02      ( v2_tops_1(sK1,sK0)
% 2.97/1.02      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.97/1.02      | ~ l1_pre_topc(sK0) ),
% 2.97/1.02      inference(unflattening,[status(thm)],[c_435]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_1022,plain,
% 2.97/1.02      ( ~ v2_tops_1(sK1,sK0)
% 2.97/1.02      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.97/1.02      | k1_tops_1(sK0,sK1) = k1_xboole_0 ),
% 2.97/1.02      inference(instantiation,[status(thm)],[c_471]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_1664,plain,
% 2.97/1.02      ( k1_tops_1(sK0,sK1) = k1_xboole_0 ),
% 2.97/1.02      inference(global_propositional_subsumption,
% 2.97/1.02                [status(thm)],
% 2.97/1.02                [c_1542,c_24,c_23,c_436,c_1022]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_1685,plain,
% 2.97/1.02      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_xboole_0) = k2_tops_1(sK0,sK1) ),
% 2.97/1.02      inference(light_normalisation,[status(thm)],[c_1678,c_1664]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_13,plain,
% 2.97/1.02      ( ~ v3_pre_topc(X0,X1)
% 2.97/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.97/1.02      | ~ l1_pre_topc(X1)
% 2.97/1.02      | k2_pre_topc(X1,k1_tops_1(X1,k2_pre_topc(X1,X0))) = k2_pre_topc(X1,X0) ),
% 2.97/1.02      inference(cnf_transformation,[],[f63]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_22,negated_conjecture,
% 2.97/1.02      ( v3_pre_topc(sK1,sK0) ),
% 2.97/1.02      inference(cnf_transformation,[],[f73]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_281,plain,
% 2.97/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.97/1.02      | ~ l1_pre_topc(X1)
% 2.97/1.02      | k2_pre_topc(X1,k1_tops_1(X1,k2_pre_topc(X1,X0))) = k2_pre_topc(X1,X0)
% 2.97/1.02      | sK0 != X1
% 2.97/1.02      | sK1 != X0 ),
% 2.97/1.02      inference(resolution_lifted,[status(thm)],[c_13,c_22]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_282,plain,
% 2.97/1.02      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.97/1.02      | ~ l1_pre_topc(sK0)
% 2.97/1.02      | k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) = k2_pre_topc(sK0,sK1) ),
% 2.97/1.02      inference(unflattening,[status(thm)],[c_281]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_284,plain,
% 2.97/1.02      ( k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) = k2_pre_topc(sK0,sK1) ),
% 2.97/1.02      inference(global_propositional_subsumption,
% 2.97/1.02                [status(thm)],
% 2.97/1.02                [c_282,c_24,c_23]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_7,plain,
% 2.97/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.97/1.02      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.97/1.02      | ~ l1_pre_topc(X1) ),
% 2.97/1.02      inference(cnf_transformation,[],[f57]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_536,plain,
% 2.97/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.97/1.02      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.97/1.02      | sK0 != X1 ),
% 2.97/1.02      inference(resolution_lifted,[status(thm)],[c_7,c_24]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_537,plain,
% 2.97/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.97/1.02      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.97/1.02      inference(unflattening,[status(thm)],[c_536]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_911,plain,
% 2.97/1.02      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.97/1.02      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.97/1.02      inference(predicate_to_equality,[status(thm)],[c_537]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_1085,plain,
% 2.97/1.02      ( m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.97/1.02      | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.97/1.02      inference(superposition,[status(thm)],[c_284,c_911]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_28,plain,
% 2.97/1.02      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.97/1.02      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_1012,plain,
% 2.97/1.02      ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 2.97/1.02      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.97/1.02      inference(instantiation,[status(thm)],[c_537]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_1013,plain,
% 2.97/1.02      ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 2.97/1.02      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.97/1.02      inference(predicate_to_equality,[status(thm)],[c_1012]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_1855,plain,
% 2.97/1.02      ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.97/1.02      inference(global_propositional_subsumption,
% 2.97/1.02                [status(thm)],
% 2.97/1.02                [c_1085,c_28,c_1013]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_4,plain,
% 2.97/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.97/1.02      | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 2.97/1.02      inference(cnf_transformation,[],[f54]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_923,plain,
% 2.97/1.02      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
% 2.97/1.02      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 2.97/1.02      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_1860,plain,
% 2.97/1.02      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X0) = k4_xboole_0(k2_pre_topc(sK0,sK1),X0) ),
% 2.97/1.02      inference(superposition,[status(thm)],[c_1855,c_923]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_2213,plain,
% 2.97/1.02      ( k4_xboole_0(k2_pre_topc(sK0,sK1),k1_xboole_0) = k2_tops_1(sK0,sK1) ),
% 2.97/1.02      inference(superposition,[status(thm)],[c_1685,c_1860]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_2,plain,
% 2.97/1.02      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 2.97/1.02      inference(cnf_transformation,[],[f52]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_2215,plain,
% 2.97/1.02      ( k2_tops_1(sK0,sK1) = k2_pre_topc(sK0,sK1) ),
% 2.97/1.02      inference(demodulation,[status(thm)],[c_2213,c_2]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_2538,plain,
% 2.97/1.02      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_xboole_0) = k2_pre_topc(sK0,sK1) ),
% 2.97/1.02      inference(demodulation,[status(thm)],[c_2215,c_1685]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_5,plain,
% 2.97/1.02      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 2.97/1.02      inference(cnf_transformation,[],[f55]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_922,plain,
% 2.97/1.02      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.97/1.02      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_1677,plain,
% 2.97/1.02      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_xboole_0),k1_tops_1(sK0,k1_xboole_0)) = k2_tops_1(sK0,k1_xboole_0) ),
% 2.97/1.02      inference(superposition,[status(thm)],[c_922,c_912]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_12,plain,
% 2.97/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.97/1.02      | ~ l1_pre_topc(X1)
% 2.97/1.02      | k1_tops_1(X1,k1_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
% 2.97/1.02      inference(cnf_transformation,[],[f62]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_512,plain,
% 2.97/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.97/1.02      | k1_tops_1(X1,k1_tops_1(X1,X0)) = k1_tops_1(X1,X0)
% 2.97/1.02      | sK0 != X1 ),
% 2.97/1.02      inference(resolution_lifted,[status(thm)],[c_12,c_24]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_513,plain,
% 2.97/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.97/1.02      | k1_tops_1(sK0,k1_tops_1(sK0,X0)) = k1_tops_1(sK0,X0) ),
% 2.97/1.02      inference(unflattening,[status(thm)],[c_512]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_913,plain,
% 2.97/1.02      ( k1_tops_1(sK0,k1_tops_1(sK0,X0)) = k1_tops_1(sK0,X0)
% 2.97/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.97/1.02      inference(predicate_to_equality,[status(thm)],[c_513]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_1135,plain,
% 2.97/1.02      ( k1_tops_1(sK0,k1_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
% 2.97/1.02      inference(superposition,[status(thm)],[c_921,c_913]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_1668,plain,
% 2.97/1.02      ( k1_tops_1(sK0,k1_xboole_0) = k1_xboole_0 ),
% 2.97/1.02      inference(demodulation,[status(thm)],[c_1664,c_1135]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_2153,plain,
% 2.97/1.02      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_xboole_0),k1_xboole_0) = k2_tops_1(sK0,k1_xboole_0) ),
% 2.97/1.02      inference(light_normalisation,[status(thm)],[c_1677,c_1668]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_1862,plain,
% 2.97/1.02      ( k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_xboole_0
% 2.97/1.02      | v2_tops_1(k2_pre_topc(sK0,sK1),sK0) != iProver_top ),
% 2.97/1.02      inference(superposition,[status(thm)],[c_1855,c_916]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_9,plain,
% 2.97/1.02      ( v2_tops_1(k2_pre_topc(X0,X1),X0)
% 2.97/1.02      | ~ v3_tops_1(X1,X0)
% 2.97/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.97/1.02      | ~ l1_pre_topc(X0) ),
% 2.97/1.02      inference(cnf_transformation,[],[f58]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_424,plain,
% 2.97/1.02      ( v2_tops_1(k2_pre_topc(X0,X1),X0)
% 2.97/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.97/1.02      | ~ l1_pre_topc(X0)
% 2.97/1.02      | sK0 != X0
% 2.97/1.02      | sK1 != X1 ),
% 2.97/1.02      inference(resolution_lifted,[status(thm)],[c_9,c_21]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_425,plain,
% 2.97/1.02      ( v2_tops_1(k2_pre_topc(sK0,sK1),sK0)
% 2.97/1.02      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.97/1.02      | ~ l1_pre_topc(sK0) ),
% 2.97/1.02      inference(unflattening,[status(thm)],[c_424]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_1019,plain,
% 2.97/1.02      ( ~ v2_tops_1(k2_pre_topc(sK0,sK1),sK0)
% 2.97/1.02      | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 2.97/1.02      | k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_xboole_0 ),
% 2.97/1.02      inference(instantiation,[status(thm)],[c_471]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_3078,plain,
% 2.97/1.02      ( k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_xboole_0 ),
% 2.97/1.02      inference(global_propositional_subsumption,
% 2.97/1.02                [status(thm)],
% 2.97/1.02                [c_1862,c_24,c_23,c_425,c_1012,c_1019]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_3082,plain,
% 2.97/1.02      ( k2_pre_topc(sK0,k1_xboole_0) = k2_pre_topc(sK0,sK1) ),
% 2.97/1.02      inference(demodulation,[status(thm)],[c_3078,c_284]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_3313,plain,
% 2.97/1.02      ( k2_tops_1(sK0,k1_xboole_0) = k2_pre_topc(sK0,k1_xboole_0) ),
% 2.97/1.02      inference(light_normalisation,[status(thm)],[c_2538,c_2153,c_3082]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_0,plain,
% 2.97/1.02      ( v1_xboole_0(k1_xboole_0) ),
% 2.97/1.02      inference(cnf_transformation,[],[f50]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_6,plain,
% 2.97/1.02      ( v4_pre_topc(X0,X1)
% 2.97/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.97/1.02      | ~ v2_pre_topc(X1)
% 2.97/1.02      | ~ l1_pre_topc(X1)
% 2.97/1.02      | ~ v1_xboole_0(X0) ),
% 2.97/1.02      inference(cnf_transformation,[],[f56]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_290,plain,
% 2.97/1.02      ( v4_pre_topc(X0,X1)
% 2.97/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.97/1.02      | ~ v2_pre_topc(X1)
% 2.97/1.02      | ~ l1_pre_topc(X1)
% 2.97/1.02      | k1_xboole_0 != X0 ),
% 2.97/1.02      inference(resolution_lifted,[status(thm)],[c_0,c_6]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_291,plain,
% 2.97/1.02      ( v4_pre_topc(k1_xboole_0,X0)
% 2.97/1.02      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
% 2.97/1.02      | ~ v2_pre_topc(X0)
% 2.97/1.02      | ~ l1_pre_topc(X0) ),
% 2.97/1.02      inference(unflattening,[status(thm)],[c_290]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_303,plain,
% 2.97/1.02      ( v4_pre_topc(k1_xboole_0,X0)
% 2.97/1.02      | ~ v2_pre_topc(X0)
% 2.97/1.02      | ~ l1_pre_topc(X0) ),
% 2.97/1.02      inference(forward_subsumption_resolution,[status(thm)],[c_291,c_5]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_25,negated_conjecture,
% 2.97/1.02      ( v2_pre_topc(sK0) ),
% 2.97/1.02      inference(cnf_transformation,[],[f70]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_314,plain,
% 2.97/1.02      ( v4_pre_topc(k1_xboole_0,X0) | ~ l1_pre_topc(X0) | sK0 != X0 ),
% 2.97/1.02      inference(resolution_lifted,[status(thm)],[c_303,c_25]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_315,plain,
% 2.97/1.02      ( v4_pre_topc(k1_xboole_0,sK0) | ~ l1_pre_topc(sK0) ),
% 2.97/1.02      inference(unflattening,[status(thm)],[c_314]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_317,plain,
% 2.97/1.02      ( v4_pre_topc(k1_xboole_0,sK0) ),
% 2.97/1.02      inference(global_propositional_subsumption,
% 2.97/1.02                [status(thm)],
% 2.97/1.02                [c_315,c_24]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_16,plain,
% 2.97/1.02      ( ~ v4_pre_topc(X0,X1)
% 2.97/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.97/1.02      | ~ v2_pre_topc(X1)
% 2.97/1.02      | ~ l1_pre_topc(X1)
% 2.97/1.02      | k7_subset_1(u1_struct_0(X1),X0,k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
% 2.97/1.02      inference(cnf_transformation,[],[f65]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_325,plain,
% 2.97/1.02      ( ~ v4_pre_topc(X0,X1)
% 2.97/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.97/1.02      | ~ l1_pre_topc(X1)
% 2.97/1.02      | k7_subset_1(u1_struct_0(X1),X0,k1_tops_1(X1,X0)) = k2_tops_1(X1,X0)
% 2.97/1.02      | sK0 != X1 ),
% 2.97/1.02      inference(resolution_lifted,[status(thm)],[c_16,c_25]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_326,plain,
% 2.97/1.02      ( ~ v4_pre_topc(X0,sK0)
% 2.97/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.97/1.02      | ~ l1_pre_topc(sK0)
% 2.97/1.02      | k7_subset_1(u1_struct_0(sK0),X0,k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
% 2.97/1.02      inference(unflattening,[status(thm)],[c_325]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_330,plain,
% 2.97/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.97/1.02      | ~ v4_pre_topc(X0,sK0)
% 2.97/1.02      | k7_subset_1(u1_struct_0(sK0),X0,k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
% 2.97/1.02      inference(global_propositional_subsumption,
% 2.97/1.02                [status(thm)],
% 2.97/1.02                [c_326,c_24]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_331,plain,
% 2.97/1.02      ( ~ v4_pre_topc(X0,sK0)
% 2.97/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.97/1.02      | k7_subset_1(u1_struct_0(sK0),X0,k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
% 2.97/1.02      inference(renaming,[status(thm)],[c_330]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_395,plain,
% 2.97/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.97/1.02      | k7_subset_1(u1_struct_0(sK0),X0,k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0)
% 2.97/1.02      | sK0 != sK0
% 2.97/1.02      | k1_xboole_0 != X0 ),
% 2.97/1.02      inference(resolution_lifted,[status(thm)],[c_317,c_331]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_396,plain,
% 2.97/1.02      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.97/1.02      | k7_subset_1(u1_struct_0(sK0),k1_xboole_0,k1_tops_1(sK0,k1_xboole_0)) = k2_tops_1(sK0,k1_xboole_0) ),
% 2.97/1.02      inference(unflattening,[status(thm)],[c_395]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_402,plain,
% 2.97/1.02      ( k7_subset_1(u1_struct_0(sK0),k1_xboole_0,k1_tops_1(sK0,k1_xboole_0)) = k2_tops_1(sK0,k1_xboole_0) ),
% 2.97/1.02      inference(forward_subsumption_resolution,[status(thm)],[c_396,c_5]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_2067,plain,
% 2.97/1.02      ( k7_subset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0) = k2_tops_1(sK0,k1_xboole_0) ),
% 2.97/1.02      inference(demodulation,[status(thm)],[c_1668,c_402]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_3315,plain,
% 2.97/1.02      ( k7_subset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0) = k2_pre_topc(sK0,k1_xboole_0) ),
% 2.97/1.02      inference(demodulation,[status(thm)],[c_3313,c_2067]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_1277,plain,
% 2.97/1.02      ( k7_subset_1(X0,k1_xboole_0,X1) = k4_xboole_0(k1_xboole_0,X1) ),
% 2.97/1.02      inference(superposition,[status(thm)],[c_922,c_923]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_1,plain,
% 2.97/1.02      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 2.97/1.02      inference(cnf_transformation,[],[f51]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_3,plain,
% 2.97/1.02      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 2.97/1.02      inference(cnf_transformation,[],[f53]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_274,plain,
% 2.97/1.02      ( k4_xboole_0(X0,X1) != X2 | k1_xboole_0 != X0 | k1_xboole_0 = X2 ),
% 2.97/1.02      inference(resolution_lifted,[status(thm)],[c_1,c_3]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_275,plain,
% 2.97/1.02      ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
% 2.97/1.02      inference(unflattening,[status(thm)],[c_274]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_1287,plain,
% 2.97/1.02      ( k7_subset_1(X0,k1_xboole_0,X1) = k1_xboole_0 ),
% 2.97/1.02      inference(demodulation,[status(thm)],[c_1277,c_275]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_3845,plain,
% 2.97/1.02      ( k2_pre_topc(sK0,k1_xboole_0) = k1_xboole_0 ),
% 2.97/1.02      inference(demodulation,[status(thm)],[c_3315,c_1287]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_1278,plain,
% 2.97/1.02      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
% 2.97/1.02      inference(superposition,[status(thm)],[c_921,c_923]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_14,plain,
% 2.97/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.97/1.02      | ~ l1_pre_topc(X1)
% 2.97/1.02      | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
% 2.97/1.02      inference(cnf_transformation,[],[f64]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_500,plain,
% 2.97/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.97/1.02      | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0)
% 2.97/1.02      | sK0 != X1 ),
% 2.97/1.02      inference(resolution_lifted,[status(thm)],[c_14,c_24]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_501,plain,
% 2.97/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.97/1.02      | k7_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k1_tops_1(sK0,X0) ),
% 2.97/1.02      inference(unflattening,[status(thm)],[c_500]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_914,plain,
% 2.97/1.02      ( k7_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k1_tops_1(sK0,X0)
% 2.97/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.97/1.02      inference(predicate_to_equality,[status(thm)],[c_501]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_1445,plain,
% 2.97/1.02      ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
% 2.97/1.02      inference(superposition,[status(thm)],[c_921,c_914]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_1459,plain,
% 2.97/1.02      ( k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
% 2.97/1.02      inference(superposition,[status(thm)],[c_1278,c_1445]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_2128,plain,
% 2.97/1.02      ( k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k1_xboole_0 ),
% 2.97/1.02      inference(light_normalisation,[status(thm)],[c_1459,c_1664]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_2540,plain,
% 2.97/1.02      ( k4_xboole_0(sK1,k2_pre_topc(sK0,sK1)) = k1_xboole_0 ),
% 2.97/1.02      inference(demodulation,[status(thm)],[c_2215,c_2128]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_3091,plain,
% 2.97/1.02      ( k4_xboole_0(sK1,k2_pre_topc(sK0,k1_xboole_0)) = k1_xboole_0 ),
% 2.97/1.02      inference(demodulation,[status(thm)],[c_3082,c_2540]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_3853,plain,
% 2.97/1.02      ( k4_xboole_0(sK1,k1_xboole_0) = k1_xboole_0 ),
% 2.97/1.02      inference(demodulation,[status(thm)],[c_3845,c_3091]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_670,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_2077,plain,
% 2.97/1.02      ( k4_xboole_0(sK1,k1_xboole_0) != X0
% 2.97/1.02      | k1_xboole_0 != X0
% 2.97/1.02      | k1_xboole_0 = k4_xboole_0(sK1,k1_xboole_0) ),
% 2.97/1.02      inference(instantiation,[status(thm)],[c_670]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_2078,plain,
% 2.97/1.02      ( k4_xboole_0(sK1,k1_xboole_0) != k1_xboole_0
% 2.97/1.02      | k1_xboole_0 = k4_xboole_0(sK1,k1_xboole_0)
% 2.97/1.02      | k1_xboole_0 != k1_xboole_0 ),
% 2.97/1.02      inference(instantiation,[status(thm)],[c_2077]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_1062,plain,
% 2.97/1.02      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 2.97/1.02      inference(instantiation,[status(thm)],[c_670]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_1563,plain,
% 2.97/1.02      ( sK1 != k4_xboole_0(sK1,k1_xboole_0)
% 2.97/1.02      | k1_xboole_0 != k4_xboole_0(sK1,k1_xboole_0)
% 2.97/1.02      | k1_xboole_0 = sK1 ),
% 2.97/1.02      inference(instantiation,[status(thm)],[c_1062]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_1109,plain,
% 2.97/1.02      ( X0 != X1 | sK1 != X1 | sK1 = X0 ),
% 2.97/1.02      inference(instantiation,[status(thm)],[c_670]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_1249,plain,
% 2.97/1.02      ( X0 != sK1 | sK1 = X0 | sK1 != sK1 ),
% 2.97/1.02      inference(instantiation,[status(thm)],[c_1109]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_1394,plain,
% 2.97/1.02      ( k4_xboole_0(sK1,k1_xboole_0) != sK1
% 2.97/1.02      | sK1 = k4_xboole_0(sK1,k1_xboole_0)
% 2.97/1.02      | sK1 != sK1 ),
% 2.97/1.02      inference(instantiation,[status(thm)],[c_1249]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_669,plain,( X0 = X0 ),theory(equality) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_1117,plain,
% 2.97/1.02      ( sK1 = sK1 ),
% 2.97/1.02      inference(instantiation,[status(thm)],[c_669]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_1111,plain,
% 2.97/1.02      ( k4_xboole_0(sK1,k1_xboole_0) = sK1 ),
% 2.97/1.02      inference(instantiation,[status(thm)],[c_2]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_690,plain,
% 2.97/1.02      ( k1_xboole_0 = k1_xboole_0 ),
% 2.97/1.02      inference(instantiation,[status(thm)],[c_669]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(c_20,negated_conjecture,
% 2.97/1.02      ( k1_xboole_0 != sK1 ),
% 2.97/1.02      inference(cnf_transformation,[],[f75]) ).
% 2.97/1.02  
% 2.97/1.02  cnf(contradiction,plain,
% 2.97/1.02      ( $false ),
% 2.97/1.02      inference(minisat,
% 2.97/1.02                [status(thm)],
% 2.97/1.02                [c_3853,c_2078,c_1563,c_1394,c_1117,c_1111,c_690,c_20]) ).
% 2.97/1.02  
% 2.97/1.02  
% 2.97/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 2.97/1.02  
% 2.97/1.02  ------                               Statistics
% 2.97/1.02  
% 2.97/1.02  ------ General
% 2.97/1.02  
% 2.97/1.02  abstr_ref_over_cycles:                  0
% 2.97/1.02  abstr_ref_under_cycles:                 0
% 2.97/1.02  gc_basic_clause_elim:                   0
% 2.97/1.02  forced_gc_time:                         0
% 2.97/1.02  parsing_time:                           0.01
% 2.97/1.02  unif_index_cands_time:                  0.
% 2.97/1.02  unif_index_add_time:                    0.
% 2.97/1.02  orderings_time:                         0.
% 2.97/1.02  out_proof_time:                         0.024
% 2.97/1.02  total_time:                             0.194
% 2.97/1.02  num_of_symbols:                         50
% 2.97/1.02  num_of_terms:                           3005
% 2.97/1.02  
% 2.97/1.02  ------ Preprocessing
% 2.97/1.02  
% 2.97/1.02  num_of_splits:                          0
% 2.97/1.02  num_of_split_atoms:                     0
% 2.97/1.02  num_of_reused_defs:                     0
% 2.97/1.02  num_eq_ax_congr_red:                    8
% 2.97/1.02  num_of_sem_filtered_clauses:            1
% 2.97/1.02  num_of_subtypes:                        0
% 2.97/1.02  monotx_restored_types:                  0
% 2.97/1.02  sat_num_of_epr_types:                   0
% 2.97/1.02  sat_num_of_non_cyclic_types:            0
% 2.97/1.02  sat_guarded_non_collapsed_types:        0
% 2.97/1.02  num_pure_diseq_elim:                    0
% 2.97/1.02  simp_replaced_by:                       0
% 2.97/1.02  res_preprocessed:                       103
% 2.97/1.02  prep_upred:                             0
% 2.97/1.02  prep_unflattend:                        23
% 2.97/1.02  smt_new_axioms:                         0
% 2.97/1.02  pred_elim_cands:                        2
% 2.97/1.02  pred_elim:                              7
% 2.97/1.02  pred_elim_cl:                           8
% 2.97/1.02  pred_elim_cycles:                       9
% 2.97/1.02  merged_defs:                            0
% 2.97/1.02  merged_defs_ncl:                        0
% 2.97/1.02  bin_hyper_res:                          0
% 2.97/1.02  prep_cycles:                            4
% 2.97/1.02  pred_elim_time:                         0.007
% 2.97/1.02  splitting_time:                         0.
% 2.97/1.02  sem_filter_time:                        0.
% 2.97/1.02  monotx_time:                            0.
% 2.97/1.02  subtype_inf_time:                       0.
% 2.97/1.02  
% 2.97/1.02  ------ Problem properties
% 2.97/1.02  
% 2.97/1.02  clauses:                                18
% 2.97/1.02  conjectures:                            2
% 2.97/1.02  epr:                                    2
% 2.97/1.02  horn:                                   18
% 2.97/1.02  ground:                                 6
% 2.97/1.02  unary:                                  9
% 2.97/1.02  binary:                                 6
% 2.97/1.02  lits:                                   30
% 2.97/1.02  lits_eq:                                12
% 2.97/1.02  fd_pure:                                0
% 2.97/1.02  fd_pseudo:                              0
% 2.97/1.02  fd_cond:                                0
% 2.97/1.02  fd_pseudo_cond:                         0
% 2.97/1.02  ac_symbols:                             0
% 2.97/1.02  
% 2.97/1.02  ------ Propositional Solver
% 2.97/1.02  
% 2.97/1.02  prop_solver_calls:                      29
% 2.97/1.02  prop_fast_solver_calls:                 598
% 2.97/1.02  smt_solver_calls:                       0
% 2.97/1.02  smt_fast_solver_calls:                  0
% 2.97/1.02  prop_num_of_clauses:                    1486
% 2.97/1.02  prop_preprocess_simplified:             4684
% 2.97/1.02  prop_fo_subsumed:                       14
% 2.97/1.02  prop_solver_time:                       0.
% 2.97/1.02  smt_solver_time:                        0.
% 2.97/1.02  smt_fast_solver_time:                   0.
% 2.97/1.02  prop_fast_solver_time:                  0.
% 2.97/1.02  prop_unsat_core_time:                   0.
% 2.97/1.02  
% 2.97/1.02  ------ QBF
% 2.97/1.02  
% 2.97/1.02  qbf_q_res:                              0
% 2.97/1.02  qbf_num_tautologies:                    0
% 2.97/1.02  qbf_prep_cycles:                        0
% 2.97/1.02  
% 2.97/1.02  ------ BMC1
% 2.97/1.02  
% 2.97/1.02  bmc1_current_bound:                     -1
% 2.97/1.02  bmc1_last_solved_bound:                 -1
% 2.97/1.02  bmc1_unsat_core_size:                   -1
% 2.97/1.02  bmc1_unsat_core_parents_size:           -1
% 2.97/1.02  bmc1_merge_next_fun:                    0
% 2.97/1.02  bmc1_unsat_core_clauses_time:           0.
% 2.97/1.02  
% 2.97/1.02  ------ Instantiation
% 2.97/1.02  
% 2.97/1.02  inst_num_of_clauses:                    527
% 2.97/1.02  inst_num_in_passive:                    242
% 2.97/1.02  inst_num_in_active:                     261
% 2.97/1.02  inst_num_in_unprocessed:                24
% 2.97/1.02  inst_num_of_loops:                      290
% 2.97/1.02  inst_num_of_learning_restarts:          0
% 2.97/1.02  inst_num_moves_active_passive:          25
% 2.97/1.02  inst_lit_activity:                      0
% 2.97/1.02  inst_lit_activity_moves:                0
% 2.97/1.02  inst_num_tautologies:                   0
% 2.97/1.02  inst_num_prop_implied:                  0
% 2.97/1.02  inst_num_existing_simplified:           0
% 2.97/1.02  inst_num_eq_res_simplified:             0
% 2.97/1.02  inst_num_child_elim:                    0
% 2.97/1.02  inst_num_of_dismatching_blockings:      232
% 2.97/1.02  inst_num_of_non_proper_insts:           450
% 2.97/1.02  inst_num_of_duplicates:                 0
% 2.97/1.02  inst_inst_num_from_inst_to_res:         0
% 2.97/1.02  inst_dismatching_checking_time:         0.
% 2.97/1.02  
% 2.97/1.02  ------ Resolution
% 2.97/1.02  
% 2.97/1.02  res_num_of_clauses:                     0
% 2.97/1.02  res_num_in_passive:                     0
% 2.97/1.02  res_num_in_active:                      0
% 2.97/1.02  res_num_of_loops:                       107
% 2.97/1.02  res_forward_subset_subsumed:            40
% 2.97/1.02  res_backward_subset_subsumed:           0
% 2.97/1.02  res_forward_subsumed:                   0
% 2.97/1.02  res_backward_subsumed:                  0
% 2.97/1.02  res_forward_subsumption_resolution:     2
% 2.97/1.02  res_backward_subsumption_resolution:    0
% 2.97/1.02  res_clause_to_clause_subsumption:       116
% 2.97/1.02  res_orphan_elimination:                 0
% 2.97/1.02  res_tautology_del:                      39
% 2.97/1.02  res_num_eq_res_simplified:              0
% 2.97/1.02  res_num_sel_changes:                    0
% 2.97/1.02  res_moves_from_active_to_pass:          0
% 2.97/1.02  
% 2.97/1.02  ------ Superposition
% 2.97/1.02  
% 2.97/1.02  sup_time_total:                         0.
% 2.97/1.02  sup_time_generating:                    0.
% 2.97/1.02  sup_time_sim_full:                      0.
% 2.97/1.02  sup_time_sim_immed:                     0.
% 2.97/1.02  
% 2.97/1.02  sup_num_of_clauses:                     48
% 2.97/1.02  sup_num_in_active:                      23
% 2.97/1.02  sup_num_in_passive:                     25
% 2.97/1.02  sup_num_of_loops:                       57
% 2.97/1.02  sup_fw_superposition:                   39
% 2.97/1.02  sup_bw_superposition:                   34
% 2.97/1.02  sup_immediate_simplified:               20
% 2.97/1.02  sup_given_eliminated:                   0
% 2.97/1.02  comparisons_done:                       0
% 2.97/1.02  comparisons_avoided:                    0
% 2.97/1.02  
% 2.97/1.02  ------ Simplifications
% 2.97/1.02  
% 2.97/1.02  
% 2.97/1.02  sim_fw_subset_subsumed:                 10
% 2.97/1.02  sim_bw_subset_subsumed:                 2
% 2.97/1.02  sim_fw_subsumed:                        3
% 2.97/1.02  sim_bw_subsumed:                        0
% 2.97/1.02  sim_fw_subsumption_res:                 0
% 2.97/1.02  sim_bw_subsumption_res:                 0
% 2.97/1.02  sim_tautology_del:                      0
% 2.97/1.02  sim_eq_tautology_del:                   3
% 2.97/1.02  sim_eq_res_simp:                        0
% 2.97/1.02  sim_fw_demodulated:                     3
% 2.97/1.02  sim_bw_demodulated:                     34
% 2.97/1.02  sim_light_normalised:                   13
% 2.97/1.02  sim_joinable_taut:                      0
% 2.97/1.02  sim_joinable_simp:                      0
% 2.97/1.02  sim_ac_normalised:                      0
% 2.97/1.02  sim_smt_subsumption:                    0
% 2.97/1.02  
%------------------------------------------------------------------------------
