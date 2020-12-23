%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:43 EST 2020

% Result     : Theorem 1.24s
% Output     : Refutation 1.24s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 616 expanded)
%              Number of leaves         :   14 ( 163 expanded)
%              Depth                    :   22
%              Number of atoms          :  277 (3467 expanded)
%              Number of equality atoms :   75 ( 945 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f120,plain,(
    $false ),
    inference(subsumption_resolution,[],[f119,f57])).

fof(f57,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f119,plain,(
    ~ r1_tarski(sK1,sK1) ),
    inference(forward_demodulation,[],[f116,f108])).

fof(f108,plain,(
    sK1 = k2_tops_1(sK0,sK1) ),
    inference(duplicate_literal_removal,[],[f105])).

fof(f105,plain,
    ( sK1 = k2_tops_1(sK0,sK1)
    | sK1 = k2_tops_1(sK0,sK1) ),
    inference(superposition,[],[f104,f79])).

fof(f79,plain,
    ( sK1 = k3_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | sK1 = k2_tops_1(sK0,sK1) ),
    inference(resolution,[],[f78,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f78,plain,
    ( r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | sK1 = k2_tops_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f77,f37])).

fof(f37,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ( sK1 != k2_tops_1(sK0,sK1)
      | ~ v3_tops_1(sK1,sK0) )
    & ( sK1 = k2_tops_1(sK0,sK1)
      | v3_tops_1(sK1,sK0) )
    & v4_pre_topc(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f29,f31,f30])).

fof(f30,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k2_tops_1(X0,X1) != X1
              | ~ v3_tops_1(X1,X0) )
            & ( k2_tops_1(X0,X1) = X1
              | v3_tops_1(X1,X0) )
            & v4_pre_topc(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k2_tops_1(sK0,X1) != X1
            | ~ v3_tops_1(X1,sK0) )
          & ( k2_tops_1(sK0,X1) = X1
            | v3_tops_1(X1,sK0) )
          & v4_pre_topc(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X1] :
        ( ( k2_tops_1(sK0,X1) != X1
          | ~ v3_tops_1(X1,sK0) )
        & ( k2_tops_1(sK0,X1) = X1
          | v3_tops_1(X1,sK0) )
        & v4_pre_topc(X1,sK0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( sK1 != k2_tops_1(sK0,sK1)
        | ~ v3_tops_1(sK1,sK0) )
      & ( sK1 = k2_tops_1(sK0,sK1)
        | v3_tops_1(sK1,sK0) )
      & v4_pre_topc(sK1,sK0)
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != X1
            | ~ v3_tops_1(X1,X0) )
          & ( k2_tops_1(X0,X1) = X1
            | v3_tops_1(X1,X0) )
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != X1
            | ~ v3_tops_1(X1,X0) )
          & ( k2_tops_1(X0,X1) = X1
            | v3_tops_1(X1,X0) )
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tops_1(X1,X0)
          <~> k2_tops_1(X0,X1) = X1 )
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tops_1(X1,X0)
          <~> k2_tops_1(X0,X1) = X1 )
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
             => ( v3_tops_1(X1,X0)
              <=> k2_tops_1(X0,X1) = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => ( v3_tops_1(X1,X0)
            <=> k2_tops_1(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_tops_1)).

fof(f77,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | sK1 = k2_tops_1(sK0,sK1) ),
    inference(resolution,[],[f58,f76])).

fof(f76,plain,
    ( v2_tops_1(sK1,sK0)
    | sK1 = k2_tops_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f75,f37])).

fof(f75,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_tops_1(sK1,sK0)
    | sK1 = k2_tops_1(sK0,sK1) ),
    inference(resolution,[],[f62,f39])).

fof(f39,plain,
    ( v3_tops_1(sK1,sK0)
    | sK1 = k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f62,plain,(
    ! [X4] :
      ( ~ v3_tops_1(X4,sK0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_tops_1(X4,sK0) ) ),
    inference(resolution,[],[f36,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v3_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tops_1(X1,X0)
          | ~ v3_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tops_1(X1,X0)
          | ~ v3_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tops_1(X1,X0)
           => v2_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_tops_1)).

fof(f36,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f58,plain,(
    ! [X0] :
      ( ~ v2_tops_1(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_tarski(X0,k2_tops_1(sK0,X0)) ) ),
    inference(resolution,[],[f36,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(X1,k2_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | ~ r1_tarski(X1,k2_tops_1(X0,X1)) )
            & ( r1_tarski(X1,k2_tops_1(X0,X1))
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> r1_tarski(X1,k2_tops_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> r1_tarski(X1,k2_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tops_1)).

fof(f104,plain,(
    k2_tops_1(sK0,sK1) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f103,f99])).

fof(f99,plain,(
    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    inference(superposition,[],[f94,f65])).

fof(f65,plain,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
    inference(resolution,[],[f37,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f94,plain,(
    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f93,f87])).

fof(f87,plain,(
    sK1 = k2_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f86,f37])).

fof(f86,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | sK1 = k2_pre_topc(sK0,sK1) ),
    inference(resolution,[],[f64,f38])).

fof(f38,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f64,plain,(
    ! [X6] :
      ( ~ v4_pre_topc(X6,sK0)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,X6) = X6 ) ),
    inference(resolution,[],[f36,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f27])).

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
    inference(flattening,[],[f26])).

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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f93,plain,(
    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f60,f37])).

fof(f60,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_tops_1(sK0,X2) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X2),k1_tops_1(sK0,X2)) ) ),
    inference(resolution,[],[f36,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

fof(f103,plain,(
    k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    inference(superposition,[],[f54,f102])).

fof(f102,plain,(
    k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f101,f71])).

fof(f71,plain,(
    k1_tops_1(sK0,sK1) = k3_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    inference(superposition,[],[f68,f55])).

fof(f55,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f68,plain,(
    k1_tops_1(sK0,sK1) = k3_xboole_0(k1_tops_1(sK0,sK1),sK1) ),
    inference(resolution,[],[f67,f49])).

fof(f67,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(resolution,[],[f63,f37])).

fof(f63,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_tarski(k1_tops_1(sK0,X5),X5) ) ),
    inference(resolution,[],[f36,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(f101,plain,(
    k3_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    inference(superposition,[],[f54,f99])).

fof(f54,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f116,plain,(
    ~ r1_tarski(sK1,k2_tops_1(sK0,sK1)) ),
    inference(trivial_inequality_removal,[],[f112])).

fof(f112,plain,
    ( sK1 != sK1
    | ~ r1_tarski(sK1,k2_tops_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f97,f108])).

fof(f97,plain,
    ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | sK1 != k2_tops_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f96,f37])).

fof(f96,plain,
    ( sK1 != k2_tops_1(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(sK1,k2_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f92,f59])).

fof(f59,plain,(
    ! [X1] :
      ( v2_tops_1(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X1,k2_tops_1(sK0,X1)) ) ),
    inference(resolution,[],[f36,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r1_tarski(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f92,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | sK1 != k2_tops_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f91,f38])).

fof(f91,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | ~ v4_pre_topc(sK1,sK0)
    | sK1 != k2_tops_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f88,f37])).

fof(f88,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_pre_topc(sK1,sK0)
    | sK1 != k2_tops_1(sK0,sK1) ),
    inference(resolution,[],[f61,f40])).

fof(f40,plain,
    ( ~ v3_tops_1(sK1,sK0)
    | sK1 != k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f61,plain,(
    ! [X3] :
      ( v3_tops_1(X3,sK0)
      | ~ v2_tops_1(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v4_pre_topc(X3,sK0) ) ),
    inference(resolution,[],[f36,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tops_1(X1,X0)
          | ~ v4_pre_topc(X1,X0)
          | ~ v2_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tops_1(X1,X0)
          | ~ v4_pre_topc(X1,X0)
          | ~ v2_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v4_pre_topc(X1,X0)
              & v2_tops_1(X1,X0) )
           => v3_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_tops_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:25:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (32454)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.51  % (32470)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.24/0.52  % (32454)Refutation not found, incomplete strategy% (32454)------------------------------
% 1.24/0.52  % (32454)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.52  % (32462)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.24/0.52  % (32454)Termination reason: Refutation not found, incomplete strategy
% 1.24/0.52  
% 1.24/0.52  % (32454)Memory used [KB]: 10746
% 1.24/0.52  % (32454)Time elapsed: 0.106 s
% 1.24/0.52  % (32454)------------------------------
% 1.24/0.52  % (32454)------------------------------
% 1.24/0.53  % (32447)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.24/0.53  % (32444)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.24/0.53  % (32462)Refutation found. Thanks to Tanya!
% 1.24/0.53  % SZS status Theorem for theBenchmark
% 1.24/0.53  % SZS output start Proof for theBenchmark
% 1.24/0.53  fof(f120,plain,(
% 1.24/0.53    $false),
% 1.24/0.53    inference(subsumption_resolution,[],[f119,f57])).
% 1.24/0.53  fof(f57,plain,(
% 1.24/0.53    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.24/0.53    inference(equality_resolution,[],[f46])).
% 1.24/0.53  fof(f46,plain,(
% 1.24/0.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.24/0.53    inference(cnf_transformation,[],[f35])).
% 1.24/0.53  fof(f35,plain,(
% 1.24/0.53    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.24/0.53    inference(flattening,[],[f34])).
% 1.24/0.53  fof(f34,plain,(
% 1.24/0.53    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.24/0.53    inference(nnf_transformation,[],[f2])).
% 1.24/0.53  fof(f2,axiom,(
% 1.24/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.24/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.24/0.53  fof(f119,plain,(
% 1.24/0.53    ~r1_tarski(sK1,sK1)),
% 1.24/0.53    inference(forward_demodulation,[],[f116,f108])).
% 1.24/0.53  fof(f108,plain,(
% 1.24/0.53    sK1 = k2_tops_1(sK0,sK1)),
% 1.24/0.53    inference(duplicate_literal_removal,[],[f105])).
% 1.24/0.53  fof(f105,plain,(
% 1.24/0.53    sK1 = k2_tops_1(sK0,sK1) | sK1 = k2_tops_1(sK0,sK1)),
% 1.24/0.53    inference(superposition,[],[f104,f79])).
% 1.24/0.53  fof(f79,plain,(
% 1.24/0.53    sK1 = k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) | sK1 = k2_tops_1(sK0,sK1)),
% 1.24/0.53    inference(resolution,[],[f78,f49])).
% 1.24/0.53  fof(f49,plain,(
% 1.24/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.24/0.53    inference(cnf_transformation,[],[f23])).
% 1.24/0.53  fof(f23,plain,(
% 1.24/0.53    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.24/0.53    inference(ennf_transformation,[],[f3])).
% 1.24/0.53  fof(f3,axiom,(
% 1.24/0.53    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.24/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.24/0.53  fof(f78,plain,(
% 1.24/0.53    r1_tarski(sK1,k2_tops_1(sK0,sK1)) | sK1 = k2_tops_1(sK0,sK1)),
% 1.24/0.53    inference(subsumption_resolution,[],[f77,f37])).
% 1.24/0.53  fof(f37,plain,(
% 1.24/0.53    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.24/0.53    inference(cnf_transformation,[],[f32])).
% 1.24/0.53  fof(f32,plain,(
% 1.24/0.53    ((sK1 != k2_tops_1(sK0,sK1) | ~v3_tops_1(sK1,sK0)) & (sK1 = k2_tops_1(sK0,sK1) | v3_tops_1(sK1,sK0)) & v4_pre_topc(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 1.24/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f29,f31,f30])).
% 1.24/0.53  fof(f30,plain,(
% 1.24/0.53    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != X1 | ~v3_tops_1(X1,X0)) & (k2_tops_1(X0,X1) = X1 | v3_tops_1(X1,X0)) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != X1 | ~v3_tops_1(X1,sK0)) & (k2_tops_1(sK0,X1) = X1 | v3_tops_1(X1,sK0)) & v4_pre_topc(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 1.24/0.53    introduced(choice_axiom,[])).
% 1.24/0.53  fof(f31,plain,(
% 1.24/0.53    ? [X1] : ((k2_tops_1(sK0,X1) != X1 | ~v3_tops_1(X1,sK0)) & (k2_tops_1(sK0,X1) = X1 | v3_tops_1(X1,sK0)) & v4_pre_topc(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((sK1 != k2_tops_1(sK0,sK1) | ~v3_tops_1(sK1,sK0)) & (sK1 = k2_tops_1(sK0,sK1) | v3_tops_1(sK1,sK0)) & v4_pre_topc(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.24/0.53    introduced(choice_axiom,[])).
% 1.24/0.53  fof(f29,plain,(
% 1.24/0.53    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != X1 | ~v3_tops_1(X1,X0)) & (k2_tops_1(X0,X1) = X1 | v3_tops_1(X1,X0)) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.24/0.53    inference(flattening,[],[f28])).
% 1.24/0.53  fof(f28,plain,(
% 1.24/0.53    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != X1 | ~v3_tops_1(X1,X0)) & (k2_tops_1(X0,X1) = X1 | v3_tops_1(X1,X0))) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.24/0.53    inference(nnf_transformation,[],[f16])).
% 1.24/0.53  fof(f16,plain,(
% 1.24/0.53    ? [X0] : (? [X1] : ((v3_tops_1(X1,X0) <~> k2_tops_1(X0,X1) = X1) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.24/0.53    inference(flattening,[],[f15])).
% 1.24/0.53  fof(f15,plain,(
% 1.24/0.53    ? [X0] : (? [X1] : (((v3_tops_1(X1,X0) <~> k2_tops_1(X0,X1) = X1) & v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.24/0.53    inference(ennf_transformation,[],[f14])).
% 1.24/0.53  fof(f14,negated_conjecture,(
% 1.24/0.53    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => (v3_tops_1(X1,X0) <=> k2_tops_1(X0,X1) = X1))))),
% 1.24/0.53    inference(negated_conjecture,[],[f13])).
% 1.24/0.53  fof(f13,conjecture,(
% 1.24/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => (v3_tops_1(X1,X0) <=> k2_tops_1(X0,X1) = X1))))),
% 1.24/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_tops_1)).
% 1.24/0.53  fof(f77,plain,(
% 1.24/0.53    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(sK1,k2_tops_1(sK0,sK1)) | sK1 = k2_tops_1(sK0,sK1)),
% 1.24/0.53    inference(resolution,[],[f58,f76])).
% 1.24/0.53  fof(f76,plain,(
% 1.24/0.53    v2_tops_1(sK1,sK0) | sK1 = k2_tops_1(sK0,sK1)),
% 1.24/0.53    inference(subsumption_resolution,[],[f75,f37])).
% 1.24/0.53  fof(f75,plain,(
% 1.24/0.53    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tops_1(sK1,sK0) | sK1 = k2_tops_1(sK0,sK1)),
% 1.24/0.53    inference(resolution,[],[f62,f39])).
% 1.24/0.53  fof(f39,plain,(
% 1.24/0.53    v3_tops_1(sK1,sK0) | sK1 = k2_tops_1(sK0,sK1)),
% 1.24/0.53    inference(cnf_transformation,[],[f32])).
% 1.24/0.53  fof(f62,plain,(
% 1.24/0.53    ( ! [X4] : (~v3_tops_1(X4,sK0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tops_1(X4,sK0)) )),
% 1.24/0.53    inference(resolution,[],[f36,f45])).
% 1.24/0.53  fof(f45,plain,(
% 1.24/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v3_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_tops_1(X1,X0)) )),
% 1.24/0.53    inference(cnf_transformation,[],[f22])).
% 1.24/0.53  fof(f22,plain,(
% 1.24/0.53    ! [X0] : (! [X1] : (v2_tops_1(X1,X0) | ~v3_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.24/0.53    inference(flattening,[],[f21])).
% 1.24/0.53  fof(f21,plain,(
% 1.24/0.53    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) | ~v3_tops_1(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.24/0.53    inference(ennf_transformation,[],[f11])).
% 1.24/0.53  fof(f11,axiom,(
% 1.24/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tops_1(X1,X0) => v2_tops_1(X1,X0))))),
% 1.24/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_tops_1)).
% 1.24/0.53  fof(f36,plain,(
% 1.24/0.53    l1_pre_topc(sK0)),
% 1.24/0.53    inference(cnf_transformation,[],[f32])).
% 1.24/0.53  fof(f58,plain,(
% 1.24/0.53    ( ! [X0] : (~v2_tops_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(X0,k2_tops_1(sK0,X0))) )),
% 1.24/0.53    inference(resolution,[],[f36,f41])).
% 1.24/0.53  fof(f41,plain,(
% 1.24/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(X1,k2_tops_1(X0,X1))) )),
% 1.24/0.53    inference(cnf_transformation,[],[f33])).
% 1.24/0.53  fof(f33,plain,(
% 1.24/0.53    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | ~r1_tarski(X1,k2_tops_1(X0,X1))) & (r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.24/0.53    inference(nnf_transformation,[],[f17])).
% 1.24/0.53  fof(f17,plain,(
% 1.24/0.53    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> r1_tarski(X1,k2_tops_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.24/0.53    inference(ennf_transformation,[],[f10])).
% 1.24/0.53  fof(f10,axiom,(
% 1.24/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> r1_tarski(X1,k2_tops_1(X0,X1)))))),
% 1.24/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tops_1)).
% 1.24/0.53  fof(f104,plain,(
% 1.24/0.53    k2_tops_1(sK0,sK1) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 1.24/0.53    inference(forward_demodulation,[],[f103,f99])).
% 1.24/0.53  fof(f99,plain,(
% 1.24/0.53    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))),
% 1.24/0.53    inference(superposition,[],[f94,f65])).
% 1.24/0.53  fof(f65,plain,(
% 1.24/0.53    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)) )),
% 1.24/0.53    inference(resolution,[],[f37,f51])).
% 1.24/0.53  fof(f51,plain,(
% 1.24/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)) )),
% 1.24/0.53    inference(cnf_transformation,[],[f25])).
% 1.24/0.53  fof(f25,plain,(
% 1.24/0.53    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.24/0.53    inference(ennf_transformation,[],[f5])).
% 1.24/0.53  fof(f5,axiom,(
% 1.24/0.53    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 1.24/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 1.24/0.53  fof(f94,plain,(
% 1.24/0.53    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),
% 1.24/0.53    inference(forward_demodulation,[],[f93,f87])).
% 1.24/0.53  fof(f87,plain,(
% 1.24/0.53    sK1 = k2_pre_topc(sK0,sK1)),
% 1.24/0.53    inference(subsumption_resolution,[],[f86,f37])).
% 1.24/0.53  fof(f86,plain,(
% 1.24/0.53    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = k2_pre_topc(sK0,sK1)),
% 1.24/0.53    inference(resolution,[],[f64,f38])).
% 1.24/0.53  fof(f38,plain,(
% 1.24/0.53    v4_pre_topc(sK1,sK0)),
% 1.24/0.53    inference(cnf_transformation,[],[f32])).
% 1.24/0.53  fof(f64,plain,(
% 1.24/0.53    ( ! [X6] : (~v4_pre_topc(X6,sK0) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X6) = X6) )),
% 1.24/0.53    inference(resolution,[],[f36,f52])).
% 1.24/0.53  fof(f52,plain,(
% 1.24/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = X1) )),
% 1.24/0.53    inference(cnf_transformation,[],[f27])).
% 1.24/0.53  fof(f27,plain,(
% 1.24/0.53    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.24/0.53    inference(flattening,[],[f26])).
% 1.24/0.53  fof(f26,plain,(
% 1.24/0.53    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.24/0.53    inference(ennf_transformation,[],[f6])).
% 1.24/0.53  fof(f6,axiom,(
% 1.24/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 1.24/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).
% 1.24/0.53  fof(f93,plain,(
% 1.24/0.53    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),
% 1.24/0.53    inference(resolution,[],[f60,f37])).
% 1.24/0.53  fof(f60,plain,(
% 1.24/0.53    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | k2_tops_1(sK0,X2) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X2),k1_tops_1(sK0,X2))) )),
% 1.24/0.53    inference(resolution,[],[f36,f43])).
% 1.24/0.53  fof(f43,plain,(
% 1.24/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))) )),
% 1.24/0.53    inference(cnf_transformation,[],[f18])).
% 1.24/0.53  fof(f18,plain,(
% 1.24/0.53    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.24/0.53    inference(ennf_transformation,[],[f7])).
% 1.24/0.53  fof(f7,axiom,(
% 1.24/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 1.24/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).
% 1.24/0.53  fof(f103,plain,(
% 1.24/0.53    k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))),
% 1.24/0.53    inference(superposition,[],[f54,f102])).
% 1.24/0.53  fof(f102,plain,(
% 1.24/0.53    k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 1.24/0.53    inference(forward_demodulation,[],[f101,f71])).
% 1.24/0.53  fof(f71,plain,(
% 1.24/0.53    k1_tops_1(sK0,sK1) = k3_xboole_0(sK1,k1_tops_1(sK0,sK1))),
% 1.24/0.53    inference(superposition,[],[f68,f55])).
% 1.24/0.53  fof(f55,plain,(
% 1.24/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.24/0.53    inference(cnf_transformation,[],[f1])).
% 1.24/0.53  fof(f1,axiom,(
% 1.24/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.24/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.24/0.53  fof(f68,plain,(
% 1.24/0.53    k1_tops_1(sK0,sK1) = k3_xboole_0(k1_tops_1(sK0,sK1),sK1)),
% 1.24/0.53    inference(resolution,[],[f67,f49])).
% 1.24/0.53  fof(f67,plain,(
% 1.24/0.53    r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 1.24/0.53    inference(resolution,[],[f63,f37])).
% 1.24/0.53  fof(f63,plain,(
% 1.24/0.53    ( ! [X5] : (~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k1_tops_1(sK0,X5),X5)) )),
% 1.24/0.53    inference(resolution,[],[f36,f50])).
% 1.24/0.53  fof(f50,plain,(
% 1.24/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,X1),X1)) )),
% 1.24/0.53    inference(cnf_transformation,[],[f24])).
% 1.24/0.53  fof(f24,plain,(
% 1.24/0.53    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.24/0.53    inference(ennf_transformation,[],[f8])).
% 1.24/0.53  fof(f8,axiom,(
% 1.24/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 1.24/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).
% 1.24/0.53  fof(f101,plain,(
% 1.24/0.53    k3_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 1.24/0.53    inference(superposition,[],[f54,f99])).
% 1.24/0.53  fof(f54,plain,(
% 1.24/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.24/0.53    inference(cnf_transformation,[],[f4])).
% 1.24/0.53  fof(f4,axiom,(
% 1.24/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.24/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.24/0.53  fof(f116,plain,(
% 1.24/0.53    ~r1_tarski(sK1,k2_tops_1(sK0,sK1))),
% 1.24/0.53    inference(trivial_inequality_removal,[],[f112])).
% 1.24/0.53  fof(f112,plain,(
% 1.24/0.53    sK1 != sK1 | ~r1_tarski(sK1,k2_tops_1(sK0,sK1))),
% 1.24/0.53    inference(backward_demodulation,[],[f97,f108])).
% 1.24/0.53  fof(f97,plain,(
% 1.24/0.53    ~r1_tarski(sK1,k2_tops_1(sK0,sK1)) | sK1 != k2_tops_1(sK0,sK1)),
% 1.24/0.53    inference(subsumption_resolution,[],[f96,f37])).
% 1.24/0.53  fof(f96,plain,(
% 1.24/0.53    sK1 != k2_tops_1(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK1,k2_tops_1(sK0,sK1))),
% 1.24/0.53    inference(resolution,[],[f92,f59])).
% 1.24/0.53  fof(f59,plain,(
% 1.24/0.53    ( ! [X1] : (v2_tops_1(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X1,k2_tops_1(sK0,X1))) )),
% 1.24/0.53    inference(resolution,[],[f36,f42])).
% 1.24/0.53  fof(f42,plain,(
% 1.24/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~r1_tarski(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_tops_1(X1,X0)) )),
% 1.24/0.53    inference(cnf_transformation,[],[f33])).
% 1.24/0.53  fof(f92,plain,(
% 1.24/0.53    ~v2_tops_1(sK1,sK0) | sK1 != k2_tops_1(sK0,sK1)),
% 1.24/0.53    inference(subsumption_resolution,[],[f91,f38])).
% 1.24/0.53  fof(f91,plain,(
% 1.24/0.53    ~v2_tops_1(sK1,sK0) | ~v4_pre_topc(sK1,sK0) | sK1 != k2_tops_1(sK0,sK1)),
% 1.24/0.53    inference(subsumption_resolution,[],[f88,f37])).
% 1.24/0.53  fof(f88,plain,(
% 1.24/0.53    ~v2_tops_1(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(sK1,sK0) | sK1 != k2_tops_1(sK0,sK1)),
% 1.24/0.53    inference(resolution,[],[f61,f40])).
% 1.24/0.53  fof(f40,plain,(
% 1.24/0.53    ~v3_tops_1(sK1,sK0) | sK1 != k2_tops_1(sK0,sK1)),
% 1.24/0.53    inference(cnf_transformation,[],[f32])).
% 1.24/0.53  fof(f61,plain,(
% 1.24/0.53    ( ! [X3] : (v3_tops_1(X3,sK0) | ~v2_tops_1(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X3,sK0)) )),
% 1.24/0.53    inference(resolution,[],[f36,f44])).
% 1.24/0.53  fof(f44,plain,(
% 1.24/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v4_pre_topc(X1,X0) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_tops_1(X1,X0)) )),
% 1.24/0.53    inference(cnf_transformation,[],[f20])).
% 1.24/0.53  fof(f20,plain,(
% 1.24/0.53    ! [X0] : (! [X1] : (v3_tops_1(X1,X0) | ~v4_pre_topc(X1,X0) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.24/0.53    inference(flattening,[],[f19])).
% 1.24/0.53  fof(f19,plain,(
% 1.24/0.53    ! [X0] : (! [X1] : ((v3_tops_1(X1,X0) | (~v4_pre_topc(X1,X0) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.24/0.53    inference(ennf_transformation,[],[f12])).
% 1.24/0.53  fof(f12,axiom,(
% 1.24/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X1,X0) & v2_tops_1(X1,X0)) => v3_tops_1(X1,X0))))),
% 1.24/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_tops_1)).
% 1.24/0.53  % SZS output end Proof for theBenchmark
% 1.24/0.53  % (32462)------------------------------
% 1.24/0.53  % (32462)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.53  % (32462)Termination reason: Refutation
% 1.24/0.53  
% 1.24/0.53  % (32462)Memory used [KB]: 1791
% 1.24/0.53  % (32462)Time elapsed: 0.118 s
% 1.24/0.53  % (32462)------------------------------
% 1.24/0.53  % (32462)------------------------------
% 1.24/0.53  % (32466)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.37/0.54  % (32443)Success in time 0.173 s
%------------------------------------------------------------------------------
