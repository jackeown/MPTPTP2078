%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:03 EST 2020

% Result     : Theorem 1.25s
% Output     : Refutation 1.25s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 558 expanded)
%              Number of leaves         :   12 ( 148 expanded)
%              Depth                    :   25
%              Number of atoms          :  278 (3104 expanded)
%              Number of equality atoms :   48 ( 155 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f192,plain,(
    $false ),
    inference(resolution,[],[f187,f145])).

fof(f145,plain,(
    ~ v6_tops_1(sK1,sK0) ),
    inference(resolution,[],[f142,f39])).

fof(f39,plain,
    ( ~ v5_tops_1(sK1,sK0)
    | ~ v6_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ( ~ v6_tops_1(sK1,sK0)
      | ~ v5_tops_1(sK1,sK0) )
    & ( v6_tops_1(sK1,sK0)
      | v5_tops_1(sK1,sK0) )
    & v4_pre_topc(sK1,sK0)
    & v3_pre_topc(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f28,f27])).

fof(f27,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v6_tops_1(X1,X0)
              | ~ v5_tops_1(X1,X0) )
            & ( v6_tops_1(X1,X0)
              | v5_tops_1(X1,X0) )
            & v4_pre_topc(X1,X0)
            & v3_pre_topc(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ~ v6_tops_1(X1,sK0)
            | ~ v5_tops_1(X1,sK0) )
          & ( v6_tops_1(X1,sK0)
            | v5_tops_1(X1,sK0) )
          & v4_pre_topc(X1,sK0)
          & v3_pre_topc(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X1] :
        ( ( ~ v6_tops_1(X1,sK0)
          | ~ v5_tops_1(X1,sK0) )
        & ( v6_tops_1(X1,sK0)
          | v5_tops_1(X1,sK0) )
        & v4_pre_topc(X1,sK0)
        & v3_pre_topc(X1,sK0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( ~ v6_tops_1(sK1,sK0)
        | ~ v5_tops_1(sK1,sK0) )
      & ( v6_tops_1(sK1,sK0)
        | v5_tops_1(sK1,sK0) )
      & v4_pre_topc(sK1,sK0)
      & v3_pre_topc(sK1,sK0)
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v6_tops_1(X1,X0)
            | ~ v5_tops_1(X1,X0) )
          & ( v6_tops_1(X1,X0)
            | v5_tops_1(X1,X0) )
          & v4_pre_topc(X1,X0)
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v6_tops_1(X1,X0)
            | ~ v5_tops_1(X1,X0) )
          & ( v6_tops_1(X1,X0)
            | v5_tops_1(X1,X0) )
          & v4_pre_topc(X1,X0)
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v5_tops_1(X1,X0)
          <~> v6_tops_1(X1,X0) )
          & v4_pre_topc(X1,X0)
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v5_tops_1(X1,X0)
          <~> v6_tops_1(X1,X0) )
          & v4_pre_topc(X1,X0)
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ( v4_pre_topc(X1,X0)
                & v3_pre_topc(X1,X0) )
             => ( v5_tops_1(X1,X0)
              <=> v6_tops_1(X1,X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v4_pre_topc(X1,X0)
              & v3_pre_topc(X1,X0) )
           => ( v5_tops_1(X1,X0)
            <=> v6_tops_1(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_tops_1)).

fof(f142,plain,(
    v5_tops_1(sK1,sK0) ),
    inference(resolution,[],[f140,f35])).

fof(f35,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f29])).

fof(f140,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v5_tops_1(sK1,sK0) ),
    inference(resolution,[],[f139,f34])).

fof(f34,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f139,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v5_tops_1(sK1,sK0) ),
    inference(trivial_inequality_removal,[],[f138])).

fof(f138,plain,
    ( sK1 != sK1
    | v5_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(forward_demodulation,[],[f137,f78])).

fof(f78,plain,(
    sK1 = k2_pre_topc(sK0,sK1) ),
    inference(resolution,[],[f77,f35])).

fof(f77,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | sK1 = k2_pre_topc(sK0,sK1) ),
    inference(resolution,[],[f76,f37])).

fof(f37,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f76,plain,(
    ! [X0] :
      ( ~ v4_pre_topc(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,X0) = X0 ) ),
    inference(resolution,[],[f41,f34])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

% (4619)Refutation not found, incomplete strategy% (4619)------------------------------
% (4619)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (4619)Termination reason: Refutation not found, incomplete strategy

% (4619)Memory used [KB]: 10618
% (4619)Time elapsed: 0.060 s
% (4619)------------------------------
% (4619)------------------------------
fof(f5,axiom,(
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

fof(f137,plain,
    ( sK1 != k2_pre_topc(sK0,sK1)
    | v5_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(superposition,[],[f47,f136])).

fof(f136,plain,(
    sK1 = k1_tops_1(sK0,sK1) ),
    inference(forward_demodulation,[],[f135,f63])).

fof(f63,plain,(
    sK1 = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) ),
    inference(forward_demodulation,[],[f61,f57])).

fof(f57,plain,(
    k4_xboole_0(u1_struct_0(sK0),sK1) = k3_subset_1(u1_struct_0(sK0),sK1) ),
    inference(resolution,[],[f51,f35])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f61,plain,(
    sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f52,f35])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f135,plain,(
    k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) = k1_tops_1(sK0,sK1) ),
    inference(forward_demodulation,[],[f134,f128])).

fof(f128,plain,(
    k4_xboole_0(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f127,f50])).

fof(f50,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f127,plain,
    ( ~ r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | k4_xboole_0(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f121,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f121,plain,
    ( ~ m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_xboole_0(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f119,f76])).

fof(f119,plain,(
    v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) ),
    inference(resolution,[],[f117,f36])).

fof(f36,plain,(
    v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f117,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) ),
    inference(superposition,[],[f114,f68])).

fof(f68,plain,(
    sK1 = k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) ),
    inference(superposition,[],[f59,f63])).

fof(f59,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_subset_1(X0,k4_xboole_0(X0,X1)) ),
    inference(resolution,[],[f58,f50])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(resolution,[],[f51,f54])).

fof(f114,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),X0)),sK0)
      | v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),X0),sK0) ) ),
    inference(forward_demodulation,[],[f112,f59])).

fof(f112,plain,(
    ! [X0] :
      ( v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),X0),sK0)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),X0)),sK0) ) ),
    inference(resolution,[],[f111,f50])).

fof(f111,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,u1_struct_0(sK0))
      | v4_pre_topc(X0,sK0)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0) ) ),
    inference(resolution,[],[f109,f54])).

fof(f109,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0)
      | v4_pre_topc(X0,sK0) ) ),
    inference(resolution,[],[f49,f34])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v4_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_1)).

fof(f134,plain,(
    k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))) ),
    inference(forward_demodulation,[],[f132,f57])).

fof(f132,plain,(
    k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ),
    inference(resolution,[],[f131,f35])).

fof(f131,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_tops_1(sK0,X0) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) ) ),
    inference(resolution,[],[f40,f34])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).

fof(f47,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1
      | v5_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_tops_1(X1,X0)
              | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1 )
            & ( k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1
              | ~ v5_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_tops_1(X1,X0)
          <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v5_tops_1(X1,X0)
          <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tops_1)).

fof(f187,plain,(
    v6_tops_1(sK1,sK0) ),
    inference(resolution,[],[f177,f92])).

fof(f92,plain,
    ( ~ v5_tops_1(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)
    | v6_tops_1(sK1,sK0) ),
    inference(forward_demodulation,[],[f90,f57])).

fof(f90,plain,
    ( ~ v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | v6_tops_1(sK1,sK0) ),
    inference(resolution,[],[f87,f35])).

fof(f87,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v5_tops_1(k3_subset_1(u1_struct_0(sK0),X0),sK0)
      | v6_tops_1(X0,sK0) ) ),
    inference(resolution,[],[f45,f34])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v6_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v6_tops_1(X1,X0)
              | ~ v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v6_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v6_tops_1(X1,X0)
          <=> v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v6_tops_1(X1,X0)
          <=> v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t101_tops_1)).

fof(f177,plain,(
    v5_tops_1(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) ),
    inference(resolution,[],[f176,f50])).

fof(f176,plain,
    ( ~ r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | v5_tops_1(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) ),
    inference(resolution,[],[f175,f54])).

fof(f175,plain,
    ( ~ m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v5_tops_1(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) ),
    inference(resolution,[],[f174,f34])).

fof(f174,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v5_tops_1(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) ),
    inference(trivial_inequality_removal,[],[f173])).

fof(f173,plain,
    ( k4_xboole_0(u1_struct_0(sK0),sK1) != k4_xboole_0(u1_struct_0(sK0),sK1)
    | v5_tops_1(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(forward_demodulation,[],[f172,f128])).

fof(f172,plain,
    ( k4_xboole_0(u1_struct_0(sK0),sK1) != k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))
    | v5_tops_1(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(superposition,[],[f47,f169])).

fof(f169,plain,(
    k4_xboole_0(u1_struct_0(sK0),sK1) = k1_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) ),
    inference(forward_demodulation,[],[f168,f57])).

fof(f168,plain,(
    k3_subset_1(u1_struct_0(sK0),sK1) = k1_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) ),
    inference(forward_demodulation,[],[f164,f78])).

fof(f164,plain,(
    k1_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) ),
    inference(superposition,[],[f153,f68])).

fof(f153,plain,(
    ! [X0] : k1_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),X0)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),X0)))) ),
    inference(forward_demodulation,[],[f151,f59])).

fof(f151,plain,(
    ! [X0] : k1_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),X0)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),X0)))) ),
    inference(resolution,[],[f133,f50])).

fof(f133,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,u1_struct_0(sK0))
      | k1_tops_1(sK0,X0) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) ) ),
    inference(resolution,[],[f131,f54])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:47:35 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (4602)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.22/0.50  % (4597)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.22/0.51  % (4599)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.22/0.51  % (4596)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.22/0.51  % (4618)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.22/0.51  % (4598)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.22/0.51  % (4612)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.22/0.51  % (4619)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.22/0.51  % (4602)Refutation not found, incomplete strategy% (4602)------------------------------
% 0.22/0.51  % (4602)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (4614)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.22/0.51  % (4611)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.22/0.52  % (4605)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.22/0.52  % (4599)Refutation not found, incomplete strategy% (4599)------------------------------
% 0.22/0.52  % (4599)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (4599)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (4599)Memory used [KB]: 10618
% 0.22/0.52  % (4599)Time elapsed: 0.100 s
% 0.22/0.52  % (4599)------------------------------
% 0.22/0.52  % (4599)------------------------------
% 0.22/0.52  % (4600)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.22/0.52  % (4609)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.22/0.52  % (4602)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (4602)Memory used [KB]: 10746
% 0.22/0.52  % (4602)Time elapsed: 0.096 s
% 0.22/0.52  % (4602)------------------------------
% 0.22/0.52  % (4602)------------------------------
% 1.25/0.52  % (4601)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 1.25/0.52  % (4612)Refutation not found, incomplete strategy% (4612)------------------------------
% 1.25/0.52  % (4612)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.52  % (4612)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.52  
% 1.25/0.52  % (4612)Memory used [KB]: 1663
% 1.25/0.52  % (4612)Time elapsed: 0.106 s
% 1.25/0.52  % (4612)------------------------------
% 1.25/0.52  % (4612)------------------------------
% 1.25/0.52  % (4605)Refutation found. Thanks to Tanya!
% 1.25/0.52  % SZS status Theorem for theBenchmark
% 1.25/0.52  % SZS output start Proof for theBenchmark
% 1.25/0.52  fof(f192,plain,(
% 1.25/0.52    $false),
% 1.25/0.52    inference(resolution,[],[f187,f145])).
% 1.25/0.52  fof(f145,plain,(
% 1.25/0.52    ~v6_tops_1(sK1,sK0)),
% 1.25/0.52    inference(resolution,[],[f142,f39])).
% 1.25/0.52  fof(f39,plain,(
% 1.25/0.52    ~v5_tops_1(sK1,sK0) | ~v6_tops_1(sK1,sK0)),
% 1.25/0.52    inference(cnf_transformation,[],[f29])).
% 1.25/0.52  fof(f29,plain,(
% 1.25/0.52    ((~v6_tops_1(sK1,sK0) | ~v5_tops_1(sK1,sK0)) & (v6_tops_1(sK1,sK0) | v5_tops_1(sK1,sK0)) & v4_pre_topc(sK1,sK0) & v3_pre_topc(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 1.25/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f28,f27])).
% 1.25/0.52  fof(f27,plain,(
% 1.25/0.52    ? [X0] : (? [X1] : ((~v6_tops_1(X1,X0) | ~v5_tops_1(X1,X0)) & (v6_tops_1(X1,X0) | v5_tops_1(X1,X0)) & v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((~v6_tops_1(X1,sK0) | ~v5_tops_1(X1,sK0)) & (v6_tops_1(X1,sK0) | v5_tops_1(X1,sK0)) & v4_pre_topc(X1,sK0) & v3_pre_topc(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 1.25/0.52    introduced(choice_axiom,[])).
% 1.25/0.52  fof(f28,plain,(
% 1.25/0.52    ? [X1] : ((~v6_tops_1(X1,sK0) | ~v5_tops_1(X1,sK0)) & (v6_tops_1(X1,sK0) | v5_tops_1(X1,sK0)) & v4_pre_topc(X1,sK0) & v3_pre_topc(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((~v6_tops_1(sK1,sK0) | ~v5_tops_1(sK1,sK0)) & (v6_tops_1(sK1,sK0) | v5_tops_1(sK1,sK0)) & v4_pre_topc(sK1,sK0) & v3_pre_topc(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.25/0.52    introduced(choice_axiom,[])).
% 1.25/0.52  fof(f26,plain,(
% 1.25/0.52    ? [X0] : (? [X1] : ((~v6_tops_1(X1,X0) | ~v5_tops_1(X1,X0)) & (v6_tops_1(X1,X0) | v5_tops_1(X1,X0)) & v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.25/0.52    inference(flattening,[],[f25])).
% 1.25/0.52  fof(f25,plain,(
% 1.25/0.52    ? [X0] : (? [X1] : (((~v6_tops_1(X1,X0) | ~v5_tops_1(X1,X0)) & (v6_tops_1(X1,X0) | v5_tops_1(X1,X0))) & v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.25/0.52    inference(nnf_transformation,[],[f14])).
% 1.25/0.52  fof(f14,plain,(
% 1.25/0.52    ? [X0] : (? [X1] : ((v5_tops_1(X1,X0) <~> v6_tops_1(X1,X0)) & v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.25/0.52    inference(flattening,[],[f13])).
% 1.25/0.52  fof(f13,plain,(
% 1.25/0.52    ? [X0] : (? [X1] : (((v5_tops_1(X1,X0) <~> v6_tops_1(X1,X0)) & (v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.25/0.52    inference(ennf_transformation,[],[f12])).
% 1.25/0.52  fof(f12,negated_conjecture,(
% 1.25/0.52    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0)) => (v5_tops_1(X1,X0) <=> v6_tops_1(X1,X0)))))),
% 1.25/0.52    inference(negated_conjecture,[],[f11])).
% 1.25/0.52  fof(f11,conjecture,(
% 1.25/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0)) => (v5_tops_1(X1,X0) <=> v6_tops_1(X1,X0)))))),
% 1.25/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_tops_1)).
% 1.25/0.52  fof(f142,plain,(
% 1.25/0.52    v5_tops_1(sK1,sK0)),
% 1.25/0.52    inference(resolution,[],[f140,f35])).
% 1.25/0.52  fof(f35,plain,(
% 1.25/0.52    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.25/0.52    inference(cnf_transformation,[],[f29])).
% 1.25/0.52  fof(f140,plain,(
% 1.25/0.52    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v5_tops_1(sK1,sK0)),
% 1.25/0.52    inference(resolution,[],[f139,f34])).
% 1.25/0.52  fof(f34,plain,(
% 1.25/0.52    l1_pre_topc(sK0)),
% 1.25/0.52    inference(cnf_transformation,[],[f29])).
% 1.25/0.52  fof(f139,plain,(
% 1.25/0.52    ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v5_tops_1(sK1,sK0)),
% 1.25/0.52    inference(trivial_inequality_removal,[],[f138])).
% 1.25/0.52  fof(f138,plain,(
% 1.25/0.52    sK1 != sK1 | v5_tops_1(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 1.25/0.52    inference(forward_demodulation,[],[f137,f78])).
% 1.25/0.52  fof(f78,plain,(
% 1.25/0.52    sK1 = k2_pre_topc(sK0,sK1)),
% 1.25/0.52    inference(resolution,[],[f77,f35])).
% 1.25/0.52  fof(f77,plain,(
% 1.25/0.52    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = k2_pre_topc(sK0,sK1)),
% 1.25/0.52    inference(resolution,[],[f76,f37])).
% 1.25/0.52  fof(f37,plain,(
% 1.25/0.52    v4_pre_topc(sK1,sK0)),
% 1.25/0.52    inference(cnf_transformation,[],[f29])).
% 1.25/0.52  fof(f76,plain,(
% 1.25/0.52    ( ! [X0] : (~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = X0) )),
% 1.25/0.52    inference(resolution,[],[f41,f34])).
% 1.25/0.52  fof(f41,plain,(
% 1.25/0.52    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = X1) )),
% 1.25/0.52    inference(cnf_transformation,[],[f17])).
% 1.25/0.52  fof(f17,plain,(
% 1.25/0.52    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.25/0.52    inference(flattening,[],[f16])).
% 1.25/0.52  fof(f16,plain,(
% 1.25/0.52    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.25/0.52    inference(ennf_transformation,[],[f5])).
% 1.25/0.52  % (4619)Refutation not found, incomplete strategy% (4619)------------------------------
% 1.25/0.52  % (4619)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.52  % (4619)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.52  
% 1.25/0.52  % (4619)Memory used [KB]: 10618
% 1.25/0.52  % (4619)Time elapsed: 0.060 s
% 1.25/0.52  % (4619)------------------------------
% 1.25/0.52  % (4619)------------------------------
% 1.25/0.53  fof(f5,axiom,(
% 1.25/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 1.25/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).
% 1.25/0.53  fof(f137,plain,(
% 1.25/0.53    sK1 != k2_pre_topc(sK0,sK1) | v5_tops_1(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 1.25/0.53    inference(superposition,[],[f47,f136])).
% 1.25/0.53  fof(f136,plain,(
% 1.25/0.53    sK1 = k1_tops_1(sK0,sK1)),
% 1.25/0.53    inference(forward_demodulation,[],[f135,f63])).
% 1.25/0.53  fof(f63,plain,(
% 1.25/0.53    sK1 = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1))),
% 1.25/0.53    inference(forward_demodulation,[],[f61,f57])).
% 1.25/0.53  fof(f57,plain,(
% 1.25/0.53    k4_xboole_0(u1_struct_0(sK0),sK1) = k3_subset_1(u1_struct_0(sK0),sK1)),
% 1.25/0.53    inference(resolution,[],[f51,f35])).
% 1.25/0.53  fof(f51,plain,(
% 1.25/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 1.25/0.53    inference(cnf_transformation,[],[f23])).
% 1.25/0.53  fof(f23,plain,(
% 1.25/0.53    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.25/0.53    inference(ennf_transformation,[],[f2])).
% 1.25/0.53  fof(f2,axiom,(
% 1.25/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.25/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 1.25/0.53  fof(f61,plain,(
% 1.25/0.53    sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))),
% 1.25/0.53    inference(resolution,[],[f52,f35])).
% 1.25/0.53  fof(f52,plain,(
% 1.25/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 1.25/0.53    inference(cnf_transformation,[],[f24])).
% 1.25/0.53  fof(f24,plain,(
% 1.25/0.53    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.25/0.53    inference(ennf_transformation,[],[f3])).
% 1.25/0.53  fof(f3,axiom,(
% 1.25/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 1.25/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 1.25/0.53  fof(f135,plain,(
% 1.25/0.53    k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) = k1_tops_1(sK0,sK1)),
% 1.25/0.53    inference(forward_demodulation,[],[f134,f128])).
% 1.25/0.53  fof(f128,plain,(
% 1.25/0.53    k4_xboole_0(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))),
% 1.25/0.53    inference(resolution,[],[f127,f50])).
% 1.25/0.53  fof(f50,plain,(
% 1.25/0.53    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.25/0.53    inference(cnf_transformation,[],[f1])).
% 1.25/0.53  fof(f1,axiom,(
% 1.25/0.53    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.25/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.25/0.53  fof(f127,plain,(
% 1.25/0.53    ~r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | k4_xboole_0(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))),
% 1.25/0.53    inference(resolution,[],[f121,f54])).
% 1.25/0.53  fof(f54,plain,(
% 1.25/0.53    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.25/0.53    inference(cnf_transformation,[],[f33])).
% 1.25/0.53  fof(f33,plain,(
% 1.25/0.53    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.25/0.53    inference(nnf_transformation,[],[f4])).
% 1.25/0.53  fof(f4,axiom,(
% 1.25/0.53    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.25/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.25/0.53  fof(f121,plain,(
% 1.25/0.53    ~m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | k4_xboole_0(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))),
% 1.25/0.53    inference(resolution,[],[f119,f76])).
% 1.25/0.53  fof(f119,plain,(
% 1.25/0.53    v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)),
% 1.25/0.53    inference(resolution,[],[f117,f36])).
% 1.25/0.53  fof(f36,plain,(
% 1.25/0.53    v3_pre_topc(sK1,sK0)),
% 1.25/0.53    inference(cnf_transformation,[],[f29])).
% 1.25/0.53  fof(f117,plain,(
% 1.25/0.53    ~v3_pre_topc(sK1,sK0) | v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)),
% 1.25/0.53    inference(superposition,[],[f114,f68])).
% 1.25/0.53  fof(f68,plain,(
% 1.25/0.53    sK1 = k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1))),
% 1.25/0.53    inference(superposition,[],[f59,f63])).
% 1.25/0.53  fof(f59,plain,(
% 1.25/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_subset_1(X0,k4_xboole_0(X0,X1))) )),
% 1.25/0.53    inference(resolution,[],[f58,f50])).
% 1.25/0.53  fof(f58,plain,(
% 1.25/0.53    ( ! [X0,X1] : (~r1_tarski(X1,X0) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 1.25/0.53    inference(resolution,[],[f51,f54])).
% 1.25/0.53  fof(f114,plain,(
% 1.25/0.53    ( ! [X0] : (~v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),X0)),sK0) | v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),X0),sK0)) )),
% 1.25/0.53    inference(forward_demodulation,[],[f112,f59])).
% 1.25/0.53  fof(f112,plain,(
% 1.25/0.53    ( ! [X0] : (v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),X0),sK0) | ~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),X0)),sK0)) )),
% 1.25/0.53    inference(resolution,[],[f111,f50])).
% 1.25/0.53  fof(f111,plain,(
% 1.25/0.53    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK0)) | v4_pre_topc(X0,sK0) | ~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0)) )),
% 1.25/0.53    inference(resolution,[],[f109,f54])).
% 1.25/0.53  fof(f109,plain,(
% 1.25/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0) | v4_pre_topc(X0,sK0)) )),
% 1.25/0.53    inference(resolution,[],[f49,f34])).
% 1.25/0.53  fof(f49,plain,(
% 1.25/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v4_pre_topc(X1,X0)) )),
% 1.25/0.53    inference(cnf_transformation,[],[f32])).
% 1.25/0.53  fof(f32,plain,(
% 1.25/0.53    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | ~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.25/0.53    inference(nnf_transformation,[],[f22])).
% 1.25/0.53  fof(f22,plain,(
% 1.25/0.53    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.25/0.53    inference(ennf_transformation,[],[f9])).
% 1.25/0.53  fof(f9,axiom,(
% 1.25/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 1.25/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_1)).
% 1.25/0.53  fof(f134,plain,(
% 1.25/0.53    k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)))),
% 1.25/0.53    inference(forward_demodulation,[],[f132,f57])).
% 1.25/0.53  fof(f132,plain,(
% 1.25/0.53    k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))),
% 1.25/0.53    inference(resolution,[],[f131,f35])).
% 1.25/0.53  fof(f131,plain,(
% 1.25/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_tops_1(sK0,X0) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)))) )),
% 1.25/0.53    inference(resolution,[],[f40,f34])).
% 1.25/0.53  fof(f40,plain,(
% 1.25/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))) )),
% 1.25/0.53    inference(cnf_transformation,[],[f15])).
% 1.25/0.53  fof(f15,plain,(
% 1.25/0.53    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.25/0.53    inference(ennf_transformation,[],[f6])).
% 1.25/0.53  fof(f6,axiom,(
% 1.25/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))))),
% 1.25/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).
% 1.25/0.53  fof(f47,plain,(
% 1.25/0.53    ( ! [X0,X1] : (k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1 | v5_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.25/0.53    inference(cnf_transformation,[],[f31])).
% 1.25/0.53  fof(f31,plain,(
% 1.25/0.53    ! [X0] : (! [X1] : (((v5_tops_1(X1,X0) | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1) & (k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 | ~v5_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.25/0.53    inference(nnf_transformation,[],[f21])).
% 1.25/0.53  fof(f21,plain,(
% 1.25/0.53    ! [X0] : (! [X1] : ((v5_tops_1(X1,X0) <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.25/0.53    inference(ennf_transformation,[],[f7])).
% 1.25/0.53  fof(f7,axiom,(
% 1.25/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v5_tops_1(X1,X0) <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1)))),
% 1.25/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tops_1)).
% 1.25/0.53  fof(f187,plain,(
% 1.25/0.53    v6_tops_1(sK1,sK0)),
% 1.25/0.53    inference(resolution,[],[f177,f92])).
% 1.25/0.53  fof(f92,plain,(
% 1.25/0.53    ~v5_tops_1(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) | v6_tops_1(sK1,sK0)),
% 1.25/0.53    inference(forward_demodulation,[],[f90,f57])).
% 1.25/0.53  fof(f90,plain,(
% 1.25/0.53    ~v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | v6_tops_1(sK1,sK0)),
% 1.25/0.53    inference(resolution,[],[f87,f35])).
% 1.25/0.53  fof(f87,plain,(
% 1.25/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v5_tops_1(k3_subset_1(u1_struct_0(sK0),X0),sK0) | v6_tops_1(X0,sK0)) )),
% 1.25/0.53    inference(resolution,[],[f45,f34])).
% 1.25/0.53  fof(f45,plain,(
% 1.25/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v6_tops_1(X1,X0)) )),
% 1.25/0.53    inference(cnf_transformation,[],[f30])).
% 1.25/0.53  fof(f30,plain,(
% 1.25/0.53    ! [X0] : (! [X1] : (((v6_tops_1(X1,X0) | ~v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v6_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.25/0.53    inference(nnf_transformation,[],[f20])).
% 1.25/0.53  fof(f20,plain,(
% 1.25/0.53    ! [X0] : (! [X1] : ((v6_tops_1(X1,X0) <=> v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.25/0.53    inference(ennf_transformation,[],[f8])).
% 1.25/0.53  fof(f8,axiom,(
% 1.25/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v6_tops_1(X1,X0) <=> v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 1.25/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t101_tops_1)).
% 1.25/0.53  fof(f177,plain,(
% 1.25/0.53    v5_tops_1(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)),
% 1.25/0.53    inference(resolution,[],[f176,f50])).
% 1.25/0.53  fof(f176,plain,(
% 1.25/0.53    ~r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | v5_tops_1(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)),
% 1.25/0.53    inference(resolution,[],[f175,f54])).
% 1.25/0.53  fof(f175,plain,(
% 1.25/0.53    ~m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v5_tops_1(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)),
% 1.25/0.53    inference(resolution,[],[f174,f34])).
% 1.25/0.53  fof(f174,plain,(
% 1.25/0.53    ~l1_pre_topc(sK0) | ~m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v5_tops_1(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)),
% 1.25/0.53    inference(trivial_inequality_removal,[],[f173])).
% 1.25/0.53  fof(f173,plain,(
% 1.25/0.53    k4_xboole_0(u1_struct_0(sK0),sK1) != k4_xboole_0(u1_struct_0(sK0),sK1) | v5_tops_1(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) | ~m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 1.25/0.53    inference(forward_demodulation,[],[f172,f128])).
% 1.25/0.53  fof(f172,plain,(
% 1.25/0.53    k4_xboole_0(u1_struct_0(sK0),sK1) != k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) | v5_tops_1(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) | ~m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 1.25/0.53    inference(superposition,[],[f47,f169])).
% 1.25/0.53  fof(f169,plain,(
% 1.25/0.53    k4_xboole_0(u1_struct_0(sK0),sK1) = k1_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))),
% 1.25/0.53    inference(forward_demodulation,[],[f168,f57])).
% 1.25/0.53  fof(f168,plain,(
% 1.25/0.53    k3_subset_1(u1_struct_0(sK0),sK1) = k1_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))),
% 1.25/0.53    inference(forward_demodulation,[],[f164,f78])).
% 1.25/0.53  fof(f164,plain,(
% 1.25/0.53    k1_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))),
% 1.25/0.53    inference(superposition,[],[f153,f68])).
% 1.25/0.53  fof(f153,plain,(
% 1.25/0.53    ( ! [X0] : (k1_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),X0)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),X0))))) )),
% 1.25/0.53    inference(forward_demodulation,[],[f151,f59])).
% 1.25/0.53  fof(f151,plain,(
% 1.25/0.53    ( ! [X0] : (k1_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),X0)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),X0))))) )),
% 1.25/0.53    inference(resolution,[],[f133,f50])).
% 1.25/0.53  fof(f133,plain,(
% 1.25/0.53    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK0)) | k1_tops_1(sK0,X0) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)))) )),
% 1.25/0.53    inference(resolution,[],[f131,f54])).
% 1.25/0.53  % SZS output end Proof for theBenchmark
% 1.25/0.53  % (4605)------------------------------
% 1.25/0.53  % (4605)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.53  % (4605)Termination reason: Refutation
% 1.25/0.53  
% 1.25/0.53  % (4605)Memory used [KB]: 1663
% 1.25/0.53  % (4605)Time elapsed: 0.114 s
% 1.25/0.53  % (4605)------------------------------
% 1.25/0.53  % (4605)------------------------------
% 1.25/0.53  % (4595)Success in time 0.163 s
%------------------------------------------------------------------------------
