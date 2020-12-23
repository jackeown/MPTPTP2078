%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:28 EST 2020

% Result     : Theorem 1.29s
% Output     : Refutation 1.29s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 641 expanded)
%              Number of leaves         :   11 ( 123 expanded)
%              Depth                    :   21
%              Number of atoms          :  215 (3184 expanded)
%              Number of equality atoms :   26 ( 364 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f266,plain,(
    $false ),
    inference(subsumption_resolution,[],[f265,f231])).

fof(f231,plain,(
    ~ r1_tarski(k1_xboole_0,sK2) ),
    inference(subsumption_resolution,[],[f230,f96])).

fof(f96,plain,(
    k1_xboole_0 != sK2 ),
    inference(resolution,[],[f84,f29])).

fof(f29,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_1(X1,X0)
          <~> ! [X2] :
                ( k1_xboole_0 = X2
                | ~ v3_pre_topc(X2,X0)
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_1(X1,X0)
          <~> ! [X2] :
                ( k1_xboole_0 = X2
                | ~ v3_pre_topc(X2,X0)
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tops_1(X1,X0)
            <=> ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( v3_pre_topc(X2,X0)
                      & r1_tarski(X2,X1) )
                   => k1_xboole_0 = X2 ) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v3_pre_topc(X2,X0)
                    & r1_tarski(X2,X1) )
                 => k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_tops_1)).

fof(f84,plain,(
    v2_tops_1(sK1,sK0) ),
    inference(resolution,[],[f80,f71])).

fof(f71,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_tops_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f70,f57])).

fof(f57,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | v2_tops_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f52,f33])).

fof(f33,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f52,plain,
    ( ~ l1_pre_topc(sK0)
    | k1_xboole_0 != k1_tops_1(sK0,sK1)
    | v2_tops_1(sK1,sK0) ),
    inference(resolution,[],[f31,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k1_xboole_0 != k1_tops_1(X0,X1)
      | v2_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

fof(f31,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f15])).

fof(f70,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = k1_tops_1(sK0,sK1)
    | v2_tops_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f69,f54])).

fof(f54,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(subsumption_resolution,[],[f50,f33])).

fof(f50,plain,
    ( ~ l1_pre_topc(sK0)
    | r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(resolution,[],[f31,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
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

fof(f69,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = k1_tops_1(sK0,sK1)
    | v2_tops_1(sK1,sK0) ),
    inference(resolution,[],[f30,f56])).

fof(f56,plain,(
    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f55,f32])).

fof(f32,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f55,plain,
    ( ~ v2_pre_topc(sK0)
    | v3_pre_topc(k1_tops_1(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f51,f33])).

fof(f51,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v3_pre_topc(k1_tops_1(sK0,sK1),sK0) ),
    inference(resolution,[],[f31,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f30,plain,(
    ! [X2] :
      ( ~ v3_pre_topc(X2,sK0)
      | ~ r1_tarski(X2,sK1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_xboole_0 = X2
      | v2_tops_1(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f80,plain,(
    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f78,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f78,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) ),
    inference(resolution,[],[f66,f53])).

fof(f53,plain,(
    r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f31,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f66,plain,(
    ! [X1] :
      ( ~ r1_tarski(sK1,X1)
      | r1_tarski(k1_tops_1(sK0,sK1),X1) ) ),
    inference(resolution,[],[f54,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f230,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f225,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f225,plain,(
    r1_tarski(sK2,k1_xboole_0) ),
    inference(forward_demodulation,[],[f224,f101])).

fof(f101,plain,(
    k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f100,f33])).

fof(f100,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f99,f31])).

fof(f99,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f84,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_xboole_0 = k1_tops_1(X0,X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f224,plain,(
    r1_tarski(sK2,k1_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f221,f98])).

fof(f98,plain,(
    r1_tarski(sK2,sK1) ),
    inference(resolution,[],[f84,f27])).

fof(f27,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f221,plain,
    ( ~ r1_tarski(sK2,sK1)
    | r1_tarski(sK2,k1_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f138,f31])).

fof(f138,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(sK2,X0)
      | r1_tarski(sK2,k1_tops_1(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f137,f33])).

fof(f137,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ r1_tarski(sK2,X0)
      | r1_tarski(sK2,k1_tops_1(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f136,f95])).

fof(f95,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f84,f26])).

fof(f26,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f15])).

fof(f136,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ r1_tarski(sK2,X0)
      | r1_tarski(sK2,k1_tops_1(sK0,X0)) ) ),
    inference(resolution,[],[f97,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X1,k1_tops_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X1,X2)
                  & v3_pre_topc(X1,X0) )
               => r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_1)).

fof(f97,plain,(
    v3_pre_topc(sK2,sK0) ),
    inference(resolution,[],[f84,f28])).

fof(f28,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | v3_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f265,plain,(
    r1_tarski(k1_xboole_0,sK2) ),
    inference(superposition,[],[f46,f216])).

fof(f216,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(sK2,k4_xboole_0(X0,sK1)) ),
    inference(resolution,[],[f142,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f142,plain,(
    ! [X0] : r1_xboole_0(sK2,k4_xboole_0(X0,sK1)) ),
    inference(resolution,[],[f98,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

fof(f46,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:23:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.46  % (15085)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.51  % (15079)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.51  % (15084)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.51  % (15087)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (15096)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.52  % (15089)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.52  % (15076)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.29/0.52  % (15092)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.29/0.52  % (15080)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.29/0.52  % (15079)Refutation found. Thanks to Tanya!
% 1.29/0.52  % SZS status Theorem for theBenchmark
% 1.29/0.52  % SZS output start Proof for theBenchmark
% 1.29/0.52  fof(f266,plain,(
% 1.29/0.52    $false),
% 1.29/0.52    inference(subsumption_resolution,[],[f265,f231])).
% 1.29/0.52  fof(f231,plain,(
% 1.29/0.52    ~r1_tarski(k1_xboole_0,sK2)),
% 1.29/0.52    inference(subsumption_resolution,[],[f230,f96])).
% 1.29/0.52  fof(f96,plain,(
% 1.29/0.52    k1_xboole_0 != sK2),
% 1.29/0.52    inference(resolution,[],[f84,f29])).
% 1.29/0.52  fof(f29,plain,(
% 1.29/0.52    ~v2_tops_1(sK1,sK0) | k1_xboole_0 != sK2),
% 1.29/0.52    inference(cnf_transformation,[],[f15])).
% 1.29/0.52  fof(f15,plain,(
% 1.29/0.52    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> ! [X2] : (k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.29/0.52    inference(flattening,[],[f14])).
% 1.29/0.52  fof(f14,plain,(
% 1.29/0.52    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> ! [X2] : ((k1_xboole_0 = X2 | (~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.29/0.52    inference(ennf_transformation,[],[f12])).
% 1.29/0.52  fof(f12,negated_conjecture,(
% 1.29/0.52    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & r1_tarski(X2,X1)) => k1_xboole_0 = X2)))))),
% 1.29/0.52    inference(negated_conjecture,[],[f11])).
% 1.29/0.52  fof(f11,conjecture,(
% 1.29/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & r1_tarski(X2,X1)) => k1_xboole_0 = X2)))))),
% 1.29/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_tops_1)).
% 1.29/0.53  fof(f84,plain,(
% 1.29/0.53    v2_tops_1(sK1,sK0)),
% 1.29/0.53    inference(resolution,[],[f80,f71])).
% 1.29/0.53  fof(f71,plain,(
% 1.29/0.53    ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v2_tops_1(sK1,sK0)),
% 1.29/0.53    inference(subsumption_resolution,[],[f70,f57])).
% 1.29/0.53  fof(f57,plain,(
% 1.29/0.53    k1_xboole_0 != k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0)),
% 1.29/0.53    inference(subsumption_resolution,[],[f52,f33])).
% 1.29/0.53  fof(f33,plain,(
% 1.29/0.53    l1_pre_topc(sK0)),
% 1.29/0.53    inference(cnf_transformation,[],[f15])).
% 1.29/0.53  fof(f52,plain,(
% 1.29/0.53    ~l1_pre_topc(sK0) | k1_xboole_0 != k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0)),
% 1.29/0.53    inference(resolution,[],[f31,f38])).
% 1.29/0.53  fof(f38,plain,(
% 1.29/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k1_xboole_0 != k1_tops_1(X0,X1) | v2_tops_1(X1,X0)) )),
% 1.29/0.53    inference(cnf_transformation,[],[f17])).
% 1.29/0.53  fof(f17,plain,(
% 1.29/0.53    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.29/0.53    inference(ennf_transformation,[],[f10])).
% 1.29/0.53  fof(f10,axiom,(
% 1.29/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 1.29/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).
% 1.29/0.53  fof(f31,plain,(
% 1.29/0.53    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.29/0.53    inference(cnf_transformation,[],[f15])).
% 1.29/0.53  fof(f70,plain,(
% 1.29/0.53    ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0)),
% 1.29/0.53    inference(subsumption_resolution,[],[f69,f54])).
% 1.29/0.53  fof(f54,plain,(
% 1.29/0.53    r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 1.29/0.53    inference(subsumption_resolution,[],[f50,f33])).
% 1.29/0.53  fof(f50,plain,(
% 1.29/0.53    ~l1_pre_topc(sK0) | r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 1.29/0.53    inference(resolution,[],[f31,f45])).
% 1.29/0.53  fof(f45,plain,(
% 1.29/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | r1_tarski(k1_tops_1(X0,X1),X1)) )),
% 1.29/0.53    inference(cnf_transformation,[],[f24])).
% 1.29/0.53  fof(f24,plain,(
% 1.29/0.53    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.29/0.53    inference(ennf_transformation,[],[f8])).
% 1.29/0.53  fof(f8,axiom,(
% 1.29/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 1.29/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).
% 1.29/0.53  fof(f69,plain,(
% 1.29/0.53    ~r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0)),
% 1.29/0.53    inference(resolution,[],[f30,f56])).
% 1.29/0.53  fof(f56,plain,(
% 1.29/0.53    v3_pre_topc(k1_tops_1(sK0,sK1),sK0)),
% 1.29/0.53    inference(subsumption_resolution,[],[f55,f32])).
% 1.29/0.53  fof(f32,plain,(
% 1.29/0.53    v2_pre_topc(sK0)),
% 1.29/0.53    inference(cnf_transformation,[],[f15])).
% 1.29/0.53  fof(f55,plain,(
% 1.29/0.53    ~v2_pre_topc(sK0) | v3_pre_topc(k1_tops_1(sK0,sK1),sK0)),
% 1.29/0.53    inference(subsumption_resolution,[],[f51,f33])).
% 1.29/0.53  fof(f51,plain,(
% 1.29/0.53    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v3_pre_topc(k1_tops_1(sK0,sK1),sK0)),
% 1.29/0.53    inference(resolution,[],[f31,f40])).
% 1.29/0.53  fof(f40,plain,(
% 1.29/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v3_pre_topc(k1_tops_1(X0,X1),X0)) )),
% 1.29/0.53    inference(cnf_transformation,[],[f19])).
% 1.29/0.53  fof(f19,plain,(
% 1.29/0.53    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.29/0.53    inference(flattening,[],[f18])).
% 1.29/0.53  fof(f18,plain,(
% 1.29/0.53    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.29/0.53    inference(ennf_transformation,[],[f7])).
% 1.29/0.53  fof(f7,axiom,(
% 1.29/0.53    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 1.29/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).
% 1.29/0.53  fof(f30,plain,(
% 1.29/0.53    ( ! [X2] : (~v3_pre_topc(X2,sK0) | ~r1_tarski(X2,sK1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X2 | v2_tops_1(sK1,sK0)) )),
% 1.29/0.53    inference(cnf_transformation,[],[f15])).
% 1.29/0.53  fof(f80,plain,(
% 1.29/0.53    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.29/0.53    inference(resolution,[],[f78,f43])).
% 1.29/0.53  fof(f43,plain,(
% 1.29/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.29/0.53    inference(cnf_transformation,[],[f6])).
% 1.29/0.53  fof(f6,axiom,(
% 1.29/0.53    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.29/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.29/0.53  fof(f78,plain,(
% 1.29/0.53    r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))),
% 1.29/0.53    inference(resolution,[],[f66,f53])).
% 1.29/0.53  fof(f53,plain,(
% 1.29/0.53    r1_tarski(sK1,u1_struct_0(sK0))),
% 1.29/0.53    inference(resolution,[],[f31,f44])).
% 1.29/0.53  fof(f44,plain,(
% 1.29/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.29/0.53    inference(cnf_transformation,[],[f6])).
% 1.29/0.53  fof(f66,plain,(
% 1.29/0.53    ( ! [X1] : (~r1_tarski(sK1,X1) | r1_tarski(k1_tops_1(sK0,sK1),X1)) )),
% 1.29/0.53    inference(resolution,[],[f54,f42])).
% 1.29/0.53  fof(f42,plain,(
% 1.29/0.53    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) )),
% 1.29/0.53    inference(cnf_transformation,[],[f23])).
% 1.29/0.53  fof(f23,plain,(
% 1.29/0.53    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.29/0.53    inference(flattening,[],[f22])).
% 1.29/0.53  fof(f22,plain,(
% 1.29/0.53    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.29/0.53    inference(ennf_transformation,[],[f4])).
% 1.29/0.53  fof(f4,axiom,(
% 1.29/0.53    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.29/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.29/0.53  fof(f230,plain,(
% 1.29/0.53    ~r1_tarski(k1_xboole_0,sK2) | k1_xboole_0 = sK2),
% 1.29/0.53    inference(resolution,[],[f225,f37])).
% 1.29/0.53  fof(f37,plain,(
% 1.29/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.29/0.53    inference(cnf_transformation,[],[f2])).
% 1.29/0.53  fof(f2,axiom,(
% 1.29/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.29/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.29/0.53  fof(f225,plain,(
% 1.29/0.53    r1_tarski(sK2,k1_xboole_0)),
% 1.29/0.53    inference(forward_demodulation,[],[f224,f101])).
% 1.29/0.53  fof(f101,plain,(
% 1.29/0.53    k1_xboole_0 = k1_tops_1(sK0,sK1)),
% 1.29/0.53    inference(subsumption_resolution,[],[f100,f33])).
% 1.29/0.53  fof(f100,plain,(
% 1.29/0.53    k1_xboole_0 = k1_tops_1(sK0,sK1) | ~l1_pre_topc(sK0)),
% 1.29/0.53    inference(subsumption_resolution,[],[f99,f31])).
% 1.29/0.53  fof(f99,plain,(
% 1.29/0.53    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = k1_tops_1(sK0,sK1) | ~l1_pre_topc(sK0)),
% 1.29/0.53    inference(resolution,[],[f84,f39])).
% 1.29/0.53  fof(f39,plain,(
% 1.29/0.53    ( ! [X0,X1] : (~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 = k1_tops_1(X0,X1) | ~l1_pre_topc(X0)) )),
% 1.29/0.53    inference(cnf_transformation,[],[f17])).
% 1.29/0.53  fof(f224,plain,(
% 1.29/0.53    r1_tarski(sK2,k1_tops_1(sK0,sK1))),
% 1.29/0.53    inference(subsumption_resolution,[],[f221,f98])).
% 1.29/0.53  fof(f98,plain,(
% 1.29/0.53    r1_tarski(sK2,sK1)),
% 1.29/0.53    inference(resolution,[],[f84,f27])).
% 1.29/0.53  fof(f27,plain,(
% 1.29/0.53    ~v2_tops_1(sK1,sK0) | r1_tarski(sK2,sK1)),
% 1.29/0.53    inference(cnf_transformation,[],[f15])).
% 1.29/0.53  fof(f221,plain,(
% 1.29/0.53    ~r1_tarski(sK2,sK1) | r1_tarski(sK2,k1_tops_1(sK0,sK1))),
% 1.29/0.53    inference(resolution,[],[f138,f31])).
% 1.29/0.53  fof(f138,plain,(
% 1.29/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK2,X0) | r1_tarski(sK2,k1_tops_1(sK0,X0))) )),
% 1.29/0.53    inference(subsumption_resolution,[],[f137,f33])).
% 1.29/0.53  fof(f137,plain,(
% 1.29/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~r1_tarski(sK2,X0) | r1_tarski(sK2,k1_tops_1(sK0,X0))) )),
% 1.29/0.53    inference(subsumption_resolution,[],[f136,f95])).
% 1.29/0.53  fof(f95,plain,(
% 1.29/0.53    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.29/0.53    inference(resolution,[],[f84,f26])).
% 1.29/0.53  fof(f26,plain,(
% 1.29/0.53    ~v2_tops_1(sK1,sK0) | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.29/0.53    inference(cnf_transformation,[],[f15])).
% 1.29/0.53  fof(f136,plain,(
% 1.29/0.53    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~r1_tarski(sK2,X0) | r1_tarski(sK2,k1_tops_1(sK0,X0))) )),
% 1.29/0.53    inference(resolution,[],[f97,f41])).
% 1.29/0.53  fof(f41,plain,(
% 1.29/0.53    ( ! [X2,X0,X1] : (~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~r1_tarski(X1,X2) | r1_tarski(X1,k1_tops_1(X0,X2))) )),
% 1.29/0.53    inference(cnf_transformation,[],[f21])).
% 1.29/0.53  fof(f21,plain,(
% 1.29/0.53    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.29/0.53    inference(flattening,[],[f20])).
% 1.29/0.53  fof(f20,plain,(
% 1.29/0.53    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.29/0.53    inference(ennf_transformation,[],[f9])).
% 1.29/0.53  fof(f9,axiom,(
% 1.29/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 1.29/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_1)).
% 1.29/0.53  fof(f97,plain,(
% 1.29/0.53    v3_pre_topc(sK2,sK0)),
% 1.29/0.53    inference(resolution,[],[f84,f28])).
% 1.29/0.53  fof(f28,plain,(
% 1.29/0.53    ~v2_tops_1(sK1,sK0) | v3_pre_topc(sK2,sK0)),
% 1.29/0.53    inference(cnf_transformation,[],[f15])).
% 1.29/0.53  fof(f265,plain,(
% 1.29/0.53    r1_tarski(k1_xboole_0,sK2)),
% 1.29/0.53    inference(superposition,[],[f46,f216])).
% 1.29/0.53  fof(f216,plain,(
% 1.29/0.53    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(sK2,k4_xboole_0(X0,sK1))) )),
% 1.29/0.53    inference(resolution,[],[f142,f34])).
% 1.29/0.53  fof(f34,plain,(
% 1.29/0.53    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.29/0.53    inference(cnf_transformation,[],[f16])).
% 1.29/0.53  fof(f16,plain,(
% 1.29/0.53    ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1))),
% 1.29/0.53    inference(ennf_transformation,[],[f13])).
% 1.29/0.53  fof(f13,plain,(
% 1.29/0.53    ! [X0,X1] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.29/0.53    inference(unused_predicate_definition_removal,[],[f1])).
% 1.29/0.53  fof(f1,axiom,(
% 1.29/0.53    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.29/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.29/0.53  fof(f142,plain,(
% 1.29/0.53    ( ! [X0] : (r1_xboole_0(sK2,k4_xboole_0(X0,sK1))) )),
% 1.29/0.53    inference(resolution,[],[f98,f47])).
% 1.29/0.53  fof(f47,plain,(
% 1.29/0.53    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_xboole_0(X0,k4_xboole_0(X2,X1))) )),
% 1.29/0.53    inference(cnf_transformation,[],[f25])).
% 1.29/0.53  fof(f25,plain,(
% 1.29/0.53    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 1.29/0.53    inference(ennf_transformation,[],[f5])).
% 1.29/0.53  fof(f5,axiom,(
% 1.29/0.53    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 1.29/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).
% 1.29/0.53  fof(f46,plain,(
% 1.29/0.53    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.29/0.53    inference(cnf_transformation,[],[f3])).
% 1.29/0.53  fof(f3,axiom,(
% 1.29/0.53    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.29/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.29/0.53  % SZS output end Proof for theBenchmark
% 1.29/0.53  % (15079)------------------------------
% 1.29/0.53  % (15079)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.53  % (15079)Termination reason: Refutation
% 1.29/0.53  
% 1.29/0.53  % (15079)Memory used [KB]: 6268
% 1.29/0.53  % (15079)Time elapsed: 0.097 s
% 1.29/0.53  % (15079)------------------------------
% 1.29/0.53  % (15079)------------------------------
% 1.29/0.53  % (15068)Success in time 0.167 s
%------------------------------------------------------------------------------
