%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:09 EST 2020

% Result     : Theorem 6.30s
% Output     : Refutation 6.30s
% Verified   : 
% Statistics : Number of formulae       :  161 (24480 expanded)
%              Number of leaves         :   18 (6758 expanded)
%              Depth                    :   46
%              Number of atoms          :  289 (46188 expanded)
%              Number of equality atoms :  113 (18326 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12557,plain,(
    $false ),
    inference(subsumption_resolution,[],[f12553,f12361])).

fof(f12361,plain,(
    k2_tops_1(sK0,sK1) != k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f12265,f87])).

fof(f87,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | k2_tops_1(sK0,sK1) != k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f37,f84])).

fof(f84,plain,(
    ! [X2] : k7_subset_1(u1_struct_0(sK0),sK1,X2) = k4_xboole_0(sK1,X2) ),
    inference(resolution,[],[f38,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f38,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

fof(f37,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f12265,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(backward_demodulation,[],[f100,f12264])).

fof(f12264,plain,(
    sK1 = k2_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f12263,f3431])).

fof(f3431,plain,(
    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
    inference(superposition,[],[f3125,f553])).

fof(f553,plain,(
    k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f387,f552])).

fof(f552,plain,(
    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f75,f38])).

fof(f75,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,X4) = k4_subset_1(u1_struct_0(sK0),X4,k2_tops_1(sK0,X4)) ) ),
    inference(resolution,[],[f40,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

fof(f40,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f387,plain,(
    k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f83,f208])).

fof(f208,plain,(
    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f70,f38])).

fof(f70,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f40,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f83,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_xboole_0(sK1,X1) = k4_subset_1(u1_struct_0(sK0),sK1,X1) ) ),
    inference(resolution,[],[f38,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f3125,plain,(
    ! [X6,X7] : r1_tarski(X6,k2_xboole_0(X6,X7)) ),
    inference(forward_demodulation,[],[f3124,f3066])).

fof(f3066,plain,(
    ! [X4] : k4_xboole_0(X4,k1_xboole_0) = X4 ),
    inference(forward_demodulation,[],[f3060,f440])).

fof(f440,plain,(
    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK1) ),
    inference(forward_demodulation,[],[f420,f328])).

fof(f328,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK1) ),
    inference(superposition,[],[f323,f41])).

fof(f41,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f323,plain,(
    k1_xboole_0 = k2_xboole_0(k4_xboole_0(sK1,sK1),k1_xboole_0) ),
    inference(resolution,[],[f312,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f312,plain,(
    r1_tarski(k4_xboole_0(sK1,sK1),k1_xboole_0) ),
    inference(superposition,[],[f46,f194])).

fof(f194,plain,(
    k4_xboole_0(sK1,sK1) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,sK1)) ),
    inference(superposition,[],[f62,f189])).

fof(f189,plain,(
    sK1 = k4_xboole_0(sK1,k1_xboole_0) ),
    inference(forward_demodulation,[],[f184,f144])).

fof(f144,plain,(
    sK1 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK1)) ),
    inference(forward_demodulation,[],[f142,f95])).

fof(f95,plain,(
    ! [X1] : k4_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK1,u1_struct_0(sK0)),X1)) = k4_xboole_0(sK1,X1) ),
    inference(superposition,[],[f58,f92])).

fof(f92,plain,(
    sK1 = k4_xboole_0(sK1,k4_xboole_0(sK1,u1_struct_0(sK0))) ),
    inference(resolution,[],[f85,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f49,f48])).

fof(f48,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f85,plain,(
    r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f38,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f58,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f142,plain,(
    sK1 = k4_xboole_0(sK1,k4_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK1,u1_struct_0(sK0)),sK1))) ),
    inference(resolution,[],[f132,f63])).

fof(f132,plain,(
    r1_tarski(sK1,k2_xboole_0(k4_xboole_0(sK1,u1_struct_0(sK0)),sK1)) ),
    inference(resolution,[],[f94,f65])).

fof(f65,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f94,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK1,X0)
      | r1_tarski(sK1,k2_xboole_0(k4_xboole_0(sK1,u1_struct_0(sK0)),X0)) ) ),
    inference(superposition,[],[f60,f92])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k4_xboole_0(X0,X1),X2)
      | r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f184,plain,(
    k4_xboole_0(sK1,k4_xboole_0(sK1,sK1)) = k4_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[],[f146,f41])).

fof(f146,plain,(
    ! [X1] : k4_xboole_0(sK1,X1) = k4_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK1,sK1),X1)) ),
    inference(superposition,[],[f58,f144])).

fof(f62,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f47,f48,f48])).

fof(f47,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f46,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f420,plain,(
    k4_xboole_0(sK1,sK1) = k4_xboole_0(k1_xboole_0,sK1) ),
    inference(superposition,[],[f362,f374])).

fof(f374,plain,(
    sK1 = k2_xboole_0(sK1,sK1) ),
    inference(backward_demodulation,[],[f215,f369])).

fof(f369,plain,(
    sK1 = k2_xboole_0(k1_xboole_0,sK1) ),
    inference(resolution,[],[f364,f50])).

fof(f364,plain,(
    r1_tarski(k1_xboole_0,sK1) ),
    inference(superposition,[],[f46,f328])).

fof(f215,plain,(
    k2_xboole_0(k1_xboole_0,sK1) = k2_xboole_0(sK1,k2_xboole_0(k1_xboole_0,sK1)) ),
    inference(resolution,[],[f197,f50])).

fof(f197,plain,(
    r1_tarski(sK1,k2_xboole_0(k1_xboole_0,sK1)) ),
    inference(resolution,[],[f191,f65])).

fof(f191,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK1,X0)
      | r1_tarski(sK1,k2_xboole_0(k1_xboole_0,X0)) ) ),
    inference(superposition,[],[f60,f189])).

fof(f362,plain,(
    ! [X1] : k4_xboole_0(sK1,k2_xboole_0(sK1,X1)) = k4_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[],[f58,f328])).

fof(f3060,plain,(
    ! [X4] : k4_xboole_0(X4,k4_xboole_0(k1_xboole_0,sK1)) = X4 ),
    inference(backward_demodulation,[],[f529,f2999])).

fof(f2999,plain,(
    ! [X4,X5] : k4_xboole_0(k1_xboole_0,X5) = k4_xboole_0(X4,k2_xboole_0(k4_xboole_0(X4,k1_xboole_0),X5)) ),
    inference(superposition,[],[f58,f2859])).

fof(f2859,plain,(
    ! [X3] : k1_xboole_0 = k4_xboole_0(X3,k4_xboole_0(X3,k1_xboole_0)) ),
    inference(superposition,[],[f2829,f62])).

fof(f2829,plain,(
    ! [X7] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X7)) ),
    inference(forward_demodulation,[],[f2782,f358])).

fof(f358,plain,(
    ! [X1] : k4_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,X1)) = k4_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[],[f58,f356])).

fof(f356,plain,(
    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f327,f328])).

fof(f327,plain,(
    k4_xboole_0(sK1,sK1) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,sK1)) ),
    inference(forward_demodulation,[],[f326,f41])).

fof(f326,plain,(
    k4_xboole_0(sK1,sK1) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,k2_xboole_0(sK1,k1_xboole_0))) ),
    inference(forward_demodulation,[],[f324,f58])).

fof(f324,plain,(
    k4_xboole_0(sK1,sK1) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,sK1),k1_xboole_0)) ),
    inference(resolution,[],[f312,f63])).

fof(f2782,plain,(
    ! [X7] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,X7))) ),
    inference(resolution,[],[f2761,f63])).

fof(f2761,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,k2_xboole_0(k1_xboole_0,X0)) ),
    inference(forward_demodulation,[],[f2732,f41])).

fof(f2732,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,k2_xboole_0(k2_xboole_0(k1_xboole_0,X0),k1_xboole_0)) ),
    inference(resolution,[],[f414,f46])).

fof(f414,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k4_xboole_0(k1_xboole_0,X0),X1)
      | r1_tarski(k1_xboole_0,k2_xboole_0(k2_xboole_0(k1_xboole_0,X0),X1)) ) ),
    inference(superposition,[],[f60,f358])).

fof(f529,plain,(
    ! [X4] : k4_xboole_0(X4,k4_xboole_0(X4,k2_xboole_0(k4_xboole_0(X4,k1_xboole_0),sK1))) = X4 ),
    inference(resolution,[],[f492,f63])).

fof(f492,plain,(
    ! [X0] : r1_tarski(X0,k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),sK1)) ),
    inference(resolution,[],[f455,f60])).

fof(f455,plain,(
    ! [X2] : r1_tarski(k4_xboole_0(X2,k4_xboole_0(X2,k1_xboole_0)),sK1) ),
    inference(superposition,[],[f426,f62])).

fof(f426,plain,(
    ! [X7] : r1_tarski(k4_xboole_0(k1_xboole_0,X7),sK1) ),
    inference(superposition,[],[f46,f362])).

fof(f3124,plain,(
    ! [X6,X7] : r1_tarski(X6,k2_xboole_0(k4_xboole_0(X6,k1_xboole_0),X7)) ),
    inference(subsumption_resolution,[],[f3000,f2998])).

fof(f2998,plain,(
    ! [X3] : r1_tarski(k1_xboole_0,X3) ),
    inference(superposition,[],[f46,f2859])).

fof(f3000,plain,(
    ! [X6,X7] :
      ( ~ r1_tarski(k1_xboole_0,X7)
      | r1_tarski(X6,k2_xboole_0(k4_xboole_0(X6,k1_xboole_0),X7)) ) ),
    inference(superposition,[],[f60,f2859])).

fof(f12263,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
    inference(duplicate_literal_removal,[],[f12257])).

fof(f12257,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | sK1 = k2_pre_topc(sK0,sK1) ),
    inference(resolution,[],[f9967,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f9967,plain,
    ( r1_tarski(k2_pre_topc(sK0,sK1),sK1)
    | sK1 = k2_pre_topc(sK0,sK1) ),
    inference(forward_demodulation,[],[f9959,f553])).

fof(f9959,plain,
    ( r1_tarski(k2_xboole_0(sK1,k2_tops_1(sK0,sK1)),sK1)
    | sK1 = k2_pre_topc(sK0,sK1) ),
    inference(superposition,[],[f9825,f784])).

fof(f784,plain,
    ( sK1 = k2_xboole_0(k2_tops_1(sK0,sK1),sK1)
    | sK1 = k2_pre_topc(sK0,sK1) ),
    inference(resolution,[],[f467,f50])).

fof(f467,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | sK1 = k2_pre_topc(sK0,sK1) ),
    inference(superposition,[],[f46,f106])).

fof(f106,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | sK1 = k2_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f105,f38])).

fof(f105,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | sK1 = k2_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f104,f40])).

fof(f104,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | sK1 = k2_pre_topc(sK0,sK1) ),
    inference(resolution,[],[f86,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f86,plain,
    ( v4_pre_topc(sK1,sK0)
    | k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f36,f84])).

fof(f36,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f9825,plain,(
    ! [X0] : r1_tarski(k2_xboole_0(sK1,X0),k2_xboole_0(X0,sK1)) ),
    inference(superposition,[],[f5717,f9677])).

fof(f9677,plain,(
    ! [X8,X9] : k2_xboole_0(k4_xboole_0(k2_xboole_0(X8,X9),X8),X9) = X9 ),
    inference(resolution,[],[f9643,f50])).

fof(f9643,plain,(
    ! [X21,X20] : r1_tarski(k4_xboole_0(k2_xboole_0(X20,X21),X20),X21) ),
    inference(forward_demodulation,[],[f9604,f41])).

fof(f9604,plain,(
    ! [X21,X20] : r1_tarski(k4_xboole_0(k2_xboole_0(X20,X21),X20),k2_xboole_0(X21,k1_xboole_0)) ),
    inference(superposition,[],[f4471,f3069])).

fof(f3069,plain,(
    ! [X3] : k1_xboole_0 = k4_xboole_0(X3,X3) ),
    inference(backward_demodulation,[],[f2859,f3066])).

fof(f4471,plain,(
    ! [X14,X15,X13] : r1_tarski(k4_xboole_0(X13,X14),k2_xboole_0(X15,k4_xboole_0(X13,k2_xboole_0(X14,X15)))) ),
    inference(superposition,[],[f4437,f58])).

fof(f4437,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) ),
    inference(superposition,[],[f3414,f4299])).

fof(f4299,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(superposition,[],[f3410,f41])).

fof(f3410,plain,(
    ! [X6,X7] : k2_xboole_0(X6,X7) = k2_xboole_0(X6,k2_xboole_0(X6,X7)) ),
    inference(resolution,[],[f3125,f50])).

fof(f3414,plain,(
    ! [X14,X12,X13] : r1_tarski(X12,k2_xboole_0(X13,k2_xboole_0(k4_xboole_0(X12,X13),X14))) ),
    inference(resolution,[],[f3125,f60])).

fof(f5717,plain,(
    ! [X10,X9] : r1_tarski(X9,k2_xboole_0(k2_xboole_0(k4_xboole_0(X9,sK1),X10),sK1)) ),
    inference(superposition,[],[f3831,f3191])).

fof(f3191,plain,(
    ! [X5] : k2_xboole_0(X5,sK1) = k2_xboole_0(sK1,k2_xboole_0(X5,sK1)) ),
    inference(backward_demodulation,[],[f2213,f3160])).

fof(f3160,plain,(
    ! [X6] : k2_xboole_0(k1_xboole_0,X6) = X6 ),
    inference(resolution,[],[f2998,f50])).

fof(f2213,plain,(
    ! [X5] : k2_xboole_0(k2_xboole_0(k1_xboole_0,X5),sK1) = k2_xboole_0(sK1,k2_xboole_0(k2_xboole_0(k1_xboole_0,X5),sK1)) ),
    inference(resolution,[],[f2156,f50])).

fof(f2156,plain,(
    ! [X0] : r1_tarski(sK1,k2_xboole_0(k2_xboole_0(k1_xboole_0,X0),sK1)) ),
    inference(resolution,[],[f302,f46])).

fof(f302,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k4_xboole_0(sK1,X0),X1)
      | r1_tarski(sK1,k2_xboole_0(k2_xboole_0(k1_xboole_0,X0),X1)) ) ),
    inference(superposition,[],[f60,f192])).

fof(f192,plain,(
    ! [X1] : k4_xboole_0(sK1,X1) = k4_xboole_0(sK1,k2_xboole_0(k1_xboole_0,X1)) ),
    inference(superposition,[],[f58,f189])).

fof(f3831,plain,(
    ! [X21,X19,X22,X20] : r1_tarski(X19,k2_xboole_0(X20,k2_xboole_0(k2_xboole_0(k4_xboole_0(X19,X20),X21),X22))) ),
    inference(resolution,[],[f3808,f60])).

fof(f3808,plain,(
    ! [X6,X7,X5] : r1_tarski(X5,k2_xboole_0(k2_xboole_0(X5,X6),X7)) ),
    inference(subsumption_resolution,[],[f3769,f2998])).

fof(f3769,plain,(
    ! [X6,X7,X5] :
      ( ~ r1_tarski(k1_xboole_0,X7)
      | r1_tarski(X5,k2_xboole_0(k2_xboole_0(X5,X6),X7)) ) ),
    inference(superposition,[],[f60,f3490])).

fof(f3490,plain,(
    ! [X4,X5] : k1_xboole_0 = k4_xboole_0(X4,k2_xboole_0(X4,X5)) ),
    inference(backward_demodulation,[],[f3070,f3465])).

fof(f3465,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f3158,f46])).

fof(f3158,plain,(
    ! [X4] :
      ( ~ r1_tarski(X4,k1_xboole_0)
      | k1_xboole_0 = X4 ) ),
    inference(resolution,[],[f2998,f55])).

fof(f3070,plain,(
    ! [X4,X5] : k4_xboole_0(k1_xboole_0,X5) = k4_xboole_0(X4,k2_xboole_0(X4,X5)) ),
    inference(backward_demodulation,[],[f2999,f3066])).

fof(f100,plain,(
    v4_pre_topc(k2_pre_topc(sK0,sK1),sK0) ),
    inference(resolution,[],[f68,f38])).

fof(f68,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v4_pre_topc(k2_pre_topc(sK0,X0),sK0) ) ),
    inference(subsumption_resolution,[],[f66,f40])).

fof(f66,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v4_pre_topc(k2_pre_topc(sK0,X0),sK0) ) ),
    inference(resolution,[],[f39,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).

fof(f39,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f12553,plain,(
    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    inference(superposition,[],[f12270,f84])).

fof(f12270,plain,(
    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f621,f12264])).

fof(f621,plain,(
    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f74,f38])).

fof(f74,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_tops_1(sK0,X3) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X3),k1_tops_1(sK0,X3)) ) ),
    inference(resolution,[],[f40,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_vampire %s %d
% 0.11/0.33  % Computer   : n022.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 10:06:11 EST 2020
% 0.11/0.34  % CPUTime    : 
% 0.19/0.48  % (11172)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.19/0.49  % (11164)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.19/0.49  % (11150)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.19/0.50  % (11153)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.19/0.50  % (11152)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.19/0.50  % (11155)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.19/0.50  % (11151)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.19/0.50  % (11161)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.19/0.52  % (11175)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.19/0.52  % (11174)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.19/0.52  % (11173)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.35/0.53  % (11163)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.35/0.53  % (11157)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.35/0.53  % (11178)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.35/0.53  % (11160)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.35/0.53  % (11170)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.35/0.54  % (11177)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.35/0.54  % (11166)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.35/0.54  % (11165)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.35/0.54  % (11166)Refutation not found, incomplete strategy% (11166)------------------------------
% 1.35/0.54  % (11166)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.54  % (11159)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.54/0.55  % (11156)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.54/0.55  % (11166)Termination reason: Refutation not found, incomplete strategy
% 1.54/0.55  
% 1.54/0.55  % (11166)Memory used [KB]: 10618
% 1.54/0.55  % (11166)Time elapsed: 0.134 s
% 1.54/0.55  % (11166)------------------------------
% 1.54/0.55  % (11166)------------------------------
% 1.54/0.55  % (11171)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.54/0.55  % (11158)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.54/0.55  % (11167)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.54/0.55  % (11154)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.54/0.55  % (11169)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.54/0.56  % (11176)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.54/0.56  % (11162)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.54/0.56  % (11179)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.54/0.57  % (11168)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 2.63/0.70  % (11180)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 3.17/0.80  % (11152)Time limit reached!
% 3.17/0.80  % (11152)------------------------------
% 3.17/0.80  % (11152)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.17/0.80  % (11152)Termination reason: Time limit
% 3.17/0.80  
% 3.17/0.80  % (11152)Memory used [KB]: 6652
% 3.17/0.80  % (11152)Time elapsed: 0.409 s
% 3.17/0.80  % (11152)------------------------------
% 3.17/0.80  % (11152)------------------------------
% 3.52/0.82  % (11174)Time limit reached!
% 3.52/0.82  % (11174)------------------------------
% 3.52/0.82  % (11174)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.52/0.82  % (11174)Termination reason: Time limit
% 3.52/0.82  % (11174)Termination phase: Saturation
% 3.52/0.82  
% 3.52/0.82  % (11174)Memory used [KB]: 13944
% 3.52/0.82  % (11174)Time elapsed: 0.400 s
% 3.52/0.82  % (11174)------------------------------
% 3.52/0.82  % (11174)------------------------------
% 3.81/0.90  % (11156)Time limit reached!
% 3.81/0.90  % (11156)------------------------------
% 3.81/0.90  % (11156)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.81/0.90  % (11156)Termination reason: Time limit
% 3.81/0.90  
% 3.81/0.90  % (11156)Memory used [KB]: 14200
% 3.81/0.90  % (11156)Time elapsed: 0.510 s
% 3.81/0.90  % (11156)------------------------------
% 3.81/0.90  % (11156)------------------------------
% 3.81/0.90  % (11179)Time limit reached!
% 3.81/0.90  % (11179)------------------------------
% 3.81/0.90  % (11179)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.81/0.90  % (11179)Termination reason: Time limit
% 3.81/0.90  
% 3.81/0.90  % (11179)Memory used [KB]: 1918
% 3.81/0.90  % (11179)Time elapsed: 0.510 s
% 3.81/0.90  % (11179)------------------------------
% 3.81/0.90  % (11179)------------------------------
% 4.41/0.94  % (11164)Time limit reached!
% 4.41/0.94  % (11164)------------------------------
% 4.41/0.94  % (11164)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.41/0.94  % (11164)Termination reason: Time limit
% 4.41/0.94  
% 4.41/0.94  % (11164)Memory used [KB]: 6524
% 4.41/0.94  % (11164)Time elapsed: 0.510 s
% 4.41/0.94  % (11164)------------------------------
% 4.41/0.94  % (11164)------------------------------
% 4.41/0.96  % (11182)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 4.41/0.97  % (11181)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 4.78/1.01  % (11157)Time limit reached!
% 4.78/1.01  % (11157)------------------------------
% 4.78/1.01  % (11157)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.78/1.01  % (11157)Termination reason: Time limit
% 4.78/1.01  
% 4.78/1.01  % (11157)Memory used [KB]: 6780
% 4.78/1.01  % (11157)Time elapsed: 0.607 s
% 4.78/1.01  % (11157)------------------------------
% 4.78/1.01  % (11157)------------------------------
% 4.78/1.03  % (11183)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 4.78/1.04  % (11184)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 4.78/1.05  % (11185)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 6.30/1.16  % (11186)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 6.30/1.19  % (11167)Refutation found. Thanks to Tanya!
% 6.30/1.19  % SZS status Theorem for theBenchmark
% 6.30/1.19  % SZS output start Proof for theBenchmark
% 6.30/1.19  fof(f12557,plain,(
% 6.30/1.19    $false),
% 6.30/1.19    inference(subsumption_resolution,[],[f12553,f12361])).
% 6.30/1.19  fof(f12361,plain,(
% 6.30/1.19    k2_tops_1(sK0,sK1) != k4_xboole_0(sK1,k1_tops_1(sK0,sK1))),
% 6.30/1.19    inference(resolution,[],[f12265,f87])).
% 6.30/1.19  fof(f87,plain,(
% 6.30/1.19    ~v4_pre_topc(sK1,sK0) | k2_tops_1(sK0,sK1) != k4_xboole_0(sK1,k1_tops_1(sK0,sK1))),
% 6.30/1.19    inference(backward_demodulation,[],[f37,f84])).
% 6.30/1.19  fof(f84,plain,(
% 6.30/1.19    ( ! [X2] : (k7_subset_1(u1_struct_0(sK0),sK1,X2) = k4_xboole_0(sK1,X2)) )),
% 6.30/1.19    inference(resolution,[],[f38,f59])).
% 6.30/1.19  fof(f59,plain,(
% 6.30/1.19    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)) )),
% 6.30/1.19    inference(cnf_transformation,[],[f32])).
% 6.30/1.19  fof(f32,plain,(
% 6.30/1.19    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 6.30/1.19    inference(ennf_transformation,[],[f11])).
% 6.30/1.19  fof(f11,axiom,(
% 6.30/1.19    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 6.30/1.19    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 6.30/1.19  fof(f38,plain,(
% 6.30/1.19    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 6.30/1.19    inference(cnf_transformation,[],[f21])).
% 6.30/1.19  fof(f21,plain,(
% 6.30/1.19    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 6.30/1.19    inference(flattening,[],[f20])).
% 6.30/1.19  fof(f20,plain,(
% 6.30/1.19    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 6.30/1.19    inference(ennf_transformation,[],[f19])).
% 6.30/1.19  fof(f19,negated_conjecture,(
% 6.30/1.19    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 6.30/1.19    inference(negated_conjecture,[],[f18])).
% 6.30/1.19  fof(f18,conjecture,(
% 6.30/1.19    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 6.30/1.19    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).
% 6.30/1.19  fof(f37,plain,(
% 6.30/1.19    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)),
% 6.30/1.19    inference(cnf_transformation,[],[f21])).
% 6.30/1.19  fof(f12265,plain,(
% 6.30/1.19    v4_pre_topc(sK1,sK0)),
% 6.30/1.19    inference(backward_demodulation,[],[f100,f12264])).
% 6.30/1.19  fof(f12264,plain,(
% 6.30/1.19    sK1 = k2_pre_topc(sK0,sK1)),
% 6.30/1.19    inference(subsumption_resolution,[],[f12263,f3431])).
% 6.30/1.19  fof(f3431,plain,(
% 6.30/1.19    r1_tarski(sK1,k2_pre_topc(sK0,sK1))),
% 6.30/1.19    inference(superposition,[],[f3125,f553])).
% 6.30/1.19  fof(f553,plain,(
% 6.30/1.19    k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 6.30/1.19    inference(backward_demodulation,[],[f387,f552])).
% 6.30/1.19  fof(f552,plain,(
% 6.30/1.19    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 6.30/1.19    inference(resolution,[],[f75,f38])).
% 6.30/1.19  fof(f75,plain,(
% 6.30/1.19    ( ! [X4] : (~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X4) = k4_subset_1(u1_struct_0(sK0),X4,k2_tops_1(sK0,X4))) )),
% 6.30/1.19    inference(resolution,[],[f40,f42])).
% 6.30/1.19  fof(f42,plain,(
% 6.30/1.19    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))) )),
% 6.30/1.19    inference(cnf_transformation,[],[f22])).
% 6.30/1.19  fof(f22,plain,(
% 6.30/1.19    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 6.30/1.19    inference(ennf_transformation,[],[f17])).
% 6.30/1.19  fof(f17,axiom,(
% 6.30/1.19    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 6.30/1.19    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).
% 6.30/1.19  fof(f40,plain,(
% 6.30/1.19    l1_pre_topc(sK0)),
% 6.30/1.19    inference(cnf_transformation,[],[f21])).
% 6.30/1.19  fof(f387,plain,(
% 6.30/1.19    k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 6.30/1.19    inference(resolution,[],[f83,f208])).
% 6.30/1.19  fof(f208,plain,(
% 6.30/1.19    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 6.30/1.19    inference(resolution,[],[f70,f38])).
% 6.30/1.19  fof(f70,plain,(
% 6.30/1.19    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 6.30/1.19    inference(resolution,[],[f40,f52])).
% 6.30/1.19  fof(f52,plain,(
% 6.30/1.19    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 6.30/1.19    inference(cnf_transformation,[],[f31])).
% 6.30/1.19  fof(f31,plain,(
% 6.30/1.19    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 6.30/1.19    inference(flattening,[],[f30])).
% 6.30/1.19  fof(f30,plain,(
% 6.30/1.19    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 6.30/1.19    inference(ennf_transformation,[],[f14])).
% 6.30/1.19  fof(f14,axiom,(
% 6.30/1.19    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 6.30/1.19    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 6.30/1.19  fof(f83,plain,(
% 6.30/1.19    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k2_xboole_0(sK1,X1) = k4_subset_1(u1_struct_0(sK0),sK1,X1)) )),
% 6.30/1.19    inference(resolution,[],[f38,f61])).
% 6.30/1.19  fof(f61,plain,(
% 6.30/1.19    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)) )),
% 6.30/1.19    inference(cnf_transformation,[],[f35])).
% 6.30/1.19  fof(f35,plain,(
% 6.30/1.19    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 6.30/1.19    inference(flattening,[],[f34])).
% 6.30/1.19  fof(f34,plain,(
% 6.30/1.19    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 6.30/1.19    inference(ennf_transformation,[],[f10])).
% 6.30/1.19  fof(f10,axiom,(
% 6.30/1.19    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 6.30/1.19    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 6.30/1.19  fof(f3125,plain,(
% 6.30/1.19    ( ! [X6,X7] : (r1_tarski(X6,k2_xboole_0(X6,X7))) )),
% 6.30/1.19    inference(forward_demodulation,[],[f3124,f3066])).
% 6.30/1.19  fof(f3066,plain,(
% 6.30/1.19    ( ! [X4] : (k4_xboole_0(X4,k1_xboole_0) = X4) )),
% 6.30/1.19    inference(forward_demodulation,[],[f3060,f440])).
% 6.30/1.19  fof(f440,plain,(
% 6.30/1.19    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK1)),
% 6.30/1.19    inference(forward_demodulation,[],[f420,f328])).
% 6.30/1.19  fof(f328,plain,(
% 6.30/1.19    k1_xboole_0 = k4_xboole_0(sK1,sK1)),
% 6.30/1.19    inference(superposition,[],[f323,f41])).
% 6.30/1.19  fof(f41,plain,(
% 6.30/1.19    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 6.30/1.19    inference(cnf_transformation,[],[f4])).
% 6.30/1.19  fof(f4,axiom,(
% 6.30/1.19    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 6.30/1.19    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 6.30/1.19  fof(f323,plain,(
% 6.30/1.19    k1_xboole_0 = k2_xboole_0(k4_xboole_0(sK1,sK1),k1_xboole_0)),
% 6.30/1.19    inference(resolution,[],[f312,f50])).
% 6.30/1.19  fof(f50,plain,(
% 6.30/1.19    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 6.30/1.19    inference(cnf_transformation,[],[f27])).
% 6.30/1.19  fof(f27,plain,(
% 6.30/1.19    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 6.30/1.19    inference(ennf_transformation,[],[f3])).
% 6.30/1.19  fof(f3,axiom,(
% 6.30/1.19    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 6.30/1.19    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 6.30/1.19  fof(f312,plain,(
% 6.30/1.19    r1_tarski(k4_xboole_0(sK1,sK1),k1_xboole_0)),
% 6.30/1.19    inference(superposition,[],[f46,f194])).
% 6.30/1.19  fof(f194,plain,(
% 6.30/1.19    k4_xboole_0(sK1,sK1) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,sK1))),
% 6.30/1.19    inference(superposition,[],[f62,f189])).
% 6.30/1.19  fof(f189,plain,(
% 6.30/1.19    sK1 = k4_xboole_0(sK1,k1_xboole_0)),
% 6.30/1.19    inference(forward_demodulation,[],[f184,f144])).
% 6.30/1.19  fof(f144,plain,(
% 6.30/1.19    sK1 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK1))),
% 6.30/1.19    inference(forward_demodulation,[],[f142,f95])).
% 6.30/1.19  fof(f95,plain,(
% 6.30/1.19    ( ! [X1] : (k4_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK1,u1_struct_0(sK0)),X1)) = k4_xboole_0(sK1,X1)) )),
% 6.30/1.19    inference(superposition,[],[f58,f92])).
% 6.30/1.19  fof(f92,plain,(
% 6.30/1.19    sK1 = k4_xboole_0(sK1,k4_xboole_0(sK1,u1_struct_0(sK0)))),
% 6.30/1.19    inference(resolution,[],[f85,f63])).
% 6.30/1.19  fof(f63,plain,(
% 6.30/1.19    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0) )),
% 6.30/1.19    inference(definition_unfolding,[],[f49,f48])).
% 6.30/1.19  fof(f48,plain,(
% 6.30/1.19    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 6.30/1.19    inference(cnf_transformation,[],[f9])).
% 6.30/1.19  fof(f9,axiom,(
% 6.30/1.19    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 6.30/1.19    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 6.30/1.19  fof(f49,plain,(
% 6.30/1.19    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 6.30/1.19    inference(cnf_transformation,[],[f26])).
% 6.30/1.19  fof(f26,plain,(
% 6.30/1.19    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 6.30/1.19    inference(ennf_transformation,[],[f5])).
% 6.30/1.19  fof(f5,axiom,(
% 6.30/1.19    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 6.30/1.19    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 6.30/1.19  fof(f85,plain,(
% 6.30/1.19    r1_tarski(sK1,u1_struct_0(sK0))),
% 6.30/1.19    inference(resolution,[],[f38,f57])).
% 6.30/1.19  fof(f57,plain,(
% 6.30/1.19    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 6.30/1.19    inference(cnf_transformation,[],[f12])).
% 6.30/1.19  fof(f12,axiom,(
% 6.30/1.19    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 6.30/1.19    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 6.30/1.19  fof(f58,plain,(
% 6.30/1.19    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 6.30/1.19    inference(cnf_transformation,[],[f7])).
% 6.30/1.19  fof(f7,axiom,(
% 6.30/1.19    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 6.30/1.19    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 6.30/1.19  fof(f142,plain,(
% 6.30/1.19    sK1 = k4_xboole_0(sK1,k4_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK1,u1_struct_0(sK0)),sK1)))),
% 6.30/1.19    inference(resolution,[],[f132,f63])).
% 6.30/1.19  fof(f132,plain,(
% 6.30/1.19    r1_tarski(sK1,k2_xboole_0(k4_xboole_0(sK1,u1_struct_0(sK0)),sK1))),
% 6.30/1.19    inference(resolution,[],[f94,f65])).
% 6.30/1.19  fof(f65,plain,(
% 6.30/1.19    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 6.30/1.19    inference(equality_resolution,[],[f53])).
% 6.30/1.19  fof(f53,plain,(
% 6.30/1.19    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 6.30/1.19    inference(cnf_transformation,[],[f2])).
% 6.30/1.19  fof(f2,axiom,(
% 6.30/1.19    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 6.30/1.19    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 6.30/1.19  fof(f94,plain,(
% 6.30/1.19    ( ! [X0] : (~r1_tarski(sK1,X0) | r1_tarski(sK1,k2_xboole_0(k4_xboole_0(sK1,u1_struct_0(sK0)),X0))) )),
% 6.30/1.19    inference(superposition,[],[f60,f92])).
% 6.30/1.21  fof(f60,plain,(
% 6.30/1.21    ( ! [X2,X0,X1] : (~r1_tarski(k4_xboole_0(X0,X1),X2) | r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 6.30/1.21    inference(cnf_transformation,[],[f33])).
% 6.30/1.21  fof(f33,plain,(
% 6.30/1.21    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 6.30/1.21    inference(ennf_transformation,[],[f8])).
% 6.30/1.21  fof(f8,axiom,(
% 6.30/1.21    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 6.30/1.21    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).
% 6.30/1.21  fof(f184,plain,(
% 6.30/1.21    k4_xboole_0(sK1,k4_xboole_0(sK1,sK1)) = k4_xboole_0(sK1,k1_xboole_0)),
% 6.30/1.21    inference(superposition,[],[f146,f41])).
% 6.30/1.21  fof(f146,plain,(
% 6.30/1.21    ( ! [X1] : (k4_xboole_0(sK1,X1) = k4_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK1,sK1),X1))) )),
% 6.30/1.21    inference(superposition,[],[f58,f144])).
% 6.30/1.21  fof(f62,plain,(
% 6.30/1.21    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 6.30/1.21    inference(definition_unfolding,[],[f47,f48,f48])).
% 6.30/1.21  fof(f47,plain,(
% 6.30/1.21    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 6.30/1.21    inference(cnf_transformation,[],[f1])).
% 6.30/1.21  fof(f1,axiom,(
% 6.30/1.21    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 6.30/1.21    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 6.30/1.21  fof(f46,plain,(
% 6.30/1.21    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 6.30/1.21    inference(cnf_transformation,[],[f6])).
% 6.30/1.21  fof(f6,axiom,(
% 6.30/1.21    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 6.30/1.21    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 6.30/1.21  fof(f420,plain,(
% 6.30/1.21    k4_xboole_0(sK1,sK1) = k4_xboole_0(k1_xboole_0,sK1)),
% 6.30/1.21    inference(superposition,[],[f362,f374])).
% 6.30/1.21  fof(f374,plain,(
% 6.30/1.21    sK1 = k2_xboole_0(sK1,sK1)),
% 6.30/1.21    inference(backward_demodulation,[],[f215,f369])).
% 6.30/1.21  fof(f369,plain,(
% 6.30/1.21    sK1 = k2_xboole_0(k1_xboole_0,sK1)),
% 6.30/1.21    inference(resolution,[],[f364,f50])).
% 6.30/1.21  fof(f364,plain,(
% 6.30/1.21    r1_tarski(k1_xboole_0,sK1)),
% 6.30/1.21    inference(superposition,[],[f46,f328])).
% 6.30/1.21  fof(f215,plain,(
% 6.30/1.21    k2_xboole_0(k1_xboole_0,sK1) = k2_xboole_0(sK1,k2_xboole_0(k1_xboole_0,sK1))),
% 6.30/1.21    inference(resolution,[],[f197,f50])).
% 6.30/1.21  fof(f197,plain,(
% 6.30/1.21    r1_tarski(sK1,k2_xboole_0(k1_xboole_0,sK1))),
% 6.30/1.21    inference(resolution,[],[f191,f65])).
% 6.30/1.21  fof(f191,plain,(
% 6.30/1.21    ( ! [X0] : (~r1_tarski(sK1,X0) | r1_tarski(sK1,k2_xboole_0(k1_xboole_0,X0))) )),
% 6.30/1.21    inference(superposition,[],[f60,f189])).
% 6.30/1.21  fof(f362,plain,(
% 6.30/1.21    ( ! [X1] : (k4_xboole_0(sK1,k2_xboole_0(sK1,X1)) = k4_xboole_0(k1_xboole_0,X1)) )),
% 6.30/1.21    inference(superposition,[],[f58,f328])).
% 6.30/1.21  fof(f3060,plain,(
% 6.30/1.21    ( ! [X4] : (k4_xboole_0(X4,k4_xboole_0(k1_xboole_0,sK1)) = X4) )),
% 6.30/1.21    inference(backward_demodulation,[],[f529,f2999])).
% 6.30/1.21  fof(f2999,plain,(
% 6.30/1.21    ( ! [X4,X5] : (k4_xboole_0(k1_xboole_0,X5) = k4_xboole_0(X4,k2_xboole_0(k4_xboole_0(X4,k1_xboole_0),X5))) )),
% 6.30/1.21    inference(superposition,[],[f58,f2859])).
% 6.30/1.21  fof(f2859,plain,(
% 6.30/1.21    ( ! [X3] : (k1_xboole_0 = k4_xboole_0(X3,k4_xboole_0(X3,k1_xboole_0))) )),
% 6.30/1.21    inference(superposition,[],[f2829,f62])).
% 6.30/1.21  fof(f2829,plain,(
% 6.30/1.21    ( ! [X7] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X7))) )),
% 6.30/1.21    inference(forward_demodulation,[],[f2782,f358])).
% 6.30/1.21  fof(f358,plain,(
% 6.30/1.21    ( ! [X1] : (k4_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,X1)) = k4_xboole_0(k1_xboole_0,X1)) )),
% 6.30/1.21    inference(superposition,[],[f58,f356])).
% 6.30/1.21  fof(f356,plain,(
% 6.30/1.21    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)),
% 6.30/1.21    inference(backward_demodulation,[],[f327,f328])).
% 6.30/1.21  fof(f327,plain,(
% 6.30/1.21    k4_xboole_0(sK1,sK1) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,sK1))),
% 6.30/1.21    inference(forward_demodulation,[],[f326,f41])).
% 6.30/1.21  fof(f326,plain,(
% 6.30/1.21    k4_xboole_0(sK1,sK1) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,k2_xboole_0(sK1,k1_xboole_0)))),
% 6.30/1.21    inference(forward_demodulation,[],[f324,f58])).
% 6.30/1.21  fof(f324,plain,(
% 6.30/1.21    k4_xboole_0(sK1,sK1) = k4_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(k4_xboole_0(sK1,sK1),k1_xboole_0))),
% 6.30/1.21    inference(resolution,[],[f312,f63])).
% 6.30/1.21  fof(f2782,plain,(
% 6.30/1.21    ( ! [X7] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,X7)))) )),
% 6.30/1.21    inference(resolution,[],[f2761,f63])).
% 6.30/1.21  fof(f2761,plain,(
% 6.30/1.21    ( ! [X0] : (r1_tarski(k1_xboole_0,k2_xboole_0(k1_xboole_0,X0))) )),
% 6.30/1.21    inference(forward_demodulation,[],[f2732,f41])).
% 6.30/1.21  fof(f2732,plain,(
% 6.30/1.21    ( ! [X0] : (r1_tarski(k1_xboole_0,k2_xboole_0(k2_xboole_0(k1_xboole_0,X0),k1_xboole_0))) )),
% 6.30/1.21    inference(resolution,[],[f414,f46])).
% 6.30/1.21  fof(f414,plain,(
% 6.30/1.21    ( ! [X0,X1] : (~r1_tarski(k4_xboole_0(k1_xboole_0,X0),X1) | r1_tarski(k1_xboole_0,k2_xboole_0(k2_xboole_0(k1_xboole_0,X0),X1))) )),
% 6.30/1.21    inference(superposition,[],[f60,f358])).
% 6.30/1.21  fof(f529,plain,(
% 6.30/1.21    ( ! [X4] : (k4_xboole_0(X4,k4_xboole_0(X4,k2_xboole_0(k4_xboole_0(X4,k1_xboole_0),sK1))) = X4) )),
% 6.30/1.21    inference(resolution,[],[f492,f63])).
% 6.30/1.21  fof(f492,plain,(
% 6.30/1.21    ( ! [X0] : (r1_tarski(X0,k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),sK1))) )),
% 6.30/1.21    inference(resolution,[],[f455,f60])).
% 6.30/1.21  fof(f455,plain,(
% 6.30/1.21    ( ! [X2] : (r1_tarski(k4_xboole_0(X2,k4_xboole_0(X2,k1_xboole_0)),sK1)) )),
% 6.30/1.21    inference(superposition,[],[f426,f62])).
% 6.30/1.21  fof(f426,plain,(
% 6.30/1.21    ( ! [X7] : (r1_tarski(k4_xboole_0(k1_xboole_0,X7),sK1)) )),
% 6.30/1.21    inference(superposition,[],[f46,f362])).
% 6.30/1.21  fof(f3124,plain,(
% 6.30/1.21    ( ! [X6,X7] : (r1_tarski(X6,k2_xboole_0(k4_xboole_0(X6,k1_xboole_0),X7))) )),
% 6.30/1.21    inference(subsumption_resolution,[],[f3000,f2998])).
% 6.30/1.21  fof(f2998,plain,(
% 6.30/1.21    ( ! [X3] : (r1_tarski(k1_xboole_0,X3)) )),
% 6.30/1.21    inference(superposition,[],[f46,f2859])).
% 6.30/1.21  fof(f3000,plain,(
% 6.30/1.21    ( ! [X6,X7] : (~r1_tarski(k1_xboole_0,X7) | r1_tarski(X6,k2_xboole_0(k4_xboole_0(X6,k1_xboole_0),X7))) )),
% 6.30/1.21    inference(superposition,[],[f60,f2859])).
% 6.30/1.21  fof(f12263,plain,(
% 6.30/1.21    sK1 = k2_pre_topc(sK0,sK1) | ~r1_tarski(sK1,k2_pre_topc(sK0,sK1))),
% 6.30/1.21    inference(duplicate_literal_removal,[],[f12257])).
% 6.30/1.21  fof(f12257,plain,(
% 6.30/1.21    sK1 = k2_pre_topc(sK0,sK1) | ~r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | sK1 = k2_pre_topc(sK0,sK1)),
% 6.30/1.21    inference(resolution,[],[f9967,f55])).
% 6.30/1.21  fof(f55,plain,(
% 6.30/1.21    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 6.30/1.21    inference(cnf_transformation,[],[f2])).
% 6.30/1.21  fof(f9967,plain,(
% 6.30/1.21    r1_tarski(k2_pre_topc(sK0,sK1),sK1) | sK1 = k2_pre_topc(sK0,sK1)),
% 6.30/1.21    inference(forward_demodulation,[],[f9959,f553])).
% 6.30/1.21  fof(f9959,plain,(
% 6.30/1.21    r1_tarski(k2_xboole_0(sK1,k2_tops_1(sK0,sK1)),sK1) | sK1 = k2_pre_topc(sK0,sK1)),
% 6.30/1.21    inference(superposition,[],[f9825,f784])).
% 6.30/1.21  fof(f784,plain,(
% 6.30/1.21    sK1 = k2_xboole_0(k2_tops_1(sK0,sK1),sK1) | sK1 = k2_pre_topc(sK0,sK1)),
% 6.30/1.21    inference(resolution,[],[f467,f50])).
% 6.30/1.21  fof(f467,plain,(
% 6.30/1.21    r1_tarski(k2_tops_1(sK0,sK1),sK1) | sK1 = k2_pre_topc(sK0,sK1)),
% 6.30/1.21    inference(superposition,[],[f46,f106])).
% 6.30/1.21  fof(f106,plain,(
% 6.30/1.21    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | sK1 = k2_pre_topc(sK0,sK1)),
% 6.30/1.21    inference(subsumption_resolution,[],[f105,f38])).
% 6.30/1.21  fof(f105,plain,(
% 6.30/1.21    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = k2_pre_topc(sK0,sK1)),
% 6.30/1.21    inference(subsumption_resolution,[],[f104,f40])).
% 6.30/1.21  fof(f104,plain,(
% 6.30/1.21    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = k2_pre_topc(sK0,sK1)),
% 6.30/1.21    inference(resolution,[],[f86,f45])).
% 6.30/1.21  fof(f45,plain,(
% 6.30/1.21    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1) )),
% 6.30/1.21    inference(cnf_transformation,[],[f25])).
% 6.30/1.21  fof(f25,plain,(
% 6.30/1.21    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 6.30/1.21    inference(flattening,[],[f24])).
% 6.30/1.21  fof(f24,plain,(
% 6.30/1.21    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 6.30/1.21    inference(ennf_transformation,[],[f13])).
% 6.30/1.21  fof(f13,axiom,(
% 6.30/1.21    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 6.30/1.21    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).
% 6.30/1.21  fof(f86,plain,(
% 6.30/1.21    v4_pre_topc(sK1,sK0) | k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))),
% 6.30/1.21    inference(backward_demodulation,[],[f36,f84])).
% 6.30/1.21  fof(f36,plain,(
% 6.30/1.21    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)),
% 6.30/1.21    inference(cnf_transformation,[],[f21])).
% 6.30/1.21  fof(f9825,plain,(
% 6.30/1.21    ( ! [X0] : (r1_tarski(k2_xboole_0(sK1,X0),k2_xboole_0(X0,sK1))) )),
% 6.30/1.21    inference(superposition,[],[f5717,f9677])).
% 6.30/1.21  fof(f9677,plain,(
% 6.30/1.21    ( ! [X8,X9] : (k2_xboole_0(k4_xboole_0(k2_xboole_0(X8,X9),X8),X9) = X9) )),
% 6.30/1.21    inference(resolution,[],[f9643,f50])).
% 6.30/1.21  fof(f9643,plain,(
% 6.30/1.21    ( ! [X21,X20] : (r1_tarski(k4_xboole_0(k2_xboole_0(X20,X21),X20),X21)) )),
% 6.30/1.21    inference(forward_demodulation,[],[f9604,f41])).
% 6.30/1.21  fof(f9604,plain,(
% 6.30/1.21    ( ! [X21,X20] : (r1_tarski(k4_xboole_0(k2_xboole_0(X20,X21),X20),k2_xboole_0(X21,k1_xboole_0))) )),
% 6.30/1.21    inference(superposition,[],[f4471,f3069])).
% 6.30/1.21  fof(f3069,plain,(
% 6.30/1.21    ( ! [X3] : (k1_xboole_0 = k4_xboole_0(X3,X3)) )),
% 6.30/1.21    inference(backward_demodulation,[],[f2859,f3066])).
% 6.30/1.21  fof(f4471,plain,(
% 6.30/1.21    ( ! [X14,X15,X13] : (r1_tarski(k4_xboole_0(X13,X14),k2_xboole_0(X15,k4_xboole_0(X13,k2_xboole_0(X14,X15))))) )),
% 6.30/1.21    inference(superposition,[],[f4437,f58])).
% 6.30/1.21  fof(f4437,plain,(
% 6.30/1.21    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1)))) )),
% 6.30/1.21    inference(superposition,[],[f3414,f4299])).
% 6.30/1.21  fof(f4299,plain,(
% 6.30/1.21    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 6.30/1.21    inference(superposition,[],[f3410,f41])).
% 6.30/1.21  fof(f3410,plain,(
% 6.30/1.21    ( ! [X6,X7] : (k2_xboole_0(X6,X7) = k2_xboole_0(X6,k2_xboole_0(X6,X7))) )),
% 6.30/1.21    inference(resolution,[],[f3125,f50])).
% 6.30/1.21  fof(f3414,plain,(
% 6.30/1.21    ( ! [X14,X12,X13] : (r1_tarski(X12,k2_xboole_0(X13,k2_xboole_0(k4_xboole_0(X12,X13),X14)))) )),
% 6.30/1.21    inference(resolution,[],[f3125,f60])).
% 6.30/1.21  fof(f5717,plain,(
% 6.30/1.21    ( ! [X10,X9] : (r1_tarski(X9,k2_xboole_0(k2_xboole_0(k4_xboole_0(X9,sK1),X10),sK1))) )),
% 6.30/1.21    inference(superposition,[],[f3831,f3191])).
% 6.30/1.21  fof(f3191,plain,(
% 6.30/1.21    ( ! [X5] : (k2_xboole_0(X5,sK1) = k2_xboole_0(sK1,k2_xboole_0(X5,sK1))) )),
% 6.30/1.21    inference(backward_demodulation,[],[f2213,f3160])).
% 6.30/1.21  fof(f3160,plain,(
% 6.30/1.21    ( ! [X6] : (k2_xboole_0(k1_xboole_0,X6) = X6) )),
% 6.30/1.21    inference(resolution,[],[f2998,f50])).
% 6.30/1.21  fof(f2213,plain,(
% 6.30/1.21    ( ! [X5] : (k2_xboole_0(k2_xboole_0(k1_xboole_0,X5),sK1) = k2_xboole_0(sK1,k2_xboole_0(k2_xboole_0(k1_xboole_0,X5),sK1))) )),
% 6.30/1.21    inference(resolution,[],[f2156,f50])).
% 6.30/1.21  fof(f2156,plain,(
% 6.30/1.21    ( ! [X0] : (r1_tarski(sK1,k2_xboole_0(k2_xboole_0(k1_xboole_0,X0),sK1))) )),
% 6.30/1.21    inference(resolution,[],[f302,f46])).
% 6.30/1.21  fof(f302,plain,(
% 6.30/1.21    ( ! [X0,X1] : (~r1_tarski(k4_xboole_0(sK1,X0),X1) | r1_tarski(sK1,k2_xboole_0(k2_xboole_0(k1_xboole_0,X0),X1))) )),
% 6.30/1.21    inference(superposition,[],[f60,f192])).
% 6.30/1.21  fof(f192,plain,(
% 6.30/1.21    ( ! [X1] : (k4_xboole_0(sK1,X1) = k4_xboole_0(sK1,k2_xboole_0(k1_xboole_0,X1))) )),
% 6.30/1.21    inference(superposition,[],[f58,f189])).
% 6.30/1.21  fof(f3831,plain,(
% 6.30/1.21    ( ! [X21,X19,X22,X20] : (r1_tarski(X19,k2_xboole_0(X20,k2_xboole_0(k2_xboole_0(k4_xboole_0(X19,X20),X21),X22)))) )),
% 6.30/1.21    inference(resolution,[],[f3808,f60])).
% 6.30/1.21  fof(f3808,plain,(
% 6.30/1.21    ( ! [X6,X7,X5] : (r1_tarski(X5,k2_xboole_0(k2_xboole_0(X5,X6),X7))) )),
% 6.30/1.21    inference(subsumption_resolution,[],[f3769,f2998])).
% 6.30/1.21  fof(f3769,plain,(
% 6.30/1.21    ( ! [X6,X7,X5] : (~r1_tarski(k1_xboole_0,X7) | r1_tarski(X5,k2_xboole_0(k2_xboole_0(X5,X6),X7))) )),
% 6.30/1.21    inference(superposition,[],[f60,f3490])).
% 6.30/1.21  fof(f3490,plain,(
% 6.30/1.21    ( ! [X4,X5] : (k1_xboole_0 = k4_xboole_0(X4,k2_xboole_0(X4,X5))) )),
% 6.30/1.21    inference(backward_demodulation,[],[f3070,f3465])).
% 6.30/1.21  fof(f3465,plain,(
% 6.30/1.21    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 6.30/1.21    inference(resolution,[],[f3158,f46])).
% 6.30/1.21  fof(f3158,plain,(
% 6.30/1.21    ( ! [X4] : (~r1_tarski(X4,k1_xboole_0) | k1_xboole_0 = X4) )),
% 6.30/1.21    inference(resolution,[],[f2998,f55])).
% 6.30/1.21  fof(f3070,plain,(
% 6.30/1.21    ( ! [X4,X5] : (k4_xboole_0(k1_xboole_0,X5) = k4_xboole_0(X4,k2_xboole_0(X4,X5))) )),
% 6.30/1.21    inference(backward_demodulation,[],[f2999,f3066])).
% 6.30/1.21  fof(f100,plain,(
% 6.30/1.21    v4_pre_topc(k2_pre_topc(sK0,sK1),sK0)),
% 6.30/1.21    inference(resolution,[],[f68,f38])).
% 6.30/1.21  fof(f68,plain,(
% 6.30/1.21    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(k2_pre_topc(sK0,X0),sK0)) )),
% 6.30/1.21    inference(subsumption_resolution,[],[f66,f40])).
% 6.30/1.21  fof(f66,plain,(
% 6.30/1.21    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(k2_pre_topc(sK0,X0),sK0)) )),
% 6.30/1.21    inference(resolution,[],[f39,f51])).
% 6.30/1.21  fof(f51,plain,(
% 6.30/1.21    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v4_pre_topc(k2_pre_topc(X0,X1),X0)) )),
% 6.30/1.21    inference(cnf_transformation,[],[f29])).
% 6.30/1.21  fof(f29,plain,(
% 6.30/1.21    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 6.30/1.21    inference(flattening,[],[f28])).
% 6.30/1.21  fof(f28,plain,(
% 6.30/1.21    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 6.30/1.21    inference(ennf_transformation,[],[f15])).
% 6.30/1.21  fof(f15,axiom,(
% 6.30/1.21    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_pre_topc(X0,X1),X0))),
% 6.30/1.21    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).
% 6.30/1.21  fof(f39,plain,(
% 6.30/1.21    v2_pre_topc(sK0)),
% 6.30/1.21    inference(cnf_transformation,[],[f21])).
% 6.30/1.21  fof(f12553,plain,(
% 6.30/1.21    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))),
% 6.30/1.21    inference(superposition,[],[f12270,f84])).
% 6.30/1.21  fof(f12270,plain,(
% 6.30/1.21    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),
% 6.30/1.21    inference(backward_demodulation,[],[f621,f12264])).
% 6.30/1.21  fof(f621,plain,(
% 6.30/1.21    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),
% 6.30/1.21    inference(resolution,[],[f74,f38])).
% 6.30/1.21  fof(f74,plain,(
% 6.30/1.21    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | k2_tops_1(sK0,X3) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X3),k1_tops_1(sK0,X3))) )),
% 6.30/1.21    inference(resolution,[],[f40,f43])).
% 6.30/1.21  fof(f43,plain,(
% 6.30/1.21    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))) )),
% 6.30/1.21    inference(cnf_transformation,[],[f23])).
% 6.30/1.21  fof(f23,plain,(
% 6.30/1.21    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 6.30/1.21    inference(ennf_transformation,[],[f16])).
% 6.30/1.21  fof(f16,axiom,(
% 6.30/1.21    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 6.30/1.21    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).
% 6.30/1.21  % SZS output end Proof for theBenchmark
% 6.30/1.21  % (11167)------------------------------
% 6.30/1.21  % (11167)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.30/1.21  % (11167)Termination reason: Refutation
% 6.30/1.21  
% 6.30/1.21  % (11167)Memory used [KB]: 7036
% 6.30/1.21  % (11167)Time elapsed: 0.796 s
% 6.30/1.21  % (11167)------------------------------
% 6.30/1.21  % (11167)------------------------------
% 6.30/1.21  % (11149)Success in time 0.86 s
%------------------------------------------------------------------------------
