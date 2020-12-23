%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:48 EST 2020

% Result     : Theorem 6.19s
% Output     : Refutation 6.42s
% Verified   : 
% Statistics : Number of formulae       :  143 (10721 expanded)
%              Number of leaves         :   19 (3066 expanded)
%              Depth                    :   33
%              Number of atoms          :  266 (17565 expanded)
%              Number of equality atoms :   77 (6798 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9097,plain,(
    $false ),
    inference(subsumption_resolution,[],[f9096,f9088])).

fof(f9088,plain,(
    ~ v3_pre_topc(k5_xboole_0(k2_struct_0(sK0),sK1),sK0) ),
    inference(subsumption_resolution,[],[f9087,f8067])).

fof(f8067,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | ~ v3_pre_topc(k5_xboole_0(k2_struct_0(sK0),sK1),sK0) ),
    inference(backward_demodulation,[],[f92,f8050])).

fof(f8050,plain,(
    k3_subset_1(k2_struct_0(sK0),sK1) = k5_xboole_0(k2_struct_0(sK0),sK1) ),
    inference(backward_demodulation,[],[f177,f8049])).

fof(f8049,plain,(
    sK1 = k9_subset_1(sK1,sK1,k2_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f7953,f8048])).

fof(f8048,plain,(
    sK1 = k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f7991,f3486])).

fof(f3486,plain,(
    ! [X0,X1] : r1_tarski(k9_subset_1(X0,X0,X1),X0) ),
    inference(superposition,[],[f3476,f220])).

fof(f220,plain,(
    ! [X4,X5] : k9_subset_1(X4,X4,X5) = k1_setfam_1(k2_tarski(X4,X5)) ),
    inference(superposition,[],[f179,f138])).

fof(f138,plain,(
    ! [X0,X1] : k9_subset_1(X0,X1,X0) = k9_subset_1(X0,X0,X1) ),
    inference(resolution,[],[f64,f88])).

fof(f88,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f44,f41])).

fof(f41,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

% (8785)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
fof(f44,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

fof(f179,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X1,X0)) = k9_subset_1(X1,X0,X1) ),
    inference(superposition,[],[f153,f49])).

fof(f49,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f153,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X1,X0)) = k9_subset_1(X0,X1,X0) ),
    inference(resolution,[],[f76,f88])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) ) ),
    inference(definition_unfolding,[],[f63,f50])).

fof(f50,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f3476,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
    inference(duplicate_literal_removal,[],[f3442])).

fof(f3442,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)
      | r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ) ),
    inference(resolution,[],[f1187,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f1187,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(k1_setfam_1(k2_tarski(X0,X1)),X2),X0)
      | r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X2) ) ),
    inference(resolution,[],[f1175,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f1175,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k1_setfam_1(k2_tarski(X0,X1)))
      | r2_hidden(X2,X0) ) ),
    inference(superposition,[],[f87,f74])).

fof(f74,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))))) ),
    inference(definition_unfolding,[],[f51,f50,f72,f72])).

fof(f72,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f52,f50])).

fof(f52,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f51,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f87,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))
      | r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) != X2 ) ),
    inference(definition_unfolding,[],[f69,f72])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f7991,plain,
    ( ~ r1_tarski(k9_subset_1(sK1,sK1,k2_struct_0(sK0)),sK1)
    | sK1 = k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1)) ),
    inference(backward_demodulation,[],[f6210,f7953])).

fof(f6210,plain,
    ( ~ r1_tarski(k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1)),sK1)
    | sK1 = k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f6205,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f6205,plain,(
    r1_tarski(sK1,k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1))) ),
    inference(duplicate_literal_removal,[],[f6199])).

fof(f6199,plain,
    ( r1_tarski(sK1,k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1)))
    | r1_tarski(sK1,k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1))) ),
    inference(resolution,[],[f6195,f62])).

fof(f6195,plain,(
    ! [X0] :
      ( r2_hidden(sK2(sK1,X0),k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1)))
      | r1_tarski(sK1,X0) ) ),
    inference(forward_demodulation,[],[f6194,f5850])).

fof(f5850,plain,(
    k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1)) = k5_xboole_0(k2_struct_0(sK0),k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1)) ),
    inference(forward_demodulation,[],[f5839,f4240])).

fof(f4240,plain,(
    k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) = k1_setfam_1(k2_tarski(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1))) ),
    inference(superposition,[],[f4155,f220])).

fof(f4155,plain,(
    k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) = k9_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f3321,f88])).

fof(f3321,plain,(
    ! [X7] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(k2_struct_0(sK0)))
      | k7_subset_1(k2_struct_0(sK0),X7,sK1) = k9_subset_1(k2_struct_0(sK0),X7,k3_subset_1(k2_struct_0(sK0),sK1)) ) ),
    inference(resolution,[],[f56,f93])).

fof(f93,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f39,f90])).

fof(f90,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f45,f89])).

fof(f89,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f46,f40])).

fof(f40,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).

fof(f46,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f45,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f39,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f24])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).

fof(f5839,plain,(
    k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1)) = k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k2_tarski(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1)))) ),
    inference(resolution,[],[f171,f93])).

fof(f171,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(X2))
      | k3_subset_1(X2,k3_subset_1(X2,X3)) = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,k3_subset_1(X2,X3)))) ) ),
    inference(resolution,[],[f75,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ) ),
    inference(definition_unfolding,[],[f54,f72])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f6194,plain,(
    ! [X0] :
      ( r2_hidden(sK2(sK1,X0),k5_xboole_0(k2_struct_0(sK0),k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1)))
      | r1_tarski(sK1,X0) ) ),
    inference(subsumption_resolution,[],[f6181,f3403])).

fof(f3403,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2(sK1,X0),k3_subset_1(k2_struct_0(sK0),sK1))
      | r1_tarski(sK1,X0) ) ),
    inference(superposition,[],[f3308,f177])).

fof(f3308,plain,(
    ! [X10,X11,X9] :
      ( ~ r2_hidden(sK2(X10,X11),k5_xboole_0(X9,k9_subset_1(X10,X10,X9)))
      | r1_tarski(X10,X11) ) ),
    inference(superposition,[],[f104,f181])).

fof(f181,plain,(
    ! [X2,X3] : k1_setfam_1(k2_tarski(X3,X2)) = k9_subset_1(X2,X2,X3) ),
    inference(superposition,[],[f153,f138])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X0))))
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f86,f61])).

fof(f86,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) ) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) != X2 ) ),
    inference(definition_unfolding,[],[f70,f72])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f6181,plain,(
    ! [X0] :
      ( r2_hidden(sK2(sK1,X0),k5_xboole_0(k2_struct_0(sK0),k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1)))
      | r2_hidden(sK2(sK1,X0),k3_subset_1(k2_struct_0(sK0),sK1))
      | r1_tarski(sK1,X0) ) ),
    inference(superposition,[],[f541,f4240])).

fof(f541,plain,(
    ! [X4,X3] :
      ( r2_hidden(sK2(sK1,X3),k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k2_tarski(k2_struct_0(sK0),X4))))
      | r2_hidden(sK2(sK1,X3),X4)
      | r1_tarski(sK1,X3) ) ),
    inference(resolution,[],[f85,f119])).

fof(f119,plain,(
    ! [X7] :
      ( r2_hidden(sK2(sK1,X7),k2_struct_0(sK0))
      | r1_tarski(sK1,X7) ) ),
    inference(resolution,[],[f102,f93])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r2_hidden(sK2(X0,X2),X1)
      | r1_tarski(X0,X2) ) ),
    inference(resolution,[],[f55,f61])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f85,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) ) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) != X2 ) ),
    inference(definition_unfolding,[],[f71,f72])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f7953,plain,(
    k9_subset_1(sK1,sK1,k2_struct_0(sK0)) = k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1)) ),
    inference(backward_demodulation,[],[f5850,f7952])).

fof(f7952,plain,(
    k9_subset_1(sK1,sK1,k2_struct_0(sK0)) = k5_xboole_0(k2_struct_0(sK0),k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1)) ),
    inference(forward_demodulation,[],[f7951,f4240])).

fof(f7951,plain,(
    k9_subset_1(sK1,sK1,k2_struct_0(sK0)) = k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k2_tarski(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1)))) ),
    inference(forward_demodulation,[],[f7950,f219])).

fof(f219,plain,(
    ! [X2,X3] : k1_setfam_1(k2_tarski(X2,X3)) = k1_setfam_1(k2_tarski(X3,X2)) ),
    inference(superposition,[],[f179,f153])).

fof(f7950,plain,(
    k9_subset_1(sK1,sK1,k2_struct_0(sK0)) = k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k2_tarski(k3_subset_1(k2_struct_0(sK0),sK1),k2_struct_0(sK0)))) ),
    inference(forward_demodulation,[],[f7927,f181])).

fof(f7927,plain,(
    k9_subset_1(sK1,sK1,k2_struct_0(sK0)) = k5_xboole_0(k2_struct_0(sK0),k9_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1))) ),
    inference(superposition,[],[f7401,f177])).

fof(f7401,plain,(
    ! [X8,X7] : k9_subset_1(X8,X8,X7) = k5_xboole_0(X7,k9_subset_1(X7,X7,k5_xboole_0(X7,k9_subset_1(X8,X8,X7)))) ),
    inference(superposition,[],[f1171,f181])).

fof(f1171,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k5_xboole_0(X0,k9_subset_1(X0,X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))) ),
    inference(superposition,[],[f74,f220])).

fof(f177,plain,(
    k3_subset_1(k2_struct_0(sK0),sK1) = k5_xboole_0(k2_struct_0(sK0),k9_subset_1(sK1,sK1,k2_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f176,f138])).

fof(f176,plain,(
    k3_subset_1(k2_struct_0(sK0),sK1) = k5_xboole_0(k2_struct_0(sK0),k9_subset_1(sK1,k2_struct_0(sK0),sK1)) ),
    inference(forward_demodulation,[],[f172,f153])).

fof(f172,plain,(
    k3_subset_1(k2_struct_0(sK0),sK1) = k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k2_tarski(k2_struct_0(sK0),sK1))) ),
    inference(resolution,[],[f75,f93])).

fof(f92,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | ~ v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0) ),
    inference(backward_demodulation,[],[f38,f90])).

fof(f38,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f9087,plain,
    ( ~ v3_pre_topc(k5_xboole_0(k2_struct_0(sK0),sK1),sK0)
    | v4_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f9086,f93])).

fof(f9086,plain,
    ( ~ v3_pre_topc(k5_xboole_0(k2_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | v4_pre_topc(sK1,sK0) ),
    inference(superposition,[],[f2167,f8307])).

fof(f8307,plain,(
    k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) = k5_xboole_0(k2_struct_0(sK0),sK1) ),
    inference(forward_demodulation,[],[f8306,f8049])).

fof(f8306,plain,(
    k5_xboole_0(k2_struct_0(sK0),k9_subset_1(sK1,sK1,k2_struct_0(sK0))) = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) ),
    inference(forward_demodulation,[],[f8305,f138])).

fof(f8305,plain,(
    k5_xboole_0(k2_struct_0(sK0),k9_subset_1(sK1,k2_struct_0(sK0),sK1)) = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) ),
    inference(forward_demodulation,[],[f8304,f153])).

fof(f8304,plain,(
    k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k2_tarski(k2_struct_0(sK0),sK1))) = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) ),
    inference(forward_demodulation,[],[f8010,f8049])).

fof(f8010,plain,(
    k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) = k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k2_tarski(k2_struct_0(sK0),k9_subset_1(sK1,sK1,k2_struct_0(sK0))))) ),
    inference(backward_demodulation,[],[f6501,f7953])).

fof(f6501,plain,(
    k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) = k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k2_tarski(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1))))) ),
    inference(backward_demodulation,[],[f4298,f6500])).

fof(f6500,plain,(
    k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k2_tarski(k2_struct_0(sK0),k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1)))) = k1_setfam_1(k2_tarski(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1)))) ),
    inference(forward_demodulation,[],[f6434,f5850])).

fof(f6434,plain,(
    k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k2_tarski(k2_struct_0(sK0),k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1)))) = k1_setfam_1(k2_tarski(k2_struct_0(sK0),k5_xboole_0(k2_struct_0(sK0),k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1)))) ),
    inference(superposition,[],[f1170,f4240])).

fof(f1170,plain,(
    ! [X2,X1] : k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))))) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k1_setfam_1(k2_tarski(X1,X2))))) ),
    inference(superposition,[],[f74,f74])).

fof(f4298,plain,(
    k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) = k5_xboole_0(k2_struct_0(sK0),k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k2_tarski(k2_struct_0(sK0),k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1))))) ),
    inference(superposition,[],[f1182,f4240])).

fof(f1182,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_setfam_1(k2_tarski(X0,X1)))))) ),
    inference(backward_demodulation,[],[f74,f1170])).

fof(f2167,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),X0),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | v4_pre_topc(X0,sK0) ) ),
    inference(forward_demodulation,[],[f2166,f90])).

fof(f2166,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0),sK0)
      | v4_pre_topc(X0,sK0) ) ),
    inference(forward_demodulation,[],[f2165,f90])).

fof(f2165,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0),sK0)
      | v4_pre_topc(X0,sK0) ) ),
    inference(resolution,[],[f47,f40])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
      | v4_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_pre_topc)).

fof(f9096,plain,(
    v3_pre_topc(k5_xboole_0(k2_struct_0(sK0),sK1),sK0) ),
    inference(forward_demodulation,[],[f9095,f8307])).

fof(f9095,plain,(
    v3_pre_topc(k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1),sK0) ),
    inference(forward_demodulation,[],[f9094,f90])).

fof(f9094,plain,(
    v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0) ),
    inference(subsumption_resolution,[],[f9093,f93])).

fof(f9093,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0) ),
    inference(forward_demodulation,[],[f9092,f90])).

fof(f9092,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0) ),
    inference(subsumption_resolution,[],[f9091,f40])).

fof(f9091,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f9089,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f9089,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(resolution,[],[f9088,f8066])).

fof(f8066,plain,
    ( v3_pre_topc(k5_xboole_0(k2_struct_0(sK0),sK1),sK0)
    | v4_pre_topc(sK1,sK0) ),
    inference(backward_demodulation,[],[f91,f8050])).

fof(f91,plain,
    ( v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0)
    | v4_pre_topc(sK1,sK0) ),
    inference(backward_demodulation,[],[f37,f90])).

fof(f37,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:10:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.50  % (8754)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.50  % (8770)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.50  % (8749)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.50  % (8751)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (8752)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.51  % (8762)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.52  % (8769)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.52  % (8761)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.52  % (8757)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.52  % (8765)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.53  % (8748)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.53  % (8753)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.53  % (8774)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.53  % (8771)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.53  % (8750)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  % (8747)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.54  % (8775)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.54  % (8776)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.54  % (8767)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.48/0.54  % (8764)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.48/0.54  % (8766)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.48/0.54  % (8768)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.48/0.55  % (8764)Refutation not found, incomplete strategy% (8764)------------------------------
% 1.48/0.55  % (8764)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.55  % (8764)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.55  
% 1.48/0.55  % (8764)Memory used [KB]: 10618
% 1.48/0.55  % (8764)Time elapsed: 0.147 s
% 1.48/0.55  % (8764)------------------------------
% 1.48/0.55  % (8764)------------------------------
% 1.48/0.55  % (8772)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.48/0.55  % (8773)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.48/0.55  % (8759)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.48/0.55  % (8758)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.48/0.55  % (8760)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.48/0.55  % (8763)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.48/0.55  % (8755)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.48/0.55  % (8756)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 2.33/0.70  % (8777)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 3.18/0.82  % (8752)Time limit reached!
% 3.18/0.82  % (8752)------------------------------
% 3.18/0.82  % (8752)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.68/0.84  % (8752)Termination reason: Time limit
% 3.68/0.84  % (8752)Termination phase: Saturation
% 3.68/0.84  
% 3.68/0.84  % (8752)Memory used [KB]: 9978
% 3.68/0.84  % (8752)Time elapsed: 0.400 s
% 3.68/0.84  % (8752)------------------------------
% 3.68/0.84  % (8752)------------------------------
% 3.89/0.90  % (8748)Time limit reached!
% 3.89/0.90  % (8748)------------------------------
% 3.89/0.90  % (8748)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.89/0.90  % (8748)Termination reason: Time limit
% 3.89/0.90  % (8748)Termination phase: Saturation
% 3.89/0.90  
% 3.89/0.90  % (8748)Memory used [KB]: 7291
% 3.89/0.90  % (8748)Time elapsed: 0.500 s
% 3.89/0.90  % (8748)------------------------------
% 3.89/0.90  % (8748)------------------------------
% 3.89/0.91  % (8759)Time limit reached!
% 3.89/0.91  % (8759)------------------------------
% 3.89/0.91  % (8759)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.89/0.91  % (8759)Termination reason: Time limit
% 3.89/0.91  
% 3.89/0.91  % (8759)Memory used [KB]: 8571
% 3.89/0.91  % (8759)Time elapsed: 0.522 s
% 3.89/0.91  % (8759)------------------------------
% 3.89/0.91  % (8759)------------------------------
% 3.89/0.92  % (8757)Time limit reached!
% 3.89/0.92  % (8757)------------------------------
% 3.89/0.92  % (8757)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.89/0.92  % (8757)Termination reason: Time limit
% 3.89/0.92  
% 3.89/0.92  % (8757)Memory used [KB]: 12409
% 3.89/0.92  % (8757)Time elapsed: 0.518 s
% 3.89/0.92  % (8757)------------------------------
% 3.89/0.92  % (8757)------------------------------
% 4.42/0.94  % (8747)Time limit reached!
% 4.42/0.94  % (8747)------------------------------
% 4.42/0.94  % (8747)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.42/0.94  % (8747)Termination reason: Time limit
% 4.42/0.94  % (8747)Termination phase: Saturation
% 4.42/0.94  
% 4.42/0.94  % (8747)Memory used [KB]: 3582
% 4.42/0.94  % (8747)Time elapsed: 0.500 s
% 4.42/0.94  % (8747)------------------------------
% 4.42/0.94  % (8747)------------------------------
% 4.42/0.96  % (8778)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 4.64/1.00  % (8763)Time limit reached!
% 4.64/1.00  % (8763)------------------------------
% 4.64/1.00  % (8763)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.64/1.00  % (8763)Termination reason: Time limit
% 4.64/1.00  
% 4.64/1.00  % (8763)Memory used [KB]: 14967
% 4.64/1.00  % (8763)Time elapsed: 0.609 s
% 4.64/1.00  % (8763)------------------------------
% 4.64/1.00  % (8763)------------------------------
% 4.64/1.00  % (8754)Time limit reached!
% 4.64/1.00  % (8754)------------------------------
% 4.64/1.00  % (8754)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.64/1.01  % (8754)Termination reason: Time limit
% 4.64/1.01  % (8754)Termination phase: Saturation
% 4.64/1.01  
% 4.64/1.01  % (8754)Memory used [KB]: 9338
% 4.64/1.01  % (8754)Time elapsed: 0.600 s
% 4.64/1.01  % (8754)------------------------------
% 4.64/1.01  % (8754)------------------------------
% 4.64/1.03  % (8775)Time limit reached!
% 4.64/1.03  % (8775)------------------------------
% 4.64/1.03  % (8775)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.64/1.03  % (8775)Termination reason: Time limit
% 4.64/1.03  
% 4.64/1.03  % (8775)Memory used [KB]: 8955
% 4.64/1.03  % (8775)Time elapsed: 0.632 s
% 4.64/1.03  % (8775)------------------------------
% 4.64/1.03  % (8775)------------------------------
% 5.13/1.04  % (8780)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 5.13/1.05  % (8779)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 5.13/1.05  % (8781)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 5.13/1.07  % (8782)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 6.19/1.15  % (8784)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 6.19/1.15  % (8783)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 6.19/1.15  % (8753)Refutation found. Thanks to Tanya!
% 6.19/1.15  % SZS status Theorem for theBenchmark
% 6.19/1.15  % SZS output start Proof for theBenchmark
% 6.19/1.15  fof(f9097,plain,(
% 6.19/1.15    $false),
% 6.19/1.15    inference(subsumption_resolution,[],[f9096,f9088])).
% 6.19/1.15  fof(f9088,plain,(
% 6.19/1.15    ~v3_pre_topc(k5_xboole_0(k2_struct_0(sK0),sK1),sK0)),
% 6.19/1.15    inference(subsumption_resolution,[],[f9087,f8067])).
% 6.19/1.15  fof(f8067,plain,(
% 6.19/1.15    ~v4_pre_topc(sK1,sK0) | ~v3_pre_topc(k5_xboole_0(k2_struct_0(sK0),sK1),sK0)),
% 6.19/1.15    inference(backward_demodulation,[],[f92,f8050])).
% 6.19/1.15  fof(f8050,plain,(
% 6.19/1.15    k3_subset_1(k2_struct_0(sK0),sK1) = k5_xboole_0(k2_struct_0(sK0),sK1)),
% 6.19/1.15    inference(backward_demodulation,[],[f177,f8049])).
% 6.19/1.15  fof(f8049,plain,(
% 6.19/1.15    sK1 = k9_subset_1(sK1,sK1,k2_struct_0(sK0))),
% 6.19/1.15    inference(backward_demodulation,[],[f7953,f8048])).
% 6.19/1.15  fof(f8048,plain,(
% 6.19/1.15    sK1 = k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1))),
% 6.19/1.15    inference(subsumption_resolution,[],[f7991,f3486])).
% 6.19/1.15  fof(f3486,plain,(
% 6.19/1.15    ( ! [X0,X1] : (r1_tarski(k9_subset_1(X0,X0,X1),X0)) )),
% 6.19/1.15    inference(superposition,[],[f3476,f220])).
% 6.19/1.15  fof(f220,plain,(
% 6.19/1.15    ( ! [X4,X5] : (k9_subset_1(X4,X4,X5) = k1_setfam_1(k2_tarski(X4,X5))) )),
% 6.19/1.15    inference(superposition,[],[f179,f138])).
% 6.19/1.15  fof(f138,plain,(
% 6.19/1.15    ( ! [X0,X1] : (k9_subset_1(X0,X1,X0) = k9_subset_1(X0,X0,X1)) )),
% 6.19/1.15    inference(resolution,[],[f64,f88])).
% 6.19/1.15  fof(f88,plain,(
% 6.19/1.15    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 6.19/1.15    inference(forward_demodulation,[],[f44,f41])).
% 6.19/1.15  fof(f41,plain,(
% 6.19/1.15    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 6.19/1.15    inference(cnf_transformation,[],[f9])).
% 6.19/1.15  fof(f9,axiom,(
% 6.19/1.15    ! [X0] : k2_subset_1(X0) = X0),
% 6.19/1.15    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 6.19/1.17  % (8785)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 6.42/1.18  fof(f44,plain,(
% 6.42/1.18    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 6.42/1.18    inference(cnf_transformation,[],[f11])).
% 6.42/1.18  fof(f11,axiom,(
% 6.42/1.18    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 6.42/1.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 6.42/1.18  fof(f64,plain,(
% 6.42/1.18    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)) )),
% 6.42/1.18    inference(cnf_transformation,[],[f34])).
% 6.42/1.18  fof(f34,plain,(
% 6.42/1.18    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 6.42/1.18    inference(ennf_transformation,[],[f8])).
% 6.42/1.18  fof(f8,axiom,(
% 6.42/1.18    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1))),
% 6.42/1.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).
% 6.42/1.18  fof(f179,plain,(
% 6.42/1.18    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X1,X0)) = k9_subset_1(X1,X0,X1)) )),
% 6.42/1.18    inference(superposition,[],[f153,f49])).
% 6.42/1.18  fof(f49,plain,(
% 6.42/1.18    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 6.42/1.18    inference(cnf_transformation,[],[f7])).
% 6.42/1.18  fof(f7,axiom,(
% 6.42/1.18    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 6.42/1.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 6.42/1.18  fof(f153,plain,(
% 6.42/1.18    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X1,X0)) = k9_subset_1(X0,X1,X0)) )),
% 6.42/1.18    inference(resolution,[],[f76,f88])).
% 6.42/1.18  fof(f76,plain,(
% 6.42/1.18    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))) )),
% 6.42/1.18    inference(definition_unfolding,[],[f63,f50])).
% 6.42/1.18  fof(f50,plain,(
% 6.42/1.18    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 6.42/1.18    inference(cnf_transformation,[],[f17])).
% 6.42/1.18  fof(f17,axiom,(
% 6.42/1.18    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 6.42/1.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 6.42/1.18  fof(f63,plain,(
% 6.42/1.18    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) )),
% 6.42/1.18    inference(cnf_transformation,[],[f33])).
% 6.42/1.18  fof(f33,plain,(
% 6.42/1.18    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 6.42/1.18    inference(ennf_transformation,[],[f14])).
% 6.42/1.18  fof(f14,axiom,(
% 6.42/1.18    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 6.42/1.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 6.42/1.18  fof(f3476,plain,(
% 6.42/1.18    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)) )),
% 6.42/1.18    inference(duplicate_literal_removal,[],[f3442])).
% 6.42/1.18  fof(f3442,plain,(
% 6.42/1.18    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) | r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)) )),
% 6.42/1.18    inference(resolution,[],[f1187,f62])).
% 6.42/1.18  fof(f62,plain,(
% 6.42/1.18    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 6.42/1.18    inference(cnf_transformation,[],[f32])).
% 6.42/1.18  fof(f32,plain,(
% 6.42/1.18    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 6.42/1.18    inference(ennf_transformation,[],[f1])).
% 6.42/1.18  fof(f1,axiom,(
% 6.42/1.18    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 6.42/1.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 6.42/1.18  fof(f1187,plain,(
% 6.42/1.18    ( ! [X2,X0,X1] : (r2_hidden(sK2(k1_setfam_1(k2_tarski(X0,X1)),X2),X0) | r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X2)) )),
% 6.42/1.18    inference(resolution,[],[f1175,f61])).
% 6.42/1.18  fof(f61,plain,(
% 6.42/1.18    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 6.42/1.18    inference(cnf_transformation,[],[f32])).
% 6.42/1.18  fof(f1175,plain,(
% 6.42/1.18    ( ! [X2,X0,X1] : (~r2_hidden(X2,k1_setfam_1(k2_tarski(X0,X1))) | r2_hidden(X2,X0)) )),
% 6.42/1.18    inference(superposition,[],[f87,f74])).
% 6.42/1.18  fof(f74,plain,(
% 6.42/1.18    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))))) )),
% 6.42/1.18    inference(definition_unfolding,[],[f51,f50,f72,f72])).
% 6.42/1.18  fof(f72,plain,(
% 6.42/1.18    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 6.42/1.18    inference(definition_unfolding,[],[f52,f50])).
% 6.42/1.18  fof(f52,plain,(
% 6.42/1.18    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 6.42/1.18    inference(cnf_transformation,[],[f4])).
% 6.42/1.18  fof(f4,axiom,(
% 6.42/1.18    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 6.42/1.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 6.42/1.18  fof(f51,plain,(
% 6.42/1.18    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 6.42/1.18    inference(cnf_transformation,[],[f6])).
% 6.42/1.18  fof(f6,axiom,(
% 6.42/1.18    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 6.42/1.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 6.42/1.18  fof(f87,plain,(
% 6.42/1.18    ( ! [X0,X3,X1] : (~r2_hidden(X3,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) | r2_hidden(X3,X0)) )),
% 6.42/1.18    inference(equality_resolution,[],[f79])).
% 6.42/1.18  fof(f79,plain,(
% 6.42/1.18    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) != X2) )),
% 6.42/1.18    inference(definition_unfolding,[],[f69,f72])).
% 6.42/1.18  fof(f69,plain,(
% 6.42/1.18    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 6.42/1.18    inference(cnf_transformation,[],[f2])).
% 6.42/1.18  fof(f2,axiom,(
% 6.42/1.18    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 6.42/1.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 6.42/1.18  fof(f7991,plain,(
% 6.42/1.18    ~r1_tarski(k9_subset_1(sK1,sK1,k2_struct_0(sK0)),sK1) | sK1 = k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1))),
% 6.42/1.18    inference(backward_demodulation,[],[f6210,f7953])).
% 6.42/1.18  fof(f6210,plain,(
% 6.42/1.18    ~r1_tarski(k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1)),sK1) | sK1 = k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1))),
% 6.42/1.18    inference(resolution,[],[f6205,f59])).
% 6.42/1.18  fof(f59,plain,(
% 6.42/1.18    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 6.42/1.18    inference(cnf_transformation,[],[f3])).
% 6.42/1.18  fof(f3,axiom,(
% 6.42/1.18    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 6.42/1.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 6.42/1.18  fof(f6205,plain,(
% 6.42/1.18    r1_tarski(sK1,k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1)))),
% 6.42/1.18    inference(duplicate_literal_removal,[],[f6199])).
% 6.42/1.18  fof(f6199,plain,(
% 6.42/1.18    r1_tarski(sK1,k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1))) | r1_tarski(sK1,k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1)))),
% 6.42/1.18    inference(resolution,[],[f6195,f62])).
% 6.42/1.18  fof(f6195,plain,(
% 6.42/1.18    ( ! [X0] : (r2_hidden(sK2(sK1,X0),k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1))) | r1_tarski(sK1,X0)) )),
% 6.42/1.18    inference(forward_demodulation,[],[f6194,f5850])).
% 6.42/1.18  fof(f5850,plain,(
% 6.42/1.18    k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1)) = k5_xboole_0(k2_struct_0(sK0),k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1))),
% 6.42/1.18    inference(forward_demodulation,[],[f5839,f4240])).
% 6.42/1.18  fof(f4240,plain,(
% 6.42/1.18    k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) = k1_setfam_1(k2_tarski(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1)))),
% 6.42/1.18    inference(superposition,[],[f4155,f220])).
% 6.42/1.18  fof(f4155,plain,(
% 6.42/1.18    k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) = k9_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1))),
% 6.42/1.18    inference(resolution,[],[f3321,f88])).
% 6.42/1.18  fof(f3321,plain,(
% 6.42/1.18    ( ! [X7] : (~m1_subset_1(X7,k1_zfmisc_1(k2_struct_0(sK0))) | k7_subset_1(k2_struct_0(sK0),X7,sK1) = k9_subset_1(k2_struct_0(sK0),X7,k3_subset_1(k2_struct_0(sK0),sK1))) )),
% 6.42/1.18    inference(resolution,[],[f56,f93])).
% 6.42/1.18  fof(f93,plain,(
% 6.42/1.18    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 6.42/1.18    inference(backward_demodulation,[],[f39,f90])).
% 6.42/1.18  fof(f90,plain,(
% 6.42/1.18    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 6.42/1.18    inference(resolution,[],[f45,f89])).
% 6.42/1.18  fof(f89,plain,(
% 6.42/1.18    l1_struct_0(sK0)),
% 6.42/1.18    inference(resolution,[],[f46,f40])).
% 6.42/1.18  fof(f40,plain,(
% 6.42/1.18    l1_pre_topc(sK0)),
% 6.42/1.18    inference(cnf_transformation,[],[f24])).
% 6.42/1.18  fof(f24,plain,(
% 6.42/1.18    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 6.42/1.18    inference(ennf_transformation,[],[f23])).
% 6.42/1.18  fof(f23,negated_conjecture,(
% 6.42/1.18    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 6.42/1.18    inference(negated_conjecture,[],[f22])).
% 6.42/1.18  fof(f22,conjecture,(
% 6.42/1.18    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 6.42/1.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).
% 6.42/1.18  fof(f46,plain,(
% 6.42/1.18    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 6.42/1.18    inference(cnf_transformation,[],[f26])).
% 6.42/1.18  fof(f26,plain,(
% 6.42/1.18    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 6.42/1.18    inference(ennf_transformation,[],[f21])).
% 6.42/1.18  fof(f21,axiom,(
% 6.42/1.18    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 6.42/1.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 6.42/1.18  fof(f45,plain,(
% 6.42/1.18    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 6.42/1.18    inference(cnf_transformation,[],[f25])).
% 6.42/1.18  fof(f25,plain,(
% 6.42/1.18    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 6.42/1.18    inference(ennf_transformation,[],[f19])).
% 6.42/1.18  fof(f19,axiom,(
% 6.42/1.18    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 6.42/1.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 6.42/1.18  fof(f39,plain,(
% 6.42/1.18    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 6.42/1.18    inference(cnf_transformation,[],[f24])).
% 6.42/1.18  fof(f56,plain,(
% 6.42/1.18    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))) )),
% 6.42/1.18    inference(cnf_transformation,[],[f31])).
% 6.42/1.18  fof(f31,plain,(
% 6.42/1.18    ! [X0,X1] : (! [X2] : (k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 6.42/1.18    inference(ennf_transformation,[],[f15])).
% 6.42/1.18  fof(f15,axiom,(
% 6.42/1.18    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))))),
% 6.42/1.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).
% 6.42/1.18  fof(f5839,plain,(
% 6.42/1.18    k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1)) = k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k2_tarski(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1))))),
% 6.42/1.18    inference(resolution,[],[f171,f93])).
% 6.42/1.18  fof(f171,plain,(
% 6.42/1.18    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(X2)) | k3_subset_1(X2,k3_subset_1(X2,X3)) = k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,k3_subset_1(X2,X3))))) )),
% 6.42/1.18    inference(resolution,[],[f75,f53])).
% 6.42/1.18  fof(f53,plain,(
% 6.42/1.18    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 6.42/1.18    inference(cnf_transformation,[],[f28])).
% 6.42/1.18  fof(f28,plain,(
% 6.42/1.18    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 6.42/1.18    inference(ennf_transformation,[],[f12])).
% 6.42/1.18  fof(f12,axiom,(
% 6.42/1.18    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 6.42/1.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 6.42/1.18  fof(f75,plain,(
% 6.42/1.18    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 6.42/1.18    inference(definition_unfolding,[],[f54,f72])).
% 6.42/1.18  fof(f54,plain,(
% 6.42/1.18    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 6.42/1.18    inference(cnf_transformation,[],[f29])).
% 6.42/1.18  fof(f29,plain,(
% 6.42/1.18    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 6.42/1.18    inference(ennf_transformation,[],[f10])).
% 6.42/1.18  fof(f10,axiom,(
% 6.42/1.18    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 6.42/1.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 6.42/1.18  fof(f6194,plain,(
% 6.42/1.18    ( ! [X0] : (r2_hidden(sK2(sK1,X0),k5_xboole_0(k2_struct_0(sK0),k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1))) | r1_tarski(sK1,X0)) )),
% 6.42/1.18    inference(subsumption_resolution,[],[f6181,f3403])).
% 6.42/1.18  fof(f3403,plain,(
% 6.42/1.18    ( ! [X0] : (~r2_hidden(sK2(sK1,X0),k3_subset_1(k2_struct_0(sK0),sK1)) | r1_tarski(sK1,X0)) )),
% 6.42/1.18    inference(superposition,[],[f3308,f177])).
% 6.42/1.18  fof(f3308,plain,(
% 6.42/1.18    ( ! [X10,X11,X9] : (~r2_hidden(sK2(X10,X11),k5_xboole_0(X9,k9_subset_1(X10,X10,X9))) | r1_tarski(X10,X11)) )),
% 6.42/1.18    inference(superposition,[],[f104,f181])).
% 6.42/1.18  fof(f181,plain,(
% 6.42/1.18    ( ! [X2,X3] : (k1_setfam_1(k2_tarski(X3,X2)) = k9_subset_1(X2,X2,X3)) )),
% 6.42/1.18    inference(superposition,[],[f153,f138])).
% 6.42/1.18  fof(f104,plain,(
% 6.42/1.18    ( ! [X2,X0,X1] : (~r2_hidden(sK2(X0,X1),k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X0)))) | r1_tarski(X0,X1)) )),
% 6.42/1.18    inference(resolution,[],[f86,f61])).
% 6.42/1.18  fof(f86,plain,(
% 6.42/1.18    ( ! [X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))) )),
% 6.42/1.18    inference(equality_resolution,[],[f78])).
% 6.42/1.18  fof(f78,plain,(
% 6.42/1.18    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) != X2) )),
% 6.42/1.18    inference(definition_unfolding,[],[f70,f72])).
% 6.42/1.18  fof(f70,plain,(
% 6.42/1.18    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 6.42/1.18    inference(cnf_transformation,[],[f2])).
% 6.42/1.18  fof(f6181,plain,(
% 6.42/1.18    ( ! [X0] : (r2_hidden(sK2(sK1,X0),k5_xboole_0(k2_struct_0(sK0),k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1))) | r2_hidden(sK2(sK1,X0),k3_subset_1(k2_struct_0(sK0),sK1)) | r1_tarski(sK1,X0)) )),
% 6.42/1.18    inference(superposition,[],[f541,f4240])).
% 6.42/1.18  fof(f541,plain,(
% 6.42/1.18    ( ! [X4,X3] : (r2_hidden(sK2(sK1,X3),k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k2_tarski(k2_struct_0(sK0),X4)))) | r2_hidden(sK2(sK1,X3),X4) | r1_tarski(sK1,X3)) )),
% 6.42/1.18    inference(resolution,[],[f85,f119])).
% 6.42/1.18  fof(f119,plain,(
% 6.42/1.18    ( ! [X7] : (r2_hidden(sK2(sK1,X7),k2_struct_0(sK0)) | r1_tarski(sK1,X7)) )),
% 6.42/1.18    inference(resolution,[],[f102,f93])).
% 6.42/1.18  fof(f102,plain,(
% 6.42/1.18    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r2_hidden(sK2(X0,X2),X1) | r1_tarski(X0,X2)) )),
% 6.42/1.18    inference(resolution,[],[f55,f61])).
% 6.42/1.18  fof(f55,plain,(
% 6.42/1.18    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | r2_hidden(X2,X0)) )),
% 6.42/1.18    inference(cnf_transformation,[],[f30])).
% 6.42/1.18  fof(f30,plain,(
% 6.42/1.18    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 6.42/1.18    inference(ennf_transformation,[],[f13])).
% 6.42/1.18  fof(f13,axiom,(
% 6.42/1.18    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 6.42/1.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 6.42/1.18  fof(f85,plain,(
% 6.42/1.18    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))) )),
% 6.42/1.18    inference(equality_resolution,[],[f77])).
% 6.42/1.18  fof(f77,plain,(
% 6.42/1.18    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X2) | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) != X2) )),
% 6.42/1.18    inference(definition_unfolding,[],[f71,f72])).
% 6.42/1.18  fof(f71,plain,(
% 6.42/1.18    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 6.42/1.18    inference(cnf_transformation,[],[f2])).
% 6.42/1.18  fof(f7953,plain,(
% 6.42/1.18    k9_subset_1(sK1,sK1,k2_struct_0(sK0)) = k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1))),
% 6.42/1.18    inference(backward_demodulation,[],[f5850,f7952])).
% 6.42/1.18  fof(f7952,plain,(
% 6.42/1.18    k9_subset_1(sK1,sK1,k2_struct_0(sK0)) = k5_xboole_0(k2_struct_0(sK0),k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1))),
% 6.42/1.18    inference(forward_demodulation,[],[f7951,f4240])).
% 6.42/1.18  fof(f7951,plain,(
% 6.42/1.18    k9_subset_1(sK1,sK1,k2_struct_0(sK0)) = k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k2_tarski(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1))))),
% 6.42/1.18    inference(forward_demodulation,[],[f7950,f219])).
% 6.42/1.18  fof(f219,plain,(
% 6.42/1.18    ( ! [X2,X3] : (k1_setfam_1(k2_tarski(X2,X3)) = k1_setfam_1(k2_tarski(X3,X2))) )),
% 6.42/1.18    inference(superposition,[],[f179,f153])).
% 6.42/1.18  fof(f7950,plain,(
% 6.42/1.18    k9_subset_1(sK1,sK1,k2_struct_0(sK0)) = k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k2_tarski(k3_subset_1(k2_struct_0(sK0),sK1),k2_struct_0(sK0))))),
% 6.42/1.18    inference(forward_demodulation,[],[f7927,f181])).
% 6.42/1.18  fof(f7927,plain,(
% 6.42/1.18    k9_subset_1(sK1,sK1,k2_struct_0(sK0)) = k5_xboole_0(k2_struct_0(sK0),k9_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1)))),
% 6.42/1.18    inference(superposition,[],[f7401,f177])).
% 6.42/1.18  fof(f7401,plain,(
% 6.42/1.18    ( ! [X8,X7] : (k9_subset_1(X8,X8,X7) = k5_xboole_0(X7,k9_subset_1(X7,X7,k5_xboole_0(X7,k9_subset_1(X8,X8,X7))))) )),
% 6.42/1.18    inference(superposition,[],[f1171,f181])).
% 6.42/1.18  fof(f1171,plain,(
% 6.42/1.18    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k5_xboole_0(X0,k9_subset_1(X0,X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))))) )),
% 6.42/1.18    inference(superposition,[],[f74,f220])).
% 6.42/1.18  fof(f177,plain,(
% 6.42/1.18    k3_subset_1(k2_struct_0(sK0),sK1) = k5_xboole_0(k2_struct_0(sK0),k9_subset_1(sK1,sK1,k2_struct_0(sK0)))),
% 6.42/1.18    inference(forward_demodulation,[],[f176,f138])).
% 6.42/1.18  fof(f176,plain,(
% 6.42/1.18    k3_subset_1(k2_struct_0(sK0),sK1) = k5_xboole_0(k2_struct_0(sK0),k9_subset_1(sK1,k2_struct_0(sK0),sK1))),
% 6.42/1.18    inference(forward_demodulation,[],[f172,f153])).
% 6.42/1.18  fof(f172,plain,(
% 6.42/1.18    k3_subset_1(k2_struct_0(sK0),sK1) = k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k2_tarski(k2_struct_0(sK0),sK1)))),
% 6.42/1.18    inference(resolution,[],[f75,f93])).
% 6.42/1.18  fof(f92,plain,(
% 6.42/1.18    ~v4_pre_topc(sK1,sK0) | ~v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0)),
% 6.42/1.18    inference(backward_demodulation,[],[f38,f90])).
% 6.42/1.18  fof(f38,plain,(
% 6.42/1.18    ~v4_pre_topc(sK1,sK0) | ~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)),
% 6.42/1.18    inference(cnf_transformation,[],[f24])).
% 6.42/1.18  fof(f9087,plain,(
% 6.42/1.18    ~v3_pre_topc(k5_xboole_0(k2_struct_0(sK0),sK1),sK0) | v4_pre_topc(sK1,sK0)),
% 6.42/1.18    inference(subsumption_resolution,[],[f9086,f93])).
% 6.42/1.18  fof(f9086,plain,(
% 6.42/1.18    ~v3_pre_topc(k5_xboole_0(k2_struct_0(sK0),sK1),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | v4_pre_topc(sK1,sK0)),
% 6.42/1.18    inference(superposition,[],[f2167,f8307])).
% 6.42/1.18  fof(f8307,plain,(
% 6.42/1.18    k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) = k5_xboole_0(k2_struct_0(sK0),sK1)),
% 6.42/1.18    inference(forward_demodulation,[],[f8306,f8049])).
% 6.42/1.18  fof(f8306,plain,(
% 6.42/1.18    k5_xboole_0(k2_struct_0(sK0),k9_subset_1(sK1,sK1,k2_struct_0(sK0))) = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1)),
% 6.42/1.18    inference(forward_demodulation,[],[f8305,f138])).
% 6.42/1.18  fof(f8305,plain,(
% 6.42/1.18    k5_xboole_0(k2_struct_0(sK0),k9_subset_1(sK1,k2_struct_0(sK0),sK1)) = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1)),
% 6.42/1.18    inference(forward_demodulation,[],[f8304,f153])).
% 6.42/1.18  fof(f8304,plain,(
% 6.42/1.18    k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k2_tarski(k2_struct_0(sK0),sK1))) = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1)),
% 6.42/1.18    inference(forward_demodulation,[],[f8010,f8049])).
% 6.42/1.18  fof(f8010,plain,(
% 6.42/1.18    k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) = k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k2_tarski(k2_struct_0(sK0),k9_subset_1(sK1,sK1,k2_struct_0(sK0)))))),
% 6.42/1.18    inference(backward_demodulation,[],[f6501,f7953])).
% 6.42/1.18  fof(f6501,plain,(
% 6.42/1.18    k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) = k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k2_tarski(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1)))))),
% 6.42/1.18    inference(backward_demodulation,[],[f4298,f6500])).
% 6.42/1.18  fof(f6500,plain,(
% 6.42/1.18    k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k2_tarski(k2_struct_0(sK0),k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1)))) = k1_setfam_1(k2_tarski(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1))))),
% 6.42/1.18    inference(forward_demodulation,[],[f6434,f5850])).
% 6.42/1.18  fof(f6434,plain,(
% 6.42/1.18    k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k2_tarski(k2_struct_0(sK0),k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1)))) = k1_setfam_1(k2_tarski(k2_struct_0(sK0),k5_xboole_0(k2_struct_0(sK0),k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1))))),
% 6.42/1.18    inference(superposition,[],[f1170,f4240])).
% 6.42/1.18  fof(f1170,plain,(
% 6.42/1.18    ( ! [X2,X1] : (k1_setfam_1(k2_tarski(X1,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))))) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,k1_setfam_1(k2_tarski(X1,X2)))))) )),
% 6.42/1.18    inference(superposition,[],[f74,f74])).
% 6.42/1.18  fof(f4298,plain,(
% 6.42/1.18    k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) = k5_xboole_0(k2_struct_0(sK0),k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k2_tarski(k2_struct_0(sK0),k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1)))))),
% 6.42/1.18    inference(superposition,[],[f1182,f4240])).
% 6.42/1.18  fof(f1182,plain,(
% 6.42/1.18    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_setfam_1(k2_tarski(X0,X1))))))) )),
% 6.42/1.18    inference(backward_demodulation,[],[f74,f1170])).
% 6.42/1.18  fof(f2167,plain,(
% 6.42/1.18    ( ! [X0] : (~v3_pre_topc(k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v4_pre_topc(X0,sK0)) )),
% 6.42/1.18    inference(forward_demodulation,[],[f2166,f90])).
% 6.42/1.18  fof(f2166,plain,(
% 6.42/1.18    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0),sK0) | v4_pre_topc(X0,sK0)) )),
% 6.42/1.18    inference(forward_demodulation,[],[f2165,f90])).
% 6.42/1.18  fof(f2165,plain,(
% 6.42/1.18    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0),sK0) | v4_pre_topc(X0,sK0)) )),
% 6.42/1.18    inference(resolution,[],[f47,f40])).
% 6.42/1.18  fof(f47,plain,(
% 6.42/1.18    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) | v4_pre_topc(X1,X0)) )),
% 6.42/1.18    inference(cnf_transformation,[],[f27])).
% 6.42/1.18  fof(f27,plain,(
% 6.42/1.18    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 6.42/1.18    inference(ennf_transformation,[],[f20])).
% 6.42/1.18  fof(f20,axiom,(
% 6.42/1.18    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0))))),
% 6.42/1.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_pre_topc)).
% 6.42/1.18  fof(f9096,plain,(
% 6.42/1.18    v3_pre_topc(k5_xboole_0(k2_struct_0(sK0),sK1),sK0)),
% 6.42/1.18    inference(forward_demodulation,[],[f9095,f8307])).
% 6.42/1.18  fof(f9095,plain,(
% 6.42/1.18    v3_pre_topc(k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1),sK0)),
% 6.42/1.18    inference(forward_demodulation,[],[f9094,f90])).
% 6.42/1.18  fof(f9094,plain,(
% 6.42/1.18    v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0)),
% 6.42/1.18    inference(subsumption_resolution,[],[f9093,f93])).
% 6.42/1.18  fof(f9093,plain,(
% 6.42/1.18    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0)),
% 6.42/1.18    inference(forward_demodulation,[],[f9092,f90])).
% 6.42/1.18  fof(f9092,plain,(
% 6.42/1.18    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0)),
% 6.42/1.18    inference(subsumption_resolution,[],[f9091,f40])).
% 6.42/1.18  fof(f9091,plain,(
% 6.42/1.18    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0) | ~l1_pre_topc(sK0)),
% 6.42/1.18    inference(resolution,[],[f9089,f48])).
% 6.42/1.18  fof(f48,plain,(
% 6.42/1.18    ( ! [X0,X1] : (~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) | ~l1_pre_topc(X0)) )),
% 6.42/1.18    inference(cnf_transformation,[],[f27])).
% 6.42/1.18  fof(f9089,plain,(
% 6.42/1.18    v4_pre_topc(sK1,sK0)),
% 6.42/1.18    inference(resolution,[],[f9088,f8066])).
% 6.42/1.18  fof(f8066,plain,(
% 6.42/1.18    v3_pre_topc(k5_xboole_0(k2_struct_0(sK0),sK1),sK0) | v4_pre_topc(sK1,sK0)),
% 6.42/1.18    inference(backward_demodulation,[],[f91,f8050])).
% 6.42/1.18  fof(f91,plain,(
% 6.42/1.18    v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0) | v4_pre_topc(sK1,sK0)),
% 6.42/1.18    inference(backward_demodulation,[],[f37,f90])).
% 6.42/1.18  fof(f37,plain,(
% 6.42/1.18    v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | v4_pre_topc(sK1,sK0)),
% 6.42/1.18    inference(cnf_transformation,[],[f24])).
% 6.42/1.18  % SZS output end Proof for theBenchmark
% 6.42/1.18  % (8753)------------------------------
% 6.42/1.18  % (8753)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.42/1.18  % (8753)Termination reason: Refutation
% 6.42/1.18  
% 6.42/1.18  % (8753)Memory used [KB]: 11385
% 6.42/1.18  % (8753)Time elapsed: 0.726 s
% 6.42/1.18  % (8753)------------------------------
% 6.42/1.18  % (8753)------------------------------
% 6.42/1.18  % (8746)Success in time 0.821 s
%------------------------------------------------------------------------------
