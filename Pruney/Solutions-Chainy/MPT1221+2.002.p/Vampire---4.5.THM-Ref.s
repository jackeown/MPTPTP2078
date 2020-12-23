%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:49 EST 2020

% Result     : Theorem 3.31s
% Output     : Refutation 3.31s
% Verified   : 
% Statistics : Number of formulae       :  102 (1928 expanded)
%              Number of leaves         :   16 ( 513 expanded)
%              Depth                    :   29
%              Number of atoms          :  205 (4032 expanded)
%              Number of equality atoms :   54 (1143 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3815,plain,(
    $false ),
    inference(subsumption_resolution,[],[f3814,f3806])).

fof(f3806,plain,(
    ~ v3_pre_topc(k5_xboole_0(k2_struct_0(sK0),sK1),sK0) ),
    inference(subsumption_resolution,[],[f3805,f2506])).

fof(f2506,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | ~ v3_pre_topc(k5_xboole_0(k2_struct_0(sK0),sK1),sK0) ),
    inference(backward_demodulation,[],[f74,f2466])).

fof(f2466,plain,(
    k3_subset_1(k2_struct_0(sK0),sK1) = k5_xboole_0(k2_struct_0(sK0),sK1) ),
    inference(backward_demodulation,[],[f125,f2437])).

fof(f2437,plain,(
    sK1 = k9_subset_1(sK1,k2_struct_0(sK0),sK1) ),
    inference(superposition,[],[f2430,f103])).

fof(f103,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X1,X0)) = k9_subset_1(X1,X0,X1) ),
    inference(superposition,[],[f98,f38])).

fof(f38,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f98,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X1,X0)) = k9_subset_1(X0,X1,X0) ),
    inference(resolution,[],[f60,f70])).

fof(f70,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f33,f32])).

fof(f32,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f33,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) ) ),
    inference(definition_unfolding,[],[f50,f39])).

fof(f39,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f2430,plain,(
    sK1 = k1_setfam_1(k2_tarski(sK1,k2_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f2374,f38])).

fof(f2374,plain,(
    sK1 = k1_setfam_1(k2_tarski(k2_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f2080,f78])).

fof(f78,plain,(
    r1_tarski(sK1,k2_struct_0(sK0)) ),
    inference(resolution,[],[f49,f75])).

fof(f75,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f30,f72])).

fof(f72,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f34,f71])).

fof(f71,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f35,f31])).

fof(f31,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_1)).

fof(f35,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f34,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f30,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f2080,plain,(
    ! [X6,X7] :
      ( ~ r1_tarski(X7,X6)
      | k1_setfam_1(k2_tarski(X6,X7)) = X7 ) ),
    inference(duplicate_literal_removal,[],[f2075])).

fof(f2075,plain,(
    ! [X6,X7] :
      ( k1_setfam_1(k2_tarski(X6,X7)) = X7
      | k1_setfam_1(k2_tarski(X6,X7)) = X7
      | ~ r1_tarski(X7,X6) ) ),
    inference(resolution,[],[f1950,f878])).

fof(f878,plain,(
    ! [X4,X5,X3] :
      ( r2_hidden(sK3(X3,X4,X4),X5)
      | k1_setfam_1(k2_tarski(X3,X4)) = X4
      | ~ r1_tarski(X4,X5) ) ),
    inference(resolution,[],[f876,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f876,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1,X1),X1)
      | k1_setfam_1(k2_tarski(X0,X1)) = X1 ) ),
    inference(factoring,[],[f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | k1_setfam_1(k2_tarski(X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f53,f39])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f1950,plain,(
    ! [X10,X11] :
      ( ~ r2_hidden(sK3(X10,X11,X11),X10)
      | k1_setfam_1(k2_tarski(X10,X11)) = X11 ) ),
    inference(subsumption_resolution,[],[f1947,f64])).

fof(f1947,plain,(
    ! [X10,X11] :
      ( ~ r2_hidden(sK3(X10,X11,X11),X11)
      | ~ r2_hidden(sK3(X10,X11,X11),X10)
      | k1_setfam_1(k2_tarski(X10,X11)) = X11 ) ),
    inference(duplicate_literal_removal,[],[f1940])).

fof(f1940,plain,(
    ! [X10,X11] :
      ( ~ r2_hidden(sK3(X10,X11,X11),X11)
      | ~ r2_hidden(sK3(X10,X11,X11),X10)
      | k1_setfam_1(k2_tarski(X10,X11)) = X11
      | k1_setfam_1(k2_tarski(X10,X11)) = X11 ) ),
    inference(resolution,[],[f66,f876])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X2),X2)
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X0)
      | k1_setfam_1(k2_tarski(X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f51,f39])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X2),X0)
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f125,plain,(
    k3_subset_1(k2_struct_0(sK0),sK1) = k5_xboole_0(k2_struct_0(sK0),k9_subset_1(sK1,k2_struct_0(sK0),sK1)) ),
    inference(forward_demodulation,[],[f123,f98])).

fof(f123,plain,(
    k3_subset_1(k2_struct_0(sK0),sK1) = k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k2_tarski(k2_struct_0(sK0),sK1))) ),
    inference(resolution,[],[f59,f75])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ) ),
    inference(definition_unfolding,[],[f43,f57])).

fof(f57,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f40,f39])).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f74,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | ~ v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0) ),
    inference(backward_demodulation,[],[f29,f72])).

fof(f29,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f3805,plain,
    ( ~ v3_pre_topc(k5_xboole_0(k2_struct_0(sK0),sK1),sK0)
    | v4_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f3804,f75])).

fof(f3804,plain,
    ( ~ v3_pre_topc(k5_xboole_0(k2_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | v4_pre_topc(sK1,sK0) ),
    inference(superposition,[],[f319,f3799])).

fof(f3799,plain,(
    k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) = k5_xboole_0(k2_struct_0(sK0),sK1) ),
    inference(forward_demodulation,[],[f3793,f2644])).

fof(f2644,plain,(
    k5_xboole_0(k2_struct_0(sK0),sK1) = k1_setfam_1(k2_tarski(k2_struct_0(sK0),k5_xboole_0(k2_struct_0(sK0),sK1))) ),
    inference(resolution,[],[f2642,f2080])).

fof(f2642,plain,(
    r1_tarski(k5_xboole_0(k2_struct_0(sK0),sK1),k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f2640,f75])).

fof(f2640,plain,
    ( r1_tarski(k5_xboole_0(k2_struct_0(sK0),sK1),k2_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(superposition,[],[f88,f2466])).

fof(f88,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_subset_1(X1,X0),X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(resolution,[],[f42,f49])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f3793,plain,(
    k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) = k1_setfam_1(k2_tarski(k2_struct_0(sK0),k5_xboole_0(k2_struct_0(sK0),sK1))) ),
    inference(resolution,[],[f2650,f70])).

fof(f2650,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_struct_0(sK0)))
      | k7_subset_1(k2_struct_0(sK0),X5,sK1) = k1_setfam_1(k2_tarski(X5,k5_xboole_0(k2_struct_0(sK0),sK1))) ) ),
    inference(backward_demodulation,[],[f2507,f2646])).

fof(f2646,plain,(
    ! [X0] : k9_subset_1(k2_struct_0(sK0),X0,k5_xboole_0(k2_struct_0(sK0),sK1)) = k1_setfam_1(k2_tarski(X0,k5_xboole_0(k2_struct_0(sK0),sK1))) ),
    inference(resolution,[],[f2642,f99])).

fof(f99,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(X4,X2)
      | k1_setfam_1(k2_tarski(X3,X4)) = k9_subset_1(X2,X3,X4) ) ),
    inference(resolution,[],[f60,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f2507,plain,(
    ! [X5] :
      ( k7_subset_1(k2_struct_0(sK0),X5,sK1) = k9_subset_1(k2_struct_0(sK0),X5,k5_xboole_0(k2_struct_0(sK0),sK1))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(backward_demodulation,[],[f1797,f2466])).

fof(f1797,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_struct_0(sK0)))
      | k7_subset_1(k2_struct_0(sK0),X5,sK1) = k9_subset_1(k2_struct_0(sK0),X5,k3_subset_1(k2_struct_0(sK0),sK1)) ) ),
    inference(resolution,[],[f44,f75])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_subset_1)).

fof(f319,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),X0),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | v4_pre_topc(X0,sK0) ) ),
    inference(forward_demodulation,[],[f318,f72])).

fof(f318,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0),sK0)
      | v4_pre_topc(X0,sK0) ) ),
    inference(forward_demodulation,[],[f317,f72])).

fof(f317,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0),sK0)
      | v4_pre_topc(X0,sK0) ) ),
    inference(resolution,[],[f36,f31])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
      | v4_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_pre_topc)).

fof(f3814,plain,(
    v3_pre_topc(k5_xboole_0(k2_struct_0(sK0),sK1),sK0) ),
    inference(forward_demodulation,[],[f3813,f3799])).

fof(f3813,plain,(
    v3_pre_topc(k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1),sK0) ),
    inference(forward_demodulation,[],[f3812,f72])).

fof(f3812,plain,(
    v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0) ),
    inference(subsumption_resolution,[],[f3811,f75])).

fof(f3811,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0) ),
    inference(forward_demodulation,[],[f3810,f72])).

fof(f3810,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0) ),
    inference(subsumption_resolution,[],[f3809,f31])).

fof(f3809,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f3807,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f3807,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(resolution,[],[f3806,f2505])).

fof(f2505,plain,
    ( v3_pre_topc(k5_xboole_0(k2_struct_0(sK0),sK1),sK0)
    | v4_pre_topc(sK1,sK0) ),
    inference(backward_demodulation,[],[f73,f2466])).

fof(f73,plain,
    ( v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0)
    | v4_pre_topc(sK1,sK0) ),
    inference(backward_demodulation,[],[f28,f72])).

fof(f28,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:18:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.48  % (21078)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.19/0.49  % (21067)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.19/0.50  % (21059)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.19/0.51  % (21068)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.26/0.51  % (21060)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.26/0.52  % (21082)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.26/0.52  % (21076)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.26/0.52  % (21058)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.26/0.52  % (21054)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.26/0.52  % (21055)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.26/0.53  % (21057)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.26/0.53  % (21056)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.39/0.53  % (21062)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.39/0.53  % (21063)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.39/0.53  % (21065)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.39/0.53  % (21064)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.39/0.53  % (21061)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.39/0.53  % (21066)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.39/0.54  % (21079)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.39/0.54  % (21053)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.39/0.54  % (21074)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.39/0.54  % (21075)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.39/0.54  % (21080)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.39/0.54  % (21081)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.39/0.54  % (21074)Refutation not found, incomplete strategy% (21074)------------------------------
% 1.39/0.54  % (21074)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.54  % (21074)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.54  
% 1.39/0.54  % (21074)Memory used [KB]: 1791
% 1.39/0.54  % (21074)Time elapsed: 0.150 s
% 1.39/0.54  % (21074)------------------------------
% 1.39/0.54  % (21074)------------------------------
% 1.39/0.54  % (21075)Refutation not found, incomplete strategy% (21075)------------------------------
% 1.39/0.54  % (21075)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.54  % (21075)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.54  
% 1.39/0.54  % (21075)Memory used [KB]: 10746
% 1.39/0.54  % (21075)Time elapsed: 0.148 s
% 1.39/0.54  % (21075)------------------------------
% 1.39/0.54  % (21075)------------------------------
% 1.39/0.54  % (21070)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.39/0.54  % (21071)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.39/0.54  % (21072)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.39/0.54  % (21073)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.39/0.55  % (21069)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.39/0.55  % (21077)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.39/0.55  % (21073)Refutation not found, incomplete strategy% (21073)------------------------------
% 1.39/0.55  % (21073)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.56  % (21070)Refutation not found, incomplete strategy% (21070)------------------------------
% 1.39/0.56  % (21070)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.56  % (21070)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.56  
% 1.39/0.56  % (21070)Memory used [KB]: 10618
% 1.39/0.56  % (21070)Time elapsed: 0.170 s
% 1.39/0.56  % (21070)------------------------------
% 1.39/0.56  % (21070)------------------------------
% 1.39/0.56  % (21073)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.56  
% 1.39/0.56  % (21073)Memory used [KB]: 10746
% 1.39/0.56  % (21073)Time elapsed: 0.162 s
% 1.39/0.56  % (21073)------------------------------
% 1.39/0.56  % (21073)------------------------------
% 2.11/0.68  % (21135)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.11/0.68  % (21136)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.11/0.68  % (21137)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.56/0.70  % (21138)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 3.07/0.80  % (21058)Time limit reached!
% 3.07/0.80  % (21058)------------------------------
% 3.07/0.80  % (21058)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.31/0.80  % (21058)Termination reason: Time limit
% 3.31/0.80  
% 3.31/0.80  % (21058)Memory used [KB]: 8827
% 3.31/0.80  % (21058)Time elapsed: 0.407 s
% 3.31/0.80  % (21058)------------------------------
% 3.31/0.80  % (21058)------------------------------
% 3.31/0.81  % (21059)Refutation found. Thanks to Tanya!
% 3.31/0.81  % SZS status Theorem for theBenchmark
% 3.31/0.81  % SZS output start Proof for theBenchmark
% 3.31/0.81  fof(f3815,plain,(
% 3.31/0.81    $false),
% 3.31/0.81    inference(subsumption_resolution,[],[f3814,f3806])).
% 3.31/0.81  fof(f3806,plain,(
% 3.31/0.81    ~v3_pre_topc(k5_xboole_0(k2_struct_0(sK0),sK1),sK0)),
% 3.31/0.81    inference(subsumption_resolution,[],[f3805,f2506])).
% 3.31/0.81  fof(f2506,plain,(
% 3.31/0.81    ~v4_pre_topc(sK1,sK0) | ~v3_pre_topc(k5_xboole_0(k2_struct_0(sK0),sK1),sK0)),
% 3.31/0.81    inference(backward_demodulation,[],[f74,f2466])).
% 3.31/0.81  fof(f2466,plain,(
% 3.31/0.81    k3_subset_1(k2_struct_0(sK0),sK1) = k5_xboole_0(k2_struct_0(sK0),sK1)),
% 3.31/0.81    inference(backward_demodulation,[],[f125,f2437])).
% 3.31/0.81  fof(f2437,plain,(
% 3.31/0.81    sK1 = k9_subset_1(sK1,k2_struct_0(sK0),sK1)),
% 3.31/0.81    inference(superposition,[],[f2430,f103])).
% 3.31/0.81  fof(f103,plain,(
% 3.31/0.81    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X1,X0)) = k9_subset_1(X1,X0,X1)) )),
% 3.31/0.81    inference(superposition,[],[f98,f38])).
% 3.31/0.81  fof(f38,plain,(
% 3.31/0.81    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 3.31/0.81    inference(cnf_transformation,[],[f5])).
% 3.31/0.81  fof(f5,axiom,(
% 3.31/0.81    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 3.31/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 3.31/0.81  fof(f98,plain,(
% 3.31/0.81    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X1,X0)) = k9_subset_1(X0,X1,X0)) )),
% 3.31/0.81    inference(resolution,[],[f60,f70])).
% 3.31/0.81  fof(f70,plain,(
% 3.31/0.81    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 3.31/0.81    inference(forward_demodulation,[],[f33,f32])).
% 3.31/0.81  fof(f32,plain,(
% 3.31/0.81    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 3.31/0.81    inference(cnf_transformation,[],[f6])).
% 3.31/0.81  fof(f6,axiom,(
% 3.31/0.81    ! [X0] : k2_subset_1(X0) = X0),
% 3.31/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 3.31/0.81  fof(f33,plain,(
% 3.31/0.81    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 3.31/0.81    inference(cnf_transformation,[],[f8])).
% 3.31/0.81  fof(f8,axiom,(
% 3.31/0.81    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 3.31/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 3.31/0.81  fof(f60,plain,(
% 3.31/0.81    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))) )),
% 3.31/0.81    inference(definition_unfolding,[],[f50,f39])).
% 3.31/0.81  fof(f39,plain,(
% 3.31/0.81    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.31/0.81    inference(cnf_transformation,[],[f12])).
% 3.31/0.81  fof(f12,axiom,(
% 3.31/0.81    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.31/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 3.31/0.81  fof(f50,plain,(
% 3.31/0.81    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) )),
% 3.31/0.81    inference(cnf_transformation,[],[f27])).
% 3.31/0.81  fof(f27,plain,(
% 3.31/0.81    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 3.31/0.81    inference(ennf_transformation,[],[f10])).
% 3.31/0.81  fof(f10,axiom,(
% 3.31/0.81    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 3.31/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 3.31/0.81  fof(f2430,plain,(
% 3.31/0.81    sK1 = k1_setfam_1(k2_tarski(sK1,k2_struct_0(sK0)))),
% 3.31/0.81    inference(forward_demodulation,[],[f2374,f38])).
% 3.31/0.81  fof(f2374,plain,(
% 3.31/0.81    sK1 = k1_setfam_1(k2_tarski(k2_struct_0(sK0),sK1))),
% 3.31/0.81    inference(resolution,[],[f2080,f78])).
% 3.31/0.81  fof(f78,plain,(
% 3.31/0.81    r1_tarski(sK1,k2_struct_0(sK0))),
% 3.31/0.81    inference(resolution,[],[f49,f75])).
% 3.31/0.81  fof(f75,plain,(
% 3.31/0.81    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 3.31/0.81    inference(backward_demodulation,[],[f30,f72])).
% 3.31/0.81  fof(f72,plain,(
% 3.31/0.81    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 3.31/0.81    inference(resolution,[],[f34,f71])).
% 3.31/0.81  fof(f71,plain,(
% 3.31/0.81    l1_struct_0(sK0)),
% 3.31/0.81    inference(resolution,[],[f35,f31])).
% 3.31/0.81  fof(f31,plain,(
% 3.31/0.81    l1_pre_topc(sK0)),
% 3.31/0.81    inference(cnf_transformation,[],[f19])).
% 3.31/0.81  fof(f19,plain,(
% 3.31/0.81    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.31/0.81    inference(ennf_transformation,[],[f18])).
% 3.31/0.81  fof(f18,negated_conjecture,(
% 3.31/0.81    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 3.31/0.81    inference(negated_conjecture,[],[f17])).
% 3.31/0.81  fof(f17,conjecture,(
% 3.31/0.81    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 3.31/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_1)).
% 3.31/0.81  fof(f35,plain,(
% 3.31/0.81    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 3.31/0.81    inference(cnf_transformation,[],[f21])).
% 3.31/0.81  fof(f21,plain,(
% 3.31/0.81    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.31/0.81    inference(ennf_transformation,[],[f16])).
% 3.31/0.81  fof(f16,axiom,(
% 3.31/0.81    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.31/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 3.31/0.81  fof(f34,plain,(
% 3.31/0.81    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 3.31/0.81    inference(cnf_transformation,[],[f20])).
% 3.31/0.81  fof(f20,plain,(
% 3.31/0.81    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 3.31/0.81    inference(ennf_transformation,[],[f14])).
% 3.31/0.81  fof(f14,axiom,(
% 3.31/0.81    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 3.31/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 3.31/0.81  fof(f30,plain,(
% 3.31/0.81    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.31/0.81    inference(cnf_transformation,[],[f19])).
% 3.31/0.81  fof(f49,plain,(
% 3.31/0.81    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 3.31/0.81    inference(cnf_transformation,[],[f13])).
% 3.31/0.81  fof(f13,axiom,(
% 3.31/0.81    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.31/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 3.31/0.81  fof(f2080,plain,(
% 3.31/0.81    ( ! [X6,X7] : (~r1_tarski(X7,X6) | k1_setfam_1(k2_tarski(X6,X7)) = X7) )),
% 3.31/0.81    inference(duplicate_literal_removal,[],[f2075])).
% 3.31/0.81  fof(f2075,plain,(
% 3.31/0.81    ( ! [X6,X7] : (k1_setfam_1(k2_tarski(X6,X7)) = X7 | k1_setfam_1(k2_tarski(X6,X7)) = X7 | ~r1_tarski(X7,X6)) )),
% 3.31/0.81    inference(resolution,[],[f1950,f878])).
% 3.31/0.81  fof(f878,plain,(
% 3.31/0.81    ( ! [X4,X5,X3] : (r2_hidden(sK3(X3,X4,X4),X5) | k1_setfam_1(k2_tarski(X3,X4)) = X4 | ~r1_tarski(X4,X5)) )),
% 3.31/0.81    inference(resolution,[],[f876,f45])).
% 3.31/0.81  fof(f45,plain,(
% 3.31/0.81    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 3.31/0.81    inference(cnf_transformation,[],[f26])).
% 3.31/0.81  fof(f26,plain,(
% 3.31/0.81    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.31/0.81    inference(ennf_transformation,[],[f1])).
% 3.31/0.81  fof(f1,axiom,(
% 3.31/0.81    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.31/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 3.31/0.81  fof(f876,plain,(
% 3.31/0.81    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1,X1),X1) | k1_setfam_1(k2_tarski(X0,X1)) = X1) )),
% 3.31/0.81    inference(factoring,[],[f64])).
% 3.31/0.81  fof(f64,plain,(
% 3.31/0.81    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X2) | k1_setfam_1(k2_tarski(X0,X1)) = X2) )),
% 3.31/0.81    inference(definition_unfolding,[],[f53,f39])).
% 3.31/0.81  fof(f53,plain,(
% 3.31/0.81    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X2) | k3_xboole_0(X0,X1) = X2) )),
% 3.31/0.81    inference(cnf_transformation,[],[f2])).
% 3.31/0.81  fof(f2,axiom,(
% 3.31/0.81    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.31/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 3.31/0.81  fof(f1950,plain,(
% 3.31/0.81    ( ! [X10,X11] : (~r2_hidden(sK3(X10,X11,X11),X10) | k1_setfam_1(k2_tarski(X10,X11)) = X11) )),
% 3.31/0.81    inference(subsumption_resolution,[],[f1947,f64])).
% 3.31/0.81  fof(f1947,plain,(
% 3.31/0.81    ( ! [X10,X11] : (~r2_hidden(sK3(X10,X11,X11),X11) | ~r2_hidden(sK3(X10,X11,X11),X10) | k1_setfam_1(k2_tarski(X10,X11)) = X11) )),
% 3.31/0.81    inference(duplicate_literal_removal,[],[f1940])).
% 3.31/0.81  fof(f1940,plain,(
% 3.31/0.81    ( ! [X10,X11] : (~r2_hidden(sK3(X10,X11,X11),X11) | ~r2_hidden(sK3(X10,X11,X11),X10) | k1_setfam_1(k2_tarski(X10,X11)) = X11 | k1_setfam_1(k2_tarski(X10,X11)) = X11) )),
% 3.31/0.81    inference(resolution,[],[f66,f876])).
% 3.31/0.81  fof(f66,plain,(
% 3.31/0.81    ( ! [X2,X0,X1] : (~r2_hidden(sK3(X0,X1,X2),X2) | ~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | k1_setfam_1(k2_tarski(X0,X1)) = X2) )),
% 3.31/0.81    inference(definition_unfolding,[],[f51,f39])).
% 3.31/0.81  fof(f51,plain,(
% 3.31/0.81    ( ! [X2,X0,X1] : (~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X2) | k3_xboole_0(X0,X1) = X2) )),
% 3.31/0.81    inference(cnf_transformation,[],[f2])).
% 3.31/0.81  fof(f125,plain,(
% 3.31/0.81    k3_subset_1(k2_struct_0(sK0),sK1) = k5_xboole_0(k2_struct_0(sK0),k9_subset_1(sK1,k2_struct_0(sK0),sK1))),
% 3.31/0.81    inference(forward_demodulation,[],[f123,f98])).
% 3.31/0.81  fof(f123,plain,(
% 3.31/0.81    k3_subset_1(k2_struct_0(sK0),sK1) = k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k2_tarski(k2_struct_0(sK0),sK1)))),
% 3.31/0.81    inference(resolution,[],[f59,f75])).
% 3.31/0.81  fof(f59,plain,(
% 3.31/0.81    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 3.31/0.81    inference(definition_unfolding,[],[f43,f57])).
% 3.31/0.81  fof(f57,plain,(
% 3.31/0.81    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 3.31/0.81    inference(definition_unfolding,[],[f40,f39])).
% 3.31/0.81  fof(f40,plain,(
% 3.31/0.81    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.31/0.81    inference(cnf_transformation,[],[f3])).
% 3.31/0.81  fof(f3,axiom,(
% 3.31/0.81    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.31/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 3.31/0.81  fof(f43,plain,(
% 3.31/0.81    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 3.31/0.81    inference(cnf_transformation,[],[f24])).
% 3.31/0.81  fof(f24,plain,(
% 3.31/0.81    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.31/0.81    inference(ennf_transformation,[],[f7])).
% 3.31/0.81  fof(f7,axiom,(
% 3.31/0.81    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 3.31/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 3.31/0.81  fof(f74,plain,(
% 3.31/0.81    ~v4_pre_topc(sK1,sK0) | ~v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0)),
% 3.31/0.81    inference(backward_demodulation,[],[f29,f72])).
% 3.31/0.81  fof(f29,plain,(
% 3.31/0.81    ~v4_pre_topc(sK1,sK0) | ~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)),
% 3.31/0.81    inference(cnf_transformation,[],[f19])).
% 3.31/0.81  fof(f3805,plain,(
% 3.31/0.81    ~v3_pre_topc(k5_xboole_0(k2_struct_0(sK0),sK1),sK0) | v4_pre_topc(sK1,sK0)),
% 3.31/0.81    inference(subsumption_resolution,[],[f3804,f75])).
% 3.31/0.81  fof(f3804,plain,(
% 3.31/0.81    ~v3_pre_topc(k5_xboole_0(k2_struct_0(sK0),sK1),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | v4_pre_topc(sK1,sK0)),
% 3.31/0.81    inference(superposition,[],[f319,f3799])).
% 3.31/0.81  fof(f3799,plain,(
% 3.31/0.81    k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) = k5_xboole_0(k2_struct_0(sK0),sK1)),
% 3.31/0.81    inference(forward_demodulation,[],[f3793,f2644])).
% 3.31/0.81  fof(f2644,plain,(
% 3.31/0.81    k5_xboole_0(k2_struct_0(sK0),sK1) = k1_setfam_1(k2_tarski(k2_struct_0(sK0),k5_xboole_0(k2_struct_0(sK0),sK1)))),
% 3.31/0.81    inference(resolution,[],[f2642,f2080])).
% 3.31/0.81  fof(f2642,plain,(
% 3.31/0.81    r1_tarski(k5_xboole_0(k2_struct_0(sK0),sK1),k2_struct_0(sK0))),
% 3.31/0.81    inference(subsumption_resolution,[],[f2640,f75])).
% 3.31/0.81  fof(f2640,plain,(
% 3.31/0.81    r1_tarski(k5_xboole_0(k2_struct_0(sK0),sK1),k2_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 3.31/0.81    inference(superposition,[],[f88,f2466])).
% 3.31/0.81  fof(f88,plain,(
% 3.31/0.81    ( ! [X0,X1] : (r1_tarski(k3_subset_1(X1,X0),X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.31/0.81    inference(resolution,[],[f42,f49])).
% 3.31/0.81  fof(f42,plain,(
% 3.31/0.81    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.31/0.81    inference(cnf_transformation,[],[f23])).
% 3.31/0.81  fof(f23,plain,(
% 3.31/0.81    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.31/0.81    inference(ennf_transformation,[],[f9])).
% 3.31/0.81  fof(f9,axiom,(
% 3.31/0.81    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 3.31/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 3.31/0.81  fof(f3793,plain,(
% 3.31/0.81    k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) = k1_setfam_1(k2_tarski(k2_struct_0(sK0),k5_xboole_0(k2_struct_0(sK0),sK1)))),
% 3.31/0.81    inference(resolution,[],[f2650,f70])).
% 3.31/0.81  fof(f2650,plain,(
% 3.31/0.81    ( ! [X5] : (~m1_subset_1(X5,k1_zfmisc_1(k2_struct_0(sK0))) | k7_subset_1(k2_struct_0(sK0),X5,sK1) = k1_setfam_1(k2_tarski(X5,k5_xboole_0(k2_struct_0(sK0),sK1)))) )),
% 3.31/0.81    inference(backward_demodulation,[],[f2507,f2646])).
% 3.31/0.81  fof(f2646,plain,(
% 3.31/0.81    ( ! [X0] : (k9_subset_1(k2_struct_0(sK0),X0,k5_xboole_0(k2_struct_0(sK0),sK1)) = k1_setfam_1(k2_tarski(X0,k5_xboole_0(k2_struct_0(sK0),sK1)))) )),
% 3.31/0.81    inference(resolution,[],[f2642,f99])).
% 3.31/0.81  fof(f99,plain,(
% 3.31/0.81    ( ! [X4,X2,X3] : (~r1_tarski(X4,X2) | k1_setfam_1(k2_tarski(X3,X4)) = k9_subset_1(X2,X3,X4)) )),
% 3.31/0.81    inference(resolution,[],[f60,f48])).
% 3.31/0.81  fof(f48,plain,(
% 3.31/0.81    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.31/0.81    inference(cnf_transformation,[],[f13])).
% 3.31/0.81  fof(f2507,plain,(
% 3.31/0.81    ( ! [X5] : (k7_subset_1(k2_struct_0(sK0),X5,sK1) = k9_subset_1(k2_struct_0(sK0),X5,k5_xboole_0(k2_struct_0(sK0),sK1)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 3.31/0.81    inference(backward_demodulation,[],[f1797,f2466])).
% 3.31/0.81  fof(f1797,plain,(
% 3.31/0.81    ( ! [X5] : (~m1_subset_1(X5,k1_zfmisc_1(k2_struct_0(sK0))) | k7_subset_1(k2_struct_0(sK0),X5,sK1) = k9_subset_1(k2_struct_0(sK0),X5,k3_subset_1(k2_struct_0(sK0),sK1))) )),
% 3.31/0.81    inference(resolution,[],[f44,f75])).
% 3.31/0.81  fof(f44,plain,(
% 3.31/0.81    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))) )),
% 3.31/0.81    inference(cnf_transformation,[],[f25])).
% 3.31/0.81  fof(f25,plain,(
% 3.31/0.81    ! [X0,X1] : (! [X2] : (k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.31/0.81    inference(ennf_transformation,[],[f11])).
% 3.31/0.81  fof(f11,axiom,(
% 3.31/0.81    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))))),
% 3.31/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_subset_1)).
% 3.31/0.81  fof(f319,plain,(
% 3.31/0.81    ( ! [X0] : (~v3_pre_topc(k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v4_pre_topc(X0,sK0)) )),
% 3.31/0.81    inference(forward_demodulation,[],[f318,f72])).
% 3.31/0.81  fof(f318,plain,(
% 3.31/0.81    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0),sK0) | v4_pre_topc(X0,sK0)) )),
% 3.31/0.81    inference(forward_demodulation,[],[f317,f72])).
% 3.31/0.81  fof(f317,plain,(
% 3.31/0.81    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0),sK0) | v4_pre_topc(X0,sK0)) )),
% 3.31/0.81    inference(resolution,[],[f36,f31])).
% 3.31/0.81  fof(f36,plain,(
% 3.31/0.81    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) | v4_pre_topc(X1,X0)) )),
% 3.31/0.81    inference(cnf_transformation,[],[f22])).
% 3.31/0.81  fof(f22,plain,(
% 3.31/0.81    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.31/0.81    inference(ennf_transformation,[],[f15])).
% 3.31/0.81  fof(f15,axiom,(
% 3.31/0.81    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0))))),
% 3.31/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_pre_topc)).
% 3.31/0.81  fof(f3814,plain,(
% 3.31/0.81    v3_pre_topc(k5_xboole_0(k2_struct_0(sK0),sK1),sK0)),
% 3.31/0.81    inference(forward_demodulation,[],[f3813,f3799])).
% 3.31/0.81  fof(f3813,plain,(
% 3.31/0.81    v3_pre_topc(k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1),sK0)),
% 3.31/0.81    inference(forward_demodulation,[],[f3812,f72])).
% 3.31/0.81  fof(f3812,plain,(
% 3.31/0.81    v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0)),
% 3.31/0.81    inference(subsumption_resolution,[],[f3811,f75])).
% 3.31/0.81  fof(f3811,plain,(
% 3.31/0.81    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0)),
% 3.31/0.81    inference(forward_demodulation,[],[f3810,f72])).
% 3.31/0.81  fof(f3810,plain,(
% 3.31/0.81    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0)),
% 3.31/0.81    inference(subsumption_resolution,[],[f3809,f31])).
% 3.31/0.81  fof(f3809,plain,(
% 3.31/0.81    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0) | ~l1_pre_topc(sK0)),
% 3.31/0.81    inference(resolution,[],[f3807,f37])).
% 3.31/0.81  fof(f37,plain,(
% 3.31/0.81    ( ! [X0,X1] : (~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) | ~l1_pre_topc(X0)) )),
% 3.31/0.81    inference(cnf_transformation,[],[f22])).
% 3.31/0.81  fof(f3807,plain,(
% 3.31/0.81    v4_pre_topc(sK1,sK0)),
% 3.31/0.81    inference(resolution,[],[f3806,f2505])).
% 3.31/0.81  fof(f2505,plain,(
% 3.31/0.81    v3_pre_topc(k5_xboole_0(k2_struct_0(sK0),sK1),sK0) | v4_pre_topc(sK1,sK0)),
% 3.31/0.81    inference(backward_demodulation,[],[f73,f2466])).
% 3.31/0.81  fof(f73,plain,(
% 3.31/0.81    v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0) | v4_pre_topc(sK1,sK0)),
% 3.31/0.81    inference(backward_demodulation,[],[f28,f72])).
% 3.31/0.81  fof(f28,plain,(
% 3.31/0.81    v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | v4_pre_topc(sK1,sK0)),
% 3.31/0.81    inference(cnf_transformation,[],[f19])).
% 3.31/0.81  % SZS output end Proof for theBenchmark
% 3.31/0.81  % (21059)------------------------------
% 3.31/0.81  % (21059)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.31/0.81  % (21059)Termination reason: Refutation
% 3.31/0.81  
% 3.31/0.81  % (21059)Memory used [KB]: 9850
% 3.31/0.81  % (21059)Time elapsed: 0.368 s
% 3.31/0.81  % (21059)------------------------------
% 3.31/0.81  % (21059)------------------------------
% 3.31/0.81  % (21050)Success in time 0.462 s
%------------------------------------------------------------------------------
