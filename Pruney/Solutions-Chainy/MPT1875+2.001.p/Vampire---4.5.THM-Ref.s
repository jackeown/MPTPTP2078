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
% DateTime   : Thu Dec  3 13:21:31 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 399 expanded)
%              Number of leaves         :   16 (  82 expanded)
%              Depth                    :   37
%              Number of atoms          :  416 (1681 expanded)
%              Number of equality atoms :   37 (  84 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f487,plain,(
    $false ),
    inference(subsumption_resolution,[],[f485,f82])).

fof(f82,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
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

fof(f485,plain,(
    ~ r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0)) ),
    inference(resolution,[],[f483,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f483,plain,(
    ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f481,f115])).

fof(f115,plain,
    ( v2_tex_2(u1_struct_0(sK0),sK0)
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f114,f45])).

fof(f45,plain,(
    v1_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => v2_tex_2(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tex_2)).

fof(f114,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_tdlat_3(sK0)
    | v2_tex_2(u1_struct_0(sK0),sK0) ),
    inference(subsumption_resolution,[],[f89,f46])).

fof(f46,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f89,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_tdlat_3(sK0)
    | v2_tex_2(u1_struct_0(sK0),sK0) ),
    inference(resolution,[],[f43,f78])).

fof(f78,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tdlat_3(X0)
      | v2_tex_2(u1_struct_0(X0),X0) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X0) != X1
      | ~ v1_tdlat_3(X0)
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> v1_tdlat_3(X0) )
          | u1_struct_0(X0) != X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> v1_tdlat_3(X0) )
          | u1_struct_0(X0) != X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( u1_struct_0(X0) = X1
           => ( v2_tex_2(X1,X0)
            <=> v1_tdlat_3(X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_tex_2)).

fof(f43,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f481,plain,(
    ~ v2_tex_2(u1_struct_0(sK0),sK0) ),
    inference(forward_demodulation,[],[f477,f47])).

fof(f47,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f477,plain,(
    ~ v2_tex_2(k2_subset_1(u1_struct_0(sK0)),sK0) ),
    inference(resolution,[],[f475,f48])).

fof(f48,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f475,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tex_2(X1,sK0) ) ),
    inference(subsumption_resolution,[],[f474,f41])).

fof(f41,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f21])).

fof(f474,plain,(
    ! [X1] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tex_2(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f473,f42])).

fof(f42,plain,(
    ~ v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f473,plain,(
    ! [X1] :
      ( v2_tex_2(sK1,sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tex_2(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(superposition,[],[f146,f471])).

fof(f471,plain,(
    ! [X2] : sK1 = k3_xboole_0(X2,sK1) ),
    inference(subsumption_resolution,[],[f470,f419])).

fof(f419,plain,(
    ! [X0] : r1_tarski(sK1,X0) ),
    inference(condensation,[],[f418])).

fof(f418,plain,(
    ! [X4,X3] :
      ( r1_tarski(sK1,X4)
      | r1_tarski(sK1,X3) ) ),
    inference(forward_demodulation,[],[f414,f47])).

fof(f414,plain,(
    ! [X4,X3] :
      ( r1_tarski(sK1,X3)
      | r1_tarski(k2_subset_1(sK1),X4) ) ),
    inference(resolution,[],[f411,f48])).

fof(f411,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1))
      | r1_tarski(sK1,X1)
      | r1_tarski(X0,X2) ) ),
    inference(resolution,[],[f410,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
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

fof(f410,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(sK1))
      | r1_tarski(sK1,X0) ) ),
    inference(resolution,[],[f408,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f408,plain,(
    ! [X0] :
      ( v1_xboole_0(sK1)
      | r1_tarski(sK1,X0) ) ),
    inference(subsumption_resolution,[],[f407,f41])).

fof(f407,plain,(
    ! [X0] :
      ( v1_xboole_0(sK1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_tarski(sK1,X0) ) ),
    inference(subsumption_resolution,[],[f403,f42])).

fof(f403,plain,(
    ! [X0] :
      ( v2_tex_2(sK1,sK0)
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_tarski(sK1,X0) ) ),
    inference(superposition,[],[f113,f396])).

fof(f396,plain,(
    ! [X0] :
      ( sK1 = u1_struct_0(sK2(sK0,sK1))
      | r1_tarski(sK1,X0) ) ),
    inference(resolution,[],[f395,f82])).

fof(f395,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(X3,sK1)
      | sK1 = u1_struct_0(sK2(sK0,sK1))
      | r1_tarski(X3,X4) ) ),
    inference(forward_demodulation,[],[f392,f47])).

fof(f392,plain,(
    ! [X4,X3] :
      ( sK1 = u1_struct_0(sK2(sK0,sK1))
      | ~ r1_tarski(X3,k2_subset_1(sK1))
      | r1_tarski(X3,X4) ) ),
    inference(resolution,[],[f387,f48])).

fof(f387,plain,(
    ! [X17,X18,X16] :
      ( ~ m1_subset_1(X16,k1_zfmisc_1(sK1))
      | sK1 = u1_struct_0(sK2(sK0,sK1))
      | ~ r1_tarski(X17,X16)
      | r1_tarski(X17,X18) ) ),
    inference(resolution,[],[f336,f41])).

fof(f336,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | u1_struct_0(sK2(sK0,X1)) = X1
      | ~ r1_tarski(X2,X0)
      | r1_tarski(X2,X3) ) ),
    inference(resolution,[],[f127,f70])).

fof(f127,plain,(
    ! [X6,X4,X5,X3] :
      ( ~ r2_hidden(X5,X6)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK2(sK0,X3)) = X3
      | ~ r1_tarski(X6,X4) ) ),
    inference(resolution,[],[f119,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | u1_struct_0(sK2(sK0,X0)) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f118,f76])).

fof(f118,plain,(
    ! [X2] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK2(sK0,X2)) = X2 ) ),
    inference(subsumption_resolution,[],[f85,f46])).

fof(f85,plain,(
    ! [X2] :
      ( ~ l1_pre_topc(sK0)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK2(sK0,X2)) = X2 ) ),
    inference(resolution,[],[f43,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(sK2(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_tsep_1)).

fof(f113,plain,(
    ! [X0] :
      ( v2_tex_2(u1_struct_0(sK2(sK0,X0)),sK0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f112,f107])).

fof(f107,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_struct_0(sK2(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f83,f46])).

fof(f83,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_struct_0(sK2(sK0,X0)) ) ),
    inference(resolution,[],[f43,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_struct_0(sK2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f112,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X0)
      | v2_struct_0(sK2(sK0,X0))
      | v2_tex_2(u1_struct_0(sK2(sK0,X0)),sK0) ) ),
    inference(resolution,[],[f111,f110])).

fof(f110,plain,(
    ! [X7] :
      ( ~ m1_pre_topc(X7,sK0)
      | v2_struct_0(X7)
      | v2_tex_2(u1_struct_0(X7),sK0) ) ),
    inference(subsumption_resolution,[],[f109,f101])).

fof(f101,plain,(
    ! [X5] :
      ( v1_tdlat_3(X5)
      | ~ m1_pre_topc(X5,sK0) ) ),
    inference(subsumption_resolution,[],[f100,f46])).

fof(f100,plain,(
    ! [X5] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_pre_topc(X5,sK0)
      | v1_tdlat_3(X5) ) ),
    inference(subsumption_resolution,[],[f94,f45])).

fof(f94,plain,(
    ! [X5] :
      ( ~ v1_tdlat_3(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_pre_topc(X5,sK0)
      | v1_tdlat_3(X5) ) ),
    inference(subsumption_resolution,[],[f88,f49])).

fof(f49,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_tdlat_3)).

fof(f88,plain,(
    ! [X5] :
      ( ~ v2_pre_topc(sK0)
      | ~ v1_tdlat_3(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_pre_topc(X5,sK0)
      | v1_tdlat_3(X5) ) ),
    inference(resolution,[],[f43,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v1_tdlat_3(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tdlat_3(X1)
            & v1_tsep_1(X1,X0)
            & v1_borsuk_1(X1,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tdlat_3(X1)
            & v1_tsep_1(X1,X0)
            & v1_borsuk_1(X1,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tdlat_3(X1)
            & v1_tsep_1(X1,X0)
            & v1_borsuk_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_tdlat_3)).

fof(f109,plain,(
    ! [X7] :
      ( v2_struct_0(X7)
      | ~ m1_pre_topc(X7,sK0)
      | ~ v1_tdlat_3(X7)
      | v2_tex_2(u1_struct_0(X7),sK0) ) ),
    inference(subsumption_resolution,[],[f96,f46])).

fof(f96,plain,(
    ! [X7] :
      ( ~ l1_pre_topc(sK0)
      | v2_struct_0(X7)
      | ~ m1_pre_topc(X7,sK0)
      | ~ v1_tdlat_3(X7)
      | v2_tex_2(u1_struct_0(X7),sK0) ) ),
    inference(subsumption_resolution,[],[f91,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f91,plain,(
    ! [X7] :
      ( ~ l1_pre_topc(sK0)
      | v2_struct_0(X7)
      | ~ m1_pre_topc(X7,sK0)
      | ~ m1_subset_1(u1_struct_0(X7),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v1_tdlat_3(X7)
      | v2_tex_2(u1_struct_0(X7),sK0) ) ),
    inference(resolution,[],[f43,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tdlat_3(X1)
      | v2_tex_2(u1_struct_0(X1),X0) ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X1) != X2
      | ~ v1_tdlat_3(X1)
      | v2_tex_2(X2,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_tex_2(X2,X0)
              <=> v1_tdlat_3(X1) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_tex_2(X2,X0)
              <=> v1_tdlat_3(X1) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( v2_tex_2(X2,X0)
                <=> v1_tdlat_3(X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_tex_2)).

fof(f111,plain,(
    ! [X1] :
      ( m1_pre_topc(sK2(sK0,X1),sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X1) ) ),
    inference(subsumption_resolution,[],[f84,f46])).

fof(f84,plain,(
    ! [X1] :
      ( ~ l1_pre_topc(sK0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_pre_topc(sK2(sK0,X1),sK0) ) ),
    inference(resolution,[],[f43,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_pre_topc(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f470,plain,(
    ! [X2] :
      ( sK1 = k3_xboole_0(X2,sK1)
      | ~ r1_tarski(sK1,sK1) ) ),
    inference(resolution,[],[f457,f72])).

fof(f457,plain,(
    ! [X2] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK1))
      | sK1 = k3_xboole_0(X2,sK1) ) ),
    inference(superposition,[],[f456,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f456,plain,(
    ! [X2] : sK1 = k9_subset_1(sK1,X2,sK1) ),
    inference(forward_demodulation,[],[f453,f47])).

fof(f453,plain,(
    ! [X2] : sK1 = k9_subset_1(sK1,X2,k2_subset_1(sK1)) ),
    inference(resolution,[],[f450,f48])).

fof(f450,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(sK1))
      | sK1 = k9_subset_1(sK1,X1,X2) ) ),
    inference(resolution,[],[f443,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(f443,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(sK1))
      | sK1 = X4 ) ),
    inference(resolution,[],[f420,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f420,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1)
      | sK1 = X0 ) ),
    inference(resolution,[],[f419,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f146,plain,(
    ! [X0,X1] :
      ( v2_tex_2(k3_xboole_0(X0,X1),sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tex_2(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(duplicate_literal_removal,[],[f145])).

fof(f145,plain,(
    ! [X0,X1] :
      ( v2_tex_2(k3_xboole_0(X0,X1),sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tex_2(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(superposition,[],[f97,f75])).

fof(f97,plain,(
    ! [X0,X1] :
      ( v2_tex_2(k9_subset_1(u1_struct_0(sK0),X0,X1),sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tex_2(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f46,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              | ( ~ v2_tex_2(X2,X0)
                & ~ v2_tex_2(X1,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              | ( ~ v2_tex_2(X2,X0)
                & ~ v2_tex_2(X1,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v2_tex_2(X2,X0)
                  | v2_tex_2(X1,X0) )
               => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tex_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:02:55 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.49  % (22749)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.50  % (22757)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.50  % (22748)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (22747)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.51  % (22758)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.51  % (22747)Refutation not found, incomplete strategy% (22747)------------------------------
% 0.20/0.51  % (22747)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (22747)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (22747)Memory used [KB]: 10618
% 0.20/0.51  % (22747)Time elapsed: 0.109 s
% 0.20/0.51  % (22747)------------------------------
% 0.20/0.51  % (22747)------------------------------
% 0.20/0.51  % (22750)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.51  % (22765)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.52  % (22740)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.52  % (22741)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.52  % (22743)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.52  % (22736)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.52  % (22736)Refutation not found, incomplete strategy% (22736)------------------------------
% 0.20/0.52  % (22736)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (22736)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (22736)Memory used [KB]: 1663
% 0.20/0.52  % (22736)Time elapsed: 0.100 s
% 0.20/0.52  % (22736)------------------------------
% 0.20/0.52  % (22736)------------------------------
% 0.20/0.52  % (22738)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.52  % (22758)Refutation not found, incomplete strategy% (22758)------------------------------
% 0.20/0.52  % (22758)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (22759)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.52  % (22737)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.52  % (22763)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.52  % (22742)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.52  % (22761)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.53  % (22739)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  % (22755)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.53  % (22764)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.53  % (22758)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (22758)Memory used [KB]: 10746
% 0.20/0.53  % (22758)Time elapsed: 0.078 s
% 0.20/0.53  % (22758)------------------------------
% 0.20/0.53  % (22758)------------------------------
% 0.20/0.53  % (22751)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.53  % (22760)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.53  % (22754)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.53  % (22752)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.53  % (22744)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.53  % (22746)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.53  % (22762)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.54  % (22753)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.54  % (22745)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.54  % (22753)Refutation not found, incomplete strategy% (22753)------------------------------
% 0.20/0.54  % (22753)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (22745)Refutation not found, incomplete strategy% (22745)------------------------------
% 0.20/0.54  % (22745)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (22753)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (22753)Memory used [KB]: 10618
% 0.20/0.54  % (22753)Time elapsed: 0.140 s
% 0.20/0.54  % (22753)------------------------------
% 0.20/0.54  % (22753)------------------------------
% 0.20/0.54  % (22745)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (22745)Memory used [KB]: 10618
% 0.20/0.54  % (22745)Time elapsed: 0.141 s
% 0.20/0.54  % (22745)------------------------------
% 0.20/0.54  % (22745)------------------------------
% 0.20/0.55  % (22746)Refutation not found, incomplete strategy% (22746)------------------------------
% 0.20/0.55  % (22746)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (22746)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (22746)Memory used [KB]: 10618
% 0.20/0.55  % (22746)Time elapsed: 0.151 s
% 0.20/0.55  % (22746)------------------------------
% 0.20/0.55  % (22746)------------------------------
% 0.20/0.55  % (22756)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.55  % (22757)Refutation found. Thanks to Tanya!
% 0.20/0.55  % SZS status Theorem for theBenchmark
% 0.20/0.55  % SZS output start Proof for theBenchmark
% 0.20/0.55  fof(f487,plain,(
% 0.20/0.55    $false),
% 0.20/0.55    inference(subsumption_resolution,[],[f485,f82])).
% 0.20/0.55  fof(f82,plain,(
% 0.20/0.55    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.55    inference(equality_resolution,[],[f66])).
% 0.20/0.55  fof(f66,plain,(
% 0.20/0.55    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.20/0.55    inference(cnf_transformation,[],[f2])).
% 0.20/0.55  fof(f2,axiom,(
% 0.20/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.55  fof(f485,plain,(
% 0.20/0.55    ~r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0))),
% 0.20/0.55    inference(resolution,[],[f483,f72])).
% 0.20/0.55  fof(f72,plain,(
% 0.20/0.55    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f8])).
% 0.20/0.55  fof(f8,axiom,(
% 0.20/0.55    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.55  fof(f483,plain,(
% 0.20/0.55    ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.55    inference(resolution,[],[f481,f115])).
% 0.20/0.55  fof(f115,plain,(
% 0.20/0.55    v2_tex_2(u1_struct_0(sK0),sK0) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.55    inference(subsumption_resolution,[],[f114,f45])).
% 0.20/0.55  fof(f45,plain,(
% 0.20/0.55    v1_tdlat_3(sK0)),
% 0.20/0.55    inference(cnf_transformation,[],[f21])).
% 0.20/0.55  fof(f21,plain,(
% 0.20/0.55    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.55    inference(flattening,[],[f20])).
% 0.20/0.55  fof(f20,plain,(
% 0.20/0.55    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.55    inference(ennf_transformation,[],[f19])).
% 0.20/0.55  fof(f19,negated_conjecture,(
% 0.20/0.55    ~! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v2_tex_2(X1,X0)))),
% 0.20/0.55    inference(negated_conjecture,[],[f18])).
% 0.20/0.55  fof(f18,conjecture,(
% 0.20/0.55    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v2_tex_2(X1,X0)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tex_2)).
% 0.20/0.55  fof(f114,plain,(
% 0.20/0.55    ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_tdlat_3(sK0) | v2_tex_2(u1_struct_0(sK0),sK0)),
% 0.20/0.55    inference(subsumption_resolution,[],[f89,f46])).
% 0.20/0.55  fof(f46,plain,(
% 0.20/0.55    l1_pre_topc(sK0)),
% 0.20/0.55    inference(cnf_transformation,[],[f21])).
% 0.20/0.55  fof(f89,plain,(
% 0.20/0.55    ~l1_pre_topc(sK0) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_tdlat_3(sK0) | v2_tex_2(u1_struct_0(sK0),sK0)),
% 0.20/0.55    inference(resolution,[],[f43,f78])).
% 0.20/0.55  fof(f78,plain,(
% 0.20/0.55    ( ! [X0] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tdlat_3(X0) | v2_tex_2(u1_struct_0(X0),X0)) )),
% 0.20/0.55    inference(equality_resolution,[],[f55])).
% 0.20/0.55  fof(f55,plain,(
% 0.20/0.55    ( ! [X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X0) != X1 | ~v1_tdlat_3(X0) | v2_tex_2(X1,X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f30])).
% 0.20/0.55  fof(f30,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> v1_tdlat_3(X0)) | u1_struct_0(X0) != X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.55    inference(flattening,[],[f29])).
% 0.20/0.55  fof(f29,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) <=> v1_tdlat_3(X0)) | u1_struct_0(X0) != X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.55    inference(ennf_transformation,[],[f16])).
% 0.20/0.55  fof(f16,axiom,(
% 0.20/0.55    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X0) = X1 => (v2_tex_2(X1,X0) <=> v1_tdlat_3(X0)))))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_tex_2)).
% 0.20/0.55  fof(f43,plain,(
% 0.20/0.55    ~v2_struct_0(sK0)),
% 0.20/0.55    inference(cnf_transformation,[],[f21])).
% 0.20/0.55  fof(f481,plain,(
% 0.20/0.55    ~v2_tex_2(u1_struct_0(sK0),sK0)),
% 0.20/0.55    inference(forward_demodulation,[],[f477,f47])).
% 0.20/0.55  fof(f47,plain,(
% 0.20/0.55    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.20/0.55    inference(cnf_transformation,[],[f3])).
% 0.20/0.55  fof(f3,axiom,(
% 0.20/0.55    ! [X0] : k2_subset_1(X0) = X0),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.20/0.55  fof(f477,plain,(
% 0.20/0.55    ~v2_tex_2(k2_subset_1(u1_struct_0(sK0)),sK0)),
% 0.20/0.55    inference(resolution,[],[f475,f48])).
% 0.20/0.55  fof(f48,plain,(
% 0.20/0.55    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f4])).
% 0.20/0.55  fof(f4,axiom,(
% 0.20/0.55    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.20/0.55  fof(f475,plain,(
% 0.20/0.55    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X1,sK0)) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f474,f41])).
% 0.20/0.55  fof(f41,plain,(
% 0.20/0.55    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.55    inference(cnf_transformation,[],[f21])).
% 0.20/0.55  fof(f474,plain,(
% 0.20/0.55    ( ! [X1] : (~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f473,f42])).
% 0.20/0.55  fof(f42,plain,(
% 0.20/0.55    ~v2_tex_2(sK1,sK0)),
% 0.20/0.55    inference(cnf_transformation,[],[f21])).
% 0.20/0.55  fof(f473,plain,(
% 0.20/0.55    ( ! [X1] : (v2_tex_2(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.20/0.55    inference(superposition,[],[f146,f471])).
% 0.20/0.55  fof(f471,plain,(
% 0.20/0.55    ( ! [X2] : (sK1 = k3_xboole_0(X2,sK1)) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f470,f419])).
% 0.20/0.55  fof(f419,plain,(
% 0.20/0.55    ( ! [X0] : (r1_tarski(sK1,X0)) )),
% 0.20/0.55    inference(condensation,[],[f418])).
% 0.20/0.55  fof(f418,plain,(
% 0.20/0.55    ( ! [X4,X3] : (r1_tarski(sK1,X4) | r1_tarski(sK1,X3)) )),
% 0.20/0.55    inference(forward_demodulation,[],[f414,f47])).
% 0.20/0.55  fof(f414,plain,(
% 0.20/0.55    ( ! [X4,X3] : (r1_tarski(sK1,X3) | r1_tarski(k2_subset_1(sK1),X4)) )),
% 0.20/0.55    inference(resolution,[],[f411,f48])).
% 0.20/0.55  fof(f411,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(sK1)) | r1_tarski(sK1,X1) | r1_tarski(X0,X2)) )),
% 0.20/0.55    inference(resolution,[],[f410,f70])).
% 0.20/0.55  fof(f70,plain,(
% 0.20/0.55    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f37])).
% 0.20/0.55  fof(f37,plain,(
% 0.20/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.55    inference(ennf_transformation,[],[f1])).
% 0.20/0.55  fof(f1,axiom,(
% 0.20/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.55  fof(f410,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(sK1)) | r1_tarski(sK1,X0)) )),
% 0.20/0.55    inference(resolution,[],[f408,f76])).
% 0.20/0.55  fof(f76,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f40])).
% 0.20/0.55  fof(f40,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.20/0.55    inference(ennf_transformation,[],[f9])).
% 0.20/0.55  fof(f9,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 0.20/0.55  fof(f408,plain,(
% 0.20/0.55    ( ! [X0] : (v1_xboole_0(sK1) | r1_tarski(sK1,X0)) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f407,f41])).
% 0.20/0.55  fof(f407,plain,(
% 0.20/0.55    ( ! [X0] : (v1_xboole_0(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(sK1,X0)) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f403,f42])).
% 0.20/0.55  fof(f403,plain,(
% 0.20/0.55    ( ! [X0] : (v2_tex_2(sK1,sK0) | v1_xboole_0(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(sK1,X0)) )),
% 0.20/0.55    inference(superposition,[],[f113,f396])).
% 0.20/0.55  fof(f396,plain,(
% 0.20/0.55    ( ! [X0] : (sK1 = u1_struct_0(sK2(sK0,sK1)) | r1_tarski(sK1,X0)) )),
% 0.20/0.55    inference(resolution,[],[f395,f82])).
% 0.20/0.55  fof(f395,plain,(
% 0.20/0.55    ( ! [X4,X3] : (~r1_tarski(X3,sK1) | sK1 = u1_struct_0(sK2(sK0,sK1)) | r1_tarski(X3,X4)) )),
% 0.20/0.55    inference(forward_demodulation,[],[f392,f47])).
% 0.20/0.55  fof(f392,plain,(
% 0.20/0.55    ( ! [X4,X3] : (sK1 = u1_struct_0(sK2(sK0,sK1)) | ~r1_tarski(X3,k2_subset_1(sK1)) | r1_tarski(X3,X4)) )),
% 0.20/0.55    inference(resolution,[],[f387,f48])).
% 0.20/0.55  fof(f387,plain,(
% 0.20/0.55    ( ! [X17,X18,X16] : (~m1_subset_1(X16,k1_zfmisc_1(sK1)) | sK1 = u1_struct_0(sK2(sK0,sK1)) | ~r1_tarski(X17,X16) | r1_tarski(X17,X18)) )),
% 0.20/0.55    inference(resolution,[],[f336,f41])).
% 0.20/0.55  fof(f336,plain,(
% 0.20/0.55    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(X1)) | u1_struct_0(sK2(sK0,X1)) = X1 | ~r1_tarski(X2,X0) | r1_tarski(X2,X3)) )),
% 0.20/0.55    inference(resolution,[],[f127,f70])).
% 0.20/0.55  fof(f127,plain,(
% 0.20/0.55    ( ! [X6,X4,X5,X3] : (~r2_hidden(X5,X6) | ~m1_subset_1(X4,k1_zfmisc_1(X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK2(sK0,X3)) = X3 | ~r1_tarski(X6,X4)) )),
% 0.20/0.55    inference(resolution,[],[f119,f69])).
% 0.20/0.55  fof(f69,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f37])).
% 0.20/0.55  fof(f119,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | u1_struct_0(sK2(sK0,X0)) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.20/0.55    inference(resolution,[],[f118,f76])).
% 0.20/0.55  fof(f118,plain,(
% 0.20/0.55    ( ! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK2(sK0,X2)) = X2) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f85,f46])).
% 0.20/0.55  fof(f85,plain,(
% 0.20/0.55    ( ! [X2] : (~l1_pre_topc(sK0) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK2(sK0,X2)) = X2) )),
% 0.20/0.55    inference(resolution,[],[f43,f60])).
% 0.20/0.55  fof(f60,plain,(
% 0.20/0.55    ( ! [X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(sK2(X0,X1)) = X1) )),
% 0.20/0.55    inference(cnf_transformation,[],[f32])).
% 0.20/0.55  fof(f32,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.55    inference(flattening,[],[f31])).
% 0.20/0.55  fof(f31,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.55    inference(ennf_transformation,[],[f14])).
% 0.20/0.55  fof(f14,axiom,(
% 0.20/0.55    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2))))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_tsep_1)).
% 0.20/0.55  fof(f113,plain,(
% 0.20/0.55    ( ! [X0] : (v2_tex_2(u1_struct_0(sK2(sK0,X0)),sK0) | v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f112,f107])).
% 0.20/0.55  fof(f107,plain,(
% 0.20/0.55    ( ! [X0] : (v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_struct_0(sK2(sK0,X0))) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f83,f46])).
% 0.20/0.55  fof(f83,plain,(
% 0.20/0.55    ( ! [X0] : (~l1_pre_topc(sK0) | v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_struct_0(sK2(sK0,X0))) )),
% 0.20/0.55    inference(resolution,[],[f43,f57])).
% 0.20/0.55  fof(f57,plain,(
% 0.20/0.55    ( ! [X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_struct_0(sK2(X0,X1))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f32])).
% 0.20/0.55  fof(f112,plain,(
% 0.20/0.55    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X0) | v2_struct_0(sK2(sK0,X0)) | v2_tex_2(u1_struct_0(sK2(sK0,X0)),sK0)) )),
% 0.20/0.55    inference(resolution,[],[f111,f110])).
% 0.20/0.55  fof(f110,plain,(
% 0.20/0.55    ( ! [X7] : (~m1_pre_topc(X7,sK0) | v2_struct_0(X7) | v2_tex_2(u1_struct_0(X7),sK0)) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f109,f101])).
% 0.20/0.55  fof(f101,plain,(
% 0.20/0.55    ( ! [X5] : (v1_tdlat_3(X5) | ~m1_pre_topc(X5,sK0)) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f100,f46])).
% 0.20/0.55  fof(f100,plain,(
% 0.20/0.55    ( ! [X5] : (~l1_pre_topc(sK0) | ~m1_pre_topc(X5,sK0) | v1_tdlat_3(X5)) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f94,f45])).
% 0.20/0.55  fof(f94,plain,(
% 0.20/0.55    ( ! [X5] : (~v1_tdlat_3(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(X5,sK0) | v1_tdlat_3(X5)) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f88,f49])).
% 0.20/0.55  fof(f49,plain,(
% 0.20/0.55    ( ! [X0] : (v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f23])).
% 0.20/0.55  fof(f23,plain,(
% 0.20/0.55    ! [X0] : (v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 0.20/0.55    inference(flattening,[],[f22])).
% 0.20/0.55  fof(f22,plain,(
% 0.20/0.55    ! [X0] : ((v2_pre_topc(X0) | ~v1_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 0.20/0.55    inference(ennf_transformation,[],[f12])).
% 0.20/0.55  fof(f12,axiom,(
% 0.20/0.55    ! [X0] : (l1_pre_topc(X0) => (v1_tdlat_3(X0) => v2_pre_topc(X0)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_tdlat_3)).
% 0.20/0.55  fof(f88,plain,(
% 0.20/0.55    ( ! [X5] : (~v2_pre_topc(sK0) | ~v1_tdlat_3(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(X5,sK0) | v1_tdlat_3(X5)) )),
% 0.20/0.55    inference(resolution,[],[f43,f65])).
% 0.20/0.55  fof(f65,plain,(
% 0.20/0.55    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v1_tdlat_3(X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f36])).
% 0.20/0.55  fof(f36,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : ((v1_tdlat_3(X1) & v1_tsep_1(X1,X0) & v1_borsuk_1(X1,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.55    inference(flattening,[],[f35])).
% 0.20/0.55  fof(f35,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : ((v1_tdlat_3(X1) & v1_tsep_1(X1,X0) & v1_borsuk_1(X1,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.55    inference(ennf_transformation,[],[f13])).
% 0.20/0.55  fof(f13,axiom,(
% 0.20/0.55    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tdlat_3(X1) & v1_tsep_1(X1,X0) & v1_borsuk_1(X1,X0))))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_tdlat_3)).
% 0.20/0.55  fof(f109,plain,(
% 0.20/0.55    ( ! [X7] : (v2_struct_0(X7) | ~m1_pre_topc(X7,sK0) | ~v1_tdlat_3(X7) | v2_tex_2(u1_struct_0(X7),sK0)) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f96,f46])).
% 0.20/0.55  fof(f96,plain,(
% 0.20/0.55    ( ! [X7] : (~l1_pre_topc(sK0) | v2_struct_0(X7) | ~m1_pre_topc(X7,sK0) | ~v1_tdlat_3(X7) | v2_tex_2(u1_struct_0(X7),sK0)) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f91,f50])).
% 0.20/0.55  fof(f50,plain,(
% 0.20/0.55    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f24])).
% 0.20/0.55  fof(f24,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.55    inference(ennf_transformation,[],[f11])).
% 0.20/0.55  fof(f11,axiom,(
% 0.20/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.20/0.55  fof(f91,plain,(
% 0.20/0.55    ( ! [X7] : (~l1_pre_topc(sK0) | v2_struct_0(X7) | ~m1_pre_topc(X7,sK0) | ~m1_subset_1(u1_struct_0(X7),k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_tdlat_3(X7) | v2_tex_2(u1_struct_0(X7),sK0)) )),
% 0.20/0.55    inference(resolution,[],[f43,f80])).
% 0.20/0.55  fof(f80,plain,(
% 0.20/0.55    ( ! [X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tdlat_3(X1) | v2_tex_2(u1_struct_0(X1),X0)) )),
% 0.20/0.55    inference(equality_resolution,[],[f61])).
% 0.20/0.55  fof(f61,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X1) != X2 | ~v1_tdlat_3(X1) | v2_tex_2(X2,X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f34])).
% 0.20/0.55  fof(f34,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (! [X2] : ((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.55    inference(flattening,[],[f33])).
% 0.20/0.55  fof(f33,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (! [X2] : (((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.55    inference(ennf_transformation,[],[f15])).
% 0.20/0.55  fof(f15,axiom,(
% 0.20/0.55    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => (v2_tex_2(X2,X0) <=> v1_tdlat_3(X1))))))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_tex_2)).
% 0.20/0.55  fof(f111,plain,(
% 0.20/0.55    ( ! [X1] : (m1_pre_topc(sK2(sK0,X1),sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X1)) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f84,f46])).
% 0.20/0.55  fof(f84,plain,(
% 0.20/0.55    ( ! [X1] : (~l1_pre_topc(sK0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | m1_pre_topc(sK2(sK0,X1),sK0)) )),
% 0.20/0.55    inference(resolution,[],[f43,f59])).
% 0.20/0.55  fof(f59,plain,(
% 0.20/0.55    ( ! [X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_pre_topc(sK2(X0,X1),X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f32])).
% 0.20/0.55  fof(f470,plain,(
% 0.20/0.55    ( ! [X2] : (sK1 = k3_xboole_0(X2,sK1) | ~r1_tarski(sK1,sK1)) )),
% 0.20/0.55    inference(resolution,[],[f457,f72])).
% 0.20/0.55  fof(f457,plain,(
% 0.20/0.55    ( ! [X2] : (~m1_subset_1(sK1,k1_zfmisc_1(sK1)) | sK1 = k3_xboole_0(X2,sK1)) )),
% 0.20/0.55    inference(superposition,[],[f456,f75])).
% 0.20/0.55  fof(f75,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f39])).
% 0.20/0.55  fof(f39,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.20/0.55    inference(ennf_transformation,[],[f6])).
% 0.20/0.55  fof(f6,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.20/0.55  fof(f456,plain,(
% 0.20/0.55    ( ! [X2] : (sK1 = k9_subset_1(sK1,X2,sK1)) )),
% 0.20/0.55    inference(forward_demodulation,[],[f453,f47])).
% 0.20/0.55  fof(f453,plain,(
% 0.20/0.55    ( ! [X2] : (sK1 = k9_subset_1(sK1,X2,k2_subset_1(sK1))) )),
% 0.20/0.55    inference(resolution,[],[f450,f48])).
% 0.20/0.55  fof(f450,plain,(
% 0.20/0.55    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(sK1)) | sK1 = k9_subset_1(sK1,X1,X2)) )),
% 0.20/0.55    inference(resolution,[],[f443,f74])).
% 0.20/0.55  fof(f74,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f38])).
% 0.20/0.55  fof(f38,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.20/0.55    inference(ennf_transformation,[],[f5])).
% 0.20/0.55  fof(f5,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).
% 0.20/0.55  fof(f443,plain,(
% 0.20/0.55    ( ! [X4] : (~m1_subset_1(X4,k1_zfmisc_1(sK1)) | sK1 = X4) )),
% 0.20/0.55    inference(resolution,[],[f420,f73])).
% 0.20/0.55  fof(f73,plain,(
% 0.20/0.55    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f8])).
% 0.20/0.55  fof(f420,plain,(
% 0.20/0.55    ( ! [X0] : (~r1_tarski(X0,sK1) | sK1 = X0) )),
% 0.20/0.55    inference(resolution,[],[f419,f68])).
% 0.20/0.55  fof(f68,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.20/0.55    inference(cnf_transformation,[],[f2])).
% 0.20/0.55  fof(f146,plain,(
% 0.20/0.55    ( ! [X0,X1] : (v2_tex_2(k3_xboole_0(X0,X1),sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.20/0.55    inference(duplicate_literal_removal,[],[f145])).
% 0.20/0.55  fof(f145,plain,(
% 0.20/0.55    ( ! [X0,X1] : (v2_tex_2(k3_xboole_0(X0,X1),sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.20/0.55    inference(superposition,[],[f97,f75])).
% 0.20/0.55  fof(f97,plain,(
% 0.20/0.55    ( ! [X0,X1] : (v2_tex_2(k9_subset_1(u1_struct_0(sK0),X0,X1),sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.20/0.55    inference(resolution,[],[f46,f52])).
% 0.20/0.55  fof(f52,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f27])).
% 0.20/0.55  fof(f27,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (! [X2] : (v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) | (~v2_tex_2(X2,X0) & ~v2_tex_2(X1,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.55    inference(flattening,[],[f26])).
% 0.20/0.55  fof(f26,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (! [X2] : ((v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) | (~v2_tex_2(X2,X0) & ~v2_tex_2(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.55    inference(ennf_transformation,[],[f17])).
% 0.20/0.55  fof(f17,axiom,(
% 0.20/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tex_2)).
% 0.20/0.55  % SZS output end Proof for theBenchmark
% 0.20/0.55  % (22757)------------------------------
% 0.20/0.55  % (22757)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (22757)Termination reason: Refutation
% 0.20/0.55  
% 0.20/0.55  % (22757)Memory used [KB]: 1918
% 0.20/0.55  % (22757)Time elapsed: 0.144 s
% 0.20/0.55  % (22757)------------------------------
% 0.20/0.55  % (22757)------------------------------
% 0.20/0.56  % (22735)Success in time 0.2 s
%------------------------------------------------------------------------------
