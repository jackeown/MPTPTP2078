%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:55 EST 2020

% Result     : Theorem 1.19s
% Output     : Refutation 1.19s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 642 expanded)
%              Number of leaves         :   16 ( 139 expanded)
%              Depth                    :   17
%              Number of atoms          :  325 (2309 expanded)
%              Number of equality atoms :   35 ( 164 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f297,plain,(
    $false ),
    inference(subsumption_resolution,[],[f261,f270])).

fof(f270,plain,(
    ~ v3_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f234,f68])).

fof(f68,plain,(
    ! [X0] : ~ v1_subset_1(X0,X0) ),
    inference(backward_demodulation,[],[f43,f44])).

fof(f44,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f43,plain,(
    ! [X0] : ~ v1_subset_1(k2_subset_1(X0),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : ~ v1_subset_1(k2_subset_1(X0),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc14_subset_1)).

fof(f234,plain,
    ( v1_subset_1(sK1,sK1)
    | ~ v3_tex_2(sK1,sK0) ),
    inference(backward_demodulation,[],[f86,f230])).

fof(f230,plain,(
    sK1 = k2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f229,f102])).

fof(f102,plain,(
    r1_tarski(sK1,k2_struct_0(sK0)) ),
    inference(duplicate_literal_removal,[],[f99])).

fof(f99,plain,
    ( r1_tarski(sK1,k2_struct_0(sK0))
    | r1_tarski(sK1,k2_struct_0(sK0)) ),
    inference(resolution,[],[f98,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
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

fof(f98,plain,(
    ! [X4] :
      ( r2_hidden(sK3(sK1,X4),k2_struct_0(sK0))
      | r1_tarski(sK1,X4) ) ),
    inference(resolution,[],[f94,f87])).

fof(f87,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f38,f82])).

% (7326)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
fof(f82,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f79,f71])).

fof(f71,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f48,f42])).

fof(f42,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_tex_2(X1,X0)
            <=> ~ v1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tex_2(X1,X0)
          <=> ~ v1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_tex_2)).

fof(f48,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f79,plain,(
    ! [X1] :
      ( ~ l1_struct_0(X1)
      | u1_struct_0(X1) = k2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f78,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc12_struct_0)).

fof(f78,plain,(
    ! [X1] :
      ( u1_struct_0(X1) = k2_struct_0(X1)
      | v1_subset_1(k2_struct_0(X1),u1_struct_0(X1))
      | ~ l1_struct_0(X1) ) ),
    inference(resolution,[],[f61,f47])).

fof(f47,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

fof(f38,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r2_hidden(sK3(X0,X2),X1)
      | r1_tarski(X0,X2) ) ),
    inference(resolution,[],[f63,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f229,plain,
    ( sK1 = k2_struct_0(sK0)
    | ~ r1_tarski(sK1,k2_struct_0(sK0)) ),
    inference(duplicate_literal_removal,[],[f224])).

fof(f224,plain,
    ( sK1 = k2_struct_0(sK0)
    | ~ r1_tarski(sK1,k2_struct_0(sK0))
    | sK1 = k2_struct_0(sK0) ),
    inference(resolution,[],[f220,f69])).

fof(f69,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f45,f44])).

fof(f45,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f220,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | sK1 = X0
      | ~ r1_tarski(sK1,X0)
      | sK1 = k2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f218,f87])).

fof(f218,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r1_tarski(sK1,X0)
      | sK1 = X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | sK1 = k2_struct_0(sK0) ) ),
    inference(resolution,[],[f217,f83])).

fof(f83,plain,
    ( v3_tex_2(sK1,sK0)
    | sK1 = k2_struct_0(sK0) ),
    inference(backward_demodulation,[],[f80,f82])).

fof(f80,plain,
    ( v3_tex_2(sK1,sK0)
    | sK1 = u1_struct_0(sK0) ),
    inference(resolution,[],[f76,f36])).

fof(f36,plain,
    ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
    | v3_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f76,plain,
    ( v1_subset_1(sK1,u1_struct_0(sK0))
    | sK1 = u1_struct_0(sK0) ),
    inference(resolution,[],[f61,f38])).

fof(f217,plain,(
    ! [X0,X1] :
      ( ~ v3_tex_2(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r1_tarski(X0,X1)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f216,f118])).

fof(f118,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | v2_tex_2(X0,sK0) ) ),
    inference(forward_demodulation,[],[f117,f82])).

fof(f117,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_tex_2(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f116,f42])).

fof(f116,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_tex_2(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f115,f39])).

fof(f39,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f115,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_tex_2(X0,sK0) ) ),
    inference(resolution,[],[f70,f41])).

fof(f41,plain,(
    v1_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ v1_tdlat_3(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tex_2(X1,X0) ) ),
    inference(subsumption_resolution,[],[f59,f50])).

fof(f50,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_tdlat_3)).

fof(f59,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tex_2)).

fof(f216,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v2_tex_2(X1,sK0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1
      | ~ v3_tex_2(X0,sK0) ) ),
    inference(forward_demodulation,[],[f215,f82])).

fof(f215,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tex_2(X1,sK0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1
      | ~ v3_tex_2(X0,sK0) ) ),
    inference(forward_demodulation,[],[f214,f82])).

fof(f214,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tex_2(X1,sK0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1
      | ~ v3_tex_2(X0,sK0) ) ),
    inference(resolution,[],[f57,f42])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X2,X0)
      | ~ r1_tarski(X1,X2)
      | X1 = X2
      | ~ v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r1_tarski(X1,X2)
                      & v2_tex_2(X2,X0) )
                   => X1 = X2 ) )
              & v2_tex_2(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tex_2)).

fof(f86,plain,
    ( ~ v3_tex_2(sK1,sK0)
    | v1_subset_1(sK1,k2_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f37,f82])).

fof(f37,plain,
    ( ~ v3_tex_2(sK1,sK0)
    | v1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f261,plain,(
    v3_tex_2(sK1,sK0) ),
    inference(backward_demodulation,[],[f176,f230])).

fof(f176,plain,(
    v3_tex_2(k2_struct_0(sK0),sK0) ),
    inference(subsumption_resolution,[],[f175,f69])).

fof(f175,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | v3_tex_2(k2_struct_0(sK0),sK0) ),
    inference(resolution,[],[f174,f125])).

fof(f125,plain,(
    v1_tops_1(k2_struct_0(sK0),sK0) ),
    inference(subsumption_resolution,[],[f124,f69])).

fof(f124,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | v1_tops_1(k2_struct_0(sK0),sK0) ),
    inference(forward_demodulation,[],[f123,f82])).

fof(f123,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_tops_1(k2_struct_0(sK0),sK0) ),
    inference(subsumption_resolution,[],[f122,f42])).

fof(f122,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | v1_tops_1(k2_struct_0(sK0),sK0) ),
    inference(subsumption_resolution,[],[f121,f82])).

fof(f121,plain,
    ( u1_struct_0(sK0) != k2_struct_0(sK0)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | v1_tops_1(k2_struct_0(sK0),sK0) ),
    inference(superposition,[],[f51,f74])).

fof(f74,plain,(
    k2_struct_0(sK0) = k2_pre_topc(sK0,k2_struct_0(sK0)) ),
    inference(resolution,[],[f49,f42])).

fof(f49,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_tops_1)).

fof(f51,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) != k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v1_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_3)).

fof(f174,plain,(
    ! [X0] :
      ( ~ v1_tops_1(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | v3_tex_2(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f173,f118])).

fof(f173,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v1_tops_1(X0,sK0)
      | ~ v2_tex_2(X0,sK0)
      | v3_tex_2(X0,sK0) ) ),
    inference(forward_demodulation,[],[f172,f82])).

fof(f172,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v1_tops_1(X0,sK0)
      | ~ v2_tex_2(X0,sK0)
      | v3_tex_2(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f171,f39])).

fof(f171,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v1_tops_1(X0,sK0)
      | ~ v2_tex_2(X0,sK0)
      | v3_tex_2(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f170,f40])).

fof(f40,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f170,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v1_tops_1(X0,sK0)
      | ~ v2_tex_2(X0,sK0)
      | v3_tex_2(X0,sK0) ) ),
    inference(resolution,[],[f60,f42])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tops_1(X1,X0)
      | ~ v2_tex_2(X1,X0)
      | v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tex_2(X1,X0)
          | ~ v2_tex_2(X1,X0)
          | ~ v1_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tex_2(X1,X0)
          | ~ v2_tex_2(X1,X0)
          | ~ v1_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v2_tex_2(X1,X0)
              & v1_tops_1(X1,X0) )
           => v3_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tex_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:53:35 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.46  % (7333)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.48  % (7333)Refutation not found, incomplete strategy% (7333)------------------------------
% 0.20/0.48  % (7333)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (7333)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (7333)Memory used [KB]: 10618
% 0.20/0.48  % (7333)Time elapsed: 0.094 s
% 0.20/0.48  % (7333)------------------------------
% 0.20/0.48  % (7333)------------------------------
% 0.20/0.50  % (7330)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.19/0.53  % (7330)Refutation found. Thanks to Tanya!
% 1.19/0.53  % SZS status Theorem for theBenchmark
% 1.19/0.53  % SZS output start Proof for theBenchmark
% 1.19/0.53  fof(f297,plain,(
% 1.19/0.53    $false),
% 1.19/0.53    inference(subsumption_resolution,[],[f261,f270])).
% 1.19/0.53  fof(f270,plain,(
% 1.19/0.53    ~v3_tex_2(sK1,sK0)),
% 1.19/0.53    inference(subsumption_resolution,[],[f234,f68])).
% 1.19/0.53  fof(f68,plain,(
% 1.19/0.53    ( ! [X0] : (~v1_subset_1(X0,X0)) )),
% 1.19/0.53    inference(backward_demodulation,[],[f43,f44])).
% 1.19/0.53  fof(f44,plain,(
% 1.19/0.53    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.19/0.53    inference(cnf_transformation,[],[f2])).
% 1.19/0.53  fof(f2,axiom,(
% 1.19/0.53    ! [X0] : k2_subset_1(X0) = X0),
% 1.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 1.19/0.53  fof(f43,plain,(
% 1.19/0.53    ( ! [X0] : (~v1_subset_1(k2_subset_1(X0),X0)) )),
% 1.19/0.53    inference(cnf_transformation,[],[f5])).
% 1.19/0.53  fof(f5,axiom,(
% 1.19/0.53    ! [X0] : ~v1_subset_1(k2_subset_1(X0),X0)),
% 1.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc14_subset_1)).
% 1.19/0.53  fof(f234,plain,(
% 1.19/0.53    v1_subset_1(sK1,sK1) | ~v3_tex_2(sK1,sK0)),
% 1.19/0.53    inference(backward_demodulation,[],[f86,f230])).
% 1.19/0.53  fof(f230,plain,(
% 1.19/0.53    sK1 = k2_struct_0(sK0)),
% 1.19/0.53    inference(subsumption_resolution,[],[f229,f102])).
% 1.19/0.53  fof(f102,plain,(
% 1.19/0.53    r1_tarski(sK1,k2_struct_0(sK0))),
% 1.19/0.53    inference(duplicate_literal_removal,[],[f99])).
% 1.19/0.53  fof(f99,plain,(
% 1.19/0.53    r1_tarski(sK1,k2_struct_0(sK0)) | r1_tarski(sK1,k2_struct_0(sK0))),
% 1.19/0.53    inference(resolution,[],[f98,f66])).
% 1.19/0.53  fof(f66,plain,(
% 1.19/0.53    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.19/0.53    inference(cnf_transformation,[],[f35])).
% 1.19/0.53  fof(f35,plain,(
% 1.19/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.19/0.53    inference(ennf_transformation,[],[f1])).
% 1.19/0.53  fof(f1,axiom,(
% 1.19/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.19/0.53  fof(f98,plain,(
% 1.19/0.53    ( ! [X4] : (r2_hidden(sK3(sK1,X4),k2_struct_0(sK0)) | r1_tarski(sK1,X4)) )),
% 1.19/0.53    inference(resolution,[],[f94,f87])).
% 1.19/0.53  fof(f87,plain,(
% 1.19/0.53    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 1.19/0.53    inference(backward_demodulation,[],[f38,f82])).
% 1.19/0.53  % (7326)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.19/0.53  fof(f82,plain,(
% 1.19/0.53    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 1.19/0.53    inference(resolution,[],[f79,f71])).
% 1.19/0.53  fof(f71,plain,(
% 1.19/0.53    l1_struct_0(sK0)),
% 1.19/0.53    inference(resolution,[],[f48,f42])).
% 1.19/0.53  fof(f42,plain,(
% 1.19/0.53    l1_pre_topc(sK0)),
% 1.19/0.53    inference(cnf_transformation,[],[f19])).
% 1.19/0.53  fof(f19,plain,(
% 1.19/0.53    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> ~v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.19/0.53    inference(flattening,[],[f18])).
% 1.19/0.53  fof(f18,plain,(
% 1.19/0.53    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> ~v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.19/0.53    inference(ennf_transformation,[],[f17])).
% 1.19/0.53  fof(f17,negated_conjecture,(
% 1.19/0.53    ~! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> ~v1_subset_1(X1,u1_struct_0(X0)))))),
% 1.19/0.53    inference(negated_conjecture,[],[f16])).
% 1.19/0.53  fof(f16,conjecture,(
% 1.19/0.53    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> ~v1_subset_1(X1,u1_struct_0(X0)))))),
% 1.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_tex_2)).
% 1.19/0.53  fof(f48,plain,(
% 1.19/0.53    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 1.19/0.53    inference(cnf_transformation,[],[f22])).
% 1.19/0.53  fof(f22,plain,(
% 1.19/0.53    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.19/0.53    inference(ennf_transformation,[],[f7])).
% 1.19/0.53  fof(f7,axiom,(
% 1.19/0.53    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.19/0.53  fof(f79,plain,(
% 1.19/0.53    ( ! [X1] : (~l1_struct_0(X1) | u1_struct_0(X1) = k2_struct_0(X1)) )),
% 1.19/0.53    inference(subsumption_resolution,[],[f78,f46])).
% 1.19/0.53  fof(f46,plain,(
% 1.19/0.53    ( ! [X0] : (~v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)) | ~l1_struct_0(X0)) )),
% 1.19/0.53    inference(cnf_transformation,[],[f20])).
% 1.19/0.53  fof(f20,plain,(
% 1.19/0.53    ! [X0] : (~v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)) | ~l1_struct_0(X0))),
% 1.19/0.53    inference(ennf_transformation,[],[f8])).
% 1.19/0.53  fof(f8,axiom,(
% 1.19/0.53    ! [X0] : (l1_struct_0(X0) => ~v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)))),
% 1.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc12_struct_0)).
% 1.19/0.53  fof(f78,plain,(
% 1.19/0.53    ( ! [X1] : (u1_struct_0(X1) = k2_struct_0(X1) | v1_subset_1(k2_struct_0(X1),u1_struct_0(X1)) | ~l1_struct_0(X1)) )),
% 1.19/0.53    inference(resolution,[],[f61,f47])).
% 1.19/0.53  fof(f47,plain,(
% 1.19/0.53    ( ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0)) )),
% 1.19/0.53    inference(cnf_transformation,[],[f21])).
% 1.19/0.53  fof(f21,plain,(
% 1.19/0.53    ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0))),
% 1.19/0.53    inference(ennf_transformation,[],[f6])).
% 1.19/0.53  fof(f6,axiom,(
% 1.19/0.53    ! [X0] : (l1_struct_0(X0) => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).
% 1.19/0.53  fof(f61,plain,(
% 1.19/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) )),
% 1.19/0.53    inference(cnf_transformation,[],[f33])).
% 1.19/0.53  fof(f33,plain,(
% 1.19/0.53    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.19/0.53    inference(ennf_transformation,[],[f12])).
% 1.19/0.53  fof(f12,axiom,(
% 1.19/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 1.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).
% 1.19/0.53  fof(f38,plain,(
% 1.19/0.53    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.19/0.53    inference(cnf_transformation,[],[f19])).
% 1.19/0.53  fof(f94,plain,(
% 1.19/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r2_hidden(sK3(X0,X2),X1) | r1_tarski(X0,X2)) )),
% 1.19/0.53    inference(resolution,[],[f63,f65])).
% 1.19/0.53  fof(f65,plain,(
% 1.19/0.53    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.19/0.53    inference(cnf_transformation,[],[f35])).
% 1.19/0.53  fof(f63,plain,(
% 1.19/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | r2_hidden(X2,X0)) )),
% 1.19/0.53    inference(cnf_transformation,[],[f34])).
% 1.19/0.53  fof(f34,plain,(
% 1.19/0.53    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.19/0.53    inference(ennf_transformation,[],[f4])).
% 1.19/0.53  fof(f4,axiom,(
% 1.19/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 1.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 1.19/0.53  fof(f229,plain,(
% 1.19/0.53    sK1 = k2_struct_0(sK0) | ~r1_tarski(sK1,k2_struct_0(sK0))),
% 1.19/0.53    inference(duplicate_literal_removal,[],[f224])).
% 1.19/0.53  fof(f224,plain,(
% 1.19/0.53    sK1 = k2_struct_0(sK0) | ~r1_tarski(sK1,k2_struct_0(sK0)) | sK1 = k2_struct_0(sK0)),
% 1.19/0.53    inference(resolution,[],[f220,f69])).
% 1.19/0.53  fof(f69,plain,(
% 1.19/0.53    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 1.19/0.53    inference(forward_demodulation,[],[f45,f44])).
% 1.19/0.53  fof(f45,plain,(
% 1.19/0.53    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.19/0.53    inference(cnf_transformation,[],[f3])).
% 1.19/0.53  fof(f3,axiom,(
% 1.19/0.53    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 1.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 1.19/0.53  fof(f220,plain,(
% 1.19/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | sK1 = X0 | ~r1_tarski(sK1,X0) | sK1 = k2_struct_0(sK0)) )),
% 1.19/0.53    inference(subsumption_resolution,[],[f218,f87])).
% 1.19/0.53  fof(f218,plain,(
% 1.19/0.53    ( ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | ~r1_tarski(sK1,X0) | sK1 = X0 | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | sK1 = k2_struct_0(sK0)) )),
% 1.19/0.53    inference(resolution,[],[f217,f83])).
% 1.19/0.53  fof(f83,plain,(
% 1.19/0.53    v3_tex_2(sK1,sK0) | sK1 = k2_struct_0(sK0)),
% 1.19/0.53    inference(backward_demodulation,[],[f80,f82])).
% 1.19/0.53  fof(f80,plain,(
% 1.19/0.53    v3_tex_2(sK1,sK0) | sK1 = u1_struct_0(sK0)),
% 1.19/0.53    inference(resolution,[],[f76,f36])).
% 1.19/0.53  fof(f36,plain,(
% 1.19/0.53    ~v1_subset_1(sK1,u1_struct_0(sK0)) | v3_tex_2(sK1,sK0)),
% 1.19/0.53    inference(cnf_transformation,[],[f19])).
% 1.19/0.53  fof(f76,plain,(
% 1.19/0.53    v1_subset_1(sK1,u1_struct_0(sK0)) | sK1 = u1_struct_0(sK0)),
% 1.19/0.53    inference(resolution,[],[f61,f38])).
% 1.19/0.53  fof(f217,plain,(
% 1.19/0.53    ( ! [X0,X1] : (~v3_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~r1_tarski(X0,X1) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 1.19/0.53    inference(subsumption_resolution,[],[f216,f118])).
% 1.19/0.53  fof(f118,plain,(
% 1.19/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v2_tex_2(X0,sK0)) )),
% 1.19/0.53    inference(forward_demodulation,[],[f117,f82])).
% 1.19/0.53  fof(f117,plain,(
% 1.19/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(X0,sK0)) )),
% 1.19/0.53    inference(subsumption_resolution,[],[f116,f42])).
% 1.19/0.53  fof(f116,plain,(
% 1.19/0.53    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(X0,sK0)) )),
% 1.19/0.53    inference(subsumption_resolution,[],[f115,f39])).
% 1.19/0.53  fof(f39,plain,(
% 1.19/0.53    ~v2_struct_0(sK0)),
% 1.19/0.53    inference(cnf_transformation,[],[f19])).
% 1.19/0.53  fof(f115,plain,(
% 1.19/0.53    ( ! [X0] : (v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(X0,sK0)) )),
% 1.19/0.53    inference(resolution,[],[f70,f41])).
% 1.19/0.53  fof(f41,plain,(
% 1.19/0.53    v1_tdlat_3(sK0)),
% 1.19/0.53    inference(cnf_transformation,[],[f19])).
% 1.19/0.53  fof(f70,plain,(
% 1.19/0.53    ( ! [X0,X1] : (~v1_tdlat_3(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_tex_2(X1,X0)) )),
% 1.19/0.53    inference(subsumption_resolution,[],[f59,f50])).
% 1.19/0.53  fof(f50,plain,(
% 1.19/0.53    ( ! [X0] : (v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0)) )),
% 1.19/0.53    inference(cnf_transformation,[],[f25])).
% 1.19/0.53  fof(f25,plain,(
% 1.19/0.53    ! [X0] : (v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 1.19/0.53    inference(flattening,[],[f24])).
% 1.19/0.53  fof(f24,plain,(
% 1.19/0.53    ! [X0] : ((v2_pre_topc(X0) | ~v1_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 1.19/0.53    inference(ennf_transformation,[],[f10])).
% 1.19/0.53  fof(f10,axiom,(
% 1.19/0.53    ! [X0] : (l1_pre_topc(X0) => (v1_tdlat_3(X0) => v2_pre_topc(X0)))),
% 1.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_tdlat_3)).
% 1.19/0.53  fof(f59,plain,(
% 1.19/0.53    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_tex_2(X1,X0)) )),
% 1.19/0.53    inference(cnf_transformation,[],[f30])).
% 1.19/0.53  fof(f30,plain,(
% 1.19/0.53    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.19/0.53    inference(flattening,[],[f29])).
% 1.19/0.53  fof(f29,plain,(
% 1.19/0.53    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.19/0.53    inference(ennf_transformation,[],[f14])).
% 1.19/0.53  fof(f14,axiom,(
% 1.19/0.53    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v2_tex_2(X1,X0)))),
% 1.19/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tex_2)).
% 1.19/0.53  fof(f216,plain,(
% 1.19/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v2_tex_2(X1,sK0) | ~r1_tarski(X0,X1) | X0 = X1 | ~v3_tex_2(X0,sK0)) )),
% 1.19/0.53    inference(forward_demodulation,[],[f215,f82])).
% 1.19/0.53  fof(f215,plain,(
% 1.19/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X1,sK0) | ~r1_tarski(X0,X1) | X0 = X1 | ~v3_tex_2(X0,sK0)) )),
% 1.19/0.53    inference(forward_demodulation,[],[f214,f82])).
% 1.19/0.53  fof(f214,plain,(
% 1.19/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X1,sK0) | ~r1_tarski(X0,X1) | X0 = X1 | ~v3_tex_2(X0,sK0)) )),
% 1.19/0.53    inference(resolution,[],[f57,f42])).
% 1.19/0.54  fof(f57,plain,(
% 1.19/0.54    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X2,X0) | ~r1_tarski(X1,X2) | X1 = X2 | ~v3_tex_2(X1,X0)) )),
% 1.19/0.54    inference(cnf_transformation,[],[f28])).
% 1.19/0.54  fof(f28,plain,(
% 1.19/0.54    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.19/0.54    inference(flattening,[],[f27])).
% 1.19/0.54  fof(f27,plain,(
% 1.19/0.54    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.19/0.54    inference(ennf_transformation,[],[f13])).
% 1.19/0.54  fof(f13,axiom,(
% 1.19/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 1.19/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tex_2)).
% 1.19/0.54  fof(f86,plain,(
% 1.19/0.54    ~v3_tex_2(sK1,sK0) | v1_subset_1(sK1,k2_struct_0(sK0))),
% 1.19/0.54    inference(backward_demodulation,[],[f37,f82])).
% 1.19/0.54  fof(f37,plain,(
% 1.19/0.54    ~v3_tex_2(sK1,sK0) | v1_subset_1(sK1,u1_struct_0(sK0))),
% 1.19/0.54    inference(cnf_transformation,[],[f19])).
% 1.19/0.54  fof(f261,plain,(
% 1.19/0.54    v3_tex_2(sK1,sK0)),
% 1.19/0.54    inference(backward_demodulation,[],[f176,f230])).
% 1.19/0.54  fof(f176,plain,(
% 1.19/0.54    v3_tex_2(k2_struct_0(sK0),sK0)),
% 1.19/0.54    inference(subsumption_resolution,[],[f175,f69])).
% 1.19/0.54  fof(f175,plain,(
% 1.19/0.54    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | v3_tex_2(k2_struct_0(sK0),sK0)),
% 1.19/0.54    inference(resolution,[],[f174,f125])).
% 1.19/0.54  fof(f125,plain,(
% 1.19/0.54    v1_tops_1(k2_struct_0(sK0),sK0)),
% 1.19/0.54    inference(subsumption_resolution,[],[f124,f69])).
% 1.19/0.54  fof(f124,plain,(
% 1.19/0.54    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | v1_tops_1(k2_struct_0(sK0),sK0)),
% 1.19/0.54    inference(forward_demodulation,[],[f123,f82])).
% 1.19/0.54  fof(f123,plain,(
% 1.19/0.54    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_tops_1(k2_struct_0(sK0),sK0)),
% 1.19/0.54    inference(subsumption_resolution,[],[f122,f42])).
% 1.19/0.54  fof(f122,plain,(
% 1.19/0.54    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | v1_tops_1(k2_struct_0(sK0),sK0)),
% 1.19/0.54    inference(subsumption_resolution,[],[f121,f82])).
% 1.19/0.54  fof(f121,plain,(
% 1.19/0.54    u1_struct_0(sK0) != k2_struct_0(sK0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | v1_tops_1(k2_struct_0(sK0),sK0)),
% 1.19/0.54    inference(superposition,[],[f51,f74])).
% 1.19/0.54  fof(f74,plain,(
% 1.19/0.54    k2_struct_0(sK0) = k2_pre_topc(sK0,k2_struct_0(sK0))),
% 1.19/0.54    inference(resolution,[],[f49,f42])).
% 1.19/0.54  fof(f49,plain,(
% 1.19/0.54    ( ! [X0] : (~l1_pre_topc(X0) | k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0))) )),
% 1.19/0.54    inference(cnf_transformation,[],[f23])).
% 1.19/0.54  fof(f23,plain,(
% 1.19/0.54    ! [X0] : (k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0)) | ~l1_pre_topc(X0))),
% 1.19/0.54    inference(ennf_transformation,[],[f9])).
% 1.19/0.54  fof(f9,axiom,(
% 1.19/0.54    ! [X0] : (l1_pre_topc(X0) => k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0)))),
% 1.19/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_tops_1)).
% 1.19/0.54  fof(f51,plain,(
% 1.19/0.54    ( ! [X0,X1] : (u1_struct_0(X0) != k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v1_tops_1(X1,X0)) )),
% 1.19/0.54    inference(cnf_transformation,[],[f26])).
% 1.19/0.54  fof(f26,plain,(
% 1.19/0.54    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.19/0.54    inference(ennf_transformation,[],[f11])).
% 1.19/0.54  fof(f11,axiom,(
% 1.19/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 1.19/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_3)).
% 1.19/0.54  fof(f174,plain,(
% 1.19/0.54    ( ! [X0] : (~v1_tops_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v3_tex_2(X0,sK0)) )),
% 1.19/0.54    inference(subsumption_resolution,[],[f173,f118])).
% 1.19/0.54  fof(f173,plain,(
% 1.19/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v1_tops_1(X0,sK0) | ~v2_tex_2(X0,sK0) | v3_tex_2(X0,sK0)) )),
% 1.19/0.54    inference(forward_demodulation,[],[f172,f82])).
% 1.19/0.54  fof(f172,plain,(
% 1.19/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_tops_1(X0,sK0) | ~v2_tex_2(X0,sK0) | v3_tex_2(X0,sK0)) )),
% 1.19/0.54    inference(subsumption_resolution,[],[f171,f39])).
% 1.19/0.54  fof(f171,plain,(
% 1.19/0.54    ( ! [X0] : (v2_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_tops_1(X0,sK0) | ~v2_tex_2(X0,sK0) | v3_tex_2(X0,sK0)) )),
% 1.19/0.54    inference(subsumption_resolution,[],[f170,f40])).
% 1.19/0.54  fof(f40,plain,(
% 1.19/0.54    v2_pre_topc(sK0)),
% 1.19/0.54    inference(cnf_transformation,[],[f19])).
% 1.19/0.54  fof(f170,plain,(
% 1.19/0.54    ( ! [X0] : (~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_tops_1(X0,sK0) | ~v2_tex_2(X0,sK0) | v3_tex_2(X0,sK0)) )),
% 1.19/0.54    inference(resolution,[],[f60,f42])).
% 1.19/0.54  fof(f60,plain,(
% 1.19/0.54    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tops_1(X1,X0) | ~v2_tex_2(X1,X0) | v3_tex_2(X1,X0)) )),
% 1.19/0.54    inference(cnf_transformation,[],[f32])).
% 1.19/0.54  fof(f32,plain,(
% 1.19/0.54    ! [X0] : (! [X1] : (v3_tex_2(X1,X0) | ~v2_tex_2(X1,X0) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.19/0.54    inference(flattening,[],[f31])).
% 1.19/0.54  fof(f31,plain,(
% 1.19/0.54    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) | (~v2_tex_2(X1,X0) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.19/0.54    inference(ennf_transformation,[],[f15])).
% 1.19/0.54  fof(f15,axiom,(
% 1.19/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X1,X0) & v1_tops_1(X1,X0)) => v3_tex_2(X1,X0))))),
% 1.19/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tex_2)).
% 1.19/0.54  % SZS output end Proof for theBenchmark
% 1.19/0.54  % (7330)------------------------------
% 1.19/0.54  % (7330)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.19/0.54  % (7330)Termination reason: Refutation
% 1.19/0.54  
% 1.19/0.54  % (7330)Memory used [KB]: 6396
% 1.19/0.54  % (7330)Time elapsed: 0.124 s
% 1.19/0.54  % (7330)------------------------------
% 1.19/0.54  % (7330)------------------------------
% 1.19/0.54  % (7348)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.19/0.54  % (7323)Success in time 0.181 s
%------------------------------------------------------------------------------
