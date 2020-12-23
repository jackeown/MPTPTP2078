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
% DateTime   : Thu Dec  3 13:21:20 EST 2020

% Result     : Theorem 1.52s
% Output     : Refutation 1.52s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 410 expanded)
%              Number of leaves         :   15 (  85 expanded)
%              Depth                    :   11
%              Number of atoms          :  304 (1686 expanded)
%              Number of equality atoms :   20 (  25 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f282,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f250,f261,f273,f281])).

fof(f281,plain,(
    ~ spl2_24 ),
    inference(avatar_contradiction_clause,[],[f279])).

fof(f279,plain,
    ( $false
    | ~ spl2_24 ),
    inference(unit_resulting_resolution,[],[f41,f39,f110,f70,f118,f249])).

fof(f249,plain,
    ( ! [X5] :
        ( v2_tex_2(k1_tarski(sK1),X5)
        | ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(X5)))
        | v2_struct_0(X5)
        | ~ m1_pre_topc(k1_tex_2(sK0,sK1),X5)
        | ~ l1_pre_topc(X5) )
    | ~ spl2_24 ),
    inference(avatar_component_clause,[],[f248])).

fof(f248,plain,
    ( spl2_24
  <=> ! [X5] :
        ( ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(X5)))
        | v2_tex_2(k1_tarski(sK1),X5)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(k1_tex_2(sK0,sK1),X5)
        | ~ l1_pre_topc(X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).

fof(f118,plain,(
    m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f106,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

fof(f106,plain,(
    r2_hidden(sK1,u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f37,f104,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f104,plain,(
    ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f71,f67,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f67,plain,(
    m1_subset_1(k1_connsp_2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f40,f39,f41,f37,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_connsp_2)).

fof(f40,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).

fof(f71,plain,(
    r2_hidden(sK1,k1_connsp_2(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f40,f39,f41,f37,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r2_hidden(X1,k1_connsp_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,k1_connsp_2(X0,X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,k1_connsp_2(X0,X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r2_hidden(X1,k1_connsp_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_connsp_2)).

fof(f37,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f70,plain,(
    m1_pre_topc(k1_tex_2(sK0,sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f41,f39,f37,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | m1_pre_topc(k1_tex_2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tex_2)).

fof(f110,plain,(
    ~ v2_tex_2(k1_tarski(sK1),sK0) ),
    inference(backward_demodulation,[],[f38,f107])).

fof(f107,plain,(
    k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1) ),
    inference(unit_resulting_resolution,[],[f37,f104,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f38,plain,(
    ~ v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f39,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f41,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f273,plain,(
    ~ spl2_23 ),
    inference(avatar_contradiction_clause,[],[f268])).

fof(f268,plain,
    ( $false
    | ~ spl2_23 ),
    inference(unit_resulting_resolution,[],[f39,f41,f37,f246,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v2_struct_0(k1_tex_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f246,plain,
    ( v2_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl2_23 ),
    inference(avatar_component_clause,[],[f244])).

fof(f244,plain,
    ( spl2_23
  <=> v2_struct_0(k1_tex_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f261,plain,(
    spl2_22 ),
    inference(avatar_contradiction_clause,[],[f256])).

fof(f256,plain,
    ( $false
    | spl2_22 ),
    inference(unit_resulting_resolution,[],[f39,f41,f79,f37,f242,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v1_tdlat_3(k1_tex_2(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v2_pre_topc(k1_tex_2(X0,X1))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tdlat_3(k1_tex_2(X0,X1))
            & v1_tdlat_3(k1_tex_2(X0,X1)) )
          | ~ v2_pre_topc(k1_tex_2(X0,X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tdlat_3(k1_tex_2(X0,X1))
            & v1_tdlat_3(k1_tex_2(X0,X1)) )
          | ~ v2_pre_topc(k1_tex_2(X0,X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v2_pre_topc(k1_tex_2(X0,X1))
           => ( v2_tdlat_3(k1_tex_2(X0,X1))
              & v1_tdlat_3(k1_tex_2(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tex_2)).

fof(f242,plain,
    ( ~ v1_tdlat_3(k1_tex_2(sK0,sK1))
    | spl2_22 ),
    inference(avatar_component_clause,[],[f240])).

fof(f240,plain,
    ( spl2_22
  <=> v1_tdlat_3(k1_tex_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f79,plain,(
    v2_pre_topc(k1_tex_2(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f40,f41,f70,f47])).

% (16142)Refutation not found, incomplete strategy% (16142)------------------------------
% (16142)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (16142)Termination reason: Refutation not found, incomplete strategy

% (16142)Memory used [KB]: 10618
% (16142)Time elapsed: 0.148 s
% (16142)------------------------------
% (16142)------------------------------
fof(f47,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f250,plain,
    ( ~ spl2_22
    | spl2_23
    | spl2_24 ),
    inference(avatar_split_clause,[],[f137,f248,f244,f240])).

fof(f137,plain,(
    ! [X5] :
      ( ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(X5)))
      | ~ l1_pre_topc(X5)
      | v2_struct_0(k1_tex_2(sK0,sK1))
      | ~ m1_pre_topc(k1_tex_2(sK0,sK1),X5)
      | v2_struct_0(X5)
      | ~ v1_tdlat_3(k1_tex_2(sK0,sK1))
      | v2_tex_2(k1_tarski(sK1),X5) ) ),
    inference(superposition,[],[f59,f111])).

fof(f111,plain,(
    u1_struct_0(k1_tex_2(sK0,sK1)) = k1_tarski(sK1) ),
    inference(backward_demodulation,[],[f78,f107])).

fof(f78,plain,(
    k6_domain_1(u1_struct_0(sK0),sK1) = u1_struct_0(k1_tex_2(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f41,f39,f69,f68,f37,f70,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v1_pre_topc(k1_tex_2(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(k1_tex_2(X0,X1))
      | v2_struct_0(X0)
      | ~ m1_pre_topc(k1_tex_2(X0,X1),X0)
      | k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(k1_tex_2(X0,X1)) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X2)
      | ~ v1_pre_topc(X2)
      | ~ m1_pre_topc(X2,X0)
      | u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)
      | k1_tex_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_tex_2(X0,X1) = X2
              <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_tex_2(X0,X1) = X2
              <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_pre_topc(X2)
                & ~ v2_struct_0(X2) )
             => ( k1_tex_2(X0,X1) = X2
              <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tex_2)).

fof(f68,plain,(
    ~ v2_struct_0(k1_tex_2(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f41,f39,f37,f53])).

fof(f69,plain,(
    v1_pre_topc(k1_tex_2(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f41,f39,f37,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v1_pre_topc(k1_tex_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X0)
      | ~ v1_tdlat_3(X1)
      | v2_tex_2(u1_struct_0(X1),X0) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X1) != X2
      | ~ v1_tdlat_3(X1)
      | v2_tex_2(X2,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:27:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.54  % (16150)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.55  % (16141)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.55  % (16132)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.56  % (16145)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.56  % (16136)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.56  % (16134)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.52/0.56  % (16159)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.52/0.56  % (16134)Refutation not found, incomplete strategy% (16134)------------------------------
% 1.52/0.56  % (16134)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.56  % (16134)Termination reason: Refutation not found, incomplete strategy
% 1.52/0.56  
% 1.52/0.56  % (16134)Memory used [KB]: 10746
% 1.52/0.56  % (16134)Time elapsed: 0.135 s
% 1.52/0.56  % (16134)------------------------------
% 1.52/0.56  % (16134)------------------------------
% 1.52/0.57  % (16157)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.52/0.57  % (16133)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.52/0.57  % (16141)Refutation not found, incomplete strategy% (16141)------------------------------
% 1.52/0.57  % (16141)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.57  % (16141)Termination reason: Refutation not found, incomplete strategy
% 1.52/0.57  
% 1.52/0.57  % (16141)Memory used [KB]: 10618
% 1.52/0.57  % (16141)Time elapsed: 0.133 s
% 1.52/0.57  % (16141)------------------------------
% 1.52/0.57  % (16141)------------------------------
% 1.52/0.57  % (16136)Refutation found. Thanks to Tanya!
% 1.52/0.57  % SZS status Theorem for theBenchmark
% 1.52/0.57  % (16146)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.52/0.57  % (16142)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.52/0.57  % SZS output start Proof for theBenchmark
% 1.52/0.57  fof(f282,plain,(
% 1.52/0.57    $false),
% 1.52/0.57    inference(avatar_sat_refutation,[],[f250,f261,f273,f281])).
% 1.52/0.57  fof(f281,plain,(
% 1.52/0.57    ~spl2_24),
% 1.52/0.57    inference(avatar_contradiction_clause,[],[f279])).
% 1.52/0.57  fof(f279,plain,(
% 1.52/0.57    $false | ~spl2_24),
% 1.52/0.57    inference(unit_resulting_resolution,[],[f41,f39,f110,f70,f118,f249])).
% 1.52/0.57  fof(f249,plain,(
% 1.52/0.57    ( ! [X5] : (v2_tex_2(k1_tarski(sK1),X5) | ~m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(X5))) | v2_struct_0(X5) | ~m1_pre_topc(k1_tex_2(sK0,sK1),X5) | ~l1_pre_topc(X5)) ) | ~spl2_24),
% 1.52/0.57    inference(avatar_component_clause,[],[f248])).
% 1.52/0.57  fof(f248,plain,(
% 1.52/0.57    spl2_24 <=> ! [X5] : (~m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(X5))) | v2_tex_2(k1_tarski(sK1),X5) | v2_struct_0(X5) | ~m1_pre_topc(k1_tex_2(sK0,sK1),X5) | ~l1_pre_topc(X5))),
% 1.52/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).
% 1.52/0.57  fof(f118,plain,(
% 1.52/0.57    m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.52/0.57    inference(unit_resulting_resolution,[],[f106,f52])).
% 1.52/0.57  fof(f52,plain,(
% 1.52/0.57    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))) )),
% 1.52/0.57    inference(cnf_transformation,[],[f30])).
% 1.52/0.57  fof(f30,plain,(
% 1.52/0.57    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 1.52/0.57    inference(ennf_transformation,[],[f2])).
% 1.52/0.57  fof(f2,axiom,(
% 1.52/0.57    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 1.52/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).
% 1.52/0.57  fof(f106,plain,(
% 1.52/0.57    r2_hidden(sK1,u1_struct_0(sK0))),
% 1.52/0.57    inference(unit_resulting_resolution,[],[f37,f104,f56])).
% 1.52/0.57  fof(f56,plain,(
% 1.52/0.57    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X0,X1) | r2_hidden(X0,X1)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f34])).
% 1.52/0.57  fof(f34,plain,(
% 1.52/0.57    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.52/0.57    inference(flattening,[],[f33])).
% 1.52/0.57  fof(f33,plain,(
% 1.52/0.57    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.52/0.57    inference(ennf_transformation,[],[f3])).
% 1.52/0.57  fof(f3,axiom,(
% 1.52/0.57    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.52/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 1.52/0.57  fof(f104,plain,(
% 1.52/0.57    ~v1_xboole_0(u1_struct_0(sK0))),
% 1.52/0.57    inference(unit_resulting_resolution,[],[f71,f67,f50])).
% 1.52/0.57  fof(f50,plain,(
% 1.52/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1) | ~v1_xboole_0(X2)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f27])).
% 1.52/0.57  fof(f27,plain,(
% 1.52/0.57    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.52/0.57    inference(ennf_transformation,[],[f4])).
% 1.52/0.57  fof(f4,axiom,(
% 1.52/0.57    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.52/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 1.52/0.57  fof(f67,plain,(
% 1.52/0.57    m1_subset_1(k1_connsp_2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.52/0.57    inference(unit_resulting_resolution,[],[f40,f39,f41,f37,f51])).
% 1.52/0.57  fof(f51,plain,(
% 1.52/0.57    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 1.52/0.57    inference(cnf_transformation,[],[f29])).
% 1.52/0.57  fof(f29,plain,(
% 1.52/0.57    ! [X0,X1] : (m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.52/0.57    inference(flattening,[],[f28])).
% 1.52/0.57  fof(f28,plain,(
% 1.52/0.57    ! [X0,X1] : (m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.52/0.57    inference(ennf_transformation,[],[f7])).
% 1.52/0.57  fof(f7,axiom,(
% 1.52/0.57    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.52/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_connsp_2)).
% 1.52/0.57  fof(f40,plain,(
% 1.52/0.57    v2_pre_topc(sK0)),
% 1.52/0.57    inference(cnf_transformation,[],[f16])).
% 1.52/0.57  fof(f16,plain,(
% 1.52/0.57    ? [X0] : (? [X1] : (~v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.52/0.57    inference(flattening,[],[f15])).
% 1.52/0.57  fof(f15,plain,(
% 1.52/0.57    ? [X0] : (? [X1] : (~v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.52/0.57    inference(ennf_transformation,[],[f14])).
% 1.52/0.57  fof(f14,negated_conjecture,(
% 1.52/0.57    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)))),
% 1.52/0.57    inference(negated_conjecture,[],[f13])).
% 1.52/0.57  fof(f13,conjecture,(
% 1.52/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)))),
% 1.52/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).
% 1.52/0.57  fof(f71,plain,(
% 1.52/0.57    r2_hidden(sK1,k1_connsp_2(sK0,sK1))),
% 1.52/0.57    inference(unit_resulting_resolution,[],[f40,f39,f41,f37,f57])).
% 1.52/0.57  fof(f57,plain,(
% 1.52/0.57    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | r2_hidden(X1,k1_connsp_2(X0,X1))) )),
% 1.52/0.57    inference(cnf_transformation,[],[f36])).
% 1.52/0.57  fof(f36,plain,(
% 1.52/0.57    ! [X0] : (! [X1] : (r2_hidden(X1,k1_connsp_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.52/0.57    inference(flattening,[],[f35])).
% 1.52/0.57  fof(f35,plain,(
% 1.52/0.57    ! [X0] : (! [X1] : (r2_hidden(X1,k1_connsp_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.52/0.57    inference(ennf_transformation,[],[f8])).
% 1.52/0.57  fof(f8,axiom,(
% 1.52/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r2_hidden(X1,k1_connsp_2(X0,X1))))),
% 1.52/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_connsp_2)).
% 1.52/0.57  fof(f37,plain,(
% 1.52/0.57    m1_subset_1(sK1,u1_struct_0(sK0))),
% 1.52/0.57    inference(cnf_transformation,[],[f16])).
% 1.52/0.57  fof(f70,plain,(
% 1.52/0.57    m1_pre_topc(k1_tex_2(sK0,sK1),sK0)),
% 1.52/0.57    inference(unit_resulting_resolution,[],[f41,f39,f37,f55])).
% 1.52/0.57  fof(f55,plain,(
% 1.52/0.57    ( ! [X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | m1_pre_topc(k1_tex_2(X0,X1),X0)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f32])).
% 1.52/0.57  fof(f32,plain,(
% 1.52/0.57    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.52/0.57    inference(flattening,[],[f31])).
% 1.52/0.57  fof(f31,plain,(
% 1.52/0.57    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.52/0.57    inference(ennf_transformation,[],[f10])).
% 1.52/0.57  fof(f10,axiom,(
% 1.52/0.57    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 1.52/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tex_2)).
% 1.52/0.57  fof(f110,plain,(
% 1.52/0.57    ~v2_tex_2(k1_tarski(sK1),sK0)),
% 1.52/0.57    inference(backward_demodulation,[],[f38,f107])).
% 1.52/0.57  fof(f107,plain,(
% 1.52/0.57    k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1)),
% 1.52/0.57    inference(unit_resulting_resolution,[],[f37,f104,f44])).
% 1.52/0.57  fof(f44,plain,(
% 1.52/0.57    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k1_tarski(X1)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f20])).
% 1.52/0.57  fof(f20,plain,(
% 1.52/0.57    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.52/0.57    inference(flattening,[],[f19])).
% 1.52/0.57  fof(f19,plain,(
% 1.52/0.57    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.52/0.57    inference(ennf_transformation,[],[f6])).
% 1.52/0.57  fof(f6,axiom,(
% 1.52/0.57    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 1.52/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 1.52/0.57  fof(f38,plain,(
% 1.52/0.57    ~v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK1),sK0)),
% 1.52/0.57    inference(cnf_transformation,[],[f16])).
% 1.52/0.57  fof(f39,plain,(
% 1.52/0.57    ~v2_struct_0(sK0)),
% 1.52/0.57    inference(cnf_transformation,[],[f16])).
% 1.52/0.57  fof(f41,plain,(
% 1.52/0.57    l1_pre_topc(sK0)),
% 1.52/0.57    inference(cnf_transformation,[],[f16])).
% 1.52/0.57  fof(f273,plain,(
% 1.52/0.57    ~spl2_23),
% 1.52/0.57    inference(avatar_contradiction_clause,[],[f268])).
% 1.52/0.57  fof(f268,plain,(
% 1.52/0.57    $false | ~spl2_23),
% 1.52/0.57    inference(unit_resulting_resolution,[],[f39,f41,f37,f246,f53])).
% 1.52/0.57  fof(f53,plain,(
% 1.52/0.57    ( ! [X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v2_struct_0(k1_tex_2(X0,X1))) )),
% 1.52/0.57    inference(cnf_transformation,[],[f32])).
% 1.52/0.57  fof(f246,plain,(
% 1.52/0.57    v2_struct_0(k1_tex_2(sK0,sK1)) | ~spl2_23),
% 1.52/0.57    inference(avatar_component_clause,[],[f244])).
% 1.52/0.57  fof(f244,plain,(
% 1.52/0.57    spl2_23 <=> v2_struct_0(k1_tex_2(sK0,sK1))),
% 1.52/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).
% 1.52/0.57  fof(f261,plain,(
% 1.52/0.57    spl2_22),
% 1.52/0.57    inference(avatar_contradiction_clause,[],[f256])).
% 1.52/0.57  fof(f256,plain,(
% 1.52/0.57    $false | spl2_22),
% 1.52/0.57    inference(unit_resulting_resolution,[],[f39,f41,f79,f37,f242,f48])).
% 1.52/0.57  fof(f48,plain,(
% 1.52/0.57    ( ! [X0,X1] : (v1_tdlat_3(k1_tex_2(X0,X1)) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v2_pre_topc(k1_tex_2(X0,X1)) | v2_struct_0(X0)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f26])).
% 1.52/0.57  fof(f26,plain,(
% 1.52/0.57    ! [X0] : (! [X1] : ((v2_tdlat_3(k1_tex_2(X0,X1)) & v1_tdlat_3(k1_tex_2(X0,X1))) | ~v2_pre_topc(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.52/0.57    inference(flattening,[],[f25])).
% 1.52/0.57  fof(f25,plain,(
% 1.52/0.57    ! [X0] : (! [X1] : (((v2_tdlat_3(k1_tex_2(X0,X1)) & v1_tdlat_3(k1_tex_2(X0,X1))) | ~v2_pre_topc(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.52/0.57    inference(ennf_transformation,[],[f11])).
% 1.52/0.57  fof(f11,axiom,(
% 1.52/0.57    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v2_pre_topc(k1_tex_2(X0,X1)) => (v2_tdlat_3(k1_tex_2(X0,X1)) & v1_tdlat_3(k1_tex_2(X0,X1))))))),
% 1.52/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tex_2)).
% 1.52/0.57  fof(f242,plain,(
% 1.52/0.57    ~v1_tdlat_3(k1_tex_2(sK0,sK1)) | spl2_22),
% 1.52/0.57    inference(avatar_component_clause,[],[f240])).
% 1.52/0.57  fof(f240,plain,(
% 1.52/0.57    spl2_22 <=> v1_tdlat_3(k1_tex_2(sK0,sK1))),
% 1.52/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 1.52/0.57  fof(f79,plain,(
% 1.52/0.57    v2_pre_topc(k1_tex_2(sK0,sK1))),
% 1.52/0.57    inference(unit_resulting_resolution,[],[f40,f41,f70,f47])).
% 1.52/0.57  % (16142)Refutation not found, incomplete strategy% (16142)------------------------------
% 1.52/0.57  % (16142)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.57  % (16142)Termination reason: Refutation not found, incomplete strategy
% 1.52/0.57  
% 1.52/0.57  % (16142)Memory used [KB]: 10618
% 1.52/0.57  % (16142)Time elapsed: 0.148 s
% 1.52/0.57  % (16142)------------------------------
% 1.52/0.57  % (16142)------------------------------
% 1.52/0.57  fof(f47,plain,(
% 1.52/0.57    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_pre_topc(X1)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f24])).
% 1.52/0.57  fof(f24,plain,(
% 1.52/0.57    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.52/0.57    inference(flattening,[],[f23])).
% 1.52/0.57  fof(f23,plain,(
% 1.52/0.57    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.52/0.57    inference(ennf_transformation,[],[f5])).
% 1.52/0.57  fof(f5,axiom,(
% 1.52/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 1.52/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).
% 1.52/0.57  fof(f250,plain,(
% 1.52/0.57    ~spl2_22 | spl2_23 | spl2_24),
% 1.52/0.57    inference(avatar_split_clause,[],[f137,f248,f244,f240])).
% 1.52/0.57  fof(f137,plain,(
% 1.52/0.57    ( ! [X5] : (~m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(X5))) | ~l1_pre_topc(X5) | v2_struct_0(k1_tex_2(sK0,sK1)) | ~m1_pre_topc(k1_tex_2(sK0,sK1),X5) | v2_struct_0(X5) | ~v1_tdlat_3(k1_tex_2(sK0,sK1)) | v2_tex_2(k1_tarski(sK1),X5)) )),
% 1.52/0.57    inference(superposition,[],[f59,f111])).
% 1.52/0.57  fof(f111,plain,(
% 1.52/0.57    u1_struct_0(k1_tex_2(sK0,sK1)) = k1_tarski(sK1)),
% 1.52/0.57    inference(backward_demodulation,[],[f78,f107])).
% 1.52/0.57  fof(f78,plain,(
% 1.52/0.57    k6_domain_1(u1_struct_0(sK0),sK1) = u1_struct_0(k1_tex_2(sK0,sK1))),
% 1.52/0.57    inference(unit_resulting_resolution,[],[f41,f39,f69,f68,f37,f70,f60])).
% 1.52/0.57  fof(f60,plain,(
% 1.52/0.57    ( ! [X0,X1] : (~v1_pre_topc(k1_tex_2(X0,X1)) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(k1_tex_2(X0,X1)) | v2_struct_0(X0) | ~m1_pre_topc(k1_tex_2(X0,X1),X0) | k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(k1_tex_2(X0,X1))) )),
% 1.52/0.57    inference(equality_resolution,[],[f46])).
% 1.52/0.57  fof(f46,plain,(
% 1.52/0.57    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X2,X0) | u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) | k1_tex_2(X0,X1) != X2) )),
% 1.52/0.57    inference(cnf_transformation,[],[f22])).
% 1.52/0.57  fof(f22,plain,(
% 1.52/0.57    ! [X0] : (! [X1] : (! [X2] : ((k1_tex_2(X0,X1) = X2 <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.52/0.57    inference(flattening,[],[f21])).
% 1.52/0.57  fof(f21,plain,(
% 1.52/0.57    ! [X0] : (! [X1] : (! [X2] : ((k1_tex_2(X0,X1) = X2 <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)) | (~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.52/0.57    inference(ennf_transformation,[],[f9])).
% 1.52/0.57  fof(f9,axiom,(
% 1.52/0.57    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => (k1_tex_2(X0,X1) = X2 <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)))))),
% 1.52/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tex_2)).
% 1.52/0.57  fof(f68,plain,(
% 1.52/0.57    ~v2_struct_0(k1_tex_2(sK0,sK1))),
% 1.52/0.57    inference(unit_resulting_resolution,[],[f41,f39,f37,f53])).
% 1.52/0.57  fof(f69,plain,(
% 1.52/0.57    v1_pre_topc(k1_tex_2(sK0,sK1))),
% 1.52/0.57    inference(unit_resulting_resolution,[],[f41,f39,f37,f54])).
% 1.52/0.57  fof(f54,plain,(
% 1.52/0.57    ( ! [X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v1_pre_topc(k1_tex_2(X0,X1))) )),
% 1.52/0.57    inference(cnf_transformation,[],[f32])).
% 1.52/0.57  fof(f59,plain,(
% 1.52/0.57    ( ! [X0,X1] : (~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X0) | ~v1_tdlat_3(X1) | v2_tex_2(u1_struct_0(X1),X0)) )),
% 1.52/0.57    inference(equality_resolution,[],[f42])).
% 1.52/0.57  fof(f42,plain,(
% 1.52/0.57    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X1) != X2 | ~v1_tdlat_3(X1) | v2_tex_2(X2,X0)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f18])).
% 1.52/0.57  fof(f18,plain,(
% 1.52/0.57    ! [X0] : (! [X1] : (! [X2] : ((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.52/0.57    inference(flattening,[],[f17])).
% 1.52/0.57  fof(f17,plain,(
% 1.52/0.57    ! [X0] : (! [X1] : (! [X2] : (((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.52/0.57    inference(ennf_transformation,[],[f12])).
% 1.52/0.57  fof(f12,axiom,(
% 1.52/0.57    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => (v2_tex_2(X2,X0) <=> v1_tdlat_3(X1))))))),
% 1.52/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_tex_2)).
% 1.52/0.57  % SZS output end Proof for theBenchmark
% 1.52/0.57  % (16136)------------------------------
% 1.52/0.57  % (16136)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.57  % (16136)Termination reason: Refutation
% 1.52/0.57  
% 1.52/0.57  % (16136)Memory used [KB]: 6396
% 1.52/0.57  % (16136)Time elapsed: 0.131 s
% 1.52/0.57  % (16136)------------------------------
% 1.52/0.57  % (16136)------------------------------
% 1.52/0.58  % (16127)Success in time 0.208 s
%------------------------------------------------------------------------------
