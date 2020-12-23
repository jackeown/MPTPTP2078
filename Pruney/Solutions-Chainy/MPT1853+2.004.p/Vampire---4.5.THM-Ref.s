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
% DateTime   : Thu Dec  3 13:20:42 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 238 expanded)
%              Number of leaves         :   12 (  48 expanded)
%              Depth                    :   16
%              Number of atoms          :  310 ( 928 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f97,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f56,f58,f85,f96])).

fof(f96,plain,
    ( ~ spl2_1
    | spl2_2 ),
    inference(avatar_contradiction_clause,[],[f95])).

fof(f95,plain,
    ( $false
    | ~ spl2_1
    | spl2_2 ),
    inference(subsumption_resolution,[],[f94,f91])).

fof(f91,plain,
    ( ~ v7_struct_0(sK0)
    | ~ spl2_1 ),
    inference(subsumption_resolution,[],[f90,f33])).

fof(f33,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( v1_tex_2(k1_tex_2(X0,X1),X0)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_tex_2)).

fof(f90,plain,
    ( ~ v7_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl2_1 ),
    inference(subsumption_resolution,[],[f89,f64])).

fof(f64,plain,(
    ~ v2_struct_0(k1_tex_2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f63,f33])).

fof(f63,plain,
    ( v2_struct_0(sK0)
    | ~ v2_struct_0(k1_tex_2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f62,f34])).

fof(f34,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f62,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ v2_struct_0(k1_tex_2(sK0,sK1)) ),
    inference(resolution,[],[f42,f32])).

fof(f32,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v2_struct_0(k1_tex_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tex_2)).

fof(f89,plain,
    ( ~ v7_struct_0(sK0)
    | v2_struct_0(k1_tex_2(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ spl2_1 ),
    inference(subsumption_resolution,[],[f88,f73])).

fof(f73,plain,(
    m1_pre_topc(k1_tex_2(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f72,f33])).

fof(f72,plain,
    ( v2_struct_0(sK0)
    | m1_pre_topc(k1_tex_2(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f71,f34])).

fof(f71,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | m1_pre_topc(k1_tex_2(sK0,sK1),sK0) ),
    inference(resolution,[],[f44,f32])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | m1_pre_topc(k1_tex_2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f88,plain,
    ( ~ v7_struct_0(sK0)
    | ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | v2_struct_0(k1_tex_2(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ spl2_1 ),
    inference(subsumption_resolution,[],[f87,f34])).

fof(f87,plain,
    ( ~ v7_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | v2_struct_0(k1_tex_2(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ spl2_1 ),
    inference(resolution,[],[f51,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_tex_2(X1,X0)
      | ~ v7_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_tex_2(X1,X0)
            & ~ v2_struct_0(X1) )
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_tex_2(X1,X0)
            & ~ v2_struct_0(X1) )
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( ~ v2_struct_0(X1)
           => ( ~ v1_tex_2(X1,X0)
              & ~ v2_struct_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc10_tex_2)).

fof(f51,plain,
    ( v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl2_1
  <=> v1_tex_2(k1_tex_2(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f94,plain,
    ( v7_struct_0(sK0)
    | spl2_2 ),
    inference(subsumption_resolution,[],[f93,f59])).

fof(f59,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f36,f34])).

fof(f36,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f93,plain,
    ( ~ l1_struct_0(sK0)
    | v7_struct_0(sK0)
    | spl2_2 ),
    inference(resolution,[],[f92,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v7_struct_0(X0) )
     => ~ v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_struct_0)).

fof(f92,plain,
    ( v1_zfmisc_1(u1_struct_0(sK0))
    | spl2_2 ),
    inference(subsumption_resolution,[],[f61,f54])).

fof(f54,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl2_2
  <=> v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f61,plain,
    ( v1_zfmisc_1(u1_struct_0(sK0))
    | v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    inference(resolution,[],[f60,f32])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_zfmisc_1(X0)
      | v1_subset_1(k6_domain_1(X0,X1),X0) ) ),
    inference(subsumption_resolution,[],[f37,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_zfmisc_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( v1_zfmisc_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_zfmisc_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_zfmisc_1)).

fof(f37,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | v1_zfmisc_1(X0)
      | ~ m1_subset_1(X1,X0)
      | v1_subset_1(k6_domain_1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( ~ v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tex_2)).

fof(f85,plain,
    ( spl2_1
    | ~ spl2_2 ),
    inference(avatar_contradiction_clause,[],[f84])).

fof(f84,plain,
    ( $false
    | spl2_1
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f83,f79])).

fof(f79,plain,
    ( v7_struct_0(sK0)
    | spl2_1 ),
    inference(subsumption_resolution,[],[f78,f70])).

fof(f70,plain,(
    v7_struct_0(k1_tex_2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f69,f33])).

fof(f69,plain,
    ( v2_struct_0(sK0)
    | v7_struct_0(k1_tex_2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f68,f34])).

fof(f68,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v7_struct_0(k1_tex_2(sK0,sK1)) ),
    inference(resolution,[],[f46,f32])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v7_struct_0(k1_tex_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_tex_2)).

fof(f78,plain,
    ( v7_struct_0(sK0)
    | ~ v7_struct_0(k1_tex_2(sK0,sK1))
    | spl2_1 ),
    inference(subsumption_resolution,[],[f77,f50])).

fof(f50,plain,
    ( ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f49])).

fof(f77,plain,
    ( v7_struct_0(sK0)
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ v7_struct_0(k1_tex_2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f76,f64])).

fof(f76,plain,
    ( v7_struct_0(sK0)
    | v2_struct_0(k1_tex_2(sK0,sK1))
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ v7_struct_0(k1_tex_2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f75,f33])).

fof(f75,plain,
    ( v7_struct_0(sK0)
    | v2_struct_0(sK0)
    | v2_struct_0(k1_tex_2(sK0,sK1))
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ v7_struct_0(k1_tex_2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f74,f34])).

fof(f74,plain,
    ( v7_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v2_struct_0(k1_tex_2(sK0,sK1))
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ v7_struct_0(k1_tex_2(sK0,sK1)) ),
    inference(resolution,[],[f39,f73])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | v7_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v2_struct_0(X1)
      | v1_tex_2(X1,X0)
      | ~ v7_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v7_struct_0(X1)
            & ~ v2_struct_0(X1) )
          | v1_tex_2(X1,X0)
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v7_struct_0(X1)
            & ~ v2_struct_0(X1) )
          | v1_tex_2(X1,X0)
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( ( ~ v1_tex_2(X1,X0)
              & ~ v2_struct_0(X1) )
           => ( ~ v7_struct_0(X1)
              & ~ v2_struct_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc13_tex_2)).

fof(f83,plain,
    ( ~ v7_struct_0(sK0)
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f82,f33])).

fof(f82,plain,
    ( v2_struct_0(sK0)
    | ~ v7_struct_0(sK0)
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f81,f32])).

fof(f81,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ v7_struct_0(sK0)
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f80,f59])).

fof(f80,plain,
    ( ~ l1_struct_0(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ v7_struct_0(sK0)
    | ~ spl2_2 ),
    inference(resolution,[],[f40,f55])).

fof(f55,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f53])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v7_struct_0(X0)
          | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v7_struct_0(X0)
          | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ~ ( v7_struct_0(X0)
              & v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_tex_2)).

fof(f58,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f57,f53,f49])).

fof(f57,plain,
    ( ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f31,f55])).

fof(f31,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f56,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f30,f53,f49])).

fof(f30,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:33:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.43  % (11039)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.21/0.46  % (11040)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.21/0.46  % (11040)Refutation not found, incomplete strategy% (11040)------------------------------
% 0.21/0.46  % (11040)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (11040)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.46  
% 0.21/0.46  % (11040)Memory used [KB]: 5373
% 0.21/0.46  % (11040)Time elapsed: 0.006 s
% 0.21/0.46  % (11040)------------------------------
% 0.21/0.46  % (11040)------------------------------
% 0.21/0.47  % (11032)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.21/0.47  % (11032)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f97,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f56,f58,f85,f96])).
% 0.21/0.47  fof(f96,plain,(
% 0.21/0.47    ~spl2_1 | spl2_2),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f95])).
% 0.21/0.47  fof(f95,plain,(
% 0.21/0.47    $false | (~spl2_1 | spl2_2)),
% 0.21/0.47    inference(subsumption_resolution,[],[f94,f91])).
% 0.21/0.47  fof(f91,plain,(
% 0.21/0.47    ~v7_struct_0(sK0) | ~spl2_1),
% 0.21/0.47    inference(subsumption_resolution,[],[f90,f33])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    ~v2_struct_0(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f13])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f11])).
% 0.21/0.47  fof(f11,negated_conjecture,(
% 0.21/0.47    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 0.21/0.47    inference(negated_conjecture,[],[f10])).
% 0.21/0.47  fof(f10,conjecture,(
% 0.21/0.47    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_tex_2)).
% 0.21/0.47  fof(f90,plain,(
% 0.21/0.47    ~v7_struct_0(sK0) | v2_struct_0(sK0) | ~spl2_1),
% 0.21/0.47    inference(subsumption_resolution,[],[f89,f64])).
% 0.21/0.47  fof(f64,plain,(
% 0.21/0.47    ~v2_struct_0(k1_tex_2(sK0,sK1))),
% 0.21/0.47    inference(subsumption_resolution,[],[f63,f33])).
% 0.21/0.47  fof(f63,plain,(
% 0.21/0.47    v2_struct_0(sK0) | ~v2_struct_0(k1_tex_2(sK0,sK1))),
% 0.21/0.47    inference(subsumption_resolution,[],[f62,f34])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    l1_pre_topc(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f13])).
% 0.21/0.47  fof(f62,plain,(
% 0.21/0.47    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~v2_struct_0(k1_tex_2(sK0,sK1))),
% 0.21/0.47    inference(resolution,[],[f42,f32])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.47    inference(cnf_transformation,[],[f13])).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~v2_struct_0(k1_tex_2(X0,X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f27])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f26])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,axiom,(
% 0.21/0.47    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tex_2)).
% 0.21/0.47  fof(f89,plain,(
% 0.21/0.47    ~v7_struct_0(sK0) | v2_struct_0(k1_tex_2(sK0,sK1)) | v2_struct_0(sK0) | ~spl2_1),
% 0.21/0.47    inference(subsumption_resolution,[],[f88,f73])).
% 0.21/0.47  fof(f73,plain,(
% 0.21/0.47    m1_pre_topc(k1_tex_2(sK0,sK1),sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f72,f33])).
% 0.21/0.47  fof(f72,plain,(
% 0.21/0.47    v2_struct_0(sK0) | m1_pre_topc(k1_tex_2(sK0,sK1),sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f71,f34])).
% 0.21/0.47  fof(f71,plain,(
% 0.21/0.47    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | m1_pre_topc(k1_tex_2(sK0,sK1),sK0)),
% 0.21/0.47    inference(resolution,[],[f44,f32])).
% 0.21/0.47  fof(f44,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0) | m1_pre_topc(k1_tex_2(X0,X1),X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f27])).
% 0.21/0.47  fof(f88,plain,(
% 0.21/0.47    ~v7_struct_0(sK0) | ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | v2_struct_0(k1_tex_2(sK0,sK1)) | v2_struct_0(sK0) | ~spl2_1),
% 0.21/0.47    inference(subsumption_resolution,[],[f87,f34])).
% 0.21/0.47  fof(f87,plain,(
% 0.21/0.47    ~v7_struct_0(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | v2_struct_0(k1_tex_2(sK0,sK1)) | v2_struct_0(sK0) | ~spl2_1),
% 0.21/0.47    inference(resolution,[],[f51,f41])).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v1_tex_2(X1,X0) | ~v7_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | v2_struct_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f25])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : ((~v1_tex_2(X1,X0) & ~v2_struct_0(X1)) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v7_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f24])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (((~v1_tex_2(X1,X0) & ~v2_struct_0(X1)) | v2_struct_0(X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v7_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0] : ((l1_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => (~v2_struct_0(X1) => (~v1_tex_2(X1,X0) & ~v2_struct_0(X1)))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc10_tex_2)).
% 0.21/0.47  fof(f51,plain,(
% 0.21/0.47    v1_tex_2(k1_tex_2(sK0,sK1),sK0) | ~spl2_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f49])).
% 0.21/0.47  fof(f49,plain,(
% 0.21/0.47    spl2_1 <=> v1_tex_2(k1_tex_2(sK0,sK1),sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.47  fof(f94,plain,(
% 0.21/0.47    v7_struct_0(sK0) | spl2_2),
% 0.21/0.47    inference(subsumption_resolution,[],[f93,f59])).
% 0.21/0.47  fof(f59,plain,(
% 0.21/0.47    l1_struct_0(sK0)),
% 0.21/0.47    inference(resolution,[],[f36,f34])).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.47  fof(f93,plain,(
% 0.21/0.47    ~l1_struct_0(sK0) | v7_struct_0(sK0) | spl2_2),
% 0.21/0.47    inference(resolution,[],[f92,f38])).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    ( ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | v7_struct_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | v7_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | v7_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0] : ((l1_struct_0(X0) & ~v7_struct_0(X0)) => ~v1_zfmisc_1(u1_struct_0(X0)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_struct_0)).
% 0.21/0.47  fof(f92,plain,(
% 0.21/0.47    v1_zfmisc_1(u1_struct_0(sK0)) | spl2_2),
% 0.21/0.47    inference(subsumption_resolution,[],[f61,f54])).
% 0.21/0.47  fof(f54,plain,(
% 0.21/0.47    ~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | spl2_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f53])).
% 0.21/0.47  fof(f53,plain,(
% 0.21/0.47    spl2_2 <=> v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.47  fof(f61,plain,(
% 0.21/0.47    v1_zfmisc_1(u1_struct_0(sK0)) | v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))),
% 0.21/0.47    inference(resolution,[],[f60,f32])).
% 0.21/0.47  fof(f60,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | v1_zfmisc_1(X0) | v1_subset_1(k6_domain_1(X0,X1),X0)) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f37,f35])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    ( ! [X0] : (~v1_xboole_0(X0) | v1_zfmisc_1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ! [X0] : (v1_zfmisc_1(X0) | ~v1_xboole_0(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0] : (v1_xboole_0(X0) => v1_zfmisc_1(X0))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_zfmisc_1)).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v1_xboole_0(X0) | v1_zfmisc_1(X0) | ~m1_subset_1(X1,X0) | v1_subset_1(k6_domain_1(X0,X1),X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0)) | v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 0.21/0.47    inference(flattening,[],[f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0)) | (v1_zfmisc_1(X0) | v1_xboole_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,axiom,(
% 0.21/0.47    ! [X0] : ((~v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (m1_subset_1(X1,X0) => v1_subset_1(k6_domain_1(X0,X1),X0)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tex_2)).
% 0.21/0.47  fof(f85,plain,(
% 0.21/0.47    spl2_1 | ~spl2_2),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f84])).
% 0.21/0.47  fof(f84,plain,(
% 0.21/0.47    $false | (spl2_1 | ~spl2_2)),
% 0.21/0.47    inference(subsumption_resolution,[],[f83,f79])).
% 0.21/0.47  fof(f79,plain,(
% 0.21/0.47    v7_struct_0(sK0) | spl2_1),
% 0.21/0.47    inference(subsumption_resolution,[],[f78,f70])).
% 0.21/0.47  fof(f70,plain,(
% 0.21/0.47    v7_struct_0(k1_tex_2(sK0,sK1))),
% 0.21/0.47    inference(subsumption_resolution,[],[f69,f33])).
% 0.21/0.47  fof(f69,plain,(
% 0.21/0.47    v2_struct_0(sK0) | v7_struct_0(k1_tex_2(sK0,sK1))),
% 0.21/0.47    inference(subsumption_resolution,[],[f68,f34])).
% 0.21/0.47  fof(f68,plain,(
% 0.21/0.47    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v7_struct_0(k1_tex_2(sK0,sK1))),
% 0.21/0.47    inference(resolution,[],[f46,f32])).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0) | v7_struct_0(k1_tex_2(X0,X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f29])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ! [X0,X1] : ((v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f28])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    ! [X0,X1] : ((v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,axiom,(
% 0.21/0.47    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_tex_2)).
% 0.21/0.47  fof(f78,plain,(
% 0.21/0.47    v7_struct_0(sK0) | ~v7_struct_0(k1_tex_2(sK0,sK1)) | spl2_1),
% 0.21/0.47    inference(subsumption_resolution,[],[f77,f50])).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    ~v1_tex_2(k1_tex_2(sK0,sK1),sK0) | spl2_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f49])).
% 0.21/0.47  fof(f77,plain,(
% 0.21/0.47    v7_struct_0(sK0) | v1_tex_2(k1_tex_2(sK0,sK1),sK0) | ~v7_struct_0(k1_tex_2(sK0,sK1))),
% 0.21/0.47    inference(subsumption_resolution,[],[f76,f64])).
% 0.21/0.47  fof(f76,plain,(
% 0.21/0.47    v7_struct_0(sK0) | v2_struct_0(k1_tex_2(sK0,sK1)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0) | ~v7_struct_0(k1_tex_2(sK0,sK1))),
% 0.21/0.47    inference(subsumption_resolution,[],[f75,f33])).
% 0.21/0.47  fof(f75,plain,(
% 0.21/0.47    v7_struct_0(sK0) | v2_struct_0(sK0) | v2_struct_0(k1_tex_2(sK0,sK1)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0) | ~v7_struct_0(k1_tex_2(sK0,sK1))),
% 0.21/0.47    inference(subsumption_resolution,[],[f74,f34])).
% 0.21/0.47  fof(f74,plain,(
% 0.21/0.47    v7_struct_0(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v2_struct_0(k1_tex_2(sK0,sK1)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0) | ~v7_struct_0(k1_tex_2(sK0,sK1))),
% 0.21/0.47    inference(resolution,[],[f39,f73])).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | v7_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | v2_struct_0(X1) | v1_tex_2(X1,X0) | ~v7_struct_0(X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : ((~v7_struct_0(X1) & ~v2_struct_0(X1)) | v1_tex_2(X1,X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | v7_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (((~v7_struct_0(X1) & ~v2_struct_0(X1)) | (v1_tex_2(X1,X0) | v2_struct_0(X1))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | v7_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0] : ((l1_pre_topc(X0) & ~v7_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ((~v1_tex_2(X1,X0) & ~v2_struct_0(X1)) => (~v7_struct_0(X1) & ~v2_struct_0(X1)))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc13_tex_2)).
% 0.21/0.47  fof(f83,plain,(
% 0.21/0.47    ~v7_struct_0(sK0) | ~spl2_2),
% 0.21/0.47    inference(subsumption_resolution,[],[f82,f33])).
% 0.21/0.47  fof(f82,plain,(
% 0.21/0.47    v2_struct_0(sK0) | ~v7_struct_0(sK0) | ~spl2_2),
% 0.21/0.47    inference(subsumption_resolution,[],[f81,f32])).
% 0.21/0.47  fof(f81,plain,(
% 0.21/0.47    ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | ~v7_struct_0(sK0) | ~spl2_2),
% 0.21/0.47    inference(subsumption_resolution,[],[f80,f59])).
% 0.21/0.47  fof(f80,plain,(
% 0.21/0.47    ~l1_struct_0(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | ~v7_struct_0(sK0) | ~spl2_2),
% 0.21/0.47    inference(resolution,[],[f40,f55])).
% 0.21/0.47  fof(f55,plain,(
% 0.21/0.47    v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~spl2_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f53])).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~l1_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | ~v7_struct_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f23])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (~v7_struct_0(X0) | ~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f22])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : ((~v7_struct_0(X0) | ~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,axiom,(
% 0.21/0.47    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ~(v7_struct_0(X0) & v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_tex_2)).
% 0.21/0.47  fof(f58,plain,(
% 0.21/0.47    ~spl2_1 | ~spl2_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f57,f53,f49])).
% 0.21/0.47  fof(f57,plain,(
% 0.21/0.47    ~v1_tex_2(k1_tex_2(sK0,sK1),sK0) | ~spl2_2),
% 0.21/0.47    inference(subsumption_resolution,[],[f31,f55])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    ~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~v1_tex_2(k1_tex_2(sK0,sK1),sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f13])).
% 0.21/0.47  fof(f56,plain,(
% 0.21/0.47    spl2_1 | spl2_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f30,f53,f49])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f13])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (11032)------------------------------
% 0.21/0.47  % (11032)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (11032)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (11032)Memory used [KB]: 5373
% 0.21/0.47  % (11032)Time elapsed: 0.004 s
% 0.21/0.47  % (11032)------------------------------
% 0.21/0.47  % (11032)------------------------------
% 0.21/0.47  % (11025)Success in time 0.116 s
%------------------------------------------------------------------------------
