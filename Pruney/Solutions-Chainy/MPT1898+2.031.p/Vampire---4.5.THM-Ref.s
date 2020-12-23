%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:23 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 160 expanded)
%              Number of leaves         :   12 (  55 expanded)
%              Depth                    :   22
%              Number of atoms          :  403 ( 691 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f183,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f39,f44,f49,f54,f71,f82,f161,f180])).

fof(f180,plain,
    ( spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | spl3_16 ),
    inference(avatar_contradiction_clause,[],[f179])).

fof(f179,plain,
    ( $false
    | spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | spl3_16 ),
    inference(subsumption_resolution,[],[f178,f38])).

fof(f38,plain,
    ( ~ v2_struct_0(sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f36])).

fof(f36,plain,
    ( spl3_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f178,plain,
    ( v2_struct_0(sK0)
    | ~ spl3_2
    | ~ spl3_4
    | spl3_16 ),
    inference(subsumption_resolution,[],[f177,f53])).

fof(f53,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl3_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f177,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_2
    | spl3_16 ),
    inference(subsumption_resolution,[],[f175,f43])).

fof(f43,plain,
    ( v2_pre_topc(sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f41])).

fof(f41,plain,
    ( spl3_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f175,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl3_16 ),
    inference(resolution,[],[f160,f31])).

fof(f31,plain,(
    ! [X0] :
      ( v1_tdlat_3(sK2(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v2_tdlat_3(X1)
          & v1_tdlat_3(X1)
          & v2_pre_topc(X1)
          & v1_pre_topc(X1)
          & ~ v2_struct_0(X1)
          & m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v2_tdlat_3(X1)
          & v1_tdlat_3(X1)
          & v2_pre_topc(X1)
          & v1_pre_topc(X1)
          & ~ v2_struct_0(X1)
          & m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v2_tdlat_3(X1)
          & v1_tdlat_3(X1)
          & v2_pre_topc(X1)
          & v1_pre_topc(X1)
          & ~ v2_struct_0(X1)
          & m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc11_tex_2)).

fof(f160,plain,
    ( ~ v1_tdlat_3(sK2(sK0))
    | spl3_16 ),
    inference(avatar_component_clause,[],[f158])).

fof(f158,plain,
    ( spl3_16
  <=> v1_tdlat_3(sK2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f161,plain,
    ( ~ spl3_16
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | spl3_5
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f156,f79,f68,f51,f46,f41,f36,f158])).

fof(f46,plain,
    ( spl3_3
  <=> v3_tdlat_3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f68,plain,
    ( spl3_5
  <=> v2_struct_0(sK2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f79,plain,
    ( spl3_6
  <=> m1_pre_topc(sK2(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f156,plain,
    ( ~ v1_tdlat_3(sK2(sK0))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | spl3_5
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f155,f70])).

fof(f70,plain,
    ( ~ v2_struct_0(sK2(sK0))
    | spl3_5 ),
    inference(avatar_component_clause,[],[f68])).

fof(f155,plain,
    ( ~ v1_tdlat_3(sK2(sK0))
    | v2_struct_0(sK2(sK0))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(resolution,[],[f154,f81])).

fof(f81,plain,
    ( m1_pre_topc(sK2(sK0),sK0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f79])).

fof(f154,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ v1_tdlat_3(X0)
        | v2_struct_0(X0) )
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f153,f53])).

fof(f153,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ v1_tdlat_3(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK0) )
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(duplicate_literal_removal,[],[f152])).

fof(f152,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ v1_tdlat_3(X0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ l1_pre_topc(sK0) )
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(resolution,[],[f133,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l17_tex_2)).

% (9161)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
fof(f133,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_pre_topc(X0,sK0)
        | ~ v1_tdlat_3(X0)
        | v2_struct_0(X0) )
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(resolution,[],[f127,f83])).

fof(f83,plain,
    ( ! [X0] :
        ( v2_tex_2(u1_struct_0(X0),sK0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ v1_tdlat_3(X0)
        | v2_struct_0(X0) )
    | spl3_1
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f58,f53])).

fof(f58,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ v1_tdlat_3(X0)
        | v2_tex_2(u1_struct_0(X0),sK0) )
    | spl3_1 ),
    inference(subsumption_resolution,[],[f57,f21])).

fof(f57,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_tdlat_3(X0)
        | v2_tex_2(u1_struct_0(X0),sK0) )
    | spl3_1 ),
    inference(resolution,[],[f38,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tdlat_3(X1)
      | v2_tex_2(u1_struct_0(X1),X0) ) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X1) != X2
      | ~ v1_tdlat_3(X1)
      | v2_tex_2(X2,X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
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
    inference(flattening,[],[f10])).

fof(f10,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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

fof(f127,plain,
    ( ! [X0] :
        ( ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f126,f38])).

fof(f126,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X0,sK0)
        | v2_struct_0(sK0) )
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f125,f53])).

fof(f125,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X0,sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f124,f48])).

fof(f48,plain,
    ( v3_tdlat_3(sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f46])).

fof(f124,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X0,sK0)
        | ~ v3_tdlat_3(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f123,f43])).

fof(f123,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X0,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ v3_tdlat_3(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(duplicate_literal_removal,[],[f122])).

% (9150)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
fof(f122,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X0,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ v3_tdlat_3(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X0,sK0)
        | v2_struct_0(sK0) )
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(resolution,[],[f104,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( v3_tex_2(X2,X0)
              & r1_tarski(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( v3_tex_2(X2,X0)
              & r1_tarski(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ~ ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ~ ( v3_tex_2(X2,X0)
                      & r1_tarski(X1,X2) ) )
              & v2_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tex_2)).

fof(f104,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X0,sK0) )
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(resolution,[],[f103,f16])).

fof(f16,plain,(
    ! [X1] :
      ( ~ v3_tex_2(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ! [X1] :
          ( ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ! [X1] :
          ( ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v3_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ? [X1] :
            ( v3_tex_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v3_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_tex_2)).

fof(f103,plain,
    ( ! [X1] :
        ( v3_tex_2(sK1(sK0,X1),sK0)
        | ~ v2_tex_2(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f64,f53])).

fof(f64,plain,
    ( ! [X1] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X1,sK0)
        | v3_tex_2(sK1(sK0,X1),sK0) )
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f63,f38])).

fof(f63,plain,
    ( ! [X1] :
        ( v2_struct_0(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X1,sK0)
        | v3_tex_2(sK1(sK0,X1),sK0) )
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f60,f43])).

fof(f60,plain,
    ( ! [X1] :
        ( ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X1,sK0)
        | v3_tex_2(sK1(sK0,X1),sK0) )
    | ~ spl3_3 ),
    inference(resolution,[],[f48,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | v3_tex_2(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f82,plain,
    ( spl3_6
    | spl3_1
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f77,f51,f41,f36,f79])).

fof(f77,plain,
    ( m1_pre_topc(sK2(sK0),sK0)
    | spl3_1
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f76,f53])).

fof(f76,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_pre_topc(sK2(sK0),sK0)
    | spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f55,f43])).

fof(f55,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | m1_pre_topc(sK2(sK0),sK0)
    | spl3_1 ),
    inference(resolution,[],[f38,f27])).

fof(f27,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | m1_pre_topc(sK2(X0),X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f71,plain,
    ( ~ spl3_5
    | spl3_1
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f66,f51,f41,f36,f68])).

fof(f66,plain,
    ( ~ v2_struct_0(sK2(sK0))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f65,f53])).

fof(f65,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_struct_0(sK2(sK0))
    | spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f56,f43])).

fof(f56,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_struct_0(sK2(sK0))
    | spl3_1 ),
    inference(resolution,[],[f38,f28])).

fof(f28,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_struct_0(sK2(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f54,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f20,f51])).

fof(f20,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f49,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f19,f46])).

fof(f19,plain,(
    v3_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f44,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f18,f41])).

fof(f18,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f39,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f17,f36])).

fof(f17,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:41:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (9151)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.47  % (9148)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.47  % (9151)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f183,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f39,f44,f49,f54,f71,f82,f161,f180])).
% 0.21/0.47  fof(f180,plain,(
% 0.21/0.47    spl3_1 | ~spl3_2 | ~spl3_4 | spl3_16),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f179])).
% 0.21/0.47  fof(f179,plain,(
% 0.21/0.47    $false | (spl3_1 | ~spl3_2 | ~spl3_4 | spl3_16)),
% 0.21/0.47    inference(subsumption_resolution,[],[f178,f38])).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    ~v2_struct_0(sK0) | spl3_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f36])).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    spl3_1 <=> v2_struct_0(sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.47  fof(f178,plain,(
% 0.21/0.47    v2_struct_0(sK0) | (~spl3_2 | ~spl3_4 | spl3_16)),
% 0.21/0.47    inference(subsumption_resolution,[],[f177,f53])).
% 0.21/0.47  fof(f53,plain,(
% 0.21/0.47    l1_pre_topc(sK0) | ~spl3_4),
% 0.21/0.47    inference(avatar_component_clause,[],[f51])).
% 0.21/0.47  fof(f51,plain,(
% 0.21/0.47    spl3_4 <=> l1_pre_topc(sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.47  fof(f177,plain,(
% 0.21/0.47    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | (~spl3_2 | spl3_16)),
% 0.21/0.47    inference(subsumption_resolution,[],[f175,f43])).
% 0.21/0.47  fof(f43,plain,(
% 0.21/0.47    v2_pre_topc(sK0) | ~spl3_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f41])).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    spl3_2 <=> v2_pre_topc(sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.47  fof(f175,plain,(
% 0.21/0.47    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | spl3_16),
% 0.21/0.47    inference(resolution,[],[f160,f31])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    ( ! [X0] : (v1_tdlat_3(sK2(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ! [X0] : (? [X1] : (v2_tdlat_3(X1) & v1_tdlat_3(X1) & v2_pre_topc(X1) & v1_pre_topc(X1) & ~v2_struct_0(X1) & m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ! [X0] : (? [X1] : (v2_tdlat_3(X1) & v1_tdlat_3(X1) & v2_pre_topc(X1) & v1_pre_topc(X1) & ~v2_struct_0(X1) & m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (v2_tdlat_3(X1) & v1_tdlat_3(X1) & v2_pre_topc(X1) & v1_pre_topc(X1) & ~v2_struct_0(X1) & m1_pre_topc(X1,X0)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc11_tex_2)).
% 0.21/0.47  fof(f160,plain,(
% 0.21/0.47    ~v1_tdlat_3(sK2(sK0)) | spl3_16),
% 0.21/0.47    inference(avatar_component_clause,[],[f158])).
% 0.21/0.47  fof(f158,plain,(
% 0.21/0.47    spl3_16 <=> v1_tdlat_3(sK2(sK0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.47  fof(f161,plain,(
% 0.21/0.47    ~spl3_16 | spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | spl3_5 | ~spl3_6),
% 0.21/0.47    inference(avatar_split_clause,[],[f156,f79,f68,f51,f46,f41,f36,f158])).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    spl3_3 <=> v3_tdlat_3(sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.47  fof(f68,plain,(
% 0.21/0.47    spl3_5 <=> v2_struct_0(sK2(sK0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.47  fof(f79,plain,(
% 0.21/0.47    spl3_6 <=> m1_pre_topc(sK2(sK0),sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.47  fof(f156,plain,(
% 0.21/0.47    ~v1_tdlat_3(sK2(sK0)) | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | spl3_5 | ~spl3_6)),
% 0.21/0.47    inference(subsumption_resolution,[],[f155,f70])).
% 0.21/0.47  fof(f70,plain,(
% 0.21/0.47    ~v2_struct_0(sK2(sK0)) | spl3_5),
% 0.21/0.47    inference(avatar_component_clause,[],[f68])).
% 0.21/0.47  fof(f155,plain,(
% 0.21/0.47    ~v1_tdlat_3(sK2(sK0)) | v2_struct_0(sK2(sK0)) | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_6)),
% 0.21/0.47    inference(resolution,[],[f154,f81])).
% 0.21/0.47  fof(f81,plain,(
% 0.21/0.47    m1_pre_topc(sK2(sK0),sK0) | ~spl3_6),
% 0.21/0.47    inference(avatar_component_clause,[],[f79])).
% 0.21/0.47  fof(f154,plain,(
% 0.21/0.47    ( ! [X0] : (~m1_pre_topc(X0,sK0) | ~v1_tdlat_3(X0) | v2_struct_0(X0)) ) | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4)),
% 0.21/0.47    inference(subsumption_resolution,[],[f153,f53])).
% 0.21/0.47  fof(f153,plain,(
% 0.21/0.47    ( ! [X0] : (~m1_pre_topc(X0,sK0) | ~v1_tdlat_3(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0)) ) | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4)),
% 0.21/0.47    inference(duplicate_literal_removal,[],[f152])).
% 0.21/0.47  fof(f152,plain,(
% 0.21/0.47    ( ! [X0] : (~m1_pre_topc(X0,sK0) | ~v1_tdlat_3(X0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | ~l1_pre_topc(sK0)) ) | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4)),
% 0.21/0.47    inference(resolution,[],[f133,f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l17_tex_2)).
% 0.21/0.47  % (9161)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.47  fof(f133,plain,(
% 0.21/0.47    ( ! [X0] : (~m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_pre_topc(X0,sK0) | ~v1_tdlat_3(X0) | v2_struct_0(X0)) ) | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4)),
% 0.21/0.47    inference(resolution,[],[f127,f83])).
% 0.21/0.47  fof(f83,plain,(
% 0.21/0.47    ( ! [X0] : (v2_tex_2(u1_struct_0(X0),sK0) | ~m1_pre_topc(X0,sK0) | ~v1_tdlat_3(X0) | v2_struct_0(X0)) ) | (spl3_1 | ~spl3_4)),
% 0.21/0.47    inference(subsumption_resolution,[],[f58,f53])).
% 0.21/0.47  fof(f58,plain,(
% 0.21/0.47    ( ! [X0] : (~l1_pre_topc(sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | ~v1_tdlat_3(X0) | v2_tex_2(u1_struct_0(X0),sK0)) ) | spl3_1),
% 0.21/0.47    inference(subsumption_resolution,[],[f57,f21])).
% 0.21/0.47  fof(f57,plain,(
% 0.21/0.47    ( ! [X0] : (~l1_pre_topc(sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | ~m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_tdlat_3(X0) | v2_tex_2(u1_struct_0(X0),sK0)) ) | spl3_1),
% 0.21/0.47    inference(resolution,[],[f38,f34])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tdlat_3(X1) | v2_tex_2(u1_struct_0(X1),X0)) )),
% 0.21/0.47    inference(equality_resolution,[],[f22])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X1) != X2 | ~v1_tdlat_3(X1) | v2_tex_2(X2,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f11])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (! [X2] : ((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f10])).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (! [X2] : (((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => (v2_tex_2(X2,X0) <=> v1_tdlat_3(X1))))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_tex_2)).
% 0.21/0.47  fof(f127,plain,(
% 0.21/0.47    ( ! [X0] : (~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4)),
% 0.21/0.47    inference(subsumption_resolution,[],[f126,f38])).
% 0.21/0.47  fof(f126,plain,(
% 0.21/0.47    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X0,sK0) | v2_struct_0(sK0)) ) | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4)),
% 0.21/0.47    inference(subsumption_resolution,[],[f125,f53])).
% 0.21/0.47  fof(f125,plain,(
% 0.21/0.47    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X0,sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)) ) | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4)),
% 0.21/0.47    inference(subsumption_resolution,[],[f124,f48])).
% 0.21/0.47  fof(f48,plain,(
% 0.21/0.47    v3_tdlat_3(sK0) | ~spl3_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f46])).
% 0.21/0.47  fof(f124,plain,(
% 0.21/0.47    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X0,sK0) | ~v3_tdlat_3(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)) ) | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4)),
% 0.21/0.47    inference(subsumption_resolution,[],[f123,f43])).
% 0.21/0.47  fof(f123,plain,(
% 0.21/0.47    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X0,sK0) | ~v2_pre_topc(sK0) | ~v3_tdlat_3(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)) ) | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4)),
% 0.21/0.47    inference(duplicate_literal_removal,[],[f122])).
% 0.21/0.47  % (9150)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.47  fof(f122,plain,(
% 0.21/0.47    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X0,sK0) | ~v2_pre_topc(sK0) | ~v3_tdlat_3(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X0,sK0) | v2_struct_0(sK0)) ) | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4)),
% 0.21/0.47    inference(resolution,[],[f104,f24])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ( ! [X0,X1] : (m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~v3_tdlat_3(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | v2_struct_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f13])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (? [X2] : (v3_tex_2(X2,X0) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : ((? [X2] : ((v3_tex_2(X2,X0) & r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(v3_tex_2(X2,X0) & r1_tarski(X1,X2))) & v2_tex_2(X1,X0))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tex_2)).
% 0.21/0.47  fof(f104,plain,(
% 0.21/0.47    ( ! [X0] : (~m1_subset_1(sK1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X0,sK0)) ) | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4)),
% 0.21/0.47    inference(resolution,[],[f103,f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ( ! [X1] : (~v3_tex_2(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,plain,(
% 0.21/0.47    ? [X0] : (! [X1] : (~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f7])).
% 0.21/0.47  fof(f7,plain,(
% 0.21/0.47    ? [X0] : (! [X1] : (~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,negated_conjecture,(
% 0.21/0.47    ~! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.47    inference(negated_conjecture,[],[f5])).
% 0.21/0.47  fof(f5,conjecture,(
% 0.21/0.47    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_tex_2)).
% 0.21/0.47  fof(f103,plain,(
% 0.21/0.47    ( ! [X1] : (v3_tex_2(sK1(sK0,X1),sK0) | ~v2_tex_2(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4)),
% 0.21/0.47    inference(subsumption_resolution,[],[f64,f53])).
% 0.21/0.47  fof(f64,plain,(
% 0.21/0.47    ( ! [X1] : (~l1_pre_topc(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X1,sK0) | v3_tex_2(sK1(sK0,X1),sK0)) ) | (spl3_1 | ~spl3_2 | ~spl3_3)),
% 0.21/0.47    inference(subsumption_resolution,[],[f63,f38])).
% 0.21/0.47  fof(f63,plain,(
% 0.21/0.47    ( ! [X1] : (v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X1,sK0) | v3_tex_2(sK1(sK0,X1),sK0)) ) | (~spl3_2 | ~spl3_3)),
% 0.21/0.47    inference(subsumption_resolution,[],[f60,f43])).
% 0.21/0.47  fof(f60,plain,(
% 0.21/0.47    ( ! [X1] : (~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X1,sK0) | v3_tex_2(sK1(sK0,X1),sK0)) ) | ~spl3_3),
% 0.21/0.47    inference(resolution,[],[f48,f26])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | v3_tex_2(sK1(X0,X1),X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f13])).
% 0.21/0.47  fof(f82,plain,(
% 0.21/0.47    spl3_6 | spl3_1 | ~spl3_2 | ~spl3_4),
% 0.21/0.47    inference(avatar_split_clause,[],[f77,f51,f41,f36,f79])).
% 0.21/0.47  fof(f77,plain,(
% 0.21/0.47    m1_pre_topc(sK2(sK0),sK0) | (spl3_1 | ~spl3_2 | ~spl3_4)),
% 0.21/0.47    inference(subsumption_resolution,[],[f76,f53])).
% 0.21/0.47  fof(f76,plain,(
% 0.21/0.47    ~l1_pre_topc(sK0) | m1_pre_topc(sK2(sK0),sK0) | (spl3_1 | ~spl3_2)),
% 0.21/0.47    inference(subsumption_resolution,[],[f55,f43])).
% 0.21/0.47  fof(f55,plain,(
% 0.21/0.47    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | m1_pre_topc(sK2(sK0),sK0) | spl3_1),
% 0.21/0.47    inference(resolution,[],[f38,f27])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ( ! [X0] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | m1_pre_topc(sK2(X0),X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f15])).
% 0.21/0.47  fof(f71,plain,(
% 0.21/0.47    ~spl3_5 | spl3_1 | ~spl3_2 | ~spl3_4),
% 0.21/0.47    inference(avatar_split_clause,[],[f66,f51,f41,f36,f68])).
% 0.21/0.47  fof(f66,plain,(
% 0.21/0.47    ~v2_struct_0(sK2(sK0)) | (spl3_1 | ~spl3_2 | ~spl3_4)),
% 0.21/0.47    inference(subsumption_resolution,[],[f65,f53])).
% 0.21/0.47  fof(f65,plain,(
% 0.21/0.47    ~l1_pre_topc(sK0) | ~v2_struct_0(sK2(sK0)) | (spl3_1 | ~spl3_2)),
% 0.21/0.47    inference(subsumption_resolution,[],[f56,f43])).
% 0.21/0.47  fof(f56,plain,(
% 0.21/0.47    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v2_struct_0(sK2(sK0)) | spl3_1),
% 0.21/0.47    inference(resolution,[],[f38,f28])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    ( ! [X0] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_struct_0(sK2(X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f15])).
% 0.21/0.47  fof(f54,plain,(
% 0.21/0.47    spl3_4),
% 0.21/0.47    inference(avatar_split_clause,[],[f20,f51])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    l1_pre_topc(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f8])).
% 0.21/0.47  fof(f49,plain,(
% 0.21/0.47    spl3_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f19,f46])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    v3_tdlat_3(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f8])).
% 0.21/0.47  fof(f44,plain,(
% 0.21/0.47    spl3_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f18,f41])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    v2_pre_topc(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f8])).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    ~spl3_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f17,f36])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ~v2_struct_0(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f8])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (9151)------------------------------
% 0.21/0.47  % (9151)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (9151)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (9151)Memory used [KB]: 10618
% 0.21/0.47  % (9151)Time elapsed: 0.055 s
% 0.21/0.47  % (9151)------------------------------
% 0.21/0.47  % (9151)------------------------------
% 0.21/0.47  % (9145)Success in time 0.114 s
%------------------------------------------------------------------------------
