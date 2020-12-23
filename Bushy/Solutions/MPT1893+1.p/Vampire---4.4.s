%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tex_2__t61_tex_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:54 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 190 expanded)
%              Number of leaves         :   17 (  63 expanded)
%              Depth                    :   14
%              Number of atoms          :  378 ( 829 expanded)
%              Number of equality atoms :   22 (  27 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f236,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f93,f97,f101,f105,f113,f117,f121,f172,f206,f214,f235])).

fof(f235,plain,
    ( ~ spl6_22
    | ~ spl6_26 ),
    inference(avatar_contradiction_clause,[],[f234])).

fof(f234,plain,
    ( $false
    | ~ spl6_22
    | ~ spl6_26 ),
    inference(subsumption_resolution,[],[f231,f205])).

fof(f205,plain,
    ( v1_subset_1(sK1,sK1)
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f204])).

fof(f204,plain,
    ( spl6_22
  <=> v1_subset_1(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f231,plain,
    ( ~ v1_subset_1(sK1,sK1)
    | ~ spl6_26 ),
    inference(resolution,[],[f213,f89])).

fof(f89,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X1))
      | ~ v1_subset_1(X1,X1) ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 != X1
      | ~ v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t61_tex_2.p',d7_subset_1)).

fof(f213,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f212])).

fof(f212,plain,
    ( spl6_26
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f214,plain,
    ( spl6_26
    | ~ spl6_12
    | ~ spl6_20 ),
    inference(avatar_split_clause,[],[f173,f170,f119,f212])).

fof(f119,plain,
    ( spl6_12
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f170,plain,
    ( spl6_20
  <=> u1_struct_0(sK0) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f173,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ spl6_12
    | ~ spl6_20 ),
    inference(superposition,[],[f120,f171])).

fof(f171,plain,
    ( u1_struct_0(sK0) = sK1
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f170])).

fof(f120,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f119])).

fof(f206,plain,
    ( spl6_22
    | ~ spl6_10
    | ~ spl6_20 ),
    inference(avatar_split_clause,[],[f174,f170,f115,f204])).

fof(f115,plain,
    ( spl6_10
  <=> v1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f174,plain,
    ( v1_subset_1(sK1,sK1)
    | ~ spl6_10
    | ~ spl6_20 ),
    inference(superposition,[],[f116,f171])).

fof(f116,plain,
    ( v1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f115])).

fof(f172,plain,
    ( spl6_20
    | spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f154,f119,f111,f103,f99,f95,f91,f170])).

fof(f91,plain,
    ( spl6_1
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f95,plain,
    ( spl6_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f99,plain,
    ( spl6_4
  <=> v3_tdlat_3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f103,plain,
    ( spl6_6
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f111,plain,
    ( spl6_8
  <=> v3_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f154,plain,
    ( u1_struct_0(sK0) = sK1
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_12 ),
    inference(forward_demodulation,[],[f153,f147])).

fof(f147,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f146,f145])).

fof(f145,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f144,f100])).

fof(f100,plain,
    ( v3_tdlat_3(sK0)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f99])).

fof(f144,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ v3_tdlat_3(sK0)
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f143,f140])).

fof(f140,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f139,f55])).

fof(f55,plain,
    ( v3_pre_topc(sK1,sK0)
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_subset_1(X1,u1_struct_0(X0))
          & v3_tex_2(X1,X0)
          & ( v4_pre_topc(X1,X0)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_subset_1(X1,u1_struct_0(X0))
          & v3_tex_2(X1,X0)
          & ( v4_pre_topc(X1,X0)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v3_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ~ ( v1_subset_1(X1,u1_struct_0(X0))
                & v3_tex_2(X1,X0)
                & ( v4_pre_topc(X1,X0)
                  | v3_pre_topc(X1,X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ~ ( v1_subset_1(X1,u1_struct_0(X0))
              & v3_tex_2(X1,X0)
              & ( v4_pre_topc(X1,X0)
                | v3_pre_topc(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t61_tex_2.p',t61_tex_2)).

fof(f139,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | v3_pre_topc(sK1,sK0)
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f138,f100])).

fof(f138,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | v3_pre_topc(sK1,sK0)
    | ~ v3_tdlat_3(sK0)
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f137,f96])).

fof(f96,plain,
    ( v2_pre_topc(sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f95])).

fof(f137,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ v4_pre_topc(sK1,sK0)
    | v3_pre_topc(sK1,sK0)
    | ~ v3_tdlat_3(sK0)
    | ~ spl6_6
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f123,f104])).

fof(f104,plain,
    ( l1_pre_topc(sK0)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f103])).

fof(f123,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ v4_pre_topc(sK1,sK0)
    | v3_pre_topc(sK1,sK0)
    | ~ v3_tdlat_3(sK0)
    | ~ spl6_12 ),
    inference(resolution,[],[f120,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0)
      | v3_pre_topc(X1,X0)
      | ~ v3_tdlat_3(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
             => v3_pre_topc(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t61_tex_2.p',t24_tdlat_3)).

fof(f143,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | v4_pre_topc(sK1,sK0)
    | ~ v3_tdlat_3(sK0)
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f142,f96])).

fof(f142,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ v3_pre_topc(sK1,sK0)
    | v4_pre_topc(sK1,sK0)
    | ~ v3_tdlat_3(sK0)
    | ~ spl6_6
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f124,f104])).

fof(f124,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ v3_pre_topc(sK1,sK0)
    | v4_pre_topc(sK1,sK0)
    | ~ v3_tdlat_3(sK0)
    | ~ spl6_12 ),
    inference(resolution,[],[f120,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ v3_pre_topc(X1,X0)
      | v4_pre_topc(X1,X0)
      | ~ v3_tdlat_3(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v4_pre_topc(X1,X0)
            | ~ v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v4_pre_topc(X1,X0)
            | ~ v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
             => v4_pre_topc(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t61_tex_2.p',t23_tdlat_3)).

fof(f146,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | k2_pre_topc(sK0,sK1) = sK1
    | ~ spl6_6
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f126,f104])).

fof(f126,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v4_pre_topc(sK1,sK0)
    | k2_pre_topc(sK0,sK1) = sK1
    | ~ spl6_12 ),
    inference(resolution,[],[f120,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t61_tex_2.p',t52_pre_topc)).

fof(f153,plain,
    ( u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f152,f141])).

fof(f141,plain,
    ( v1_tops_1(sK1,sK0)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f136,f140])).

fof(f136,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | v1_tops_1(sK1,sK0)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f135,f112])).

fof(f112,plain,
    ( v3_tex_2(sK1,sK0)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f111])).

fof(f135,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | ~ v3_tex_2(sK1,sK0)
    | v1_tops_1(sK1,sK0)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f134,f92])).

fof(f92,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f91])).

fof(f134,plain,
    ( v2_struct_0(sK0)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ v3_tex_2(sK1,sK0)
    | v1_tops_1(sK1,sK0)
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f133,f104])).

fof(f133,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ v3_tex_2(sK1,sK0)
    | v1_tops_1(sK1,sK0)
    | ~ spl6_2
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f122,f96])).

fof(f122,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ v3_tex_2(sK1,sK0)
    | v1_tops_1(sK1,sK0)
    | ~ spl6_12 ),
    inference(resolution,[],[f120,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ v3_tex_2(X1,X0)
      | v1_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(X1,X0)
          | ~ v3_tex_2(X1,X0)
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(X1,X0)
          | ~ v3_tex_2(X1,X0)
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v3_tex_2(X1,X0)
              & v3_pre_topc(X1,X0) )
           => v1_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t61_tex_2.p',t47_tex_2)).

fof(f152,plain,
    ( u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ v1_tops_1(sK1,sK0)
    | ~ spl6_6
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f130,f104])).

fof(f130,plain,
    ( ~ l1_pre_topc(sK0)
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ v1_tops_1(sK1,sK0)
    | ~ spl6_12 ),
    inference(resolution,[],[f120,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | u1_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ v1_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t61_tex_2.p',d2_tops_3)).

fof(f121,plain,(
    spl6_12 ),
    inference(avatar_split_clause,[],[f56,f119])).

fof(f56,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f31])).

fof(f117,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f58,f115])).

fof(f58,plain,(
    v1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f31])).

fof(f113,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f57,f111])).

fof(f57,plain,(
    v3_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f105,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f62,f103])).

fof(f62,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f101,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f61,f99])).

fof(f61,plain,(
    v3_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f97,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f60,f95])).

fof(f60,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f93,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f59,f91])).

fof(f59,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
