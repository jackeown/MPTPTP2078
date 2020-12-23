%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:07 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 187 expanded)
%              Number of leaves         :   20 (  67 expanded)
%              Depth                    :   11
%              Number of atoms          :  365 ( 737 expanded)
%              Number of equality atoms :   24 (  56 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f150,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f42,f47,f57,f62,f70,f77,f94,f106,f113,f126,f130,f137,f144,f149])).

fof(f149,plain,
    ( spl3_2
    | ~ spl3_4
    | ~ spl3_5
    | spl3_11
    | ~ spl3_12
    | ~ spl3_14 ),
    inference(avatar_contradiction_clause,[],[f148])).

fof(f148,plain,
    ( $false
    | spl3_2
    | ~ spl3_4
    | ~ spl3_5
    | spl3_11
    | ~ spl3_12
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f147,f117])).

fof(f117,plain,
    ( ~ v4_tex_2(k1_pre_topc(sK0,sK1),sK0)
    | spl3_11 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl3_11
  <=> v4_tex_2(k1_pre_topc(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f147,plain,
    ( v4_tex_2(k1_pre_topc(sK0,sK1),sK0)
    | spl3_2
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_12
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f146,f120])).

fof(f120,plain,
    ( m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl3_12
  <=> m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f146,plain,
    ( ~ m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
    | v4_tex_2(k1_pre_topc(sK0,sK1),sK0)
    | spl3_2
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f145,f61])).

fof(f61,plain,
    ( v3_tex_2(sK1,sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl3_5
  <=> v3_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f145,plain,
    ( ~ v3_tex_2(sK1,sK0)
    | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
    | v4_tex_2(k1_pre_topc(sK0,sK1),sK0)
    | spl3_2
    | ~ spl3_4
    | ~ spl3_14 ),
    inference(superposition,[],[f85,f143])).

fof(f143,plain,
    ( sK1 = sK2(sK0,k1_pre_topc(sK0,sK1))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f141])).

fof(f141,plain,
    ( spl3_14
  <=> sK1 = sK2(sK0,k1_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f85,plain,
    ( ! [X2] :
        ( ~ v3_tex_2(sK2(sK0,X2),sK0)
        | ~ m1_pre_topc(X2,sK0)
        | v4_tex_2(X2,sK0) )
    | spl3_2
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f65,f56])).

fof(f56,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl3_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f65,plain,
    ( ! [X2] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_pre_topc(X2,sK0)
        | ~ v3_tex_2(sK2(sK0,X2),sK0)
        | v4_tex_2(X2,sK0) )
    | spl3_2 ),
    inference(resolution,[],[f46,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v3_tex_2(sK2(X0,X1),X0)
      | v4_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_tex_2(X1,X0)
          <=> ! [X2] :
                ( v3_tex_2(X2,X0)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_tex_2(X1,X0)
          <=> ! [X2] :
                ( v3_tex_2(X2,X0)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v4_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => v3_tex_2(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_tex_2)).

fof(f46,plain,
    ( ~ v2_struct_0(sK0)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl3_2
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f144,plain,
    ( spl3_14
    | spl3_2
    | ~ spl3_4
    | ~ spl3_7
    | spl3_11
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f138,f119,f115,f74,f54,f44,f141])).

fof(f74,plain,
    ( spl3_7
  <=> sK1 = u1_struct_0(k1_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f138,plain,
    ( sK1 = sK2(sK0,k1_pre_topc(sK0,sK1))
    | spl3_2
    | ~ spl3_4
    | ~ spl3_7
    | spl3_11
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f133,f120])).

fof(f133,plain,
    ( sK1 = sK2(sK0,k1_pre_topc(sK0,sK1))
    | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
    | spl3_2
    | ~ spl3_4
    | ~ spl3_7
    | spl3_11 ),
    inference(forward_demodulation,[],[f132,f76])).

fof(f76,plain,
    ( sK1 = u1_struct_0(k1_pre_topc(sK0,sK1))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f74])).

fof(f132,plain,
    ( u1_struct_0(k1_pre_topc(sK0,sK1)) = sK2(sK0,k1_pre_topc(sK0,sK1))
    | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
    | spl3_2
    | ~ spl3_4
    | spl3_11 ),
    inference(resolution,[],[f117,f95])).

fof(f95,plain,
    ( ! [X1] :
        ( v4_tex_2(X1,sK0)
        | u1_struct_0(X1) = sK2(sK0,X1)
        | ~ m1_pre_topc(X1,sK0) )
    | spl3_2
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f64,f56])).

fof(f64,plain,
    ( ! [X1] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_pre_topc(X1,sK0)
        | u1_struct_0(X1) = sK2(sK0,X1)
        | v4_tex_2(X1,sK0) )
    | spl3_2 ),
    inference(resolution,[],[f46,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | u1_struct_0(X1) = sK2(X0,X1)
      | v4_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f137,plain,
    ( ~ spl3_4
    | ~ spl3_6
    | spl3_12 ),
    inference(avatar_contradiction_clause,[],[f136])).

fof(f136,plain,
    ( $false
    | ~ spl3_4
    | ~ spl3_6
    | spl3_12 ),
    inference(subsumption_resolution,[],[f135,f56])).

fof(f135,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl3_6
    | spl3_12 ),
    inference(subsumption_resolution,[],[f134,f69])).

fof(f69,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl3_6
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f134,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_12 ),
    inference(resolution,[],[f121,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_pre_topc)).

fof(f121,plain,
    ( ~ m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
    | spl3_12 ),
    inference(avatar_component_clause,[],[f119])).

fof(f130,plain,
    ( ~ spl3_4
    | ~ spl3_6
    | spl3_13 ),
    inference(avatar_contradiction_clause,[],[f129])).

fof(f129,plain,
    ( $false
    | ~ spl3_4
    | ~ spl3_6
    | spl3_13 ),
    inference(subsumption_resolution,[],[f128,f56])).

fof(f128,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl3_6
    | spl3_13 ),
    inference(subsumption_resolution,[],[f127,f69])).

fof(f127,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_13 ),
    inference(resolution,[],[f125,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f125,plain,
    ( ~ v1_pre_topc(k1_pre_topc(sK0,sK1))
    | spl3_13 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl3_13
  <=> v1_pre_topc(k1_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f126,plain,
    ( ~ spl3_11
    | ~ spl3_12
    | ~ spl3_13
    | ~ spl3_7
    | spl3_8 ),
    inference(avatar_split_clause,[],[f108,f87,f74,f123,f119,f115])).

fof(f87,plain,
    ( spl3_8
  <=> v2_struct_0(k1_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f108,plain,
    ( ~ v1_pre_topc(k1_pre_topc(sK0,sK1))
    | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
    | ~ v4_tex_2(k1_pre_topc(sK0,sK1),sK0)
    | ~ spl3_7
    | spl3_8 ),
    inference(subsumption_resolution,[],[f83,f89])).

fof(f89,plain,
    ( ~ v2_struct_0(k1_pre_topc(sK0,sK1))
    | spl3_8 ),
    inference(avatar_component_clause,[],[f87])).

fof(f83,plain,
    ( ~ v1_pre_topc(k1_pre_topc(sK0,sK1))
    | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
    | ~ v4_tex_2(k1_pre_topc(sK0,sK1),sK0)
    | v2_struct_0(k1_pre_topc(sK0,sK1))
    | ~ spl3_7 ),
    inference(trivial_inequality_removal,[],[f78])).

fof(f78,plain,
    ( sK1 != sK1
    | ~ v1_pre_topc(k1_pre_topc(sK0,sK1))
    | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
    | ~ v4_tex_2(k1_pre_topc(sK0,sK1),sK0)
    | v2_struct_0(k1_pre_topc(sK0,sK1))
    | ~ spl3_7 ),
    inference(superposition,[],[f20,f76])).

fof(f20,plain,(
    ! [X2] :
      ( u1_struct_0(X2) != sK1
      | ~ v1_pre_topc(X2)
      | ~ m1_pre_topc(X2,sK0)
      | ~ v4_tex_2(X2,sK0)
      | v2_struct_0(X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( u1_struct_0(X2) != X1
              | ~ v4_tex_2(X2,X0)
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          & v3_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( u1_struct_0(X2) != X1
              | ~ v4_tex_2(X2,X0)
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          & v3_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & ~ v1_xboole_0(X1) )
           => ~ ( ! [X2] :
                    ( ( m1_pre_topc(X2,X0)
                      & v1_pre_topc(X2)
                      & ~ v2_struct_0(X2) )
                   => ~ ( u1_struct_0(X2) = X1
                        & v4_tex_2(X2,X0) ) )
                & v3_tex_2(X1,X0) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ~ ( ! [X2] :
                  ( ( m1_pre_topc(X2,X0)
                    & v1_pre_topc(X2)
                    & ~ v2_struct_0(X2) )
                 => ~ ( u1_struct_0(X2) = X1
                      & v4_tex_2(X2,X0) ) )
              & v3_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_tex_2)).

fof(f113,plain,
    ( ~ spl3_4
    | ~ spl3_6
    | spl3_10 ),
    inference(avatar_contradiction_clause,[],[f112])).

fof(f112,plain,
    ( $false
    | ~ spl3_4
    | ~ spl3_6
    | spl3_10 ),
    inference(subsumption_resolution,[],[f111,f69])).

fof(f111,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_4
    | spl3_10 ),
    inference(subsumption_resolution,[],[f110,f56])).

fof(f110,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_10 ),
    inference(duplicate_literal_removal,[],[f109])).

fof(f109,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_10 ),
    inference(resolution,[],[f107,f36])).

fof(f107,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(k1_pre_topc(sK0,sK1),X0)
        | ~ l1_pre_topc(X0) )
    | spl3_10 ),
    inference(resolution,[],[f105,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f105,plain,
    ( ~ l1_pre_topc(k1_pre_topc(sK0,sK1))
    | spl3_10 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl3_10
  <=> l1_pre_topc(k1_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f106,plain,
    ( ~ spl3_10
    | spl3_9 ),
    inference(avatar_split_clause,[],[f100,f91,f103])).

fof(f91,plain,
    ( spl3_9
  <=> l1_struct_0(k1_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f100,plain,
    ( ~ l1_pre_topc(k1_pre_topc(sK0,sK1))
    | spl3_9 ),
    inference(resolution,[],[f93,f27])).

fof(f27,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
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
    ( ~ l1_struct_0(k1_pre_topc(sK0,sK1))
    | spl3_9 ),
    inference(avatar_component_clause,[],[f91])).

fof(f94,plain,
    ( ~ spl3_8
    | ~ spl3_9
    | spl3_1
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f84,f74,f39,f91,f87])).

fof(f39,plain,
    ( spl3_1
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f84,plain,
    ( ~ l1_struct_0(k1_pre_topc(sK0,sK1))
    | ~ v2_struct_0(k1_pre_topc(sK0,sK1))
    | spl3_1
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f79,f41])).

fof(f41,plain,
    ( ~ v1_xboole_0(sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f39])).

fof(f79,plain,
    ( v1_xboole_0(sK1)
    | ~ l1_struct_0(k1_pre_topc(sK0,sK1))
    | ~ v2_struct_0(k1_pre_topc(sK0,sK1))
    | ~ spl3_7 ),
    inference(superposition,[],[f34,f76])).

fof(f34,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v2_struct_0(X0) )
     => v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_struct_0)).

fof(f77,plain,
    ( spl3_7
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f72,f67,f54,f74])).

fof(f72,plain,
    ( sK1 = u1_struct_0(k1_pre_topc(sK0,sK1))
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f71,f56])).

fof(f71,plain,
    ( ~ l1_pre_topc(sK0)
    | sK1 = u1_struct_0(k1_pre_topc(sK0,sK1))
    | ~ spl3_6 ),
    inference(resolution,[],[f69,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | u1_struct_0(k1_pre_topc(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => u1_struct_0(k1_pre_topc(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_pre_topc)).

fof(f70,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f22,f67])).

fof(f22,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f10])).

fof(f62,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f23,f59])).

fof(f23,plain,(
    v3_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f57,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f26,f54])).

fof(f26,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f47,plain,(
    ~ spl3_2 ),
    inference(avatar_split_clause,[],[f24,f44])).

fof(f24,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f42,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f21,f39])).

fof(f21,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:00:36 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.21/0.48  % (2345)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (2340)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (2357)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.49  % (2340)Refutation not found, incomplete strategy% (2340)------------------------------
% 0.21/0.49  % (2340)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (2340)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (2340)Memory used [KB]: 10618
% 0.21/0.49  % (2340)Time elapsed: 0.060 s
% 0.21/0.49  % (2340)------------------------------
% 0.21/0.49  % (2340)------------------------------
% 0.21/0.50  % (2342)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.50  % (2354)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.50  % (2357)Refutation not found, incomplete strategy% (2357)------------------------------
% 0.21/0.50  % (2357)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (2357)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (2357)Memory used [KB]: 1663
% 0.21/0.50  % (2357)Time elapsed: 0.073 s
% 0.21/0.50  % (2357)------------------------------
% 0.21/0.50  % (2357)------------------------------
% 0.21/0.51  % (2342)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f150,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f42,f47,f57,f62,f70,f77,f94,f106,f113,f126,f130,f137,f144,f149])).
% 0.21/0.51  fof(f149,plain,(
% 0.21/0.51    spl3_2 | ~spl3_4 | ~spl3_5 | spl3_11 | ~spl3_12 | ~spl3_14),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f148])).
% 0.21/0.51  fof(f148,plain,(
% 0.21/0.51    $false | (spl3_2 | ~spl3_4 | ~spl3_5 | spl3_11 | ~spl3_12 | ~spl3_14)),
% 0.21/0.51    inference(subsumption_resolution,[],[f147,f117])).
% 0.21/0.51  fof(f117,plain,(
% 0.21/0.51    ~v4_tex_2(k1_pre_topc(sK0,sK1),sK0) | spl3_11),
% 0.21/0.51    inference(avatar_component_clause,[],[f115])).
% 0.21/0.51  fof(f115,plain,(
% 0.21/0.51    spl3_11 <=> v4_tex_2(k1_pre_topc(sK0,sK1),sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.51  fof(f147,plain,(
% 0.21/0.51    v4_tex_2(k1_pre_topc(sK0,sK1),sK0) | (spl3_2 | ~spl3_4 | ~spl3_5 | ~spl3_12 | ~spl3_14)),
% 0.21/0.51    inference(subsumption_resolution,[],[f146,f120])).
% 0.21/0.51  fof(f120,plain,(
% 0.21/0.51    m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) | ~spl3_12),
% 0.21/0.51    inference(avatar_component_clause,[],[f119])).
% 0.21/0.51  fof(f119,plain,(
% 0.21/0.51    spl3_12 <=> m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.51  fof(f146,plain,(
% 0.21/0.51    ~m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) | v4_tex_2(k1_pre_topc(sK0,sK1),sK0) | (spl3_2 | ~spl3_4 | ~spl3_5 | ~spl3_14)),
% 0.21/0.51    inference(subsumption_resolution,[],[f145,f61])).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    v3_tex_2(sK1,sK0) | ~spl3_5),
% 0.21/0.51    inference(avatar_component_clause,[],[f59])).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    spl3_5 <=> v3_tex_2(sK1,sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.51  fof(f145,plain,(
% 0.21/0.51    ~v3_tex_2(sK1,sK0) | ~m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) | v4_tex_2(k1_pre_topc(sK0,sK1),sK0) | (spl3_2 | ~spl3_4 | ~spl3_14)),
% 0.21/0.51    inference(superposition,[],[f85,f143])).
% 0.21/0.51  fof(f143,plain,(
% 0.21/0.51    sK1 = sK2(sK0,k1_pre_topc(sK0,sK1)) | ~spl3_14),
% 0.21/0.51    inference(avatar_component_clause,[],[f141])).
% 0.21/0.51  fof(f141,plain,(
% 0.21/0.51    spl3_14 <=> sK1 = sK2(sK0,k1_pre_topc(sK0,sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.51  fof(f85,plain,(
% 0.21/0.51    ( ! [X2] : (~v3_tex_2(sK2(sK0,X2),sK0) | ~m1_pre_topc(X2,sK0) | v4_tex_2(X2,sK0)) ) | (spl3_2 | ~spl3_4)),
% 0.21/0.51    inference(subsumption_resolution,[],[f65,f56])).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    l1_pre_topc(sK0) | ~spl3_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f54])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    spl3_4 <=> l1_pre_topc(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.51  fof(f65,plain,(
% 0.21/0.51    ( ! [X2] : (~l1_pre_topc(sK0) | ~m1_pre_topc(X2,sK0) | ~v3_tex_2(sK2(sK0,X2),sK0) | v4_tex_2(X2,sK0)) ) | spl3_2),
% 0.21/0.51    inference(resolution,[],[f46,f33])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~v3_tex_2(sK2(X0,X1),X0) | v4_tex_2(X1,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : ((v4_tex_2(X1,X0) <=> ! [X2] : (v3_tex_2(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : ((v4_tex_2(X1,X0) <=> ! [X2] : ((v3_tex_2(X2,X0) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => (v4_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v3_tex_2(X2,X0))))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_tex_2)).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    ~v2_struct_0(sK0) | spl3_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f44])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    spl3_2 <=> v2_struct_0(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.51  fof(f144,plain,(
% 0.21/0.51    spl3_14 | spl3_2 | ~spl3_4 | ~spl3_7 | spl3_11 | ~spl3_12),
% 0.21/0.51    inference(avatar_split_clause,[],[f138,f119,f115,f74,f54,f44,f141])).
% 0.21/0.51  fof(f74,plain,(
% 0.21/0.51    spl3_7 <=> sK1 = u1_struct_0(k1_pre_topc(sK0,sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.51  fof(f138,plain,(
% 0.21/0.51    sK1 = sK2(sK0,k1_pre_topc(sK0,sK1)) | (spl3_2 | ~spl3_4 | ~spl3_7 | spl3_11 | ~spl3_12)),
% 0.21/0.51    inference(subsumption_resolution,[],[f133,f120])).
% 0.21/0.51  fof(f133,plain,(
% 0.21/0.51    sK1 = sK2(sK0,k1_pre_topc(sK0,sK1)) | ~m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) | (spl3_2 | ~spl3_4 | ~spl3_7 | spl3_11)),
% 0.21/0.51    inference(forward_demodulation,[],[f132,f76])).
% 0.21/0.51  fof(f76,plain,(
% 0.21/0.51    sK1 = u1_struct_0(k1_pre_topc(sK0,sK1)) | ~spl3_7),
% 0.21/0.51    inference(avatar_component_clause,[],[f74])).
% 0.21/0.51  fof(f132,plain,(
% 0.21/0.51    u1_struct_0(k1_pre_topc(sK0,sK1)) = sK2(sK0,k1_pre_topc(sK0,sK1)) | ~m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) | (spl3_2 | ~spl3_4 | spl3_11)),
% 0.21/0.51    inference(resolution,[],[f117,f95])).
% 0.21/0.51  fof(f95,plain,(
% 0.21/0.51    ( ! [X1] : (v4_tex_2(X1,sK0) | u1_struct_0(X1) = sK2(sK0,X1) | ~m1_pre_topc(X1,sK0)) ) | (spl3_2 | ~spl3_4)),
% 0.21/0.51    inference(subsumption_resolution,[],[f64,f56])).
% 0.21/0.51  fof(f64,plain,(
% 0.21/0.51    ( ! [X1] : (~l1_pre_topc(sK0) | ~m1_pre_topc(X1,sK0) | u1_struct_0(X1) = sK2(sK0,X1) | v4_tex_2(X1,sK0)) ) | spl3_2),
% 0.21/0.51    inference(resolution,[],[f46,f32])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | u1_struct_0(X1) = sK2(X0,X1) | v4_tex_2(X1,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f15])).
% 0.21/0.51  fof(f137,plain,(
% 0.21/0.51    ~spl3_4 | ~spl3_6 | spl3_12),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f136])).
% 0.21/0.51  fof(f136,plain,(
% 0.21/0.51    $false | (~spl3_4 | ~spl3_6 | spl3_12)),
% 0.21/0.51    inference(subsumption_resolution,[],[f135,f56])).
% 0.21/0.51  fof(f135,plain,(
% 0.21/0.51    ~l1_pre_topc(sK0) | (~spl3_6 | spl3_12)),
% 0.21/0.51    inference(subsumption_resolution,[],[f134,f69])).
% 0.21/0.51  fof(f69,plain,(
% 0.21/0.51    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_6),
% 0.21/0.51    inference(avatar_component_clause,[],[f67])).
% 0.21/0.51  fof(f67,plain,(
% 0.21/0.51    spl3_6 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.51  fof(f134,plain,(
% 0.21/0.51    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl3_12),
% 0.21/0.51    inference(resolution,[],[f121,f36])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ( ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(flattening,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => (m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_pre_topc)).
% 0.21/0.51  fof(f121,plain,(
% 0.21/0.51    ~m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) | spl3_12),
% 0.21/0.51    inference(avatar_component_clause,[],[f119])).
% 0.21/0.51  fof(f130,plain,(
% 0.21/0.51    ~spl3_4 | ~spl3_6 | spl3_13),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f129])).
% 0.21/0.51  fof(f129,plain,(
% 0.21/0.51    $false | (~spl3_4 | ~spl3_6 | spl3_13)),
% 0.21/0.51    inference(subsumption_resolution,[],[f128,f56])).
% 0.21/0.51  fof(f128,plain,(
% 0.21/0.51    ~l1_pre_topc(sK0) | (~spl3_6 | spl3_13)),
% 0.21/0.51    inference(subsumption_resolution,[],[f127,f69])).
% 0.21/0.51  fof(f127,plain,(
% 0.21/0.51    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl3_13),
% 0.21/0.51    inference(resolution,[],[f125,f35])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v1_pre_topc(k1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f125,plain,(
% 0.21/0.51    ~v1_pre_topc(k1_pre_topc(sK0,sK1)) | spl3_13),
% 0.21/0.51    inference(avatar_component_clause,[],[f123])).
% 0.21/0.51  fof(f123,plain,(
% 0.21/0.51    spl3_13 <=> v1_pre_topc(k1_pre_topc(sK0,sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.51  fof(f126,plain,(
% 0.21/0.51    ~spl3_11 | ~spl3_12 | ~spl3_13 | ~spl3_7 | spl3_8),
% 0.21/0.51    inference(avatar_split_clause,[],[f108,f87,f74,f123,f119,f115])).
% 0.21/0.51  fof(f87,plain,(
% 0.21/0.51    spl3_8 <=> v2_struct_0(k1_pre_topc(sK0,sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.51  fof(f108,plain,(
% 0.21/0.51    ~v1_pre_topc(k1_pre_topc(sK0,sK1)) | ~m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) | ~v4_tex_2(k1_pre_topc(sK0,sK1),sK0) | (~spl3_7 | spl3_8)),
% 0.21/0.51    inference(subsumption_resolution,[],[f83,f89])).
% 0.21/0.51  fof(f89,plain,(
% 0.21/0.51    ~v2_struct_0(k1_pre_topc(sK0,sK1)) | spl3_8),
% 0.21/0.51    inference(avatar_component_clause,[],[f87])).
% 0.21/0.51  fof(f83,plain,(
% 0.21/0.51    ~v1_pre_topc(k1_pre_topc(sK0,sK1)) | ~m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) | ~v4_tex_2(k1_pre_topc(sK0,sK1),sK0) | v2_struct_0(k1_pre_topc(sK0,sK1)) | ~spl3_7),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f78])).
% 0.21/0.51  fof(f78,plain,(
% 0.21/0.51    sK1 != sK1 | ~v1_pre_topc(k1_pre_topc(sK0,sK1)) | ~m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) | ~v4_tex_2(k1_pre_topc(sK0,sK1),sK0) | v2_struct_0(k1_pre_topc(sK0,sK1)) | ~spl3_7),
% 0.21/0.51    inference(superposition,[],[f20,f76])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ( ! [X2] : (u1_struct_0(X2) != sK1 | ~v1_pre_topc(X2) | ~m1_pre_topc(X2,sK0) | ~v4_tex_2(X2,sK0) | v2_struct_0(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (! [X2] : (u1_struct_0(X2) != X1 | ~v4_tex_2(X2,X0) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2)) & v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f9])).
% 0.21/0.51  fof(f9,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : ((! [X2] : ((u1_struct_0(X2) != X1 | ~v4_tex_2(X2,X0)) | (~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2))) & v3_tex_2(X1,X0)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,negated_conjecture,(
% 0.21/0.51    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ~(! [X2] : ((m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => ~(u1_struct_0(X2) = X1 & v4_tex_2(X2,X0))) & v3_tex_2(X1,X0))))),
% 0.21/0.51    inference(negated_conjecture,[],[f7])).
% 0.21/0.51  fof(f7,conjecture,(
% 0.21/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ~(! [X2] : ((m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => ~(u1_struct_0(X2) = X1 & v4_tex_2(X2,X0))) & v3_tex_2(X1,X0))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_tex_2)).
% 0.21/0.51  fof(f113,plain,(
% 0.21/0.51    ~spl3_4 | ~spl3_6 | spl3_10),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f112])).
% 0.21/0.51  fof(f112,plain,(
% 0.21/0.51    $false | (~spl3_4 | ~spl3_6 | spl3_10)),
% 0.21/0.51    inference(subsumption_resolution,[],[f111,f69])).
% 0.21/0.51  fof(f111,plain,(
% 0.21/0.51    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_4 | spl3_10)),
% 0.21/0.51    inference(subsumption_resolution,[],[f110,f56])).
% 0.21/0.51  fof(f110,plain,(
% 0.21/0.51    ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_10),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f109])).
% 0.21/0.51  fof(f109,plain,(
% 0.21/0.51    ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl3_10),
% 0.21/0.51    inference(resolution,[],[f107,f36])).
% 0.21/0.51  fof(f107,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_pre_topc(k1_pre_topc(sK0,sK1),X0) | ~l1_pre_topc(X0)) ) | spl3_10),
% 0.21/0.51    inference(resolution,[],[f105,f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.51  fof(f105,plain,(
% 0.21/0.51    ~l1_pre_topc(k1_pre_topc(sK0,sK1)) | spl3_10),
% 0.21/0.51    inference(avatar_component_clause,[],[f103])).
% 0.21/0.51  fof(f103,plain,(
% 0.21/0.51    spl3_10 <=> l1_pre_topc(k1_pre_topc(sK0,sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.51  fof(f106,plain,(
% 0.21/0.51    ~spl3_10 | spl3_9),
% 0.21/0.51    inference(avatar_split_clause,[],[f100,f91,f103])).
% 0.21/0.51  fof(f91,plain,(
% 0.21/0.51    spl3_9 <=> l1_struct_0(k1_pre_topc(sK0,sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.51  fof(f100,plain,(
% 0.21/0.51    ~l1_pre_topc(k1_pre_topc(sK0,sK1)) | spl3_9),
% 0.21/0.51    inference(resolution,[],[f93,f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,plain,(
% 0.21/0.51    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.51  fof(f93,plain,(
% 0.21/0.51    ~l1_struct_0(k1_pre_topc(sK0,sK1)) | spl3_9),
% 0.21/0.51    inference(avatar_component_clause,[],[f91])).
% 0.21/0.51  fof(f94,plain,(
% 0.21/0.51    ~spl3_8 | ~spl3_9 | spl3_1 | ~spl3_7),
% 0.21/0.51    inference(avatar_split_clause,[],[f84,f74,f39,f91,f87])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    spl3_1 <=> v1_xboole_0(sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.51  fof(f84,plain,(
% 0.21/0.51    ~l1_struct_0(k1_pre_topc(sK0,sK1)) | ~v2_struct_0(k1_pre_topc(sK0,sK1)) | (spl3_1 | ~spl3_7)),
% 0.21/0.51    inference(subsumption_resolution,[],[f79,f41])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    ~v1_xboole_0(sK1) | spl3_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f39])).
% 0.21/0.51  fof(f79,plain,(
% 0.21/0.51    v1_xboole_0(sK1) | ~l1_struct_0(k1_pre_topc(sK0,sK1)) | ~v2_struct_0(k1_pre_topc(sK0,sK1)) | ~spl3_7),
% 0.21/0.51    inference(superposition,[],[f34,f76])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ( ! [X0] : (v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ! [X0] : (v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ! [X0] : (v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0] : ((l1_struct_0(X0) & v2_struct_0(X0)) => v1_xboole_0(u1_struct_0(X0)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_struct_0)).
% 0.21/0.51  fof(f77,plain,(
% 0.21/0.51    spl3_7 | ~spl3_4 | ~spl3_6),
% 0.21/0.51    inference(avatar_split_clause,[],[f72,f67,f54,f74])).
% 0.21/0.51  fof(f72,plain,(
% 0.21/0.51    sK1 = u1_struct_0(k1_pre_topc(sK0,sK1)) | (~spl3_4 | ~spl3_6)),
% 0.21/0.51    inference(subsumption_resolution,[],[f71,f56])).
% 0.21/0.51  fof(f71,plain,(
% 0.21/0.51    ~l1_pre_topc(sK0) | sK1 = u1_struct_0(k1_pre_topc(sK0,sK1)) | ~spl3_6),
% 0.21/0.51    inference(resolution,[],[f69,f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | u1_struct_0(k1_pre_topc(X0,X1)) = X1) )),
% 0.21/0.51    inference(cnf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => u1_struct_0(k1_pre_topc(X0,X1)) = X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_pre_topc)).
% 0.21/0.51  fof(f70,plain,(
% 0.21/0.51    spl3_6),
% 0.21/0.51    inference(avatar_split_clause,[],[f22,f67])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.51    inference(cnf_transformation,[],[f10])).
% 0.21/0.51  fof(f62,plain,(
% 0.21/0.51    spl3_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f23,f59])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    v3_tex_2(sK1,sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f10])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    spl3_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f26,f54])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    l1_pre_topc(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f10])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    ~spl3_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f24,f44])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ~v2_struct_0(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f10])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    ~spl3_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f21,f39])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ~v1_xboole_0(sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f10])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (2342)------------------------------
% 0.21/0.51  % (2342)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (2342)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (2342)Memory used [KB]: 10618
% 0.21/0.51  % (2342)Time elapsed: 0.081 s
% 0.21/0.51  % (2342)------------------------------
% 0.21/0.51  % (2342)------------------------------
% 0.21/0.51  % (2338)Success in time 0.141 s
%------------------------------------------------------------------------------
