%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:07 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 182 expanded)
%              Number of leaves         :   14 (  64 expanded)
%              Depth                    :   11
%              Number of atoms          :  389 ( 822 expanded)
%              Number of equality atoms :   27 (  65 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f139,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f31,f36,f46,f51,f62,f70,f93,f99,f106,f126,f132,f138])).

fof(f138,plain,
    ( spl4_1
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(avatar_contradiction_clause,[],[f137])).

fof(f137,plain,
    ( $false
    | spl4_1
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f136,f35])).

fof(f35,plain,
    ( ~ v2_struct_0(sK0)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f33])).

fof(f33,plain,
    ( spl4_2
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f136,plain,
    ( v2_struct_0(sK0)
    | spl4_1
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f135,f61])).

fof(f61,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl4_6
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f135,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | spl4_1
    | ~ spl4_4
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f134,f30])).

fof(f30,plain,
    ( ~ v1_xboole_0(sK1)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f28])).

fof(f28,plain,
    ( spl4_1
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f134,plain,
    ( v1_xboole_0(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl4_4
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f133,f45])).

fof(f45,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f43])).

fof(f43,plain,
    ( spl4_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f133,plain,
    ( ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl4_8 ),
    inference(resolution,[],[f80,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(sK3(X0,X1))
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
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
    inference(flattening,[],[f9])).

fof(f9,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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

fof(f80,plain,
    ( v2_struct_0(sK3(sK0,sK1))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl4_8
  <=> v2_struct_0(sK3(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f132,plain,
    ( spl4_2
    | ~ spl4_4
    | ~ spl4_5
    | spl4_9
    | ~ spl4_10
    | ~ spl4_15 ),
    inference(avatar_contradiction_clause,[],[f131])).

fof(f131,plain,
    ( $false
    | spl4_2
    | ~ spl4_4
    | ~ spl4_5
    | spl4_9
    | ~ spl4_10
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f130,f84])).

fof(f84,plain,
    ( ~ v4_tex_2(sK3(sK0,sK1),sK0)
    | spl4_9 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl4_9
  <=> v4_tex_2(sK3(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f130,plain,
    ( v4_tex_2(sK3(sK0,sK1),sK0)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_10
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f129,f87])).

fof(f87,plain,
    ( m1_pre_topc(sK3(sK0,sK1),sK0)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl4_10
  <=> m1_pre_topc(sK3(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f129,plain,
    ( ~ m1_pre_topc(sK3(sK0,sK1),sK0)
    | v4_tex_2(sK3(sK0,sK1),sK0)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f127,f50])).

fof(f50,plain,
    ( v3_tex_2(sK1,sK0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl4_5
  <=> v3_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f127,plain,
    ( ~ v3_tex_2(sK1,sK0)
    | ~ m1_pre_topc(sK3(sK0,sK1),sK0)
    | v4_tex_2(sK3(sK0,sK1),sK0)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_15 ),
    inference(superposition,[],[f57,f125])).

fof(f125,plain,
    ( sK1 = sK2(sK0,sK3(sK0,sK1))
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl4_15
  <=> sK1 = sK2(sK0,sK3(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f57,plain,
    ( ! [X1] :
        ( ~ v3_tex_2(sK2(sK0,X1),sK0)
        | ~ m1_pre_topc(X1,sK0)
        | v4_tex_2(X1,sK0) )
    | spl4_2
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f55,f35])).

fof(f55,plain,
    ( ! [X1] :
        ( v2_struct_0(sK0)
        | ~ m1_pre_topc(X1,sK0)
        | ~ v3_tex_2(sK2(sK0,X1),sK0)
        | v4_tex_2(X1,sK0) )
    | ~ spl4_4 ),
    inference(resolution,[],[f45,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v3_tex_2(sK2(X0,X1),X0)
      | v4_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
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
    inference(flattening,[],[f7])).

fof(f7,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_tex_2)).

fof(f126,plain,
    ( spl4_15
    | spl4_2
    | ~ spl4_4
    | ~ spl4_7
    | spl4_9
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f121,f86,f82,f67,f43,f33,f123])).

fof(f67,plain,
    ( spl4_7
  <=> sK1 = u1_struct_0(sK3(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f121,plain,
    ( sK1 = sK2(sK0,sK3(sK0,sK1))
    | spl4_2
    | ~ spl4_4
    | ~ spl4_7
    | spl4_9
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f101,f87])).

fof(f101,plain,
    ( sK1 = sK2(sK0,sK3(sK0,sK1))
    | ~ m1_pre_topc(sK3(sK0,sK1),sK0)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_7
    | spl4_9 ),
    inference(forward_demodulation,[],[f100,f69])).

fof(f69,plain,
    ( sK1 = u1_struct_0(sK3(sK0,sK1))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f67])).

fof(f100,plain,
    ( u1_struct_0(sK3(sK0,sK1)) = sK2(sK0,sK3(sK0,sK1))
    | ~ m1_pre_topc(sK3(sK0,sK1),sK0)
    | spl4_2
    | ~ spl4_4
    | spl4_9 ),
    inference(resolution,[],[f84,f56])).

fof(f56,plain,
    ( ! [X0] :
        ( v4_tex_2(X0,sK0)
        | u1_struct_0(X0) = sK2(sK0,X0)
        | ~ m1_pre_topc(X0,sK0) )
    | spl4_2
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f54,f35])).

fof(f54,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ m1_pre_topc(X0,sK0)
        | u1_struct_0(X0) = sK2(sK0,X0)
        | v4_tex_2(X0,sK0) )
    | ~ spl4_4 ),
    inference(resolution,[],[f45,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,X0)
      | u1_struct_0(X1) = sK2(X0,X1)
      | v4_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f106,plain,
    ( spl4_1
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | spl4_10 ),
    inference(avatar_contradiction_clause,[],[f105])).

fof(f105,plain,
    ( $false
    | spl4_1
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | spl4_10 ),
    inference(subsumption_resolution,[],[f104,f45])).

fof(f104,plain,
    ( ~ l1_pre_topc(sK0)
    | spl4_1
    | spl4_2
    | ~ spl4_6
    | spl4_10 ),
    inference(subsumption_resolution,[],[f103,f61])).

fof(f103,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl4_1
    | spl4_2
    | spl4_10 ),
    inference(subsumption_resolution,[],[f102,f35])).

fof(f102,plain,
    ( v2_struct_0(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl4_1
    | spl4_10 ),
    inference(resolution,[],[f88,f52])).

fof(f52,plain,
    ( ! [X0] :
        ( m1_pre_topc(sK3(X0,sK1),X0)
        | v2_struct_0(X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | spl4_1 ),
    inference(resolution,[],[f30,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_pre_topc(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f88,plain,
    ( ~ m1_pre_topc(sK3(sK0,sK1),sK0)
    | spl4_10 ),
    inference(avatar_component_clause,[],[f86])).

fof(f99,plain,
    ( spl4_1
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | spl4_11 ),
    inference(avatar_contradiction_clause,[],[f98])).

fof(f98,plain,
    ( $false
    | spl4_1
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | spl4_11 ),
    inference(subsumption_resolution,[],[f97,f35])).

fof(f97,plain,
    ( v2_struct_0(sK0)
    | spl4_1
    | ~ spl4_4
    | ~ spl4_6
    | spl4_11 ),
    inference(subsumption_resolution,[],[f96,f61])).

fof(f96,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | spl4_1
    | ~ spl4_4
    | spl4_11 ),
    inference(subsumption_resolution,[],[f95,f30])).

fof(f95,plain,
    ( v1_xboole_0(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl4_4
    | spl4_11 ),
    inference(subsumption_resolution,[],[f94,f45])).

fof(f94,plain,
    ( ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | spl4_11 ),
    inference(resolution,[],[f92,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(sK3(X0,X1))
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f92,plain,
    ( ~ v1_pre_topc(sK3(sK0,sK1))
    | spl4_11 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl4_11
  <=> v1_pre_topc(sK3(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f93,plain,
    ( spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f76,f67,f90,f86,f82,f78])).

fof(f76,plain,
    ( ~ v1_pre_topc(sK3(sK0,sK1))
    | ~ m1_pre_topc(sK3(sK0,sK1),sK0)
    | ~ v4_tex_2(sK3(sK0,sK1),sK0)
    | v2_struct_0(sK3(sK0,sK1))
    | ~ spl4_7 ),
    inference(trivial_inequality_removal,[],[f72])).

fof(f72,plain,
    ( sK1 != sK1
    | ~ v1_pre_topc(sK3(sK0,sK1))
    | ~ m1_pre_topc(sK3(sK0,sK1),sK0)
    | ~ v4_tex_2(sK3(sK0,sK1),sK0)
    | v2_struct_0(sK3(sK0,sK1))
    | ~ spl4_7 ),
    inference(superposition,[],[f11,f69])).

fof(f11,plain,(
    ! [X2] :
      ( u1_struct_0(X2) != sK1
      | ~ v1_pre_topc(X2)
      | ~ m1_pre_topc(X2,sK0)
      | ~ v4_tex_2(X2,sK0)
      | v2_struct_0(X2) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
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
    inference(flattening,[],[f5])).

fof(f5,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
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
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_tex_2)).

fof(f70,plain,
    ( spl4_7
    | spl4_1
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f65,f59,f43,f33,f28,f67])).

fof(f65,plain,
    ( sK1 = u1_struct_0(sK3(sK0,sK1))
    | spl4_1
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f64,f45])).

fof(f64,plain,
    ( ~ l1_pre_topc(sK0)
    | sK1 = u1_struct_0(sK3(sK0,sK1))
    | spl4_1
    | spl4_2
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f63,f35])).

fof(f63,plain,
    ( v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | sK1 = u1_struct_0(sK3(sK0,sK1))
    | spl4_1
    | ~ spl4_6 ),
    inference(resolution,[],[f53,f61])).

fof(f53,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X1)))
        | v2_struct_0(X1)
        | ~ l1_pre_topc(X1)
        | sK1 = u1_struct_0(sK3(X1,sK1)) )
    | spl4_1 ),
    inference(resolution,[],[f30,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(sK3(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f62,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f13,f59])).

fof(f13,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f6])).

fof(f51,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f14,f48])).

fof(f14,plain,(
    v3_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f6])).

fof(f46,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f17,f43])).

fof(f17,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f6])).

fof(f36,plain,(
    ~ spl4_2 ),
    inference(avatar_split_clause,[],[f15,f33])).

fof(f15,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f6])).

fof(f31,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f12,f28])).

fof(f12,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f6])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:18:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.46  % (15457)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.46  % (15473)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.46  % (15458)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.47  % (15455)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.47  % (15458)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f139,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(avatar_sat_refutation,[],[f31,f36,f46,f51,f62,f70,f93,f99,f106,f126,f132,f138])).
% 0.20/0.47  fof(f138,plain,(
% 0.20/0.47    spl4_1 | spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_8),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f137])).
% 0.20/0.47  fof(f137,plain,(
% 0.20/0.47    $false | (spl4_1 | spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_8)),
% 0.20/0.47    inference(subsumption_resolution,[],[f136,f35])).
% 0.20/0.47  fof(f35,plain,(
% 0.20/0.47    ~v2_struct_0(sK0) | spl4_2),
% 0.20/0.47    inference(avatar_component_clause,[],[f33])).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    spl4_2 <=> v2_struct_0(sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.47  fof(f136,plain,(
% 0.20/0.47    v2_struct_0(sK0) | (spl4_1 | ~spl4_4 | ~spl4_6 | ~spl4_8)),
% 0.20/0.47    inference(subsumption_resolution,[],[f135,f61])).
% 0.20/0.47  fof(f61,plain,(
% 0.20/0.47    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_6),
% 0.20/0.47    inference(avatar_component_clause,[],[f59])).
% 0.20/0.47  fof(f59,plain,(
% 0.20/0.47    spl4_6 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.47  fof(f135,plain,(
% 0.20/0.47    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (spl4_1 | ~spl4_4 | ~spl4_8)),
% 0.20/0.47    inference(subsumption_resolution,[],[f134,f30])).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    ~v1_xboole_0(sK1) | spl4_1),
% 0.20/0.47    inference(avatar_component_clause,[],[f28])).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    spl4_1 <=> v1_xboole_0(sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.47  fof(f134,plain,(
% 0.20/0.47    v1_xboole_0(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (~spl4_4 | ~spl4_8)),
% 0.20/0.47    inference(subsumption_resolution,[],[f133,f45])).
% 0.20/0.47  fof(f45,plain,(
% 0.20/0.47    l1_pre_topc(sK0) | ~spl4_4),
% 0.20/0.47    inference(avatar_component_clause,[],[f43])).
% 0.20/0.47  fof(f43,plain,(
% 0.20/0.47    spl4_4 <=> l1_pre_topc(sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.47  fof(f133,plain,(
% 0.20/0.47    ~l1_pre_topc(sK0) | v1_xboole_0(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | ~spl4_8),
% 0.20/0.47    inference(resolution,[],[f80,f22])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~v2_struct_0(sK3(X0,X1)) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_struct_0(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f10])).
% 0.20/0.47  fof(f10,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.47    inference(flattening,[],[f9])).
% 0.20/0.47  fof(f9,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_tsep_1)).
% 0.20/0.47  fof(f80,plain,(
% 0.20/0.47    v2_struct_0(sK3(sK0,sK1)) | ~spl4_8),
% 0.20/0.47    inference(avatar_component_clause,[],[f78])).
% 0.20/0.47  fof(f78,plain,(
% 0.20/0.47    spl4_8 <=> v2_struct_0(sK3(sK0,sK1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.20/0.47  fof(f132,plain,(
% 0.20/0.47    spl4_2 | ~spl4_4 | ~spl4_5 | spl4_9 | ~spl4_10 | ~spl4_15),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f131])).
% 0.20/0.47  fof(f131,plain,(
% 0.20/0.47    $false | (spl4_2 | ~spl4_4 | ~spl4_5 | spl4_9 | ~spl4_10 | ~spl4_15)),
% 0.20/0.47    inference(subsumption_resolution,[],[f130,f84])).
% 0.20/0.47  fof(f84,plain,(
% 0.20/0.47    ~v4_tex_2(sK3(sK0,sK1),sK0) | spl4_9),
% 0.20/0.47    inference(avatar_component_clause,[],[f82])).
% 0.20/0.47  fof(f82,plain,(
% 0.20/0.47    spl4_9 <=> v4_tex_2(sK3(sK0,sK1),sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.20/0.47  fof(f130,plain,(
% 0.20/0.47    v4_tex_2(sK3(sK0,sK1),sK0) | (spl4_2 | ~spl4_4 | ~spl4_5 | ~spl4_10 | ~spl4_15)),
% 0.20/0.47    inference(subsumption_resolution,[],[f129,f87])).
% 0.20/0.47  fof(f87,plain,(
% 0.20/0.47    m1_pre_topc(sK3(sK0,sK1),sK0) | ~spl4_10),
% 0.20/0.47    inference(avatar_component_clause,[],[f86])).
% 0.20/0.47  fof(f86,plain,(
% 0.20/0.47    spl4_10 <=> m1_pre_topc(sK3(sK0,sK1),sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.20/0.47  fof(f129,plain,(
% 0.20/0.47    ~m1_pre_topc(sK3(sK0,sK1),sK0) | v4_tex_2(sK3(sK0,sK1),sK0) | (spl4_2 | ~spl4_4 | ~spl4_5 | ~spl4_15)),
% 0.20/0.47    inference(subsumption_resolution,[],[f127,f50])).
% 0.20/0.47  fof(f50,plain,(
% 0.20/0.47    v3_tex_2(sK1,sK0) | ~spl4_5),
% 0.20/0.47    inference(avatar_component_clause,[],[f48])).
% 0.20/0.47  fof(f48,plain,(
% 0.20/0.47    spl4_5 <=> v3_tex_2(sK1,sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.47  fof(f127,plain,(
% 0.20/0.47    ~v3_tex_2(sK1,sK0) | ~m1_pre_topc(sK3(sK0,sK1),sK0) | v4_tex_2(sK3(sK0,sK1),sK0) | (spl4_2 | ~spl4_4 | ~spl4_15)),
% 0.20/0.47    inference(superposition,[],[f57,f125])).
% 0.20/0.47  fof(f125,plain,(
% 0.20/0.47    sK1 = sK2(sK0,sK3(sK0,sK1)) | ~spl4_15),
% 0.20/0.47    inference(avatar_component_clause,[],[f123])).
% 0.20/0.47  fof(f123,plain,(
% 0.20/0.47    spl4_15 <=> sK1 = sK2(sK0,sK3(sK0,sK1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.20/0.47  fof(f57,plain,(
% 0.20/0.47    ( ! [X1] : (~v3_tex_2(sK2(sK0,X1),sK0) | ~m1_pre_topc(X1,sK0) | v4_tex_2(X1,sK0)) ) | (spl4_2 | ~spl4_4)),
% 0.20/0.47    inference(subsumption_resolution,[],[f55,f35])).
% 0.20/0.47  fof(f55,plain,(
% 0.20/0.47    ( ! [X1] : (v2_struct_0(sK0) | ~m1_pre_topc(X1,sK0) | ~v3_tex_2(sK2(sK0,X1),sK0) | v4_tex_2(X1,sK0)) ) | ~spl4_4),
% 0.20/0.47    inference(resolution,[],[f45,f21])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~l1_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(X1,X0) | ~v3_tex_2(sK2(X0,X1),X0) | v4_tex_2(X1,X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f8])).
% 0.20/0.47  fof(f8,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : ((v4_tex_2(X1,X0) <=> ! [X2] : (v3_tex_2(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.47    inference(flattening,[],[f7])).
% 0.20/0.47  fof(f7,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : ((v4_tex_2(X1,X0) <=> ! [X2] : ((v3_tex_2(X2,X0) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => (v4_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v3_tex_2(X2,X0))))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_tex_2)).
% 0.20/0.47  fof(f126,plain,(
% 0.20/0.47    spl4_15 | spl4_2 | ~spl4_4 | ~spl4_7 | spl4_9 | ~spl4_10),
% 0.20/0.47    inference(avatar_split_clause,[],[f121,f86,f82,f67,f43,f33,f123])).
% 0.20/0.47  fof(f67,plain,(
% 0.20/0.47    spl4_7 <=> sK1 = u1_struct_0(sK3(sK0,sK1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.20/0.47  fof(f121,plain,(
% 0.20/0.47    sK1 = sK2(sK0,sK3(sK0,sK1)) | (spl4_2 | ~spl4_4 | ~spl4_7 | spl4_9 | ~spl4_10)),
% 0.20/0.47    inference(subsumption_resolution,[],[f101,f87])).
% 0.20/0.47  fof(f101,plain,(
% 0.20/0.47    sK1 = sK2(sK0,sK3(sK0,sK1)) | ~m1_pre_topc(sK3(sK0,sK1),sK0) | (spl4_2 | ~spl4_4 | ~spl4_7 | spl4_9)),
% 0.20/0.47    inference(forward_demodulation,[],[f100,f69])).
% 0.20/0.47  fof(f69,plain,(
% 0.20/0.47    sK1 = u1_struct_0(sK3(sK0,sK1)) | ~spl4_7),
% 0.20/0.47    inference(avatar_component_clause,[],[f67])).
% 0.20/0.47  fof(f100,plain,(
% 0.20/0.47    u1_struct_0(sK3(sK0,sK1)) = sK2(sK0,sK3(sK0,sK1)) | ~m1_pre_topc(sK3(sK0,sK1),sK0) | (spl4_2 | ~spl4_4 | spl4_9)),
% 0.20/0.47    inference(resolution,[],[f84,f56])).
% 0.20/0.47  fof(f56,plain,(
% 0.20/0.47    ( ! [X0] : (v4_tex_2(X0,sK0) | u1_struct_0(X0) = sK2(sK0,X0) | ~m1_pre_topc(X0,sK0)) ) | (spl4_2 | ~spl4_4)),
% 0.20/0.47    inference(subsumption_resolution,[],[f54,f35])).
% 0.20/0.47  fof(f54,plain,(
% 0.20/0.47    ( ! [X0] : (v2_struct_0(sK0) | ~m1_pre_topc(X0,sK0) | u1_struct_0(X0) = sK2(sK0,X0) | v4_tex_2(X0,sK0)) ) | ~spl4_4),
% 0.20/0.47    inference(resolution,[],[f45,f20])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~l1_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(X1,X0) | u1_struct_0(X1) = sK2(X0,X1) | v4_tex_2(X1,X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f8])).
% 0.20/0.47  fof(f106,plain,(
% 0.20/0.47    spl4_1 | spl4_2 | ~spl4_4 | ~spl4_6 | spl4_10),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f105])).
% 0.20/0.47  fof(f105,plain,(
% 0.20/0.47    $false | (spl4_1 | spl4_2 | ~spl4_4 | ~spl4_6 | spl4_10)),
% 0.20/0.47    inference(subsumption_resolution,[],[f104,f45])).
% 0.20/0.47  fof(f104,plain,(
% 0.20/0.47    ~l1_pre_topc(sK0) | (spl4_1 | spl4_2 | ~spl4_6 | spl4_10)),
% 0.20/0.47    inference(subsumption_resolution,[],[f103,f61])).
% 0.20/0.47  fof(f103,plain,(
% 0.20/0.47    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (spl4_1 | spl4_2 | spl4_10)),
% 0.20/0.47    inference(subsumption_resolution,[],[f102,f35])).
% 0.20/0.47  fof(f102,plain,(
% 0.20/0.47    v2_struct_0(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (spl4_1 | spl4_10)),
% 0.20/0.47    inference(resolution,[],[f88,f52])).
% 0.20/0.47  fof(f52,plain,(
% 0.20/0.47    ( ! [X0] : (m1_pre_topc(sK3(X0,sK1),X0) | v2_struct_0(X0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | spl4_1),
% 0.20/0.47    inference(resolution,[],[f30,f24])).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    ( ! [X0,X1] : (v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_pre_topc(sK3(X0,X1),X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f10])).
% 0.20/0.47  fof(f88,plain,(
% 0.20/0.47    ~m1_pre_topc(sK3(sK0,sK1),sK0) | spl4_10),
% 0.20/0.47    inference(avatar_component_clause,[],[f86])).
% 0.20/0.47  fof(f99,plain,(
% 0.20/0.47    spl4_1 | spl4_2 | ~spl4_4 | ~spl4_6 | spl4_11),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f98])).
% 0.20/0.47  fof(f98,plain,(
% 0.20/0.47    $false | (spl4_1 | spl4_2 | ~spl4_4 | ~spl4_6 | spl4_11)),
% 0.20/0.47    inference(subsumption_resolution,[],[f97,f35])).
% 0.20/0.47  fof(f97,plain,(
% 0.20/0.47    v2_struct_0(sK0) | (spl4_1 | ~spl4_4 | ~spl4_6 | spl4_11)),
% 0.20/0.47    inference(subsumption_resolution,[],[f96,f61])).
% 0.20/0.47  fof(f96,plain,(
% 0.20/0.47    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (spl4_1 | ~spl4_4 | spl4_11)),
% 0.20/0.47    inference(subsumption_resolution,[],[f95,f30])).
% 0.20/0.47  fof(f95,plain,(
% 0.20/0.47    v1_xboole_0(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (~spl4_4 | spl4_11)),
% 0.20/0.47    inference(subsumption_resolution,[],[f94,f45])).
% 0.20/0.47  fof(f94,plain,(
% 0.20/0.47    ~l1_pre_topc(sK0) | v1_xboole_0(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | spl4_11),
% 0.20/0.47    inference(resolution,[],[f92,f23])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    ( ! [X0,X1] : (v1_pre_topc(sK3(X0,X1)) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_struct_0(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f10])).
% 0.20/0.47  fof(f92,plain,(
% 0.20/0.47    ~v1_pre_topc(sK3(sK0,sK1)) | spl4_11),
% 0.20/0.47    inference(avatar_component_clause,[],[f90])).
% 0.20/0.47  fof(f90,plain,(
% 0.20/0.47    spl4_11 <=> v1_pre_topc(sK3(sK0,sK1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.20/0.47  fof(f93,plain,(
% 0.20/0.47    spl4_8 | ~spl4_9 | ~spl4_10 | ~spl4_11 | ~spl4_7),
% 0.20/0.47    inference(avatar_split_clause,[],[f76,f67,f90,f86,f82,f78])).
% 0.20/0.47  fof(f76,plain,(
% 0.20/0.47    ~v1_pre_topc(sK3(sK0,sK1)) | ~m1_pre_topc(sK3(sK0,sK1),sK0) | ~v4_tex_2(sK3(sK0,sK1),sK0) | v2_struct_0(sK3(sK0,sK1)) | ~spl4_7),
% 0.20/0.47    inference(trivial_inequality_removal,[],[f72])).
% 0.20/0.47  fof(f72,plain,(
% 0.20/0.47    sK1 != sK1 | ~v1_pre_topc(sK3(sK0,sK1)) | ~m1_pre_topc(sK3(sK0,sK1),sK0) | ~v4_tex_2(sK3(sK0,sK1),sK0) | v2_struct_0(sK3(sK0,sK1)) | ~spl4_7),
% 0.20/0.47    inference(superposition,[],[f11,f69])).
% 0.20/0.47  fof(f11,plain,(
% 0.20/0.47    ( ! [X2] : (u1_struct_0(X2) != sK1 | ~v1_pre_topc(X2) | ~m1_pre_topc(X2,sK0) | ~v4_tex_2(X2,sK0) | v2_struct_0(X2)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f6])).
% 0.20/0.47  fof(f6,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : (! [X2] : (u1_struct_0(X2) != X1 | ~v4_tex_2(X2,X0) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2)) & v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.47    inference(flattening,[],[f5])).
% 0.20/0.47  fof(f5,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : ((! [X2] : ((u1_struct_0(X2) != X1 | ~v4_tex_2(X2,X0)) | (~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2))) & v3_tex_2(X1,X0)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,negated_conjecture,(
% 0.20/0.47    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ~(! [X2] : ((m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => ~(u1_struct_0(X2) = X1 & v4_tex_2(X2,X0))) & v3_tex_2(X1,X0))))),
% 0.20/0.47    inference(negated_conjecture,[],[f3])).
% 0.20/0.47  fof(f3,conjecture,(
% 0.20/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ~(! [X2] : ((m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => ~(u1_struct_0(X2) = X1 & v4_tex_2(X2,X0))) & v3_tex_2(X1,X0))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_tex_2)).
% 0.20/0.47  fof(f70,plain,(
% 0.20/0.47    spl4_7 | spl4_1 | spl4_2 | ~spl4_4 | ~spl4_6),
% 0.20/0.47    inference(avatar_split_clause,[],[f65,f59,f43,f33,f28,f67])).
% 0.20/0.47  fof(f65,plain,(
% 0.20/0.47    sK1 = u1_struct_0(sK3(sK0,sK1)) | (spl4_1 | spl4_2 | ~spl4_4 | ~spl4_6)),
% 0.20/0.47    inference(subsumption_resolution,[],[f64,f45])).
% 0.20/0.47  fof(f64,plain,(
% 0.20/0.47    ~l1_pre_topc(sK0) | sK1 = u1_struct_0(sK3(sK0,sK1)) | (spl4_1 | spl4_2 | ~spl4_6)),
% 0.20/0.47    inference(subsumption_resolution,[],[f63,f35])).
% 0.20/0.47  fof(f63,plain,(
% 0.20/0.47    v2_struct_0(sK0) | ~l1_pre_topc(sK0) | sK1 = u1_struct_0(sK3(sK0,sK1)) | (spl4_1 | ~spl4_6)),
% 0.20/0.47    inference(resolution,[],[f53,f61])).
% 0.20/0.47  fof(f53,plain,(
% 0.20/0.47    ( ! [X1] : (~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X1))) | v2_struct_0(X1) | ~l1_pre_topc(X1) | sK1 = u1_struct_0(sK3(X1,sK1))) ) | spl4_1),
% 0.20/0.47    inference(resolution,[],[f30,f25])).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    ( ! [X0,X1] : (v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(sK3(X0,X1)) = X1) )),
% 0.20/0.47    inference(cnf_transformation,[],[f10])).
% 0.20/0.47  fof(f62,plain,(
% 0.20/0.47    spl4_6),
% 0.20/0.47    inference(avatar_split_clause,[],[f13,f59])).
% 0.20/0.47  fof(f13,plain,(
% 0.20/0.47    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.47    inference(cnf_transformation,[],[f6])).
% 0.20/0.47  fof(f51,plain,(
% 0.20/0.47    spl4_5),
% 0.20/0.47    inference(avatar_split_clause,[],[f14,f48])).
% 0.20/0.47  fof(f14,plain,(
% 0.20/0.47    v3_tex_2(sK1,sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f6])).
% 0.20/0.47  fof(f46,plain,(
% 0.20/0.47    spl4_4),
% 0.20/0.47    inference(avatar_split_clause,[],[f17,f43])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    l1_pre_topc(sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f6])).
% 0.20/0.47  fof(f36,plain,(
% 0.20/0.47    ~spl4_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f15,f33])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    ~v2_struct_0(sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f6])).
% 0.20/0.47  fof(f31,plain,(
% 0.20/0.47    ~spl4_1),
% 0.20/0.47    inference(avatar_split_clause,[],[f12,f28])).
% 0.20/0.47  fof(f12,plain,(
% 0.20/0.47    ~v1_xboole_0(sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f6])).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (15458)------------------------------
% 0.20/0.47  % (15458)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (15458)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (15458)Memory used [KB]: 10618
% 0.20/0.47  % (15458)Time elapsed: 0.055 s
% 0.20/0.47  % (15458)------------------------------
% 0.20/0.47  % (15458)------------------------------
% 0.20/0.47  % (15451)Success in time 0.112 s
%------------------------------------------------------------------------------
