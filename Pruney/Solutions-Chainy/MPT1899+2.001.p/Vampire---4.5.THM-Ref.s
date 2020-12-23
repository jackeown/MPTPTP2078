%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:23 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  217 ( 525 expanded)
%              Number of leaves         :   27 ( 179 expanded)
%              Depth                    :   26
%              Number of atoms          : 1210 (2492 expanded)
%              Number of equality atoms :   42 (  67 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f527,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f57,f62,f67,f72,f77,f82,f87,f239,f254,f322,f335,f345,f366,f382,f419,f442,f451,f468,f492,f526])).

fof(f526,plain,
    ( spl5_3
    | ~ spl5_6
    | spl5_21
    | ~ spl5_22
    | ~ spl5_23
    | ~ spl5_30 ),
    inference(avatar_contradiction_clause,[],[f525])).

fof(f525,plain,
    ( $false
    | spl5_3
    | ~ spl5_6
    | spl5_21
    | ~ spl5_22
    | ~ spl5_23
    | ~ spl5_30 ),
    inference(subsumption_resolution,[],[f524,f294])).

fof(f294,plain,
    ( ~ v4_tex_2(sK4(sK0,sK2(sK0,u1_struct_0(sK1))),sK0)
    | spl5_21 ),
    inference(avatar_component_clause,[],[f292])).

fof(f292,plain,
    ( spl5_21
  <=> v4_tex_2(sK4(sK0,sK2(sK0,u1_struct_0(sK1))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f524,plain,
    ( v4_tex_2(sK4(sK0,sK2(sK0,u1_struct_0(sK1))),sK0)
    | spl5_3
    | ~ spl5_6
    | ~ spl5_22
    | ~ spl5_23
    | ~ spl5_30 ),
    inference(subsumption_resolution,[],[f523,f297])).

fof(f297,plain,
    ( m1_pre_topc(sK4(sK0,sK2(sK0,u1_struct_0(sK1))),sK0)
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f296])).

fof(f296,plain,
    ( spl5_22
  <=> m1_pre_topc(sK4(sK0,sK2(sK0,u1_struct_0(sK1))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f523,plain,
    ( ~ m1_pre_topc(sK4(sK0,sK2(sK0,u1_struct_0(sK1))),sK0)
    | v4_tex_2(sK4(sK0,sK2(sK0,u1_struct_0(sK1))),sK0)
    | spl5_3
    | ~ spl5_6
    | ~ spl5_23
    | ~ spl5_30 ),
    inference(subsumption_resolution,[],[f521,f302])).

fof(f302,plain,
    ( v3_tex_2(sK2(sK0,u1_struct_0(sK1)),sK0)
    | ~ spl5_23 ),
    inference(avatar_component_clause,[],[f300])).

fof(f300,plain,
    ( spl5_23
  <=> v3_tex_2(sK2(sK0,u1_struct_0(sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f521,plain,
    ( ~ v3_tex_2(sK2(sK0,u1_struct_0(sK1)),sK0)
    | ~ m1_pre_topc(sK4(sK0,sK2(sK0,u1_struct_0(sK1))),sK0)
    | v4_tex_2(sK4(sK0,sK2(sK0,u1_struct_0(sK1))),sK0)
    | spl5_3
    | ~ spl5_6
    | ~ spl5_30 ),
    inference(superposition,[],[f122,f418])).

fof(f418,plain,
    ( sK2(sK0,u1_struct_0(sK1)) = sK3(sK0,sK4(sK0,sK2(sK0,u1_struct_0(sK1))))
    | ~ spl5_30 ),
    inference(avatar_component_clause,[],[f416])).

fof(f416,plain,
    ( spl5_30
  <=> sK2(sK0,u1_struct_0(sK1)) = sK3(sK0,sK4(sK0,sK2(sK0,u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f122,plain,
    ( ! [X1] :
        ( ~ v3_tex_2(sK3(sK0,X1),sK0)
        | ~ m1_pre_topc(X1,sK0)
        | v4_tex_2(X1,sK0) )
    | spl5_3
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f98,f81])).

fof(f81,plain,
    ( l1_pre_topc(sK0)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl5_6
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f98,plain,
    ( ! [X1] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_pre_topc(X1,sK0)
        | ~ v3_tex_2(sK3(sK0,X1),sK0)
        | v4_tex_2(X1,sK0) )
    | spl5_3 ),
    inference(resolution,[],[f66,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v3_tex_2(sK3(X0,X1),X0)
      | v4_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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

fof(f66,plain,
    ( ~ v2_struct_0(sK0)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl5_3
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f492,plain,
    ( spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_16
    | ~ spl5_22
    | ~ spl5_24
    | ~ spl5_25
    | spl5_31 ),
    inference(avatar_contradiction_clause,[],[f491])).

fof(f491,plain,
    ( $false
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_16
    | ~ spl5_22
    | ~ spl5_24
    | ~ spl5_25
    | spl5_31 ),
    inference(subsumption_resolution,[],[f490,f316])).

fof(f316,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f315])).

fof(f315,plain,
    ( spl5_24
  <=> m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f490,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_16
    | ~ spl5_22
    | ~ spl5_25
    | spl5_31 ),
    inference(subsumption_resolution,[],[f489,f320])).

fof(f320,plain,
    ( v2_tex_2(u1_struct_0(sK1),sK0)
    | ~ spl5_25 ),
    inference(avatar_component_clause,[],[f319])).

fof(f319,plain,
    ( spl5_25
  <=> v2_tex_2(u1_struct_0(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f489,plain,
    ( ~ v2_tex_2(u1_struct_0(sK1),sK0)
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_16
    | ~ spl5_22
    | spl5_31 ),
    inference(subsumption_resolution,[],[f488,f86])).

fof(f86,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl5_7
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f488,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ v2_tex_2(u1_struct_0(sK1),sK0)
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_16
    | ~ spl5_22
    | spl5_31 ),
    inference(subsumption_resolution,[],[f486,f437])).

fof(f437,plain,
    ( ~ m1_pre_topc(sK1,sK4(sK0,sK2(sK0,u1_struct_0(sK1))))
    | spl5_31 ),
    inference(avatar_component_clause,[],[f435])).

fof(f435,plain,
    ( spl5_31
  <=> m1_pre_topc(sK1,sK4(sK0,sK2(sK0,u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).

fof(f486,plain,
    ( m1_pre_topc(sK1,sK4(sK0,sK2(sK0,u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK1,sK0)
    | ~ v2_tex_2(u1_struct_0(sK1),sK0)
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_16
    | ~ spl5_22 ),
    inference(resolution,[],[f456,f134])).

fof(f134,plain,
    ( ! [X0] :
        ( r1_tarski(X0,sK2(sK0,X0))
        | ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f110,f81])).

fof(f110,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X0,sK0)
        | r1_tarski(X0,sK2(sK0,X0)) )
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f109,f66])).

fof(f109,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X0,sK0)
        | r1_tarski(X0,sK2(sK0,X0)) )
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f107,f71])).

fof(f71,plain,
    ( v2_pre_topc(sK0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl5_4
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f107,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X0,sK0)
        | r1_tarski(X0,sK2(sK0,X0)) )
    | ~ spl5_5 ),
    inference(resolution,[],[f76,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | r1_tarski(X1,sK2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f76,plain,
    ( v3_tdlat_3(sK0)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl5_5
  <=> v3_tdlat_3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f456,plain,
    ( ! [X0] :
        ( ~ r1_tarski(u1_struct_0(X0),sK2(sK0,u1_struct_0(sK1)))
        | m1_pre_topc(X0,sK4(sK0,sK2(sK0,u1_struct_0(sK1))))
        | ~ m1_pre_topc(X0,sK0) )
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_16
    | ~ spl5_22 ),
    inference(subsumption_resolution,[],[f455,f297])).

fof(f455,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(sK4(sK0,sK2(sK0,u1_struct_0(sK1))),sK0)
        | m1_pre_topc(X0,sK4(sK0,sK2(sK0,u1_struct_0(sK1))))
        | ~ r1_tarski(u1_struct_0(X0),sK2(sK0,u1_struct_0(sK1))) )
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f454,f81])).

fof(f454,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(sK4(sK0,sK2(sK0,u1_struct_0(sK1))),sK0)
        | m1_pre_topc(X0,sK4(sK0,sK2(sK0,u1_struct_0(sK1))))
        | ~ r1_tarski(u1_struct_0(X0),sK2(sK0,u1_struct_0(sK1))) )
    | ~ spl5_4
    | ~ spl5_16 ),
    inference(resolution,[],[f260,f71])).

fof(f260,plain,
    ( ! [X6,X7] :
        ( ~ v2_pre_topc(X7)
        | ~ l1_pre_topc(X7)
        | ~ m1_pre_topc(X6,X7)
        | ~ m1_pre_topc(sK4(sK0,sK2(sK0,u1_struct_0(sK1))),X7)
        | m1_pre_topc(X6,sK4(sK0,sK2(sK0,u1_struct_0(sK1))))
        | ~ r1_tarski(u1_struct_0(X6),sK2(sK0,u1_struct_0(sK1))) )
    | ~ spl5_16 ),
    inference(superposition,[],[f49,f253])).

fof(f253,plain,
    ( sK2(sK0,u1_struct_0(sK1)) = u1_struct_0(sK4(sK0,sK2(sK0,u1_struct_0(sK1))))
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f251])).

fof(f251,plain,
    ( spl5_16
  <=> sK2(sK0,u1_struct_0(sK1)) = u1_struct_0(sK4(sK0,sK2(sK0,u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | m1_pre_topc(X1,X2)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).

fof(f468,plain,
    ( spl5_3
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_23
    | ~ spl5_26
    | ~ spl5_27 ),
    inference(avatar_contradiction_clause,[],[f467])).

fof(f467,plain,
    ( $false
    | spl5_3
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_23
    | ~ spl5_26
    | ~ spl5_27 ),
    inference(subsumption_resolution,[],[f466,f302])).

fof(f466,plain,
    ( ~ v3_tex_2(sK2(sK0,u1_struct_0(sK1)),sK0)
    | spl5_3
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_26
    | ~ spl5_27 ),
    inference(subsumption_resolution,[],[f465,f364])).

fof(f364,plain,
    ( m1_subset_1(sK2(sK0,u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_27 ),
    inference(avatar_component_clause,[],[f363])).

fof(f363,plain,
    ( spl5_27
  <=> m1_subset_1(sK2(sK0,u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f465,plain,
    ( ~ m1_subset_1(sK2(sK0,u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_tex_2(sK2(sK0,u1_struct_0(sK1)),sK0)
    | spl5_3
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_26 ),
    inference(subsumption_resolution,[],[f464,f66])).

fof(f464,plain,
    ( v2_struct_0(sK0)
    | ~ m1_subset_1(sK2(sK0,u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_tex_2(sK2(sK0,u1_struct_0(sK1)),sK0)
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_26 ),
    inference(subsumption_resolution,[],[f463,f81])).

fof(f463,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK2(sK0,u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_tex_2(sK2(sK0,u1_struct_0(sK1)),sK0)
    | ~ spl5_4
    | ~ spl5_26 ),
    inference(resolution,[],[f457,f71])).

fof(f457,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ m1_subset_1(sK2(sK0,u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v3_tex_2(sK2(sK0,u1_struct_0(sK1)),X0) )
    | ~ spl5_26 ),
    inference(resolution,[],[f361,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => ~ v3_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_tex_2)).

fof(f361,plain,
    ( v1_xboole_0(sK2(sK0,u1_struct_0(sK1)))
    | ~ spl5_26 ),
    inference(avatar_component_clause,[],[f359])).

fof(f359,plain,
    ( spl5_26
  <=> v1_xboole_0(sK2(sK0,u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f451,plain,
    ( spl5_3
    | ~ spl5_6
    | spl5_26
    | ~ spl5_27
    | spl5_32 ),
    inference(avatar_contradiction_clause,[],[f450])).

fof(f450,plain,
    ( $false
    | spl5_3
    | ~ spl5_6
    | spl5_26
    | ~ spl5_27
    | spl5_32 ),
    inference(subsumption_resolution,[],[f449,f66])).

fof(f449,plain,
    ( v2_struct_0(sK0)
    | ~ spl5_6
    | spl5_26
    | ~ spl5_27
    | spl5_32 ),
    inference(subsumption_resolution,[],[f448,f364])).

fof(f448,plain,
    ( ~ m1_subset_1(sK2(sK0,u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl5_6
    | spl5_26
    | spl5_32 ),
    inference(subsumption_resolution,[],[f447,f360])).

fof(f360,plain,
    ( ~ v1_xboole_0(sK2(sK0,u1_struct_0(sK1)))
    | spl5_26 ),
    inference(avatar_component_clause,[],[f359])).

fof(f447,plain,
    ( v1_xboole_0(sK2(sK0,u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2(sK0,u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl5_6
    | spl5_32 ),
    inference(subsumption_resolution,[],[f446,f81])).

fof(f446,plain,
    ( ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK2(sK0,u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2(sK0,u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | spl5_32 ),
    inference(resolution,[],[f441,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(sK4(X0,X1))
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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

fof(f441,plain,
    ( ~ v1_pre_topc(sK4(sK0,sK2(sK0,u1_struct_0(sK1))))
    | spl5_32 ),
    inference(avatar_component_clause,[],[f439])).

fof(f439,plain,
    ( spl5_32
  <=> v1_pre_topc(sK4(sK0,sK2(sK0,u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f442,plain,
    ( ~ spl5_31
    | ~ spl5_32
    | spl5_15
    | ~ spl5_21
    | ~ spl5_22 ),
    inference(avatar_split_clause,[],[f428,f296,f292,f236,f439,f435])).

fof(f236,plain,
    ( spl5_15
  <=> v2_struct_0(sK4(sK0,sK2(sK0,u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f428,plain,
    ( ~ v1_pre_topc(sK4(sK0,sK2(sK0,u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK1,sK4(sK0,sK2(sK0,u1_struct_0(sK1))))
    | spl5_15
    | ~ spl5_21
    | ~ spl5_22 ),
    inference(subsumption_resolution,[],[f427,f238])).

fof(f238,plain,
    ( ~ v2_struct_0(sK4(sK0,sK2(sK0,u1_struct_0(sK1))))
    | spl5_15 ),
    inference(avatar_component_clause,[],[f236])).

fof(f427,plain,
    ( ~ v1_pre_topc(sK4(sK0,sK2(sK0,u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK1,sK4(sK0,sK2(sK0,u1_struct_0(sK1))))
    | v2_struct_0(sK4(sK0,sK2(sK0,u1_struct_0(sK1))))
    | ~ spl5_21
    | ~ spl5_22 ),
    inference(subsumption_resolution,[],[f422,f297])).

fof(f422,plain,
    ( ~ v1_pre_topc(sK4(sK0,sK2(sK0,u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK4(sK0,sK2(sK0,u1_struct_0(sK1))),sK0)
    | ~ m1_pre_topc(sK1,sK4(sK0,sK2(sK0,u1_struct_0(sK1))))
    | v2_struct_0(sK4(sK0,sK2(sK0,u1_struct_0(sK1))))
    | ~ spl5_21 ),
    inference(resolution,[],[f293,f25])).

fof(f25,plain,(
    ! [X2] :
      ( ~ v4_tex_2(X2,sK0)
      | ~ v1_pre_topc(X2)
      | ~ m1_pre_topc(X2,sK0)
      | ~ m1_pre_topc(sK1,X2)
      | v2_struct_0(X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ~ v4_tex_2(X2,X0)
              | ~ m1_pre_topc(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & v1_tdlat_3(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ~ v4_tex_2(X2,X0)
              | ~ m1_pre_topc(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & v1_tdlat_3(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v3_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & v1_tdlat_3(X1)
              & ~ v2_struct_0(X1) )
           => ? [X2] :
                ( v4_tex_2(X2,X0)
                & m1_pre_topc(X1,X2)
                & m1_pre_topc(X2,X0)
                & v1_pre_topc(X2)
                & ~ v2_struct_0(X2) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & v1_tdlat_3(X1)
            & ~ v2_struct_0(X1) )
         => ? [X2] :
              ( v4_tex_2(X2,X0)
              & m1_pre_topc(X1,X2)
              & m1_pre_topc(X2,X0)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_tex_2)).

fof(f293,plain,
    ( v4_tex_2(sK4(sK0,sK2(sK0,u1_struct_0(sK1))),sK0)
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f292])).

fof(f419,plain,
    ( spl5_30
    | spl5_3
    | ~ spl5_6
    | ~ spl5_16
    | spl5_21
    | ~ spl5_22 ),
    inference(avatar_split_clause,[],[f411,f296,f292,f251,f79,f64,f416])).

fof(f411,plain,
    ( sK2(sK0,u1_struct_0(sK1)) = sK3(sK0,sK4(sK0,sK2(sK0,u1_struct_0(sK1))))
    | spl5_3
    | ~ spl5_6
    | ~ spl5_16
    | spl5_21
    | ~ spl5_22 ),
    inference(subsumption_resolution,[],[f309,f297])).

fof(f309,plain,
    ( sK2(sK0,u1_struct_0(sK1)) = sK3(sK0,sK4(sK0,sK2(sK0,u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK4(sK0,sK2(sK0,u1_struct_0(sK1))),sK0)
    | spl5_3
    | ~ spl5_6
    | ~ spl5_16
    | spl5_21 ),
    inference(forward_demodulation,[],[f308,f253])).

fof(f308,plain,
    ( u1_struct_0(sK4(sK0,sK2(sK0,u1_struct_0(sK1)))) = sK3(sK0,sK4(sK0,sK2(sK0,u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK4(sK0,sK2(sK0,u1_struct_0(sK1))),sK0)
    | spl5_3
    | ~ spl5_6
    | spl5_21 ),
    inference(resolution,[],[f294,f126])).

fof(f126,plain,
    ( ! [X0] :
        ( v4_tex_2(X0,sK0)
        | u1_struct_0(X0) = sK3(sK0,X0)
        | ~ m1_pre_topc(X0,sK0) )
    | spl5_3
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f97,f81])).

fof(f97,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_pre_topc(X0,sK0)
        | u1_struct_0(X0) = sK3(sK0,X0)
        | v4_tex_2(X0,sK0) )
    | spl5_3 ),
    inference(resolution,[],[f66,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | u1_struct_0(X1) = sK3(X0,X1)
      | v4_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

% (6951)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f382,plain,
    ( spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_24
    | ~ spl5_25
    | spl5_27 ),
    inference(avatar_contradiction_clause,[],[f381])).

fof(f381,plain,
    ( $false
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_24
    | ~ spl5_25
    | spl5_27 ),
    inference(subsumption_resolution,[],[f380,f66])).

fof(f380,plain,
    ( v2_struct_0(sK0)
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_24
    | ~ spl5_25
    | spl5_27 ),
    inference(subsumption_resolution,[],[f379,f320])).

fof(f379,plain,
    ( ~ v2_tex_2(u1_struct_0(sK1),sK0)
    | v2_struct_0(sK0)
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_24
    | spl5_27 ),
    inference(subsumption_resolution,[],[f378,f316])).

fof(f378,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tex_2(u1_struct_0(sK1),sK0)
    | v2_struct_0(sK0)
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | spl5_27 ),
    inference(subsumption_resolution,[],[f377,f81])).

fof(f377,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tex_2(u1_struct_0(sK1),sK0)
    | v2_struct_0(sK0)
    | ~ spl5_4
    | ~ spl5_5
    | spl5_27 ),
    inference(subsumption_resolution,[],[f376,f76])).

fof(f376,plain,
    ( ~ v3_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tex_2(u1_struct_0(sK1),sK0)
    | v2_struct_0(sK0)
    | ~ spl5_4
    | spl5_27 ),
    inference(subsumption_resolution,[],[f375,f71])).

fof(f375,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ v3_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tex_2(u1_struct_0(sK1),sK0)
    | v2_struct_0(sK0)
    | spl5_27 ),
    inference(resolution,[],[f365,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f365,plain,
    ( ~ m1_subset_1(sK2(sK0,u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_27 ),
    inference(avatar_component_clause,[],[f363])).

fof(f366,plain,
    ( spl5_26
    | ~ spl5_27
    | spl5_3
    | ~ spl5_6
    | spl5_22 ),
    inference(avatar_split_clause,[],[f310,f296,f79,f64,f363,f359])).

fof(f310,plain,
    ( ~ m1_subset_1(sK2(sK0,u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK2(sK0,u1_struct_0(sK1)))
    | spl5_3
    | ~ spl5_6
    | spl5_22 ),
    inference(resolution,[],[f298,f129])).

fof(f129,plain,
    ( ! [X3] :
        ( m1_pre_topc(sK4(sK0,X3),sK0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X3) )
    | spl5_3
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f100,f81])).

fof(f100,plain,
    ( ! [X3] :
        ( ~ l1_pre_topc(sK0)
        | v1_xboole_0(X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_pre_topc(sK4(sK0,X3),sK0) )
    | spl5_3 ),
    inference(resolution,[],[f66,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_pre_topc(sK4(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f298,plain,
    ( ~ m1_pre_topc(sK4(sK0,sK2(sK0,u1_struct_0(sK1))),sK0)
    | spl5_22 ),
    inference(avatar_component_clause,[],[f296])).

fof(f345,plain,
    ( ~ spl5_6
    | ~ spl5_7
    | spl5_24 ),
    inference(avatar_contradiction_clause,[],[f344])).

fof(f344,plain,
    ( $false
    | ~ spl5_6
    | ~ spl5_7
    | spl5_24 ),
    inference(subsumption_resolution,[],[f343,f81])).

fof(f343,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl5_7
    | spl5_24 ),
    inference(subsumption_resolution,[],[f342,f86])).

fof(f342,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | spl5_24 ),
    inference(resolution,[],[f317,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f317,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_24 ),
    inference(avatar_component_clause,[],[f315])).

fof(f335,plain,
    ( spl5_1
    | ~ spl5_2
    | spl5_3
    | ~ spl5_6
    | ~ spl5_7
    | spl5_25 ),
    inference(avatar_contradiction_clause,[],[f334])).

fof(f334,plain,
    ( $false
    | spl5_1
    | ~ spl5_2
    | spl5_3
    | ~ spl5_6
    | ~ spl5_7
    | spl5_25 ),
    inference(subsumption_resolution,[],[f333,f56])).

fof(f56,plain,
    ( ~ v2_struct_0(sK1)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl5_1
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f333,plain,
    ( v2_struct_0(sK1)
    | ~ spl5_2
    | spl5_3
    | ~ spl5_6
    | ~ spl5_7
    | spl5_25 ),
    inference(subsumption_resolution,[],[f332,f61])).

fof(f61,plain,
    ( v1_tdlat_3(sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl5_2
  <=> v1_tdlat_3(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f332,plain,
    ( ~ v1_tdlat_3(sK1)
    | v2_struct_0(sK1)
    | spl5_3
    | ~ spl5_6
    | ~ spl5_7
    | spl5_25 ),
    inference(subsumption_resolution,[],[f331,f86])).

fof(f331,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ v1_tdlat_3(sK1)
    | v2_struct_0(sK1)
    | spl5_3
    | ~ spl5_6
    | spl5_25 ),
    inference(resolution,[],[f321,f125])).

fof(f125,plain,
    ( ! [X6] :
        ( v2_tex_2(u1_struct_0(X6),sK0)
        | ~ m1_pre_topc(X6,sK0)
        | ~ v1_tdlat_3(X6)
        | v2_struct_0(X6) )
    | spl5_3
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f105,f81])).

fof(f105,plain,
    ( ! [X6] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(X6,sK0)
        | ~ v1_tdlat_3(X6)
        | v2_tex_2(u1_struct_0(X6),sK0) )
    | spl5_3 ),
    inference(subsumption_resolution,[],[f103,f33])).

fof(f103,plain,
    ( ! [X6] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(X6,sK0)
        | ~ m1_subset_1(u1_struct_0(X6),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_tdlat_3(X6)
        | v2_tex_2(u1_struct_0(X6),sK0) )
    | spl5_3 ),
    inference(resolution,[],[f66,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tdlat_3(X1)
      | v2_tex_2(u1_struct_0(X1),X0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X1) != X2
      | ~ v1_tdlat_3(X1)
      | v2_tex_2(X2,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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

fof(f321,plain,
    ( ~ v2_tex_2(u1_struct_0(sK1),sK0)
    | spl5_25 ),
    inference(avatar_component_clause,[],[f319])).

fof(f322,plain,
    ( ~ spl5_24
    | ~ spl5_25
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | spl5_23 ),
    inference(avatar_split_clause,[],[f304,f300,f79,f74,f69,f64,f319,f315])).

fof(f304,plain,
    ( ~ v2_tex_2(u1_struct_0(sK1),sK0)
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | spl5_23 ),
    inference(resolution,[],[f301,f135])).

fof(f135,plain,
    ( ! [X1] :
        ( v3_tex_2(sK2(sK0,X1),sK0)
        | ~ v2_tex_2(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f112,f81])).

fof(f112,plain,
    ( ! [X1] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X1,sK0)
        | v3_tex_2(sK2(sK0,X1),sK0) )
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f111,f66])).

fof(f111,plain,
    ( ! [X1] :
        ( v2_struct_0(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X1,sK0)
        | v3_tex_2(sK2(sK0,X1),sK0) )
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f108,f71])).

fof(f108,plain,
    ( ! [X1] :
        ( ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X1,sK0)
        | v3_tex_2(sK2(sK0,X1),sK0) )
    | ~ spl5_5 ),
    inference(resolution,[],[f76,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | v3_tex_2(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f301,plain,
    ( ~ v3_tex_2(sK2(sK0,u1_struct_0(sK1)),sK0)
    | spl5_23 ),
    inference(avatar_component_clause,[],[f300])).

fof(f254,plain,
    ( spl5_16
    | spl5_1
    | ~ spl5_2
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f232,f84,f79,f74,f69,f64,f59,f54,f251])).

fof(f232,plain,
    ( sK2(sK0,u1_struct_0(sK1)) = u1_struct_0(sK4(sK0,sK2(sK0,u1_struct_0(sK1))))
    | spl5_1
    | ~ spl5_2
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f231,f56])).

fof(f231,plain,
    ( sK2(sK0,u1_struct_0(sK1)) = u1_struct_0(sK4(sK0,sK2(sK0,u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | ~ spl5_2
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f228,f86])).

fof(f228,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | sK2(sK0,u1_struct_0(sK1)) = u1_struct_0(sK4(sK0,sK2(sK0,u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | ~ spl5_2
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(resolution,[],[f201,f61])).

fof(f201,plain,
    ( ! [X0] :
        ( ~ v1_tdlat_3(X0)
        | ~ m1_pre_topc(X0,sK0)
        | sK2(sK0,u1_struct_0(X0)) = u1_struct_0(sK4(sK0,sK2(sK0,u1_struct_0(X0))))
        | v2_struct_0(X0) )
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f200,f81])).

fof(f200,plain,
    ( ! [X0] :
        ( sK2(sK0,u1_struct_0(X0)) = u1_struct_0(sK4(sK0,sK2(sK0,u1_struct_0(X0))))
        | ~ m1_pre_topc(X0,sK0)
        | ~ v1_tdlat_3(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK0) )
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(duplicate_literal_removal,[],[f199])).

fof(f199,plain,
    ( ! [X0] :
        ( sK2(sK0,u1_struct_0(X0)) = u1_struct_0(sK4(sK0,sK2(sK0,u1_struct_0(X0))))
        | ~ m1_pre_topc(X0,sK0)
        | ~ v1_tdlat_3(X0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ l1_pre_topc(sK0) )
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(resolution,[],[f184,f33])).

fof(f184,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | sK2(sK0,u1_struct_0(X0)) = u1_struct_0(sK4(sK0,sK2(sK0,u1_struct_0(X0))))
        | ~ m1_pre_topc(X0,sK0)
        | ~ v1_tdlat_3(X0)
        | v2_struct_0(X0) )
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(resolution,[],[f171,f125])).

fof(f171,plain,
    ( ! [X0] :
        ( ~ v2_tex_2(X0,sK0)
        | sK2(sK0,X0) = u1_struct_0(sK4(sK0,sK2(sK0,X0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f170,f66])).

fof(f170,plain,
    ( ! [X0] :
        ( sK2(sK0,X0) = u1_struct_0(sK4(sK0,sK2(sK0,X0)))
        | ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_struct_0(sK0) )
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f169,f81])).

fof(f169,plain,
    ( ! [X0] :
        ( sK2(sK0,X0) = u1_struct_0(sK4(sK0,sK2(sK0,X0)))
        | ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f168,f76])).

fof(f168,plain,
    ( ! [X0] :
        ( sK2(sK0,X0) = u1_struct_0(sK4(sK0,sK2(sK0,X0)))
        | ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_tdlat_3(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f167,f71])).

fof(f167,plain,
    ( ! [X0] :
        ( sK2(sK0,X0) = u1_struct_0(sK4(sK0,sK2(sK0,X0)))
        | ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_pre_topc(sK0)
        | ~ v3_tdlat_3(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(duplicate_literal_removal,[],[f166])).

fof(f166,plain,
    ( ! [X0] :
        ( sK2(sK0,X0) = u1_struct_0(sK4(sK0,sK2(sK0,X0)))
        | ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_pre_topc(sK0)
        | ~ v3_tdlat_3(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X0,sK0)
        | v2_struct_0(sK0) )
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(resolution,[],[f149,f34])).

fof(f149,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK2(sK0,X1),k1_zfmisc_1(u1_struct_0(sK0)))
        | sK2(sK0,X1) = u1_struct_0(sK4(sK0,sK2(sK0,X1)))
        | ~ v2_tex_2(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(resolution,[],[f145,f135])).

fof(f145,plain,
    ( ! [X0] :
        ( ~ v3_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | u1_struct_0(sK4(sK0,X0)) = X0 )
    | spl5_3
    | ~ spl5_4
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f144,f66])).

fof(f144,plain,
    ( ! [X0] :
        ( u1_struct_0(sK4(sK0,X0)) = X0
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_struct_0(sK0)
        | ~ v3_tex_2(X0,sK0) )
    | spl5_3
    | ~ spl5_4
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f143,f81])).

fof(f143,plain,
    ( ! [X0] :
        ( u1_struct_0(sK4(sK0,X0)) = X0
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ v3_tex_2(X0,sK0) )
    | spl5_3
    | ~ spl5_4
    | ~ spl5_6 ),
    inference(duplicate_literal_removal,[],[f142])).

fof(f142,plain,
    ( ! [X0] :
        ( u1_struct_0(sK4(sK0,X0)) = X0
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_tex_2(X0,sK0) )
    | spl5_3
    | ~ spl5_4
    | ~ spl5_6 ),
    inference(resolution,[],[f131,f71])).

% (6957)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
fof(f131,plain,
    ( ! [X0,X1] :
        ( ~ v2_pre_topc(X1)
        | u1_struct_0(sK4(sK0,X0)) = X0
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ v3_tex_2(X0,X1) )
    | spl5_3
    | ~ spl5_6 ),
    inference(resolution,[],[f130,f37])).

fof(f130,plain,
    ( ! [X4] :
        ( v1_xboole_0(X4)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | u1_struct_0(sK4(sK0,X4)) = X4 )
    | spl5_3
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f101,f81])).

fof(f101,plain,
    ( ! [X4] :
        ( ~ l1_pre_topc(sK0)
        | v1_xboole_0(X4)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | u1_struct_0(sK4(sK0,X4)) = X4 )
    | spl5_3 ),
    inference(resolution,[],[f66,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(sK4(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f239,plain,
    ( ~ spl5_15
    | spl5_1
    | ~ spl5_2
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f226,f84,f79,f74,f69,f64,f59,f54,f236])).

fof(f226,plain,
    ( ~ v2_struct_0(sK4(sK0,sK2(sK0,u1_struct_0(sK1))))
    | spl5_1
    | ~ spl5_2
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f225,f56])).

fof(f225,plain,
    ( ~ v2_struct_0(sK4(sK0,sK2(sK0,u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | ~ spl5_2
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f222,f86])).

fof(f222,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ v2_struct_0(sK4(sK0,sK2(sK0,u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | ~ spl5_2
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(resolution,[],[f198,f61])).

fof(f198,plain,
    ( ! [X0] :
        ( ~ v1_tdlat_3(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ v2_struct_0(sK4(sK0,sK2(sK0,u1_struct_0(X0))))
        | v2_struct_0(X0) )
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f197,f81])).

fof(f197,plain,
    ( ! [X0] :
        ( ~ v2_struct_0(sK4(sK0,sK2(sK0,u1_struct_0(X0))))
        | ~ m1_pre_topc(X0,sK0)
        | ~ v1_tdlat_3(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK0) )
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(duplicate_literal_removal,[],[f196])).

fof(f196,plain,
    ( ! [X0] :
        ( ~ v2_struct_0(sK4(sK0,sK2(sK0,u1_struct_0(X0))))
        | ~ m1_pre_topc(X0,sK0)
        | ~ v1_tdlat_3(X0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ l1_pre_topc(sK0) )
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(resolution,[],[f174,f33])).

fof(f174,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_struct_0(sK4(sK0,sK2(sK0,u1_struct_0(X0))))
        | ~ m1_pre_topc(X0,sK0)
        | ~ v1_tdlat_3(X0)
        | v2_struct_0(X0) )
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(resolution,[],[f165,f125])).

fof(f165,plain,
    ( ! [X0] :
        ( ~ v2_tex_2(X0,sK0)
        | ~ v2_struct_0(sK4(sK0,sK2(sK0,X0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f164,f66])).

fof(f164,plain,
    ( ! [X0] :
        ( ~ v2_struct_0(sK4(sK0,sK2(sK0,X0)))
        | ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_struct_0(sK0) )
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f163,f81])).

fof(f163,plain,
    ( ! [X0] :
        ( ~ v2_struct_0(sK4(sK0,sK2(sK0,X0)))
        | ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f162,f76])).

fof(f162,plain,
    ( ! [X0] :
        ( ~ v2_struct_0(sK4(sK0,sK2(sK0,X0)))
        | ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_tdlat_3(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f161,f71])).

fof(f161,plain,
    ( ! [X0] :
        ( ~ v2_struct_0(sK4(sK0,sK2(sK0,X0)))
        | ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_pre_topc(sK0)
        | ~ v3_tdlat_3(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(duplicate_literal_removal,[],[f160])).

fof(f160,plain,
    ( ! [X0] :
        ( ~ v2_struct_0(sK4(sK0,sK2(sK0,X0)))
        | ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_pre_topc(sK0)
        | ~ v3_tdlat_3(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X0,sK0)
        | v2_struct_0(sK0) )
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(resolution,[],[f147,f34])).

fof(f147,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK2(sK0,X1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_struct_0(sK4(sK0,sK2(sK0,X1)))
        | ~ v2_tex_2(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(resolution,[],[f141,f135])).

fof(f141,plain,
    ( ! [X0] :
        ( ~ v3_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_struct_0(sK4(sK0,X0)) )
    | spl5_3
    | ~ spl5_4
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f140,f66])).

fof(f140,plain,
    ( ! [X0] :
        ( ~ v2_struct_0(sK4(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_struct_0(sK0)
        | ~ v3_tex_2(X0,sK0) )
    | spl5_3
    | ~ spl5_4
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f139,f81])).

fof(f139,plain,
    ( ! [X0] :
        ( ~ v2_struct_0(sK4(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ v3_tex_2(X0,sK0) )
    | spl5_3
    | ~ spl5_4
    | ~ spl5_6 ),
    inference(duplicate_literal_removal,[],[f138])).

fof(f138,plain,
    ( ! [X0] :
        ( ~ v2_struct_0(sK4(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_tex_2(X0,sK0) )
    | spl5_3
    | ~ spl5_4
    | ~ spl5_6 ),
    inference(resolution,[],[f124,f71])).

fof(f124,plain,
    ( ! [X0,X1] :
        ( ~ v2_pre_topc(X1)
        | ~ v2_struct_0(sK4(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ v3_tex_2(X0,X1) )
    | spl5_3
    | ~ spl5_6 ),
    inference(resolution,[],[f123,f37])).

fof(f123,plain,
    ( ! [X2] :
        ( v1_xboole_0(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_struct_0(sK4(sK0,X2)) )
    | spl5_3
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f99,f81])).

fof(f99,plain,
    ( ! [X2] :
        ( ~ l1_pre_topc(sK0)
        | v1_xboole_0(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_struct_0(sK4(sK0,X2)) )
    | spl5_3 ),
    inference(resolution,[],[f66,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_struct_0(sK4(X0,X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f87,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f28,f84])).

fof(f28,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f82,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f32,f79])).

fof(f32,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f77,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f31,f74])).

fof(f31,plain,(
    v3_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f72,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f30,f69])).

fof(f30,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f67,plain,(
    ~ spl5_3 ),
    inference(avatar_split_clause,[],[f29,f64])).

fof(f29,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f62,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f27,f59])).

fof(f27,plain,(
    v1_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f57,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f26,f54])).

fof(f26,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:07:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (6941)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.47  % (6942)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.47  % (6943)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.48  % (6944)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.49  % (6949)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.49  % (6954)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.49  % (6950)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.49  % (6945)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.49  % (6939)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.50  % (6946)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.50  % (6942)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f527,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(avatar_sat_refutation,[],[f57,f62,f67,f72,f77,f82,f87,f239,f254,f322,f335,f345,f366,f382,f419,f442,f451,f468,f492,f526])).
% 0.20/0.50  fof(f526,plain,(
% 0.20/0.50    spl5_3 | ~spl5_6 | spl5_21 | ~spl5_22 | ~spl5_23 | ~spl5_30),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f525])).
% 0.20/0.50  fof(f525,plain,(
% 0.20/0.50    $false | (spl5_3 | ~spl5_6 | spl5_21 | ~spl5_22 | ~spl5_23 | ~spl5_30)),
% 0.20/0.50    inference(subsumption_resolution,[],[f524,f294])).
% 0.20/0.50  fof(f294,plain,(
% 0.20/0.50    ~v4_tex_2(sK4(sK0,sK2(sK0,u1_struct_0(sK1))),sK0) | spl5_21),
% 0.20/0.50    inference(avatar_component_clause,[],[f292])).
% 0.20/0.50  fof(f292,plain,(
% 0.20/0.50    spl5_21 <=> v4_tex_2(sK4(sK0,sK2(sK0,u1_struct_0(sK1))),sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 0.20/0.50  fof(f524,plain,(
% 0.20/0.50    v4_tex_2(sK4(sK0,sK2(sK0,u1_struct_0(sK1))),sK0) | (spl5_3 | ~spl5_6 | ~spl5_22 | ~spl5_23 | ~spl5_30)),
% 0.20/0.50    inference(subsumption_resolution,[],[f523,f297])).
% 0.20/0.50  fof(f297,plain,(
% 0.20/0.50    m1_pre_topc(sK4(sK0,sK2(sK0,u1_struct_0(sK1))),sK0) | ~spl5_22),
% 0.20/0.50    inference(avatar_component_clause,[],[f296])).
% 0.20/0.50  fof(f296,plain,(
% 0.20/0.50    spl5_22 <=> m1_pre_topc(sK4(sK0,sK2(sK0,u1_struct_0(sK1))),sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 0.20/0.50  fof(f523,plain,(
% 0.20/0.50    ~m1_pre_topc(sK4(sK0,sK2(sK0,u1_struct_0(sK1))),sK0) | v4_tex_2(sK4(sK0,sK2(sK0,u1_struct_0(sK1))),sK0) | (spl5_3 | ~spl5_6 | ~spl5_23 | ~spl5_30)),
% 0.20/0.50    inference(subsumption_resolution,[],[f521,f302])).
% 0.20/0.50  fof(f302,plain,(
% 0.20/0.50    v3_tex_2(sK2(sK0,u1_struct_0(sK1)),sK0) | ~spl5_23),
% 0.20/0.50    inference(avatar_component_clause,[],[f300])).
% 0.20/0.50  fof(f300,plain,(
% 0.20/0.50    spl5_23 <=> v3_tex_2(sK2(sK0,u1_struct_0(sK1)),sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 0.20/0.50  fof(f521,plain,(
% 0.20/0.50    ~v3_tex_2(sK2(sK0,u1_struct_0(sK1)),sK0) | ~m1_pre_topc(sK4(sK0,sK2(sK0,u1_struct_0(sK1))),sK0) | v4_tex_2(sK4(sK0,sK2(sK0,u1_struct_0(sK1))),sK0) | (spl5_3 | ~spl5_6 | ~spl5_30)),
% 0.20/0.50    inference(superposition,[],[f122,f418])).
% 0.20/0.50  fof(f418,plain,(
% 0.20/0.50    sK2(sK0,u1_struct_0(sK1)) = sK3(sK0,sK4(sK0,sK2(sK0,u1_struct_0(sK1)))) | ~spl5_30),
% 0.20/0.50    inference(avatar_component_clause,[],[f416])).
% 0.20/0.50  fof(f416,plain,(
% 0.20/0.50    spl5_30 <=> sK2(sK0,u1_struct_0(sK1)) = sK3(sK0,sK4(sK0,sK2(sK0,u1_struct_0(sK1))))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).
% 0.20/0.50  fof(f122,plain,(
% 0.20/0.50    ( ! [X1] : (~v3_tex_2(sK3(sK0,X1),sK0) | ~m1_pre_topc(X1,sK0) | v4_tex_2(X1,sK0)) ) | (spl5_3 | ~spl5_6)),
% 0.20/0.50    inference(subsumption_resolution,[],[f98,f81])).
% 0.20/0.50  fof(f81,plain,(
% 0.20/0.50    l1_pre_topc(sK0) | ~spl5_6),
% 0.20/0.50    inference(avatar_component_clause,[],[f79])).
% 0.20/0.50  fof(f79,plain,(
% 0.20/0.50    spl5_6 <=> l1_pre_topc(sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.20/0.50  fof(f98,plain,(
% 0.20/0.50    ( ! [X1] : (~l1_pre_topc(sK0) | ~m1_pre_topc(X1,sK0) | ~v3_tex_2(sK3(sK0,X1),sK0) | v4_tex_2(X1,sK0)) ) | spl5_3),
% 0.20/0.50    inference(resolution,[],[f66,f41])).
% 0.20/0.50  fof(f41,plain,(
% 0.20/0.50    ( ! [X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~v3_tex_2(sK3(X0,X1),X0) | v4_tex_2(X1,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f18])).
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : ((v4_tex_2(X1,X0) <=> ! [X2] : (v3_tex_2(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f17])).
% 0.20/0.50  fof(f17,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : ((v4_tex_2(X1,X0) <=> ! [X2] : ((v3_tex_2(X2,X0) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => (v4_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v3_tex_2(X2,X0))))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_tex_2)).
% 0.20/0.50  fof(f66,plain,(
% 0.20/0.50    ~v2_struct_0(sK0) | spl5_3),
% 0.20/0.50    inference(avatar_component_clause,[],[f64])).
% 0.20/0.50  fof(f64,plain,(
% 0.20/0.50    spl5_3 <=> v2_struct_0(sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.20/0.50  fof(f492,plain,(
% 0.20/0.50    spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_7 | ~spl5_16 | ~spl5_22 | ~spl5_24 | ~spl5_25 | spl5_31),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f491])).
% 0.20/0.50  fof(f491,plain,(
% 0.20/0.50    $false | (spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_7 | ~spl5_16 | ~spl5_22 | ~spl5_24 | ~spl5_25 | spl5_31)),
% 0.20/0.50    inference(subsumption_resolution,[],[f490,f316])).
% 0.20/0.50  fof(f316,plain,(
% 0.20/0.50    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_24),
% 0.20/0.50    inference(avatar_component_clause,[],[f315])).
% 0.20/0.50  fof(f315,plain,(
% 0.20/0.50    spl5_24 <=> m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 0.20/0.50  fof(f490,plain,(
% 0.20/0.50    ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_7 | ~spl5_16 | ~spl5_22 | ~spl5_25 | spl5_31)),
% 0.20/0.50    inference(subsumption_resolution,[],[f489,f320])).
% 0.20/0.50  fof(f320,plain,(
% 0.20/0.50    v2_tex_2(u1_struct_0(sK1),sK0) | ~spl5_25),
% 0.20/0.50    inference(avatar_component_clause,[],[f319])).
% 0.20/0.50  fof(f319,plain,(
% 0.20/0.50    spl5_25 <=> v2_tex_2(u1_struct_0(sK1),sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 0.20/0.50  fof(f489,plain,(
% 0.20/0.50    ~v2_tex_2(u1_struct_0(sK1),sK0) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_7 | ~spl5_16 | ~spl5_22 | spl5_31)),
% 0.20/0.50    inference(subsumption_resolution,[],[f488,f86])).
% 0.20/0.50  fof(f86,plain,(
% 0.20/0.50    m1_pre_topc(sK1,sK0) | ~spl5_7),
% 0.20/0.50    inference(avatar_component_clause,[],[f84])).
% 0.20/0.50  fof(f84,plain,(
% 0.20/0.50    spl5_7 <=> m1_pre_topc(sK1,sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.20/0.50  fof(f488,plain,(
% 0.20/0.50    ~m1_pre_topc(sK1,sK0) | ~v2_tex_2(u1_struct_0(sK1),sK0) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_16 | ~spl5_22 | spl5_31)),
% 0.20/0.50    inference(subsumption_resolution,[],[f486,f437])).
% 0.20/0.50  fof(f437,plain,(
% 0.20/0.50    ~m1_pre_topc(sK1,sK4(sK0,sK2(sK0,u1_struct_0(sK1)))) | spl5_31),
% 0.20/0.50    inference(avatar_component_clause,[],[f435])).
% 0.20/0.50  fof(f435,plain,(
% 0.20/0.50    spl5_31 <=> m1_pre_topc(sK1,sK4(sK0,sK2(sK0,u1_struct_0(sK1))))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).
% 0.20/0.50  fof(f486,plain,(
% 0.20/0.50    m1_pre_topc(sK1,sK4(sK0,sK2(sK0,u1_struct_0(sK1)))) | ~m1_pre_topc(sK1,sK0) | ~v2_tex_2(u1_struct_0(sK1),sK0) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_16 | ~spl5_22)),
% 0.20/0.50    inference(resolution,[],[f456,f134])).
% 0.20/0.50  fof(f134,plain,(
% 0.20/0.50    ( ! [X0] : (r1_tarski(X0,sK2(sK0,X0)) | ~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6)),
% 0.20/0.50    inference(subsumption_resolution,[],[f110,f81])).
% 0.20/0.50  fof(f110,plain,(
% 0.20/0.50    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X0,sK0) | r1_tarski(X0,sK2(sK0,X0))) ) | (spl5_3 | ~spl5_4 | ~spl5_5)),
% 0.20/0.50    inference(subsumption_resolution,[],[f109,f66])).
% 0.20/0.50  fof(f109,plain,(
% 0.20/0.50    ( ! [X0] : (v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X0,sK0) | r1_tarski(X0,sK2(sK0,X0))) ) | (~spl5_4 | ~spl5_5)),
% 0.20/0.50    inference(subsumption_resolution,[],[f107,f71])).
% 0.20/0.50  fof(f71,plain,(
% 0.20/0.50    v2_pre_topc(sK0) | ~spl5_4),
% 0.20/0.50    inference(avatar_component_clause,[],[f69])).
% 0.20/0.50  fof(f69,plain,(
% 0.20/0.50    spl5_4 <=> v2_pre_topc(sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.20/0.50  fof(f107,plain,(
% 0.20/0.50    ( ! [X0] : (~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X0,sK0) | r1_tarski(X0,sK2(sK0,X0))) ) | ~spl5_5),
% 0.20/0.50    inference(resolution,[],[f76,f35])).
% 0.20/0.50  fof(f35,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | r1_tarski(X1,sK2(X0,X1))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f14])).
% 0.20/0.50  fof(f14,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (? [X2] : (v3_tex_2(X2,X0) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f13])).
% 0.20/0.50  fof(f13,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : ((? [X2] : ((v3_tex_2(X2,X0) & r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f7])).
% 0.20/0.50  fof(f7,axiom,(
% 0.20/0.50    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(v3_tex_2(X2,X0) & r1_tarski(X1,X2))) & v2_tex_2(X1,X0))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tex_2)).
% 0.20/0.50  fof(f76,plain,(
% 0.20/0.50    v3_tdlat_3(sK0) | ~spl5_5),
% 0.20/0.50    inference(avatar_component_clause,[],[f74])).
% 0.20/0.50  fof(f74,plain,(
% 0.20/0.50    spl5_5 <=> v3_tdlat_3(sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.20/0.50  fof(f456,plain,(
% 0.20/0.50    ( ! [X0] : (~r1_tarski(u1_struct_0(X0),sK2(sK0,u1_struct_0(sK1))) | m1_pre_topc(X0,sK4(sK0,sK2(sK0,u1_struct_0(sK1)))) | ~m1_pre_topc(X0,sK0)) ) | (~spl5_4 | ~spl5_6 | ~spl5_16 | ~spl5_22)),
% 0.20/0.50    inference(subsumption_resolution,[],[f455,f297])).
% 0.20/0.50  fof(f455,plain,(
% 0.20/0.50    ( ! [X0] : (~m1_pre_topc(X0,sK0) | ~m1_pre_topc(sK4(sK0,sK2(sK0,u1_struct_0(sK1))),sK0) | m1_pre_topc(X0,sK4(sK0,sK2(sK0,u1_struct_0(sK1)))) | ~r1_tarski(u1_struct_0(X0),sK2(sK0,u1_struct_0(sK1)))) ) | (~spl5_4 | ~spl5_6 | ~spl5_16)),
% 0.20/0.50    inference(subsumption_resolution,[],[f454,f81])).
% 0.20/0.50  fof(f454,plain,(
% 0.20/0.50    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(sK4(sK0,sK2(sK0,u1_struct_0(sK1))),sK0) | m1_pre_topc(X0,sK4(sK0,sK2(sK0,u1_struct_0(sK1)))) | ~r1_tarski(u1_struct_0(X0),sK2(sK0,u1_struct_0(sK1)))) ) | (~spl5_4 | ~spl5_16)),
% 0.20/0.50    inference(resolution,[],[f260,f71])).
% 0.20/0.50  fof(f260,plain,(
% 0.20/0.50    ( ! [X6,X7] : (~v2_pre_topc(X7) | ~l1_pre_topc(X7) | ~m1_pre_topc(X6,X7) | ~m1_pre_topc(sK4(sK0,sK2(sK0,u1_struct_0(sK1))),X7) | m1_pre_topc(X6,sK4(sK0,sK2(sK0,u1_struct_0(sK1)))) | ~r1_tarski(u1_struct_0(X6),sK2(sK0,u1_struct_0(sK1)))) ) | ~spl5_16),
% 0.20/0.50    inference(superposition,[],[f49,f253])).
% 0.20/0.50  fof(f253,plain,(
% 0.20/0.50    sK2(sK0,u1_struct_0(sK1)) = u1_struct_0(sK4(sK0,sK2(sK0,u1_struct_0(sK1)))) | ~spl5_16),
% 0.20/0.50    inference(avatar_component_clause,[],[f251])).
% 0.20/0.50  fof(f251,plain,(
% 0.20/0.50    spl5_16 <=> sK2(sK0,u1_struct_0(sK1)) = u1_struct_0(sK4(sK0,sK2(sK0,u1_struct_0(sK1))))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.20/0.50  fof(f49,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0) | m1_pre_topc(X1,X2) | ~v2_pre_topc(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f24])).
% 0.20/0.50  fof(f24,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.50    inference(flattening,[],[f23])).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).
% 0.20/0.50  fof(f468,plain,(
% 0.20/0.50    spl5_3 | ~spl5_4 | ~spl5_6 | ~spl5_23 | ~spl5_26 | ~spl5_27),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f467])).
% 0.20/0.50  fof(f467,plain,(
% 0.20/0.50    $false | (spl5_3 | ~spl5_4 | ~spl5_6 | ~spl5_23 | ~spl5_26 | ~spl5_27)),
% 0.20/0.50    inference(subsumption_resolution,[],[f466,f302])).
% 0.20/0.50  fof(f466,plain,(
% 0.20/0.50    ~v3_tex_2(sK2(sK0,u1_struct_0(sK1)),sK0) | (spl5_3 | ~spl5_4 | ~spl5_6 | ~spl5_26 | ~spl5_27)),
% 0.20/0.50    inference(subsumption_resolution,[],[f465,f364])).
% 0.20/0.50  fof(f364,plain,(
% 0.20/0.50    m1_subset_1(sK2(sK0,u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_27),
% 0.20/0.50    inference(avatar_component_clause,[],[f363])).
% 0.20/0.50  fof(f363,plain,(
% 0.20/0.50    spl5_27 <=> m1_subset_1(sK2(sK0,u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).
% 0.20/0.50  fof(f465,plain,(
% 0.20/0.50    ~m1_subset_1(sK2(sK0,u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_tex_2(sK2(sK0,u1_struct_0(sK1)),sK0) | (spl5_3 | ~spl5_4 | ~spl5_6 | ~spl5_26)),
% 0.20/0.50    inference(subsumption_resolution,[],[f464,f66])).
% 0.20/0.50  fof(f464,plain,(
% 0.20/0.50    v2_struct_0(sK0) | ~m1_subset_1(sK2(sK0,u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_tex_2(sK2(sK0,u1_struct_0(sK1)),sK0) | (~spl5_4 | ~spl5_6 | ~spl5_26)),
% 0.20/0.50    inference(subsumption_resolution,[],[f463,f81])).
% 0.20/0.50  fof(f463,plain,(
% 0.20/0.50    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_subset_1(sK2(sK0,u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_tex_2(sK2(sK0,u1_struct_0(sK1)),sK0) | (~spl5_4 | ~spl5_26)),
% 0.20/0.50    inference(resolution,[],[f457,f71])).
% 0.20/0.50  fof(f457,plain,(
% 0.20/0.50    ( ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~m1_subset_1(sK2(sK0,u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(X0))) | ~v3_tex_2(sK2(sK0,u1_struct_0(sK1)),X0)) ) | ~spl5_26),
% 0.20/0.50    inference(resolution,[],[f361,f37])).
% 0.20/0.50  fof(f37,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v1_xboole_0(X1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_tex_2(X1,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f16])).
% 0.20/0.50  fof(f16,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f15])).
% 0.20/0.50  fof(f15,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (~v3_tex_2(X1,X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f6])).
% 0.20/0.50  fof(f6,axiom,(
% 0.20/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => ~v3_tex_2(X1,X0)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_tex_2)).
% 0.20/0.50  fof(f361,plain,(
% 0.20/0.50    v1_xboole_0(sK2(sK0,u1_struct_0(sK1))) | ~spl5_26),
% 0.20/0.50    inference(avatar_component_clause,[],[f359])).
% 0.20/0.50  fof(f359,plain,(
% 0.20/0.50    spl5_26 <=> v1_xboole_0(sK2(sK0,u1_struct_0(sK1)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 0.20/0.50  fof(f451,plain,(
% 0.20/0.50    spl5_3 | ~spl5_6 | spl5_26 | ~spl5_27 | spl5_32),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f450])).
% 0.20/0.50  fof(f450,plain,(
% 0.20/0.50    $false | (spl5_3 | ~spl5_6 | spl5_26 | ~spl5_27 | spl5_32)),
% 0.20/0.50    inference(subsumption_resolution,[],[f449,f66])).
% 0.20/0.50  fof(f449,plain,(
% 0.20/0.50    v2_struct_0(sK0) | (~spl5_6 | spl5_26 | ~spl5_27 | spl5_32)),
% 0.20/0.50    inference(subsumption_resolution,[],[f448,f364])).
% 0.20/0.50  fof(f448,plain,(
% 0.20/0.50    ~m1_subset_1(sK2(sK0,u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (~spl5_6 | spl5_26 | spl5_32)),
% 0.20/0.50    inference(subsumption_resolution,[],[f447,f360])).
% 0.20/0.50  fof(f360,plain,(
% 0.20/0.50    ~v1_xboole_0(sK2(sK0,u1_struct_0(sK1))) | spl5_26),
% 0.20/0.50    inference(avatar_component_clause,[],[f359])).
% 0.20/0.50  fof(f447,plain,(
% 0.20/0.50    v1_xboole_0(sK2(sK0,u1_struct_0(sK1))) | ~m1_subset_1(sK2(sK0,u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (~spl5_6 | spl5_32)),
% 0.20/0.50    inference(subsumption_resolution,[],[f446,f81])).
% 0.20/0.50  fof(f446,plain,(
% 0.20/0.50    ~l1_pre_topc(sK0) | v1_xboole_0(sK2(sK0,u1_struct_0(sK1))) | ~m1_subset_1(sK2(sK0,u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | spl5_32),
% 0.20/0.50    inference(resolution,[],[f441,f43])).
% 0.20/0.50  fof(f43,plain,(
% 0.20/0.50    ( ! [X0,X1] : (v1_pre_topc(sK4(X0,X1)) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f20])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f19])).
% 0.20/0.50  fof(f19,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_tsep_1)).
% 0.20/0.50  fof(f441,plain,(
% 0.20/0.50    ~v1_pre_topc(sK4(sK0,sK2(sK0,u1_struct_0(sK1)))) | spl5_32),
% 0.20/0.50    inference(avatar_component_clause,[],[f439])).
% 0.20/0.50  fof(f439,plain,(
% 0.20/0.50    spl5_32 <=> v1_pre_topc(sK4(sK0,sK2(sK0,u1_struct_0(sK1))))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).
% 0.20/0.50  fof(f442,plain,(
% 0.20/0.50    ~spl5_31 | ~spl5_32 | spl5_15 | ~spl5_21 | ~spl5_22),
% 0.20/0.50    inference(avatar_split_clause,[],[f428,f296,f292,f236,f439,f435])).
% 0.20/0.50  fof(f236,plain,(
% 0.20/0.50    spl5_15 <=> v2_struct_0(sK4(sK0,sK2(sK0,u1_struct_0(sK1))))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.20/0.50  fof(f428,plain,(
% 0.20/0.50    ~v1_pre_topc(sK4(sK0,sK2(sK0,u1_struct_0(sK1)))) | ~m1_pre_topc(sK1,sK4(sK0,sK2(sK0,u1_struct_0(sK1)))) | (spl5_15 | ~spl5_21 | ~spl5_22)),
% 0.20/0.50    inference(subsumption_resolution,[],[f427,f238])).
% 0.20/0.50  fof(f238,plain,(
% 0.20/0.50    ~v2_struct_0(sK4(sK0,sK2(sK0,u1_struct_0(sK1)))) | spl5_15),
% 0.20/0.50    inference(avatar_component_clause,[],[f236])).
% 0.20/0.50  fof(f427,plain,(
% 0.20/0.50    ~v1_pre_topc(sK4(sK0,sK2(sK0,u1_struct_0(sK1)))) | ~m1_pre_topc(sK1,sK4(sK0,sK2(sK0,u1_struct_0(sK1)))) | v2_struct_0(sK4(sK0,sK2(sK0,u1_struct_0(sK1)))) | (~spl5_21 | ~spl5_22)),
% 0.20/0.50    inference(subsumption_resolution,[],[f422,f297])).
% 0.20/0.50  fof(f422,plain,(
% 0.20/0.50    ~v1_pre_topc(sK4(sK0,sK2(sK0,u1_struct_0(sK1)))) | ~m1_pre_topc(sK4(sK0,sK2(sK0,u1_struct_0(sK1))),sK0) | ~m1_pre_topc(sK1,sK4(sK0,sK2(sK0,u1_struct_0(sK1)))) | v2_struct_0(sK4(sK0,sK2(sK0,u1_struct_0(sK1)))) | ~spl5_21),
% 0.20/0.50    inference(resolution,[],[f293,f25])).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    ( ! [X2] : (~v4_tex_2(X2,sK0) | ~v1_pre_topc(X2) | ~m1_pre_topc(X2,sK0) | ~m1_pre_topc(sK1,X2) | v2_struct_0(X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f11])).
% 0.20/0.50  fof(f11,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (! [X2] : (~v4_tex_2(X2,X0) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2)) & m1_pre_topc(X1,X0) & v1_tdlat_3(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f10])).
% 0.20/0.50  fof(f10,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (! [X2] : (~v4_tex_2(X2,X0) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2)) & (m1_pre_topc(X1,X0) & v1_tdlat_3(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f9])).
% 0.20/0.50  fof(f9,negated_conjecture,(
% 0.20/0.50    ~! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v1_tdlat_3(X1) & ~v2_struct_0(X1)) => ? [X2] : (v4_tex_2(X2,X0) & m1_pre_topc(X1,X2) & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2))))),
% 0.20/0.50    inference(negated_conjecture,[],[f8])).
% 0.20/0.50  fof(f8,conjecture,(
% 0.20/0.50    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v1_tdlat_3(X1) & ~v2_struct_0(X1)) => ? [X2] : (v4_tex_2(X2,X0) & m1_pre_topc(X1,X2) & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_tex_2)).
% 0.20/0.50  fof(f293,plain,(
% 0.20/0.50    v4_tex_2(sK4(sK0,sK2(sK0,u1_struct_0(sK1))),sK0) | ~spl5_21),
% 0.20/0.50    inference(avatar_component_clause,[],[f292])).
% 0.20/0.50  fof(f419,plain,(
% 0.20/0.50    spl5_30 | spl5_3 | ~spl5_6 | ~spl5_16 | spl5_21 | ~spl5_22),
% 0.20/0.50    inference(avatar_split_clause,[],[f411,f296,f292,f251,f79,f64,f416])).
% 0.20/0.50  fof(f411,plain,(
% 0.20/0.50    sK2(sK0,u1_struct_0(sK1)) = sK3(sK0,sK4(sK0,sK2(sK0,u1_struct_0(sK1)))) | (spl5_3 | ~spl5_6 | ~spl5_16 | spl5_21 | ~spl5_22)),
% 0.20/0.50    inference(subsumption_resolution,[],[f309,f297])).
% 0.20/0.50  fof(f309,plain,(
% 0.20/0.50    sK2(sK0,u1_struct_0(sK1)) = sK3(sK0,sK4(sK0,sK2(sK0,u1_struct_0(sK1)))) | ~m1_pre_topc(sK4(sK0,sK2(sK0,u1_struct_0(sK1))),sK0) | (spl5_3 | ~spl5_6 | ~spl5_16 | spl5_21)),
% 0.20/0.50    inference(forward_demodulation,[],[f308,f253])).
% 0.20/0.50  fof(f308,plain,(
% 0.20/0.50    u1_struct_0(sK4(sK0,sK2(sK0,u1_struct_0(sK1)))) = sK3(sK0,sK4(sK0,sK2(sK0,u1_struct_0(sK1)))) | ~m1_pre_topc(sK4(sK0,sK2(sK0,u1_struct_0(sK1))),sK0) | (spl5_3 | ~spl5_6 | spl5_21)),
% 0.20/0.50    inference(resolution,[],[f294,f126])).
% 0.20/0.50  fof(f126,plain,(
% 0.20/0.50    ( ! [X0] : (v4_tex_2(X0,sK0) | u1_struct_0(X0) = sK3(sK0,X0) | ~m1_pre_topc(X0,sK0)) ) | (spl5_3 | ~spl5_6)),
% 0.20/0.50    inference(subsumption_resolution,[],[f97,f81])).
% 0.20/0.50  fof(f97,plain,(
% 0.20/0.50    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_pre_topc(X0,sK0) | u1_struct_0(X0) = sK3(sK0,X0) | v4_tex_2(X0,sK0)) ) | spl5_3),
% 0.20/0.50    inference(resolution,[],[f66,f40])).
% 0.20/0.50  fof(f40,plain,(
% 0.20/0.50    ( ! [X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | u1_struct_0(X1) = sK3(X0,X1) | v4_tex_2(X1,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f18])).
% 0.20/0.50  % (6951)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  fof(f382,plain,(
% 0.20/0.50    spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_24 | ~spl5_25 | spl5_27),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f381])).
% 0.20/0.50  fof(f381,plain,(
% 0.20/0.50    $false | (spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_24 | ~spl5_25 | spl5_27)),
% 0.20/0.50    inference(subsumption_resolution,[],[f380,f66])).
% 0.20/0.50  fof(f380,plain,(
% 0.20/0.50    v2_struct_0(sK0) | (~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_24 | ~spl5_25 | spl5_27)),
% 0.20/0.50    inference(subsumption_resolution,[],[f379,f320])).
% 0.20/0.50  fof(f379,plain,(
% 0.20/0.50    ~v2_tex_2(u1_struct_0(sK1),sK0) | v2_struct_0(sK0) | (~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_24 | spl5_27)),
% 0.20/0.50    inference(subsumption_resolution,[],[f378,f316])).
% 0.20/0.50  fof(f378,plain,(
% 0.20/0.50    ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(u1_struct_0(sK1),sK0) | v2_struct_0(sK0) | (~spl5_4 | ~spl5_5 | ~spl5_6 | spl5_27)),
% 0.20/0.50    inference(subsumption_resolution,[],[f377,f81])).
% 0.20/0.50  fof(f377,plain,(
% 0.20/0.50    ~l1_pre_topc(sK0) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(u1_struct_0(sK1),sK0) | v2_struct_0(sK0) | (~spl5_4 | ~spl5_5 | spl5_27)),
% 0.20/0.50    inference(subsumption_resolution,[],[f376,f76])).
% 0.20/0.50  fof(f376,plain,(
% 0.20/0.50    ~v3_tdlat_3(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(u1_struct_0(sK1),sK0) | v2_struct_0(sK0) | (~spl5_4 | spl5_27)),
% 0.20/0.50    inference(subsumption_resolution,[],[f375,f71])).
% 0.20/0.50  fof(f375,plain,(
% 0.20/0.50    ~v2_pre_topc(sK0) | ~v3_tdlat_3(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(u1_struct_0(sK1),sK0) | v2_struct_0(sK0) | spl5_27),
% 0.20/0.50    inference(resolution,[],[f365,f34])).
% 0.20/0.50  fof(f34,plain,(
% 0.20/0.50    ( ! [X0,X1] : (m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~v3_tdlat_3(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | v2_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f14])).
% 0.20/0.50  fof(f365,plain,(
% 0.20/0.50    ~m1_subset_1(sK2(sK0,u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | spl5_27),
% 0.20/0.50    inference(avatar_component_clause,[],[f363])).
% 0.20/0.50  fof(f366,plain,(
% 0.20/0.50    spl5_26 | ~spl5_27 | spl5_3 | ~spl5_6 | spl5_22),
% 0.20/0.50    inference(avatar_split_clause,[],[f310,f296,f79,f64,f363,f359])).
% 0.20/0.50  fof(f310,plain,(
% 0.20/0.50    ~m1_subset_1(sK2(sK0,u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(sK2(sK0,u1_struct_0(sK1))) | (spl5_3 | ~spl5_6 | spl5_22)),
% 0.20/0.50    inference(resolution,[],[f298,f129])).
% 0.20/0.50  fof(f129,plain,(
% 0.20/0.50    ( ! [X3] : (m1_pre_topc(sK4(sK0,X3),sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X3)) ) | (spl5_3 | ~spl5_6)),
% 0.20/0.50    inference(subsumption_resolution,[],[f100,f81])).
% 0.20/0.50  fof(f100,plain,(
% 0.20/0.50    ( ! [X3] : (~l1_pre_topc(sK0) | v1_xboole_0(X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | m1_pre_topc(sK4(sK0,X3),sK0)) ) | spl5_3),
% 0.20/0.50    inference(resolution,[],[f66,f44])).
% 0.20/0.50  fof(f44,plain,(
% 0.20/0.50    ( ! [X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_pre_topc(sK4(X0,X1),X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f20])).
% 0.20/0.50  fof(f298,plain,(
% 0.20/0.50    ~m1_pre_topc(sK4(sK0,sK2(sK0,u1_struct_0(sK1))),sK0) | spl5_22),
% 0.20/0.50    inference(avatar_component_clause,[],[f296])).
% 0.20/0.50  fof(f345,plain,(
% 0.20/0.50    ~spl5_6 | ~spl5_7 | spl5_24),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f344])).
% 0.20/0.50  fof(f344,plain,(
% 0.20/0.50    $false | (~spl5_6 | ~spl5_7 | spl5_24)),
% 0.20/0.50    inference(subsumption_resolution,[],[f343,f81])).
% 0.20/0.50  fof(f343,plain,(
% 0.20/0.50    ~l1_pre_topc(sK0) | (~spl5_7 | spl5_24)),
% 0.20/0.50    inference(subsumption_resolution,[],[f342,f86])).
% 0.20/0.50  fof(f342,plain,(
% 0.20/0.50    ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | spl5_24),
% 0.20/0.50    inference(resolution,[],[f317,f33])).
% 0.20/0.50  fof(f33,plain,(
% 0.20/0.50    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f12])).
% 0.20/0.50  fof(f12,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.20/0.50  fof(f317,plain,(
% 0.20/0.50    ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl5_24),
% 0.20/0.50    inference(avatar_component_clause,[],[f315])).
% 0.20/0.50  fof(f335,plain,(
% 0.20/0.50    spl5_1 | ~spl5_2 | spl5_3 | ~spl5_6 | ~spl5_7 | spl5_25),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f334])).
% 0.20/0.50  fof(f334,plain,(
% 0.20/0.50    $false | (spl5_1 | ~spl5_2 | spl5_3 | ~spl5_6 | ~spl5_7 | spl5_25)),
% 0.20/0.50    inference(subsumption_resolution,[],[f333,f56])).
% 0.20/0.50  fof(f56,plain,(
% 0.20/0.50    ~v2_struct_0(sK1) | spl5_1),
% 0.20/0.50    inference(avatar_component_clause,[],[f54])).
% 0.20/0.50  fof(f54,plain,(
% 0.20/0.50    spl5_1 <=> v2_struct_0(sK1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.50  fof(f333,plain,(
% 0.20/0.50    v2_struct_0(sK1) | (~spl5_2 | spl5_3 | ~spl5_6 | ~spl5_7 | spl5_25)),
% 0.20/0.50    inference(subsumption_resolution,[],[f332,f61])).
% 0.20/0.50  fof(f61,plain,(
% 0.20/0.50    v1_tdlat_3(sK1) | ~spl5_2),
% 0.20/0.50    inference(avatar_component_clause,[],[f59])).
% 0.20/0.50  fof(f59,plain,(
% 0.20/0.50    spl5_2 <=> v1_tdlat_3(sK1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.20/0.50  fof(f332,plain,(
% 0.20/0.50    ~v1_tdlat_3(sK1) | v2_struct_0(sK1) | (spl5_3 | ~spl5_6 | ~spl5_7 | spl5_25)),
% 0.20/0.50    inference(subsumption_resolution,[],[f331,f86])).
% 0.20/0.50  fof(f331,plain,(
% 0.20/0.50    ~m1_pre_topc(sK1,sK0) | ~v1_tdlat_3(sK1) | v2_struct_0(sK1) | (spl5_3 | ~spl5_6 | spl5_25)),
% 0.20/0.50    inference(resolution,[],[f321,f125])).
% 0.20/0.50  fof(f125,plain,(
% 0.20/0.50    ( ! [X6] : (v2_tex_2(u1_struct_0(X6),sK0) | ~m1_pre_topc(X6,sK0) | ~v1_tdlat_3(X6) | v2_struct_0(X6)) ) | (spl5_3 | ~spl5_6)),
% 0.20/0.50    inference(subsumption_resolution,[],[f105,f81])).
% 0.20/0.50  fof(f105,plain,(
% 0.20/0.50    ( ! [X6] : (~l1_pre_topc(sK0) | v2_struct_0(X6) | ~m1_pre_topc(X6,sK0) | ~v1_tdlat_3(X6) | v2_tex_2(u1_struct_0(X6),sK0)) ) | spl5_3),
% 0.20/0.50    inference(subsumption_resolution,[],[f103,f33])).
% 0.20/0.50  fof(f103,plain,(
% 0.20/0.50    ( ! [X6] : (~l1_pre_topc(sK0) | v2_struct_0(X6) | ~m1_pre_topc(X6,sK0) | ~m1_subset_1(u1_struct_0(X6),k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_tdlat_3(X6) | v2_tex_2(u1_struct_0(X6),sK0)) ) | spl5_3),
% 0.20/0.50    inference(resolution,[],[f66,f52])).
% 0.20/0.50  fof(f52,plain,(
% 0.20/0.50    ( ! [X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tdlat_3(X1) | v2_tex_2(u1_struct_0(X1),X0)) )),
% 0.20/0.50    inference(equality_resolution,[],[f46])).
% 0.20/0.50  fof(f46,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X1) != X2 | ~v1_tdlat_3(X1) | v2_tex_2(X2,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f22])).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : ((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f21])).
% 0.20/0.50  fof(f21,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : (((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f5])).
% 0.20/0.50  fof(f5,axiom,(
% 0.20/0.50    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => (v2_tex_2(X2,X0) <=> v1_tdlat_3(X1))))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_tex_2)).
% 0.20/0.50  fof(f321,plain,(
% 0.20/0.50    ~v2_tex_2(u1_struct_0(sK1),sK0) | spl5_25),
% 0.20/0.50    inference(avatar_component_clause,[],[f319])).
% 0.20/0.50  fof(f322,plain,(
% 0.20/0.50    ~spl5_24 | ~spl5_25 | spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | spl5_23),
% 0.20/0.50    inference(avatar_split_clause,[],[f304,f300,f79,f74,f69,f64,f319,f315])).
% 0.20/0.50  fof(f304,plain,(
% 0.20/0.50    ~v2_tex_2(u1_struct_0(sK1),sK0) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | spl5_23)),
% 0.20/0.50    inference(resolution,[],[f301,f135])).
% 0.20/0.50  fof(f135,plain,(
% 0.20/0.50    ( ! [X1] : (v3_tex_2(sK2(sK0,X1),sK0) | ~v2_tex_2(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6)),
% 0.20/0.50    inference(subsumption_resolution,[],[f112,f81])).
% 0.20/0.50  fof(f112,plain,(
% 0.20/0.50    ( ! [X1] : (~l1_pre_topc(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X1,sK0) | v3_tex_2(sK2(sK0,X1),sK0)) ) | (spl5_3 | ~spl5_4 | ~spl5_5)),
% 0.20/0.50    inference(subsumption_resolution,[],[f111,f66])).
% 0.20/0.50  fof(f111,plain,(
% 0.20/0.50    ( ! [X1] : (v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X1,sK0) | v3_tex_2(sK2(sK0,X1),sK0)) ) | (~spl5_4 | ~spl5_5)),
% 0.20/0.50    inference(subsumption_resolution,[],[f108,f71])).
% 0.20/0.50  fof(f108,plain,(
% 0.20/0.50    ( ! [X1] : (~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X1,sK0) | v3_tex_2(sK2(sK0,X1),sK0)) ) | ~spl5_5),
% 0.20/0.50    inference(resolution,[],[f76,f36])).
% 0.20/0.50  fof(f36,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | v3_tex_2(sK2(X0,X1),X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f14])).
% 0.20/0.50  fof(f301,plain,(
% 0.20/0.50    ~v3_tex_2(sK2(sK0,u1_struct_0(sK1)),sK0) | spl5_23),
% 0.20/0.50    inference(avatar_component_clause,[],[f300])).
% 0.20/0.50  fof(f254,plain,(
% 0.20/0.50    spl5_16 | spl5_1 | ~spl5_2 | spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_7),
% 0.20/0.50    inference(avatar_split_clause,[],[f232,f84,f79,f74,f69,f64,f59,f54,f251])).
% 0.20/0.50  fof(f232,plain,(
% 0.20/0.50    sK2(sK0,u1_struct_0(sK1)) = u1_struct_0(sK4(sK0,sK2(sK0,u1_struct_0(sK1)))) | (spl5_1 | ~spl5_2 | spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_7)),
% 0.20/0.50    inference(subsumption_resolution,[],[f231,f56])).
% 0.20/0.50  fof(f231,plain,(
% 0.20/0.50    sK2(sK0,u1_struct_0(sK1)) = u1_struct_0(sK4(sK0,sK2(sK0,u1_struct_0(sK1)))) | v2_struct_0(sK1) | (~spl5_2 | spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_7)),
% 0.20/0.50    inference(subsumption_resolution,[],[f228,f86])).
% 0.20/0.50  fof(f228,plain,(
% 0.20/0.50    ~m1_pre_topc(sK1,sK0) | sK2(sK0,u1_struct_0(sK1)) = u1_struct_0(sK4(sK0,sK2(sK0,u1_struct_0(sK1)))) | v2_struct_0(sK1) | (~spl5_2 | spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6)),
% 0.20/0.50    inference(resolution,[],[f201,f61])).
% 0.20/0.50  fof(f201,plain,(
% 0.20/0.50    ( ! [X0] : (~v1_tdlat_3(X0) | ~m1_pre_topc(X0,sK0) | sK2(sK0,u1_struct_0(X0)) = u1_struct_0(sK4(sK0,sK2(sK0,u1_struct_0(X0)))) | v2_struct_0(X0)) ) | (spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6)),
% 0.20/0.50    inference(subsumption_resolution,[],[f200,f81])).
% 0.20/0.50  fof(f200,plain,(
% 0.20/0.50    ( ! [X0] : (sK2(sK0,u1_struct_0(X0)) = u1_struct_0(sK4(sK0,sK2(sK0,u1_struct_0(X0)))) | ~m1_pre_topc(X0,sK0) | ~v1_tdlat_3(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0)) ) | (spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6)),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f199])).
% 0.20/0.50  fof(f199,plain,(
% 0.20/0.50    ( ! [X0] : (sK2(sK0,u1_struct_0(X0)) = u1_struct_0(sK4(sK0,sK2(sK0,u1_struct_0(X0)))) | ~m1_pre_topc(X0,sK0) | ~v1_tdlat_3(X0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | ~l1_pre_topc(sK0)) ) | (spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6)),
% 0.20/0.50    inference(resolution,[],[f184,f33])).
% 0.20/0.50  fof(f184,plain,(
% 0.20/0.50    ( ! [X0] : (~m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK0))) | sK2(sK0,u1_struct_0(X0)) = u1_struct_0(sK4(sK0,sK2(sK0,u1_struct_0(X0)))) | ~m1_pre_topc(X0,sK0) | ~v1_tdlat_3(X0) | v2_struct_0(X0)) ) | (spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6)),
% 0.20/0.50    inference(resolution,[],[f171,f125])).
% 0.20/0.50  fof(f171,plain,(
% 0.20/0.50    ( ! [X0] : (~v2_tex_2(X0,sK0) | sK2(sK0,X0) = u1_struct_0(sK4(sK0,sK2(sK0,X0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6)),
% 0.20/0.50    inference(subsumption_resolution,[],[f170,f66])).
% 0.20/0.50  fof(f170,plain,(
% 0.20/0.50    ( ! [X0] : (sK2(sK0,X0) = u1_struct_0(sK4(sK0,sK2(sK0,X0))) | ~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)) ) | (spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6)),
% 0.20/0.50    inference(subsumption_resolution,[],[f169,f81])).
% 0.20/0.50  fof(f169,plain,(
% 0.20/0.50    ( ! [X0] : (sK2(sK0,X0) = u1_struct_0(sK4(sK0,sK2(sK0,X0))) | ~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)) ) | (spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6)),
% 0.20/0.50    inference(subsumption_resolution,[],[f168,f76])).
% 0.20/0.50  fof(f168,plain,(
% 0.20/0.50    ( ! [X0] : (sK2(sK0,X0) = u1_struct_0(sK4(sK0,sK2(sK0,X0))) | ~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_tdlat_3(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)) ) | (spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6)),
% 0.20/0.50    inference(subsumption_resolution,[],[f167,f71])).
% 0.20/0.50  fof(f167,plain,(
% 0.20/0.50    ( ! [X0] : (sK2(sK0,X0) = u1_struct_0(sK4(sK0,sK2(sK0,X0))) | ~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | ~v3_tdlat_3(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)) ) | (spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6)),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f166])).
% 0.20/0.50  fof(f166,plain,(
% 0.20/0.50    ( ! [X0] : (sK2(sK0,X0) = u1_struct_0(sK4(sK0,sK2(sK0,X0))) | ~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | ~v3_tdlat_3(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X0,sK0) | v2_struct_0(sK0)) ) | (spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6)),
% 0.20/0.50    inference(resolution,[],[f149,f34])).
% 0.20/0.50  fof(f149,plain,(
% 0.20/0.50    ( ! [X1] : (~m1_subset_1(sK2(sK0,X1),k1_zfmisc_1(u1_struct_0(sK0))) | sK2(sK0,X1) = u1_struct_0(sK4(sK0,sK2(sK0,X1))) | ~v2_tex_2(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6)),
% 0.20/0.50    inference(resolution,[],[f145,f135])).
% 0.20/0.50  fof(f145,plain,(
% 0.20/0.50    ( ! [X0] : (~v3_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK4(sK0,X0)) = X0) ) | (spl5_3 | ~spl5_4 | ~spl5_6)),
% 0.20/0.50    inference(subsumption_resolution,[],[f144,f66])).
% 0.20/0.50  fof(f144,plain,(
% 0.20/0.50    ( ! [X0] : (u1_struct_0(sK4(sK0,X0)) = X0 | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | ~v3_tex_2(X0,sK0)) ) | (spl5_3 | ~spl5_4 | ~spl5_6)),
% 0.20/0.50    inference(subsumption_resolution,[],[f143,f81])).
% 0.20/0.50  fof(f143,plain,(
% 0.20/0.50    ( ! [X0] : (u1_struct_0(sK4(sK0,X0)) = X0 | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~v3_tex_2(X0,sK0)) ) | (spl5_3 | ~spl5_4 | ~spl5_6)),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f142])).
% 0.20/0.50  fof(f142,plain,(
% 0.20/0.50    ( ! [X0] : (u1_struct_0(sK4(sK0,X0)) = X0 | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_tex_2(X0,sK0)) ) | (spl5_3 | ~spl5_4 | ~spl5_6)),
% 0.20/0.50    inference(resolution,[],[f131,f71])).
% 0.20/0.50  % (6957)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.50  fof(f131,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v2_pre_topc(X1) | u1_struct_0(sK4(sK0,X0)) = X0 | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(X1) | v2_struct_0(X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_tex_2(X0,X1)) ) | (spl5_3 | ~spl5_6)),
% 0.20/0.50    inference(resolution,[],[f130,f37])).
% 0.20/0.50  fof(f130,plain,(
% 0.20/0.50    ( ! [X4] : (v1_xboole_0(X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK4(sK0,X4)) = X4) ) | (spl5_3 | ~spl5_6)),
% 0.20/0.50    inference(subsumption_resolution,[],[f101,f81])).
% 0.20/0.50  fof(f101,plain,(
% 0.20/0.50    ( ! [X4] : (~l1_pre_topc(sK0) | v1_xboole_0(X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK4(sK0,X4)) = X4) ) | spl5_3),
% 0.20/0.50    inference(resolution,[],[f66,f45])).
% 0.20/0.50  fof(f45,plain,(
% 0.20/0.50    ( ! [X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(sK4(X0,X1)) = X1) )),
% 0.20/0.50    inference(cnf_transformation,[],[f20])).
% 0.20/0.50  fof(f239,plain,(
% 0.20/0.50    ~spl5_15 | spl5_1 | ~spl5_2 | spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_7),
% 0.20/0.50    inference(avatar_split_clause,[],[f226,f84,f79,f74,f69,f64,f59,f54,f236])).
% 0.20/0.50  fof(f226,plain,(
% 0.20/0.50    ~v2_struct_0(sK4(sK0,sK2(sK0,u1_struct_0(sK1)))) | (spl5_1 | ~spl5_2 | spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_7)),
% 0.20/0.50    inference(subsumption_resolution,[],[f225,f56])).
% 0.20/0.50  fof(f225,plain,(
% 0.20/0.50    ~v2_struct_0(sK4(sK0,sK2(sK0,u1_struct_0(sK1)))) | v2_struct_0(sK1) | (~spl5_2 | spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_7)),
% 0.20/0.50    inference(subsumption_resolution,[],[f222,f86])).
% 0.20/0.50  fof(f222,plain,(
% 0.20/0.50    ~m1_pre_topc(sK1,sK0) | ~v2_struct_0(sK4(sK0,sK2(sK0,u1_struct_0(sK1)))) | v2_struct_0(sK1) | (~spl5_2 | spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6)),
% 0.20/0.50    inference(resolution,[],[f198,f61])).
% 0.20/0.50  fof(f198,plain,(
% 0.20/0.50    ( ! [X0] : (~v1_tdlat_3(X0) | ~m1_pre_topc(X0,sK0) | ~v2_struct_0(sK4(sK0,sK2(sK0,u1_struct_0(X0)))) | v2_struct_0(X0)) ) | (spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6)),
% 0.20/0.50    inference(subsumption_resolution,[],[f197,f81])).
% 0.20/0.50  fof(f197,plain,(
% 0.20/0.50    ( ! [X0] : (~v2_struct_0(sK4(sK0,sK2(sK0,u1_struct_0(X0)))) | ~m1_pre_topc(X0,sK0) | ~v1_tdlat_3(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK0)) ) | (spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6)),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f196])).
% 0.20/0.50  fof(f196,plain,(
% 0.20/0.50    ( ! [X0] : (~v2_struct_0(sK4(sK0,sK2(sK0,u1_struct_0(X0)))) | ~m1_pre_topc(X0,sK0) | ~v1_tdlat_3(X0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | ~l1_pre_topc(sK0)) ) | (spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6)),
% 0.20/0.50    inference(resolution,[],[f174,f33])).
% 0.20/0.50  fof(f174,plain,(
% 0.20/0.50    ( ! [X0] : (~m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_struct_0(sK4(sK0,sK2(sK0,u1_struct_0(X0)))) | ~m1_pre_topc(X0,sK0) | ~v1_tdlat_3(X0) | v2_struct_0(X0)) ) | (spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6)),
% 0.20/0.50    inference(resolution,[],[f165,f125])).
% 0.20/0.50  fof(f165,plain,(
% 0.20/0.50    ( ! [X0] : (~v2_tex_2(X0,sK0) | ~v2_struct_0(sK4(sK0,sK2(sK0,X0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6)),
% 0.20/0.50    inference(subsumption_resolution,[],[f164,f66])).
% 0.20/0.50  fof(f164,plain,(
% 0.20/0.50    ( ! [X0] : (~v2_struct_0(sK4(sK0,sK2(sK0,X0))) | ~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)) ) | (spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6)),
% 0.20/0.50    inference(subsumption_resolution,[],[f163,f81])).
% 0.20/0.50  fof(f163,plain,(
% 0.20/0.50    ( ! [X0] : (~v2_struct_0(sK4(sK0,sK2(sK0,X0))) | ~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)) ) | (spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6)),
% 0.20/0.50    inference(subsumption_resolution,[],[f162,f76])).
% 0.20/0.50  fof(f162,plain,(
% 0.20/0.50    ( ! [X0] : (~v2_struct_0(sK4(sK0,sK2(sK0,X0))) | ~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_tdlat_3(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)) ) | (spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6)),
% 0.20/0.50    inference(subsumption_resolution,[],[f161,f71])).
% 0.20/0.50  fof(f161,plain,(
% 0.20/0.50    ( ! [X0] : (~v2_struct_0(sK4(sK0,sK2(sK0,X0))) | ~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | ~v3_tdlat_3(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)) ) | (spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6)),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f160])).
% 0.20/0.50  fof(f160,plain,(
% 0.20/0.50    ( ! [X0] : (~v2_struct_0(sK4(sK0,sK2(sK0,X0))) | ~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | ~v3_tdlat_3(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X0,sK0) | v2_struct_0(sK0)) ) | (spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6)),
% 0.20/0.50    inference(resolution,[],[f147,f34])).
% 0.20/0.50  fof(f147,plain,(
% 0.20/0.50    ( ! [X1] : (~m1_subset_1(sK2(sK0,X1),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_struct_0(sK4(sK0,sK2(sK0,X1))) | ~v2_tex_2(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6)),
% 0.20/0.50    inference(resolution,[],[f141,f135])).
% 0.20/0.50  fof(f141,plain,(
% 0.20/0.50    ( ! [X0] : (~v3_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_struct_0(sK4(sK0,X0))) ) | (spl5_3 | ~spl5_4 | ~spl5_6)),
% 0.20/0.50    inference(subsumption_resolution,[],[f140,f66])).
% 0.20/0.50  fof(f140,plain,(
% 0.20/0.50    ( ! [X0] : (~v2_struct_0(sK4(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | ~v3_tex_2(X0,sK0)) ) | (spl5_3 | ~spl5_4 | ~spl5_6)),
% 0.20/0.50    inference(subsumption_resolution,[],[f139,f81])).
% 0.20/0.50  fof(f139,plain,(
% 0.20/0.50    ( ! [X0] : (~v2_struct_0(sK4(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~v3_tex_2(X0,sK0)) ) | (spl5_3 | ~spl5_4 | ~spl5_6)),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f138])).
% 0.20/0.50  fof(f138,plain,(
% 0.20/0.50    ( ! [X0] : (~v2_struct_0(sK4(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_tex_2(X0,sK0)) ) | (spl5_3 | ~spl5_4 | ~spl5_6)),
% 0.20/0.50    inference(resolution,[],[f124,f71])).
% 0.20/0.50  fof(f124,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v2_pre_topc(X1) | ~v2_struct_0(sK4(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(X1) | v2_struct_0(X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_tex_2(X0,X1)) ) | (spl5_3 | ~spl5_6)),
% 0.20/0.50    inference(resolution,[],[f123,f37])).
% 0.20/0.50  fof(f123,plain,(
% 0.20/0.50    ( ! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_struct_0(sK4(sK0,X2))) ) | (spl5_3 | ~spl5_6)),
% 0.20/0.50    inference(subsumption_resolution,[],[f99,f81])).
% 0.20/0.50  fof(f99,plain,(
% 0.20/0.50    ( ! [X2] : (~l1_pre_topc(sK0) | v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_struct_0(sK4(sK0,X2))) ) | spl5_3),
% 0.20/0.50    inference(resolution,[],[f66,f42])).
% 0.20/0.50  fof(f42,plain,(
% 0.20/0.50    ( ! [X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_struct_0(sK4(X0,X1))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f20])).
% 0.20/0.50  fof(f87,plain,(
% 0.20/0.50    spl5_7),
% 0.20/0.50    inference(avatar_split_clause,[],[f28,f84])).
% 0.20/0.50  fof(f28,plain,(
% 0.20/0.50    m1_pre_topc(sK1,sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f11])).
% 0.20/0.50  fof(f82,plain,(
% 0.20/0.50    spl5_6),
% 0.20/0.50    inference(avatar_split_clause,[],[f32,f79])).
% 0.20/0.50  fof(f32,plain,(
% 0.20/0.50    l1_pre_topc(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f11])).
% 0.20/0.50  fof(f77,plain,(
% 0.20/0.50    spl5_5),
% 0.20/0.50    inference(avatar_split_clause,[],[f31,f74])).
% 0.20/0.50  fof(f31,plain,(
% 0.20/0.50    v3_tdlat_3(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f11])).
% 0.20/0.50  fof(f72,plain,(
% 0.20/0.50    spl5_4),
% 0.20/0.50    inference(avatar_split_clause,[],[f30,f69])).
% 0.20/0.50  fof(f30,plain,(
% 0.20/0.50    v2_pre_topc(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f11])).
% 0.20/0.50  fof(f67,plain,(
% 0.20/0.50    ~spl5_3),
% 0.20/0.50    inference(avatar_split_clause,[],[f29,f64])).
% 0.20/0.50  fof(f29,plain,(
% 0.20/0.50    ~v2_struct_0(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f11])).
% 0.20/0.50  fof(f62,plain,(
% 0.20/0.50    spl5_2),
% 0.20/0.50    inference(avatar_split_clause,[],[f27,f59])).
% 0.20/0.50  fof(f27,plain,(
% 0.20/0.50    v1_tdlat_3(sK1)),
% 0.20/0.50    inference(cnf_transformation,[],[f11])).
% 0.20/0.50  fof(f57,plain,(
% 0.20/0.50    ~spl5_1),
% 0.20/0.50    inference(avatar_split_clause,[],[f26,f54])).
% 0.20/0.50  fof(f26,plain,(
% 0.20/0.50    ~v2_struct_0(sK1)),
% 0.20/0.50    inference(cnf_transformation,[],[f11])).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (6942)------------------------------
% 0.20/0.50  % (6942)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (6942)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (6942)Memory used [KB]: 10874
% 0.20/0.50  % (6942)Time elapsed: 0.087 s
% 0.20/0.50  % (6942)------------------------------
% 0.20/0.50  % (6942)------------------------------
% 0.20/0.50  % (6956)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.50  % (6948)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.50  % (6935)Success in time 0.149 s
%------------------------------------------------------------------------------
