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
% DateTime   : Thu Dec  3 13:19:32 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  194 ( 450 expanded)
%              Number of leaves         :   32 ( 170 expanded)
%              Depth                    :   15
%              Number of atoms          :  857 (1746 expanded)
%              Number of equality atoms :  105 ( 191 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f428,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f70,f74,f78,f82,f88,f115,f122,f127,f131,f139,f153,f157,f161,f299,f303,f384,f397,f405,f406,f426,f427])).

fof(f427,plain,
    ( u1_pre_topc(sK0) != u1_pre_topc(k8_tmap_1(sK0,sK1))
    | u1_pre_topc(sK0) != k5_tmap_1(sK0,sK3(sK0))
    | k8_tmap_1(sK0,sK1) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(k8_tmap_1(sK0,sK1)))
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f426,plain,
    ( spl4_1
    | spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_14
    | spl4_24 ),
    inference(avatar_contradiction_clause,[],[f425])).

fof(f425,plain,
    ( $false
    | spl4_1
    | spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_14
    | spl4_24 ),
    inference(subsumption_resolution,[],[f424,f423])).

fof(f423,plain,
    ( r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f234,f419])).

fof(f419,plain,
    ( v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f411,f118])).

fof(f118,plain,
    ( v1_tsep_1(sK1,sK0)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl4_7
  <=> v1_tsep_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f411,plain,
    ( v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ v1_tsep_1(sK1,sK0)
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f410,f81])).

fof(f81,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl4_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f410,plain,
    ( ~ l1_pre_topc(sK0)
    | v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ v1_tsep_1(sK1,sK0)
    | ~ spl4_5
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f195,f87])).

fof(f87,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl4_5
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f195,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ v1_tsep_1(sK1,sK0)
    | ~ spl4_14 ),
    inference(resolution,[],[f156,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v3_pre_topc(u1_struct_0(X1),X0)
      | ~ v1_tsep_1(X1,X0) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X1) != X2
      | v3_pre_topc(X2,X0)
      | ~ v1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tsep_1(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tsep_1(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tsep_1(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tsep_1)).

fof(f156,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f155])).

fof(f155,plain,
    ( spl4_14
  <=> m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f234,plain,
    ( r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | ~ v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ spl4_4
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f204,f81])).

fof(f204,plain,
    ( ~ l1_pre_topc(sK0)
    | r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | ~ v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ spl4_14 ),
    inference(resolution,[],[f156,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | r2_hidden(X1,u1_pre_topc(X0))
      | ~ v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

fof(f424,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | spl4_1
    | spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_14
    | spl4_24 ),
    inference(subsumption_resolution,[],[f222,f302])).

fof(f302,plain,
    ( u1_pre_topc(sK0) != u1_pre_topc(k8_tmap_1(sK0,sK1))
    | spl4_24 ),
    inference(avatar_component_clause,[],[f301])).

fof(f301,plain,
    ( spl4_24
  <=> u1_pre_topc(sK0) = u1_pre_topc(k8_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f222,plain,
    ( u1_pre_topc(sK0) = u1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | spl4_1
    | spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_14 ),
    inference(forward_demodulation,[],[f221,f209])).

fof(f209,plain,
    ( u1_pre_topc(k8_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,u1_struct_0(sK1))
    | spl4_1
    | spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f208,f73])).

fof(f73,plain,
    ( ~ v2_struct_0(sK0)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl4_2
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f208,plain,
    ( v2_struct_0(sK0)
    | u1_pre_topc(k8_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,u1_struct_0(sK1))
    | spl4_1
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f207,f87])).

fof(f207,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | u1_pre_topc(k8_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,u1_struct_0(sK1))
    | spl4_1
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f206,f69])).

fof(f69,plain,
    ( ~ v2_struct_0(sK1)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl4_1
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f206,plain,
    ( v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | u1_pre_topc(k8_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,u1_struct_0(sK1))
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f205,f81])).

fof(f205,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | u1_pre_topc(k8_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,u1_struct_0(sK1))
    | ~ spl4_3
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f196,f77])).

fof(f77,plain,
    ( v2_pre_topc(sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl4_3
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f196,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | u1_pre_topc(k8_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,u1_struct_0(sK1))
    | ~ spl4_14 ),
    inference(resolution,[],[f156,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X0)
      | u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,u1_struct_0(X1)) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X1) != X2
      | u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ! [X2] :
                ( u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ! [X2] :
                ( u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ( ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2) ) )
            & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t114_tmap_1)).

fof(f221,plain,
    ( u1_pre_topc(sK0) = k5_tmap_1(sK0,u1_struct_0(sK1))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f220,f73])).

fof(f220,plain,
    ( v2_struct_0(sK0)
    | u1_pre_topc(sK0) = k5_tmap_1(sK0,u1_struct_0(sK1))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f219,f81])).

fof(f219,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | u1_pre_topc(sK0) = k5_tmap_1(sK0,u1_struct_0(sK1))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | ~ spl4_3
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f199,f77])).

fof(f199,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | u1_pre_topc(sK0) = k5_tmap_1(sK0,u1_struct_0(sK1))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | ~ spl4_14 ),
    inference(resolution,[],[f156,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | u1_pre_topc(X0) = k5_tmap_1(X0,X1)
      | ~ r2_hidden(X1,u1_pre_topc(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
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
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_tmap_1)).

fof(f406,plain,
    ( k6_tmap_1(sK0,sK3(sK0)) != g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK3(sK0)))
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k8_tmap_1(sK0,sK1)
    | k5_tmap_1(sK0,sK3(sK0)) != u1_pre_topc(k6_tmap_1(sK0,sK3(sK0)))
    | u1_pre_topc(sK0) != k5_tmap_1(sK0,sK3(sK0))
    | u1_pre_topc(sK0) = u1_pre_topc(k8_tmap_1(sK0,sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f405,plain,
    ( spl4_36
    | spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f172,f151,f80,f76,f72,f403])).

fof(f403,plain,
    ( spl4_36
  <=> k6_tmap_1(sK0,sK3(sK0)) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f151,plain,
    ( spl4_13
  <=> m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f172,plain,
    ( k6_tmap_1(sK0,sK3(sK0)) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK3(sK0)))
    | spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f171,f73])).

fof(f171,plain,
    ( v2_struct_0(sK0)
    | k6_tmap_1(sK0,sK3(sK0)) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK3(sK0)))
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f170,f81])).

fof(f170,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | k6_tmap_1(sK0,sK3(sK0)) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK3(sK0)))
    | ~ spl4_3
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f162,f77])).

fof(f162,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | k6_tmap_1(sK0,sK3(sK0)) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK3(sK0)))
    | ~ spl4_13 ),
    inference(resolution,[],[f152,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
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
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_tmap_1)).

fof(f152,plain,
    ( m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f151])).

fof(f397,plain,
    ( spl4_34
    | spl4_1
    | spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_9
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f142,f137,f129,f86,f80,f76,f72,f68,f395])).

fof(f395,plain,
    ( spl4_34
  <=> k8_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(k8_tmap_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f129,plain,
    ( spl4_9
  <=> v1_pre_topc(k8_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f137,plain,
    ( spl4_11
  <=> l1_pre_topc(k8_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f142,plain,
    ( k8_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(k8_tmap_1(sK0,sK1)))
    | spl4_1
    | spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_9
    | ~ spl4_11 ),
    inference(forward_demodulation,[],[f141,f108])).

fof(f108,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1))
    | spl4_1
    | spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f107,f73])).

fof(f107,plain,
    ( v2_struct_0(sK0)
    | u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1))
    | spl4_1
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f106,f69])).

fof(f106,plain,
    ( v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1))
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f105,f81])).

fof(f105,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1))
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f92,f77])).

fof(f92,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1))
    | ~ spl4_5 ),
    inference(resolution,[],[f87,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | v2_struct_0(X0)
      | u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f141,plain,
    ( k8_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(k8_tmap_1(sK0,sK1)),u1_pre_topc(k8_tmap_1(sK0,sK1)))
    | ~ spl4_9
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f140,f138])).

fof(f138,plain,
    ( l1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f137])).

fof(f140,plain,
    ( ~ l1_pre_topc(k8_tmap_1(sK0,sK1))
    | k8_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(k8_tmap_1(sK0,sK1)),u1_pre_topc(k8_tmap_1(sK0,sK1)))
    | ~ spl4_9 ),
    inference(resolution,[],[f130,f49])).

fof(f49,plain,(
    ! [X0] :
      ( ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(f130,plain,
    ( v1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f129])).

fof(f384,plain,
    ( spl4_31
    | spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f184,f151,f80,f76,f72,f382])).

fof(f382,plain,
    ( spl4_31
  <=> k5_tmap_1(sK0,sK3(sK0)) = u1_pre_topc(k6_tmap_1(sK0,sK3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f184,plain,
    ( k5_tmap_1(sK0,sK3(sK0)) = u1_pre_topc(k6_tmap_1(sK0,sK3(sK0)))
    | spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f183,f73])).

fof(f183,plain,
    ( v2_struct_0(sK0)
    | k5_tmap_1(sK0,sK3(sK0)) = u1_pre_topc(k6_tmap_1(sK0,sK3(sK0)))
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f182,f81])).

fof(f182,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | k5_tmap_1(sK0,sK3(sK0)) = u1_pre_topc(k6_tmap_1(sK0,sK3(sK0)))
    | ~ spl4_3
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f166,f77])).

fof(f166,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | k5_tmap_1(sK0,sK3(sK0)) = u1_pre_topc(k6_tmap_1(sK0,sK3(sK0)))
    | ~ spl4_13 ),
    inference(resolution,[],[f152,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_tmap_1)).

fof(f303,plain,
    ( ~ spl4_24
    | spl4_1
    | spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | spl4_7
    | ~ spl4_14
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f241,f159,f155,f117,f86,f80,f76,f72,f68,f301])).

fof(f159,plain,
    ( spl4_15
  <=> sK2(sK0,sK1) = u1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f241,plain,
    ( u1_pre_topc(sK0) != u1_pre_topc(k8_tmap_1(sK0,sK1))
    | spl4_1
    | spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | spl4_7
    | ~ spl4_14
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f218,f239])).

fof(f239,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | ~ spl4_4
    | ~ spl4_5
    | spl4_7
    | ~ spl4_14
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f233,f238])).

fof(f238,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ spl4_4
    | ~ spl4_5
    | spl4_7
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f237,f126])).

fof(f126,plain,
    ( ~ v1_tsep_1(sK1,sK0)
    | spl4_7 ),
    inference(avatar_component_clause,[],[f117])).

fof(f237,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK1),sK0)
    | v1_tsep_1(sK1,sK0)
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f236,f81])).

fof(f236,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | v1_tsep_1(sK1,sK0)
    | ~ spl4_5
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f235,f87])).

fof(f235,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | v1_tsep_1(sK1,sK0)
    | ~ spl4_15 ),
    inference(superposition,[],[f53,f160])).

fof(f160,plain,
    ( sK2(sK0,sK1) = u1_struct_0(sK1)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f159])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(sK2(X0,X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f233,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ spl4_4
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f203,f81])).

fof(f203,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ spl4_14 ),
    inference(resolution,[],[f156,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f218,plain,
    ( u1_pre_topc(sK0) != u1_pre_topc(k8_tmap_1(sK0,sK1))
    | r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | spl4_1
    | spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_14 ),
    inference(forward_demodulation,[],[f217,f209])).

fof(f217,plain,
    ( u1_pre_topc(sK0) != k5_tmap_1(sK0,u1_struct_0(sK1))
    | r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f216,f73])).

fof(f216,plain,
    ( v2_struct_0(sK0)
    | u1_pre_topc(sK0) != k5_tmap_1(sK0,u1_struct_0(sK1))
    | r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f215,f81])).

% (29677)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
fof(f215,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | u1_pre_topc(sK0) != k5_tmap_1(sK0,u1_struct_0(sK1))
    | r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | ~ spl4_3
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f198,f77])).

fof(f198,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | u1_pre_topc(sK0) != k5_tmap_1(sK0,u1_struct_0(sK1))
    | r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | ~ spl4_14 ),
    inference(resolution,[],[f156,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | u1_pre_topc(X0) != k5_tmap_1(X0,X1)
      | r2_hidden(X1,u1_pre_topc(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f299,plain,
    ( spl4_23
    | spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f190,f151,f113,f80,f76,f72,f297])).

fof(f297,plain,
    ( spl4_23
  <=> u1_pre_topc(sK0) = k5_tmap_1(sK0,sK3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f113,plain,
    ( spl4_6
  <=> v1_xboole_0(sK3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f190,plain,
    ( u1_pre_topc(sK0) = k5_tmap_1(sK0,sK3(sK0))
    | spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f178,f189])).

fof(f189,plain,
    ( r2_hidden(sK3(sK0),u1_pre_topc(sK0))
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f188,f187])).

fof(f187,plain,
    ( v3_pre_topc(sK3(sK0),sK0)
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f186,f114])).

fof(f114,plain,
    ( v1_xboole_0(sK3(sK0))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f113])).

fof(f186,plain,
    ( ~ v1_xboole_0(sK3(sK0))
    | v3_pre_topc(sK3(sK0),sK0)
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f185,f77])).

fof(f185,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ v1_xboole_0(sK3(sK0))
    | v3_pre_topc(sK3(sK0),sK0)
    | ~ spl4_4
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f167,f81])).

fof(f167,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ v1_xboole_0(sK3(sK0))
    | v3_pre_topc(sK3(sK0),sK0)
    | ~ spl4_13 ),
    inference(resolution,[],[f152,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ v1_xboole_0(X1)
      | v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_xboole_0(X1)
           => v3_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_tops_1)).

fof(f188,plain,
    ( r2_hidden(sK3(sK0),u1_pre_topc(sK0))
    | ~ v3_pre_topc(sK3(sK0),sK0)
    | ~ spl4_4
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f169,f81])).

fof(f169,plain,
    ( ~ l1_pre_topc(sK0)
    | r2_hidden(sK3(sK0),u1_pre_topc(sK0))
    | ~ v3_pre_topc(sK3(sK0),sK0)
    | ~ spl4_13 ),
    inference(resolution,[],[f152,f61])).

fof(f178,plain,
    ( u1_pre_topc(sK0) = k5_tmap_1(sK0,sK3(sK0))
    | ~ r2_hidden(sK3(sK0),u1_pre_topc(sK0))
    | spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f177,f73])).

fof(f177,plain,
    ( v2_struct_0(sK0)
    | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK3(sK0))
    | ~ r2_hidden(sK3(sK0),u1_pre_topc(sK0))
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f176,f81])).

fof(f176,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK3(sK0))
    | ~ r2_hidden(sK3(sK0),u1_pre_topc(sK0))
    | ~ spl4_3
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f164,f77])).

fof(f164,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK3(sK0))
    | ~ r2_hidden(sK3(sK0),u1_pre_topc(sK0))
    | ~ spl4_13 ),
    inference(resolution,[],[f152,f56])).

fof(f161,plain,
    ( spl4_15
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f124,f120,f86,f80,f159])).

fof(f120,plain,
    ( spl4_8
  <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f124,plain,
    ( sK2(sK0,sK1) = u1_struct_0(sK1)
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f110,f123])).

fof(f123,plain,
    ( ~ v1_tsep_1(sK1,sK0)
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f66,f121])).

fof(f121,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f120])).

fof(f66,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k8_tmap_1(sK0,sK1)
    | ~ v1_tsep_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f35,f39])).

fof(f39,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) )
          <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) )
          <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ( ( m1_pre_topc(X1,X0)
                & v1_tsep_1(X1,X0) )
            <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ( ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) )
          <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_tmap_1)).

fof(f35,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k8_tmap_1(sK0,sK1)
    | ~ v1_tsep_1(sK1,sK0)
    | ~ m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f110,plain,
    ( sK2(sK0,sK1) = u1_struct_0(sK1)
    | v1_tsep_1(sK1,sK0)
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f94,f81])).

fof(f94,plain,
    ( ~ l1_pre_topc(sK0)
    | sK2(sK0,sK1) = u1_struct_0(sK1)
    | v1_tsep_1(sK1,sK0)
    | ~ spl4_5 ),
    inference(resolution,[],[f87,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | u1_struct_0(X1) = sK2(X0,X1)
      | v1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f157,plain,
    ( spl4_14
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f111,f86,f80,f155])).

fof(f111,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f95,f81])).

fof(f95,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_5 ),
    inference(resolution,[],[f87,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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

fof(f153,plain,
    ( spl4_13
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f83,f80,f151])).

fof(f83,plain,
    ( m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_4 ),
    inference(resolution,[],[f81,f62])).

fof(f62,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ? [X1] :
          ( v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_connsp_1)).

fof(f139,plain,
    ( spl4_11
    | spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f104,f86,f80,f76,f72,f137])).

fof(f104,plain,
    ( l1_pre_topc(k8_tmap_1(sK0,sK1))
    | spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f103,f73])).

fof(f103,plain,
    ( v2_struct_0(sK0)
    | l1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f102,f81])).

fof(f102,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | l1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f91,f77])).

fof(f91,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | l1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ spl4_5 ),
    inference(resolution,[],[f87,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | l1_pre_topc(k8_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_tmap_1)).

fof(f131,plain,
    ( spl4_9
    | spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f98,f86,f80,f76,f72,f129])).

fof(f98,plain,
    ( v1_pre_topc(k8_tmap_1(sK0,sK1))
    | spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f97,f73])).

fof(f97,plain,
    ( v2_struct_0(sK0)
    | v1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f96,f81])).

fof(f96,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f89,f77])).

fof(f89,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_pre_topc(k8_tmap_1(sK0,sK1))
    | ~ spl4_5 ),
    inference(resolution,[],[f87,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_pre_topc(k8_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f127,plain,
    ( ~ spl4_7
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f123,f120,f117])).

fof(f122,plain,
    ( spl4_7
    | spl4_8 ),
    inference(avatar_split_clause,[],[f36,f120,f117])).

fof(f36,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1)
    | v1_tsep_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f115,plain,
    ( spl4_6
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f84,f80,f113])).

fof(f84,plain,
    ( v1_xboole_0(sK3(sK0))
    | ~ spl4_4 ),
    inference(resolution,[],[f81,f63])).

fof(f63,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | v1_xboole_0(sK3(X0)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f88,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f39,f86])).

fof(f82,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f42,f80])).

fof(f42,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f78,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f41,f76])).

fof(f41,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f74,plain,(
    ~ spl4_2 ),
    inference(avatar_split_clause,[],[f40,f72])).

fof(f40,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f70,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f38,f68])).

fof(f38,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:49:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.41  % (29685)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.42  % (29685)Refutation not found, incomplete strategy% (29685)------------------------------
% 0.20/0.42  % (29685)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.44  % (29685)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.44  
% 0.20/0.44  % (29685)Memory used [KB]: 1791
% 0.20/0.44  % (29685)Time elapsed: 0.008 s
% 0.20/0.44  % (29685)------------------------------
% 0.20/0.44  % (29685)------------------------------
% 0.20/0.44  % (29684)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.44  % (29684)Refutation not found, incomplete strategy% (29684)------------------------------
% 0.20/0.44  % (29684)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.44  % (29684)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.44  
% 0.20/0.44  % (29684)Memory used [KB]: 6140
% 0.20/0.44  % (29684)Time elapsed: 0.043 s
% 0.20/0.44  % (29684)------------------------------
% 0.20/0.44  % (29684)------------------------------
% 0.20/0.45  % (29680)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.48  % (29672)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.48  % (29692)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.48  % (29679)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.48  % (29673)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.49  % (29686)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.49  % (29681)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.49  % (29692)Refutation not found, incomplete strategy% (29692)------------------------------
% 0.20/0.49  % (29692)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (29692)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (29692)Memory used [KB]: 10618
% 0.20/0.49  % (29692)Time elapsed: 0.072 s
% 0.20/0.49  % (29692)------------------------------
% 0.20/0.49  % (29692)------------------------------
% 0.20/0.49  % (29682)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.49  % (29690)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.49  % (29674)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.49  % (29691)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.50  % (29672)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f428,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(avatar_sat_refutation,[],[f70,f74,f78,f82,f88,f115,f122,f127,f131,f139,f153,f157,f161,f299,f303,f384,f397,f405,f406,f426,f427])).
% 0.20/0.50  fof(f427,plain,(
% 0.20/0.50    u1_pre_topc(sK0) != u1_pre_topc(k8_tmap_1(sK0,sK1)) | u1_pre_topc(sK0) != k5_tmap_1(sK0,sK3(sK0)) | k8_tmap_1(sK0,sK1) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(k8_tmap_1(sK0,sK1))) | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1)),
% 0.20/0.50    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.50  fof(f426,plain,(
% 0.20/0.50    spl4_1 | spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_7 | ~spl4_14 | spl4_24),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f425])).
% 0.20/0.50  fof(f425,plain,(
% 0.20/0.50    $false | (spl4_1 | spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_7 | ~spl4_14 | spl4_24)),
% 0.20/0.50    inference(subsumption_resolution,[],[f424,f423])).
% 0.20/0.50  fof(f423,plain,(
% 0.20/0.50    r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0)) | (~spl4_4 | ~spl4_5 | ~spl4_7 | ~spl4_14)),
% 0.20/0.50    inference(subsumption_resolution,[],[f234,f419])).
% 0.20/0.50  fof(f419,plain,(
% 0.20/0.50    v3_pre_topc(u1_struct_0(sK1),sK0) | (~spl4_4 | ~spl4_5 | ~spl4_7 | ~spl4_14)),
% 0.20/0.50    inference(subsumption_resolution,[],[f411,f118])).
% 0.20/0.50  fof(f118,plain,(
% 0.20/0.50    v1_tsep_1(sK1,sK0) | ~spl4_7),
% 0.20/0.50    inference(avatar_component_clause,[],[f117])).
% 0.20/0.50  fof(f117,plain,(
% 0.20/0.50    spl4_7 <=> v1_tsep_1(sK1,sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.20/0.50  fof(f411,plain,(
% 0.20/0.50    v3_pre_topc(u1_struct_0(sK1),sK0) | ~v1_tsep_1(sK1,sK0) | (~spl4_4 | ~spl4_5 | ~spl4_14)),
% 0.20/0.50    inference(subsumption_resolution,[],[f410,f81])).
% 0.20/0.50  fof(f81,plain,(
% 0.20/0.50    l1_pre_topc(sK0) | ~spl4_4),
% 0.20/0.50    inference(avatar_component_clause,[],[f80])).
% 0.20/0.50  fof(f80,plain,(
% 0.20/0.50    spl4_4 <=> l1_pre_topc(sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.50  fof(f410,plain,(
% 0.20/0.50    ~l1_pre_topc(sK0) | v3_pre_topc(u1_struct_0(sK1),sK0) | ~v1_tsep_1(sK1,sK0) | (~spl4_5 | ~spl4_14)),
% 0.20/0.50    inference(subsumption_resolution,[],[f195,f87])).
% 0.20/0.50  fof(f87,plain,(
% 0.20/0.50    m1_pre_topc(sK1,sK0) | ~spl4_5),
% 0.20/0.50    inference(avatar_component_clause,[],[f86])).
% 0.20/0.50  fof(f86,plain,(
% 0.20/0.50    spl4_5 <=> m1_pre_topc(sK1,sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.50  fof(f195,plain,(
% 0.20/0.50    ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | v3_pre_topc(u1_struct_0(sK1),sK0) | ~v1_tsep_1(sK1,sK0) | ~spl4_14),
% 0.20/0.50    inference(resolution,[],[f156,f65])).
% 0.20/0.50  fof(f65,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v3_pre_topc(u1_struct_0(X1),X0) | ~v1_tsep_1(X1,X0)) )),
% 0.20/0.50    inference(equality_resolution,[],[f50])).
% 0.20/0.50  fof(f50,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X1) != X2 | v3_pre_topc(X2,X0) | ~v1_tsep_1(X1,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f25])).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : ((v1_tsep_1(X1,X0) <=> ! [X2] : (v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.50    inference(flattening,[],[f24])).
% 0.20/0.50  fof(f24,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : ((v1_tsep_1(X1,X0) <=> ! [X2] : ((v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f5])).
% 0.20/0.50  fof(f5,axiom,(
% 0.20/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tsep_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v3_pre_topc(X2,X0))))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tsep_1)).
% 0.20/0.50  fof(f156,plain,(
% 0.20/0.50    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_14),
% 0.20/0.50    inference(avatar_component_clause,[],[f155])).
% 0.20/0.50  fof(f155,plain,(
% 0.20/0.50    spl4_14 <=> m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.20/0.50  fof(f234,plain,(
% 0.20/0.50    r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0)) | ~v3_pre_topc(u1_struct_0(sK1),sK0) | (~spl4_4 | ~spl4_14)),
% 0.20/0.50    inference(subsumption_resolution,[],[f204,f81])).
% 0.20/0.50  fof(f204,plain,(
% 0.20/0.50    ~l1_pre_topc(sK0) | r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0)) | ~v3_pre_topc(u1_struct_0(sK1),sK0) | ~spl4_14),
% 0.20/0.50    inference(resolution,[],[f156,f61])).
% 0.20/0.50  fof(f61,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f33])).
% 0.20/0.50  fof(f33,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0)))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).
% 0.20/0.50  fof(f424,plain,(
% 0.20/0.50    ~r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0)) | (spl4_1 | spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_14 | spl4_24)),
% 0.20/0.50    inference(subsumption_resolution,[],[f222,f302])).
% 0.20/0.50  fof(f302,plain,(
% 0.20/0.50    u1_pre_topc(sK0) != u1_pre_topc(k8_tmap_1(sK0,sK1)) | spl4_24),
% 0.20/0.50    inference(avatar_component_clause,[],[f301])).
% 0.20/0.50  fof(f301,plain,(
% 0.20/0.50    spl4_24 <=> u1_pre_topc(sK0) = u1_pre_topc(k8_tmap_1(sK0,sK1))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 0.20/0.50  fof(f222,plain,(
% 0.20/0.50    u1_pre_topc(sK0) = u1_pre_topc(k8_tmap_1(sK0,sK1)) | ~r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0)) | (spl4_1 | spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_14)),
% 0.20/0.50    inference(forward_demodulation,[],[f221,f209])).
% 0.20/0.50  fof(f209,plain,(
% 0.20/0.50    u1_pre_topc(k8_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,u1_struct_0(sK1)) | (spl4_1 | spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_14)),
% 0.20/0.50    inference(subsumption_resolution,[],[f208,f73])).
% 0.20/0.50  fof(f73,plain,(
% 0.20/0.50    ~v2_struct_0(sK0) | spl4_2),
% 0.20/0.50    inference(avatar_component_clause,[],[f72])).
% 0.20/0.50  fof(f72,plain,(
% 0.20/0.50    spl4_2 <=> v2_struct_0(sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.50  fof(f208,plain,(
% 0.20/0.50    v2_struct_0(sK0) | u1_pre_topc(k8_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,u1_struct_0(sK1)) | (spl4_1 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_14)),
% 0.20/0.50    inference(subsumption_resolution,[],[f207,f87])).
% 0.20/0.50  fof(f207,plain,(
% 0.20/0.50    ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK0) | u1_pre_topc(k8_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,u1_struct_0(sK1)) | (spl4_1 | ~spl4_3 | ~spl4_4 | ~spl4_14)),
% 0.20/0.50    inference(subsumption_resolution,[],[f206,f69])).
% 0.20/0.50  fof(f69,plain,(
% 0.20/0.50    ~v2_struct_0(sK1) | spl4_1),
% 0.20/0.50    inference(avatar_component_clause,[],[f68])).
% 0.20/0.50  fof(f68,plain,(
% 0.20/0.50    spl4_1 <=> v2_struct_0(sK1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.50  fof(f206,plain,(
% 0.20/0.50    v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK0) | u1_pre_topc(k8_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,u1_struct_0(sK1)) | (~spl4_3 | ~spl4_4 | ~spl4_14)),
% 0.20/0.50    inference(subsumption_resolution,[],[f205,f81])).
% 0.20/0.50  fof(f205,plain,(
% 0.20/0.50    ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK0) | u1_pre_topc(k8_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,u1_struct_0(sK1)) | (~spl4_3 | ~spl4_14)),
% 0.20/0.50    inference(subsumption_resolution,[],[f196,f77])).
% 0.20/0.50  fof(f77,plain,(
% 0.20/0.50    v2_pre_topc(sK0) | ~spl4_3),
% 0.20/0.50    inference(avatar_component_clause,[],[f76])).
% 0.20/0.50  fof(f76,plain,(
% 0.20/0.50    spl4_3 <=> v2_pre_topc(sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.50  fof(f196,plain,(
% 0.20/0.50    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK0) | u1_pre_topc(k8_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,u1_struct_0(sK1)) | ~spl4_14),
% 0.20/0.50    inference(resolution,[],[f156,f64])).
% 0.20/0.50  fof(f64,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X0) | u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,u1_struct_0(X1))) )),
% 0.20/0.50    inference(equality_resolution,[],[f46])).
% 0.20/0.50  fof(f46,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X1) != X2 | u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f19])).
% 0.20/0.50  fof(f19,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : ((! [X2] : (u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f18])).
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : ((! [X2] : ((u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f10])).
% 0.20/0.50  fof(f10,axiom,(
% 0.20/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2))) & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1)))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t114_tmap_1)).
% 0.20/0.50  fof(f221,plain,(
% 0.20/0.50    u1_pre_topc(sK0) = k5_tmap_1(sK0,u1_struct_0(sK1)) | ~r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0)) | (spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_14)),
% 0.20/0.50    inference(subsumption_resolution,[],[f220,f73])).
% 0.20/0.50  fof(f220,plain,(
% 0.20/0.50    v2_struct_0(sK0) | u1_pre_topc(sK0) = k5_tmap_1(sK0,u1_struct_0(sK1)) | ~r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0)) | (~spl4_3 | ~spl4_4 | ~spl4_14)),
% 0.20/0.50    inference(subsumption_resolution,[],[f219,f81])).
% 0.20/0.50  fof(f219,plain,(
% 0.20/0.50    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | u1_pre_topc(sK0) = k5_tmap_1(sK0,u1_struct_0(sK1)) | ~r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0)) | (~spl4_3 | ~spl4_14)),
% 0.20/0.50    inference(subsumption_resolution,[],[f199,f77])).
% 0.20/0.50  fof(f199,plain,(
% 0.20/0.50    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | u1_pre_topc(sK0) = k5_tmap_1(sK0,u1_struct_0(sK1)) | ~r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0)) | ~spl4_14),
% 0.20/0.50    inference(resolution,[],[f156,f56])).
% 0.20/0.50  fof(f56,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | u1_pre_topc(X0) = k5_tmap_1(X0,X1) | ~r2_hidden(X1,u1_pre_topc(X0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f28])).
% 0.20/0.50  fof(f28,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : ((r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f27])).
% 0.20/0.50  fof(f27,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : ((r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f8])).
% 0.20/0.50  fof(f8,axiom,(
% 0.20/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_tmap_1)).
% 0.20/0.50  fof(f406,plain,(
% 0.20/0.50    k6_tmap_1(sK0,sK3(sK0)) != g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK3(sK0))) | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k8_tmap_1(sK0,sK1) | k5_tmap_1(sK0,sK3(sK0)) != u1_pre_topc(k6_tmap_1(sK0,sK3(sK0))) | u1_pre_topc(sK0) != k5_tmap_1(sK0,sK3(sK0)) | u1_pre_topc(sK0) = u1_pre_topc(k8_tmap_1(sK0,sK1))),
% 0.20/0.50    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.50  fof(f405,plain,(
% 0.20/0.50    spl4_36 | spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_13),
% 0.20/0.50    inference(avatar_split_clause,[],[f172,f151,f80,f76,f72,f403])).
% 0.20/0.50  fof(f403,plain,(
% 0.20/0.50    spl4_36 <=> k6_tmap_1(sK0,sK3(sK0)) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK3(sK0)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 0.20/0.50  fof(f151,plain,(
% 0.20/0.50    spl4_13 <=> m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.20/0.50  fof(f172,plain,(
% 0.20/0.50    k6_tmap_1(sK0,sK3(sK0)) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK3(sK0))) | (spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_13)),
% 0.20/0.50    inference(subsumption_resolution,[],[f171,f73])).
% 0.20/0.50  fof(f171,plain,(
% 0.20/0.50    v2_struct_0(sK0) | k6_tmap_1(sK0,sK3(sK0)) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK3(sK0))) | (~spl4_3 | ~spl4_4 | ~spl4_13)),
% 0.20/0.50    inference(subsumption_resolution,[],[f170,f81])).
% 0.20/0.50  fof(f170,plain,(
% 0.20/0.50    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | k6_tmap_1(sK0,sK3(sK0)) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK3(sK0))) | (~spl4_3 | ~spl4_13)),
% 0.20/0.50    inference(subsumption_resolution,[],[f162,f77])).
% 0.20/0.50  fof(f162,plain,(
% 0.20/0.50    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | k6_tmap_1(sK0,sK3(sK0)) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK3(sK0))) | ~spl4_13),
% 0.20/0.50    inference(resolution,[],[f152,f48])).
% 0.20/0.50  fof(f48,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f21])).
% 0.20/0.50  fof(f21,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f20])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f6])).
% 0.20/0.50  fof(f6,axiom,(
% 0.20/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_tmap_1)).
% 0.20/0.50  fof(f152,plain,(
% 0.20/0.50    m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_13),
% 0.20/0.50    inference(avatar_component_clause,[],[f151])).
% 0.20/0.50  fof(f397,plain,(
% 0.20/0.50    spl4_34 | spl4_1 | spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_9 | ~spl4_11),
% 0.20/0.50    inference(avatar_split_clause,[],[f142,f137,f129,f86,f80,f76,f72,f68,f395])).
% 0.20/0.50  fof(f395,plain,(
% 0.20/0.50    spl4_34 <=> k8_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(k8_tmap_1(sK0,sK1)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).
% 0.20/0.50  fof(f129,plain,(
% 0.20/0.50    spl4_9 <=> v1_pre_topc(k8_tmap_1(sK0,sK1))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.20/0.50  fof(f137,plain,(
% 0.20/0.50    spl4_11 <=> l1_pre_topc(k8_tmap_1(sK0,sK1))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.20/0.50  fof(f142,plain,(
% 0.20/0.50    k8_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(k8_tmap_1(sK0,sK1))) | (spl4_1 | spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_9 | ~spl4_11)),
% 0.20/0.50    inference(forward_demodulation,[],[f141,f108])).
% 0.20/0.50  fof(f108,plain,(
% 0.20/0.50    u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1)) | (spl4_1 | spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5)),
% 0.20/0.50    inference(subsumption_resolution,[],[f107,f73])).
% 0.20/0.50  fof(f107,plain,(
% 0.20/0.50    v2_struct_0(sK0) | u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1)) | (spl4_1 | ~spl4_3 | ~spl4_4 | ~spl4_5)),
% 0.20/0.50    inference(subsumption_resolution,[],[f106,f69])).
% 0.20/0.50  fof(f106,plain,(
% 0.20/0.50    v2_struct_0(sK1) | v2_struct_0(sK0) | u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1)) | (~spl4_3 | ~spl4_4 | ~spl4_5)),
% 0.20/0.50    inference(subsumption_resolution,[],[f105,f81])).
% 0.20/0.50  fof(f105,plain,(
% 0.20/0.50    ~l1_pre_topc(sK0) | v2_struct_0(sK1) | v2_struct_0(sK0) | u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1)) | (~spl4_3 | ~spl4_5)),
% 0.20/0.50    inference(subsumption_resolution,[],[f92,f77])).
% 0.20/0.50  fof(f92,plain,(
% 0.20/0.50    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | v2_struct_0(sK0) | u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1)) | ~spl4_5),
% 0.20/0.50    inference(resolution,[],[f87,f47])).
% 0.20/0.50  fof(f47,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | v2_struct_0(X0) | u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f19])).
% 0.20/0.50  fof(f141,plain,(
% 0.20/0.50    k8_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(k8_tmap_1(sK0,sK1)),u1_pre_topc(k8_tmap_1(sK0,sK1))) | (~spl4_9 | ~spl4_11)),
% 0.20/0.50    inference(subsumption_resolution,[],[f140,f138])).
% 0.20/0.50  fof(f138,plain,(
% 0.20/0.50    l1_pre_topc(k8_tmap_1(sK0,sK1)) | ~spl4_11),
% 0.20/0.50    inference(avatar_component_clause,[],[f137])).
% 0.20/0.50  fof(f140,plain,(
% 0.20/0.50    ~l1_pre_topc(k8_tmap_1(sK0,sK1)) | k8_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(k8_tmap_1(sK0,sK1)),u1_pre_topc(k8_tmap_1(sK0,sK1))) | ~spl4_9),
% 0.20/0.50    inference(resolution,[],[f130,f49])).
% 0.20/0.50  fof(f49,plain,(
% 0.20/0.50    ( ! [X0] : (~v1_pre_topc(X0) | ~l1_pre_topc(X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0) )),
% 0.20/0.50    inference(cnf_transformation,[],[f23])).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 0.20/0.50    inference(flattening,[],[f22])).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).
% 0.20/0.50  fof(f130,plain,(
% 0.20/0.50    v1_pre_topc(k8_tmap_1(sK0,sK1)) | ~spl4_9),
% 0.20/0.50    inference(avatar_component_clause,[],[f129])).
% 0.20/0.50  fof(f384,plain,(
% 0.20/0.50    spl4_31 | spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_13),
% 0.20/0.50    inference(avatar_split_clause,[],[f184,f151,f80,f76,f72,f382])).
% 0.20/0.50  fof(f382,plain,(
% 0.20/0.50    spl4_31 <=> k5_tmap_1(sK0,sK3(sK0)) = u1_pre_topc(k6_tmap_1(sK0,sK3(sK0)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).
% 0.20/0.50  fof(f184,plain,(
% 0.20/0.50    k5_tmap_1(sK0,sK3(sK0)) = u1_pre_topc(k6_tmap_1(sK0,sK3(sK0))) | (spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_13)),
% 0.20/0.50    inference(subsumption_resolution,[],[f183,f73])).
% 0.20/0.50  fof(f183,plain,(
% 0.20/0.50    v2_struct_0(sK0) | k5_tmap_1(sK0,sK3(sK0)) = u1_pre_topc(k6_tmap_1(sK0,sK3(sK0))) | (~spl4_3 | ~spl4_4 | ~spl4_13)),
% 0.20/0.50    inference(subsumption_resolution,[],[f182,f81])).
% 0.20/0.50  fof(f182,plain,(
% 0.20/0.50    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | k5_tmap_1(sK0,sK3(sK0)) = u1_pre_topc(k6_tmap_1(sK0,sK3(sK0))) | (~spl4_3 | ~spl4_13)),
% 0.20/0.50    inference(subsumption_resolution,[],[f166,f77])).
% 0.20/0.50  fof(f166,plain,(
% 0.20/0.50    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | k5_tmap_1(sK0,sK3(sK0)) = u1_pre_topc(k6_tmap_1(sK0,sK3(sK0))) | ~spl4_13),
% 0.20/0.50    inference(resolution,[],[f152,f58])).
% 0.20/0.50  fof(f58,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f30])).
% 0.20/0.50  fof(f30,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : ((k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1)) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f29])).
% 0.20/0.50  fof(f29,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : ((k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1)) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f9])).
% 0.20/0.50  fof(f9,axiom,(
% 0.20/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1)) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_tmap_1)).
% 0.20/0.50  fof(f303,plain,(
% 0.20/0.50    ~spl4_24 | spl4_1 | spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | spl4_7 | ~spl4_14 | ~spl4_15),
% 0.20/0.50    inference(avatar_split_clause,[],[f241,f159,f155,f117,f86,f80,f76,f72,f68,f301])).
% 0.20/0.50  fof(f159,plain,(
% 0.20/0.50    spl4_15 <=> sK2(sK0,sK1) = u1_struct_0(sK1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.20/0.50  fof(f241,plain,(
% 0.20/0.50    u1_pre_topc(sK0) != u1_pre_topc(k8_tmap_1(sK0,sK1)) | (spl4_1 | spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | spl4_7 | ~spl4_14 | ~spl4_15)),
% 0.20/0.50    inference(subsumption_resolution,[],[f218,f239])).
% 0.20/0.50  fof(f239,plain,(
% 0.20/0.50    ~r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0)) | (~spl4_4 | ~spl4_5 | spl4_7 | ~spl4_14 | ~spl4_15)),
% 0.20/0.50    inference(subsumption_resolution,[],[f233,f238])).
% 0.20/0.50  fof(f238,plain,(
% 0.20/0.50    ~v3_pre_topc(u1_struct_0(sK1),sK0) | (~spl4_4 | ~spl4_5 | spl4_7 | ~spl4_15)),
% 0.20/0.50    inference(subsumption_resolution,[],[f237,f126])).
% 0.20/0.50  fof(f126,plain,(
% 0.20/0.50    ~v1_tsep_1(sK1,sK0) | spl4_7),
% 0.20/0.50    inference(avatar_component_clause,[],[f117])).
% 0.20/0.50  fof(f237,plain,(
% 0.20/0.50    ~v3_pre_topc(u1_struct_0(sK1),sK0) | v1_tsep_1(sK1,sK0) | (~spl4_4 | ~spl4_5 | ~spl4_15)),
% 0.20/0.50    inference(subsumption_resolution,[],[f236,f81])).
% 0.20/0.50  fof(f236,plain,(
% 0.20/0.50    ~v3_pre_topc(u1_struct_0(sK1),sK0) | ~l1_pre_topc(sK0) | v1_tsep_1(sK1,sK0) | (~spl4_5 | ~spl4_15)),
% 0.20/0.50    inference(subsumption_resolution,[],[f235,f87])).
% 0.20/0.50  fof(f235,plain,(
% 0.20/0.50    ~v3_pre_topc(u1_struct_0(sK1),sK0) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | v1_tsep_1(sK1,sK0) | ~spl4_15),
% 0.20/0.50    inference(superposition,[],[f53,f160])).
% 0.20/0.50  fof(f160,plain,(
% 0.20/0.50    sK2(sK0,sK1) = u1_struct_0(sK1) | ~spl4_15),
% 0.20/0.50    inference(avatar_component_clause,[],[f159])).
% 0.20/0.50  fof(f53,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v3_pre_topc(sK2(X0,X1),X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v1_tsep_1(X1,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f25])).
% 0.20/0.50  fof(f233,plain,(
% 0.20/0.50    ~r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0)) | v3_pre_topc(u1_struct_0(sK1),sK0) | (~spl4_4 | ~spl4_14)),
% 0.20/0.50    inference(subsumption_resolution,[],[f203,f81])).
% 0.20/0.50  fof(f203,plain,(
% 0.20/0.50    ~l1_pre_topc(sK0) | ~r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0)) | v3_pre_topc(u1_struct_0(sK1),sK0) | ~spl4_14),
% 0.20/0.50    inference(resolution,[],[f156,f60])).
% 0.20/0.50  fof(f60,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~r2_hidden(X1,u1_pre_topc(X0)) | v3_pre_topc(X1,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f33])).
% 0.20/0.50  fof(f218,plain,(
% 0.20/0.50    u1_pre_topc(sK0) != u1_pre_topc(k8_tmap_1(sK0,sK1)) | r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0)) | (spl4_1 | spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_14)),
% 0.20/0.50    inference(forward_demodulation,[],[f217,f209])).
% 0.20/0.50  fof(f217,plain,(
% 0.20/0.50    u1_pre_topc(sK0) != k5_tmap_1(sK0,u1_struct_0(sK1)) | r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0)) | (spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_14)),
% 0.20/0.50    inference(subsumption_resolution,[],[f216,f73])).
% 0.20/0.50  fof(f216,plain,(
% 0.20/0.50    v2_struct_0(sK0) | u1_pre_topc(sK0) != k5_tmap_1(sK0,u1_struct_0(sK1)) | r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0)) | (~spl4_3 | ~spl4_4 | ~spl4_14)),
% 0.20/0.50    inference(subsumption_resolution,[],[f215,f81])).
% 0.20/0.50  % (29677)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.50  fof(f215,plain,(
% 0.20/0.50    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | u1_pre_topc(sK0) != k5_tmap_1(sK0,u1_struct_0(sK1)) | r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0)) | (~spl4_3 | ~spl4_14)),
% 0.20/0.50    inference(subsumption_resolution,[],[f198,f77])).
% 0.20/0.50  fof(f198,plain,(
% 0.20/0.50    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | u1_pre_topc(sK0) != k5_tmap_1(sK0,u1_struct_0(sK1)) | r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0)) | ~spl4_14),
% 0.20/0.50    inference(resolution,[],[f156,f55])).
% 0.20/0.50  fof(f55,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | u1_pre_topc(X0) != k5_tmap_1(X0,X1) | r2_hidden(X1,u1_pre_topc(X0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f28])).
% 0.20/0.50  fof(f299,plain,(
% 0.20/0.50    spl4_23 | spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_6 | ~spl4_13),
% 0.20/0.50    inference(avatar_split_clause,[],[f190,f151,f113,f80,f76,f72,f297])).
% 0.20/0.50  fof(f297,plain,(
% 0.20/0.50    spl4_23 <=> u1_pre_topc(sK0) = k5_tmap_1(sK0,sK3(sK0))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 0.20/0.50  fof(f113,plain,(
% 0.20/0.50    spl4_6 <=> v1_xboole_0(sK3(sK0))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.50  fof(f190,plain,(
% 0.20/0.50    u1_pre_topc(sK0) = k5_tmap_1(sK0,sK3(sK0)) | (spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_6 | ~spl4_13)),
% 0.20/0.50    inference(subsumption_resolution,[],[f178,f189])).
% 0.20/0.50  fof(f189,plain,(
% 0.20/0.50    r2_hidden(sK3(sK0),u1_pre_topc(sK0)) | (~spl4_3 | ~spl4_4 | ~spl4_6 | ~spl4_13)),
% 0.20/0.50    inference(subsumption_resolution,[],[f188,f187])).
% 0.20/0.50  fof(f187,plain,(
% 0.20/0.50    v3_pre_topc(sK3(sK0),sK0) | (~spl4_3 | ~spl4_4 | ~spl4_6 | ~spl4_13)),
% 0.20/0.50    inference(subsumption_resolution,[],[f186,f114])).
% 0.20/0.50  fof(f114,plain,(
% 0.20/0.50    v1_xboole_0(sK3(sK0)) | ~spl4_6),
% 0.20/0.50    inference(avatar_component_clause,[],[f113])).
% 0.20/0.50  fof(f186,plain,(
% 0.20/0.50    ~v1_xboole_0(sK3(sK0)) | v3_pre_topc(sK3(sK0),sK0) | (~spl4_3 | ~spl4_4 | ~spl4_13)),
% 0.20/0.50    inference(subsumption_resolution,[],[f185,f77])).
% 0.20/0.50  fof(f185,plain,(
% 0.20/0.50    ~v2_pre_topc(sK0) | ~v1_xboole_0(sK3(sK0)) | v3_pre_topc(sK3(sK0),sK0) | (~spl4_4 | ~spl4_13)),
% 0.20/0.50    inference(subsumption_resolution,[],[f167,f81])).
% 0.20/0.50  fof(f167,plain,(
% 0.20/0.50    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~v1_xboole_0(sK3(sK0)) | v3_pre_topc(sK3(sK0),sK0) | ~spl4_13),
% 0.20/0.50    inference(resolution,[],[f152,f59])).
% 0.20/0.50  fof(f59,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~v1_xboole_0(X1) | v3_pre_topc(X1,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f32])).
% 0.20/0.50  fof(f32,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (v3_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.50    inference(flattening,[],[f31])).
% 0.20/0.50  fof(f31,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) | ~v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_xboole_0(X1) => v3_pre_topc(X1,X0))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_tops_1)).
% 0.20/0.50  fof(f188,plain,(
% 0.20/0.50    r2_hidden(sK3(sK0),u1_pre_topc(sK0)) | ~v3_pre_topc(sK3(sK0),sK0) | (~spl4_4 | ~spl4_13)),
% 0.20/0.50    inference(subsumption_resolution,[],[f169,f81])).
% 0.20/0.50  fof(f169,plain,(
% 0.20/0.50    ~l1_pre_topc(sK0) | r2_hidden(sK3(sK0),u1_pre_topc(sK0)) | ~v3_pre_topc(sK3(sK0),sK0) | ~spl4_13),
% 0.20/0.50    inference(resolution,[],[f152,f61])).
% 0.20/0.50  fof(f178,plain,(
% 0.20/0.50    u1_pre_topc(sK0) = k5_tmap_1(sK0,sK3(sK0)) | ~r2_hidden(sK3(sK0),u1_pre_topc(sK0)) | (spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_13)),
% 0.20/0.50    inference(subsumption_resolution,[],[f177,f73])).
% 0.20/0.50  fof(f177,plain,(
% 0.20/0.50    v2_struct_0(sK0) | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK3(sK0)) | ~r2_hidden(sK3(sK0),u1_pre_topc(sK0)) | (~spl4_3 | ~spl4_4 | ~spl4_13)),
% 0.20/0.50    inference(subsumption_resolution,[],[f176,f81])).
% 0.20/0.50  fof(f176,plain,(
% 0.20/0.50    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK3(sK0)) | ~r2_hidden(sK3(sK0),u1_pre_topc(sK0)) | (~spl4_3 | ~spl4_13)),
% 0.20/0.50    inference(subsumption_resolution,[],[f164,f77])).
% 0.20/0.50  fof(f164,plain,(
% 0.20/0.50    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK3(sK0)) | ~r2_hidden(sK3(sK0),u1_pre_topc(sK0)) | ~spl4_13),
% 0.20/0.50    inference(resolution,[],[f152,f56])).
% 0.20/0.50  fof(f161,plain,(
% 0.20/0.50    spl4_15 | ~spl4_4 | ~spl4_5 | ~spl4_8),
% 0.20/0.50    inference(avatar_split_clause,[],[f124,f120,f86,f80,f159])).
% 0.20/0.50  fof(f120,plain,(
% 0.20/0.50    spl4_8 <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.20/0.50  fof(f124,plain,(
% 0.20/0.50    sK2(sK0,sK1) = u1_struct_0(sK1) | (~spl4_4 | ~spl4_5 | ~spl4_8)),
% 0.20/0.50    inference(subsumption_resolution,[],[f110,f123])).
% 0.20/0.50  fof(f123,plain,(
% 0.20/0.50    ~v1_tsep_1(sK1,sK0) | ~spl4_8),
% 0.20/0.50    inference(subsumption_resolution,[],[f66,f121])).
% 0.20/0.50  fof(f121,plain,(
% 0.20/0.50    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1) | ~spl4_8),
% 0.20/0.50    inference(avatar_component_clause,[],[f120])).
% 0.20/0.50  fof(f66,plain,(
% 0.20/0.50    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k8_tmap_1(sK0,sK1) | ~v1_tsep_1(sK1,sK0)),
% 0.20/0.50    inference(subsumption_resolution,[],[f35,f39])).
% 0.20/0.50  fof(f39,plain,(
% 0.20/0.50    m1_pre_topc(sK1,sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f15])).
% 0.20/0.50  fof(f15,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f14])).
% 0.20/0.50  fof(f14,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1)) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f13])).
% 0.20/0.50  fof(f13,negated_conjecture,(
% 0.20/0.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1))))),
% 0.20/0.50    inference(negated_conjecture,[],[f12])).
% 0.20/0.50  fof(f12,conjecture,(
% 0.20/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_tmap_1)).
% 0.20/0.50  fof(f35,plain,(
% 0.20/0.50    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k8_tmap_1(sK0,sK1) | ~v1_tsep_1(sK1,sK0) | ~m1_pre_topc(sK1,sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f15])).
% 0.20/0.50  fof(f110,plain,(
% 0.20/0.50    sK2(sK0,sK1) = u1_struct_0(sK1) | v1_tsep_1(sK1,sK0) | (~spl4_4 | ~spl4_5)),
% 0.20/0.50    inference(subsumption_resolution,[],[f94,f81])).
% 0.20/0.50  fof(f94,plain,(
% 0.20/0.50    ~l1_pre_topc(sK0) | sK2(sK0,sK1) = u1_struct_0(sK1) | v1_tsep_1(sK1,sK0) | ~spl4_5),
% 0.20/0.50    inference(resolution,[],[f87,f52])).
% 0.20/0.50  fof(f52,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | u1_struct_0(X1) = sK2(X0,X1) | v1_tsep_1(X1,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f25])).
% 0.20/0.50  fof(f157,plain,(
% 0.20/0.50    spl4_14 | ~spl4_4 | ~spl4_5),
% 0.20/0.50    inference(avatar_split_clause,[],[f111,f86,f80,f155])).
% 0.20/0.50  fof(f111,plain,(
% 0.20/0.50    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl4_4 | ~spl4_5)),
% 0.20/0.50    inference(subsumption_resolution,[],[f95,f81])).
% 0.20/0.50  fof(f95,plain,(
% 0.20/0.50    ~l1_pre_topc(sK0) | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_5),
% 0.20/0.50    inference(resolution,[],[f87,f54])).
% 0.20/0.50  fof(f54,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f26])).
% 0.20/0.50  fof(f26,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f11])).
% 0.20/0.50  fof(f11,axiom,(
% 0.20/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.20/0.50  fof(f153,plain,(
% 0.20/0.50    spl4_13 | ~spl4_4),
% 0.20/0.50    inference(avatar_split_clause,[],[f83,f80,f151])).
% 0.20/0.50  fof(f83,plain,(
% 0.20/0.50    m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_4),
% 0.20/0.50    inference(resolution,[],[f81,f62])).
% 0.20/0.50  fof(f62,plain,(
% 0.20/0.50    ( ! [X0] : (~l1_pre_topc(X0) | m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f34])).
% 0.20/0.50  fof(f34,plain,(
% 0.20/0.50    ! [X0] : (? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0] : (l1_pre_topc(X0) => ? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_connsp_1)).
% 0.20/0.50  fof(f139,plain,(
% 0.20/0.50    spl4_11 | spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5),
% 0.20/0.50    inference(avatar_split_clause,[],[f104,f86,f80,f76,f72,f137])).
% 0.20/0.50  fof(f104,plain,(
% 0.20/0.50    l1_pre_topc(k8_tmap_1(sK0,sK1)) | (spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5)),
% 0.20/0.50    inference(subsumption_resolution,[],[f103,f73])).
% 0.20/0.50  fof(f103,plain,(
% 0.20/0.50    v2_struct_0(sK0) | l1_pre_topc(k8_tmap_1(sK0,sK1)) | (~spl4_3 | ~spl4_4 | ~spl4_5)),
% 0.20/0.50    inference(subsumption_resolution,[],[f102,f81])).
% 0.20/0.50  fof(f102,plain,(
% 0.20/0.50    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | l1_pre_topc(k8_tmap_1(sK0,sK1)) | (~spl4_3 | ~spl4_5)),
% 0.20/0.50    inference(subsumption_resolution,[],[f91,f77])).
% 0.20/0.50  fof(f91,plain,(
% 0.20/0.50    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | l1_pre_topc(k8_tmap_1(sK0,sK1)) | ~spl4_5),
% 0.20/0.50    inference(resolution,[],[f87,f45])).
% 0.20/0.50  fof(f45,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | l1_pre_topc(k8_tmap_1(X0,X1))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f17])).
% 0.20/0.50  fof(f17,plain,(
% 0.20/0.50    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f16])).
% 0.20/0.50  fof(f16,plain,(
% 0.20/0.50    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f7])).
% 0.20/0.50  fof(f7,axiom,(
% 0.20/0.50    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_tmap_1)).
% 0.20/0.50  fof(f131,plain,(
% 0.20/0.50    spl4_9 | spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5),
% 0.20/0.50    inference(avatar_split_clause,[],[f98,f86,f80,f76,f72,f129])).
% 0.20/0.50  fof(f98,plain,(
% 0.20/0.50    v1_pre_topc(k8_tmap_1(sK0,sK1)) | (spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5)),
% 0.20/0.50    inference(subsumption_resolution,[],[f97,f73])).
% 0.20/0.50  fof(f97,plain,(
% 0.20/0.50    v2_struct_0(sK0) | v1_pre_topc(k8_tmap_1(sK0,sK1)) | (~spl4_3 | ~spl4_4 | ~spl4_5)),
% 0.20/0.50    inference(subsumption_resolution,[],[f96,f81])).
% 0.20/0.50  fof(f96,plain,(
% 0.20/0.50    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v1_pre_topc(k8_tmap_1(sK0,sK1)) | (~spl4_3 | ~spl4_5)),
% 0.20/0.50    inference(subsumption_resolution,[],[f89,f77])).
% 0.20/0.50  fof(f89,plain,(
% 0.20/0.50    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v1_pre_topc(k8_tmap_1(sK0,sK1)) | ~spl4_5),
% 0.20/0.50    inference(resolution,[],[f87,f43])).
% 0.20/0.50  fof(f43,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | v1_pre_topc(k8_tmap_1(X0,X1))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f17])).
% 0.20/0.50  fof(f127,plain,(
% 0.20/0.50    ~spl4_7 | ~spl4_8),
% 0.20/0.50    inference(avatar_split_clause,[],[f123,f120,f117])).
% 0.20/0.50  fof(f122,plain,(
% 0.20/0.50    spl4_7 | spl4_8),
% 0.20/0.50    inference(avatar_split_clause,[],[f36,f120,f117])).
% 0.20/0.50  fof(f36,plain,(
% 0.20/0.50    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1) | v1_tsep_1(sK1,sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f15])).
% 0.20/0.50  fof(f115,plain,(
% 0.20/0.50    spl4_6 | ~spl4_4),
% 0.20/0.50    inference(avatar_split_clause,[],[f84,f80,f113])).
% 0.20/0.50  fof(f84,plain,(
% 0.20/0.50    v1_xboole_0(sK3(sK0)) | ~spl4_4),
% 0.20/0.50    inference(resolution,[],[f81,f63])).
% 0.20/0.50  fof(f63,plain,(
% 0.20/0.50    ( ! [X0] : (~l1_pre_topc(X0) | v1_xboole_0(sK3(X0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f34])).
% 0.20/0.50  fof(f88,plain,(
% 0.20/0.50    spl4_5),
% 0.20/0.50    inference(avatar_split_clause,[],[f39,f86])).
% 0.20/0.50  fof(f82,plain,(
% 0.20/0.50    spl4_4),
% 0.20/0.50    inference(avatar_split_clause,[],[f42,f80])).
% 0.20/0.50  fof(f42,plain,(
% 0.20/0.50    l1_pre_topc(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f15])).
% 0.20/0.50  fof(f78,plain,(
% 0.20/0.50    spl4_3),
% 0.20/0.50    inference(avatar_split_clause,[],[f41,f76])).
% 0.20/0.50  fof(f41,plain,(
% 0.20/0.50    v2_pre_topc(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f15])).
% 0.20/0.50  fof(f74,plain,(
% 0.20/0.50    ~spl4_2),
% 0.20/0.50    inference(avatar_split_clause,[],[f40,f72])).
% 0.20/0.50  fof(f40,plain,(
% 0.20/0.50    ~v2_struct_0(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f15])).
% 0.20/0.50  fof(f70,plain,(
% 0.20/0.50    ~spl4_1),
% 0.20/0.50    inference(avatar_split_clause,[],[f38,f68])).
% 0.20/0.50  fof(f38,plain,(
% 0.20/0.50    ~v2_struct_0(sK1)),
% 0.20/0.50    inference(cnf_transformation,[],[f15])).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (29672)------------------------------
% 0.20/0.50  % (29672)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (29672)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (29672)Memory used [KB]: 6396
% 0.20/0.50  % (29672)Time elapsed: 0.069 s
% 0.20/0.50  % (29672)------------------------------
% 0.20/0.50  % (29672)------------------------------
% 0.20/0.50  % (29671)Success in time 0.14 s
%------------------------------------------------------------------------------
