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
% DateTime   : Thu Dec  3 13:19:26 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 265 expanded)
%              Number of leaves         :   25 ( 115 expanded)
%              Depth                    :   12
%              Number of atoms          :  491 (1096 expanded)
%              Number of equality atoms :   53 ( 152 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f402,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f68,f69,f74,f79,f84,f89,f104,f145,f164,f262,f293,f381,f385,f394,f400,f401])).

fof(f401,plain,
    ( u1_pre_topc(sK2) != k5_tmap_1(sK2,sK3)
    | k6_tmap_1(sK2,sK3) != g1_pre_topc(u1_struct_0(sK2),k5_tmap_1(sK2,sK3))
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k6_tmap_1(sK2,sK3) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f400,plain,
    ( ~ spl4_11
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | spl4_6
    | spl4_21 ),
    inference(avatar_split_clause,[],[f356,f352,f86,f81,f76,f71,f139])).

fof(f139,plain,
    ( spl4_11
  <=> r2_hidden(sK3,u1_pre_topc(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f71,plain,
    ( spl4_3
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f76,plain,
    ( spl4_4
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f81,plain,
    ( spl4_5
  <=> v2_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f86,plain,
    ( spl4_6
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f352,plain,
    ( spl4_21
  <=> u1_pre_topc(sK2) = k5_tmap_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f356,plain,
    ( ~ r2_hidden(sK3,u1_pre_topc(sK2))
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | spl4_6
    | spl4_21 ),
    inference(unit_resulting_resolution,[],[f88,f83,f78,f73,f354,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( u1_pre_topc(X0) = k5_tmap_1(X0,X1)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r2_hidden(X1,u1_pre_topc(X0))
              | u1_pre_topc(X0) != k5_tmap_1(X0,X1) )
            & ( u1_pre_topc(X0) = k5_tmap_1(X0,X1)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_tmap_1)).

fof(f354,plain,
    ( u1_pre_topc(sK2) != k5_tmap_1(sK2,sK3)
    | spl4_21 ),
    inference(avatar_component_clause,[],[f352])).

fof(f73,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f71])).

fof(f78,plain,
    ( l1_pre_topc(sK2)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f76])).

fof(f83,plain,
    ( v2_pre_topc(sK2)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f81])).

fof(f88,plain,
    ( ~ v2_struct_0(sK2)
    | spl4_6 ),
    inference(avatar_component_clause,[],[f86])).

fof(f394,plain,
    ( spl4_11
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f393,f76,f71,f61,f139])).

fof(f61,plain,
    ( spl4_1
  <=> v3_pre_topc(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f393,plain,
    ( r2_hidden(sK3,u1_pre_topc(sK2))
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f392,f78])).

fof(f392,plain,
    ( r2_hidden(sK3,u1_pre_topc(sK2))
    | ~ l1_pre_topc(sK2)
    | ~ spl4_1
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f115,f62])).

fof(f62,plain,
    ( v3_pre_topc(sK3,sK2)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f61])).

fof(f115,plain,
    ( ~ v3_pre_topc(sK3,sK2)
    | r2_hidden(sK3,u1_pre_topc(sK2))
    | ~ l1_pre_topc(sK2)
    | ~ spl4_3 ),
    inference(resolution,[],[f43,f73])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | r2_hidden(X1,u1_pre_topc(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

fof(f385,plain,
    ( spl4_18
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | spl4_6
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f384,f161,f86,f81,f76,f71,f290])).

fof(f290,plain,
    ( spl4_18
  <=> v3_pre_topc(sK3,k6_tmap_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f161,plain,
    ( spl4_12
  <=> u1_struct_0(sK2) = u1_struct_0(k6_tmap_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f384,plain,
    ( v3_pre_topc(sK3,k6_tmap_1(sK2,sK3))
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | spl4_6
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f383,f88])).

fof(f383,plain,
    ( v3_pre_topc(sK3,k6_tmap_1(sK2,sK3))
    | v2_struct_0(sK2)
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f382,f83])).

fof(f382,plain,
    ( v3_pre_topc(sK3,k6_tmap_1(sK2,sK3))
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f368,f78])).

fof(f368,plain,
    ( v3_pre_topc(sK3,k6_tmap_1(sK2,sK3))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl4_3
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f363,f73])).

fof(f363,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | v3_pre_topc(sK3,k6_tmap_1(sK2,sK3))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl4_12 ),
    inference(duplicate_literal_removal,[],[f362])).

fof(f362,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | v3_pre_topc(sK3,k6_tmap_1(sK2,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl4_12 ),
    inference(superposition,[],[f59,f163])).

fof(f163,plain,
    ( u1_struct_0(sK2) = u1_struct_0(k6_tmap_1(sK2,sK3))
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f161])).

fof(f59,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X2))))
      | v3_pre_topc(X2,k6_tmap_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(X2,k6_tmap_1(X0,X1))
      | X1 != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v3_pre_topc(X2,k6_tmap_1(X0,X1))
              | X1 != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v3_pre_topc(X2,k6_tmap_1(X0,X1))
              | X1 != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1)))) )
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
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1))))
             => ( X1 = X2
               => v3_pre_topc(X2,k6_tmap_1(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_tmap_1)).

fof(f381,plain,
    ( ~ spl4_7
    | ~ spl4_4
    | spl4_11 ),
    inference(avatar_split_clause,[],[f146,f139,f76,f92])).

fof(f92,plain,
    ( spl4_7
  <=> sP0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f146,plain,
    ( ~ sP0(sK2,sK3)
    | ~ spl4_4
    | spl4_11 ),
    inference(unit_resulting_resolution,[],[f78,f141,f119])).

fof(f119,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,u1_pre_topc(X1))
      | ~ l1_pre_topc(X1)
      | ~ sP0(X1,X0) ) ),
    inference(subsumption_resolution,[],[f116,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v3_pre_topc(X1,X0) )
      & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v3_pre_topc(X1,X0) )
        | ~ sP0(X0,X1) ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v3_pre_topc(X1,X0) )
      & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v3_pre_topc(X1,X0) )
        | ~ sP0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
    <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v3_pre_topc(X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f116,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(X0,X1)
      | r2_hidden(X0,u1_pre_topc(X1))
      | ~ l1_pre_topc(X1)
      | ~ sP0(X1,X0) ) ),
    inference(resolution,[],[f43,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f141,plain,
    ( ~ r2_hidden(sK3,u1_pre_topc(sK2))
    | spl4_11 ),
    inference(avatar_component_clause,[],[f139])).

fof(f293,plain,
    ( ~ spl4_18
    | ~ spl4_2
    | ~ spl4_3
    | spl4_8
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f287,f161,f101,f71,f65,f290])).

fof(f65,plain,
    ( spl4_2
  <=> g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k6_tmap_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f101,plain,
    ( spl4_8
  <=> sP1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f287,plain,
    ( ~ v3_pre_topc(sK3,k6_tmap_1(sK2,sK3))
    | ~ spl4_2
    | ~ spl4_3
    | spl4_8
    | ~ spl4_12 ),
    inference(unit_resulting_resolution,[],[f103,f73,f250])).

fof(f250,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(X0,k6_tmap_1(sK2,sK3))
        | sP1(sK2,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) )
    | ~ spl4_2
    | ~ spl4_12 ),
    inference(forward_demodulation,[],[f244,f163])).

fof(f244,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK2,sK3))))
        | sP1(sK2,X0)
        | ~ v3_pre_topc(X0,k6_tmap_1(sK2,sK3)) )
    | ~ spl4_2 ),
    inference(superposition,[],[f53,f66])).

fof(f66,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k6_tmap_1(sK2,sK3)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f65])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
      | sP1(X0,X1)
      | ~ v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
        | ~ v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
          & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
        | ~ sP1(X0,X1) ) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
        | ~ v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
          & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
        | ~ sP1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
    <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
        & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f103,plain,
    ( ~ sP1(sK2,sK3)
    | spl4_8 ),
    inference(avatar_component_clause,[],[f101])).

fof(f262,plain,
    ( spl4_17
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | spl4_6 ),
    inference(avatar_split_clause,[],[f251,f86,f81,f76,f71,f259])).

fof(f259,plain,
    ( spl4_17
  <=> k6_tmap_1(sK2,sK3) = g1_pre_topc(u1_struct_0(sK2),k5_tmap_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f251,plain,
    ( k6_tmap_1(sK2,sK3) = g1_pre_topc(u1_struct_0(sK2),k5_tmap_1(sK2,sK3))
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | spl4_6 ),
    inference(unit_resulting_resolution,[],[f88,f83,f78,f73,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_tmap_1)).

fof(f164,plain,
    ( spl4_12
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | spl4_6 ),
    inference(avatar_split_clause,[],[f150,f86,f81,f76,f71,f161])).

fof(f150,plain,
    ( u1_struct_0(sK2) = u1_struct_0(k6_tmap_1(sK2,sK3))
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | spl4_6 ),
    inference(unit_resulting_resolution,[],[f88,f83,f78,f73,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_tmap_1)).

fof(f145,plain,
    ( ~ spl4_11
    | spl4_1
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f144,f76,f71,f61,f139])).

fof(f144,plain,
    ( ~ r2_hidden(sK3,u1_pre_topc(sK2))
    | spl4_1
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f143,f78])).

fof(f143,plain,
    ( ~ r2_hidden(sK3,u1_pre_topc(sK2))
    | ~ l1_pre_topc(sK2)
    | spl4_1
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f134,f63])).

fof(f63,plain,
    ( ~ v3_pre_topc(sK3,sK2)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f61])).

fof(f134,plain,
    ( ~ r2_hidden(sK3,u1_pre_topc(sK2))
    | v3_pre_topc(sK3,sK2)
    | ~ l1_pre_topc(sK2)
    | ~ spl4_3 ),
    inference(resolution,[],[f44,f73])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f104,plain,
    ( ~ spl4_8
    | ~ spl4_4
    | ~ spl4_5
    | spl4_7 ),
    inference(avatar_split_clause,[],[f97,f92,f81,f76,f101])).

fof(f97,plain,
    ( ~ sP1(sK2,sK3)
    | ~ spl4_4
    | ~ spl4_5
    | spl4_7 ),
    inference(unit_resulting_resolution,[],[f83,f78,f94,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | sP0(X0,X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( sP0(X0,X1)
            | ~ sP1(X0,X1) )
          & ( sP1(X0,X1)
            | ~ sP0(X0,X1) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP0(X0,X1)
        <=> sP1(X0,X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(definition_folding,[],[f21,f23,f22])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v3_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v3_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v3_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_pre_topc)).

fof(f94,plain,
    ( ~ sP0(sK2,sK3)
    | spl4_7 ),
    inference(avatar_component_clause,[],[f92])).

fof(f89,plain,(
    ~ spl4_6 ),
    inference(avatar_split_clause,[],[f37,f86])).

fof(f37,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k6_tmap_1(sK2,sK3)
      | ~ v3_pre_topc(sK3,sK2) )
    & ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k6_tmap_1(sK2,sK3)
      | v3_pre_topc(sK3,sK2) )
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f26,f28,f27])).

fof(f27,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1)
              | ~ v3_pre_topc(X1,X0) )
            & ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)
              | v3_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k6_tmap_1(sK2,X1)
            | ~ v3_pre_topc(X1,sK2) )
          & ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k6_tmap_1(sK2,X1)
            | v3_pre_topc(X1,sK2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X1] :
        ( ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k6_tmap_1(sK2,X1)
          | ~ v3_pre_topc(X1,sK2) )
        & ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k6_tmap_1(sK2,X1)
          | v3_pre_topc(X1,sK2) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
   => ( ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k6_tmap_1(sK2,sK3)
        | ~ v3_pre_topc(sK3,sK2) )
      & ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k6_tmap_1(sK2,sK3)
        | v3_pre_topc(sK3,sK2) )
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
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
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_tmap_1)).

fof(f84,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f38,f81])).

fof(f38,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f79,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f39,f76])).

fof(f39,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f74,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f40,f71])).

fof(f40,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f29])).

fof(f69,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f41,f65,f61])).

fof(f41,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k6_tmap_1(sK2,sK3)
    | v3_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f68,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f42,f65,f61])).

fof(f42,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k6_tmap_1(sK2,sK3)
    | ~ v3_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:51:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.44  % (5196)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.46  % (5187)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.46  % (5191)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.46  % (5196)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.47  % (5193)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.47  % (5184)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f402,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(avatar_sat_refutation,[],[f68,f69,f74,f79,f84,f89,f104,f145,f164,f262,f293,f381,f385,f394,f400,f401])).
% 0.20/0.47  fof(f401,plain,(
% 0.20/0.47    u1_pre_topc(sK2) != k5_tmap_1(sK2,sK3) | k6_tmap_1(sK2,sK3) != g1_pre_topc(u1_struct_0(sK2),k5_tmap_1(sK2,sK3)) | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k6_tmap_1(sK2,sK3)),
% 0.20/0.47    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.47  fof(f400,plain,(
% 0.20/0.47    ~spl4_11 | ~spl4_3 | ~spl4_4 | ~spl4_5 | spl4_6 | spl4_21),
% 0.20/0.47    inference(avatar_split_clause,[],[f356,f352,f86,f81,f76,f71,f139])).
% 0.20/0.47  fof(f139,plain,(
% 0.20/0.47    spl4_11 <=> r2_hidden(sK3,u1_pre_topc(sK2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.20/0.47  fof(f71,plain,(
% 0.20/0.47    spl4_3 <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.47  fof(f76,plain,(
% 0.20/0.47    spl4_4 <=> l1_pre_topc(sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.47  fof(f81,plain,(
% 0.20/0.47    spl4_5 <=> v2_pre_topc(sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.47  fof(f86,plain,(
% 0.20/0.47    spl4_6 <=> v2_struct_0(sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.47  fof(f352,plain,(
% 0.20/0.47    spl4_21 <=> u1_pre_topc(sK2) = k5_tmap_1(sK2,sK3)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.20/0.47  fof(f356,plain,(
% 0.20/0.47    ~r2_hidden(sK3,u1_pre_topc(sK2)) | (~spl4_3 | ~spl4_4 | ~spl4_5 | spl4_6 | spl4_21)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f88,f83,f78,f73,f354,f48])).
% 0.20/0.47  fof(f48,plain,(
% 0.20/0.47    ( ! [X0,X1] : (u1_pre_topc(X0) = k5_tmap_1(X0,X1) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f31])).
% 0.20/0.47  fof(f31,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (((r2_hidden(X1,u1_pre_topc(X0)) | u1_pre_topc(X0) != k5_tmap_1(X0,X1)) & (u1_pre_topc(X0) = k5_tmap_1(X0,X1) | ~r2_hidden(X1,u1_pre_topc(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.47    inference(nnf_transformation,[],[f17])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : ((r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.47    inference(flattening,[],[f16])).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : ((r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,axiom,(
% 0.20/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_tmap_1)).
% 0.20/0.47  fof(f354,plain,(
% 0.20/0.47    u1_pre_topc(sK2) != k5_tmap_1(sK2,sK3) | spl4_21),
% 0.20/0.47    inference(avatar_component_clause,[],[f352])).
% 0.20/0.47  fof(f73,plain,(
% 0.20/0.47    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) | ~spl4_3),
% 0.20/0.47    inference(avatar_component_clause,[],[f71])).
% 0.20/0.47  fof(f78,plain,(
% 0.20/0.47    l1_pre_topc(sK2) | ~spl4_4),
% 0.20/0.47    inference(avatar_component_clause,[],[f76])).
% 0.20/0.47  fof(f83,plain,(
% 0.20/0.47    v2_pre_topc(sK2) | ~spl4_5),
% 0.20/0.47    inference(avatar_component_clause,[],[f81])).
% 0.20/0.47  fof(f88,plain,(
% 0.20/0.47    ~v2_struct_0(sK2) | spl4_6),
% 0.20/0.47    inference(avatar_component_clause,[],[f86])).
% 0.20/0.47  fof(f394,plain,(
% 0.20/0.47    spl4_11 | ~spl4_1 | ~spl4_3 | ~spl4_4),
% 0.20/0.47    inference(avatar_split_clause,[],[f393,f76,f71,f61,f139])).
% 0.20/0.47  fof(f61,plain,(
% 0.20/0.47    spl4_1 <=> v3_pre_topc(sK3,sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.47  fof(f393,plain,(
% 0.20/0.47    r2_hidden(sK3,u1_pre_topc(sK2)) | (~spl4_1 | ~spl4_3 | ~spl4_4)),
% 0.20/0.47    inference(subsumption_resolution,[],[f392,f78])).
% 0.20/0.47  fof(f392,plain,(
% 0.20/0.47    r2_hidden(sK3,u1_pre_topc(sK2)) | ~l1_pre_topc(sK2) | (~spl4_1 | ~spl4_3)),
% 0.20/0.47    inference(subsumption_resolution,[],[f115,f62])).
% 0.20/0.47  fof(f62,plain,(
% 0.20/0.47    v3_pre_topc(sK3,sK2) | ~spl4_1),
% 0.20/0.47    inference(avatar_component_clause,[],[f61])).
% 0.20/0.47  fof(f115,plain,(
% 0.20/0.47    ~v3_pre_topc(sK3,sK2) | r2_hidden(sK3,u1_pre_topc(sK2)) | ~l1_pre_topc(sK2) | ~spl4_3),
% 0.20/0.47    inference(resolution,[],[f43,f73])).
% 0.20/0.47  fof(f43,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | r2_hidden(X1,u1_pre_topc(X0)) | ~l1_pre_topc(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f30])).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0))) & (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.47    inference(nnf_transformation,[],[f11])).
% 0.20/0.47  fof(f11,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0)))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).
% 0.20/0.47  fof(f385,plain,(
% 0.20/0.47    spl4_18 | ~spl4_3 | ~spl4_4 | ~spl4_5 | spl4_6 | ~spl4_12),
% 0.20/0.47    inference(avatar_split_clause,[],[f384,f161,f86,f81,f76,f71,f290])).
% 0.20/0.47  fof(f290,plain,(
% 0.20/0.47    spl4_18 <=> v3_pre_topc(sK3,k6_tmap_1(sK2,sK3))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.20/0.47  fof(f161,plain,(
% 0.20/0.47    spl4_12 <=> u1_struct_0(sK2) = u1_struct_0(k6_tmap_1(sK2,sK3))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.20/0.47  fof(f384,plain,(
% 0.20/0.47    v3_pre_topc(sK3,k6_tmap_1(sK2,sK3)) | (~spl4_3 | ~spl4_4 | ~spl4_5 | spl4_6 | ~spl4_12)),
% 0.20/0.47    inference(subsumption_resolution,[],[f383,f88])).
% 0.20/0.47  fof(f383,plain,(
% 0.20/0.47    v3_pre_topc(sK3,k6_tmap_1(sK2,sK3)) | v2_struct_0(sK2) | (~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_12)),
% 0.20/0.47    inference(subsumption_resolution,[],[f382,f83])).
% 0.20/0.47  fof(f382,plain,(
% 0.20/0.47    v3_pre_topc(sK3,k6_tmap_1(sK2,sK3)) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl4_3 | ~spl4_4 | ~spl4_12)),
% 0.20/0.47    inference(subsumption_resolution,[],[f368,f78])).
% 0.20/0.47  fof(f368,plain,(
% 0.20/0.47    v3_pre_topc(sK3,k6_tmap_1(sK2,sK3)) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl4_3 | ~spl4_12)),
% 0.20/0.47    inference(subsumption_resolution,[],[f363,f73])).
% 0.20/0.47  fof(f363,plain,(
% 0.20/0.47    ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) | v3_pre_topc(sK3,k6_tmap_1(sK2,sK3)) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~spl4_12),
% 0.20/0.47    inference(duplicate_literal_removal,[],[f362])).
% 0.20/0.47  fof(f362,plain,(
% 0.20/0.47    ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) | v3_pre_topc(sK3,k6_tmap_1(sK2,sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~spl4_12),
% 0.20/0.47    inference(superposition,[],[f59,f163])).
% 0.20/0.47  fof(f163,plain,(
% 0.20/0.47    u1_struct_0(sK2) = u1_struct_0(k6_tmap_1(sK2,sK3)) | ~spl4_12),
% 0.20/0.47    inference(avatar_component_clause,[],[f161])).
% 0.20/0.47  fof(f59,plain,(
% 0.20/0.47    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X2)))) | v3_pre_topc(X2,k6_tmap_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.47    inference(equality_resolution,[],[f50])).
% 0.20/0.47  fof(f50,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (v3_pre_topc(X2,k6_tmap_1(X0,X1)) | X1 != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f19])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (! [X2] : (v3_pre_topc(X2,k6_tmap_1(X0,X1)) | X1 != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.47    inference(flattening,[],[f18])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (! [X2] : ((v3_pre_topc(X2,k6_tmap_1(X0,X1)) | X1 != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f6])).
% 0.20/0.47  fof(f6,axiom,(
% 0.20/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1)))) => (X1 = X2 => v3_pre_topc(X2,k6_tmap_1(X0,X1))))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_tmap_1)).
% 0.20/0.47  fof(f381,plain,(
% 0.20/0.47    ~spl4_7 | ~spl4_4 | spl4_11),
% 0.20/0.47    inference(avatar_split_clause,[],[f146,f139,f76,f92])).
% 0.20/0.47  fof(f92,plain,(
% 0.20/0.47    spl4_7 <=> sP0(sK2,sK3)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.20/0.47  fof(f146,plain,(
% 0.20/0.47    ~sP0(sK2,sK3) | (~spl4_4 | spl4_11)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f78,f141,f119])).
% 0.20/0.47  fof(f119,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r2_hidden(X0,u1_pre_topc(X1)) | ~l1_pre_topc(X1) | ~sP0(X1,X0)) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f116,f54])).
% 0.20/0.47  fof(f54,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~sP0(X0,X1) | v3_pre_topc(X1,X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f35])).
% 0.20/0.47  fof(f35,plain,(
% 0.20/0.47    ! [X0,X1] : ((sP0(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0)) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) | ~sP0(X0,X1)))),
% 0.20/0.47    inference(flattening,[],[f34])).
% 0.20/0.47  fof(f34,plain,(
% 0.20/0.47    ! [X0,X1] : ((sP0(X0,X1) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0))) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) | ~sP0(X0,X1)))),
% 0.20/0.47    inference(nnf_transformation,[],[f22])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    ! [X0,X1] : (sP0(X0,X1) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)))),
% 0.20/0.47    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.47  fof(f116,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~v3_pre_topc(X0,X1) | r2_hidden(X0,u1_pre_topc(X1)) | ~l1_pre_topc(X1) | ~sP0(X1,X0)) )),
% 0.20/0.47    inference(resolution,[],[f43,f55])).
% 0.20/0.47  fof(f55,plain,(
% 0.20/0.47    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~sP0(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f35])).
% 0.20/0.47  fof(f141,plain,(
% 0.20/0.47    ~r2_hidden(sK3,u1_pre_topc(sK2)) | spl4_11),
% 0.20/0.47    inference(avatar_component_clause,[],[f139])).
% 0.20/0.47  fof(f293,plain,(
% 0.20/0.47    ~spl4_18 | ~spl4_2 | ~spl4_3 | spl4_8 | ~spl4_12),
% 0.20/0.47    inference(avatar_split_clause,[],[f287,f161,f101,f71,f65,f290])).
% 0.20/0.47  fof(f65,plain,(
% 0.20/0.47    spl4_2 <=> g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k6_tmap_1(sK2,sK3)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.47  fof(f101,plain,(
% 0.20/0.47    spl4_8 <=> sP1(sK2,sK3)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.20/0.47  fof(f287,plain,(
% 0.20/0.47    ~v3_pre_topc(sK3,k6_tmap_1(sK2,sK3)) | (~spl4_2 | ~spl4_3 | spl4_8 | ~spl4_12)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f103,f73,f250])).
% 0.20/0.47  fof(f250,plain,(
% 0.20/0.47    ( ! [X0] : (~v3_pre_topc(X0,k6_tmap_1(sK2,sK3)) | sP1(sK2,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))) ) | (~spl4_2 | ~spl4_12)),
% 0.20/0.47    inference(forward_demodulation,[],[f244,f163])).
% 0.20/0.47  fof(f244,plain,(
% 0.20/0.47    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK2,sK3)))) | sP1(sK2,X0) | ~v3_pre_topc(X0,k6_tmap_1(sK2,sK3))) ) | ~spl4_2),
% 0.20/0.47    inference(superposition,[],[f53,f66])).
% 0.20/0.47  fof(f66,plain,(
% 0.20/0.47    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k6_tmap_1(sK2,sK3) | ~spl4_2),
% 0.20/0.47    inference(avatar_component_clause,[],[f65])).
% 0.20/0.47  fof(f53,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | sP1(X0,X1) | ~v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f33])).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    ! [X0,X1] : ((sP1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~sP1(X0,X1)))),
% 0.20/0.47    inference(flattening,[],[f32])).
% 0.20/0.47  fof(f32,plain,(
% 0.20/0.47    ! [X0,X1] : ((sP1(X0,X1) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~sP1(X0,X1)))),
% 0.20/0.47    inference(nnf_transformation,[],[f23])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    ! [X0,X1] : (sP1(X0,X1) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 0.20/0.47    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.20/0.47  fof(f103,plain,(
% 0.20/0.47    ~sP1(sK2,sK3) | spl4_8),
% 0.20/0.47    inference(avatar_component_clause,[],[f101])).
% 0.20/0.47  fof(f262,plain,(
% 0.20/0.47    spl4_17 | ~spl4_3 | ~spl4_4 | ~spl4_5 | spl4_6),
% 0.20/0.47    inference(avatar_split_clause,[],[f251,f86,f81,f76,f71,f259])).
% 0.20/0.47  fof(f259,plain,(
% 0.20/0.47    spl4_17 <=> k6_tmap_1(sK2,sK3) = g1_pre_topc(u1_struct_0(sK2),k5_tmap_1(sK2,sK3))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.20/0.47  fof(f251,plain,(
% 0.20/0.47    k6_tmap_1(sK2,sK3) = g1_pre_topc(u1_struct_0(sK2),k5_tmap_1(sK2,sK3)) | (~spl4_3 | ~spl4_4 | ~spl4_5 | spl4_6)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f88,f83,f78,f73,f45])).
% 0.20/0.47  fof(f45,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f13])).
% 0.20/0.47  fof(f13,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.47    inference(flattening,[],[f12])).
% 0.20/0.47  fof(f12,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_tmap_1)).
% 0.20/0.47  fof(f164,plain,(
% 0.20/0.47    spl4_12 | ~spl4_3 | ~spl4_4 | ~spl4_5 | spl4_6),
% 0.20/0.47    inference(avatar_split_clause,[],[f150,f86,f81,f76,f71,f161])).
% 0.20/0.47  fof(f150,plain,(
% 0.20/0.47    u1_struct_0(sK2) = u1_struct_0(k6_tmap_1(sK2,sK3)) | (~spl4_3 | ~spl4_4 | ~spl4_5 | spl4_6)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f88,f83,f78,f73,f46])).
% 0.20/0.47  fof(f46,plain,(
% 0.20/0.47    ( ! [X0,X1] : (u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f15])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : ((k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1)) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.47    inference(flattening,[],[f14])).
% 0.20/0.47  fof(f14,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : ((k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1)) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f5])).
% 0.20/0.47  fof(f5,axiom,(
% 0.20/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1)) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_tmap_1)).
% 0.20/0.47  fof(f145,plain,(
% 0.20/0.47    ~spl4_11 | spl4_1 | ~spl4_3 | ~spl4_4),
% 0.20/0.47    inference(avatar_split_clause,[],[f144,f76,f71,f61,f139])).
% 0.20/0.47  fof(f144,plain,(
% 0.20/0.47    ~r2_hidden(sK3,u1_pre_topc(sK2)) | (spl4_1 | ~spl4_3 | ~spl4_4)),
% 0.20/0.47    inference(subsumption_resolution,[],[f143,f78])).
% 0.20/0.47  fof(f143,plain,(
% 0.20/0.47    ~r2_hidden(sK3,u1_pre_topc(sK2)) | ~l1_pre_topc(sK2) | (spl4_1 | ~spl4_3)),
% 0.20/0.47    inference(subsumption_resolution,[],[f134,f63])).
% 0.20/0.47  fof(f63,plain,(
% 0.20/0.47    ~v3_pre_topc(sK3,sK2) | spl4_1),
% 0.20/0.47    inference(avatar_component_clause,[],[f61])).
% 0.20/0.47  fof(f134,plain,(
% 0.20/0.47    ~r2_hidden(sK3,u1_pre_topc(sK2)) | v3_pre_topc(sK3,sK2) | ~l1_pre_topc(sK2) | ~spl4_3),
% 0.20/0.47    inference(resolution,[],[f44,f73])).
% 0.20/0.47  fof(f44,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X1,u1_pre_topc(X0)) | v3_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f30])).
% 0.20/0.47  fof(f104,plain,(
% 0.20/0.47    ~spl4_8 | ~spl4_4 | ~spl4_5 | spl4_7),
% 0.20/0.47    inference(avatar_split_clause,[],[f97,f92,f81,f76,f101])).
% 0.20/0.47  fof(f97,plain,(
% 0.20/0.47    ~sP1(sK2,sK3) | (~spl4_4 | ~spl4_5 | spl4_7)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f83,f78,f94,f58])).
% 0.20/0.47  fof(f58,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~sP1(X0,X1) | sP0(X0,X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f36])).
% 0.20/0.47  fof(f36,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : ((sP0(X0,X1) | ~sP1(X0,X1)) & (sP1(X0,X1) | ~sP0(X0,X1))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.47    inference(nnf_transformation,[],[f24])).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (sP0(X0,X1) <=> sP1(X0,X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.47    inference(definition_folding,[],[f21,f23,f22])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.47    inference(flattening,[],[f20])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_pre_topc)).
% 0.20/0.47  fof(f94,plain,(
% 0.20/0.47    ~sP0(sK2,sK3) | spl4_7),
% 0.20/0.47    inference(avatar_component_clause,[],[f92])).
% 0.20/0.47  fof(f89,plain,(
% 0.20/0.47    ~spl4_6),
% 0.20/0.47    inference(avatar_split_clause,[],[f37,f86])).
% 0.20/0.47  fof(f37,plain,(
% 0.20/0.47    ~v2_struct_0(sK2)),
% 0.20/0.47    inference(cnf_transformation,[],[f29])).
% 0.20/0.47  fof(f29,plain,(
% 0.20/0.47    ((g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k6_tmap_1(sK2,sK3) | ~v3_pre_topc(sK3,sK2)) & (g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k6_tmap_1(sK2,sK3) | v3_pre_topc(sK3,sK2)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f26,f28,f27])).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1) | ~v3_pre_topc(X1,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k6_tmap_1(sK2,X1) | ~v3_pre_topc(X1,sK2)) & (g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k6_tmap_1(sK2,X1) | v3_pre_topc(X1,sK2)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    ? [X1] : ((g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k6_tmap_1(sK2,X1) | ~v3_pre_topc(X1,sK2)) & (g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k6_tmap_1(sK2,X1) | v3_pre_topc(X1,sK2)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) => ((g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k6_tmap_1(sK2,sK3) | ~v3_pre_topc(sK3,sK2)) & (g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k6_tmap_1(sK2,sK3) | v3_pre_topc(sK3,sK2)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1) | ~v3_pre_topc(X1,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.47    inference(flattening,[],[f25])).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : (((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1) | ~v3_pre_topc(X1,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.47    inference(nnf_transformation,[],[f10])).
% 0.20/0.47  fof(f10,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.47    inference(flattening,[],[f9])).
% 0.20/0.47  fof(f9,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f8])).
% 0.20/0.47  fof(f8,negated_conjecture,(
% 0.20/0.47    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1))))),
% 0.20/0.47    inference(negated_conjecture,[],[f7])).
% 0.20/0.47  fof(f7,conjecture,(
% 0.20/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_tmap_1)).
% 0.20/0.47  fof(f84,plain,(
% 0.20/0.47    spl4_5),
% 0.20/0.47    inference(avatar_split_clause,[],[f38,f81])).
% 0.20/0.47  fof(f38,plain,(
% 0.20/0.47    v2_pre_topc(sK2)),
% 0.20/0.47    inference(cnf_transformation,[],[f29])).
% 0.20/0.47  fof(f79,plain,(
% 0.20/0.47    spl4_4),
% 0.20/0.47    inference(avatar_split_clause,[],[f39,f76])).
% 0.20/0.47  fof(f39,plain,(
% 0.20/0.47    l1_pre_topc(sK2)),
% 0.20/0.47    inference(cnf_transformation,[],[f29])).
% 0.20/0.47  fof(f74,plain,(
% 0.20/0.47    spl4_3),
% 0.20/0.47    inference(avatar_split_clause,[],[f40,f71])).
% 0.20/0.47  fof(f40,plain,(
% 0.20/0.47    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.20/0.47    inference(cnf_transformation,[],[f29])).
% 0.20/0.47  fof(f69,plain,(
% 0.20/0.47    spl4_1 | spl4_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f41,f65,f61])).
% 0.20/0.47  fof(f41,plain,(
% 0.20/0.47    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k6_tmap_1(sK2,sK3) | v3_pre_topc(sK3,sK2)),
% 0.20/0.47    inference(cnf_transformation,[],[f29])).
% 0.20/0.47  fof(f68,plain,(
% 0.20/0.47    ~spl4_1 | ~spl4_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f42,f65,f61])).
% 0.20/0.47  fof(f42,plain,(
% 0.20/0.47    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != k6_tmap_1(sK2,sK3) | ~v3_pre_topc(sK3,sK2)),
% 0.20/0.47    inference(cnf_transformation,[],[f29])).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (5196)------------------------------
% 0.20/0.47  % (5196)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (5196)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (5196)Memory used [KB]: 10874
% 0.20/0.47  % (5196)Time elapsed: 0.068 s
% 0.20/0.47  % (5196)------------------------------
% 0.20/0.47  % (5196)------------------------------
% 0.20/0.47  % (5179)Success in time 0.118 s
%------------------------------------------------------------------------------
