%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:13 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 231 expanded)
%              Number of leaves         :   34 ( 105 expanded)
%              Depth                    :    8
%              Number of atoms          :  471 ( 791 expanded)
%              Number of equality atoms :   45 (  78 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f262,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f48,f56,f60,f64,f72,f76,f80,f88,f93,f105,f110,f118,f124,f131,f135,f140,f144,f149,f163,f173,f188,f204,f212,f226,f249,f261])).

fof(f261,plain,
    ( ~ spl4_3
    | ~ spl4_4
    | ~ spl4_7
    | ~ spl4_10
    | ~ spl4_20
    | spl4_39 ),
    inference(avatar_contradiction_clause,[],[f260])).

fof(f260,plain,
    ( $false
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_7
    | ~ spl4_10
    | ~ spl4_20
    | spl4_39 ),
    inference(subsumption_resolution,[],[f259,f55])).

fof(f55,plain,
    ( v2_pre_topc(sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl4_3
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f259,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ spl4_4
    | ~ spl4_7
    | ~ spl4_10
    | ~ spl4_20
    | spl4_39 ),
    inference(subsumption_resolution,[],[f258,f87])).

fof(f87,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl4_10
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f258,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v2_pre_topc(sK0)
    | ~ spl4_4
    | ~ spl4_7
    | ~ spl4_20
    | spl4_39 ),
    inference(subsumption_resolution,[],[f257,f71])).

fof(f71,plain,
    ( ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl4_7
  <=> ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f257,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_xboole_0(k1_xboole_0)
    | ~ v2_pre_topc(sK0)
    | ~ spl4_4
    | ~ spl4_20
    | spl4_39 ),
    inference(subsumption_resolution,[],[f255,f59])).

fof(f59,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl4_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f255,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_xboole_0(k1_xboole_0)
    | ~ v2_pre_topc(sK0)
    | ~ spl4_20
    | spl4_39 ),
    inference(resolution,[],[f248,f134])).

fof(f134,plain,
    ( ! [X0,X1] :
        ( v4_pre_topc(X1,X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v1_xboole_0(X1)
        | ~ v2_pre_topc(X0) )
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl4_20
  <=> ! [X1,X0] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v1_xboole_0(X1)
        | v4_pre_topc(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f248,plain,
    ( ~ v4_pre_topc(k1_xboole_0,sK0)
    | spl4_39 ),
    inference(avatar_component_clause,[],[f247])).

fof(f247,plain,
    ( spl4_39
  <=> v4_pre_topc(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f249,plain,
    ( ~ spl4_39
    | ~ spl4_7
    | ~ spl4_35
    | ~ spl4_37 ),
    inference(avatar_split_clause,[],[f236,f224,f210,f70,f247])).

fof(f210,plain,
    ( spl4_35
  <=> ! [X0] :
        ( k1_xboole_0 != k3_xboole_0(k1_xboole_0,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f224,plain,
    ( spl4_37
  <=> ! [X2] : k1_xboole_0 = k3_xboole_0(X2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f236,plain,
    ( ~ v4_pre_topc(k1_xboole_0,sK0)
    | ~ spl4_7
    | ~ spl4_35
    | ~ spl4_37 ),
    inference(subsumption_resolution,[],[f235,f71])).

fof(f235,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_pre_topc(k1_xboole_0,sK0)
    | ~ spl4_35
    | ~ spl4_37 ),
    inference(trivial_inequality_removal,[],[f234])).

fof(f234,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_pre_topc(k1_xboole_0,sK0)
    | ~ spl4_35
    | ~ spl4_37 ),
    inference(superposition,[],[f211,f225])).

fof(f225,plain,
    ( ! [X2] : k1_xboole_0 = k3_xboole_0(X2,k1_xboole_0)
    | ~ spl4_37 ),
    inference(avatar_component_clause,[],[f224])).

fof(f211,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k3_xboole_0(k1_xboole_0,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_pre_topc(X0,sK0) )
    | ~ spl4_35 ),
    inference(avatar_component_clause,[],[f210])).

fof(f226,plain,
    ( spl4_37
    | ~ spl4_7
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f216,f142,f70,f224])).

fof(f142,plain,
    ( spl4_22
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = k3_xboole_0(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f216,plain,
    ( ! [X2] : k1_xboole_0 = k3_xboole_0(X2,k1_xboole_0)
    | ~ spl4_7
    | ~ spl4_22 ),
    inference(resolution,[],[f143,f71])).

fof(f143,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = k3_xboole_0(X1,X0) )
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f142])).

fof(f212,plain,
    ( spl4_35
    | ~ spl4_4
    | ~ spl4_7
    | spl4_11
    | ~ spl4_31
    | ~ spl4_34 ),
    inference(avatar_split_clause,[],[f208,f202,f186,f91,f70,f58,f210])).

fof(f91,plain,
    ( spl4_11
  <=> v2_tex_2(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f186,plain,
    ( spl4_31
  <=> k1_xboole_0 = sK2(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f202,plain,
    ( spl4_34
  <=> ! [X1,X0,X2] :
        ( k3_xboole_0(X1,X2) != sK2(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v4_pre_topc(X2,X0)
        | ~ l1_pre_topc(X0)
        | v2_tex_2(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f208,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k3_xboole_0(k1_xboole_0,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_pre_topc(X0,sK0) )
    | ~ spl4_4
    | ~ spl4_7
    | spl4_11
    | ~ spl4_31
    | ~ spl4_34 ),
    inference(subsumption_resolution,[],[f207,f92])).

fof(f92,plain,
    ( ~ v2_tex_2(k1_xboole_0,sK0)
    | spl4_11 ),
    inference(avatar_component_clause,[],[f91])).

fof(f207,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k3_xboole_0(k1_xboole_0,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_pre_topc(X0,sK0)
        | v2_tex_2(k1_xboole_0,sK0) )
    | ~ spl4_4
    | ~ spl4_7
    | ~ spl4_31
    | ~ spl4_34 ),
    inference(subsumption_resolution,[],[f206,f59])).

fof(f206,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k3_xboole_0(k1_xboole_0,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_pre_topc(X0,sK0)
        | ~ l1_pre_topc(sK0)
        | v2_tex_2(k1_xboole_0,sK0) )
    | ~ spl4_7
    | ~ spl4_31
    | ~ spl4_34 ),
    inference(subsumption_resolution,[],[f205,f71])).

fof(f205,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k3_xboole_0(k1_xboole_0,X0)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_pre_topc(X0,sK0)
        | ~ l1_pre_topc(sK0)
        | v2_tex_2(k1_xboole_0,sK0) )
    | ~ spl4_31
    | ~ spl4_34 ),
    inference(superposition,[],[f203,f187])).

fof(f187,plain,
    ( k1_xboole_0 = sK2(sK0,k1_xboole_0)
    | ~ spl4_31 ),
    inference(avatar_component_clause,[],[f186])).

fof(f203,plain,
    ( ! [X2,X0,X1] :
        ( k3_xboole_0(X1,X2) != sK2(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v4_pre_topc(X2,X0)
        | ~ l1_pre_topc(X0)
        | v2_tex_2(X1,X0) )
    | ~ spl4_34 ),
    inference(avatar_component_clause,[],[f202])).

fof(f204,plain,
    ( spl4_34
    | ~ spl4_18
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f184,f171,f122,f202])).

fof(f122,plain,
    ( spl4_18
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f171,plain,
    ( spl4_28
  <=> ! [X1,X3,X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v4_pre_topc(X3,X0)
        | k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1)
        | v2_tex_2(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f184,plain,
    ( ! [X2,X0,X1] :
        ( k3_xboole_0(X1,X2) != sK2(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v4_pre_topc(X2,X0)
        | ~ l1_pre_topc(X0)
        | v2_tex_2(X1,X0) )
    | ~ spl4_18
    | ~ spl4_28 ),
    inference(duplicate_literal_removal,[],[f183])).

fof(f183,plain,
    ( ! [X2,X0,X1] :
        ( k3_xboole_0(X1,X2) != sK2(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v4_pre_topc(X2,X0)
        | ~ l1_pre_topc(X0)
        | v2_tex_2(X1,X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
    | ~ spl4_18
    | ~ spl4_28 ),
    inference(superposition,[],[f172,f123])).

fof(f123,plain,
    ( ! [X2,X0,X1] :
        ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f122])).

fof(f172,plain,
    ( ! [X0,X3,X1] :
        ( k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v4_pre_topc(X3,X0)
        | ~ l1_pre_topc(X0)
        | v2_tex_2(X1,X0) )
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f171])).

fof(f188,plain,
    ( spl4_31
    | ~ spl4_9
    | ~ spl4_26 ),
    inference(avatar_split_clause,[],[f168,f161,f78,f186])).

fof(f78,plain,
    ( spl4_9
  <=> ! [X0] :
        ( ~ r1_tarski(X0,k1_xboole_0)
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f161,plain,
    ( spl4_26
  <=> r1_tarski(sK2(sK0,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f168,plain,
    ( k1_xboole_0 = sK2(sK0,k1_xboole_0)
    | ~ spl4_9
    | ~ spl4_26 ),
    inference(resolution,[],[f162,f79])).

fof(f79,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_xboole_0)
        | k1_xboole_0 = X0 )
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f78])).

fof(f162,plain,
    ( r1_tarski(sK2(sK0,k1_xboole_0),k1_xboole_0)
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f161])).

fof(f173,plain,(
    spl4_28 ),
    inference(avatar_split_clause,[],[f32,f171])).

fof(f32,plain,(
    ! [X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X3,X0)
      | k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1)
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v4_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v4_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                            & v4_pre_topc(X3,X0) ) )
                    & r1_tarski(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_tex_2)).

fof(f163,plain,
    ( spl4_26
    | ~ spl4_7
    | spl4_11
    | ~ spl4_23 ),
    inference(avatar_split_clause,[],[f155,f147,f91,f70,f161])).

fof(f147,plain,
    ( spl4_23
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(sK2(sK0,X0),X0)
        | v2_tex_2(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f155,plain,
    ( r1_tarski(sK2(sK0,k1_xboole_0),k1_xboole_0)
    | ~ spl4_7
    | spl4_11
    | ~ spl4_23 ),
    inference(subsumption_resolution,[],[f154,f71])).

fof(f154,plain,
    ( r1_tarski(sK2(sK0,k1_xboole_0),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_11
    | ~ spl4_23 ),
    inference(resolution,[],[f148,f92])).

fof(f148,plain,
    ( ! [X0] :
        ( v2_tex_2(X0,sK0)
        | r1_tarski(sK2(sK0,X0),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f147])).

fof(f149,plain,
    ( spl4_23
    | ~ spl4_4
    | ~ spl4_21 ),
    inference(avatar_split_clause,[],[f145,f138,f58,f147])).

fof(f138,plain,
    ( spl4_21
  <=> ! [X1,X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | r1_tarski(sK2(X0,X1),X1)
        | v2_tex_2(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f145,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(sK2(sK0,X0),X0)
        | v2_tex_2(X0,sK0) )
    | ~ spl4_4
    | ~ spl4_21 ),
    inference(resolution,[],[f139,f59])).

fof(f139,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | r1_tarski(sK2(X0,X1),X1)
        | v2_tex_2(X1,X0) )
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f138])).

fof(f144,plain,
    ( spl4_22
    | ~ spl4_15
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f136,f129,f108,f142])).

fof(f108,plain,
    ( spl4_15
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f129,plain,
    ( spl4_19
  <=> ! [X1,X0,X2] :
        ( m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f136,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = k3_xboole_0(X1,X0) )
    | ~ spl4_15
    | ~ spl4_19 ),
    inference(resolution,[],[f130,f109])).

fof(f109,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = X0 )
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f108])).

fof(f130,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f129])).

fof(f140,plain,(
    spl4_21 ),
    inference(avatar_split_clause,[],[f37,f138])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(sK2(X0,X1),X1)
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f135,plain,(
    spl4_20 ),
    inference(avatar_split_clause,[],[f39,f133])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_xboole_0(X1)
      | v4_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_xboole_0(X1)
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_pre_topc)).

fof(f131,plain,
    ( spl4_19
    | ~ spl4_17
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f127,f122,f116,f129])).

fof(f116,plain,
    ( spl4_17
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f127,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
    | ~ spl4_17
    | ~ spl4_18 ),
    inference(duplicate_literal_removal,[],[f126])).

fof(f126,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
    | ~ spl4_17
    | ~ spl4_18 ),
    inference(superposition,[],[f117,f123])).

fof(f117,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f116])).

fof(f124,plain,(
    spl4_18 ),
    inference(avatar_split_clause,[],[f43,f122])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f118,plain,(
    spl4_17 ),
    inference(avatar_split_clause,[],[f42,f116])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(f110,plain,
    ( spl4_15
    | ~ spl4_9
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f106,f103,f78,f108])).

fof(f103,plain,
    ( spl4_14
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f106,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = X0 )
    | ~ spl4_9
    | ~ spl4_14 ),
    inference(resolution,[],[f104,f79])).

fof(f104,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) )
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f103])).

fof(f105,plain,(
    spl4_14 ),
    inference(avatar_split_clause,[],[f41,f103])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f93,plain,
    ( ~ spl4_11
    | ~ spl4_1
    | spl4_5
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f83,f74,f62,f46,f91])).

fof(f46,plain,
    ( spl4_1
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f62,plain,
    ( spl4_5
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f74,plain,
    ( spl4_8
  <=> ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f83,plain,
    ( ~ v2_tex_2(k1_xboole_0,sK0)
    | ~ spl4_1
    | spl4_5
    | ~ spl4_8 ),
    inference(backward_demodulation,[],[f63,f81])).

fof(f81,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_1
    | ~ spl4_8 ),
    inference(resolution,[],[f75,f47])).

fof(f47,plain,
    ( v1_xboole_0(sK1)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f46])).

fof(f75,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 )
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f74])).

fof(f63,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f62])).

fof(f88,plain,
    ( spl4_10
    | ~ spl4_1
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f84,f74,f46,f86])).

fof(f84,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl4_1
    | ~ spl4_8 ),
    inference(backward_demodulation,[],[f47,f81])).

fof(f80,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f38,f78])).

fof(f38,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f76,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f31,f74])).

fof(f31,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f72,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f30,f70])).

fof(f30,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f64,plain,(
    ~ spl4_5 ),
    inference(avatar_split_clause,[],[f26,f62])).

fof(f26,plain,(
    ~ v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_xboole_0(X1) )
           => v2_tex_2(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tex_2)).

fof(f60,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f29,f58])).

fof(f29,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f56,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f28,f54])).

fof(f28,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f48,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f24,f46])).

fof(f24,plain,(
    v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:57:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.45  % (1735)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.47  % (1732)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.47  % (1726)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.48  % (1726)Refutation not found, incomplete strategy% (1726)------------------------------
% 0.20/0.48  % (1726)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (1726)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (1726)Memory used [KB]: 10618
% 0.20/0.48  % (1726)Time elapsed: 0.060 s
% 0.20/0.48  % (1726)------------------------------
% 0.20/0.48  % (1726)------------------------------
% 0.20/0.48  % (1743)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.48  % (1739)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.49  % (1733)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.49  % (1731)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.50  % (1725)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.50  % (1725)Refutation not found, incomplete strategy% (1725)------------------------------
% 0.20/0.50  % (1725)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (1725)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (1725)Memory used [KB]: 6140
% 0.20/0.50  % (1725)Time elapsed: 0.079 s
% 0.20/0.50  % (1725)------------------------------
% 0.20/0.50  % (1725)------------------------------
% 0.20/0.50  % (1727)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.50  % (1729)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.50  % (1728)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.50  % (1730)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.50  % (1745)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.51  % (1745)Refutation not found, incomplete strategy% (1745)------------------------------
% 0.20/0.51  % (1745)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (1745)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (1745)Memory used [KB]: 10490
% 0.20/0.51  % (1745)Time elapsed: 0.097 s
% 0.20/0.51  % (1745)------------------------------
% 0.20/0.51  % (1745)------------------------------
% 0.20/0.51  % (1737)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (1744)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.51  % (1734)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.51  % (1738)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.51  % (1734)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f262,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(avatar_sat_refutation,[],[f48,f56,f60,f64,f72,f76,f80,f88,f93,f105,f110,f118,f124,f131,f135,f140,f144,f149,f163,f173,f188,f204,f212,f226,f249,f261])).
% 0.20/0.51  fof(f261,plain,(
% 0.20/0.51    ~spl4_3 | ~spl4_4 | ~spl4_7 | ~spl4_10 | ~spl4_20 | spl4_39),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f260])).
% 0.20/0.51  fof(f260,plain,(
% 0.20/0.51    $false | (~spl4_3 | ~spl4_4 | ~spl4_7 | ~spl4_10 | ~spl4_20 | spl4_39)),
% 0.20/0.51    inference(subsumption_resolution,[],[f259,f55])).
% 0.20/0.51  fof(f55,plain,(
% 0.20/0.51    v2_pre_topc(sK0) | ~spl4_3),
% 0.20/0.51    inference(avatar_component_clause,[],[f54])).
% 0.20/0.51  fof(f54,plain,(
% 0.20/0.51    spl4_3 <=> v2_pre_topc(sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.51  fof(f259,plain,(
% 0.20/0.51    ~v2_pre_topc(sK0) | (~spl4_4 | ~spl4_7 | ~spl4_10 | ~spl4_20 | spl4_39)),
% 0.20/0.51    inference(subsumption_resolution,[],[f258,f87])).
% 0.20/0.51  fof(f87,plain,(
% 0.20/0.51    v1_xboole_0(k1_xboole_0) | ~spl4_10),
% 0.20/0.51    inference(avatar_component_clause,[],[f86])).
% 0.20/0.51  fof(f86,plain,(
% 0.20/0.51    spl4_10 <=> v1_xboole_0(k1_xboole_0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.20/0.51  fof(f258,plain,(
% 0.20/0.51    ~v1_xboole_0(k1_xboole_0) | ~v2_pre_topc(sK0) | (~spl4_4 | ~spl4_7 | ~spl4_20 | spl4_39)),
% 0.20/0.51    inference(subsumption_resolution,[],[f257,f71])).
% 0.20/0.51  fof(f71,plain,(
% 0.20/0.51    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) ) | ~spl4_7),
% 0.20/0.51    inference(avatar_component_clause,[],[f70])).
% 0.20/0.51  fof(f70,plain,(
% 0.20/0.51    spl4_7 <=> ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.20/0.51  fof(f257,plain,(
% 0.20/0.51    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_xboole_0(k1_xboole_0) | ~v2_pre_topc(sK0) | (~spl4_4 | ~spl4_20 | spl4_39)),
% 0.20/0.51    inference(subsumption_resolution,[],[f255,f59])).
% 0.20/0.51  fof(f59,plain,(
% 0.20/0.51    l1_pre_topc(sK0) | ~spl4_4),
% 0.20/0.51    inference(avatar_component_clause,[],[f58])).
% 0.20/0.51  fof(f58,plain,(
% 0.20/0.51    spl4_4 <=> l1_pre_topc(sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.51  fof(f255,plain,(
% 0.20/0.51    ~l1_pre_topc(sK0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_xboole_0(k1_xboole_0) | ~v2_pre_topc(sK0) | (~spl4_20 | spl4_39)),
% 0.20/0.51    inference(resolution,[],[f248,f134])).
% 0.20/0.51  fof(f134,plain,(
% 0.20/0.51    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1) | ~v2_pre_topc(X0)) ) | ~spl4_20),
% 0.20/0.51    inference(avatar_component_clause,[],[f133])).
% 0.20/0.51  fof(f133,plain,(
% 0.20/0.51    spl4_20 <=> ! [X1,X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1) | v4_pre_topc(X1,X0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.20/0.51  fof(f248,plain,(
% 0.20/0.51    ~v4_pre_topc(k1_xboole_0,sK0) | spl4_39),
% 0.20/0.51    inference(avatar_component_clause,[],[f247])).
% 0.20/0.51  fof(f247,plain,(
% 0.20/0.51    spl4_39 <=> v4_pre_topc(k1_xboole_0,sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).
% 0.20/0.51  fof(f249,plain,(
% 0.20/0.51    ~spl4_39 | ~spl4_7 | ~spl4_35 | ~spl4_37),
% 0.20/0.51    inference(avatar_split_clause,[],[f236,f224,f210,f70,f247])).
% 0.20/0.51  fof(f210,plain,(
% 0.20/0.51    spl4_35 <=> ! [X0] : (k1_xboole_0 != k3_xboole_0(k1_xboole_0,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X0,sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).
% 0.20/0.51  fof(f224,plain,(
% 0.20/0.51    spl4_37 <=> ! [X2] : k1_xboole_0 = k3_xboole_0(X2,k1_xboole_0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).
% 0.20/0.51  fof(f236,plain,(
% 0.20/0.51    ~v4_pre_topc(k1_xboole_0,sK0) | (~spl4_7 | ~spl4_35 | ~spl4_37)),
% 0.20/0.51    inference(subsumption_resolution,[],[f235,f71])).
% 0.20/0.51  fof(f235,plain,(
% 0.20/0.51    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(k1_xboole_0,sK0) | (~spl4_35 | ~spl4_37)),
% 0.20/0.51    inference(trivial_inequality_removal,[],[f234])).
% 0.20/0.51  fof(f234,plain,(
% 0.20/0.51    k1_xboole_0 != k1_xboole_0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(k1_xboole_0,sK0) | (~spl4_35 | ~spl4_37)),
% 0.20/0.51    inference(superposition,[],[f211,f225])).
% 0.20/0.51  fof(f225,plain,(
% 0.20/0.51    ( ! [X2] : (k1_xboole_0 = k3_xboole_0(X2,k1_xboole_0)) ) | ~spl4_37),
% 0.20/0.51    inference(avatar_component_clause,[],[f224])).
% 0.20/0.51  fof(f211,plain,(
% 0.20/0.51    ( ! [X0] : (k1_xboole_0 != k3_xboole_0(k1_xboole_0,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X0,sK0)) ) | ~spl4_35),
% 0.20/0.51    inference(avatar_component_clause,[],[f210])).
% 0.20/0.51  fof(f226,plain,(
% 0.20/0.51    spl4_37 | ~spl4_7 | ~spl4_22),
% 0.20/0.51    inference(avatar_split_clause,[],[f216,f142,f70,f224])).
% 0.20/0.51  fof(f142,plain,(
% 0.20/0.51    spl4_22 <=> ! [X1,X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k3_xboole_0(X1,X0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.20/0.51  fof(f216,plain,(
% 0.20/0.51    ( ! [X2] : (k1_xboole_0 = k3_xboole_0(X2,k1_xboole_0)) ) | (~spl4_7 | ~spl4_22)),
% 0.20/0.51    inference(resolution,[],[f143,f71])).
% 0.20/0.51  fof(f143,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k3_xboole_0(X1,X0)) ) | ~spl4_22),
% 0.20/0.51    inference(avatar_component_clause,[],[f142])).
% 0.20/0.51  fof(f212,plain,(
% 0.20/0.51    spl4_35 | ~spl4_4 | ~spl4_7 | spl4_11 | ~spl4_31 | ~spl4_34),
% 0.20/0.51    inference(avatar_split_clause,[],[f208,f202,f186,f91,f70,f58,f210])).
% 0.20/0.51  fof(f91,plain,(
% 0.20/0.51    spl4_11 <=> v2_tex_2(k1_xboole_0,sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.20/0.51  fof(f186,plain,(
% 0.20/0.51    spl4_31 <=> k1_xboole_0 = sK2(sK0,k1_xboole_0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).
% 0.20/0.51  fof(f202,plain,(
% 0.20/0.51    spl4_34 <=> ! [X1,X0,X2] : (k3_xboole_0(X1,X2) != sK2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X2,X0) | ~l1_pre_topc(X0) | v2_tex_2(X1,X0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).
% 0.20/0.51  fof(f208,plain,(
% 0.20/0.51    ( ! [X0] : (k1_xboole_0 != k3_xboole_0(k1_xboole_0,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X0,sK0)) ) | (~spl4_4 | ~spl4_7 | spl4_11 | ~spl4_31 | ~spl4_34)),
% 0.20/0.51    inference(subsumption_resolution,[],[f207,f92])).
% 0.20/0.51  fof(f92,plain,(
% 0.20/0.51    ~v2_tex_2(k1_xboole_0,sK0) | spl4_11),
% 0.20/0.51    inference(avatar_component_clause,[],[f91])).
% 0.20/0.51  fof(f207,plain,(
% 0.20/0.51    ( ! [X0] : (k1_xboole_0 != k3_xboole_0(k1_xboole_0,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X0,sK0) | v2_tex_2(k1_xboole_0,sK0)) ) | (~spl4_4 | ~spl4_7 | ~spl4_31 | ~spl4_34)),
% 0.20/0.51    inference(subsumption_resolution,[],[f206,f59])).
% 0.20/0.51  fof(f206,plain,(
% 0.20/0.51    ( ! [X0] : (k1_xboole_0 != k3_xboole_0(k1_xboole_0,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X0,sK0) | ~l1_pre_topc(sK0) | v2_tex_2(k1_xboole_0,sK0)) ) | (~spl4_7 | ~spl4_31 | ~spl4_34)),
% 0.20/0.51    inference(subsumption_resolution,[],[f205,f71])).
% 0.20/0.51  fof(f205,plain,(
% 0.20/0.51    ( ! [X0] : (k1_xboole_0 != k3_xboole_0(k1_xboole_0,X0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X0,sK0) | ~l1_pre_topc(sK0) | v2_tex_2(k1_xboole_0,sK0)) ) | (~spl4_31 | ~spl4_34)),
% 0.20/0.51    inference(superposition,[],[f203,f187])).
% 0.20/0.51  fof(f187,plain,(
% 0.20/0.51    k1_xboole_0 = sK2(sK0,k1_xboole_0) | ~spl4_31),
% 0.20/0.51    inference(avatar_component_clause,[],[f186])).
% 0.20/0.51  fof(f203,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) != sK2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X2,X0) | ~l1_pre_topc(X0) | v2_tex_2(X1,X0)) ) | ~spl4_34),
% 0.20/0.51    inference(avatar_component_clause,[],[f202])).
% 0.20/0.51  fof(f204,plain,(
% 0.20/0.51    spl4_34 | ~spl4_18 | ~spl4_28),
% 0.20/0.51    inference(avatar_split_clause,[],[f184,f171,f122,f202])).
% 0.20/0.51  fof(f122,plain,(
% 0.20/0.51    spl4_18 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.20/0.51  fof(f171,plain,(
% 0.20/0.51    spl4_28 <=> ! [X1,X3,X0] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X3,X0) | k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1) | v2_tex_2(X1,X0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 0.20/0.51  fof(f184,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) != sK2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X2,X0) | ~l1_pre_topc(X0) | v2_tex_2(X1,X0)) ) | (~spl4_18 | ~spl4_28)),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f183])).
% 0.20/0.51  fof(f183,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) != sK2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X2,X0) | ~l1_pre_topc(X0) | v2_tex_2(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) ) | (~spl4_18 | ~spl4_28)),
% 0.20/0.51    inference(superposition,[],[f172,f123])).
% 0.20/0.51  fof(f123,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) ) | ~spl4_18),
% 0.20/0.51    inference(avatar_component_clause,[],[f122])).
% 0.20/0.51  fof(f172,plain,(
% 0.20/0.51    ( ! [X0,X3,X1] : (k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X3,X0) | ~l1_pre_topc(X0) | v2_tex_2(X1,X0)) ) | ~spl4_28),
% 0.20/0.51    inference(avatar_component_clause,[],[f171])).
% 0.20/0.51  fof(f188,plain,(
% 0.20/0.51    spl4_31 | ~spl4_9 | ~spl4_26),
% 0.20/0.51    inference(avatar_split_clause,[],[f168,f161,f78,f186])).
% 0.20/0.51  fof(f78,plain,(
% 0.20/0.51    spl4_9 <=> ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.20/0.51  fof(f161,plain,(
% 0.20/0.51    spl4_26 <=> r1_tarski(sK2(sK0,k1_xboole_0),k1_xboole_0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 0.20/0.51  fof(f168,plain,(
% 0.20/0.51    k1_xboole_0 = sK2(sK0,k1_xboole_0) | (~spl4_9 | ~spl4_26)),
% 0.20/0.51    inference(resolution,[],[f162,f79])).
% 0.20/0.51  fof(f79,plain,(
% 0.20/0.51    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) ) | ~spl4_9),
% 0.20/0.51    inference(avatar_component_clause,[],[f78])).
% 0.20/0.51  fof(f162,plain,(
% 0.20/0.51    r1_tarski(sK2(sK0,k1_xboole_0),k1_xboole_0) | ~spl4_26),
% 0.20/0.51    inference(avatar_component_clause,[],[f161])).
% 0.20/0.51  fof(f173,plain,(
% 0.20/0.51    spl4_28),
% 0.20/0.51    inference(avatar_split_clause,[],[f32,f171])).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    ( ! [X0,X3,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X3,X0) | k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1) | v2_tex_2(X1,X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f16])).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.52    inference(flattening,[],[f15])).
% 0.20/0.52  fof(f15,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((? [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f9])).
% 0.20/0.52  fof(f9,axiom,(
% 0.20/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0))) & r1_tarski(X2,X1))))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_tex_2)).
% 0.20/0.52  fof(f163,plain,(
% 0.20/0.52    spl4_26 | ~spl4_7 | spl4_11 | ~spl4_23),
% 0.20/0.52    inference(avatar_split_clause,[],[f155,f147,f91,f70,f161])).
% 0.20/0.52  fof(f147,plain,(
% 0.20/0.52    spl4_23 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(sK2(sK0,X0),X0) | v2_tex_2(X0,sK0))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 0.20/0.52  fof(f155,plain,(
% 0.20/0.52    r1_tarski(sK2(sK0,k1_xboole_0),k1_xboole_0) | (~spl4_7 | spl4_11 | ~spl4_23)),
% 0.20/0.52    inference(subsumption_resolution,[],[f154,f71])).
% 0.20/0.52  fof(f154,plain,(
% 0.20/0.52    r1_tarski(sK2(sK0,k1_xboole_0),k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | (spl4_11 | ~spl4_23)),
% 0.20/0.52    inference(resolution,[],[f148,f92])).
% 0.20/0.52  fof(f148,plain,(
% 0.20/0.52    ( ! [X0] : (v2_tex_2(X0,sK0) | r1_tarski(sK2(sK0,X0),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl4_23),
% 0.20/0.52    inference(avatar_component_clause,[],[f147])).
% 0.20/0.52  fof(f149,plain,(
% 0.20/0.52    spl4_23 | ~spl4_4 | ~spl4_21),
% 0.20/0.52    inference(avatar_split_clause,[],[f145,f138,f58,f147])).
% 0.20/0.52  fof(f138,plain,(
% 0.20/0.52    spl4_21 <=> ! [X1,X0] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(sK2(X0,X1),X1) | v2_tex_2(X1,X0))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.20/0.52  fof(f145,plain,(
% 0.20/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(sK2(sK0,X0),X0) | v2_tex_2(X0,sK0)) ) | (~spl4_4 | ~spl4_21)),
% 0.20/0.52    inference(resolution,[],[f139,f59])).
% 0.20/0.52  fof(f139,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(sK2(X0,X1),X1) | v2_tex_2(X1,X0)) ) | ~spl4_21),
% 0.20/0.52    inference(avatar_component_clause,[],[f138])).
% 0.20/0.52  fof(f144,plain,(
% 0.20/0.52    spl4_22 | ~spl4_15 | ~spl4_19),
% 0.20/0.52    inference(avatar_split_clause,[],[f136,f129,f108,f142])).
% 0.20/0.52  fof(f108,plain,(
% 0.20/0.52    spl4_15 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.20/0.52  fof(f129,plain,(
% 0.20/0.52    spl4_19 <=> ! [X1,X0,X2] : (m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.20/0.52  fof(f136,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k3_xboole_0(X1,X0)) ) | (~spl4_15 | ~spl4_19)),
% 0.20/0.52    inference(resolution,[],[f130,f109])).
% 0.20/0.52  fof(f109,plain,(
% 0.20/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X0) ) | ~spl4_15),
% 0.20/0.52    inference(avatar_component_clause,[],[f108])).
% 0.20/0.52  fof(f130,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) ) | ~spl4_19),
% 0.20/0.52    inference(avatar_component_clause,[],[f129])).
% 0.20/0.52  fof(f140,plain,(
% 0.20/0.52    spl4_21),
% 0.20/0.52    inference(avatar_split_clause,[],[f37,f138])).
% 0.20/0.52  fof(f37,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(sK2(X0,X1),X1) | v2_tex_2(X1,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f16])).
% 0.20/0.52  fof(f135,plain,(
% 0.20/0.52    spl4_20),
% 0.20/0.52    inference(avatar_split_clause,[],[f39,f133])).
% 0.20/0.52  fof(f39,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1) | v4_pre_topc(X1,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f19])).
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (v4_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.52    inference(flattening,[],[f18])).
% 0.20/0.52  fof(f18,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) | ~v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f8])).
% 0.20/0.52  fof(f8,axiom,(
% 0.20/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_xboole_0(X1) => v4_pre_topc(X1,X0))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_pre_topc)).
% 0.20/0.52  fof(f131,plain,(
% 0.20/0.52    spl4_19 | ~spl4_17 | ~spl4_18),
% 0.20/0.52    inference(avatar_split_clause,[],[f127,f122,f116,f129])).
% 0.20/0.52  fof(f116,plain,(
% 0.20/0.52    spl4_17 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.20/0.52  fof(f127,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) ) | (~spl4_17 | ~spl4_18)),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f126])).
% 0.20/0.52  fof(f126,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) ) | (~spl4_17 | ~spl4_18)),
% 0.20/0.52    inference(superposition,[],[f117,f123])).
% 0.20/0.52  fof(f117,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) ) | ~spl4_17),
% 0.20/0.52    inference(avatar_component_clause,[],[f116])).
% 0.20/0.52  fof(f124,plain,(
% 0.20/0.52    spl4_18),
% 0.20/0.52    inference(avatar_split_clause,[],[f43,f122])).
% 0.20/0.52  fof(f43,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f21])).
% 0.20/0.52  fof(f21,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.20/0.52  fof(f118,plain,(
% 0.20/0.52    spl4_17),
% 0.20/0.52    inference(avatar_split_clause,[],[f42,f116])).
% 0.20/0.52  fof(f42,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f20])).
% 0.20/0.52  fof(f20,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).
% 0.20/0.52  fof(f110,plain,(
% 0.20/0.52    spl4_15 | ~spl4_9 | ~spl4_14),
% 0.20/0.52    inference(avatar_split_clause,[],[f106,f103,f78,f108])).
% 0.20/0.52  fof(f103,plain,(
% 0.20/0.52    spl4_14 <=> ! [X1,X0] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.20/0.52  fof(f106,plain,(
% 0.20/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X0) ) | (~spl4_9 | ~spl4_14)),
% 0.20/0.52    inference(resolution,[],[f104,f79])).
% 0.20/0.52  fof(f104,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) ) | ~spl4_14),
% 0.20/0.52    inference(avatar_component_clause,[],[f103])).
% 0.20/0.52  fof(f105,plain,(
% 0.20/0.52    spl4_14),
% 0.20/0.52    inference(avatar_split_clause,[],[f41,f103])).
% 0.20/0.52  fof(f41,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f6])).
% 0.20/0.52  fof(f6,axiom,(
% 0.20/0.52    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.52  fof(f93,plain,(
% 0.20/0.52    ~spl4_11 | ~spl4_1 | spl4_5 | ~spl4_8),
% 0.20/0.52    inference(avatar_split_clause,[],[f83,f74,f62,f46,f91])).
% 0.20/0.52  fof(f46,plain,(
% 0.20/0.52    spl4_1 <=> v1_xboole_0(sK1)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.52  fof(f62,plain,(
% 0.20/0.52    spl4_5 <=> v2_tex_2(sK1,sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.52  fof(f74,plain,(
% 0.20/0.52    spl4_8 <=> ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.20/0.52  fof(f83,plain,(
% 0.20/0.52    ~v2_tex_2(k1_xboole_0,sK0) | (~spl4_1 | spl4_5 | ~spl4_8)),
% 0.20/0.52    inference(backward_demodulation,[],[f63,f81])).
% 0.20/0.52  fof(f81,plain,(
% 0.20/0.52    k1_xboole_0 = sK1 | (~spl4_1 | ~spl4_8)),
% 0.20/0.52    inference(resolution,[],[f75,f47])).
% 0.20/0.52  fof(f47,plain,(
% 0.20/0.52    v1_xboole_0(sK1) | ~spl4_1),
% 0.20/0.52    inference(avatar_component_clause,[],[f46])).
% 0.20/0.52  fof(f75,plain,(
% 0.20/0.52    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) ) | ~spl4_8),
% 0.20/0.52    inference(avatar_component_clause,[],[f74])).
% 0.20/0.52  fof(f63,plain,(
% 0.20/0.52    ~v2_tex_2(sK1,sK0) | spl4_5),
% 0.20/0.52    inference(avatar_component_clause,[],[f62])).
% 0.20/0.52  fof(f88,plain,(
% 0.20/0.52    spl4_10 | ~spl4_1 | ~spl4_8),
% 0.20/0.52    inference(avatar_split_clause,[],[f84,f74,f46,f86])).
% 0.20/0.52  fof(f84,plain,(
% 0.20/0.52    v1_xboole_0(k1_xboole_0) | (~spl4_1 | ~spl4_8)),
% 0.20/0.52    inference(backward_demodulation,[],[f47,f81])).
% 0.20/0.52  fof(f80,plain,(
% 0.20/0.52    spl4_9),
% 0.20/0.52    inference(avatar_split_clause,[],[f38,f78])).
% 0.20/0.52  fof(f38,plain,(
% 0.20/0.52    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f17])).
% 0.20/0.52  fof(f17,plain,(
% 0.20/0.52    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.20/0.52    inference(ennf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.20/0.52  fof(f76,plain,(
% 0.20/0.52    spl4_8),
% 0.20/0.52    inference(avatar_split_clause,[],[f31,f74])).
% 0.20/0.52  fof(f31,plain,(
% 0.20/0.52    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f14])).
% 0.20/0.52  fof(f14,plain,(
% 0.20/0.52    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.20/0.52  fof(f72,plain,(
% 0.20/0.52    spl4_7),
% 0.20/0.52    inference(avatar_split_clause,[],[f30,f70])).
% 0.20/0.52  fof(f30,plain,(
% 0.20/0.52    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f5])).
% 0.20/0.52  fof(f5,axiom,(
% 0.20/0.52    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.20/0.52  fof(f64,plain,(
% 0.20/0.52    ~spl4_5),
% 0.20/0.52    inference(avatar_split_clause,[],[f26,f62])).
% 0.20/0.52  fof(f26,plain,(
% 0.20/0.52    ~v2_tex_2(sK1,sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f13])).
% 0.20/0.52  fof(f13,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.52    inference(flattening,[],[f12])).
% 0.20/0.52  fof(f12,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f11])).
% 0.20/0.52  fof(f11,negated_conjecture,(
% 0.20/0.52    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 0.20/0.52    inference(negated_conjecture,[],[f10])).
% 0.20/0.52  fof(f10,conjecture,(
% 0.20/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tex_2)).
% 0.20/0.52  fof(f60,plain,(
% 0.20/0.52    spl4_4),
% 0.20/0.52    inference(avatar_split_clause,[],[f29,f58])).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    l1_pre_topc(sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f13])).
% 0.20/0.52  fof(f56,plain,(
% 0.20/0.52    spl4_3),
% 0.20/0.52    inference(avatar_split_clause,[],[f28,f54])).
% 0.20/0.52  fof(f28,plain,(
% 0.20/0.52    v2_pre_topc(sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f13])).
% 0.20/0.52  fof(f48,plain,(
% 0.20/0.52    spl4_1),
% 0.20/0.52    inference(avatar_split_clause,[],[f24,f46])).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    v1_xboole_0(sK1)),
% 0.20/0.52    inference(cnf_transformation,[],[f13])).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (1734)------------------------------
% 0.20/0.52  % (1734)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (1734)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (1734)Memory used [KB]: 10746
% 0.20/0.52  % (1734)Time elapsed: 0.095 s
% 0.20/0.52  % (1734)------------------------------
% 0.20/0.52  % (1734)------------------------------
% 0.20/0.52  % (1724)Success in time 0.157 s
%------------------------------------------------------------------------------
