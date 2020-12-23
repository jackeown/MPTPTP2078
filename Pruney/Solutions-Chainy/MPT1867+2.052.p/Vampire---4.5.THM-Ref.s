%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:12 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  156 ( 259 expanded)
%              Number of leaves         :   40 ( 119 expanded)
%              Depth                    :    8
%              Number of atoms          :  523 ( 862 expanded)
%              Number of equality atoms :   56 (  92 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f359,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f54,f62,f66,f70,f78,f82,f90,f98,f103,f112,f116,f120,f129,f133,f138,f142,f152,f156,f160,f168,f184,f193,f213,f224,f239,f272,f291,f299,f346,f358])).

fof(f358,plain,
    ( ~ spl5_3
    | ~ spl5_4
    | ~ spl5_7
    | ~ spl5_11
    | ~ spl5_22
    | spl5_52 ),
    inference(avatar_contradiction_clause,[],[f357])).

fof(f357,plain,
    ( $false
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_7
    | ~ spl5_11
    | ~ spl5_22
    | spl5_52 ),
    inference(subsumption_resolution,[],[f356,f61])).

fof(f61,plain,
    ( v2_pre_topc(sK0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f60])).

% (28445)Refutation not found, incomplete strategy% (28445)------------------------------
% (28445)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f60,plain,
    ( spl5_3
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

% (28445)Termination reason: Refutation not found, incomplete strategy

% (28445)Memory used [KB]: 10618
% (28445)Time elapsed: 0.104 s
% (28445)------------------------------
% (28445)------------------------------
fof(f356,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ spl5_4
    | ~ spl5_7
    | ~ spl5_11
    | ~ spl5_22
    | spl5_52 ),
    inference(subsumption_resolution,[],[f355,f97])).

fof(f97,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl5_11
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f355,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v2_pre_topc(sK0)
    | ~ spl5_4
    | ~ spl5_7
    | ~ spl5_22
    | spl5_52 ),
    inference(subsumption_resolution,[],[f354,f77])).

fof(f77,plain,
    ( ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl5_7
  <=> ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f354,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_xboole_0(k1_xboole_0)
    | ~ v2_pre_topc(sK0)
    | ~ spl5_4
    | ~ spl5_22
    | spl5_52 ),
    inference(subsumption_resolution,[],[f352,f65])).

fof(f65,plain,
    ( l1_pre_topc(sK0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl5_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f352,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_xboole_0(k1_xboole_0)
    | ~ v2_pre_topc(sK0)
    | ~ spl5_22
    | spl5_52 ),
    inference(resolution,[],[f345,f151])).

fof(f151,plain,
    ( ! [X0,X1] :
        ( v4_pre_topc(X1,X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v1_xboole_0(X1)
        | ~ v2_pre_topc(X0) )
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f150])).

fof(f150,plain,
    ( spl5_22
  <=> ! [X1,X0] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v1_xboole_0(X1)
        | v4_pre_topc(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f345,plain,
    ( ~ v4_pre_topc(k1_xboole_0,sK0)
    | spl5_52 ),
    inference(avatar_component_clause,[],[f344])).

fof(f344,plain,
    ( spl5_52
  <=> v4_pre_topc(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_52])])).

fof(f346,plain,
    ( ~ spl5_52
    | ~ spl5_4
    | ~ spl5_7
    | spl5_12
    | ~ spl5_42
    | ~ spl5_47 ),
    inference(avatar_split_clause,[],[f313,f297,f270,f101,f76,f64,f344])).

fof(f101,plain,
    ( spl5_12
  <=> v2_tex_2(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f270,plain,
    ( spl5_42
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
        | sK2(X1,X0) != X0
        | ~ v4_pre_topc(X0,X1)
        | ~ l1_pre_topc(X1)
        | v2_tex_2(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).

fof(f297,plain,
    ( spl5_47
  <=> k1_xboole_0 = sK2(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_47])])).

fof(f313,plain,
    ( ~ v4_pre_topc(k1_xboole_0,sK0)
    | ~ spl5_4
    | ~ spl5_7
    | spl5_12
    | ~ spl5_42
    | ~ spl5_47 ),
    inference(subsumption_resolution,[],[f312,f102])).

fof(f102,plain,
    ( ~ v2_tex_2(k1_xboole_0,sK0)
    | spl5_12 ),
    inference(avatar_component_clause,[],[f101])).

fof(f312,plain,
    ( ~ v4_pre_topc(k1_xboole_0,sK0)
    | v2_tex_2(k1_xboole_0,sK0)
    | ~ spl5_4
    | ~ spl5_7
    | ~ spl5_42
    | ~ spl5_47 ),
    inference(subsumption_resolution,[],[f311,f65])).

fof(f311,plain,
    ( ~ v4_pre_topc(k1_xboole_0,sK0)
    | ~ l1_pre_topc(sK0)
    | v2_tex_2(k1_xboole_0,sK0)
    | ~ spl5_7
    | ~ spl5_42
    | ~ spl5_47 ),
    inference(subsumption_resolution,[],[f308,f77])).

fof(f308,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_pre_topc(k1_xboole_0,sK0)
    | ~ l1_pre_topc(sK0)
    | v2_tex_2(k1_xboole_0,sK0)
    | ~ spl5_42
    | ~ spl5_47 ),
    inference(trivial_inequality_removal,[],[f306])).

fof(f306,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_pre_topc(k1_xboole_0,sK0)
    | ~ l1_pre_topc(sK0)
    | v2_tex_2(k1_xboole_0,sK0)
    | ~ spl5_42
    | ~ spl5_47 ),
    inference(superposition,[],[f271,f298])).

% (28426)Refutation not found, incomplete strategy% (28426)------------------------------
% (28426)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (28426)Termination reason: Refutation not found, incomplete strategy

% (28426)Memory used [KB]: 10618
% (28426)Time elapsed: 0.095 s
% (28426)------------------------------
% (28426)------------------------------
fof(f298,plain,
    ( k1_xboole_0 = sK2(sK0,k1_xboole_0)
    | ~ spl5_47 ),
    inference(avatar_component_clause,[],[f297])).

fof(f271,plain,
    ( ! [X0,X1] :
        ( sK2(X1,X0) != X0
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ v4_pre_topc(X0,X1)
        | ~ l1_pre_topc(X1)
        | v2_tex_2(X0,X1) )
    | ~ spl5_42 ),
    inference(avatar_component_clause,[],[f270])).

fof(f299,plain,
    ( spl5_47
    | ~ spl5_7
    | spl5_12
    | ~ spl5_37
    | ~ spl5_46 ),
    inference(avatar_split_clause,[],[f295,f289,f237,f101,f76,f297])).

fof(f237,plain,
    ( spl5_37
  <=> ! [X4] : k1_xboole_0 = k3_xboole_0(X4,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).

fof(f289,plain,
    ( spl5_46
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_tex_2(X0,sK0)
        | sK2(sK0,X0) = k3_xboole_0(sK2(sK0,X0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_46])])).

fof(f295,plain,
    ( k1_xboole_0 = sK2(sK0,k1_xboole_0)
    | ~ spl5_7
    | spl5_12
    | ~ spl5_37
    | ~ spl5_46 ),
    inference(subsumption_resolution,[],[f294,f77])).

fof(f294,plain,
    ( k1_xboole_0 = sK2(sK0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_12
    | ~ spl5_37
    | ~ spl5_46 ),
    inference(subsumption_resolution,[],[f292,f102])).

fof(f292,plain,
    ( k1_xboole_0 = sK2(sK0,k1_xboole_0)
    | v2_tex_2(k1_xboole_0,sK0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_37
    | ~ spl5_46 ),
    inference(superposition,[],[f290,f238])).

fof(f238,plain,
    ( ! [X4] : k1_xboole_0 = k3_xboole_0(X4,k1_xboole_0)
    | ~ spl5_37 ),
    inference(avatar_component_clause,[],[f237])).

fof(f290,plain,
    ( ! [X0] :
        ( sK2(sK0,X0) = k3_xboole_0(sK2(sK0,X0),X0)
        | v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_46 ),
    inference(avatar_component_clause,[],[f289])).

fof(f291,plain,
    ( spl5_46
    | ~ spl5_14
    | ~ spl5_34 ),
    inference(avatar_split_clause,[],[f216,f211,f110,f289])).

fof(f110,plain,
    ( spl5_14
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,X1)
        | k3_xboole_0(X0,X1) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f211,plain,
    ( spl5_34
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(sK2(sK0,X0),X0)
        | v2_tex_2(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).

fof(f216,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_tex_2(X0,sK0)
        | sK2(sK0,X0) = k3_xboole_0(sK2(sK0,X0),X0) )
    | ~ spl5_14
    | ~ spl5_34 ),
    inference(resolution,[],[f212,f111])).

fof(f111,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k3_xboole_0(X0,X1) = X0 )
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f110])).

fof(f212,plain,
    ( ! [X0] :
        ( r1_tarski(sK2(sK0,X0),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_tex_2(X0,sK0) )
    | ~ spl5_34 ),
    inference(avatar_component_clause,[],[f211])).

fof(f272,plain,
    ( spl5_42
    | ~ spl5_16
    | ~ spl5_30 ),
    inference(avatar_split_clause,[],[f205,f191,f118,f270])).

fof(f118,plain,
    ( spl5_16
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | k9_subset_1(X0,X1,X1) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f191,plain,
    ( spl5_30
  <=> ! [X1,X3,X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v4_pre_topc(X3,X0)
        | k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1)
        | v2_tex_2(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f205,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
        | sK2(X1,X0) != X0
        | ~ v4_pre_topc(X0,X1)
        | ~ l1_pre_topc(X1)
        | v2_tex_2(X0,X1) )
    | ~ spl5_16
    | ~ spl5_30 ),
    inference(condensation,[],[f204])).

fof(f204,plain,
    ( ! [X2,X0,X1] :
        ( sK2(X0,X1) != X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v4_pre_topc(X1,X0)
        | ~ l1_pre_topc(X0)
        | v2_tex_2(X1,X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
    | ~ spl5_16
    | ~ spl5_30 ),
    inference(duplicate_literal_removal,[],[f203])).

fof(f203,plain,
    ( ! [X2,X0,X1] :
        ( sK2(X0,X1) != X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v4_pre_topc(X1,X0)
        | ~ l1_pre_topc(X0)
        | v2_tex_2(X1,X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
    | ~ spl5_16
    | ~ spl5_30 ),
    inference(superposition,[],[f192,f119])).

fof(f119,plain,
    ( ! [X2,X0,X1] :
        ( k9_subset_1(X0,X1,X1) = X1
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f118])).

fof(f192,plain,
    ( ! [X0,X3,X1] :
        ( k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v4_pre_topc(X3,X0)
        | ~ l1_pre_topc(X0)
        | v2_tex_2(X1,X0) )
    | ~ spl5_30 ),
    inference(avatar_component_clause,[],[f191])).

fof(f239,plain,
    ( spl5_37
    | ~ spl5_28
    | ~ spl5_36 ),
    inference(avatar_split_clause,[],[f226,f222,f182,f237])).

fof(f182,plain,
    ( spl5_28
  <=> ! [X0] : k1_xboole_0 = k9_subset_1(k1_xboole_0,X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f222,plain,
    ( spl5_36
  <=> ! [X1,X0] : k9_subset_1(X0,X1,k1_xboole_0) = k3_xboole_0(X1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).

fof(f226,plain,
    ( ! [X4] : k1_xboole_0 = k3_xboole_0(X4,k1_xboole_0)
    | ~ spl5_28
    | ~ spl5_36 ),
    inference(superposition,[],[f223,f183])).

fof(f183,plain,
    ( ! [X0] : k1_xboole_0 = k9_subset_1(k1_xboole_0,X0,k1_xboole_0)
    | ~ spl5_28 ),
    inference(avatar_component_clause,[],[f182])).

fof(f223,plain,
    ( ! [X0,X1] : k9_subset_1(X0,X1,k1_xboole_0) = k3_xboole_0(X1,k1_xboole_0)
    | ~ spl5_36 ),
    inference(avatar_component_clause,[],[f222])).

fof(f224,plain,
    ( spl5_36
    | ~ spl5_7
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f144,f136,f76,f222])).

fof(f136,plain,
    ( spl5_20
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f144,plain,
    ( ! [X0,X1] : k9_subset_1(X0,X1,k1_xboole_0) = k3_xboole_0(X1,k1_xboole_0)
    | ~ spl5_7
    | ~ spl5_20 ),
    inference(resolution,[],[f137,f77])).

fof(f137,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) )
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f136])).

fof(f213,plain,
    ( spl5_34
    | ~ spl5_4
    | ~ spl5_24 ),
    inference(avatar_split_clause,[],[f164,f158,f64,f211])).

fof(f158,plain,
    ( spl5_24
  <=> ! [X1,X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | r1_tarski(sK2(X0,X1),X1)
        | v2_tex_2(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f164,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(sK2(sK0,X0),X0)
        | v2_tex_2(X0,sK0) )
    | ~ spl5_4
    | ~ spl5_24 ),
    inference(resolution,[],[f159,f65])).

fof(f159,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | r1_tarski(sK2(X0,X1),X1)
        | v2_tex_2(X1,X0) )
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f158])).

fof(f193,plain,(
    spl5_30 ),
    inference(avatar_split_clause,[],[f35,f191])).

fof(f35,plain,(
    ! [X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X3,X0)
      | k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1)
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

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
    inference(ennf_transformation,[],[f11])).

% (28428)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
fof(f11,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_tex_2)).

fof(f184,plain,
    ( spl5_28
    | ~ spl5_7
    | ~ spl5_25 ),
    inference(avatar_split_clause,[],[f174,f166,f76,f182])).

fof(f166,plain,
    ( spl5_25
  <=> ! [X1,X0] :
        ( k1_xboole_0 = k9_subset_1(k1_xboole_0,X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f174,plain,
    ( ! [X0] : k1_xboole_0 = k9_subset_1(k1_xboole_0,X0,k1_xboole_0)
    | ~ spl5_7
    | ~ spl5_25 ),
    inference(resolution,[],[f167,f77])).

fof(f167,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = k9_subset_1(k1_xboole_0,X0,X1) )
    | ~ spl5_25 ),
    inference(avatar_component_clause,[],[f166])).

fof(f168,plain,
    ( spl5_25
    | ~ spl5_18
    | ~ spl5_23 ),
    inference(avatar_split_clause,[],[f162,f154,f127,f166])).

fof(f127,plain,
    ( spl5_18
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f154,plain,
    ( spl5_23
  <=> ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = X3 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f162,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = k9_subset_1(k1_xboole_0,X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) )
    | ~ spl5_18
    | ~ spl5_23 ),
    inference(resolution,[],[f155,f128])).

fof(f128,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f127])).

fof(f155,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = X3 )
    | ~ spl5_23 ),
    inference(avatar_component_clause,[],[f154])).

fof(f160,plain,(
    spl5_24 ),
    inference(avatar_split_clause,[],[f40,f158])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(sK2(X0,X1),X1)
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f156,plain,
    ( spl5_23
    | ~ spl5_8
    | ~ spl5_21 ),
    inference(avatar_split_clause,[],[f148,f140,f80,f154])).

fof(f80,plain,
    ( spl5_8
  <=> ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f140,plain,
    ( spl5_21
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f148,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = X3 )
    | ~ spl5_8
    | ~ spl5_21 ),
    inference(resolution,[],[f141,f81])).

fof(f81,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 )
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f80])).

fof(f141,plain,
    ( ! [X0] :
        ( v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) )
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f140])).

fof(f152,plain,(
    spl5_22 ),
    inference(avatar_split_clause,[],[f42,f150])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_xboole_0(X1)
      | v4_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_xboole_0(X1)
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_pre_topc)).

fof(f142,plain,
    ( spl5_21
    | ~ spl5_10
    | ~ spl5_19 ),
    inference(avatar_split_clause,[],[f134,f131,f88,f140])).

fof(f88,plain,
    ( spl5_10
  <=> ! [X0] :
        ( r2_hidden(sK4(X0),X0)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f131,plain,
    ( spl5_19
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | ~ r2_hidden(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f134,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | v1_xboole_0(X0) )
    | ~ spl5_10
    | ~ spl5_19 ),
    inference(resolution,[],[f132,f89])).

fof(f89,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(X0),X0)
        | v1_xboole_0(X0) )
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f88])).

fof(f132,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) )
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f131])).

fof(f138,plain,(
    spl5_20 ),
    inference(avatar_split_clause,[],[f48,f136])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f133,plain,
    ( spl5_19
    | ~ spl5_11
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f125,f114,f96,f131])).

fof(f114,plain,
    ( spl5_15
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
        | ~ v1_xboole_0(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f125,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | ~ r2_hidden(X1,X0) )
    | ~ spl5_11
    | ~ spl5_15 ),
    inference(resolution,[],[f115,f97])).

fof(f115,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_xboole_0(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
        | ~ r2_hidden(X0,X1) )
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f114])).

fof(f129,plain,(
    spl5_18 ),
    inference(avatar_split_clause,[],[f47,f127])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(f120,plain,(
    spl5_16 ),
    inference(avatar_split_clause,[],[f46,f118])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X1) = X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k9_subset_1)).

fof(f116,plain,(
    spl5_15 ),
    inference(avatar_split_clause,[],[f50,f114])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f112,plain,(
    spl5_14 ),
    inference(avatar_split_clause,[],[f45,f110])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f103,plain,
    ( ~ spl5_12
    | ~ spl5_1
    | spl5_5
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f93,f80,f68,f52,f101])).

fof(f52,plain,
    ( spl5_1
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f68,plain,
    ( spl5_5
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f93,plain,
    ( ~ v2_tex_2(k1_xboole_0,sK0)
    | ~ spl5_1
    | spl5_5
    | ~ spl5_8 ),
    inference(backward_demodulation,[],[f69,f91])).

fof(f91,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_1
    | ~ spl5_8 ),
    inference(resolution,[],[f81,f53])).

fof(f53,plain,
    ( v1_xboole_0(sK1)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f52])).

fof(f69,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | spl5_5 ),
    inference(avatar_component_clause,[],[f68])).

fof(f98,plain,
    ( spl5_11
    | ~ spl5_1
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f94,f80,f52,f96])).

fof(f94,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl5_1
    | ~ spl5_8 ),
    inference(backward_demodulation,[],[f53,f91])).

fof(f90,plain,(
    spl5_10 ),
    inference(avatar_split_clause,[],[f43,f88])).

fof(f43,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f82,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f41,f80])).

fof(f41,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f78,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f34,f76])).

fof(f34,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f70,plain,(
    ~ spl5_5 ),
    inference(avatar_split_clause,[],[f30,f68])).

fof(f30,plain,(
    ~ v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
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
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_xboole_0(X1) )
           => v2_tex_2(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tex_2)).

fof(f66,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f33,f64])).

fof(f33,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f62,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f32,f60])).

fof(f32,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f54,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f28,f52])).

fof(f28,plain,(
    v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:26:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (28440)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.46  % (28432)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.47  % (28433)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.47  % (28430)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.48  % (28425)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.49  % (28439)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.49  % (28434)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.49  % (28426)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.49  % (28427)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.50  % (28431)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.50  % (28435)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.50  % (28438)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.50  % (28429)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.50  % (28443)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.50  % (28444)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.51  % (28445)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.51  % (28434)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f359,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(avatar_sat_refutation,[],[f54,f62,f66,f70,f78,f82,f90,f98,f103,f112,f116,f120,f129,f133,f138,f142,f152,f156,f160,f168,f184,f193,f213,f224,f239,f272,f291,f299,f346,f358])).
% 0.20/0.51  fof(f358,plain,(
% 0.20/0.51    ~spl5_3 | ~spl5_4 | ~spl5_7 | ~spl5_11 | ~spl5_22 | spl5_52),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f357])).
% 0.20/0.51  fof(f357,plain,(
% 0.20/0.51    $false | (~spl5_3 | ~spl5_4 | ~spl5_7 | ~spl5_11 | ~spl5_22 | spl5_52)),
% 0.20/0.51    inference(subsumption_resolution,[],[f356,f61])).
% 0.20/0.51  fof(f61,plain,(
% 0.20/0.51    v2_pre_topc(sK0) | ~spl5_3),
% 0.20/0.51    inference(avatar_component_clause,[],[f60])).
% 0.20/0.51  % (28445)Refutation not found, incomplete strategy% (28445)------------------------------
% 0.20/0.51  % (28445)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  fof(f60,plain,(
% 0.20/0.51    spl5_3 <=> v2_pre_topc(sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.20/0.51  % (28445)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (28445)Memory used [KB]: 10618
% 0.20/0.51  % (28445)Time elapsed: 0.104 s
% 0.20/0.51  % (28445)------------------------------
% 0.20/0.51  % (28445)------------------------------
% 0.20/0.51  fof(f356,plain,(
% 0.20/0.51    ~v2_pre_topc(sK0) | (~spl5_4 | ~spl5_7 | ~spl5_11 | ~spl5_22 | spl5_52)),
% 0.20/0.51    inference(subsumption_resolution,[],[f355,f97])).
% 0.20/0.51  fof(f97,plain,(
% 0.20/0.51    v1_xboole_0(k1_xboole_0) | ~spl5_11),
% 0.20/0.51    inference(avatar_component_clause,[],[f96])).
% 0.20/0.51  fof(f96,plain,(
% 0.20/0.51    spl5_11 <=> v1_xboole_0(k1_xboole_0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.20/0.51  fof(f355,plain,(
% 0.20/0.51    ~v1_xboole_0(k1_xboole_0) | ~v2_pre_topc(sK0) | (~spl5_4 | ~spl5_7 | ~spl5_22 | spl5_52)),
% 0.20/0.51    inference(subsumption_resolution,[],[f354,f77])).
% 0.20/0.51  fof(f77,plain,(
% 0.20/0.51    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) ) | ~spl5_7),
% 0.20/0.51    inference(avatar_component_clause,[],[f76])).
% 0.20/0.51  fof(f76,plain,(
% 0.20/0.51    spl5_7 <=> ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.20/0.51  fof(f354,plain,(
% 0.20/0.51    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_xboole_0(k1_xboole_0) | ~v2_pre_topc(sK0) | (~spl5_4 | ~spl5_22 | spl5_52)),
% 0.20/0.51    inference(subsumption_resolution,[],[f352,f65])).
% 0.20/0.51  fof(f65,plain,(
% 0.20/0.51    l1_pre_topc(sK0) | ~spl5_4),
% 0.20/0.51    inference(avatar_component_clause,[],[f64])).
% 0.20/0.51  fof(f64,plain,(
% 0.20/0.51    spl5_4 <=> l1_pre_topc(sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.20/0.51  fof(f352,plain,(
% 0.20/0.51    ~l1_pre_topc(sK0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_xboole_0(k1_xboole_0) | ~v2_pre_topc(sK0) | (~spl5_22 | spl5_52)),
% 0.20/0.51    inference(resolution,[],[f345,f151])).
% 0.20/0.51  fof(f151,plain,(
% 0.20/0.51    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1) | ~v2_pre_topc(X0)) ) | ~spl5_22),
% 0.20/0.51    inference(avatar_component_clause,[],[f150])).
% 0.20/0.51  fof(f150,plain,(
% 0.20/0.51    spl5_22 <=> ! [X1,X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1) | v4_pre_topc(X1,X0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 0.20/0.51  fof(f345,plain,(
% 0.20/0.51    ~v4_pre_topc(k1_xboole_0,sK0) | spl5_52),
% 0.20/0.51    inference(avatar_component_clause,[],[f344])).
% 0.20/0.51  fof(f344,plain,(
% 0.20/0.51    spl5_52 <=> v4_pre_topc(k1_xboole_0,sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_52])])).
% 0.20/0.51  fof(f346,plain,(
% 0.20/0.51    ~spl5_52 | ~spl5_4 | ~spl5_7 | spl5_12 | ~spl5_42 | ~spl5_47),
% 0.20/0.51    inference(avatar_split_clause,[],[f313,f297,f270,f101,f76,f64,f344])).
% 0.20/0.51  fof(f101,plain,(
% 0.20/0.51    spl5_12 <=> v2_tex_2(k1_xboole_0,sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.20/0.51  fof(f270,plain,(
% 0.20/0.51    spl5_42 <=> ! [X1,X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | sK2(X1,X0) != X0 | ~v4_pre_topc(X0,X1) | ~l1_pre_topc(X1) | v2_tex_2(X0,X1))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).
% 0.20/0.51  fof(f297,plain,(
% 0.20/0.51    spl5_47 <=> k1_xboole_0 = sK2(sK0,k1_xboole_0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_47])])).
% 0.20/0.51  fof(f313,plain,(
% 0.20/0.51    ~v4_pre_topc(k1_xboole_0,sK0) | (~spl5_4 | ~spl5_7 | spl5_12 | ~spl5_42 | ~spl5_47)),
% 0.20/0.51    inference(subsumption_resolution,[],[f312,f102])).
% 0.20/0.51  fof(f102,plain,(
% 0.20/0.51    ~v2_tex_2(k1_xboole_0,sK0) | spl5_12),
% 0.20/0.51    inference(avatar_component_clause,[],[f101])).
% 0.20/0.51  fof(f312,plain,(
% 0.20/0.51    ~v4_pre_topc(k1_xboole_0,sK0) | v2_tex_2(k1_xboole_0,sK0) | (~spl5_4 | ~spl5_7 | ~spl5_42 | ~spl5_47)),
% 0.20/0.51    inference(subsumption_resolution,[],[f311,f65])).
% 0.20/0.51  fof(f311,plain,(
% 0.20/0.51    ~v4_pre_topc(k1_xboole_0,sK0) | ~l1_pre_topc(sK0) | v2_tex_2(k1_xboole_0,sK0) | (~spl5_7 | ~spl5_42 | ~spl5_47)),
% 0.20/0.51    inference(subsumption_resolution,[],[f308,f77])).
% 0.20/0.51  fof(f308,plain,(
% 0.20/0.51    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(k1_xboole_0,sK0) | ~l1_pre_topc(sK0) | v2_tex_2(k1_xboole_0,sK0) | (~spl5_42 | ~spl5_47)),
% 0.20/0.51    inference(trivial_inequality_removal,[],[f306])).
% 0.20/0.51  fof(f306,plain,(
% 0.20/0.51    k1_xboole_0 != k1_xboole_0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(k1_xboole_0,sK0) | ~l1_pre_topc(sK0) | v2_tex_2(k1_xboole_0,sK0) | (~spl5_42 | ~spl5_47)),
% 0.20/0.51    inference(superposition,[],[f271,f298])).
% 0.20/0.51  % (28426)Refutation not found, incomplete strategy% (28426)------------------------------
% 0.20/0.51  % (28426)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (28426)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (28426)Memory used [KB]: 10618
% 0.20/0.51  % (28426)Time elapsed: 0.095 s
% 0.20/0.51  % (28426)------------------------------
% 0.20/0.51  % (28426)------------------------------
% 0.20/0.51  fof(f298,plain,(
% 0.20/0.51    k1_xboole_0 = sK2(sK0,k1_xboole_0) | ~spl5_47),
% 0.20/0.51    inference(avatar_component_clause,[],[f297])).
% 0.20/0.51  fof(f271,plain,(
% 0.20/0.51    ( ! [X0,X1] : (sK2(X1,X0) != X0 | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~v4_pre_topc(X0,X1) | ~l1_pre_topc(X1) | v2_tex_2(X0,X1)) ) | ~spl5_42),
% 0.20/0.51    inference(avatar_component_clause,[],[f270])).
% 0.20/0.51  fof(f299,plain,(
% 0.20/0.51    spl5_47 | ~spl5_7 | spl5_12 | ~spl5_37 | ~spl5_46),
% 0.20/0.51    inference(avatar_split_clause,[],[f295,f289,f237,f101,f76,f297])).
% 0.20/0.51  fof(f237,plain,(
% 0.20/0.51    spl5_37 <=> ! [X4] : k1_xboole_0 = k3_xboole_0(X4,k1_xboole_0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).
% 0.20/0.51  fof(f289,plain,(
% 0.20/0.51    spl5_46 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(X0,sK0) | sK2(sK0,X0) = k3_xboole_0(sK2(sK0,X0),X0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_46])])).
% 0.20/0.51  fof(f295,plain,(
% 0.20/0.51    k1_xboole_0 = sK2(sK0,k1_xboole_0) | (~spl5_7 | spl5_12 | ~spl5_37 | ~spl5_46)),
% 0.20/0.51    inference(subsumption_resolution,[],[f294,f77])).
% 0.20/0.51  fof(f294,plain,(
% 0.20/0.51    k1_xboole_0 = sK2(sK0,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | (spl5_12 | ~spl5_37 | ~spl5_46)),
% 0.20/0.51    inference(subsumption_resolution,[],[f292,f102])).
% 0.20/0.51  fof(f292,plain,(
% 0.20/0.51    k1_xboole_0 = sK2(sK0,k1_xboole_0) | v2_tex_2(k1_xboole_0,sK0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl5_37 | ~spl5_46)),
% 0.20/0.51    inference(superposition,[],[f290,f238])).
% 0.20/0.51  fof(f238,plain,(
% 0.20/0.51    ( ! [X4] : (k1_xboole_0 = k3_xboole_0(X4,k1_xboole_0)) ) | ~spl5_37),
% 0.20/0.51    inference(avatar_component_clause,[],[f237])).
% 0.20/0.51  fof(f290,plain,(
% 0.20/0.51    ( ! [X0] : (sK2(sK0,X0) = k3_xboole_0(sK2(sK0,X0),X0) | v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl5_46),
% 0.20/0.51    inference(avatar_component_clause,[],[f289])).
% 0.20/0.51  fof(f291,plain,(
% 0.20/0.51    spl5_46 | ~spl5_14 | ~spl5_34),
% 0.20/0.51    inference(avatar_split_clause,[],[f216,f211,f110,f289])).
% 0.20/0.51  fof(f110,plain,(
% 0.20/0.51    spl5_14 <=> ! [X1,X0] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.20/0.51  fof(f211,plain,(
% 0.20/0.51    spl5_34 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(sK2(sK0,X0),X0) | v2_tex_2(X0,sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).
% 0.20/0.51  fof(f216,plain,(
% 0.20/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(X0,sK0) | sK2(sK0,X0) = k3_xboole_0(sK2(sK0,X0),X0)) ) | (~spl5_14 | ~spl5_34)),
% 0.20/0.51    inference(resolution,[],[f212,f111])).
% 0.20/0.51  fof(f111,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) ) | ~spl5_14),
% 0.20/0.51    inference(avatar_component_clause,[],[f110])).
% 0.20/0.51  fof(f212,plain,(
% 0.20/0.51    ( ! [X0] : (r1_tarski(sK2(sK0,X0),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(X0,sK0)) ) | ~spl5_34),
% 0.20/0.51    inference(avatar_component_clause,[],[f211])).
% 0.20/0.51  fof(f272,plain,(
% 0.20/0.51    spl5_42 | ~spl5_16 | ~spl5_30),
% 0.20/0.51    inference(avatar_split_clause,[],[f205,f191,f118,f270])).
% 0.20/0.51  fof(f118,plain,(
% 0.20/0.51    spl5_16 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X1) = X1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.20/0.51  fof(f191,plain,(
% 0.20/0.51    spl5_30 <=> ! [X1,X3,X0] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X3,X0) | k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1) | v2_tex_2(X1,X0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).
% 0.20/0.51  fof(f205,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | sK2(X1,X0) != X0 | ~v4_pre_topc(X0,X1) | ~l1_pre_topc(X1) | v2_tex_2(X0,X1)) ) | (~spl5_16 | ~spl5_30)),
% 0.20/0.51    inference(condensation,[],[f204])).
% 0.20/0.51  fof(f204,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (sK2(X0,X1) != X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v2_tex_2(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) ) | (~spl5_16 | ~spl5_30)),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f203])).
% 0.20/0.51  fof(f203,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (sK2(X0,X1) != X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v2_tex_2(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) ) | (~spl5_16 | ~spl5_30)),
% 0.20/0.51    inference(superposition,[],[f192,f119])).
% 0.20/0.51  fof(f119,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0))) ) | ~spl5_16),
% 0.20/0.51    inference(avatar_component_clause,[],[f118])).
% 0.20/0.51  fof(f192,plain,(
% 0.20/0.51    ( ! [X0,X3,X1] : (k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X3,X0) | ~l1_pre_topc(X0) | v2_tex_2(X1,X0)) ) | ~spl5_30),
% 0.20/0.51    inference(avatar_component_clause,[],[f191])).
% 0.20/0.51  fof(f239,plain,(
% 0.20/0.51    spl5_37 | ~spl5_28 | ~spl5_36),
% 0.20/0.51    inference(avatar_split_clause,[],[f226,f222,f182,f237])).
% 0.20/0.51  fof(f182,plain,(
% 0.20/0.51    spl5_28 <=> ! [X0] : k1_xboole_0 = k9_subset_1(k1_xboole_0,X0,k1_xboole_0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).
% 0.20/0.51  fof(f222,plain,(
% 0.20/0.51    spl5_36 <=> ! [X1,X0] : k9_subset_1(X0,X1,k1_xboole_0) = k3_xboole_0(X1,k1_xboole_0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).
% 0.20/0.51  fof(f226,plain,(
% 0.20/0.51    ( ! [X4] : (k1_xboole_0 = k3_xboole_0(X4,k1_xboole_0)) ) | (~spl5_28 | ~spl5_36)),
% 0.20/0.51    inference(superposition,[],[f223,f183])).
% 0.20/0.51  fof(f183,plain,(
% 0.20/0.51    ( ! [X0] : (k1_xboole_0 = k9_subset_1(k1_xboole_0,X0,k1_xboole_0)) ) | ~spl5_28),
% 0.20/0.51    inference(avatar_component_clause,[],[f182])).
% 0.20/0.51  fof(f223,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k9_subset_1(X0,X1,k1_xboole_0) = k3_xboole_0(X1,k1_xboole_0)) ) | ~spl5_36),
% 0.20/0.51    inference(avatar_component_clause,[],[f222])).
% 0.20/0.51  fof(f224,plain,(
% 0.20/0.51    spl5_36 | ~spl5_7 | ~spl5_20),
% 0.20/0.51    inference(avatar_split_clause,[],[f144,f136,f76,f222])).
% 0.20/0.51  fof(f136,plain,(
% 0.20/0.51    spl5_20 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 0.20/0.51  fof(f144,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k9_subset_1(X0,X1,k1_xboole_0) = k3_xboole_0(X1,k1_xboole_0)) ) | (~spl5_7 | ~spl5_20)),
% 0.20/0.51    inference(resolution,[],[f137,f77])).
% 0.20/0.51  fof(f137,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) ) | ~spl5_20),
% 0.20/0.51    inference(avatar_component_clause,[],[f136])).
% 0.20/0.51  fof(f213,plain,(
% 0.20/0.51    spl5_34 | ~spl5_4 | ~spl5_24),
% 0.20/0.51    inference(avatar_split_clause,[],[f164,f158,f64,f211])).
% 0.20/0.51  fof(f158,plain,(
% 0.20/0.51    spl5_24 <=> ! [X1,X0] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(sK2(X0,X1),X1) | v2_tex_2(X1,X0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 0.20/0.51  fof(f164,plain,(
% 0.20/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(sK2(sK0,X0),X0) | v2_tex_2(X0,sK0)) ) | (~spl5_4 | ~spl5_24)),
% 0.20/0.51    inference(resolution,[],[f159,f65])).
% 0.20/0.51  fof(f159,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(sK2(X0,X1),X1) | v2_tex_2(X1,X0)) ) | ~spl5_24),
% 0.20/0.51    inference(avatar_component_clause,[],[f158])).
% 0.20/0.51  fof(f193,plain,(
% 0.20/0.51    spl5_30),
% 0.20/0.51    inference(avatar_split_clause,[],[f35,f191])).
% 0.20/0.51  fof(f35,plain,(
% 0.20/0.51    ( ! [X0,X3,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X3,X0) | k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1) | v2_tex_2(X1,X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f17])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.51    inference(flattening,[],[f16])).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((? [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f11])).
% 0.20/0.51  % (28428)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.51  fof(f11,axiom,(
% 0.20/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0))) & r1_tarski(X2,X1))))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_tex_2)).
% 0.20/0.51  fof(f184,plain,(
% 0.20/0.51    spl5_28 | ~spl5_7 | ~spl5_25),
% 0.20/0.51    inference(avatar_split_clause,[],[f174,f166,f76,f182])).
% 0.20/0.51  fof(f166,plain,(
% 0.20/0.51    spl5_25 <=> ! [X1,X0] : (k1_xboole_0 = k9_subset_1(k1_xboole_0,X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 0.20/0.51  fof(f174,plain,(
% 0.20/0.51    ( ! [X0] : (k1_xboole_0 = k9_subset_1(k1_xboole_0,X0,k1_xboole_0)) ) | (~spl5_7 | ~spl5_25)),
% 0.20/0.51    inference(resolution,[],[f167,f77])).
% 0.20/0.51  fof(f167,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k9_subset_1(k1_xboole_0,X0,X1)) ) | ~spl5_25),
% 0.20/0.51    inference(avatar_component_clause,[],[f166])).
% 0.20/0.51  fof(f168,plain,(
% 0.20/0.51    spl5_25 | ~spl5_18 | ~spl5_23),
% 0.20/0.51    inference(avatar_split_clause,[],[f162,f154,f127,f166])).
% 0.20/0.51  fof(f127,plain,(
% 0.20/0.51    spl5_18 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 0.20/0.51  fof(f154,plain,(
% 0.20/0.51    spl5_23 <=> ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X3)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 0.20/0.51  fof(f162,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k1_xboole_0 = k9_subset_1(k1_xboole_0,X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))) ) | (~spl5_18 | ~spl5_23)),
% 0.20/0.51    inference(resolution,[],[f155,f128])).
% 0.20/0.51  fof(f128,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) ) | ~spl5_18),
% 0.20/0.51    inference(avatar_component_clause,[],[f127])).
% 0.20/0.51  fof(f155,plain,(
% 0.20/0.51    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X3) ) | ~spl5_23),
% 0.20/0.51    inference(avatar_component_clause,[],[f154])).
% 0.20/0.51  fof(f160,plain,(
% 0.20/0.51    spl5_24),
% 0.20/0.51    inference(avatar_split_clause,[],[f40,f158])).
% 0.20/0.51  fof(f40,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(sK2(X0,X1),X1) | v2_tex_2(X1,X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f17])).
% 0.20/0.51  fof(f156,plain,(
% 0.20/0.51    spl5_23 | ~spl5_8 | ~spl5_21),
% 0.20/0.51    inference(avatar_split_clause,[],[f148,f140,f80,f154])).
% 0.20/0.51  fof(f80,plain,(
% 0.20/0.51    spl5_8 <=> ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.20/0.51  fof(f140,plain,(
% 0.20/0.51    spl5_21 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | v1_xboole_0(X0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 0.20/0.51  fof(f148,plain,(
% 0.20/0.51    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X3) ) | (~spl5_8 | ~spl5_21)),
% 0.20/0.51    inference(resolution,[],[f141,f81])).
% 0.20/0.51  fof(f81,plain,(
% 0.20/0.51    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) ) | ~spl5_8),
% 0.20/0.51    inference(avatar_component_clause,[],[f80])).
% 0.20/0.51  fof(f141,plain,(
% 0.20/0.51    ( ! [X0] : (v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))) ) | ~spl5_21),
% 0.20/0.51    inference(avatar_component_clause,[],[f140])).
% 0.20/0.51  fof(f152,plain,(
% 0.20/0.51    spl5_22),
% 0.20/0.51    inference(avatar_split_clause,[],[f42,f150])).
% 0.20/0.51  fof(f42,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1) | v4_pre_topc(X1,X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f20])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (v4_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.51    inference(flattening,[],[f19])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) | ~v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f10])).
% 0.20/0.51  fof(f10,axiom,(
% 0.20/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_xboole_0(X1) => v4_pre_topc(X1,X0))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_pre_topc)).
% 0.20/0.51  fof(f142,plain,(
% 0.20/0.51    spl5_21 | ~spl5_10 | ~spl5_19),
% 0.20/0.51    inference(avatar_split_clause,[],[f134,f131,f88,f140])).
% 0.20/0.51  fof(f88,plain,(
% 0.20/0.51    spl5_10 <=> ! [X0] : (r2_hidden(sK4(X0),X0) | v1_xboole_0(X0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.20/0.51  fof(f131,plain,(
% 0.20/0.51    spl5_19 <=> ! [X1,X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | ~r2_hidden(X1,X0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 0.20/0.51  fof(f134,plain,(
% 0.20/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | v1_xboole_0(X0)) ) | (~spl5_10 | ~spl5_19)),
% 0.20/0.51    inference(resolution,[],[f132,f89])).
% 0.20/0.51  fof(f89,plain,(
% 0.20/0.51    ( ! [X0] : (r2_hidden(sK4(X0),X0) | v1_xboole_0(X0)) ) | ~spl5_10),
% 0.20/0.51    inference(avatar_component_clause,[],[f88])).
% 0.20/0.51  fof(f132,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))) ) | ~spl5_19),
% 0.20/0.51    inference(avatar_component_clause,[],[f131])).
% 0.20/0.51  fof(f138,plain,(
% 0.20/0.51    spl5_20),
% 0.20/0.51    inference(avatar_split_clause,[],[f48,f136])).
% 0.20/0.51  fof(f48,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f24])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.20/0.51  fof(f133,plain,(
% 0.20/0.51    spl5_19 | ~spl5_11 | ~spl5_15),
% 0.20/0.51    inference(avatar_split_clause,[],[f125,f114,f96,f131])).
% 0.20/0.51  fof(f114,plain,(
% 0.20/0.51    spl5_15 <=> ! [X1,X0,X2] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.20/0.51  fof(f125,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | ~r2_hidden(X1,X0)) ) | (~spl5_11 | ~spl5_15)),
% 0.20/0.51    inference(resolution,[],[f115,f97])).
% 0.20/0.51  fof(f115,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) ) | ~spl5_15),
% 0.20/0.51    inference(avatar_component_clause,[],[f114])).
% 0.20/0.51  fof(f129,plain,(
% 0.20/0.51    spl5_18),
% 0.20/0.51    inference(avatar_split_clause,[],[f47,f127])).
% 0.20/0.51  fof(f47,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f23])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).
% 0.20/0.51  fof(f120,plain,(
% 0.20/0.51    spl5_16),
% 0.20/0.51    inference(avatar_split_clause,[],[f46,f118])).
% 0.20/0.51  fof(f46,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X1) = X1) )),
% 0.20/0.51    inference(cnf_transformation,[],[f22])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f5])).
% 0.20/0.51  fof(f5,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X1) = X1)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k9_subset_1)).
% 0.20/0.51  fof(f116,plain,(
% 0.20/0.51    spl5_15),
% 0.20/0.51    inference(avatar_split_clause,[],[f50,f114])).
% 0.20/0.51  fof(f50,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f27])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f9])).
% 0.20/0.51  fof(f9,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 0.20/0.51  fof(f112,plain,(
% 0.20/0.51    spl5_14),
% 0.20/0.51    inference(avatar_split_clause,[],[f45,f110])).
% 0.20/0.51  fof(f45,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f21])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.20/0.51  fof(f103,plain,(
% 0.20/0.51    ~spl5_12 | ~spl5_1 | spl5_5 | ~spl5_8),
% 0.20/0.51    inference(avatar_split_clause,[],[f93,f80,f68,f52,f101])).
% 0.20/0.51  fof(f52,plain,(
% 0.20/0.51    spl5_1 <=> v1_xboole_0(sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.51  fof(f68,plain,(
% 0.20/0.51    spl5_5 <=> v2_tex_2(sK1,sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.20/0.51  fof(f93,plain,(
% 0.20/0.51    ~v2_tex_2(k1_xboole_0,sK0) | (~spl5_1 | spl5_5 | ~spl5_8)),
% 0.20/0.51    inference(backward_demodulation,[],[f69,f91])).
% 0.20/0.51  fof(f91,plain,(
% 0.20/0.51    k1_xboole_0 = sK1 | (~spl5_1 | ~spl5_8)),
% 0.20/0.51    inference(resolution,[],[f81,f53])).
% 0.20/0.51  fof(f53,plain,(
% 0.20/0.51    v1_xboole_0(sK1) | ~spl5_1),
% 0.20/0.51    inference(avatar_component_clause,[],[f52])).
% 0.20/0.51  fof(f69,plain,(
% 0.20/0.51    ~v2_tex_2(sK1,sK0) | spl5_5),
% 0.20/0.51    inference(avatar_component_clause,[],[f68])).
% 0.20/0.51  fof(f98,plain,(
% 0.20/0.51    spl5_11 | ~spl5_1 | ~spl5_8),
% 0.20/0.51    inference(avatar_split_clause,[],[f94,f80,f52,f96])).
% 0.20/0.51  fof(f94,plain,(
% 0.20/0.51    v1_xboole_0(k1_xboole_0) | (~spl5_1 | ~spl5_8)),
% 0.20/0.51    inference(backward_demodulation,[],[f53,f91])).
% 0.20/0.51  fof(f90,plain,(
% 0.20/0.51    spl5_10),
% 0.20/0.51    inference(avatar_split_clause,[],[f43,f88])).
% 0.20/0.51  fof(f43,plain,(
% 0.20/0.51    ( ! [X0] : (r2_hidden(sK4(X0),X0) | v1_xboole_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.20/0.51  fof(f82,plain,(
% 0.20/0.51    spl5_8),
% 0.20/0.51    inference(avatar_split_clause,[],[f41,f80])).
% 0.20/0.51  fof(f41,plain,(
% 0.20/0.51    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f18])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.20/0.51  fof(f78,plain,(
% 0.20/0.51    spl5_7),
% 0.20/0.51    inference(avatar_split_clause,[],[f34,f76])).
% 0.20/0.51  fof(f34,plain,(
% 0.20/0.51    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f7])).
% 0.20/0.51  fof(f7,axiom,(
% 0.20/0.51    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.20/0.51  fof(f70,plain,(
% 0.20/0.51    ~spl5_5),
% 0.20/0.51    inference(avatar_split_clause,[],[f30,f68])).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    ~v2_tex_2(sK1,sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f15])).
% 0.20/0.51  fof(f15,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.51    inference(flattening,[],[f14])).
% 0.20/0.51  fof(f14,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f13])).
% 0.20/0.51  fof(f13,negated_conjecture,(
% 0.20/0.51    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 0.20/0.51    inference(negated_conjecture,[],[f12])).
% 0.20/0.51  fof(f12,conjecture,(
% 0.20/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tex_2)).
% 0.20/0.51  fof(f66,plain,(
% 0.20/0.51    spl5_4),
% 0.20/0.51    inference(avatar_split_clause,[],[f33,f64])).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    l1_pre_topc(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f15])).
% 0.20/0.51  fof(f62,plain,(
% 0.20/0.51    spl5_3),
% 0.20/0.51    inference(avatar_split_clause,[],[f32,f60])).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    v2_pre_topc(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f15])).
% 0.20/0.51  fof(f54,plain,(
% 0.20/0.51    spl5_1),
% 0.20/0.51    inference(avatar_split_clause,[],[f28,f52])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    v1_xboole_0(sK1)),
% 0.20/0.51    inference(cnf_transformation,[],[f15])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (28434)------------------------------
% 0.20/0.51  % (28434)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (28434)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (28434)Memory used [KB]: 10746
% 0.20/0.51  % (28434)Time elapsed: 0.090 s
% 0.20/0.51  % (28434)------------------------------
% 0.20/0.51  % (28434)------------------------------
% 0.20/0.51  % (28424)Success in time 0.157 s
%------------------------------------------------------------------------------
