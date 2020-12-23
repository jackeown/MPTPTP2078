%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:18 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 216 expanded)
%              Number of leaves         :   35 (  91 expanded)
%              Depth                    :    7
%              Number of atoms          :  410 ( 795 expanded)
%              Number of equality atoms :   26 (  61 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f307,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f60,f64,f68,f76,f100,f104,f108,f112,f121,f135,f140,f145,f165,f170,f179,f183,f199,f214,f221,f238,f243,f247,f286,f295,f306])).

fof(f306,plain,
    ( ~ spl3_29
    | spl3_31
    | ~ spl3_36
    | spl3_44 ),
    inference(avatar_contradiction_clause,[],[f303])).

fof(f303,plain,
    ( $false
    | ~ spl3_29
    | spl3_31
    | ~ spl3_36
    | spl3_44 ),
    inference(unit_resulting_resolution,[],[f242,f192,f285,f178])).

fof(f178,plain,
    ( ! [X0,X1] :
        ( v1_xboole_0(X0)
        | r2_hidden(X1,X0)
        | ~ m1_subset_1(X1,X0) )
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f177])).

fof(f177,plain,
    ( spl3_29
  <=> ! [X1,X0] :
        ( v1_xboole_0(X0)
        | r2_hidden(X1,X0)
        | ~ m1_subset_1(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f285,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK0))
    | spl3_44 ),
    inference(avatar_component_clause,[],[f284])).

fof(f284,plain,
    ( spl3_44
  <=> v1_xboole_0(k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).

fof(f192,plain,
    ( ~ r2_hidden(sK1,k2_struct_0(sK0))
    | spl3_31 ),
    inference(avatar_component_clause,[],[f191])).

fof(f191,plain,
    ( spl3_31
  <=> r2_hidden(sK1,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f242,plain,
    ( m1_subset_1(sK1,k2_struct_0(sK0))
    | ~ spl3_36 ),
    inference(avatar_component_clause,[],[f241])).

fof(f241,plain,
    ( spl3_36
  <=> m1_subset_1(sK1,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f295,plain,
    ( ~ spl3_3
    | ~ spl3_11
    | spl3_43 ),
    inference(avatar_contradiction_clause,[],[f294])).

fof(f294,plain,
    ( $false
    | ~ spl3_3
    | ~ spl3_11
    | spl3_43 ),
    inference(subsumption_resolution,[],[f292,f67])).

fof(f67,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl3_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f292,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl3_11
    | spl3_43 ),
    inference(resolution,[],[f282,f99])).

fof(f99,plain,
    ( ! [X0] :
        ( l1_struct_0(X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl3_11
  <=> ! [X0] :
        ( ~ l1_pre_topc(X0)
        | l1_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f282,plain,
    ( ~ l1_struct_0(sK0)
    | spl3_43 ),
    inference(avatar_component_clause,[],[f281])).

fof(f281,plain,
    ( spl3_43
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).

fof(f286,plain,
    ( ~ spl3_43
    | ~ spl3_44
    | spl3_1
    | ~ spl3_21
    | ~ spl3_37 ),
    inference(avatar_split_clause,[],[f253,f245,f143,f58,f284,f281])).

fof(f58,plain,
    ( spl3_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f143,plain,
    ( spl3_21
  <=> ! [X0] :
        ( v2_struct_0(X0)
        | ~ l1_struct_0(X0)
        | ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f245,plain,
    ( spl3_37
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).

fof(f253,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | spl3_1
    | ~ spl3_21
    | ~ spl3_37 ),
    inference(subsumption_resolution,[],[f252,f59])).

fof(f59,plain,
    ( ~ v2_struct_0(sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f58])).

fof(f252,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_21
    | ~ spl3_37 ),
    inference(superposition,[],[f144,f246])).

fof(f246,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_37 ),
    inference(avatar_component_clause,[],[f245])).

fof(f144,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(u1_struct_0(X0))
        | ~ l1_struct_0(X0)
        | v2_struct_0(X0) )
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f143])).

fof(f247,plain,
    ( spl3_37
    | ~ spl3_3
    | ~ spl3_35 ),
    inference(avatar_split_clause,[],[f222,f219,f66,f245])).

fof(f219,plain,
    ( spl3_35
  <=> ! [X0] :
        ( k2_struct_0(X0) = u1_struct_0(X0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).

fof(f222,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_3
    | ~ spl3_35 ),
    inference(resolution,[],[f220,f67])).

fof(f220,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | k2_struct_0(X0) = u1_struct_0(X0) )
    | ~ spl3_35 ),
    inference(avatar_component_clause,[],[f219])).

fof(f243,plain,
    ( spl3_36
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_35 ),
    inference(avatar_split_clause,[],[f223,f219,f74,f66,f241])).

fof(f74,plain,
    ( spl3_5
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f223,plain,
    ( m1_subset_1(sK1,k2_struct_0(sK0))
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_35 ),
    inference(backward_demodulation,[],[f75,f222])).

fof(f75,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f74])).

fof(f238,plain,
    ( ~ spl3_3
    | ~ spl3_12
    | spl3_33
    | ~ spl3_35 ),
    inference(avatar_contradiction_clause,[],[f237])).

fof(f237,plain,
    ( $false
    | ~ spl3_3
    | ~ spl3_12
    | spl3_33
    | ~ spl3_35 ),
    inference(subsumption_resolution,[],[f234,f103])).

fof(f103,plain,
    ( ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl3_12
  <=> ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f234,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_3
    | spl3_33
    | ~ spl3_35 ),
    inference(backward_demodulation,[],[f198,f222])).

fof(f198,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_33 ),
    inference(avatar_component_clause,[],[f197])).

fof(f197,plain,
    ( spl3_33
  <=> m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f221,plain,
    ( spl3_35
    | ~ spl3_11
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f184,f138,f98,f219])).

fof(f138,plain,
    ( spl3_20
  <=> ! [X0] :
        ( ~ l1_struct_0(X0)
        | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f184,plain,
    ( ! [X0] :
        ( k2_struct_0(X0) = u1_struct_0(X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl3_11
    | ~ spl3_20 ),
    inference(resolution,[],[f139,f99])).

fof(f139,plain,
    ( ! [X0] :
        ( ~ l1_struct_0(X0)
        | k2_struct_0(X0) = u1_struct_0(X0) )
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f138])).

fof(f214,plain,
    ( ~ spl3_2
    | ~ spl3_3
    | ~ spl3_27
    | spl3_32 ),
    inference(avatar_contradiction_clause,[],[f213])).

fof(f213,plain,
    ( $false
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_27
    | spl3_32 ),
    inference(subsumption_resolution,[],[f212,f63])).

fof(f63,plain,
    ( v2_pre_topc(sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl3_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f212,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ spl3_3
    | ~ spl3_27
    | spl3_32 ),
    inference(subsumption_resolution,[],[f209,f67])).

fof(f209,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl3_27
    | spl3_32 ),
    inference(resolution,[],[f195,f169])).

fof(f169,plain,
    ( ! [X0] :
        ( v4_pre_topc(k2_struct_0(X0),X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f168])).

fof(f168,plain,
    ( spl3_27
  <=> ! [X0] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v4_pre_topc(k2_struct_0(X0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f195,plain,
    ( ~ v4_pre_topc(k2_struct_0(sK0),sK0)
    | spl3_32 ),
    inference(avatar_component_clause,[],[f194])).

fof(f194,plain,
    ( spl3_32
  <=> v4_pre_topc(k2_struct_0(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f199,plain,
    ( ~ spl3_31
    | ~ spl3_32
    | ~ spl3_33
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_26
    | ~ spl3_30 ),
    inference(avatar_split_clause,[],[f189,f181,f163,f66,f62,f197,f194,f191])).

fof(f163,plain,
    ( spl3_26
  <=> ! [X0] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v3_pre_topc(k2_struct_0(X0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f181,plain,
    ( spl3_30
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | ~ v4_pre_topc(X0,sK0)
        | ~ r2_hidden(sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f189,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_pre_topc(k2_struct_0(sK0),sK0)
    | ~ r2_hidden(sK1,k2_struct_0(sK0))
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_26
    | ~ spl3_30 ),
    inference(subsumption_resolution,[],[f188,f63])).

fof(f188,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_pre_topc(k2_struct_0(sK0),sK0)
    | ~ r2_hidden(sK1,k2_struct_0(sK0))
    | ~ spl3_3
    | ~ spl3_26
    | ~ spl3_30 ),
    inference(subsumption_resolution,[],[f187,f67])).

fof(f187,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_pre_topc(k2_struct_0(sK0),sK0)
    | ~ r2_hidden(sK1,k2_struct_0(sK0))
    | ~ spl3_26
    | ~ spl3_30 ),
    inference(resolution,[],[f164,f182])).

fof(f182,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_pre_topc(X0,sK0)
        | ~ r2_hidden(sK1,X0) )
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f181])).

fof(f164,plain,
    ( ! [X0] :
        ( v3_pre_topc(k2_struct_0(X0),X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f163])).

fof(f183,plain,
    ( spl3_30
    | ~ spl3_16
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f141,f133,f119,f181])).

fof(f119,plain,
    ( spl3_16
  <=> ! [X3] :
        ( r2_hidden(X3,k1_xboole_0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X3,sK0)
        | ~ v4_pre_topc(X3,sK0)
        | ~ r2_hidden(sK1,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f133,plain,
    ( spl3_19
  <=> ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f141,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | ~ v4_pre_topc(X0,sK0)
        | ~ r2_hidden(sK1,X0) )
    | ~ spl3_16
    | ~ spl3_19 ),
    inference(resolution,[],[f134,f120])).

fof(f120,plain,
    ( ! [X3] :
        ( r2_hidden(X3,k1_xboole_0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X3,sK0)
        | ~ v4_pre_topc(X3,sK0)
        | ~ r2_hidden(sK1,X3) )
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f119])).

fof(f134,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f133])).

fof(f179,plain,(
    spl3_29 ),
    inference(avatar_split_clause,[],[f45,f177])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f170,plain,(
    spl3_27 ),
    inference(avatar_split_clause,[],[f40,f168])).

fof(f40,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v4_pre_topc(k2_struct_0(X0),X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_pre_topc)).

fof(f165,plain,(
    spl3_26 ),
    inference(avatar_split_clause,[],[f39,f163])).

fof(f39,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v3_pre_topc(k2_struct_0(X0),X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).

fof(f145,plain,(
    spl3_21 ),
    inference(avatar_split_clause,[],[f38,f143])).

fof(f38,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f140,plain,(
    spl3_20 ),
    inference(avatar_split_clause,[],[f36,f138])).

fof(f36,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f135,plain,
    ( spl3_19
    | ~ spl3_13
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f131,f110,f106,f133])).

fof(f106,plain,
    ( spl3_13
  <=> ! [X1,X0] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f110,plain,
    ( spl3_14
  <=> ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f131,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl3_13
    | ~ spl3_14 ),
    inference(superposition,[],[f107,f111])).

fof(f111,plain,
    ( ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f110])).

fof(f107,plain,
    ( ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f106])).

fof(f121,plain,(
    spl3_16 ),
    inference(avatar_split_clause,[],[f52,f119])).

fof(f52,plain,(
    ! [X3] :
      ( r2_hidden(X3,k1_xboole_0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X3,sK0)
      | ~ v4_pre_topc(X3,sK0)
      | ~ r2_hidden(sK1,X3) ) ),
    inference(forward_demodulation,[],[f27,f29])).

fof(f29,plain,(
    k1_xboole_0 = sK2 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( r2_hidden(X3,X2)
                  <=> ( r2_hidden(X1,X3)
                      & v4_pre_topc(X3,X0)
                      & v3_pre_topc(X3,X0) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( r2_hidden(X3,X2)
                  <=> ( r2_hidden(X1,X3)
                      & v4_pre_topc(X3,X0)
                      & v3_pre_topc(X3,X0) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ~ ( k1_xboole_0 = X2
                    & ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ( r2_hidden(X3,X2)
                        <=> ( r2_hidden(X1,X3)
                            & v4_pre_topc(X3,X0)
                            & v3_pre_topc(X3,X0) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ~ ( k1_xboole_0 = X2
                  & ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                     => ( r2_hidden(X3,X2)
                      <=> ( r2_hidden(X1,X3)
                          & v4_pre_topc(X3,X0)
                          & v3_pre_topc(X3,X0) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_connsp_2)).

fof(f27,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X3,sK0)
      | ~ v4_pre_topc(X3,sK0)
      | ~ r2_hidden(sK1,X3)
      | r2_hidden(X3,sK2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f112,plain,(
    spl3_14 ),
    inference(avatar_split_clause,[],[f49,f110])).

fof(f49,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f108,plain,(
    spl3_13 ),
    inference(avatar_split_clause,[],[f41,f106])).

fof(f41,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f104,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f56,f102])).

% (22371)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
fof(f56,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f35,f34])).

fof(f34,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f35,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f100,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f37,f98])).

fof(f37,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f76,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f30,f74])).

fof(f30,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f68,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f33,f66])).

fof(f33,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f14])).

% (22370)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
fof(f64,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f32,f62])).

fof(f32,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f60,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f31,f58])).

fof(f31,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:20:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (22364)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.46  % (22373)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.46  % (22373)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.46  % (22378)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.46  % (22364)Refutation not found, incomplete strategy% (22364)------------------------------
% 0.20/0.46  % (22364)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (22381)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.46  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f307,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(avatar_sat_refutation,[],[f60,f64,f68,f76,f100,f104,f108,f112,f121,f135,f140,f145,f165,f170,f179,f183,f199,f214,f221,f238,f243,f247,f286,f295,f306])).
% 0.20/0.47  fof(f306,plain,(
% 0.20/0.47    ~spl3_29 | spl3_31 | ~spl3_36 | spl3_44),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f303])).
% 0.20/0.47  fof(f303,plain,(
% 0.20/0.47    $false | (~spl3_29 | spl3_31 | ~spl3_36 | spl3_44)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f242,f192,f285,f178])).
% 0.20/0.47  fof(f178,plain,(
% 0.20/0.47    ( ! [X0,X1] : (v1_xboole_0(X0) | r2_hidden(X1,X0) | ~m1_subset_1(X1,X0)) ) | ~spl3_29),
% 0.20/0.47    inference(avatar_component_clause,[],[f177])).
% 0.20/0.47  fof(f177,plain,(
% 0.20/0.47    spl3_29 <=> ! [X1,X0] : (v1_xboole_0(X0) | r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.20/0.47  fof(f285,plain,(
% 0.20/0.47    ~v1_xboole_0(k2_struct_0(sK0)) | spl3_44),
% 0.20/0.47    inference(avatar_component_clause,[],[f284])).
% 0.20/0.47  fof(f284,plain,(
% 0.20/0.47    spl3_44 <=> v1_xboole_0(k2_struct_0(sK0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).
% 0.20/0.47  fof(f192,plain,(
% 0.20/0.47    ~r2_hidden(sK1,k2_struct_0(sK0)) | spl3_31),
% 0.20/0.47    inference(avatar_component_clause,[],[f191])).
% 0.20/0.47  fof(f191,plain,(
% 0.20/0.47    spl3_31 <=> r2_hidden(sK1,k2_struct_0(sK0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 0.20/0.47  fof(f242,plain,(
% 0.20/0.47    m1_subset_1(sK1,k2_struct_0(sK0)) | ~spl3_36),
% 0.20/0.47    inference(avatar_component_clause,[],[f241])).
% 0.20/0.47  fof(f241,plain,(
% 0.20/0.47    spl3_36 <=> m1_subset_1(sK1,k2_struct_0(sK0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 0.20/0.47  fof(f295,plain,(
% 0.20/0.47    ~spl3_3 | ~spl3_11 | spl3_43),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f294])).
% 0.20/0.47  fof(f294,plain,(
% 0.20/0.47    $false | (~spl3_3 | ~spl3_11 | spl3_43)),
% 0.20/0.47    inference(subsumption_resolution,[],[f292,f67])).
% 0.20/0.47  fof(f67,plain,(
% 0.20/0.47    l1_pre_topc(sK0) | ~spl3_3),
% 0.20/0.47    inference(avatar_component_clause,[],[f66])).
% 0.20/0.47  fof(f66,plain,(
% 0.20/0.47    spl3_3 <=> l1_pre_topc(sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.47  fof(f292,plain,(
% 0.20/0.47    ~l1_pre_topc(sK0) | (~spl3_11 | spl3_43)),
% 0.20/0.47    inference(resolution,[],[f282,f99])).
% 0.20/0.47  fof(f99,plain,(
% 0.20/0.47    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) ) | ~spl3_11),
% 0.20/0.47    inference(avatar_component_clause,[],[f98])).
% 0.20/0.47  fof(f98,plain,(
% 0.20/0.47    spl3_11 <=> ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.20/0.47  fof(f282,plain,(
% 0.20/0.47    ~l1_struct_0(sK0) | spl3_43),
% 0.20/0.47    inference(avatar_component_clause,[],[f281])).
% 0.20/0.47  fof(f281,plain,(
% 0.20/0.47    spl3_43 <=> l1_struct_0(sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).
% 0.20/0.47  fof(f286,plain,(
% 0.20/0.47    ~spl3_43 | ~spl3_44 | spl3_1 | ~spl3_21 | ~spl3_37),
% 0.20/0.47    inference(avatar_split_clause,[],[f253,f245,f143,f58,f284,f281])).
% 0.20/0.47  fof(f58,plain,(
% 0.20/0.47    spl3_1 <=> v2_struct_0(sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.47  fof(f143,plain,(
% 0.20/0.47    spl3_21 <=> ! [X0] : (v2_struct_0(X0) | ~l1_struct_0(X0) | ~v1_xboole_0(u1_struct_0(X0)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.20/0.47  fof(f245,plain,(
% 0.20/0.47    spl3_37 <=> u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).
% 0.20/0.47  fof(f253,plain,(
% 0.20/0.47    ~v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(sK0) | (spl3_1 | ~spl3_21 | ~spl3_37)),
% 0.20/0.47    inference(subsumption_resolution,[],[f252,f59])).
% 0.20/0.47  fof(f59,plain,(
% 0.20/0.47    ~v2_struct_0(sK0) | spl3_1),
% 0.20/0.47    inference(avatar_component_clause,[],[f58])).
% 0.20/0.47  fof(f252,plain,(
% 0.20/0.47    ~v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | (~spl3_21 | ~spl3_37)),
% 0.20/0.47    inference(superposition,[],[f144,f246])).
% 0.20/0.47  fof(f246,plain,(
% 0.20/0.47    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_37),
% 0.20/0.47    inference(avatar_component_clause,[],[f245])).
% 0.20/0.47  fof(f144,plain,(
% 0.20/0.47    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) ) | ~spl3_21),
% 0.20/0.47    inference(avatar_component_clause,[],[f143])).
% 0.20/0.47  fof(f247,plain,(
% 0.20/0.47    spl3_37 | ~spl3_3 | ~spl3_35),
% 0.20/0.47    inference(avatar_split_clause,[],[f222,f219,f66,f245])).
% 0.20/0.47  fof(f219,plain,(
% 0.20/0.47    spl3_35 <=> ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).
% 0.20/0.47  fof(f222,plain,(
% 0.20/0.47    u1_struct_0(sK0) = k2_struct_0(sK0) | (~spl3_3 | ~spl3_35)),
% 0.20/0.47    inference(resolution,[],[f220,f67])).
% 0.20/0.47  fof(f220,plain,(
% 0.20/0.47    ( ! [X0] : (~l1_pre_topc(X0) | k2_struct_0(X0) = u1_struct_0(X0)) ) | ~spl3_35),
% 0.20/0.47    inference(avatar_component_clause,[],[f219])).
% 0.20/0.47  fof(f243,plain,(
% 0.20/0.47    spl3_36 | ~spl3_3 | ~spl3_5 | ~spl3_35),
% 0.20/0.47    inference(avatar_split_clause,[],[f223,f219,f74,f66,f241])).
% 0.20/0.47  fof(f74,plain,(
% 0.20/0.47    spl3_5 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.47  fof(f223,plain,(
% 0.20/0.47    m1_subset_1(sK1,k2_struct_0(sK0)) | (~spl3_3 | ~spl3_5 | ~spl3_35)),
% 0.20/0.47    inference(backward_demodulation,[],[f75,f222])).
% 0.20/0.47  fof(f75,plain,(
% 0.20/0.47    m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl3_5),
% 0.20/0.47    inference(avatar_component_clause,[],[f74])).
% 0.20/0.47  fof(f238,plain,(
% 0.20/0.47    ~spl3_3 | ~spl3_12 | spl3_33 | ~spl3_35),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f237])).
% 0.20/0.47  fof(f237,plain,(
% 0.20/0.47    $false | (~spl3_3 | ~spl3_12 | spl3_33 | ~spl3_35)),
% 0.20/0.47    inference(subsumption_resolution,[],[f234,f103])).
% 0.20/0.47  fof(f103,plain,(
% 0.20/0.47    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) ) | ~spl3_12),
% 0.20/0.47    inference(avatar_component_clause,[],[f102])).
% 0.20/0.47  fof(f102,plain,(
% 0.20/0.47    spl3_12 <=> ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.20/0.47  fof(f234,plain,(
% 0.20/0.47    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | (~spl3_3 | spl3_33 | ~spl3_35)),
% 0.20/0.47    inference(backward_demodulation,[],[f198,f222])).
% 0.20/0.47  fof(f198,plain,(
% 0.20/0.47    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_33),
% 0.20/0.47    inference(avatar_component_clause,[],[f197])).
% 0.20/0.47  fof(f197,plain,(
% 0.20/0.47    spl3_33 <=> m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 0.20/0.47  fof(f221,plain,(
% 0.20/0.47    spl3_35 | ~spl3_11 | ~spl3_20),
% 0.20/0.47    inference(avatar_split_clause,[],[f184,f138,f98,f219])).
% 0.20/0.47  fof(f138,plain,(
% 0.20/0.47    spl3_20 <=> ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.20/0.47  fof(f184,plain,(
% 0.20/0.47    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_pre_topc(X0)) ) | (~spl3_11 | ~spl3_20)),
% 0.20/0.47    inference(resolution,[],[f139,f99])).
% 0.20/0.47  fof(f139,plain,(
% 0.20/0.47    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) ) | ~spl3_20),
% 0.20/0.47    inference(avatar_component_clause,[],[f138])).
% 0.20/0.47  fof(f214,plain,(
% 0.20/0.47    ~spl3_2 | ~spl3_3 | ~spl3_27 | spl3_32),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f213])).
% 0.20/0.47  fof(f213,plain,(
% 0.20/0.47    $false | (~spl3_2 | ~spl3_3 | ~spl3_27 | spl3_32)),
% 0.20/0.47    inference(subsumption_resolution,[],[f212,f63])).
% 0.20/0.47  fof(f63,plain,(
% 0.20/0.47    v2_pre_topc(sK0) | ~spl3_2),
% 0.20/0.47    inference(avatar_component_clause,[],[f62])).
% 0.20/0.47  fof(f62,plain,(
% 0.20/0.47    spl3_2 <=> v2_pre_topc(sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.47  fof(f212,plain,(
% 0.20/0.47    ~v2_pre_topc(sK0) | (~spl3_3 | ~spl3_27 | spl3_32)),
% 0.20/0.47    inference(subsumption_resolution,[],[f209,f67])).
% 0.20/0.47  fof(f209,plain,(
% 0.20/0.47    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl3_27 | spl3_32)),
% 0.20/0.47    inference(resolution,[],[f195,f169])).
% 0.20/0.47  fof(f169,plain,(
% 0.20/0.47    ( ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl3_27),
% 0.20/0.47    inference(avatar_component_clause,[],[f168])).
% 0.20/0.47  fof(f168,plain,(
% 0.20/0.47    spl3_27 <=> ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v4_pre_topc(k2_struct_0(X0),X0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 0.20/0.47  fof(f195,plain,(
% 0.20/0.47    ~v4_pre_topc(k2_struct_0(sK0),sK0) | spl3_32),
% 0.20/0.47    inference(avatar_component_clause,[],[f194])).
% 0.20/0.47  fof(f194,plain,(
% 0.20/0.47    spl3_32 <=> v4_pre_topc(k2_struct_0(sK0),sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 0.20/0.47  fof(f199,plain,(
% 0.20/0.47    ~spl3_31 | ~spl3_32 | ~spl3_33 | ~spl3_2 | ~spl3_3 | ~spl3_26 | ~spl3_30),
% 0.20/0.47    inference(avatar_split_clause,[],[f189,f181,f163,f66,f62,f197,f194,f191])).
% 0.20/0.47  fof(f163,plain,(
% 0.20/0.47    spl3_26 <=> ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v3_pre_topc(k2_struct_0(X0),X0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.20/0.47  fof(f181,plain,(
% 0.20/0.47    spl3_30 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | ~v4_pre_topc(X0,sK0) | ~r2_hidden(sK1,X0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.20/0.47  fof(f189,plain,(
% 0.20/0.47    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(k2_struct_0(sK0),sK0) | ~r2_hidden(sK1,k2_struct_0(sK0)) | (~spl3_2 | ~spl3_3 | ~spl3_26 | ~spl3_30)),
% 0.20/0.47    inference(subsumption_resolution,[],[f188,f63])).
% 0.20/0.47  fof(f188,plain,(
% 0.20/0.47    ~v2_pre_topc(sK0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(k2_struct_0(sK0),sK0) | ~r2_hidden(sK1,k2_struct_0(sK0)) | (~spl3_3 | ~spl3_26 | ~spl3_30)),
% 0.20/0.47    inference(subsumption_resolution,[],[f187,f67])).
% 0.20/0.47  fof(f187,plain,(
% 0.20/0.47    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(k2_struct_0(sK0),sK0) | ~r2_hidden(sK1,k2_struct_0(sK0)) | (~spl3_26 | ~spl3_30)),
% 0.20/0.47    inference(resolution,[],[f164,f182])).
% 0.20/0.47  fof(f182,plain,(
% 0.20/0.47    ( ! [X0] : (~v3_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X0,sK0) | ~r2_hidden(sK1,X0)) ) | ~spl3_30),
% 0.20/0.47    inference(avatar_component_clause,[],[f181])).
% 0.20/0.47  fof(f164,plain,(
% 0.20/0.47    ( ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl3_26),
% 0.20/0.47    inference(avatar_component_clause,[],[f163])).
% 0.20/0.47  fof(f183,plain,(
% 0.20/0.47    spl3_30 | ~spl3_16 | ~spl3_19),
% 0.20/0.47    inference(avatar_split_clause,[],[f141,f133,f119,f181])).
% 0.20/0.47  fof(f119,plain,(
% 0.20/0.47    spl3_16 <=> ! [X3] : (r2_hidden(X3,k1_xboole_0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X3,sK0) | ~v4_pre_topc(X3,sK0) | ~r2_hidden(sK1,X3))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.20/0.47  fof(f133,plain,(
% 0.20/0.47    spl3_19 <=> ! [X0] : ~r2_hidden(X0,k1_xboole_0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.20/0.47  fof(f141,plain,(
% 0.20/0.47    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | ~v4_pre_topc(X0,sK0) | ~r2_hidden(sK1,X0)) ) | (~spl3_16 | ~spl3_19)),
% 0.20/0.47    inference(resolution,[],[f134,f120])).
% 0.20/0.47  fof(f120,plain,(
% 0.20/0.47    ( ! [X3] : (r2_hidden(X3,k1_xboole_0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X3,sK0) | ~v4_pre_topc(X3,sK0) | ~r2_hidden(sK1,X3)) ) | ~spl3_16),
% 0.20/0.47    inference(avatar_component_clause,[],[f119])).
% 0.20/0.47  fof(f134,plain,(
% 0.20/0.47    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl3_19),
% 0.20/0.47    inference(avatar_component_clause,[],[f133])).
% 0.20/0.47  fof(f179,plain,(
% 0.20/0.47    spl3_29),
% 0.20/0.47    inference(avatar_split_clause,[],[f45,f177])).
% 0.20/0.47  fof(f45,plain,(
% 0.20/0.47    ( ! [X0,X1] : (v1_xboole_0(X0) | r2_hidden(X1,X0) | ~m1_subset_1(X1,X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f23])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.20/0.47  fof(f170,plain,(
% 0.20/0.47    spl3_27),
% 0.20/0.47    inference(avatar_split_clause,[],[f40,f168])).
% 0.20/0.47  fof(f40,plain,(
% 0.20/0.47    ( ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v4_pre_topc(k2_struct_0(X0),X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f22])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.47    inference(flattening,[],[f21])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f9])).
% 0.20/0.47  fof(f9,axiom,(
% 0.20/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_struct_0(X0),X0))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_pre_topc)).
% 0.20/0.47  fof(f165,plain,(
% 0.20/0.47    spl3_26),
% 0.20/0.47    inference(avatar_split_clause,[],[f39,f163])).
% 0.20/0.47  fof(f39,plain,(
% 0.20/0.47    ( ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v3_pre_topc(k2_struct_0(X0),X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f20])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.47    inference(flattening,[],[f19])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f10])).
% 0.20/0.47  fof(f10,axiom,(
% 0.20/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).
% 0.20/0.47  fof(f145,plain,(
% 0.20/0.47    spl3_21),
% 0.20/0.47    inference(avatar_split_clause,[],[f38,f143])).
% 0.20/0.47  fof(f38,plain,(
% 0.20/0.47    ( ! [X0] : (v2_struct_0(X0) | ~l1_struct_0(X0) | ~v1_xboole_0(u1_struct_0(X0))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f18])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.47    inference(flattening,[],[f17])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f8])).
% 0.20/0.47  fof(f8,axiom,(
% 0.20/0.47    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.20/0.47  fof(f140,plain,(
% 0.20/0.47    spl3_20),
% 0.20/0.47    inference(avatar_split_clause,[],[f36,f138])).
% 0.20/0.47  fof(f36,plain,(
% 0.20/0.47    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f15])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f6])).
% 0.20/0.47  fof(f6,axiom,(
% 0.20/0.47    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.20/0.47  fof(f135,plain,(
% 0.20/0.47    spl3_19 | ~spl3_13 | ~spl3_14),
% 0.20/0.47    inference(avatar_split_clause,[],[f131,f110,f106,f133])).
% 0.20/0.47  fof(f106,plain,(
% 0.20/0.47    spl3_13 <=> ! [X1,X0] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.20/0.47  fof(f110,plain,(
% 0.20/0.47    spl3_14 <=> ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.20/0.47  fof(f131,plain,(
% 0.20/0.47    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | (~spl3_13 | ~spl3_14)),
% 0.20/0.47    inference(superposition,[],[f107,f111])).
% 0.20/0.47  fof(f111,plain,(
% 0.20/0.47    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) ) | ~spl3_14),
% 0.20/0.47    inference(avatar_component_clause,[],[f110])).
% 0.20/0.47  fof(f107,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) ) | ~spl3_13),
% 0.20/0.47    inference(avatar_component_clause,[],[f106])).
% 0.20/0.47  fof(f121,plain,(
% 0.20/0.47    spl3_16),
% 0.20/0.47    inference(avatar_split_clause,[],[f52,f119])).
% 0.20/0.47  fof(f52,plain,(
% 0.20/0.47    ( ! [X3] : (r2_hidden(X3,k1_xboole_0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X3,sK0) | ~v4_pre_topc(X3,sK0) | ~r2_hidden(sK1,X3)) )),
% 0.20/0.47    inference(forward_demodulation,[],[f27,f29])).
% 0.20/0.47  fof(f29,plain,(
% 0.20/0.47    k1_xboole_0 = sK2),
% 0.20/0.47    inference(cnf_transformation,[],[f14])).
% 0.20/0.47  fof(f14,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : ((r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.47    inference(flattening,[],[f13])).
% 0.20/0.47  fof(f13,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : (? [X2] : ((k1_xboole_0 = X2 & ! [X3] : ((r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f12])).
% 0.20/0.47  fof(f12,negated_conjecture,(
% 0.20/0.47    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X2 & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))))))))),
% 0.20/0.47    inference(negated_conjecture,[],[f11])).
% 0.20/0.47  fof(f11,conjecture,(
% 0.20/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X2 & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))))))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_connsp_2)).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X3,sK0) | ~v4_pre_topc(X3,sK0) | ~r2_hidden(sK1,X3) | r2_hidden(X3,sK2)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f14])).
% 0.20/0.47  fof(f112,plain,(
% 0.20/0.47    spl3_14),
% 0.20/0.47    inference(avatar_split_clause,[],[f49,f110])).
% 0.20/0.47  fof(f49,plain,(
% 0.20/0.47    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.20/0.47    inference(equality_resolution,[],[f48])).
% 0.20/0.47  fof(f48,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k1_xboole_0 != X1 | k2_zfmisc_1(X0,X1) = k1_xboole_0) )),
% 0.20/0.47    inference(cnf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.47  fof(f108,plain,(
% 0.20/0.47    spl3_13),
% 0.20/0.47    inference(avatar_split_clause,[],[f41,f106])).
% 0.20/0.47  fof(f41,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 0.20/0.47  fof(f104,plain,(
% 0.20/0.47    spl3_12),
% 0.20/0.47    inference(avatar_split_clause,[],[f56,f102])).
% 0.20/0.47  % (22371)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.47  fof(f56,plain,(
% 0.20/0.47    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.20/0.47    inference(forward_demodulation,[],[f35,f34])).
% 0.20/0.47  fof(f34,plain,(
% 0.20/0.47    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.20/0.47    inference(cnf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,axiom,(
% 0.20/0.47    ! [X0] : k2_subset_1(X0) = X0),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.20/0.47  fof(f35,plain,(
% 0.20/0.47    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f5])).
% 0.20/0.47  fof(f5,axiom,(
% 0.20/0.47    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.20/0.47  fof(f100,plain,(
% 0.20/0.47    spl3_11),
% 0.20/0.47    inference(avatar_split_clause,[],[f37,f98])).
% 0.20/0.47  fof(f37,plain,(
% 0.20/0.47    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f16])).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f7])).
% 0.20/0.47  fof(f7,axiom,(
% 0.20/0.47    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.20/0.47  fof(f76,plain,(
% 0.20/0.47    spl3_5),
% 0.20/0.47    inference(avatar_split_clause,[],[f30,f74])).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.47    inference(cnf_transformation,[],[f14])).
% 0.20/0.47  fof(f68,plain,(
% 0.20/0.47    spl3_3),
% 0.20/0.47    inference(avatar_split_clause,[],[f33,f66])).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    l1_pre_topc(sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f14])).
% 0.20/0.47  % (22370)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.47  fof(f64,plain,(
% 0.20/0.47    spl3_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f32,f62])).
% 0.20/0.47  fof(f32,plain,(
% 0.20/0.47    v2_pre_topc(sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f14])).
% 0.20/0.47  fof(f60,plain,(
% 0.20/0.47    ~spl3_1),
% 0.20/0.47    inference(avatar_split_clause,[],[f31,f58])).
% 0.20/0.47  fof(f31,plain,(
% 0.20/0.47    ~v2_struct_0(sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f14])).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (22373)------------------------------
% 0.20/0.47  % (22373)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (22373)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (22373)Memory used [KB]: 10746
% 0.20/0.47  % (22373)Time elapsed: 0.065 s
% 0.20/0.47  % (22373)------------------------------
% 0.20/0.47  % (22373)------------------------------
% 0.20/0.47  % (22363)Success in time 0.117 s
%------------------------------------------------------------------------------
