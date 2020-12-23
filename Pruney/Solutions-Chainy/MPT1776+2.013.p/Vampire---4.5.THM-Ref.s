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
% DateTime   : Thu Dec  3 13:19:00 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  197 ( 571 expanded)
%              Number of leaves         :   52 ( 303 expanded)
%              Depth                    :   10
%              Number of atoms          : 1363 (8492 expanded)
%              Number of equality atoms :   41 ( 448 expanded)
%              Maximal formula depth    :   28 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f341,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f95,f98,f102,f106,f110,f114,f122,f126,f130,f134,f138,f142,f143,f147,f151,f155,f159,f163,f167,f171,f178,f183,f201,f207,f212,f216,f228,f241,f251,f257,f263,f289,f296,f309,f320,f336])).

fof(f336,plain,
    ( ~ spl8_7
    | ~ spl8_15
    | spl8_40 ),
    inference(avatar_split_clause,[],[f333,f318,f149,f116])).

fof(f116,plain,
    ( spl8_7
  <=> m1_pre_topc(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f149,plain,
    ( spl8_15
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f318,plain,
    ( spl8_40
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_40])])).

fof(f333,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | ~ spl8_15
    | spl8_40 ),
    inference(resolution,[],[f332,f150])).

fof(f150,plain,
    ( l1_pre_topc(sK1)
    | ~ spl8_15 ),
    inference(avatar_component_clause,[],[f149])).

fof(f332,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK2,X0) )
    | spl8_40 ),
    inference(resolution,[],[f319,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f319,plain,
    ( ~ l1_pre_topc(sK2)
    | spl8_40 ),
    inference(avatar_component_clause,[],[f318])).

fof(f320,plain,
    ( ~ spl8_40
    | spl8_14
    | ~ spl8_6
    | ~ spl8_39 ),
    inference(avatar_split_clause,[],[f314,f307,f112,f145,f318])).

fof(f145,plain,
    ( spl8_14
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f112,plain,
    ( spl8_6
  <=> m1_pre_topc(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f307,plain,
    ( spl8_39
  <=> ! [X0] :
        ( v1_xboole_0(u1_struct_0(X0))
        | ~ m1_pre_topc(X0,sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_39])])).

fof(f314,plain,
    ( v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | ~ spl8_6
    | ~ spl8_39 ),
    inference(resolution,[],[f313,f113])).

fof(f113,plain,
    ( m1_pre_topc(sK2,sK3)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f112])).

fof(f313,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK3)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl8_39 ),
    inference(resolution,[],[f310,f66])).

fof(f66,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f310,plain,
    ( ! [X0] :
        ( ~ l1_struct_0(X0)
        | ~ m1_pre_topc(X0,sK3)
        | v2_struct_0(X0) )
    | ~ spl8_39 ),
    inference(resolution,[],[f308,f69])).

fof(f69,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f308,plain,
    ( ! [X0] :
        ( v1_xboole_0(u1_struct_0(X0))
        | ~ m1_pre_topc(X0,sK3) )
    | ~ spl8_39 ),
    inference(avatar_component_clause,[],[f307])).

fof(f309,plain,
    ( ~ spl8_28
    | spl8_39
    | ~ spl8_26 ),
    inference(avatar_split_clause,[],[f303,f236,f307,f246])).

fof(f246,plain,
    ( spl8_28
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).

fof(f236,plain,
    ( spl8_26
  <=> v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).

fof(f303,plain,
    ( ! [X0] :
        ( v1_xboole_0(u1_struct_0(X0))
        | ~ m1_pre_topc(X0,sK3)
        | ~ l1_pre_topc(sK3) )
    | ~ spl8_26 ),
    inference(resolution,[],[f302,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f302,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
        | v1_xboole_0(X1) )
    | ~ spl8_26 ),
    inference(resolution,[],[f237,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f237,plain,
    ( v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl8_26 ),
    inference(avatar_component_clause,[],[f236])).

fof(f296,plain,
    ( ~ spl8_12
    | ~ spl8_15
    | spl8_17
    | ~ spl8_21
    | ~ spl8_16
    | ~ spl8_36 ),
    inference(avatar_split_clause,[],[f294,f287,f153,f176,f157,f149,f136])).

fof(f136,plain,
    ( spl8_12
  <=> m1_pre_topc(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f157,plain,
    ( spl8_17
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f176,plain,
    ( spl8_21
  <=> r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).

fof(f153,plain,
    ( spl8_16
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f287,plain,
    ( spl8_36
  <=> ! [X0] :
        ( ~ v2_pre_topc(X0)
        | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(X0,sK0,sK3,sK2,sK4),sK5)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK3,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_36])])).

fof(f294,plain,
    ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK5)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ spl8_16
    | ~ spl8_36 ),
    inference(resolution,[],[f288,f154])).

fof(f154,plain,
    ( v2_pre_topc(sK1)
    | ~ spl8_16 ),
    inference(avatar_component_clause,[],[f153])).

fof(f288,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(X0)
        | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(X0,sK0,sK3,sK2,sK4),sK5)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK3,X0) )
    | ~ spl8_36 ),
    inference(avatar_component_clause,[],[f287])).

fof(f289,plain,
    ( ~ spl8_7
    | ~ spl8_6
    | spl8_36
    | ~ spl8_22
    | spl8_14
    | ~ spl8_8
    | ~ spl8_30 ),
    inference(avatar_split_clause,[],[f284,f261,f120,f145,f181,f287,f112,f116])).

fof(f181,plain,
    ( spl8_22
  <=> m1_subset_1(sK5,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).

fof(f120,plain,
    ( spl8_8
  <=> v1_tsep_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f261,plain,
    ( spl8_30
  <=> ! [X1,X0] :
        ( ~ v1_tsep_1(X0,sK1)
        | v2_struct_0(X0)
        | ~ m1_subset_1(sK5,u1_struct_0(X0))
        | ~ v2_pre_topc(X1)
        | ~ m1_pre_topc(sK3,X1)
        | ~ l1_pre_topc(X1)
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_pre_topc(X0,sK1)
        | v2_struct_0(X1)
        | ~ r1_tmap_1(X0,sK0,k3_tmap_1(X1,sK0,sK3,X0,sK4),sK5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).

fof(f284,plain,
    ( ! [X0] :
        ( v2_struct_0(sK2)
        | ~ m1_subset_1(sK5,u1_struct_0(sK2))
        | ~ v2_pre_topc(X0)
        | ~ m1_pre_topc(sK3,X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK2,sK3)
        | ~ m1_pre_topc(sK2,sK1)
        | v2_struct_0(X0)
        | ~ r1_tmap_1(sK2,sK0,k3_tmap_1(X0,sK0,sK3,sK2,sK4),sK5) )
    | ~ spl8_8
    | ~ spl8_30 ),
    inference(resolution,[],[f262,f121])).

fof(f121,plain,
    ( v1_tsep_1(sK2,sK1)
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f120])).

fof(f262,plain,
    ( ! [X0,X1] :
        ( ~ v1_tsep_1(X0,sK1)
        | v2_struct_0(X0)
        | ~ m1_subset_1(sK5,u1_struct_0(X0))
        | ~ v2_pre_topc(X1)
        | ~ m1_pre_topc(sK3,X1)
        | ~ l1_pre_topc(X1)
        | ~ m1_pre_topc(X0,sK3)
        | ~ m1_pre_topc(X0,sK1)
        | v2_struct_0(X1)
        | ~ r1_tmap_1(X0,sK0,k3_tmap_1(X1,sK0,sK3,X0,sK4),sK5) )
    | ~ spl8_30 ),
    inference(avatar_component_clause,[],[f261])).

fof(f263,plain,
    ( spl8_17
    | ~ spl8_12
    | spl8_30
    | ~ spl8_15
    | ~ spl8_16
    | ~ spl8_29 ),
    inference(avatar_split_clause,[],[f258,f249,f153,f149,f261,f136,f157])).

fof(f249,plain,
    ( spl8_29
  <=> ! [X1,X0,X2] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_tsep_1(X2,X0)
        | ~ m1_pre_topc(sK3,X0)
        | ~ r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,sK3,X2,sK4),sK5)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X2,X0)
        | ~ m1_pre_topc(X2,sK3)
        | ~ l1_pre_topc(X1)
        | ~ m1_pre_topc(sK3,X1)
        | ~ v2_pre_topc(X1)
        | ~ m1_subset_1(sK5,u1_struct_0(X2))
        | v2_struct_0(X2)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).

fof(f258,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(sK1)
        | ~ v1_tsep_1(X0,sK1)
        | ~ m1_pre_topc(sK3,sK1)
        | ~ r1_tmap_1(X0,sK0,k3_tmap_1(X1,sK0,sK3,X0,sK4),sK5)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X0,sK1)
        | ~ m1_pre_topc(X0,sK3)
        | ~ l1_pre_topc(X1)
        | ~ m1_pre_topc(sK3,X1)
        | ~ v2_pre_topc(X1)
        | ~ m1_subset_1(sK5,u1_struct_0(X0))
        | v2_struct_0(X0)
        | v2_struct_0(sK1) )
    | ~ spl8_16
    | ~ spl8_29 ),
    inference(resolution,[],[f250,f154])).

fof(f250,plain,
    ( ! [X2,X0,X1] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_tsep_1(X2,X0)
        | ~ m1_pre_topc(sK3,X0)
        | ~ r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,sK3,X2,sK4),sK5)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X2,X0)
        | ~ m1_pre_topc(X2,sK3)
        | ~ l1_pre_topc(X1)
        | ~ m1_pre_topc(sK3,X1)
        | ~ v2_pre_topc(X1)
        | ~ m1_subset_1(sK5,u1_struct_0(X2))
        | v2_struct_0(X2)
        | v2_struct_0(X0) )
    | ~ spl8_29 ),
    inference(avatar_component_clause,[],[f249])).

fof(f257,plain,
    ( ~ spl8_15
    | ~ spl8_12
    | spl8_28 ),
    inference(avatar_split_clause,[],[f253,f246,f136,f149])).

fof(f253,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ spl8_12
    | spl8_28 ),
    inference(resolution,[],[f252,f137])).

fof(f137,plain,
    ( m1_pre_topc(sK3,sK1)
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f136])).

fof(f252,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK3,X0)
        | ~ l1_pre_topc(X0) )
    | spl8_28 ),
    inference(resolution,[],[f247,f67])).

fof(f247,plain,
    ( ~ l1_pre_topc(sK3)
    | spl8_28 ),
    inference(avatar_component_clause,[],[f246])).

fof(f251,plain,
    ( ~ spl8_28
    | spl8_29
    | ~ spl8_27 ),
    inference(avatar_split_clause,[],[f244,f239,f249,f246])).

fof(f239,plain,
    ( spl8_27
  <=> ! [X3,X5,X4] :
        ( ~ v2_pre_topc(X3)
        | ~ m1_subset_1(u1_struct_0(X4),k1_zfmisc_1(u1_struct_0(sK3)))
        | v2_struct_0(X3)
        | v2_struct_0(X5)
        | ~ r1_tmap_1(X4,sK0,k3_tmap_1(X5,sK0,sK3,X4,sK4),sK5)
        | v2_struct_0(X4)
        | ~ m1_subset_1(sK5,u1_struct_0(X4))
        | ~ v2_pre_topc(X5)
        | ~ m1_pre_topc(sK3,X5)
        | ~ l1_pre_topc(X5)
        | ~ m1_pre_topc(X4,sK3)
        | ~ m1_pre_topc(sK3,X3)
        | ~ m1_pre_topc(X4,X3)
        | ~ v1_tsep_1(X4,X3)
        | ~ l1_pre_topc(X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).

fof(f244,plain,
    ( ! [X2,X0,X1] :
        ( ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | v2_struct_0(X1)
        | ~ r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,sK3,X2,sK4),sK5)
        | v2_struct_0(X2)
        | ~ m1_subset_1(sK5,u1_struct_0(X2))
        | ~ v2_pre_topc(X1)
        | ~ m1_pre_topc(sK3,X1)
        | ~ l1_pre_topc(X1)
        | ~ m1_pre_topc(X2,sK3)
        | ~ m1_pre_topc(sK3,X0)
        | ~ m1_pre_topc(X2,X0)
        | ~ v1_tsep_1(X2,X0)
        | ~ l1_pre_topc(X0)
        | ~ l1_pre_topc(sK3) )
    | ~ spl8_27 ),
    inference(duplicate_literal_removal,[],[f242])).

fof(f242,plain,
    ( ! [X2,X0,X1] :
        ( ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | v2_struct_0(X1)
        | ~ r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,sK3,X2,sK4),sK5)
        | v2_struct_0(X2)
        | ~ m1_subset_1(sK5,u1_struct_0(X2))
        | ~ v2_pre_topc(X1)
        | ~ m1_pre_topc(sK3,X1)
        | ~ l1_pre_topc(X1)
        | ~ m1_pre_topc(X2,sK3)
        | ~ m1_pre_topc(sK3,X0)
        | ~ m1_pre_topc(X2,X0)
        | ~ v1_tsep_1(X2,X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X2,sK3)
        | ~ l1_pre_topc(sK3) )
    | ~ spl8_27 ),
    inference(resolution,[],[f240,f68])).

fof(f240,plain,
    ( ! [X4,X5,X3] :
        ( ~ m1_subset_1(u1_struct_0(X4),k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ v2_pre_topc(X3)
        | v2_struct_0(X3)
        | v2_struct_0(X5)
        | ~ r1_tmap_1(X4,sK0,k3_tmap_1(X5,sK0,sK3,X4,sK4),sK5)
        | v2_struct_0(X4)
        | ~ m1_subset_1(sK5,u1_struct_0(X4))
        | ~ v2_pre_topc(X5)
        | ~ m1_pre_topc(sK3,X5)
        | ~ l1_pre_topc(X5)
        | ~ m1_pre_topc(X4,sK3)
        | ~ m1_pre_topc(sK3,X3)
        | ~ m1_pre_topc(X4,X3)
        | ~ v1_tsep_1(X4,X3)
        | ~ l1_pre_topc(X3) )
    | ~ spl8_27 ),
    inference(avatar_component_clause,[],[f239])).

fof(f241,plain,
    ( spl8_26
    | spl8_27
    | ~ spl8_25 ),
    inference(avatar_split_clause,[],[f234,f210,f239,f236])).

fof(f210,plain,
    ( spl8_25
  <=> ! [X1,X0,X2] :
        ( ~ m1_pre_topc(X0,sK3)
        | v2_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | ~ v1_tsep_1(X0,X2)
        | ~ m1_pre_topc(X0,X2)
        | ~ m1_pre_topc(sK3,X2)
        | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(sK3))
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ m1_subset_1(sK5,u1_struct_0(X0))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK3,X1)
        | ~ r1_tmap_1(X0,sK0,k3_tmap_1(X1,sK0,sK3,X0,sK4),sK5)
        | v2_struct_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).

fof(f234,plain,
    ( ! [X4,X5,X3] :
        ( ~ v2_pre_topc(X3)
        | ~ l1_pre_topc(X3)
        | ~ v1_tsep_1(X4,X3)
        | ~ m1_pre_topc(X4,X3)
        | ~ m1_pre_topc(sK3,X3)
        | ~ m1_pre_topc(X4,sK3)
        | ~ v2_pre_topc(X5)
        | ~ l1_pre_topc(X5)
        | ~ m1_subset_1(sK5,u1_struct_0(X4))
        | v2_struct_0(X4)
        | ~ m1_pre_topc(sK3,X5)
        | ~ r1_tmap_1(X4,sK0,k3_tmap_1(X5,sK0,sK3,X4,sK4),sK5)
        | v2_struct_0(X5)
        | v2_struct_0(X3)
        | ~ m1_subset_1(u1_struct_0(X4),k1_zfmisc_1(u1_struct_0(sK3)))
        | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK3))) )
    | ~ spl8_25 ),
    inference(resolution,[],[f232,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f232,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_tsep_1(X1,X0)
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(sK3,X0)
        | ~ m1_pre_topc(X1,sK3)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | ~ m1_subset_1(sK5,u1_struct_0(X1))
        | v2_struct_0(X1)
        | ~ m1_pre_topc(sK3,X2)
        | ~ r1_tmap_1(X1,sK0,k3_tmap_1(X2,sK0,sK3,X1,sK4),sK5)
        | v2_struct_0(X2)
        | v2_struct_0(X0) )
    | ~ spl8_25 ),
    inference(resolution,[],[f211,f88])).

fof(f88,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK7(X0,X1),X0)
            | ~ r2_hidden(sK7(X0,X1),X1) )
          & ( r1_tarski(sK7(X0,X1),X0)
            | r2_hidden(sK7(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f42,f43])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK7(X0,X1),X0)
          | ~ r2_hidden(sK7(X0,X1),X1) )
        & ( r1_tarski(sK7(X0,X1),X0)
          | r2_hidden(sK7(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f211,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(sK3))
        | v2_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | ~ v1_tsep_1(X0,X2)
        | ~ m1_pre_topc(X0,X2)
        | ~ m1_pre_topc(sK3,X2)
        | ~ m1_pre_topc(X0,sK3)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ m1_subset_1(sK5,u1_struct_0(X0))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK3,X1)
        | ~ r1_tmap_1(X0,sK0,k3_tmap_1(X1,sK0,sK3,X0,sK4),sK5)
        | v2_struct_0(X1) )
    | ~ spl8_25 ),
    inference(avatar_component_clause,[],[f210])).

fof(f228,plain,
    ( spl8_17
    | ~ spl8_16
    | ~ spl8_15
    | spl8_20
    | ~ spl8_19
    | ~ spl8_18
    | spl8_13
    | ~ spl8_12
    | spl8_14
    | ~ spl8_7
    | ~ spl8_11
    | ~ spl8_10
    | ~ spl8_9
    | ~ spl8_5
    | ~ spl8_22
    | ~ spl8_6
    | ~ spl8_1
    | spl8_21 ),
    inference(avatar_split_clause,[],[f217,f176,f90,f112,f181,f108,f124,f128,f132,f116,f145,f136,f140,f161,f165,f169,f149,f153,f157])).

fof(f169,plain,
    ( spl8_20
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f165,plain,
    ( spl8_19
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f161,plain,
    ( spl8_18
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f140,plain,
    ( spl8_13
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f132,plain,
    ( spl8_11
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f128,plain,
    ( spl8_10
  <=> v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f124,plain,
    ( spl8_9
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f108,plain,
    ( spl8_5
  <=> m1_subset_1(sK5,u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f90,plain,
    ( spl8_1
  <=> r1_tmap_1(sK3,sK0,sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f217,plain,
    ( ~ r1_tmap_1(sK3,sK0,sK4,sK5)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK2,sK1)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | spl8_21 ),
    inference(resolution,[],[f215,f86])).

fof(f86,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
      | ~ r1_tmap_1(X2,X1,X4,X6)
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
      | ~ r1_tmap_1(X2,X1,X4,X5)
      | ~ m1_pre_topc(X3,X2)
      | X5 != X6
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
                              | ~ r1_tmap_1(X2,X1,X4,X5)
                              | ~ m1_pre_topc(X3,X2)
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X2)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
                              | ~ r1_tmap_1(X2,X1,X4,X5)
                              | ~ m1_pre_topc(X3,X2)
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X2)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
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
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X2))
                         => ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X3))
                             => ( ( r1_tmap_1(X2,X1,X4,X5)
                                  & m1_pre_topc(X3,X2)
                                  & X5 = X6 )
                               => r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_tmap_1)).

fof(f215,plain,
    ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK5)
    | spl8_21 ),
    inference(avatar_component_clause,[],[f176])).

fof(f216,plain,
    ( ~ spl8_21
    | spl8_2
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f214,f100,f93,f176])).

fof(f93,plain,
    ( spl8_2
  <=> r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f100,plain,
    ( spl8_3
  <=> sK5 = sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f214,plain,
    ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK5)
    | spl8_2
    | ~ spl8_3 ),
    inference(forward_demodulation,[],[f94,f101])).

fof(f101,plain,
    ( sK5 = sK6
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f100])).

fof(f94,plain,
    ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f93])).

fof(f212,plain,
    ( spl8_13
    | spl8_25
    | ~ spl8_24 ),
    inference(avatar_split_clause,[],[f208,f205,f210,f140])).

fof(f205,plain,
    ( spl8_24
  <=> ! [X1,X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X1,sK3)
        | ~ v1_tsep_1(X1,sK3)
        | ~ r1_tmap_1(X1,sK0,k3_tmap_1(X0,sK0,sK3,X1,sK4),sK5)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X1)
        | ~ m1_subset_1(sK5,u1_struct_0(X1))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).

fof(f208,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_pre_topc(X0,sK3)
        | v2_struct_0(X1)
        | ~ r1_tmap_1(X0,sK0,k3_tmap_1(X1,sK0,sK3,X0,sK4),sK5)
        | ~ m1_pre_topc(sK3,X1)
        | v2_struct_0(X0)
        | ~ m1_subset_1(sK5,u1_struct_0(X0))
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(sK3))
        | ~ m1_pre_topc(sK3,X2)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(X0,X2)
        | ~ v1_tsep_1(X0,X2)
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2) )
    | ~ spl8_24 ),
    inference(resolution,[],[f206,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( v1_tsep_1(X1,X2)
      | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X2)
                & v1_tsep_1(X1,X2) )
              | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v1_tsep_1(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X2)
                & v1_tsep_1(X1,X2) )
              | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v1_tsep_1(X1,X0) )
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
          ( ( m1_pre_topc(X1,X0)
            & v1_tsep_1(X1,X0) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
               => ( m1_pre_topc(X1,X2)
                  & v1_tsep_1(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_tsep_1)).

fof(f206,plain,
    ( ! [X0,X1] :
        ( ~ v1_tsep_1(X1,sK3)
        | ~ m1_pre_topc(X1,sK3)
        | v2_struct_0(X0)
        | ~ r1_tmap_1(X1,sK0,k3_tmap_1(X0,sK0,sK3,X1,sK4),sK5)
        | ~ m1_pre_topc(sK3,X0)
        | v2_struct_0(X1)
        | ~ m1_subset_1(sK5,u1_struct_0(X1))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl8_24 ),
    inference(avatar_component_clause,[],[f205])).

fof(f207,plain,
    ( ~ spl8_5
    | spl8_24
    | spl8_1
    | ~ spl8_23 ),
    inference(avatar_split_clause,[],[f202,f199,f90,f205,f108])).

fof(f199,plain,
    ( spl8_23
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X0,u1_struct_0(X1))
        | v2_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(sK3,X2)
        | r1_tmap_1(sK3,sK0,sK4,X0)
        | ~ r1_tmap_1(X1,sK0,k3_tmap_1(X2,sK0,sK3,X1,sK4),X0)
        | ~ v1_tsep_1(X1,sK3)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_subset_1(X0,u1_struct_0(sK3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).

fof(f202,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(sK3,X0)
        | ~ m1_subset_1(sK5,u1_struct_0(X1))
        | ~ r1_tmap_1(X1,sK0,k3_tmap_1(X0,sK0,sK3,X1,sK4),sK5)
        | ~ v1_tsep_1(X1,sK3)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_subset_1(sK5,u1_struct_0(sK3)) )
    | spl8_1
    | ~ spl8_23 ),
    inference(resolution,[],[f200,f91])).

fof(f91,plain,
    ( ~ r1_tmap_1(sK3,sK0,sK4,sK5)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f90])).

fof(f200,plain,
    ( ! [X2,X0,X1] :
        ( r1_tmap_1(sK3,sK0,sK4,X0)
        | v2_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(sK3,X2)
        | ~ m1_subset_1(X0,u1_struct_0(X1))
        | ~ r1_tmap_1(X1,sK0,k3_tmap_1(X2,sK0,sK3,X1,sK4),X0)
        | ~ v1_tsep_1(X1,sK3)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_subset_1(X0,u1_struct_0(sK3)) )
    | ~ spl8_23 ),
    inference(avatar_component_clause,[],[f199])).

fof(f201,plain,
    ( spl8_20
    | ~ spl8_19
    | ~ spl8_18
    | spl8_13
    | ~ spl8_9
    | spl8_23
    | ~ spl8_10
    | ~ spl8_11 ),
    inference(avatar_split_clause,[],[f192,f132,f128,f199,f124,f140,f161,f165,f169])).

fof(f192,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(X1))
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_pre_topc(X1,sK3)
        | ~ v1_tsep_1(X1,sK3)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
        | ~ r1_tmap_1(X1,sK0,k3_tmap_1(X2,sK0,sK3,X1,sK4),X0)
        | r1_tmap_1(sK3,sK0,sK4,X0)
        | ~ m1_pre_topc(sK3,X2)
        | v2_struct_0(sK3)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2) )
    | ~ spl8_10
    | ~ spl8_11 ),
    inference(resolution,[],[f191,f129])).

fof(f129,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f128])).

fof(f191,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( ~ v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1))
        | ~ m1_subset_1(X4,u1_struct_0(X0))
        | ~ m1_subset_1(X4,u1_struct_0(X3))
        | ~ m1_pre_topc(X0,X3)
        | ~ v1_tsep_1(X0,X3)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        | ~ r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4)
        | r1_tmap_1(X3,X1,sK4,X4)
        | ~ m1_pre_topc(X3,X2)
        | v2_struct_0(X3)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | ~ l1_pre_topc(X2)
        | ~ v2_pre_topc(X2)
        | v2_struct_0(X2) )
    | ~ spl8_11 ),
    inference(resolution,[],[f172,f133])).

fof(f133,plain,
    ( v1_funct_1(sK4)
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f132])).

fof(f172,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X4)
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_pre_topc(X2,X3)
      | ~ v1_tsep_1(X2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | r1_tmap_1(X3,X1,X4,X6)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f84,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).

fof(f84,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( r1_tmap_1(X3,X1,X4,X6)
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_pre_topc(X2,X3)
      | ~ v1_tsep_1(X2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X3,X1,X4,X5)
      | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
      | X5 != X6
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_pre_topc(X2,X3)
      | ~ v1_tsep_1(X2,X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( ( r1_tmap_1(X3,X1,X4,X5)
                                  | ~ r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) )
                                & ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                  | ~ r1_tmap_1(X3,X1,X4,X5) ) )
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X2)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ v1_tsep_1(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( r1_tmap_1(X3,X1,X4,X5)
                              <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) )
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X2)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ v1_tsep_1(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( r1_tmap_1(X3,X1,X4,X5)
                              <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) )
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X2)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ v1_tsep_1(X2,X3)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
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
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( ( m1_pre_topc(X2,X3)
                          & v1_tsep_1(X2,X3) )
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X3))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X2))
                               => ( X5 = X6
                                 => ( r1_tmap_1(X3,X1,X4,X5)
                                  <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_tmap_1)).

fof(f183,plain,
    ( spl8_22
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f179,f104,f100,f181])).

fof(f104,plain,
    ( spl8_4
  <=> m1_subset_1(sK6,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f179,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(superposition,[],[f105,f101])).

fof(f105,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f104])).

fof(f178,plain,
    ( spl8_21
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f174,f100,f93,f176])).

fof(f174,plain,
    ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK5)
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(forward_demodulation,[],[f97,f101])).

fof(f97,plain,
    ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f93])).

fof(f171,plain,(
    ~ spl8_20 ),
    inference(avatar_split_clause,[],[f45,f169])).

fof(f45,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
      | ~ r1_tmap_1(sK3,sK0,sK4,sK5) )
    & ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
      | r1_tmap_1(sK3,sK0,sK4,sK5) )
    & sK5 = sK6
    & m1_subset_1(sK6,u1_struct_0(sK2))
    & m1_subset_1(sK5,u1_struct_0(sK3))
    & m1_pre_topc(sK2,sK3)
    & m1_pre_topc(sK2,sK1)
    & v1_tsep_1(sK2,sK1)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
    & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
    & v1_funct_1(sK4)
    & m1_pre_topc(sK3,sK1)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK1)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f30,f37,f36,f35,f34,f33,f32,f31])).

fof(f31,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ? [X6] :
                                ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
                                  | ~ r1_tmap_1(X3,X0,X4,X5) )
                                & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
                                  | r1_tmap_1(X3,X0,X4,X5) )
                                & X5 = X6
                                & m1_subset_1(X6,u1_struct_0(X2)) )
                            & m1_subset_1(X5,u1_struct_0(X3)) )
                        & m1_pre_topc(X2,X3)
                        & m1_pre_topc(X2,X1)
                        & v1_tsep_1(X2,X1)
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                        & v1_funct_1(X4) )
                    & m1_pre_topc(X3,X1)
                    & ~ v2_struct_0(X3) )
                & m1_pre_topc(X2,X1)
                & ~ v2_struct_0(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( ~ r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,X3,X2,X4),X6)
                                | ~ r1_tmap_1(X3,sK0,X4,X5) )
                              & ( r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,X3,X2,X4),X6)
                                | r1_tmap_1(X3,sK0,X4,X5) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & m1_pre_topc(X2,X1)
                      & v1_tsep_1(X2,X1)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ? [X6] :
                            ( ( ~ r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,X3,X2,X4),X6)
                              | ~ r1_tmap_1(X3,sK0,X4,X5) )
                            & ( r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,X3,X2,X4),X6)
                              | r1_tmap_1(X3,sK0,X4,X5) )
                            & X5 = X6
                            & m1_subset_1(X6,u1_struct_0(X2)) )
                        & m1_subset_1(X5,u1_struct_0(X3)) )
                    & m1_pre_topc(X2,X3)
                    & m1_pre_topc(X2,X1)
                    & v1_tsep_1(X2,X1)
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0))))
                    & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,X1)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,X1)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ( ~ r1_tmap_1(X2,sK0,k3_tmap_1(sK1,sK0,X3,X2,X4),X6)
                            | ~ r1_tmap_1(X3,sK0,X4,X5) )
                          & ( r1_tmap_1(X2,sK0,k3_tmap_1(sK1,sK0,X3,X2,X4),X6)
                            | r1_tmap_1(X3,sK0,X4,X5) )
                          & X5 = X6
                          & m1_subset_1(X6,u1_struct_0(X2)) )
                      & m1_subset_1(X5,u1_struct_0(X3)) )
                  & m1_pre_topc(X2,X3)
                  & m1_pre_topc(X2,sK1)
                  & v1_tsep_1(X2,sK1)
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0))))
                  & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0))
                  & v1_funct_1(X4) )
              & m1_pre_topc(X3,sK1)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK1)
          & ~ v2_struct_0(X2) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ? [X6] :
                        ( ( ~ r1_tmap_1(X2,sK0,k3_tmap_1(sK1,sK0,X3,X2,X4),X6)
                          | ~ r1_tmap_1(X3,sK0,X4,X5) )
                        & ( r1_tmap_1(X2,sK0,k3_tmap_1(sK1,sK0,X3,X2,X4),X6)
                          | r1_tmap_1(X3,sK0,X4,X5) )
                        & X5 = X6
                        & m1_subset_1(X6,u1_struct_0(X2)) )
                    & m1_subset_1(X5,u1_struct_0(X3)) )
                & m1_pre_topc(X2,X3)
                & m1_pre_topc(X2,sK1)
                & v1_tsep_1(X2,sK1)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0))))
                & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,sK1)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK1)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,X3,sK2,X4),X6)
                        | ~ r1_tmap_1(X3,sK0,X4,X5) )
                      & ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,X3,sK2,X4),X6)
                        | r1_tmap_1(X3,sK0,X4,X5) )
                      & X5 = X6
                      & m1_subset_1(X6,u1_struct_0(sK2)) )
                  & m1_subset_1(X5,u1_struct_0(X3)) )
              & m1_pre_topc(sK2,X3)
              & m1_pre_topc(sK2,sK1)
              & v1_tsep_1(sK2,sK1)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0))))
              & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0))
              & v1_funct_1(X4) )
          & m1_pre_topc(X3,sK1)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK2,sK1)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,X3,sK2,X4),X6)
                      | ~ r1_tmap_1(X3,sK0,X4,X5) )
                    & ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,X3,sK2,X4),X6)
                      | r1_tmap_1(X3,sK0,X4,X5) )
                    & X5 = X6
                    & m1_subset_1(X6,u1_struct_0(sK2)) )
                & m1_subset_1(X5,u1_struct_0(X3)) )
            & m1_pre_topc(sK2,X3)
            & m1_pre_topc(sK2,sK1)
            & v1_tsep_1(sK2,sK1)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0))))
            & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0))
            & v1_funct_1(X4) )
        & m1_pre_topc(X3,sK1)
        & ~ v2_struct_0(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,X4),X6)
                    | ~ r1_tmap_1(sK3,sK0,X4,X5) )
                  & ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,X4),X6)
                    | r1_tmap_1(sK3,sK0,X4,X5) )
                  & X5 = X6
                  & m1_subset_1(X6,u1_struct_0(sK2)) )
              & m1_subset_1(X5,u1_struct_0(sK3)) )
          & m1_pre_topc(sK2,sK3)
          & m1_pre_topc(sK2,sK1)
          & v1_tsep_1(sK2,sK1)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
          & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK0))
          & v1_funct_1(X4) )
      & m1_pre_topc(sK3,sK1)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ? [X6] :
                ( ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,X4),X6)
                  | ~ r1_tmap_1(sK3,sK0,X4,X5) )
                & ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,X4),X6)
                  | r1_tmap_1(sK3,sK0,X4,X5) )
                & X5 = X6
                & m1_subset_1(X6,u1_struct_0(sK2)) )
            & m1_subset_1(X5,u1_struct_0(sK3)) )
        & m1_pre_topc(sK2,sK3)
        & m1_pre_topc(sK2,sK1)
        & v1_tsep_1(sK2,sK1)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
        & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK0))
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( ? [X6] :
              ( ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X6)
                | ~ r1_tmap_1(sK3,sK0,sK4,X5) )
              & ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X6)
                | r1_tmap_1(sK3,sK0,sK4,X5) )
              & X5 = X6
              & m1_subset_1(X6,u1_struct_0(sK2)) )
          & m1_subset_1(X5,u1_struct_0(sK3)) )
      & m1_pre_topc(sK2,sK3)
      & m1_pre_topc(sK2,sK1)
      & v1_tsep_1(sK2,sK1)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))
      & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X5] :
        ( ? [X6] :
            ( ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X6)
              | ~ r1_tmap_1(sK3,sK0,sK4,X5) )
            & ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X6)
              | r1_tmap_1(sK3,sK0,sK4,X5) )
            & X5 = X6
            & m1_subset_1(X6,u1_struct_0(sK2)) )
        & m1_subset_1(X5,u1_struct_0(sK3)) )
   => ( ? [X6] :
          ( ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X6)
            | ~ r1_tmap_1(sK3,sK0,sK4,sK5) )
          & ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X6)
            | r1_tmap_1(sK3,sK0,sK4,sK5) )
          & sK5 = X6
          & m1_subset_1(X6,u1_struct_0(sK2)) )
      & m1_subset_1(sK5,u1_struct_0(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X6] :
        ( ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X6)
          | ~ r1_tmap_1(sK3,sK0,sK4,sK5) )
        & ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X6)
          | r1_tmap_1(sK3,sK0,sK4,sK5) )
        & sK5 = X6
        & m1_subset_1(X6,u1_struct_0(sK2)) )
   => ( ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
        | ~ r1_tmap_1(sK3,sK0,sK4,sK5) )
      & ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
        | r1_tmap_1(sK3,sK0,sK4,sK5) )
      & sK5 = sK6
      & m1_subset_1(sK6,u1_struct_0(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
                                | ~ r1_tmap_1(X3,X0,X4,X5) )
                              & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
                                | r1_tmap_1(X3,X0,X4,X5) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & m1_pre_topc(X2,X1)
                      & v1_tsep_1(X2,X1)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
                                | ~ r1_tmap_1(X3,X0,X4,X5) )
                              & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
                                | r1_tmap_1(X3,X0,X4,X5) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & m1_pre_topc(X2,X1)
                      & v1_tsep_1(X2,X1)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( r1_tmap_1(X3,X0,X4,X5)
                              <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & m1_pre_topc(X2,X1)
                      & v1_tsep_1(X2,X1)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ( r1_tmap_1(X3,X0,X4,X5)
                              <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) )
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & m1_pre_topc(X2,X1)
                      & v1_tsep_1(X2,X1)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
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
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X1)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X1)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                          & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                          & v1_funct_1(X4) )
                       => ( ( m1_pre_topc(X2,X3)
                            & m1_pre_topc(X2,X1)
                            & v1_tsep_1(X2,X1) )
                         => ! [X5] :
                              ( m1_subset_1(X5,u1_struct_0(X3))
                             => ! [X6] :
                                  ( m1_subset_1(X6,u1_struct_0(X2))
                                 => ( X5 = X6
                                   => ( r1_tmap_1(X3,X0,X4,X5)
                                    <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) ) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X1)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X1)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                        & v1_funct_1(X4) )
                     => ( ( m1_pre_topc(X2,X3)
                          & m1_pre_topc(X2,X1)
                          & v1_tsep_1(X2,X1) )
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X3))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X2))
                               => ( X5 = X6
                                 => ( r1_tmap_1(X3,X0,X4,X5)
                                  <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_tmap_1)).

fof(f167,plain,(
    spl8_19 ),
    inference(avatar_split_clause,[],[f46,f165])).

fof(f46,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f163,plain,(
    spl8_18 ),
    inference(avatar_split_clause,[],[f47,f161])).

fof(f47,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f159,plain,(
    ~ spl8_17 ),
    inference(avatar_split_clause,[],[f48,f157])).

fof(f48,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f155,plain,(
    spl8_16 ),
    inference(avatar_split_clause,[],[f49,f153])).

fof(f49,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f151,plain,(
    spl8_15 ),
    inference(avatar_split_clause,[],[f50,f149])).

fof(f50,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f147,plain,(
    ~ spl8_14 ),
    inference(avatar_split_clause,[],[f51,f145])).

fof(f51,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f143,plain,(
    spl8_7 ),
    inference(avatar_split_clause,[],[f52,f116])).

fof(f52,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f142,plain,(
    ~ spl8_13 ),
    inference(avatar_split_clause,[],[f53,f140])).

fof(f53,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f138,plain,(
    spl8_12 ),
    inference(avatar_split_clause,[],[f54,f136])).

fof(f54,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f134,plain,(
    spl8_11 ),
    inference(avatar_split_clause,[],[f55,f132])).

fof(f55,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f38])).

fof(f130,plain,(
    spl8_10 ),
    inference(avatar_split_clause,[],[f56,f128])).

fof(f56,plain,(
    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f38])).

fof(f126,plain,(
    spl8_9 ),
    inference(avatar_split_clause,[],[f57,f124])).

fof(f57,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f38])).

fof(f122,plain,(
    spl8_8 ),
    inference(avatar_split_clause,[],[f58,f120])).

fof(f58,plain,(
    v1_tsep_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f114,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f60,f112])).

fof(f60,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f110,plain,(
    spl8_5 ),
    inference(avatar_split_clause,[],[f61,f108])).

fof(f61,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f38])).

fof(f106,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f62,f104])).

fof(f62,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f38])).

fof(f102,plain,(
    spl8_3 ),
    inference(avatar_split_clause,[],[f63,f100])).

fof(f63,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f38])).

fof(f98,plain,
    ( spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f64,f93,f90])).

fof(f64,plain,
    ( r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
    | r1_tmap_1(sK3,sK0,sK4,sK5) ),
    inference(cnf_transformation,[],[f38])).

fof(f95,plain,
    ( ~ spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f65,f93,f90])).

fof(f65,plain,
    ( ~ r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)
    | ~ r1_tmap_1(sK3,sK0,sK4,sK5) ),
    inference(cnf_transformation,[],[f38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:14:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (20152)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.47  % (20156)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.48  % (20166)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.48  % (20156)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % (20158)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.49  % (20165)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.49  % (20161)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.50  % (20154)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.50  % (20155)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f341,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f95,f98,f102,f106,f110,f114,f122,f126,f130,f134,f138,f142,f143,f147,f151,f155,f159,f163,f167,f171,f178,f183,f201,f207,f212,f216,f228,f241,f251,f257,f263,f289,f296,f309,f320,f336])).
% 0.22/0.50  fof(f336,plain,(
% 0.22/0.50    ~spl8_7 | ~spl8_15 | spl8_40),
% 0.22/0.50    inference(avatar_split_clause,[],[f333,f318,f149,f116])).
% 0.22/0.50  fof(f116,plain,(
% 0.22/0.50    spl8_7 <=> m1_pre_topc(sK2,sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.22/0.50  fof(f149,plain,(
% 0.22/0.50    spl8_15 <=> l1_pre_topc(sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).
% 0.22/0.50  fof(f318,plain,(
% 0.22/0.50    spl8_40 <=> l1_pre_topc(sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_40])])).
% 0.22/0.50  fof(f333,plain,(
% 0.22/0.50    ~m1_pre_topc(sK2,sK1) | (~spl8_15 | spl8_40)),
% 0.22/0.50    inference(resolution,[],[f332,f150])).
% 0.22/0.50  fof(f150,plain,(
% 0.22/0.50    l1_pre_topc(sK1) | ~spl8_15),
% 0.22/0.50    inference(avatar_component_clause,[],[f149])).
% 0.22/0.50  fof(f332,plain,(
% 0.22/0.50    ( ! [X0] : (~l1_pre_topc(X0) | ~m1_pre_topc(sK2,X0)) ) | spl8_40),
% 0.22/0.50    inference(resolution,[],[f319,f67])).
% 0.22/0.50  fof(f67,plain,(
% 0.22/0.50    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f16])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.22/0.50  fof(f319,plain,(
% 0.22/0.50    ~l1_pre_topc(sK2) | spl8_40),
% 0.22/0.50    inference(avatar_component_clause,[],[f318])).
% 0.22/0.50  fof(f320,plain,(
% 0.22/0.50    ~spl8_40 | spl8_14 | ~spl8_6 | ~spl8_39),
% 0.22/0.50    inference(avatar_split_clause,[],[f314,f307,f112,f145,f318])).
% 0.22/0.50  fof(f145,plain,(
% 0.22/0.50    spl8_14 <=> v2_struct_0(sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 0.22/0.50  fof(f112,plain,(
% 0.22/0.50    spl8_6 <=> m1_pre_topc(sK2,sK3)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.22/0.50  fof(f307,plain,(
% 0.22/0.50    spl8_39 <=> ! [X0] : (v1_xboole_0(u1_struct_0(X0)) | ~m1_pre_topc(X0,sK3))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_39])])).
% 0.22/0.50  fof(f314,plain,(
% 0.22/0.50    v2_struct_0(sK2) | ~l1_pre_topc(sK2) | (~spl8_6 | ~spl8_39)),
% 0.22/0.50    inference(resolution,[],[f313,f113])).
% 0.22/0.50  fof(f113,plain,(
% 0.22/0.50    m1_pre_topc(sK2,sK3) | ~spl8_6),
% 0.22/0.50    inference(avatar_component_clause,[],[f112])).
% 0.22/0.50  fof(f313,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_pre_topc(X0,sK3) | v2_struct_0(X0) | ~l1_pre_topc(X0)) ) | ~spl8_39),
% 0.22/0.50    inference(resolution,[],[f310,f66])).
% 0.22/0.50  fof(f66,plain,(
% 0.22/0.50    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f15])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.22/0.50  fof(f310,plain,(
% 0.22/0.50    ( ! [X0] : (~l1_struct_0(X0) | ~m1_pre_topc(X0,sK3) | v2_struct_0(X0)) ) | ~spl8_39),
% 0.22/0.50    inference(resolution,[],[f308,f69])).
% 0.22/0.50  fof(f69,plain,(
% 0.22/0.50    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f18])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.22/0.50  fof(f308,plain,(
% 0.22/0.50    ( ! [X0] : (v1_xboole_0(u1_struct_0(X0)) | ~m1_pre_topc(X0,sK3)) ) | ~spl8_39),
% 0.22/0.50    inference(avatar_component_clause,[],[f307])).
% 0.22/0.50  fof(f309,plain,(
% 0.22/0.50    ~spl8_28 | spl8_39 | ~spl8_26),
% 0.22/0.50    inference(avatar_split_clause,[],[f303,f236,f307,f246])).
% 0.22/0.50  fof(f246,plain,(
% 0.22/0.50    spl8_28 <=> l1_pre_topc(sK3)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).
% 0.22/0.50  fof(f236,plain,(
% 0.22/0.50    spl8_26 <=> v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).
% 0.22/0.50  fof(f303,plain,(
% 0.22/0.50    ( ! [X0] : (v1_xboole_0(u1_struct_0(X0)) | ~m1_pre_topc(X0,sK3) | ~l1_pre_topc(sK3)) ) | ~spl8_26),
% 0.22/0.50    inference(resolution,[],[f302,f68])).
% 0.22/0.50  fof(f68,plain,(
% 0.22/0.50    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f17])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f7])).
% 0.22/0.50  fof(f7,axiom,(
% 0.22/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.22/0.50  fof(f302,plain,(
% 0.22/0.50    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) | v1_xboole_0(X1)) ) | ~spl8_26),
% 0.22/0.50    inference(resolution,[],[f237,f78])).
% 0.22/0.50  fof(f78,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f40])).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.22/0.50    inference(nnf_transformation,[],[f28])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.22/0.50  fof(f237,plain,(
% 0.22/0.50    v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK3))) | ~spl8_26),
% 0.22/0.50    inference(avatar_component_clause,[],[f236])).
% 0.22/0.50  fof(f296,plain,(
% 0.22/0.50    ~spl8_12 | ~spl8_15 | spl8_17 | ~spl8_21 | ~spl8_16 | ~spl8_36),
% 0.22/0.50    inference(avatar_split_clause,[],[f294,f287,f153,f176,f157,f149,f136])).
% 0.22/0.50  fof(f136,plain,(
% 0.22/0.50    spl8_12 <=> m1_pre_topc(sK3,sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 0.22/0.50  fof(f157,plain,(
% 0.22/0.50    spl8_17 <=> v2_struct_0(sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).
% 0.22/0.50  fof(f176,plain,(
% 0.22/0.50    spl8_21 <=> r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK5)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).
% 0.22/0.50  fof(f153,plain,(
% 0.22/0.50    spl8_16 <=> v2_pre_topc(sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).
% 0.22/0.50  fof(f287,plain,(
% 0.22/0.50    spl8_36 <=> ! [X0] : (~v2_pre_topc(X0) | ~r1_tmap_1(sK2,sK0,k3_tmap_1(X0,sK0,sK3,sK2,sK4),sK5) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK3,X0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_36])])).
% 0.22/0.50  fof(f294,plain,(
% 0.22/0.50    ~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK5) | v2_struct_0(sK1) | ~l1_pre_topc(sK1) | ~m1_pre_topc(sK3,sK1) | (~spl8_16 | ~spl8_36)),
% 0.22/0.50    inference(resolution,[],[f288,f154])).
% 0.22/0.50  fof(f154,plain,(
% 0.22/0.50    v2_pre_topc(sK1) | ~spl8_16),
% 0.22/0.50    inference(avatar_component_clause,[],[f153])).
% 0.22/0.50  fof(f288,plain,(
% 0.22/0.50    ( ! [X0] : (~v2_pre_topc(X0) | ~r1_tmap_1(sK2,sK0,k3_tmap_1(X0,sK0,sK3,sK2,sK4),sK5) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK3,X0)) ) | ~spl8_36),
% 0.22/0.50    inference(avatar_component_clause,[],[f287])).
% 0.22/0.50  fof(f289,plain,(
% 0.22/0.50    ~spl8_7 | ~spl8_6 | spl8_36 | ~spl8_22 | spl8_14 | ~spl8_8 | ~spl8_30),
% 0.22/0.50    inference(avatar_split_clause,[],[f284,f261,f120,f145,f181,f287,f112,f116])).
% 0.22/0.50  fof(f181,plain,(
% 0.22/0.50    spl8_22 <=> m1_subset_1(sK5,u1_struct_0(sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).
% 0.22/0.50  fof(f120,plain,(
% 0.22/0.50    spl8_8 <=> v1_tsep_1(sK2,sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.22/0.50  fof(f261,plain,(
% 0.22/0.50    spl8_30 <=> ! [X1,X0] : (~v1_tsep_1(X0,sK1) | v2_struct_0(X0) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~v2_pre_topc(X1) | ~m1_pre_topc(sK3,X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(X0,sK3) | ~m1_pre_topc(X0,sK1) | v2_struct_0(X1) | ~r1_tmap_1(X0,sK0,k3_tmap_1(X1,sK0,sK3,X0,sK4),sK5))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).
% 0.22/0.50  fof(f284,plain,(
% 0.22/0.50    ( ! [X0] : (v2_struct_0(sK2) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~v2_pre_topc(X0) | ~m1_pre_topc(sK3,X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK2,sK3) | ~m1_pre_topc(sK2,sK1) | v2_struct_0(X0) | ~r1_tmap_1(sK2,sK0,k3_tmap_1(X0,sK0,sK3,sK2,sK4),sK5)) ) | (~spl8_8 | ~spl8_30)),
% 0.22/0.50    inference(resolution,[],[f262,f121])).
% 0.22/0.50  fof(f121,plain,(
% 0.22/0.50    v1_tsep_1(sK2,sK1) | ~spl8_8),
% 0.22/0.50    inference(avatar_component_clause,[],[f120])).
% 0.22/0.50  fof(f262,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v1_tsep_1(X0,sK1) | v2_struct_0(X0) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~v2_pre_topc(X1) | ~m1_pre_topc(sK3,X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(X0,sK3) | ~m1_pre_topc(X0,sK1) | v2_struct_0(X1) | ~r1_tmap_1(X0,sK0,k3_tmap_1(X1,sK0,sK3,X0,sK4),sK5)) ) | ~spl8_30),
% 0.22/0.50    inference(avatar_component_clause,[],[f261])).
% 0.22/0.50  fof(f263,plain,(
% 0.22/0.50    spl8_17 | ~spl8_12 | spl8_30 | ~spl8_15 | ~spl8_16 | ~spl8_29),
% 0.22/0.50    inference(avatar_split_clause,[],[f258,f249,f153,f149,f261,f136,f157])).
% 0.22/0.50  fof(f249,plain,(
% 0.22/0.50    spl8_29 <=> ! [X1,X0,X2] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_tsep_1(X2,X0) | ~m1_pre_topc(sK3,X0) | ~r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,sK3,X2,sK4),sK5) | v2_struct_0(X1) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,sK3) | ~l1_pre_topc(X1) | ~m1_pre_topc(sK3,X1) | ~v2_pre_topc(X1) | ~m1_subset_1(sK5,u1_struct_0(X2)) | v2_struct_0(X2) | v2_struct_0(X0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).
% 0.22/0.50  fof(f258,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~l1_pre_topc(sK1) | ~v1_tsep_1(X0,sK1) | ~m1_pre_topc(sK3,sK1) | ~r1_tmap_1(X0,sK0,k3_tmap_1(X1,sK0,sK3,X0,sK4),sK5) | v2_struct_0(X1) | ~m1_pre_topc(X0,sK1) | ~m1_pre_topc(X0,sK3) | ~l1_pre_topc(X1) | ~m1_pre_topc(sK3,X1) | ~v2_pre_topc(X1) | ~m1_subset_1(sK5,u1_struct_0(X0)) | v2_struct_0(X0) | v2_struct_0(sK1)) ) | (~spl8_16 | ~spl8_29)),
% 0.22/0.50    inference(resolution,[],[f250,f154])).
% 0.22/0.50  fof(f250,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_tsep_1(X2,X0) | ~m1_pre_topc(sK3,X0) | ~r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,sK3,X2,sK4),sK5) | v2_struct_0(X1) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,sK3) | ~l1_pre_topc(X1) | ~m1_pre_topc(sK3,X1) | ~v2_pre_topc(X1) | ~m1_subset_1(sK5,u1_struct_0(X2)) | v2_struct_0(X2) | v2_struct_0(X0)) ) | ~spl8_29),
% 0.22/0.50    inference(avatar_component_clause,[],[f249])).
% 0.22/0.50  fof(f257,plain,(
% 0.22/0.50    ~spl8_15 | ~spl8_12 | spl8_28),
% 0.22/0.50    inference(avatar_split_clause,[],[f253,f246,f136,f149])).
% 0.22/0.50  fof(f253,plain,(
% 0.22/0.50    ~l1_pre_topc(sK1) | (~spl8_12 | spl8_28)),
% 0.22/0.50    inference(resolution,[],[f252,f137])).
% 0.22/0.50  fof(f137,plain,(
% 0.22/0.50    m1_pre_topc(sK3,sK1) | ~spl8_12),
% 0.22/0.50    inference(avatar_component_clause,[],[f136])).
% 0.22/0.50  fof(f252,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_pre_topc(sK3,X0) | ~l1_pre_topc(X0)) ) | spl8_28),
% 0.22/0.50    inference(resolution,[],[f247,f67])).
% 0.22/0.50  fof(f247,plain,(
% 0.22/0.50    ~l1_pre_topc(sK3) | spl8_28),
% 0.22/0.50    inference(avatar_component_clause,[],[f246])).
% 0.22/0.50  fof(f251,plain,(
% 0.22/0.50    ~spl8_28 | spl8_29 | ~spl8_27),
% 0.22/0.50    inference(avatar_split_clause,[],[f244,f239,f249,f246])).
% 0.22/0.50  fof(f239,plain,(
% 0.22/0.50    spl8_27 <=> ! [X3,X5,X4] : (~v2_pre_topc(X3) | ~m1_subset_1(u1_struct_0(X4),k1_zfmisc_1(u1_struct_0(sK3))) | v2_struct_0(X3) | v2_struct_0(X5) | ~r1_tmap_1(X4,sK0,k3_tmap_1(X5,sK0,sK3,X4,sK4),sK5) | v2_struct_0(X4) | ~m1_subset_1(sK5,u1_struct_0(X4)) | ~v2_pre_topc(X5) | ~m1_pre_topc(sK3,X5) | ~l1_pre_topc(X5) | ~m1_pre_topc(X4,sK3) | ~m1_pre_topc(sK3,X3) | ~m1_pre_topc(X4,X3) | ~v1_tsep_1(X4,X3) | ~l1_pre_topc(X3))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).
% 0.22/0.50  fof(f244,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | v2_struct_0(X0) | v2_struct_0(X1) | ~r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,sK3,X2,sK4),sK5) | v2_struct_0(X2) | ~m1_subset_1(sK5,u1_struct_0(X2)) | ~v2_pre_topc(X1) | ~m1_pre_topc(sK3,X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(X2,sK3) | ~m1_pre_topc(sK3,X0) | ~m1_pre_topc(X2,X0) | ~v1_tsep_1(X2,X0) | ~l1_pre_topc(X0) | ~l1_pre_topc(sK3)) ) | ~spl8_27),
% 0.22/0.50    inference(duplicate_literal_removal,[],[f242])).
% 0.22/0.50  fof(f242,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | v2_struct_0(X0) | v2_struct_0(X1) | ~r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,sK3,X2,sK4),sK5) | v2_struct_0(X2) | ~m1_subset_1(sK5,u1_struct_0(X2)) | ~v2_pre_topc(X1) | ~m1_pre_topc(sK3,X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(X2,sK3) | ~m1_pre_topc(sK3,X0) | ~m1_pre_topc(X2,X0) | ~v1_tsep_1(X2,X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X2,sK3) | ~l1_pre_topc(sK3)) ) | ~spl8_27),
% 0.22/0.50    inference(resolution,[],[f240,f68])).
% 0.22/0.50  fof(f240,plain,(
% 0.22/0.50    ( ! [X4,X5,X3] : (~m1_subset_1(u1_struct_0(X4),k1_zfmisc_1(u1_struct_0(sK3))) | ~v2_pre_topc(X3) | v2_struct_0(X3) | v2_struct_0(X5) | ~r1_tmap_1(X4,sK0,k3_tmap_1(X5,sK0,sK3,X4,sK4),sK5) | v2_struct_0(X4) | ~m1_subset_1(sK5,u1_struct_0(X4)) | ~v2_pre_topc(X5) | ~m1_pre_topc(sK3,X5) | ~l1_pre_topc(X5) | ~m1_pre_topc(X4,sK3) | ~m1_pre_topc(sK3,X3) | ~m1_pre_topc(X4,X3) | ~v1_tsep_1(X4,X3) | ~l1_pre_topc(X3)) ) | ~spl8_27),
% 0.22/0.50    inference(avatar_component_clause,[],[f239])).
% 0.22/0.50  fof(f241,plain,(
% 0.22/0.50    spl8_26 | spl8_27 | ~spl8_25),
% 0.22/0.50    inference(avatar_split_clause,[],[f234,f210,f239,f236])).
% 0.22/0.50  fof(f210,plain,(
% 0.22/0.50    spl8_25 <=> ! [X1,X0,X2] : (~m1_pre_topc(X0,sK3) | v2_struct_0(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~v1_tsep_1(X0,X2) | ~m1_pre_topc(X0,X2) | ~m1_pre_topc(sK3,X2) | ~r1_tarski(u1_struct_0(X0),u1_struct_0(sK3)) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_subset_1(sK5,u1_struct_0(X0)) | v2_struct_0(X0) | ~m1_pre_topc(sK3,X1) | ~r1_tmap_1(X0,sK0,k3_tmap_1(X1,sK0,sK3,X0,sK4),sK5) | v2_struct_0(X1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).
% 0.22/0.50  fof(f234,plain,(
% 0.22/0.50    ( ! [X4,X5,X3] : (~v2_pre_topc(X3) | ~l1_pre_topc(X3) | ~v1_tsep_1(X4,X3) | ~m1_pre_topc(X4,X3) | ~m1_pre_topc(sK3,X3) | ~m1_pre_topc(X4,sK3) | ~v2_pre_topc(X5) | ~l1_pre_topc(X5) | ~m1_subset_1(sK5,u1_struct_0(X4)) | v2_struct_0(X4) | ~m1_pre_topc(sK3,X5) | ~r1_tmap_1(X4,sK0,k3_tmap_1(X5,sK0,sK3,X4,sK4),sK5) | v2_struct_0(X5) | v2_struct_0(X3) | ~m1_subset_1(u1_struct_0(X4),k1_zfmisc_1(u1_struct_0(sK3))) | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK3)))) ) | ~spl8_25),
% 0.22/0.50    inference(resolution,[],[f232,f76])).
% 0.22/0.50  fof(f76,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f40])).
% 0.22/0.50  fof(f232,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~r2_hidden(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(sK3))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0) | ~m1_pre_topc(sK3,X0) | ~m1_pre_topc(X1,sK3) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~m1_subset_1(sK5,u1_struct_0(X1)) | v2_struct_0(X1) | ~m1_pre_topc(sK3,X2) | ~r1_tmap_1(X1,sK0,k3_tmap_1(X2,sK0,sK3,X1,sK4),sK5) | v2_struct_0(X2) | v2_struct_0(X0)) ) | ~spl8_25),
% 0.22/0.50    inference(resolution,[],[f211,f88])).
% 0.22/0.50  fof(f88,plain,(
% 0.22/0.50    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 0.22/0.50    inference(equality_resolution,[],[f80])).
% 0.22/0.50  fof(f80,plain,(
% 0.22/0.50    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.22/0.50    inference(cnf_transformation,[],[f44])).
% 0.22/0.50  fof(f44,plain,(
% 0.22/0.50    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK7(X0,X1),X0) | ~r2_hidden(sK7(X0,X1),X1)) & (r1_tarski(sK7(X0,X1),X0) | r2_hidden(sK7(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f42,f43])).
% 0.22/0.50  fof(f43,plain,(
% 0.22/0.50    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK7(X0,X1),X0) | ~r2_hidden(sK7(X0,X1),X1)) & (r1_tarski(sK7(X0,X1),X0) | r2_hidden(sK7(X0,X1),X1))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f42,plain,(
% 0.22/0.50    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.22/0.50    inference(rectify,[],[f41])).
% 0.22/0.50  fof(f41,plain,(
% 0.22/0.50    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.22/0.50    inference(nnf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.22/0.50  fof(f211,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~r1_tarski(u1_struct_0(X0),u1_struct_0(sK3)) | v2_struct_0(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~v1_tsep_1(X0,X2) | ~m1_pre_topc(X0,X2) | ~m1_pre_topc(sK3,X2) | ~m1_pre_topc(X0,sK3) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~m1_subset_1(sK5,u1_struct_0(X0)) | v2_struct_0(X0) | ~m1_pre_topc(sK3,X1) | ~r1_tmap_1(X0,sK0,k3_tmap_1(X1,sK0,sK3,X0,sK4),sK5) | v2_struct_0(X1)) ) | ~spl8_25),
% 0.22/0.50    inference(avatar_component_clause,[],[f210])).
% 0.22/0.50  fof(f228,plain,(
% 0.22/0.50    spl8_17 | ~spl8_16 | ~spl8_15 | spl8_20 | ~spl8_19 | ~spl8_18 | spl8_13 | ~spl8_12 | spl8_14 | ~spl8_7 | ~spl8_11 | ~spl8_10 | ~spl8_9 | ~spl8_5 | ~spl8_22 | ~spl8_6 | ~spl8_1 | spl8_21),
% 0.22/0.50    inference(avatar_split_clause,[],[f217,f176,f90,f112,f181,f108,f124,f128,f132,f116,f145,f136,f140,f161,f165,f169,f149,f153,f157])).
% 0.22/0.50  fof(f169,plain,(
% 0.22/0.50    spl8_20 <=> v2_struct_0(sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).
% 0.22/0.50  fof(f165,plain,(
% 0.22/0.50    spl8_19 <=> v2_pre_topc(sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).
% 0.22/0.50  fof(f161,plain,(
% 0.22/0.50    spl8_18 <=> l1_pre_topc(sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).
% 0.22/0.50  fof(f140,plain,(
% 0.22/0.50    spl8_13 <=> v2_struct_0(sK3)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 0.22/0.50  fof(f132,plain,(
% 0.22/0.50    spl8_11 <=> v1_funct_1(sK4)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 0.22/0.50  fof(f128,plain,(
% 0.22/0.50    spl8_10 <=> v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 0.22/0.50  fof(f124,plain,(
% 0.22/0.50    spl8_9 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.22/0.50  fof(f108,plain,(
% 0.22/0.50    spl8_5 <=> m1_subset_1(sK5,u1_struct_0(sK3))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.22/0.50  fof(f90,plain,(
% 0.22/0.50    spl8_1 <=> r1_tmap_1(sK3,sK0,sK4,sK5)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.22/0.50  fof(f217,plain,(
% 0.22/0.50    ~r1_tmap_1(sK3,sK0,sK4,sK5) | ~m1_pre_topc(sK2,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK2,sK1) | v2_struct_0(sK2) | ~m1_pre_topc(sK3,sK1) | v2_struct_0(sK3) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | spl8_21),
% 0.22/0.50    inference(resolution,[],[f215,f86])).
% 0.22/0.50  fof(f86,plain,(
% 0.22/0.50    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X6) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.50    inference(equality_resolution,[],[f72])).
% 0.22/0.50  fof(f72,plain,(
% 0.22/0.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f23])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | ~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X2))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f22])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) | (~r1_tmap_1(X2,X1,X4,X5) | ~m1_pre_topc(X3,X2) | X5 != X6)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X2))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f9])).
% 0.22/0.50  fof(f9,axiom,(
% 0.22/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X2)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((r1_tmap_1(X2,X1,X4,X5) & m1_pre_topc(X3,X2) & X5 = X6) => r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)))))))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_tmap_1)).
% 0.22/0.50  fof(f215,plain,(
% 0.22/0.50    ~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK5) | spl8_21),
% 0.22/0.50    inference(avatar_component_clause,[],[f176])).
% 0.22/0.50  fof(f216,plain,(
% 0.22/0.50    ~spl8_21 | spl8_2 | ~spl8_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f214,f100,f93,f176])).
% 0.22/0.50  fof(f93,plain,(
% 0.22/0.50    spl8_2 <=> r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.22/0.50  fof(f100,plain,(
% 0.22/0.50    spl8_3 <=> sK5 = sK6),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.22/0.50  fof(f214,plain,(
% 0.22/0.50    ~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK5) | (spl8_2 | ~spl8_3)),
% 0.22/0.50    inference(forward_demodulation,[],[f94,f101])).
% 0.22/0.50  fof(f101,plain,(
% 0.22/0.50    sK5 = sK6 | ~spl8_3),
% 0.22/0.50    inference(avatar_component_clause,[],[f100])).
% 0.22/0.50  fof(f94,plain,(
% 0.22/0.50    ~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) | spl8_2),
% 0.22/0.50    inference(avatar_component_clause,[],[f93])).
% 0.22/0.50  fof(f212,plain,(
% 0.22/0.50    spl8_13 | spl8_25 | ~spl8_24),
% 0.22/0.50    inference(avatar_split_clause,[],[f208,f205,f210,f140])).
% 0.22/0.50  fof(f205,plain,(
% 0.22/0.50    spl8_24 <=> ! [X1,X0] : (v2_struct_0(X0) | ~m1_pre_topc(X1,sK3) | ~v1_tsep_1(X1,sK3) | ~r1_tmap_1(X1,sK0,k3_tmap_1(X0,sK0,sK3,X1,sK4),sK5) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X1) | ~m1_subset_1(sK5,u1_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).
% 0.22/0.50  fof(f208,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~m1_pre_topc(X0,sK3) | v2_struct_0(X1) | ~r1_tmap_1(X0,sK0,k3_tmap_1(X1,sK0,sK3,X0,sK4),sK5) | ~m1_pre_topc(sK3,X1) | v2_struct_0(X0) | ~m1_subset_1(sK5,u1_struct_0(X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~r1_tarski(u1_struct_0(X0),u1_struct_0(sK3)) | ~m1_pre_topc(sK3,X2) | v2_struct_0(sK3) | ~m1_pre_topc(X0,X2) | ~v1_tsep_1(X0,X2) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) ) | ~spl8_24),
% 0.22/0.50    inference(resolution,[],[f206,f73])).
% 0.22/0.50  fof(f73,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (v1_tsep_1(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : ((m1_pre_topc(X1,X2) & v1_tsep_1(X1,X2)) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f24])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X2) & v1_tsep_1(X1,X2)) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) => (m1_pre_topc(X1,X2) & v1_tsep_1(X1,X2))))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_tsep_1)).
% 0.22/0.50  fof(f206,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v1_tsep_1(X1,sK3) | ~m1_pre_topc(X1,sK3) | v2_struct_0(X0) | ~r1_tmap_1(X1,sK0,k3_tmap_1(X0,sK0,sK3,X1,sK4),sK5) | ~m1_pre_topc(sK3,X0) | v2_struct_0(X1) | ~m1_subset_1(sK5,u1_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl8_24),
% 0.22/0.50    inference(avatar_component_clause,[],[f205])).
% 0.22/0.50  fof(f207,plain,(
% 0.22/0.50    ~spl8_5 | spl8_24 | spl8_1 | ~spl8_23),
% 0.22/0.50    inference(avatar_split_clause,[],[f202,f199,f90,f205,f108])).
% 0.22/0.50  fof(f199,plain,(
% 0.22/0.50    spl8_23 <=> ! [X1,X0,X2] : (~m1_subset_1(X0,u1_struct_0(X1)) | v2_struct_0(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | v2_struct_0(X1) | ~m1_pre_topc(sK3,X2) | r1_tmap_1(sK3,sK0,sK4,X0) | ~r1_tmap_1(X1,sK0,k3_tmap_1(X2,sK0,sK3,X1,sK4),X0) | ~v1_tsep_1(X1,sK3) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(X0,u1_struct_0(sK3)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).
% 0.22/0.50  fof(f202,plain,(
% 0.22/0.50    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(sK3,X0) | ~m1_subset_1(sK5,u1_struct_0(X1)) | ~r1_tmap_1(X1,sK0,k3_tmap_1(X0,sK0,sK3,X1,sK4),sK5) | ~v1_tsep_1(X1,sK3) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3))) ) | (spl8_1 | ~spl8_23)),
% 0.22/0.50    inference(resolution,[],[f200,f91])).
% 0.22/0.50  fof(f91,plain,(
% 0.22/0.50    ~r1_tmap_1(sK3,sK0,sK4,sK5) | spl8_1),
% 0.22/0.50    inference(avatar_component_clause,[],[f90])).
% 0.22/0.50  fof(f200,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (r1_tmap_1(sK3,sK0,sK4,X0) | v2_struct_0(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | v2_struct_0(X1) | ~m1_pre_topc(sK3,X2) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~r1_tmap_1(X1,sK0,k3_tmap_1(X2,sK0,sK3,X1,sK4),X0) | ~v1_tsep_1(X1,sK3) | ~m1_pre_topc(X1,sK3) | ~m1_subset_1(X0,u1_struct_0(sK3))) ) | ~spl8_23),
% 0.22/0.50    inference(avatar_component_clause,[],[f199])).
% 0.22/0.50  fof(f201,plain,(
% 0.22/0.50    spl8_20 | ~spl8_19 | ~spl8_18 | spl8_13 | ~spl8_9 | spl8_23 | ~spl8_10 | ~spl8_11),
% 0.22/0.50    inference(avatar_split_clause,[],[f192,f132,f128,f199,f124,f140,f161,f165,f169])).
% 0.22/0.50  fof(f192,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_pre_topc(X1,sK3) | ~v1_tsep_1(X1,sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) | ~r1_tmap_1(X1,sK0,k3_tmap_1(X2,sK0,sK3,X1,sK4),X0) | r1_tmap_1(sK3,sK0,sK4,X0) | ~m1_pre_topc(sK3,X2) | v2_struct_0(sK3) | v2_struct_0(X1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) ) | (~spl8_10 | ~spl8_11)),
% 0.22/0.50    inference(resolution,[],[f191,f129])).
% 0.22/0.50  fof(f129,plain,(
% 0.22/0.50    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) | ~spl8_10),
% 0.22/0.50    inference(avatar_component_clause,[],[f128])).
% 0.22/0.50  fof(f191,plain,(
% 0.22/0.50    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_2(sK4,u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~m1_pre_topc(X0,X3) | ~v1_tsep_1(X0,X3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~r1_tmap_1(X0,X1,k3_tmap_1(X2,X1,X3,X0,sK4),X4) | r1_tmap_1(X3,X1,sK4,X4) | ~m1_pre_topc(X3,X2) | v2_struct_0(X3) | v2_struct_0(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) ) | ~spl8_11),
% 0.22/0.50    inference(resolution,[],[f172,f133])).
% 0.22/0.50  fof(f133,plain,(
% 0.22/0.50    v1_funct_1(sK4) | ~spl8_11),
% 0.22/0.50    inference(avatar_component_clause,[],[f132])).
% 0.22/0.50  fof(f172,plain,(
% 0.22/0.50    ( ! [X6,X4,X2,X0,X3,X1] : (~v1_funct_1(X4) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | r1_tmap_1(X3,X1,X4,X6) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f84,f75])).
% 0.22/0.50  fof(f75,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f27])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.50    inference(flattening,[],[f26])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f8])).
% 0.22/0.50  fof(f8,axiom,(
% 0.22/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).
% 0.22/0.50  fof(f84,plain,(
% 0.22/0.50    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X1,X4,X6) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.50    inference(equality_resolution,[],[f71])).
% 0.22/0.50  fof(f71,plain,(
% 0.22/0.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X1,X4,X5) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f39])).
% 0.22/0.50  fof(f39,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X3,X1,X4,X5) | ~r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) | ~r1_tmap_1(X3,X1,X4,X5))) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(nnf_transformation,[],[f21])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f20])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (((r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)) | X5 != X6) | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | (~m1_pre_topc(X2,X3) | ~v1_tsep_1(X2,X3))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f10])).
% 0.22/0.50  fof(f10,axiom,(
% 0.22/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & v1_tsep_1(X2,X3)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X1,X4,X5) <=> r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)))))))))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_tmap_1)).
% 0.22/0.50  fof(f183,plain,(
% 0.22/0.50    spl8_22 | ~spl8_3 | ~spl8_4),
% 0.22/0.50    inference(avatar_split_clause,[],[f179,f104,f100,f181])).
% 0.22/0.50  fof(f104,plain,(
% 0.22/0.50    spl8_4 <=> m1_subset_1(sK6,u1_struct_0(sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.22/0.50  fof(f179,plain,(
% 0.22/0.50    m1_subset_1(sK5,u1_struct_0(sK2)) | (~spl8_3 | ~spl8_4)),
% 0.22/0.50    inference(superposition,[],[f105,f101])).
% 0.22/0.50  fof(f105,plain,(
% 0.22/0.50    m1_subset_1(sK6,u1_struct_0(sK2)) | ~spl8_4),
% 0.22/0.50    inference(avatar_component_clause,[],[f104])).
% 0.22/0.50  fof(f178,plain,(
% 0.22/0.50    spl8_21 | ~spl8_2 | ~spl8_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f174,f100,f93,f176])).
% 0.22/0.50  fof(f174,plain,(
% 0.22/0.50    r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK5) | (~spl8_2 | ~spl8_3)),
% 0.22/0.50    inference(forward_demodulation,[],[f97,f101])).
% 0.22/0.50  fof(f97,plain,(
% 0.22/0.50    r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) | ~spl8_2),
% 0.22/0.50    inference(avatar_component_clause,[],[f93])).
% 0.22/0.50  fof(f171,plain,(
% 0.22/0.50    ~spl8_20),
% 0.22/0.50    inference(avatar_split_clause,[],[f45,f169])).
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    ~v2_struct_0(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f38])).
% 0.22/0.50  fof(f38,plain,(
% 0.22/0.50    (((((((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) | ~r1_tmap_1(sK3,sK0,sK4,sK5)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) | r1_tmap_1(sK3,sK0,sK4,sK5)) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK2))) & m1_subset_1(sK5,u1_struct_0(sK3))) & m1_pre_topc(sK2,sK3) & m1_pre_topc(sK2,sK1) & v1_tsep_1(sK2,sK1) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) & v1_funct_1(sK4)) & m1_pre_topc(sK3,sK1) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f30,f37,f36,f35,f34,f33,f32,f31])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,X3,X2,X4),X6) | ~r1_tmap_1(X3,sK0,X4,X5)) & (r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,X3,X2,X4),X6) | r1_tmap_1(X3,sK0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,X3,X2,X4),X6) | ~r1_tmap_1(X3,sK0,X4,X5)) & (r1_tmap_1(X2,sK0,k3_tmap_1(X1,sK0,X3,X2,X4),X6) | r1_tmap_1(X3,sK0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,sK0,k3_tmap_1(sK1,sK0,X3,X2,X4),X6) | ~r1_tmap_1(X3,sK0,X4,X5)) & (r1_tmap_1(X2,sK0,k3_tmap_1(sK1,sK0,X3,X2,X4),X6) | r1_tmap_1(X3,sK0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,sK1) & v1_tsep_1(X2,sK1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    ? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,sK0,k3_tmap_1(sK1,sK0,X3,X2,X4),X6) | ~r1_tmap_1(X3,sK0,X4,X5)) & (r1_tmap_1(X2,sK0,k3_tmap_1(sK1,sK0,X3,X2,X4),X6) | r1_tmap_1(X3,sK0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,sK1) & v1_tsep_1(X2,sK1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,X3,sK2,X4),X6) | ~r1_tmap_1(X3,sK0,X4,X5)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,X3,sK2,X4),X6) | r1_tmap_1(X3,sK0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(sK2,X3) & m1_pre_topc(sK2,sK1) & v1_tsep_1(sK2,sK1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    ? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,X3,sK2,X4),X6) | ~r1_tmap_1(X3,sK0,X4,X5)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,X3,sK2,X4),X6) | r1_tmap_1(X3,sK0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(sK2,X3) & m1_pre_topc(sK2,sK1) & v1_tsep_1(sK2,sK1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,X4),X6) | ~r1_tmap_1(sK3,sK0,X4,X5)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,X4),X6) | r1_tmap_1(sK3,sK0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(sK3))) & m1_pre_topc(sK2,sK3) & m1_pre_topc(sK2,sK1) & v1_tsep_1(sK2,sK1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_pre_topc(sK3,sK1) & ~v2_struct_0(sK3))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    ? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,X4),X6) | ~r1_tmap_1(sK3,sK0,X4,X5)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,X4),X6) | r1_tmap_1(sK3,sK0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(sK3))) & m1_pre_topc(sK2,sK3) & m1_pre_topc(sK2,sK1) & v1_tsep_1(sK2,sK1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(sK3),u1_struct_0(sK0)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : ((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X6) | ~r1_tmap_1(sK3,sK0,sK4,X5)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X6) | r1_tmap_1(sK3,sK0,sK4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(sK3))) & m1_pre_topc(sK2,sK3) & m1_pre_topc(sK2,sK1) & v1_tsep_1(sK2,sK1) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0)))) & v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0)) & v1_funct_1(sK4))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    ? [X5] : (? [X6] : ((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X6) | ~r1_tmap_1(sK3,sK0,sK4,X5)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X6) | r1_tmap_1(sK3,sK0,sK4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(X5,u1_struct_0(sK3))) => (? [X6] : ((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X6) | ~r1_tmap_1(sK3,sK0,sK4,sK5)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X6) | r1_tmap_1(sK3,sK0,sK4,sK5)) & sK5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) & m1_subset_1(sK5,u1_struct_0(sK3)))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    ? [X6] : ((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X6) | ~r1_tmap_1(sK3,sK0,sK4,sK5)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),X6) | r1_tmap_1(sK3,sK0,sK4,sK5)) & sK5 = X6 & m1_subset_1(X6,u1_struct_0(sK2))) => ((~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) | ~r1_tmap_1(sK3,sK0,sK4,sK5)) & (r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) | r1_tmap_1(sK3,sK0,sK4,sK5)) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK2)))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f29])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (((~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X5))) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.50    inference(nnf_transformation,[],[f14])).
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : ((r1_tmap_1(X3,X0,X4,X5) <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f13])).
% 0.22/0.50  fof(f13,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : (((r1_tmap_1(X3,X0,X4,X5) <~> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)) & X5 = X6) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & (m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X1) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X1) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f12])).
% 0.22/0.50  fof(f12,negated_conjecture,(
% 0.22/0.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X0,X4,X5) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)))))))))))),
% 0.22/0.50    inference(negated_conjecture,[],[f11])).
% 0.22/0.50  fof(f11,conjecture,(
% 0.22/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X0,X4,X5) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)))))))))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_tmap_1)).
% 0.22/0.50  fof(f167,plain,(
% 0.22/0.50    spl8_19),
% 0.22/0.50    inference(avatar_split_clause,[],[f46,f165])).
% 0.22/0.50  fof(f46,plain,(
% 0.22/0.50    v2_pre_topc(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f38])).
% 0.22/0.50  fof(f163,plain,(
% 0.22/0.50    spl8_18),
% 0.22/0.50    inference(avatar_split_clause,[],[f47,f161])).
% 0.22/0.50  fof(f47,plain,(
% 0.22/0.50    l1_pre_topc(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f38])).
% 0.22/0.50  fof(f159,plain,(
% 0.22/0.50    ~spl8_17),
% 0.22/0.50    inference(avatar_split_clause,[],[f48,f157])).
% 0.22/0.50  fof(f48,plain,(
% 0.22/0.50    ~v2_struct_0(sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f38])).
% 0.22/0.50  fof(f155,plain,(
% 0.22/0.50    spl8_16),
% 0.22/0.50    inference(avatar_split_clause,[],[f49,f153])).
% 0.22/0.50  fof(f49,plain,(
% 0.22/0.50    v2_pre_topc(sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f38])).
% 0.22/0.50  fof(f151,plain,(
% 0.22/0.50    spl8_15),
% 0.22/0.50    inference(avatar_split_clause,[],[f50,f149])).
% 0.22/0.50  fof(f50,plain,(
% 0.22/0.50    l1_pre_topc(sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f38])).
% 0.22/0.50  fof(f147,plain,(
% 0.22/0.50    ~spl8_14),
% 0.22/0.50    inference(avatar_split_clause,[],[f51,f145])).
% 0.22/0.50  fof(f51,plain,(
% 0.22/0.50    ~v2_struct_0(sK2)),
% 0.22/0.50    inference(cnf_transformation,[],[f38])).
% 0.22/0.50  fof(f143,plain,(
% 0.22/0.50    spl8_7),
% 0.22/0.50    inference(avatar_split_clause,[],[f52,f116])).
% 0.22/0.50  fof(f52,plain,(
% 0.22/0.50    m1_pre_topc(sK2,sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f38])).
% 0.22/0.50  fof(f142,plain,(
% 0.22/0.50    ~spl8_13),
% 0.22/0.50    inference(avatar_split_clause,[],[f53,f140])).
% 0.22/0.50  fof(f53,plain,(
% 0.22/0.50    ~v2_struct_0(sK3)),
% 0.22/0.50    inference(cnf_transformation,[],[f38])).
% 0.22/0.50  fof(f138,plain,(
% 0.22/0.50    spl8_12),
% 0.22/0.50    inference(avatar_split_clause,[],[f54,f136])).
% 0.22/0.50  fof(f54,plain,(
% 0.22/0.50    m1_pre_topc(sK3,sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f38])).
% 0.22/0.50  fof(f134,plain,(
% 0.22/0.50    spl8_11),
% 0.22/0.50    inference(avatar_split_clause,[],[f55,f132])).
% 0.22/0.50  fof(f55,plain,(
% 0.22/0.50    v1_funct_1(sK4)),
% 0.22/0.50    inference(cnf_transformation,[],[f38])).
% 0.22/0.50  fof(f130,plain,(
% 0.22/0.50    spl8_10),
% 0.22/0.50    inference(avatar_split_clause,[],[f56,f128])).
% 0.22/0.50  fof(f56,plain,(
% 0.22/0.50    v1_funct_2(sK4,u1_struct_0(sK3),u1_struct_0(sK0))),
% 0.22/0.50    inference(cnf_transformation,[],[f38])).
% 0.22/0.50  fof(f126,plain,(
% 0.22/0.50    spl8_9),
% 0.22/0.50    inference(avatar_split_clause,[],[f57,f124])).
% 0.22/0.50  fof(f57,plain,(
% 0.22/0.50    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK0))))),
% 0.22/0.50    inference(cnf_transformation,[],[f38])).
% 0.22/0.50  fof(f122,plain,(
% 0.22/0.50    spl8_8),
% 0.22/0.50    inference(avatar_split_clause,[],[f58,f120])).
% 0.22/0.50  fof(f58,plain,(
% 0.22/0.50    v1_tsep_1(sK2,sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f38])).
% 0.22/0.50  fof(f114,plain,(
% 0.22/0.50    spl8_6),
% 0.22/0.50    inference(avatar_split_clause,[],[f60,f112])).
% 0.22/0.50  fof(f60,plain,(
% 0.22/0.50    m1_pre_topc(sK2,sK3)),
% 0.22/0.50    inference(cnf_transformation,[],[f38])).
% 0.22/0.50  fof(f110,plain,(
% 0.22/0.50    spl8_5),
% 0.22/0.50    inference(avatar_split_clause,[],[f61,f108])).
% 0.22/0.50  fof(f61,plain,(
% 0.22/0.50    m1_subset_1(sK5,u1_struct_0(sK3))),
% 0.22/0.50    inference(cnf_transformation,[],[f38])).
% 0.22/0.50  fof(f106,plain,(
% 0.22/0.50    spl8_4),
% 0.22/0.50    inference(avatar_split_clause,[],[f62,f104])).
% 0.22/0.50  fof(f62,plain,(
% 0.22/0.50    m1_subset_1(sK6,u1_struct_0(sK2))),
% 0.22/0.50    inference(cnf_transformation,[],[f38])).
% 0.22/0.50  fof(f102,plain,(
% 0.22/0.50    spl8_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f63,f100])).
% 0.22/0.50  fof(f63,plain,(
% 0.22/0.50    sK5 = sK6),
% 0.22/0.50    inference(cnf_transformation,[],[f38])).
% 0.22/0.50  fof(f98,plain,(
% 0.22/0.50    spl8_1 | spl8_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f64,f93,f90])).
% 0.22/0.50  fof(f64,plain,(
% 0.22/0.50    r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) | r1_tmap_1(sK3,sK0,sK4,sK5)),
% 0.22/0.50    inference(cnf_transformation,[],[f38])).
% 0.22/0.50  fof(f95,plain,(
% 0.22/0.50    ~spl8_1 | ~spl8_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f65,f93,f90])).
% 0.22/0.50  fof(f65,plain,(
% 0.22/0.50    ~r1_tmap_1(sK2,sK0,k3_tmap_1(sK1,sK0,sK3,sK2,sK4),sK6) | ~r1_tmap_1(sK3,sK0,sK4,sK5)),
% 0.22/0.50    inference(cnf_transformation,[],[f38])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (20156)------------------------------
% 0.22/0.50  % (20156)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (20156)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (20156)Memory used [KB]: 11001
% 0.22/0.50  % (20156)Time elapsed: 0.060 s
% 0.22/0.50  % (20156)------------------------------
% 0.22/0.50  % (20156)------------------------------
% 0.22/0.51  % (20146)Success in time 0.142 s
%------------------------------------------------------------------------------
