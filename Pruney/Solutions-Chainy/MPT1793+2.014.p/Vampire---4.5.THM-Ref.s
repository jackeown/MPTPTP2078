%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:28 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  224 ( 385 expanded)
%              Number of leaves         :   55 ( 169 expanded)
%              Depth                    :    9
%              Number of atoms          : 1114 (1929 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   26 (   7 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f419,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f75,f79,f83,f87,f91,f95,f99,f103,f107,f111,f119,f123,f127,f139,f143,f147,f151,f156,f164,f179,f184,f195,f208,f215,f223,f233,f237,f246,f253,f267,f285,f291,f295,f326,f336,f339,f346,f366,f387,f393,f401,f418])).

fof(f418,plain,
    ( ~ spl7_59
    | spl7_1
    | ~ spl7_14
    | ~ spl7_62 ),
    inference(avatar_split_clause,[],[f405,f399,f125,f73,f382])).

fof(f382,plain,
    ( spl7_59
  <=> l1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_59])])).

fof(f73,plain,
    ( spl7_1
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f125,plain,
    ( spl7_14
  <=> ! [X0] :
        ( v2_struct_0(X0)
        | ~ l1_struct_0(X0)
        | ~ v1_xboole_0(sK4(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f399,plain,
    ( spl7_62
  <=> v1_xboole_0(sK4(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_62])])).

fof(f405,plain,
    ( ~ l1_struct_0(sK2)
    | spl7_1
    | ~ spl7_14
    | ~ spl7_62 ),
    inference(subsumption_resolution,[],[f402,f74])).

fof(f74,plain,
    ( ~ v2_struct_0(sK2)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f73])).

fof(f402,plain,
    ( ~ l1_struct_0(sK2)
    | v2_struct_0(sK2)
    | ~ spl7_14
    | ~ spl7_62 ),
    inference(resolution,[],[f400,f126])).

fof(f126,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(sK4(X0))
        | ~ l1_struct_0(X0)
        | v2_struct_0(X0) )
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f125])).

fof(f400,plain,
    ( v1_xboole_0(sK4(sK2))
    | ~ spl7_62 ),
    inference(avatar_component_clause,[],[f399])).

fof(f401,plain,
    ( spl7_62
    | ~ spl7_12
    | ~ spl7_60 ),
    inference(avatar_split_clause,[],[f394,f385,f117,f399])).

fof(f117,plain,
    ( spl7_12
  <=> ! [X0] :
        ( r2_hidden(sK5(X0),X0)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f385,plain,
    ( spl7_60
  <=> ! [X0] : ~ r2_hidden(X0,sK4(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_60])])).

fof(f394,plain,
    ( v1_xboole_0(sK4(sK2))
    | ~ spl7_12
    | ~ spl7_60 ),
    inference(resolution,[],[f386,f118])).

fof(f118,plain,
    ( ! [X0] :
        ( r2_hidden(sK5(X0),X0)
        | v1_xboole_0(X0) )
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f117])).

fof(f386,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK4(sK2))
    | ~ spl7_60 ),
    inference(avatar_component_clause,[],[f385])).

fof(f393,plain,
    ( ~ spl7_46
    | ~ spl7_9
    | spl7_59 ),
    inference(avatar_split_clause,[],[f388,f382,f105,f279])).

fof(f279,plain,
    ( spl7_46
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_46])])).

fof(f105,plain,
    ( spl7_9
  <=> ! [X0] :
        ( ~ l1_pre_topc(X0)
        | l1_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f388,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ spl7_9
    | spl7_59 ),
    inference(resolution,[],[f383,f106])).

fof(f106,plain,
    ( ! [X0] :
        ( l1_struct_0(X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f105])).

fof(f383,plain,
    ( ~ l1_struct_0(sK2)
    | spl7_59 ),
    inference(avatar_component_clause,[],[f382])).

fof(f387,plain,
    ( ~ spl7_59
    | spl7_60
    | spl7_1
    | ~ spl7_20
    | ~ spl7_52 ),
    inference(avatar_split_clause,[],[f358,f324,f149,f73,f385,f382])).

fof(f149,plain,
    ( spl7_20
  <=> ! [X0] :
        ( v2_struct_0(X0)
        | ~ l1_struct_0(X0)
        | m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f324,plain,
    ( spl7_52
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ r2_hidden(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_52])])).

fof(f358,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK4(sK2))
        | ~ l1_struct_0(sK2) )
    | spl7_1
    | ~ spl7_20
    | ~ spl7_52 ),
    inference(subsumption_resolution,[],[f357,f74])).

fof(f357,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK4(sK2))
        | ~ l1_struct_0(sK2)
        | v2_struct_0(sK2) )
    | ~ spl7_20
    | ~ spl7_52 ),
    inference(resolution,[],[f325,f150])).

fof(f150,plain,
    ( ! [X0] :
        ( m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_struct_0(X0)
        | v2_struct_0(X0) )
    | ~ spl7_20 ),
    inference(avatar_component_clause,[],[f149])).

fof(f325,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ r2_hidden(X1,X0) )
    | ~ spl7_52 ),
    inference(avatar_component_clause,[],[f324])).

% (8275)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f366,plain,
    ( spl7_29
    | ~ spl7_6
    | ~ spl7_17
    | spl7_55 ),
    inference(avatar_split_clause,[],[f364,f344,f137,f93,f189])).

fof(f189,plain,
    ( spl7_29
  <=> v1_xboole_0(u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).

fof(f93,plain,
    ( spl7_6
  <=> m1_subset_1(sK3,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f137,plain,
    ( spl7_17
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,X1)
        | v1_xboole_0(X1)
        | r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f344,plain,
    ( spl7_55
  <=> r2_hidden(sK3,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_55])])).

fof(f364,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | ~ spl7_6
    | ~ spl7_17
    | spl7_55 ),
    inference(subsumption_resolution,[],[f359,f94])).

fof(f94,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f93])).

fof(f359,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ spl7_17
    | spl7_55 ),
    inference(resolution,[],[f345,f138])).

fof(f138,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,X1)
        | v1_xboole_0(X1)
        | ~ m1_subset_1(X0,X1) )
    | ~ spl7_17 ),
    inference(avatar_component_clause,[],[f137])).

fof(f345,plain,
    ( ~ r2_hidden(sK3,u1_struct_0(sK2))
    | spl7_55 ),
    inference(avatar_component_clause,[],[f344])).

fof(f346,plain,
    ( ~ spl7_55
    | ~ spl7_21
    | ~ spl7_53 ),
    inference(avatar_split_clause,[],[f342,f331,f154,f344])).

fof(f154,plain,
    ( spl7_21
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,u1_struct_0(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f331,plain,
    ( spl7_53
  <=> r2_hidden(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_53])])).

fof(f342,plain,
    ( ~ r2_hidden(sK3,u1_struct_0(sK2))
    | ~ spl7_21
    | ~ spl7_53 ),
    inference(resolution,[],[f332,f155])).

fof(f155,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,u1_struct_0(sK2)) )
    | ~ spl7_21 ),
    inference(avatar_component_clause,[],[f154])).

fof(f332,plain,
    ( r2_hidden(sK3,sK1)
    | ~ spl7_53 ),
    inference(avatar_component_clause,[],[f331])).

fof(f339,plain,
    ( spl7_1
    | spl7_2
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_33
    | spl7_54 ),
    inference(avatar_contradiction_clause,[],[f337])).

fof(f337,plain,
    ( $false
    | spl7_1
    | spl7_2
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_33
    | spl7_54 ),
    inference(unit_resulting_resolution,[],[f78,f86,f74,f90,f94,f335,f207])).

fof(f207,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(X2,u1_struct_0(X0))
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_subset_1(X2,u1_struct_0(X1))
        | v2_struct_0(X0) )
    | ~ spl7_33 ),
    inference(avatar_component_clause,[],[f206])).

fof(f206,plain,
    ( spl7_33
  <=> ! [X1,X0,X2] :
        ( v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_subset_1(X2,u1_struct_0(X1))
        | m1_subset_1(X2,u1_struct_0(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).

fof(f335,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | spl7_54 ),
    inference(avatar_component_clause,[],[f334])).

fof(f334,plain,
    ( spl7_54
  <=> m1_subset_1(sK3,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_54])])).

fof(f90,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl7_5
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f86,plain,
    ( l1_pre_topc(sK0)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl7_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f78,plain,
    ( ~ v2_struct_0(sK0)
    | spl7_2 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl7_2
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f336,plain,
    ( spl7_53
    | ~ spl7_54
    | spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_38
    | spl7_48 ),
    inference(avatar_split_clause,[],[f300,f293,f231,f101,f85,f81,f77,f334,f331])).

fof(f81,plain,
    ( spl7_3
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f101,plain,
    ( spl7_8
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f231,plain,
    ( spl7_38
  <=> ! [X1,X0,X2] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | r2_hidden(X2,X1)
        | r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_38])])).

fof(f293,plain,
    ( spl7_48
  <=> r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_48])])).

fof(f300,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | r2_hidden(sK3,sK1)
    | spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_38
    | spl7_48 ),
    inference(subsumption_resolution,[],[f299,f78])).

fof(f299,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | r2_hidden(sK3,sK1)
    | v2_struct_0(sK0)
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_38
    | spl7_48 ),
    inference(subsumption_resolution,[],[f298,f102])).

fof(f102,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f101])).

fof(f298,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | r2_hidden(sK3,sK1)
    | v2_struct_0(sK0)
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_38
    | spl7_48 ),
    inference(subsumption_resolution,[],[f297,f86])).

fof(f297,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | r2_hidden(sK3,sK1)
    | v2_struct_0(sK0)
    | ~ spl7_3
    | ~ spl7_38
    | spl7_48 ),
    inference(subsumption_resolution,[],[f296,f82])).

fof(f82,plain,
    ( v2_pre_topc(sK0)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f81])).

fof(f296,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | r2_hidden(sK3,sK1)
    | v2_struct_0(sK0)
    | ~ spl7_38
    | spl7_48 ),
    inference(resolution,[],[f294,f232])).

fof(f232,plain,
    ( ! [X2,X0,X1] :
        ( r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | r2_hidden(X2,X1)
        | v2_struct_0(X0) )
    | ~ spl7_38 ),
    inference(avatar_component_clause,[],[f231])).

fof(f294,plain,
    ( ~ r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK3)
    | spl7_48 ),
    inference(avatar_component_clause,[],[f293])).

fof(f326,plain,
    ( spl7_52
    | ~ spl7_19
    | ~ spl7_29 ),
    inference(avatar_split_clause,[],[f317,f189,f145,f324])).

fof(f145,plain,
    ( spl7_19
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
        | ~ v1_xboole_0(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f317,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ r2_hidden(X1,X0) )
    | ~ spl7_19
    | ~ spl7_29 ),
    inference(resolution,[],[f190,f146])).

fof(f146,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_xboole_0(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
        | ~ r2_hidden(X0,X1) )
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f145])).

fof(f190,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | ~ spl7_29 ),
    inference(avatar_component_clause,[],[f189])).

fof(f295,plain,
    ( ~ spl7_48
    | ~ spl7_6
    | ~ spl7_8
    | spl7_10
    | ~ spl7_47 ),
    inference(avatar_split_clause,[],[f288,f283,f109,f101,f93,f293])).

fof(f109,plain,
    ( spl7_10
  <=> r1_tmap_1(sK2,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f283,plain,
    ( spl7_47
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ r1_tmap_1(sK0,k6_tmap_1(sK0,X1),k7_tmap_1(sK0,X1),X0)
        | r1_tmap_1(sK2,k6_tmap_1(sK0,X1),k2_tmap_1(sK0,k6_tmap_1(sK0,X1),k7_tmap_1(sK0,X1),sK2),X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_47])])).

fof(f288,plain,
    ( ~ r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK3)
    | ~ spl7_6
    | ~ spl7_8
    | spl7_10
    | ~ spl7_47 ),
    inference(subsumption_resolution,[],[f287,f102])).

fof(f287,plain,
    ( ~ r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK3)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_6
    | spl7_10
    | ~ spl7_47 ),
    inference(subsumption_resolution,[],[f286,f94])).

fof(f286,plain,
    ( ~ r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl7_10
    | ~ spl7_47 ),
    inference(resolution,[],[f284,f110])).

fof(f110,plain,
    ( ~ r1_tmap_1(sK2,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),sK3)
    | spl7_10 ),
    inference(avatar_component_clause,[],[f109])).

fof(f284,plain,
    ( ! [X0,X1] :
        ( r1_tmap_1(sK2,k6_tmap_1(sK0,X1),k2_tmap_1(sK0,k6_tmap_1(sK0,X1),k7_tmap_1(sK0,X1),sK2),X0)
        | ~ r1_tmap_1(sK0,k6_tmap_1(sK0,X1),k7_tmap_1(sK0,X1),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl7_47 ),
    inference(avatar_component_clause,[],[f283])).

fof(f291,plain,
    ( ~ spl7_4
    | ~ spl7_5
    | ~ spl7_13
    | spl7_46 ),
    inference(avatar_contradiction_clause,[],[f289])).

fof(f289,plain,
    ( $false
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_13
    | spl7_46 ),
    inference(unit_resulting_resolution,[],[f86,f90,f280,f122])).

fof(f122,plain,
    ( ! [X0,X1] :
        ( l1_pre_topc(X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl7_13
  <=> ! [X1,X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0)
        | l1_pre_topc(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f280,plain,
    ( ~ l1_pre_topc(sK2)
    | spl7_46 ),
    inference(avatar_component_clause,[],[f279])).

fof(f285,plain,
    ( spl7_47
    | spl7_1
    | spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_44 ),
    inference(avatar_split_clause,[],[f274,f265,f89,f85,f81,f77,f73,f283])).

fof(f265,plain,
    ( spl7_44
  <=> ! [X1,X3,X0,X2] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X0)
        | ~ m1_subset_1(X3,u1_struct_0(X2))
        | ~ r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X3)
        | r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_44])])).

fof(f274,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ r1_tmap_1(sK0,k6_tmap_1(sK0,X1),k7_tmap_1(sK0,X1),X0)
        | r1_tmap_1(sK2,k6_tmap_1(sK0,X1),k2_tmap_1(sK0,k6_tmap_1(sK0,X1),k7_tmap_1(sK0,X1),sK2),X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | spl7_1
    | spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_44 ),
    inference(subsumption_resolution,[],[f273,f78])).

fof(f273,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ r1_tmap_1(sK0,k6_tmap_1(sK0,X1),k7_tmap_1(sK0,X1),X0)
        | r1_tmap_1(sK2,k6_tmap_1(sK0,X1),k2_tmap_1(sK0,k6_tmap_1(sK0,X1),k7_tmap_1(sK0,X1),sK2),X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | spl7_1
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_44 ),
    inference(subsumption_resolution,[],[f272,f74])).

fof(f272,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(sK2)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ r1_tmap_1(sK0,k6_tmap_1(sK0,X1),k7_tmap_1(sK0,X1),X0)
        | r1_tmap_1(sK2,k6_tmap_1(sK0,X1),k2_tmap_1(sK0,k6_tmap_1(sK0,X1),k7_tmap_1(sK0,X1),sK2),X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_44 ),
    inference(subsumption_resolution,[],[f271,f86])).

fof(f271,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(sK2)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ r1_tmap_1(sK0,k6_tmap_1(sK0,X1),k7_tmap_1(sK0,X1),X0)
        | r1_tmap_1(sK2,k6_tmap_1(sK0,X1),k2_tmap_1(sK0,k6_tmap_1(sK0,X1),k7_tmap_1(sK0,X1),sK2),X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl7_3
    | ~ spl7_5
    | ~ spl7_44 ),
    inference(subsumption_resolution,[],[f270,f82])).

fof(f270,plain,
    ( ! [X0,X1] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK2)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ r1_tmap_1(sK0,k6_tmap_1(sK0,X1),k7_tmap_1(sK0,X1),X0)
        | r1_tmap_1(sK2,k6_tmap_1(sK0,X1),k2_tmap_1(sK0,k6_tmap_1(sK0,X1),k7_tmap_1(sK0,X1),sK2),X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl7_5
    | ~ spl7_44 ),
    inference(resolution,[],[f266,f90])).

fof(f266,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_pre_topc(X2,X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X2)
        | v2_struct_0(X0)
        | ~ m1_subset_1(X3,u1_struct_0(X2))
        | ~ r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X3)
        | r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
    | ~ spl7_44 ),
    inference(avatar_component_clause,[],[f265])).

fof(f267,plain,
    ( spl7_44
    | ~ spl7_22
    | ~ spl7_26
    | ~ spl7_30
    | ~ spl7_34
    | ~ spl7_36
    | ~ spl7_42 ),
    inference(avatar_split_clause,[],[f263,f251,f221,f213,f193,f177,f162,f265])).

fof(f162,plain,
    ( spl7_22
  <=> ! [X1,X0] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_struct_0(k6_tmap_1(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f177,plain,
    ( spl7_26
  <=> ! [X1,X0] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | v2_pre_topc(k6_tmap_1(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f193,plain,
    ( spl7_30
  <=> ! [X1,X0] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | l1_pre_topc(k6_tmap_1(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).

fof(f213,plain,
    ( spl7_34
  <=> ! [X1,X0] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).

fof(f221,plain,
    ( spl7_36
  <=> ! [X1,X0] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).

fof(f251,plain,
    ( spl7_42
  <=> ! [X1,X3,X5,X0,X2,X4] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X0)
        | ~ v1_funct_2(k7_tmap_1(X2,X3),u1_struct_0(X1),u1_struct_0(X0))
        | ~ m1_subset_1(k7_tmap_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        | v2_struct_0(X4)
        | ~ m1_pre_topc(X4,X1)
        | ~ m1_subset_1(X5,u1_struct_0(X4))
        | ~ r1_tmap_1(X1,X0,k7_tmap_1(X2,X3),X5)
        | r1_tmap_1(X4,X0,k2_tmap_1(X1,X0,k7_tmap_1(X2,X3),X4),X5)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
        | v2_struct_0(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_42])])).

fof(f263,plain,
    ( ! [X2,X0,X3,X1] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X0)
        | ~ m1_subset_1(X3,u1_struct_0(X2))
        | ~ r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X3)
        | r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
    | ~ spl7_22
    | ~ spl7_26
    | ~ spl7_30
    | ~ spl7_34
    | ~ spl7_36
    | ~ spl7_42 ),
    inference(subsumption_resolution,[],[f262,f222])).

fof(f222,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | v2_struct_0(X0) )
    | ~ spl7_36 ),
    inference(avatar_component_clause,[],[f221])).

fof(f262,plain,
    ( ! [X2,X0,X3,X1] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X0)
        | ~ m1_subset_1(X3,u1_struct_0(X2))
        | ~ r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X3)
        | r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
    | ~ spl7_22
    | ~ spl7_26
    | ~ spl7_30
    | ~ spl7_34
    | ~ spl7_42 ),
    inference(subsumption_resolution,[],[f261,f194])).

fof(f194,plain,
    ( ! [X0,X1] :
        ( l1_pre_topc(k6_tmap_1(X0,X1))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | v2_struct_0(X0) )
    | ~ spl7_30 ),
    inference(avatar_component_clause,[],[f193])).

fof(f261,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ l1_pre_topc(k6_tmap_1(X0,X1))
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X0)
        | ~ m1_subset_1(X3,u1_struct_0(X2))
        | ~ r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X3)
        | r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
    | ~ spl7_22
    | ~ spl7_26
    | ~ spl7_34
    | ~ spl7_42 ),
    inference(subsumption_resolution,[],[f260,f178])).

fof(f178,plain,
    ( ! [X0,X1] :
        ( v2_pre_topc(k6_tmap_1(X0,X1))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | v2_struct_0(X0) )
    | ~ spl7_26 ),
    inference(avatar_component_clause,[],[f177])).

fof(f260,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ l1_pre_topc(k6_tmap_1(X0,X1))
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(k6_tmap_1(X0,X1))
        | ~ m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X0)
        | ~ m1_subset_1(X3,u1_struct_0(X2))
        | ~ r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X3)
        | r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
    | ~ spl7_22
    | ~ spl7_34
    | ~ spl7_42 ),
    inference(subsumption_resolution,[],[f259,f163])).

fof(f163,plain,
    ( ! [X0,X1] :
        ( ~ v2_struct_0(k6_tmap_1(X0,X1))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | v2_struct_0(X0) )
    | ~ spl7_22 ),
    inference(avatar_component_clause,[],[f162])).

fof(f259,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ l1_pre_topc(k6_tmap_1(X0,X1))
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(k6_tmap_1(X0,X1))
        | ~ v2_pre_topc(k6_tmap_1(X0,X1))
        | ~ m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X0)
        | ~ m1_subset_1(X3,u1_struct_0(X2))
        | ~ r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X3)
        | r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
    | ~ spl7_34
    | ~ spl7_42 ),
    inference(duplicate_literal_removal,[],[f258])).

fof(f258,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ l1_pre_topc(k6_tmap_1(X0,X1))
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(k6_tmap_1(X0,X1))
        | ~ v2_pre_topc(k6_tmap_1(X0,X1))
        | ~ m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X0)
        | ~ m1_subset_1(X3,u1_struct_0(X2))
        | ~ r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X3)
        | r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | v2_struct_0(X0) )
    | ~ spl7_34
    | ~ spl7_42 ),
    inference(resolution,[],[f252,f214])).

fof(f214,plain,
    ( ! [X0,X1] :
        ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | v2_struct_0(X0) )
    | ~ spl7_34 ),
    inference(avatar_component_clause,[],[f213])).

% (8288)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
fof(f252,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( ~ v1_funct_2(k7_tmap_1(X2,X3),u1_struct_0(X1),u1_struct_0(X0))
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ m1_subset_1(k7_tmap_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        | v2_struct_0(X4)
        | ~ m1_pre_topc(X4,X1)
        | ~ m1_subset_1(X5,u1_struct_0(X4))
        | ~ r1_tmap_1(X1,X0,k7_tmap_1(X2,X3),X5)
        | r1_tmap_1(X4,X0,k2_tmap_1(X1,X0,k7_tmap_1(X2,X3),X4),X5)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
        | v2_struct_0(X2) )
    | ~ spl7_42 ),
    inference(avatar_component_clause,[],[f251])).

fof(f253,plain,
    ( spl7_42
    | ~ spl7_27
    | ~ spl7_41 ),
    inference(avatar_split_clause,[],[f247,f244,f182,f251])).

fof(f182,plain,
    ( spl7_27
  <=> ! [X1,X0] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | v1_funct_1(k7_tmap_1(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).

fof(f244,plain,
    ( spl7_41
  <=> ! [X1,X3,X5,X0,X2] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,X1)
        | ~ m1_subset_1(X5,u1_struct_0(X3))
        | ~ r1_tmap_1(X1,X0,X2,X5)
        | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_41])])).

fof(f247,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X0)
        | ~ v1_funct_2(k7_tmap_1(X2,X3),u1_struct_0(X1),u1_struct_0(X0))
        | ~ m1_subset_1(k7_tmap_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        | v2_struct_0(X4)
        | ~ m1_pre_topc(X4,X1)
        | ~ m1_subset_1(X5,u1_struct_0(X4))
        | ~ r1_tmap_1(X1,X0,k7_tmap_1(X2,X3),X5)
        | r1_tmap_1(X4,X0,k2_tmap_1(X1,X0,k7_tmap_1(X2,X3),X4),X5)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
        | v2_struct_0(X2) )
    | ~ spl7_27
    | ~ spl7_41 ),
    inference(resolution,[],[f245,f183])).

fof(f183,plain,
    ( ! [X0,X1] :
        ( v1_funct_1(k7_tmap_1(X0,X1))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | v2_struct_0(X0) )
    | ~ spl7_27 ),
    inference(avatar_component_clause,[],[f182])).

fof(f245,plain,
    ( ! [X2,X0,X5,X3,X1] :
        ( ~ v1_funct_1(X2)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | v2_struct_0(X0)
        | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,X1)
        | ~ m1_subset_1(X5,u1_struct_0(X3))
        | ~ r1_tmap_1(X1,X0,X2,X5)
        | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) )
    | ~ spl7_41 ),
    inference(avatar_component_clause,[],[f244])).

fof(f246,plain,
    ( spl7_41
    | ~ spl7_33
    | ~ spl7_39 ),
    inference(avatar_split_clause,[],[f238,f235,f206,f244])).

fof(f235,plain,
    ( spl7_39
  <=> ! [X1,X3,X5,X0,X2] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,X1)
        | ~ m1_subset_1(X5,u1_struct_0(X1))
        | ~ m1_subset_1(X5,u1_struct_0(X3))
        | ~ r1_tmap_1(X1,X0,X2,X5)
        | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_39])])).

fof(f238,plain,
    ( ! [X2,X0,X5,X3,X1] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,X1)
        | ~ m1_subset_1(X5,u1_struct_0(X3))
        | ~ r1_tmap_1(X1,X0,X2,X5)
        | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) )
    | ~ spl7_33
    | ~ spl7_39 ),
    inference(subsumption_resolution,[],[f236,f207])).

fof(f236,plain,
    ( ! [X2,X0,X5,X3,X1] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,X1)
        | ~ m1_subset_1(X5,u1_struct_0(X1))
        | ~ m1_subset_1(X5,u1_struct_0(X3))
        | ~ r1_tmap_1(X1,X0,X2,X5)
        | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) )
    | ~ spl7_39 ),
    inference(avatar_component_clause,[],[f235])).

fof(f237,plain,(
    spl7_39 ),
    inference(avatar_split_clause,[],[f71,f235])).

fof(f71,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ r1_tmap_1(X1,X0,X2,X5)
      | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | X4 != X5
      | ~ r1_tmap_1(X1,X0,X2,X4)
      | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                          | ~ r1_tmap_1(X1,X0,X2,X4)
                          | X4 != X5
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                          | ~ r1_tmap_1(X1,X0,X2,X4)
                          | X4 != X5
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X1)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X3))
                         => ( ( r1_tmap_1(X1,X0,X2,X4)
                              & X4 = X5 )
                           => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tmap_1)).

fof(f233,plain,(
    spl7_38 ),
    inference(avatar_split_clause,[],[f52,f231])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_hidden(X2,X1)
      | r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)
              | r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)
              | r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ~ r2_hidden(X2,X1)
               => r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_tmap_1)).

fof(f223,plain,(
    spl7_36 ),
    inference(avatar_split_clause,[],[f66,f221])).

fof(f66,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_tmap_1)).

fof(f215,plain,(
    spl7_34 ),
    inference(avatar_split_clause,[],[f65,f213])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f208,plain,(
    spl7_33 ),
    inference(avatar_split_clause,[],[f54,f206])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | m1_subset_1(X2,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_pre_topc)).

fof(f195,plain,(
    spl7_30 ),
    inference(avatar_split_clause,[],[f69,f193])).

fof(f69,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | l1_pre_topc(k6_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_tmap_1)).

fof(f184,plain,(
    spl7_27 ),
    inference(avatar_split_clause,[],[f64,f182])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_funct_1(k7_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f179,plain,(
    spl7_26 ),
    inference(avatar_split_clause,[],[f63,f177])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_pre_topc(k6_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1))
        & ~ v2_struct_0(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1))
        & ~ v2_struct_0(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1))
        & ~ v2_struct_0(k6_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_tmap_1)).

fof(f164,plain,(
    spl7_22 ),
    inference(avatar_split_clause,[],[f61,f162])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_struct_0(k6_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f156,plain,
    ( spl7_21
    | ~ spl7_7
    | ~ spl7_18 ),
    inference(avatar_split_clause,[],[f152,f141,f97,f154])).

fof(f97,plain,
    ( spl7_7
  <=> r1_xboole_0(u1_struct_0(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f141,plain,
    ( spl7_18
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(X2,X0)
        | ~ r2_hidden(X2,X1)
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f152,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,u1_struct_0(sK2)) )
    | ~ spl7_7
    | ~ spl7_18 ),
    inference(resolution,[],[f142,f98])).

fof(f98,plain,
    ( r1_xboole_0(u1_struct_0(sK2),sK1)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f97])).

fof(f142,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | ~ r2_hidden(X2,X1)
        | ~ r2_hidden(X2,X0) )
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f141])).

fof(f151,plain,(
    spl7_20 ),
    inference(avatar_split_clause,[],[f50,f149])).

fof(f50,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc4_struct_0)).

fof(f147,plain,(
    spl7_19 ),
    inference(avatar_split_clause,[],[f70,f145])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f143,plain,(
    spl7_18 ),
    inference(avatar_split_clause,[],[f57,f141])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f139,plain,(
    spl7_17 ),
    inference(avatar_split_clause,[],[f60,f137])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f127,plain,(
    spl7_14 ),
    inference(avatar_split_clause,[],[f51,f125])).

fof(f51,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | ~ v1_xboole_0(sK4(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f123,plain,(
    spl7_13 ),
    inference(avatar_split_clause,[],[f49,f121])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f119,plain,(
    spl7_12 ),
    inference(avatar_split_clause,[],[f55,f117])).

fof(f55,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f111,plain,(
    ~ spl7_10 ),
    inference(avatar_split_clause,[],[f40,f109])).

fof(f40,plain,(
    ~ r1_tmap_1(sK2,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
                  & m1_subset_1(X3,u1_struct_0(X2)) )
              & r1_xboole_0(u1_struct_0(X2),X1)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
                  & m1_subset_1(X3,u1_struct_0(X2)) )
              & r1_xboole_0(u1_struct_0(X2),X1)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ( r1_xboole_0(u1_struct_0(X2),X1)
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X2))
                     => r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( r1_xboole_0(u1_struct_0(X2),X1)
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X2))
                   => r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_tmap_1)).

fof(f107,plain,(
    spl7_9 ),
    inference(avatar_split_clause,[],[f48,f105])).

fof(f48,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f103,plain,(
    spl7_8 ),
    inference(avatar_split_clause,[],[f44,f101])).

fof(f44,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f99,plain,(
    spl7_7 ),
    inference(avatar_split_clause,[],[f43,f97])).

fof(f43,plain,(
    r1_xboole_0(u1_struct_0(sK2),sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f95,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f39,f93])).

fof(f39,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f18])).

fof(f91,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f42,f89])).

fof(f42,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f87,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f47,f85])).

fof(f47,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f83,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f46,f81])).

fof(f46,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f79,plain,(
    ~ spl7_2 ),
    inference(avatar_split_clause,[],[f45,f77])).

fof(f45,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f75,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f41,f73])).

fof(f41,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:05:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (8279)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.50  % (8287)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.50  % (8283)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.50  % (8286)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (8278)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.50  % (8283)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % (8289)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.51  % (8292)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f419,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f75,f79,f83,f87,f91,f95,f99,f103,f107,f111,f119,f123,f127,f139,f143,f147,f151,f156,f164,f179,f184,f195,f208,f215,f223,f233,f237,f246,f253,f267,f285,f291,f295,f326,f336,f339,f346,f366,f387,f393,f401,f418])).
% 0.21/0.51  fof(f418,plain,(
% 0.21/0.51    ~spl7_59 | spl7_1 | ~spl7_14 | ~spl7_62),
% 0.21/0.51    inference(avatar_split_clause,[],[f405,f399,f125,f73,f382])).
% 0.21/0.51  fof(f382,plain,(
% 0.21/0.51    spl7_59 <=> l1_struct_0(sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_59])])).
% 0.21/0.51  fof(f73,plain,(
% 0.21/0.51    spl7_1 <=> v2_struct_0(sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.21/0.51  fof(f125,plain,(
% 0.21/0.51    spl7_14 <=> ! [X0] : (v2_struct_0(X0) | ~l1_struct_0(X0) | ~v1_xboole_0(sK4(X0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 0.21/0.51  fof(f399,plain,(
% 0.21/0.51    spl7_62 <=> v1_xboole_0(sK4(sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_62])])).
% 0.21/0.51  fof(f405,plain,(
% 0.21/0.51    ~l1_struct_0(sK2) | (spl7_1 | ~spl7_14 | ~spl7_62)),
% 0.21/0.51    inference(subsumption_resolution,[],[f402,f74])).
% 0.21/0.51  fof(f74,plain,(
% 0.21/0.51    ~v2_struct_0(sK2) | spl7_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f73])).
% 0.21/0.51  fof(f402,plain,(
% 0.21/0.51    ~l1_struct_0(sK2) | v2_struct_0(sK2) | (~spl7_14 | ~spl7_62)),
% 0.21/0.51    inference(resolution,[],[f400,f126])).
% 0.21/0.51  fof(f126,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_xboole_0(sK4(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) ) | ~spl7_14),
% 0.21/0.51    inference(avatar_component_clause,[],[f125])).
% 0.21/0.51  fof(f400,plain,(
% 0.21/0.51    v1_xboole_0(sK4(sK2)) | ~spl7_62),
% 0.21/0.51    inference(avatar_component_clause,[],[f399])).
% 0.21/0.51  fof(f401,plain,(
% 0.21/0.51    spl7_62 | ~spl7_12 | ~spl7_60),
% 0.21/0.51    inference(avatar_split_clause,[],[f394,f385,f117,f399])).
% 0.21/0.51  fof(f117,plain,(
% 0.21/0.51    spl7_12 <=> ! [X0] : (r2_hidden(sK5(X0),X0) | v1_xboole_0(X0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.21/0.51  fof(f385,plain,(
% 0.21/0.51    spl7_60 <=> ! [X0] : ~r2_hidden(X0,sK4(sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_60])])).
% 0.21/0.51  fof(f394,plain,(
% 0.21/0.51    v1_xboole_0(sK4(sK2)) | (~spl7_12 | ~spl7_60)),
% 0.21/0.51    inference(resolution,[],[f386,f118])).
% 0.21/0.51  fof(f118,plain,(
% 0.21/0.51    ( ! [X0] : (r2_hidden(sK5(X0),X0) | v1_xboole_0(X0)) ) | ~spl7_12),
% 0.21/0.51    inference(avatar_component_clause,[],[f117])).
% 0.21/0.51  fof(f386,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(X0,sK4(sK2))) ) | ~spl7_60),
% 0.21/0.51    inference(avatar_component_clause,[],[f385])).
% 0.21/0.51  fof(f393,plain,(
% 0.21/0.51    ~spl7_46 | ~spl7_9 | spl7_59),
% 0.21/0.51    inference(avatar_split_clause,[],[f388,f382,f105,f279])).
% 0.21/0.51  fof(f279,plain,(
% 0.21/0.51    spl7_46 <=> l1_pre_topc(sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_46])])).
% 0.21/0.51  fof(f105,plain,(
% 0.21/0.51    spl7_9 <=> ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.21/0.51  fof(f388,plain,(
% 0.21/0.51    ~l1_pre_topc(sK2) | (~spl7_9 | spl7_59)),
% 0.21/0.51    inference(resolution,[],[f383,f106])).
% 0.21/0.51  fof(f106,plain,(
% 0.21/0.51    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) ) | ~spl7_9),
% 0.21/0.51    inference(avatar_component_clause,[],[f105])).
% 0.21/0.51  fof(f383,plain,(
% 0.21/0.51    ~l1_struct_0(sK2) | spl7_59),
% 0.21/0.51    inference(avatar_component_clause,[],[f382])).
% 0.21/0.51  fof(f387,plain,(
% 0.21/0.51    ~spl7_59 | spl7_60 | spl7_1 | ~spl7_20 | ~spl7_52),
% 0.21/0.51    inference(avatar_split_clause,[],[f358,f324,f149,f73,f385,f382])).
% 0.21/0.51  fof(f149,plain,(
% 0.21/0.51    spl7_20 <=> ! [X0] : (v2_struct_0(X0) | ~l1_struct_0(X0) | m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).
% 0.21/0.51  fof(f324,plain,(
% 0.21/0.51    spl7_52 <=> ! [X1,X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | ~r2_hidden(X1,X0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_52])])).
% 0.21/0.51  fof(f358,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(X0,sK4(sK2)) | ~l1_struct_0(sK2)) ) | (spl7_1 | ~spl7_20 | ~spl7_52)),
% 0.21/0.51    inference(subsumption_resolution,[],[f357,f74])).
% 0.21/0.51  fof(f357,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(X0,sK4(sK2)) | ~l1_struct_0(sK2) | v2_struct_0(sK2)) ) | (~spl7_20 | ~spl7_52)),
% 0.21/0.51    inference(resolution,[],[f325,f150])).
% 0.21/0.51  fof(f150,plain,(
% 0.21/0.51    ( ! [X0] : (m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0) | v2_struct_0(X0)) ) | ~spl7_20),
% 0.21/0.51    inference(avatar_component_clause,[],[f149])).
% 0.21/0.51  fof(f325,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | ~r2_hidden(X1,X0)) ) | ~spl7_52),
% 0.21/0.51    inference(avatar_component_clause,[],[f324])).
% 0.21/0.51  % (8275)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  fof(f366,plain,(
% 0.21/0.51    spl7_29 | ~spl7_6 | ~spl7_17 | spl7_55),
% 0.21/0.51    inference(avatar_split_clause,[],[f364,f344,f137,f93,f189])).
% 0.21/0.51  fof(f189,plain,(
% 0.21/0.51    spl7_29 <=> v1_xboole_0(u1_struct_0(sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).
% 0.21/0.51  fof(f93,plain,(
% 0.21/0.51    spl7_6 <=> m1_subset_1(sK3,u1_struct_0(sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.21/0.51  fof(f137,plain,(
% 0.21/0.51    spl7_17 <=> ! [X1,X0] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).
% 0.21/0.51  fof(f344,plain,(
% 0.21/0.51    spl7_55 <=> r2_hidden(sK3,u1_struct_0(sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_55])])).
% 0.21/0.51  fof(f364,plain,(
% 0.21/0.51    v1_xboole_0(u1_struct_0(sK2)) | (~spl7_6 | ~spl7_17 | spl7_55)),
% 0.21/0.51    inference(subsumption_resolution,[],[f359,f94])).
% 0.21/0.51  fof(f94,plain,(
% 0.21/0.51    m1_subset_1(sK3,u1_struct_0(sK2)) | ~spl7_6),
% 0.21/0.51    inference(avatar_component_clause,[],[f93])).
% 0.21/0.51  fof(f359,plain,(
% 0.21/0.51    v1_xboole_0(u1_struct_0(sK2)) | ~m1_subset_1(sK3,u1_struct_0(sK2)) | (~spl7_17 | spl7_55)),
% 0.21/0.51    inference(resolution,[],[f345,f138])).
% 0.21/0.51  fof(f138,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) ) | ~spl7_17),
% 0.21/0.51    inference(avatar_component_clause,[],[f137])).
% 0.21/0.51  fof(f345,plain,(
% 0.21/0.51    ~r2_hidden(sK3,u1_struct_0(sK2)) | spl7_55),
% 0.21/0.51    inference(avatar_component_clause,[],[f344])).
% 0.21/0.51  fof(f346,plain,(
% 0.21/0.51    ~spl7_55 | ~spl7_21 | ~spl7_53),
% 0.21/0.51    inference(avatar_split_clause,[],[f342,f331,f154,f344])).
% 0.21/0.51  fof(f154,plain,(
% 0.21/0.51    spl7_21 <=> ! [X0] : (~r2_hidden(X0,sK1) | ~r2_hidden(X0,u1_struct_0(sK2)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).
% 0.21/0.51  fof(f331,plain,(
% 0.21/0.51    spl7_53 <=> r2_hidden(sK3,sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_53])])).
% 0.21/0.51  fof(f342,plain,(
% 0.21/0.51    ~r2_hidden(sK3,u1_struct_0(sK2)) | (~spl7_21 | ~spl7_53)),
% 0.21/0.51    inference(resolution,[],[f332,f155])).
% 0.21/0.51  fof(f155,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(X0,sK1) | ~r2_hidden(X0,u1_struct_0(sK2))) ) | ~spl7_21),
% 0.21/0.51    inference(avatar_component_clause,[],[f154])).
% 0.21/0.51  fof(f332,plain,(
% 0.21/0.51    r2_hidden(sK3,sK1) | ~spl7_53),
% 0.21/0.51    inference(avatar_component_clause,[],[f331])).
% 0.21/0.51  fof(f339,plain,(
% 0.21/0.51    spl7_1 | spl7_2 | ~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_33 | spl7_54),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f337])).
% 0.21/0.51  fof(f337,plain,(
% 0.21/0.51    $false | (spl7_1 | spl7_2 | ~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_33 | spl7_54)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f78,f86,f74,f90,f94,f335,f207])).
% 0.21/0.51  fof(f207,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (m1_subset_1(X2,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X1)) | v2_struct_0(X0)) ) | ~spl7_33),
% 0.21/0.51    inference(avatar_component_clause,[],[f206])).
% 0.21/0.51  fof(f206,plain,(
% 0.21/0.51    spl7_33 <=> ! [X1,X0,X2] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X1)) | m1_subset_1(X2,u1_struct_0(X0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).
% 0.21/0.51  fof(f335,plain,(
% 0.21/0.51    ~m1_subset_1(sK3,u1_struct_0(sK0)) | spl7_54),
% 0.21/0.51    inference(avatar_component_clause,[],[f334])).
% 0.21/0.51  fof(f334,plain,(
% 0.21/0.51    spl7_54 <=> m1_subset_1(sK3,u1_struct_0(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_54])])).
% 0.21/0.51  fof(f90,plain,(
% 0.21/0.51    m1_pre_topc(sK2,sK0) | ~spl7_5),
% 0.21/0.51    inference(avatar_component_clause,[],[f89])).
% 0.21/0.51  fof(f89,plain,(
% 0.21/0.51    spl7_5 <=> m1_pre_topc(sK2,sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.21/0.51  fof(f86,plain,(
% 0.21/0.51    l1_pre_topc(sK0) | ~spl7_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f85])).
% 0.21/0.51  fof(f85,plain,(
% 0.21/0.51    spl7_4 <=> l1_pre_topc(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.21/0.51  fof(f78,plain,(
% 0.21/0.51    ~v2_struct_0(sK0) | spl7_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f77])).
% 0.21/0.51  fof(f77,plain,(
% 0.21/0.51    spl7_2 <=> v2_struct_0(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.21/0.51  fof(f336,plain,(
% 0.21/0.51    spl7_53 | ~spl7_54 | spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_8 | ~spl7_38 | spl7_48),
% 0.21/0.51    inference(avatar_split_clause,[],[f300,f293,f231,f101,f85,f81,f77,f334,f331])).
% 0.21/0.51  fof(f81,plain,(
% 0.21/0.51    spl7_3 <=> v2_pre_topc(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.21/0.51  fof(f101,plain,(
% 0.21/0.51    spl7_8 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.21/0.51  fof(f231,plain,(
% 0.21/0.51    spl7_38 <=> ! [X1,X0,X2] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | r2_hidden(X2,X1) | r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_38])])).
% 0.21/0.51  fof(f293,plain,(
% 0.21/0.51    spl7_48 <=> r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK3)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_48])])).
% 0.21/0.51  fof(f300,plain,(
% 0.21/0.51    ~m1_subset_1(sK3,u1_struct_0(sK0)) | r2_hidden(sK3,sK1) | (spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_8 | ~spl7_38 | spl7_48)),
% 0.21/0.51    inference(subsumption_resolution,[],[f299,f78])).
% 0.21/0.51  fof(f299,plain,(
% 0.21/0.51    ~m1_subset_1(sK3,u1_struct_0(sK0)) | r2_hidden(sK3,sK1) | v2_struct_0(sK0) | (~spl7_3 | ~spl7_4 | ~spl7_8 | ~spl7_38 | spl7_48)),
% 0.21/0.51    inference(subsumption_resolution,[],[f298,f102])).
% 0.21/0.51  fof(f102,plain,(
% 0.21/0.51    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl7_8),
% 0.21/0.51    inference(avatar_component_clause,[],[f101])).
% 0.21/0.51  fof(f298,plain,(
% 0.21/0.51    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | r2_hidden(sK3,sK1) | v2_struct_0(sK0) | (~spl7_3 | ~spl7_4 | ~spl7_38 | spl7_48)),
% 0.21/0.51    inference(subsumption_resolution,[],[f297,f86])).
% 0.21/0.51  fof(f297,plain,(
% 0.21/0.51    ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | r2_hidden(sK3,sK1) | v2_struct_0(sK0) | (~spl7_3 | ~spl7_38 | spl7_48)),
% 0.21/0.51    inference(subsumption_resolution,[],[f296,f82])).
% 0.21/0.51  fof(f82,plain,(
% 0.21/0.51    v2_pre_topc(sK0) | ~spl7_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f81])).
% 0.21/0.51  fof(f296,plain,(
% 0.21/0.51    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | r2_hidden(sK3,sK1) | v2_struct_0(sK0) | (~spl7_38 | spl7_48)),
% 0.21/0.51    inference(resolution,[],[f294,f232])).
% 0.21/0.51  fof(f232,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | r2_hidden(X2,X1) | v2_struct_0(X0)) ) | ~spl7_38),
% 0.21/0.51    inference(avatar_component_clause,[],[f231])).
% 0.21/0.51  fof(f294,plain,(
% 0.21/0.51    ~r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK3) | spl7_48),
% 0.21/0.51    inference(avatar_component_clause,[],[f293])).
% 0.21/0.51  fof(f326,plain,(
% 0.21/0.51    spl7_52 | ~spl7_19 | ~spl7_29),
% 0.21/0.51    inference(avatar_split_clause,[],[f317,f189,f145,f324])).
% 0.21/0.51  fof(f145,plain,(
% 0.21/0.51    spl7_19 <=> ! [X1,X0,X2] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).
% 0.21/0.51  fof(f317,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | ~r2_hidden(X1,X0)) ) | (~spl7_19 | ~spl7_29)),
% 0.21/0.51    inference(resolution,[],[f190,f146])).
% 0.21/0.51  fof(f146,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) ) | ~spl7_19),
% 0.21/0.51    inference(avatar_component_clause,[],[f145])).
% 0.21/0.51  fof(f190,plain,(
% 0.21/0.51    v1_xboole_0(u1_struct_0(sK2)) | ~spl7_29),
% 0.21/0.51    inference(avatar_component_clause,[],[f189])).
% 0.21/0.51  fof(f295,plain,(
% 0.21/0.51    ~spl7_48 | ~spl7_6 | ~spl7_8 | spl7_10 | ~spl7_47),
% 0.21/0.51    inference(avatar_split_clause,[],[f288,f283,f109,f101,f93,f293])).
% 0.21/0.51  fof(f109,plain,(
% 0.21/0.51    spl7_10 <=> r1_tmap_1(sK2,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),sK3)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.21/0.51  fof(f283,plain,(
% 0.21/0.51    spl7_47 <=> ! [X1,X0] : (~m1_subset_1(X0,u1_struct_0(sK2)) | ~r1_tmap_1(sK0,k6_tmap_1(sK0,X1),k7_tmap_1(sK0,X1),X0) | r1_tmap_1(sK2,k6_tmap_1(sK0,X1),k2_tmap_1(sK0,k6_tmap_1(sK0,X1),k7_tmap_1(sK0,X1),sK2),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_47])])).
% 0.21/0.51  fof(f288,plain,(
% 0.21/0.51    ~r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK3) | (~spl7_6 | ~spl7_8 | spl7_10 | ~spl7_47)),
% 0.21/0.51    inference(subsumption_resolution,[],[f287,f102])).
% 0.21/0.51  fof(f287,plain,(
% 0.21/0.51    ~r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK3) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl7_6 | spl7_10 | ~spl7_47)),
% 0.21/0.51    inference(subsumption_resolution,[],[f286,f94])).
% 0.21/0.51  fof(f286,plain,(
% 0.21/0.51    ~r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK3) | ~m1_subset_1(sK3,u1_struct_0(sK2)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (spl7_10 | ~spl7_47)),
% 0.21/0.51    inference(resolution,[],[f284,f110])).
% 0.21/0.51  fof(f110,plain,(
% 0.21/0.51    ~r1_tmap_1(sK2,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),sK3) | spl7_10),
% 0.21/0.51    inference(avatar_component_clause,[],[f109])).
% 0.21/0.51  fof(f284,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tmap_1(sK2,k6_tmap_1(sK0,X1),k2_tmap_1(sK0,k6_tmap_1(sK0,X1),k7_tmap_1(sK0,X1),sK2),X0) | ~r1_tmap_1(sK0,k6_tmap_1(sK0,X1),k7_tmap_1(sK0,X1),X0) | ~m1_subset_1(X0,u1_struct_0(sK2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl7_47),
% 0.21/0.51    inference(avatar_component_clause,[],[f283])).
% 0.21/0.51  fof(f291,plain,(
% 0.21/0.51    ~spl7_4 | ~spl7_5 | ~spl7_13 | spl7_46),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f289])).
% 0.21/0.51  fof(f289,plain,(
% 0.21/0.51    $false | (~spl7_4 | ~spl7_5 | ~spl7_13 | spl7_46)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f86,f90,f280,f122])).
% 0.21/0.51  fof(f122,plain,(
% 0.21/0.51    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) ) | ~spl7_13),
% 0.21/0.51    inference(avatar_component_clause,[],[f121])).
% 0.21/0.51  fof(f121,plain,(
% 0.21/0.51    spl7_13 <=> ! [X1,X0] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 0.21/0.51  fof(f280,plain,(
% 0.21/0.51    ~l1_pre_topc(sK2) | spl7_46),
% 0.21/0.51    inference(avatar_component_clause,[],[f279])).
% 0.21/0.51  fof(f285,plain,(
% 0.21/0.51    spl7_47 | spl7_1 | spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_44),
% 0.21/0.51    inference(avatar_split_clause,[],[f274,f265,f89,f85,f81,f77,f73,f283])).
% 0.21/0.51  fof(f265,plain,(
% 0.21/0.51    spl7_44 <=> ! [X1,X3,X0,X2] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X3) | r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_44])])).
% 0.21/0.51  fof(f274,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK2)) | ~r1_tmap_1(sK0,k6_tmap_1(sK0,X1),k7_tmap_1(sK0,X1),X0) | r1_tmap_1(sK2,k6_tmap_1(sK0,X1),k2_tmap_1(sK0,k6_tmap_1(sK0,X1),k7_tmap_1(sK0,X1),sK2),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (spl7_1 | spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_44)),
% 0.21/0.51    inference(subsumption_resolution,[],[f273,f78])).
% 0.21/0.51  fof(f273,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK2)) | ~r1_tmap_1(sK0,k6_tmap_1(sK0,X1),k7_tmap_1(sK0,X1),X0) | r1_tmap_1(sK2,k6_tmap_1(sK0,X1),k2_tmap_1(sK0,k6_tmap_1(sK0,X1),k7_tmap_1(sK0,X1),sK2),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (spl7_1 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_44)),
% 0.21/0.51    inference(subsumption_resolution,[],[f272,f74])).
% 0.21/0.51  fof(f272,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v2_struct_0(sK2) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK2)) | ~r1_tmap_1(sK0,k6_tmap_1(sK0,X1),k7_tmap_1(sK0,X1),X0) | r1_tmap_1(sK2,k6_tmap_1(sK0,X1),k2_tmap_1(sK0,k6_tmap_1(sK0,X1),k7_tmap_1(sK0,X1),sK2),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_44)),
% 0.21/0.51    inference(subsumption_resolution,[],[f271,f86])).
% 0.21/0.51  fof(f271,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~l1_pre_topc(sK0) | v2_struct_0(sK2) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK2)) | ~r1_tmap_1(sK0,k6_tmap_1(sK0,X1),k7_tmap_1(sK0,X1),X0) | r1_tmap_1(sK2,k6_tmap_1(sK0,X1),k2_tmap_1(sK0,k6_tmap_1(sK0,X1),k7_tmap_1(sK0,X1),sK2),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl7_3 | ~spl7_5 | ~spl7_44)),
% 0.21/0.51    inference(subsumption_resolution,[],[f270,f82])).
% 0.21/0.51  fof(f270,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK2) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK2)) | ~r1_tmap_1(sK0,k6_tmap_1(sK0,X1),k7_tmap_1(sK0,X1),X0) | r1_tmap_1(sK2,k6_tmap_1(sK0,X1),k2_tmap_1(sK0,k6_tmap_1(sK0,X1),k7_tmap_1(sK0,X1),sK2),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl7_5 | ~spl7_44)),
% 0.21/0.51    inference(resolution,[],[f266,f90])).
% 0.21/0.51  fof(f266,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (~m1_pre_topc(X2,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X2) | v2_struct_0(X0) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X3) | r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) ) | ~spl7_44),
% 0.21/0.51    inference(avatar_component_clause,[],[f265])).
% 0.21/0.51  fof(f267,plain,(
% 0.21/0.51    spl7_44 | ~spl7_22 | ~spl7_26 | ~spl7_30 | ~spl7_34 | ~spl7_36 | ~spl7_42),
% 0.21/0.51    inference(avatar_split_clause,[],[f263,f251,f221,f213,f193,f177,f162,f265])).
% 0.21/0.51  fof(f162,plain,(
% 0.21/0.51    spl7_22 <=> ! [X1,X0] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_struct_0(k6_tmap_1(X0,X1)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).
% 0.21/0.51  fof(f177,plain,(
% 0.21/0.51    spl7_26 <=> ! [X1,X0] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_pre_topc(k6_tmap_1(X0,X1)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).
% 0.21/0.51  fof(f193,plain,(
% 0.21/0.51    spl7_30 <=> ! [X1,X0] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | l1_pre_topc(k6_tmap_1(X0,X1)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).
% 0.21/0.51  fof(f213,plain,(
% 0.21/0.51    spl7_34 <=> ! [X1,X0] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).
% 0.21/0.51  fof(f221,plain,(
% 0.21/0.51    spl7_36 <=> ! [X1,X0] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).
% 0.21/0.51  fof(f251,plain,(
% 0.21/0.51    spl7_42 <=> ! [X1,X3,X5,X0,X2,X4] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~v1_funct_2(k7_tmap_1(X2,X3),u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(k7_tmap_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X4) | ~m1_pre_topc(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X4)) | ~r1_tmap_1(X1,X0,k7_tmap_1(X2,X3),X5) | r1_tmap_1(X4,X0,k2_tmap_1(X1,X0,k7_tmap_1(X2,X3),X4),X5) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | v2_struct_0(X2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_42])])).
% 0.21/0.51  fof(f263,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X3) | r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) ) | (~spl7_22 | ~spl7_26 | ~spl7_30 | ~spl7_34 | ~spl7_36 | ~spl7_42)),
% 0.21/0.51    inference(subsumption_resolution,[],[f262,f222])).
% 0.21/0.51  fof(f222,plain,(
% 0.21/0.51    ( ! [X0,X1] : (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_struct_0(X0)) ) | ~spl7_36),
% 0.21/0.51    inference(avatar_component_clause,[],[f221])).
% 0.21/0.51  fof(f262,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X3) | r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) ) | (~spl7_22 | ~spl7_26 | ~spl7_30 | ~spl7_34 | ~spl7_42)),
% 0.21/0.51    inference(subsumption_resolution,[],[f261,f194])).
% 0.21/0.51  fof(f194,plain,(
% 0.21/0.51    ( ! [X0,X1] : (l1_pre_topc(k6_tmap_1(X0,X1)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_struct_0(X0)) ) | ~spl7_30),
% 0.21/0.51    inference(avatar_component_clause,[],[f193])).
% 0.21/0.51  fof(f261,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (~l1_pre_topc(k6_tmap_1(X0,X1)) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X3) | r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) ) | (~spl7_22 | ~spl7_26 | ~spl7_34 | ~spl7_42)),
% 0.21/0.51    inference(subsumption_resolution,[],[f260,f178])).
% 0.21/0.51  fof(f178,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v2_pre_topc(k6_tmap_1(X0,X1)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_struct_0(X0)) ) | ~spl7_26),
% 0.21/0.51    inference(avatar_component_clause,[],[f177])).
% 0.21/0.51  fof(f260,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (~l1_pre_topc(k6_tmap_1(X0,X1)) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(k6_tmap_1(X0,X1)) | ~m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X3) | r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) ) | (~spl7_22 | ~spl7_34 | ~spl7_42)),
% 0.21/0.51    inference(subsumption_resolution,[],[f259,f163])).
% 0.21/0.51  fof(f163,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v2_struct_0(k6_tmap_1(X0,X1)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_struct_0(X0)) ) | ~spl7_22),
% 0.21/0.51    inference(avatar_component_clause,[],[f162])).
% 0.21/0.51  fof(f259,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (~l1_pre_topc(k6_tmap_1(X0,X1)) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(k6_tmap_1(X0,X1)) | ~v2_pre_topc(k6_tmap_1(X0,X1)) | ~m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X3) | r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) ) | (~spl7_34 | ~spl7_42)),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f258])).
% 0.21/0.51  fof(f258,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (~l1_pre_topc(k6_tmap_1(X0,X1)) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(k6_tmap_1(X0,X1)) | ~v2_pre_topc(k6_tmap_1(X0,X1)) | ~m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X3) | r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_struct_0(X0)) ) | (~spl7_34 | ~spl7_42)),
% 0.21/0.51    inference(resolution,[],[f252,f214])).
% 0.21/0.51  fof(f214,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_struct_0(X0)) ) | ~spl7_34),
% 0.21/0.51    inference(avatar_component_clause,[],[f213])).
% 0.21/0.51  % (8288)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.51  fof(f252,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_2(k7_tmap_1(X2,X3),u1_struct_0(X1),u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(k7_tmap_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X4) | ~m1_pre_topc(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X4)) | ~r1_tmap_1(X1,X0,k7_tmap_1(X2,X3),X5) | r1_tmap_1(X4,X0,k2_tmap_1(X1,X0,k7_tmap_1(X2,X3),X4),X5) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | v2_struct_0(X2)) ) | ~spl7_42),
% 0.21/0.51    inference(avatar_component_clause,[],[f251])).
% 0.21/0.51  fof(f253,plain,(
% 0.21/0.51    spl7_42 | ~spl7_27 | ~spl7_41),
% 0.21/0.51    inference(avatar_split_clause,[],[f247,f244,f182,f251])).
% 0.21/0.51  fof(f182,plain,(
% 0.21/0.51    spl7_27 <=> ! [X1,X0] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_funct_1(k7_tmap_1(X0,X1)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).
% 0.21/0.51  fof(f244,plain,(
% 0.21/0.51    spl7_41 <=> ! [X1,X3,X5,X0,X2] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~r1_tmap_1(X1,X0,X2,X5) | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_41])])).
% 0.21/0.51  fof(f247,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~v1_funct_2(k7_tmap_1(X2,X3),u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(k7_tmap_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X4) | ~m1_pre_topc(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X4)) | ~r1_tmap_1(X1,X0,k7_tmap_1(X2,X3),X5) | r1_tmap_1(X4,X0,k2_tmap_1(X1,X0,k7_tmap_1(X2,X3),X4),X5) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | v2_struct_0(X2)) ) | (~spl7_27 | ~spl7_41)),
% 0.21/0.51    inference(resolution,[],[f245,f183])).
% 0.21/0.51  fof(f183,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v1_funct_1(k7_tmap_1(X0,X1)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_struct_0(X0)) ) | ~spl7_27),
% 0.21/0.51    inference(avatar_component_clause,[],[f182])).
% 0.21/0.51  fof(f245,plain,(
% 0.21/0.51    ( ! [X2,X0,X5,X3,X1] : (~v1_funct_1(X2) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X0) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~r1_tmap_1(X1,X0,X2,X5) | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) ) | ~spl7_41),
% 0.21/0.51    inference(avatar_component_clause,[],[f244])).
% 0.21/0.51  fof(f246,plain,(
% 0.21/0.51    spl7_41 | ~spl7_33 | ~spl7_39),
% 0.21/0.51    inference(avatar_split_clause,[],[f238,f235,f206,f244])).
% 0.21/0.51  fof(f235,plain,(
% 0.21/0.51    spl7_39 <=> ! [X1,X3,X5,X0,X2] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~r1_tmap_1(X1,X0,X2,X5) | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_39])])).
% 0.21/0.51  fof(f238,plain,(
% 0.21/0.51    ( ! [X2,X0,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~r1_tmap_1(X1,X0,X2,X5) | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) ) | (~spl7_33 | ~spl7_39)),
% 0.21/0.51    inference(subsumption_resolution,[],[f236,f207])).
% 0.21/0.51  fof(f236,plain,(
% 0.21/0.51    ( ! [X2,X0,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~r1_tmap_1(X1,X0,X2,X5) | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) ) | ~spl7_39),
% 0.21/0.51    inference(avatar_component_clause,[],[f235])).
% 0.21/0.51  fof(f237,plain,(
% 0.21/0.51    spl7_39),
% 0.21/0.51    inference(avatar_split_clause,[],[f71,f235])).
% 0.21/0.51  fof(f71,plain,(
% 0.21/0.51    ( ! [X2,X0,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~r1_tmap_1(X1,X0,X2,X5) | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) )),
% 0.21/0.51    inference(equality_resolution,[],[f53])).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(X3)) | X4 != X5 | ~r1_tmap_1(X1,X0,X2,X4) | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | (~r1_tmap_1(X1,X0,X2,X4) | X4 != X5)) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,axiom,(
% 0.21/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ((r1_tmap_1(X1,X0,X2,X4) & X4 = X5) => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5))))))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tmap_1)).
% 0.21/0.51  fof(f233,plain,(
% 0.21/0.51    spl7_38),
% 0.21/0.51    inference(avatar_split_clause,[],[f52,f231])).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | r2_hidden(X2,X1) | r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2) | r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : ((r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2) | r2_hidden(X2,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,axiom,(
% 0.21/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (~r2_hidden(X2,X1) => r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_tmap_1)).
% 0.21/0.51  fof(f223,plain,(
% 0.21/0.51    spl7_36),
% 0.21/0.51    inference(avatar_split_clause,[],[f66,f221])).
% 0.21/0.51  fof(f66,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f35])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f34])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,axiom,(
% 0.21/0.51    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_tmap_1)).
% 0.21/0.51  fof(f215,plain,(
% 0.21/0.51    spl7_34),
% 0.21/0.51    inference(avatar_split_clause,[],[f65,f213])).
% 0.21/0.51  fof(f65,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f35])).
% 0.21/0.51  fof(f208,plain,(
% 0.21/0.51    spl7_33),
% 0.21/0.51    inference(avatar_split_clause,[],[f54,f206])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X1)) | m1_subset_1(X2,u1_struct_0(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_pre_topc)).
% 0.21/0.51  fof(f195,plain,(
% 0.21/0.51    spl7_30),
% 0.21/0.51    inference(avatar_split_clause,[],[f69,f193])).
% 0.21/0.51  fof(f69,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | l1_pre_topc(k6_tmap_1(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f37])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ! [X0,X1] : ((l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f36])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ! [X0,X1] : ((l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,axiom,(
% 0.21/0.51    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_tmap_1)).
% 0.21/0.51  fof(f184,plain,(
% 0.21/0.51    spl7_27),
% 0.21/0.51    inference(avatar_split_clause,[],[f64,f182])).
% 0.21/0.51  fof(f64,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_funct_1(k7_tmap_1(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f35])).
% 0.21/0.51  fof(f179,plain,(
% 0.21/0.51    spl7_26),
% 0.21/0.51    inference(avatar_split_clause,[],[f63,f177])).
% 0.21/0.51  fof(f63,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_pre_topc(k6_tmap_1(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f33])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ! [X0,X1] : ((v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1)) & ~v2_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f32])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ! [X0,X1] : ((v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1)) & ~v2_struct_0(k6_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,axiom,(
% 0.21/0.51    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1)) & ~v2_struct_0(k6_tmap_1(X0,X1))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_tmap_1)).
% 0.21/0.51  fof(f164,plain,(
% 0.21/0.51    spl7_22),
% 0.21/0.51    inference(avatar_split_clause,[],[f61,f162])).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_struct_0(k6_tmap_1(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f33])).
% 0.21/0.51  fof(f156,plain,(
% 0.21/0.51    spl7_21 | ~spl7_7 | ~spl7_18),
% 0.21/0.51    inference(avatar_split_clause,[],[f152,f141,f97,f154])).
% 0.21/0.51  fof(f97,plain,(
% 0.21/0.51    spl7_7 <=> r1_xboole_0(u1_struct_0(sK2),sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.21/0.51  fof(f141,plain,(
% 0.21/0.51    spl7_18 <=> ! [X1,X0,X2] : (~r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 0.21/0.51  fof(f152,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(X0,sK1) | ~r2_hidden(X0,u1_struct_0(sK2))) ) | (~spl7_7 | ~spl7_18)),
% 0.21/0.51    inference(resolution,[],[f142,f98])).
% 0.21/0.51  fof(f98,plain,(
% 0.21/0.51    r1_xboole_0(u1_struct_0(sK2),sK1) | ~spl7_7),
% 0.21/0.51    inference(avatar_component_clause,[],[f97])).
% 0.21/0.51  fof(f142,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) ) | ~spl7_18),
% 0.21/0.51    inference(avatar_component_clause,[],[f141])).
% 0.21/0.51  fof(f151,plain,(
% 0.21/0.51    spl7_20),
% 0.21/0.51    inference(avatar_split_clause,[],[f50,f149])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    ( ! [X0] : (v2_struct_0(X0) | ~l1_struct_0(X0) | m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc4_struct_0)).
% 0.21/0.51  fof(f147,plain,(
% 0.21/0.51    spl7_19),
% 0.21/0.51    inference(avatar_split_clause,[],[f70,f145])).
% 0.21/0.51  fof(f70,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f38])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 0.21/0.51  fof(f143,plain,(
% 0.21/0.51    spl7_18),
% 0.21/0.51    inference(avatar_split_clause,[],[f57,f141])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.51    inference(rectify,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.21/0.51  fof(f139,plain,(
% 0.21/0.51    spl7_17),
% 0.21/0.51    inference(avatar_split_clause,[],[f60,f137])).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.51    inference(flattening,[],[f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.51  fof(f127,plain,(
% 0.21/0.51    spl7_14),
% 0.21/0.51    inference(avatar_split_clause,[],[f51,f125])).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    ( ! [X0] : (v2_struct_0(X0) | ~l1_struct_0(X0) | ~v1_xboole_0(sK4(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f22])).
% 0.21/0.51  fof(f123,plain,(
% 0.21/0.51    spl7_13),
% 0.21/0.51    inference(avatar_split_clause,[],[f49,f121])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.51  fof(f119,plain,(
% 0.21/0.51    spl7_12),
% 0.21/0.51    inference(avatar_split_clause,[],[f55,f117])).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    ( ! [X0] : (r2_hidden(sK5(X0),X0) | v1_xboole_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.51  fof(f111,plain,(
% 0.21/0.51    ~spl7_10),
% 0.21/0.51    inference(avatar_split_clause,[],[f40,f109])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ~r1_tmap_1(sK2,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),sK3)),
% 0.21/0.51    inference(cnf_transformation,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_xboole_0(u1_struct_0(X2),X1) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (~r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_xboole_0(u1_struct_0(X2),X1)) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f15])).
% 0.21/0.51  fof(f15,negated_conjecture,(
% 0.21/0.51    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (r1_xboole_0(u1_struct_0(X2),X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X2)) => r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3))))))),
% 0.21/0.51    inference(negated_conjecture,[],[f14])).
% 0.21/0.51  fof(f14,conjecture,(
% 0.21/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (r1_xboole_0(u1_struct_0(X2),X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X2)) => r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3))))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_tmap_1)).
% 0.21/0.51  fof(f107,plain,(
% 0.21/0.51    spl7_9),
% 0.21/0.51    inference(avatar_split_clause,[],[f48,f105])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.51  fof(f103,plain,(
% 0.21/0.51    spl7_8),
% 0.21/0.51    inference(avatar_split_clause,[],[f44,f101])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.51    inference(cnf_transformation,[],[f18])).
% 0.21/0.51  fof(f99,plain,(
% 0.21/0.51    spl7_7),
% 0.21/0.51    inference(avatar_split_clause,[],[f43,f97])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    r1_xboole_0(u1_struct_0(sK2),sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f18])).
% 0.21/0.51  fof(f95,plain,(
% 0.21/0.51    spl7_6),
% 0.21/0.51    inference(avatar_split_clause,[],[f39,f93])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    m1_subset_1(sK3,u1_struct_0(sK2))),
% 0.21/0.51    inference(cnf_transformation,[],[f18])).
% 0.21/0.51  fof(f91,plain,(
% 0.21/0.51    spl7_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f42,f89])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    m1_pre_topc(sK2,sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f18])).
% 0.21/0.51  fof(f87,plain,(
% 0.21/0.51    spl7_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f47,f85])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    l1_pre_topc(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f18])).
% 0.21/0.51  fof(f83,plain,(
% 0.21/0.51    spl7_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f46,f81])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    v2_pre_topc(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f18])).
% 0.21/0.51  fof(f79,plain,(
% 0.21/0.51    ~spl7_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f45,f77])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    ~v2_struct_0(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f18])).
% 0.21/0.51  fof(f75,plain,(
% 0.21/0.51    ~spl7_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f41,f73])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    ~v2_struct_0(sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f18])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (8283)------------------------------
% 0.21/0.51  % (8283)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (8283)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (8283)Memory used [KB]: 10874
% 0.21/0.51  % (8283)Time elapsed: 0.080 s
% 0.21/0.51  % (8283)------------------------------
% 0.21/0.51  % (8283)------------------------------
% 0.21/0.52  % (8280)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.52  % (8273)Success in time 0.159 s
%------------------------------------------------------------------------------
