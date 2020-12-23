%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:36 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 249 expanded)
%              Number of leaves         :   34 ( 107 expanded)
%              Depth                    :    7
%              Number of atoms          :  511 ( 906 expanded)
%              Number of equality atoms :   60 ( 128 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f252,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f45,f53,f57,f61,f65,f69,f77,f81,f85,f89,f100,f105,f109,f117,f123,f134,f142,f172,f178,f185,f190,f202,f210,f215,f223,f236,f251])).

fof(f251,plain,
    ( ~ spl3_1
    | ~ spl3_3
    | ~ spl3_12
    | spl3_35 ),
    inference(avatar_contradiction_clause,[],[f250])).

fof(f250,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_12
    | spl3_35 ),
    inference(subsumption_resolution,[],[f249,f44])).

fof(f44,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f43])).

fof(f43,plain,
    ( spl3_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f249,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl3_3
    | ~ spl3_12
    | spl3_35 ),
    inference(subsumption_resolution,[],[f246,f52])).

fof(f52,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl3_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f246,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_12
    | spl3_35 ),
    inference(resolution,[],[f235,f88])).

fof(f88,plain,
    ( ! [X0,X1] :
        ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl3_12
  <=> ! [X1,X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | m1_pre_topc(k1_pre_topc(X0,X1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f235,plain,
    ( ~ m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
    | spl3_35 ),
    inference(avatar_component_clause,[],[f234])).

fof(f234,plain,
    ( spl3_35
  <=> m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).

fof(f236,plain,
    ( ~ spl3_35
    | ~ spl3_1
    | ~ spl3_15
    | spl3_33 ),
    inference(avatar_split_clause,[],[f226,f221,f103,f43,f234])).

fof(f103,plain,
    ( spl3_15
  <=> ! [X1,X0] :
        ( ~ l1_pre_topc(X1)
        | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | ~ m1_pre_topc(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f221,plain,
    ( spl3_33
  <=> m1_pre_topc(k1_pre_topc(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f226,plain,
    ( ~ m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
    | ~ spl3_1
    | ~ spl3_15
    | spl3_33 ),
    inference(subsumption_resolution,[],[f224,f44])).

fof(f224,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
    | ~ spl3_15
    | spl3_33 ),
    inference(resolution,[],[f222,f104])).

fof(f104,plain,
    ( ! [X0,X1] :
        ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | ~ l1_pre_topc(X1)
        | ~ m1_pre_topc(X0,X1) )
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f103])).

fof(f222,plain,
    ( ~ m1_pre_topc(k1_pre_topc(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | spl3_33 ),
    inference(avatar_component_clause,[],[f221])).

fof(f223,plain,
    ( spl3_32
    | ~ spl3_33
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_27 ),
    inference(avatar_split_clause,[],[f195,f169,f51,f43,f221,f213])).

fof(f213,plain,
    ( spl3_32
  <=> k1_pre_topc(sK0,sK1) = k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f169,plain,
    ( spl3_27
  <=> ! [X1] :
        ( ~ m1_pre_topc(k1_pre_topc(X1,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ l1_pre_topc(X1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X1)))
        | k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) = k1_pre_topc(X1,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f195,plain,
    ( ~ m1_pre_topc(k1_pre_topc(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | k1_pre_topc(sK0,sK1) = k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_27 ),
    inference(subsumption_resolution,[],[f193,f44])).

fof(f193,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | k1_pre_topc(sK0,sK1) = k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl3_3
    | ~ spl3_27 ),
    inference(resolution,[],[f170,f52])).

fof(f170,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ l1_pre_topc(X1)
        | ~ m1_pre_topc(k1_pre_topc(X1,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) = k1_pre_topc(X1,sK1) )
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f169])).

fof(f215,plain,
    ( ~ spl3_32
    | spl3_5
    | ~ spl3_31 ),
    inference(avatar_split_clause,[],[f211,f200,f59,f213])).

fof(f59,plain,
    ( spl3_5
  <=> g1_pre_topc(u1_struct_0(k1_pre_topc(sK0,sK1)),u1_pre_topc(k1_pre_topc(sK0,sK1))) = k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f200,plain,
    ( spl3_31
  <=> k1_pre_topc(sK0,sK1) = g1_pre_topc(u1_struct_0(k1_pre_topc(sK0,sK1)),u1_pre_topc(k1_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f211,plain,
    ( k1_pre_topc(sK0,sK1) != k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | spl3_5
    | ~ spl3_31 ),
    inference(backward_demodulation,[],[f60,f201])).

fof(f201,plain,
    ( k1_pre_topc(sK0,sK1) = g1_pre_topc(u1_struct_0(k1_pre_topc(sK0,sK1)),u1_pre_topc(k1_pre_topc(sK0,sK1)))
    | ~ spl3_31 ),
    inference(avatar_component_clause,[],[f200])).

fof(f60,plain,
    ( g1_pre_topc(u1_struct_0(k1_pre_topc(sK0,sK1)),u1_pre_topc(k1_pre_topc(sK0,sK1))) != k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f59])).

fof(f210,plain,
    ( ~ spl3_1
    | ~ spl3_3
    | ~ spl3_12
    | ~ spl3_30 ),
    inference(avatar_contradiction_clause,[],[f209])).

fof(f209,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_12
    | ~ spl3_30 ),
    inference(subsumption_resolution,[],[f208,f52])).

fof(f208,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_1
    | ~ spl3_12
    | ~ spl3_30 ),
    inference(subsumption_resolution,[],[f207,f44])).

fof(f207,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_12
    | ~ spl3_30 ),
    inference(duplicate_literal_removal,[],[f203])).

fof(f203,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_12
    | ~ spl3_30 ),
    inference(resolution,[],[f198,f88])).

fof(f198,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(k1_pre_topc(sK0,sK1),X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f197])).

fof(f197,plain,
    ( spl3_30
  <=> ! [X0] :
        ( ~ m1_pre_topc(k1_pre_topc(sK0,sK1),X0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f202,plain,
    ( spl3_30
    | spl3_31
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_28 ),
    inference(avatar_split_clause,[],[f181,f176,f51,f43,f200,f197])).

fof(f176,plain,
    ( spl3_28
  <=> ! [X1,X0,X2] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | k1_pre_topc(X0,X1) = g1_pre_topc(u1_struct_0(k1_pre_topc(X0,X1)),u1_pre_topc(k1_pre_topc(X0,X1)))
        | ~ m1_pre_topc(k1_pre_topc(X0,X1),X2)
        | ~ l1_pre_topc(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f181,plain,
    ( ! [X0] :
        ( k1_pre_topc(sK0,sK1) = g1_pre_topc(u1_struct_0(k1_pre_topc(sK0,sK1)),u1_pre_topc(k1_pre_topc(sK0,sK1)))
        | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_28 ),
    inference(subsumption_resolution,[],[f179,f44])).

fof(f179,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | k1_pre_topc(sK0,sK1) = g1_pre_topc(u1_struct_0(k1_pre_topc(sK0,sK1)),u1_pre_topc(k1_pre_topc(sK0,sK1)))
        | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl3_3
    | ~ spl3_28 ),
    inference(resolution,[],[f177,f52])).

fof(f177,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | k1_pre_topc(X0,X1) = g1_pre_topc(u1_struct_0(k1_pre_topc(X0,X1)),u1_pre_topc(k1_pre_topc(X0,X1)))
        | ~ m1_pre_topc(k1_pre_topc(X0,X1),X2)
        | ~ l1_pre_topc(X2) )
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f176])).

fof(f190,plain,
    ( ~ spl3_1
    | ~ spl3_7
    | spl3_29 ),
    inference(avatar_contradiction_clause,[],[f189])).

fof(f189,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_7
    | spl3_29 ),
    inference(subsumption_resolution,[],[f187,f44])).

fof(f187,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl3_7
    | spl3_29 ),
    inference(resolution,[],[f184,f68])).

fof(f68,plain,
    ( ! [X0] :
        ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ l1_pre_topc(X0) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl3_7
  <=> ! [X0] :
        ( ~ l1_pre_topc(X0)
        | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f184,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl3_29 ),
    inference(avatar_component_clause,[],[f183])).

fof(f183,plain,
    ( spl3_29
  <=> m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f185,plain,
    ( ~ spl3_29
    | ~ spl3_9
    | spl3_26 ),
    inference(avatar_split_clause,[],[f173,f165,f75,f183])).

fof(f75,plain,
    ( spl3_9
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
        | l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f165,plain,
    ( spl3_26
  <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f173,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl3_9
    | spl3_26 ),
    inference(resolution,[],[f171,f76])).

fof(f76,plain,
    ( ! [X0,X1] :
        ( l1_pre_topc(g1_pre_topc(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f75])).

fof(f171,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | spl3_26 ),
    inference(avatar_component_clause,[],[f165])).

fof(f178,plain,
    ( spl3_28
    | ~ spl3_6
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f138,f132,f63,f176])).

fof(f63,plain,
    ( spl3_6
  <=> ! [X1,X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0)
        | l1_pre_topc(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f132,plain,
    ( spl3_21
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ l1_pre_topc(X1)
        | ~ l1_pre_topc(k1_pre_topc(X1,X0))
        | k1_pre_topc(X1,X0) = g1_pre_topc(u1_struct_0(k1_pre_topc(X1,X0)),u1_pre_topc(k1_pre_topc(X1,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f138,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | k1_pre_topc(X0,X1) = g1_pre_topc(u1_struct_0(k1_pre_topc(X0,X1)),u1_pre_topc(k1_pre_topc(X0,X1)))
        | ~ m1_pre_topc(k1_pre_topc(X0,X1),X2)
        | ~ l1_pre_topc(X2) )
    | ~ spl3_6
    | ~ spl3_21 ),
    inference(resolution,[],[f133,f64])).

fof(f64,plain,
    ( ! [X0,X1] :
        ( l1_pre_topc(X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f63])).

fof(f133,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(k1_pre_topc(X1,X0))
        | ~ l1_pre_topc(X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
        | k1_pre_topc(X1,X0) = g1_pre_topc(u1_struct_0(k1_pre_topc(X1,X0)),u1_pre_topc(k1_pre_topc(X1,X0))) )
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f132])).

fof(f172,plain,
    ( spl3_27
    | ~ spl3_26
    | ~ spl3_4
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f148,f140,f55,f165,f169])).

fof(f55,plain,
    ( spl3_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f140,plain,
    ( spl3_22
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
        | ~ l1_pre_topc(X2)
        | ~ m1_pre_topc(k1_pre_topc(X0,X1),X2)
        | k1_pre_topc(X0,X1) = k1_pre_topc(X2,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

% (25058)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
fof(f148,plain,
    ( ! [X1] :
        ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ m1_pre_topc(k1_pre_topc(X1,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) = k1_pre_topc(X1,sK1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ l1_pre_topc(X1) )
    | ~ spl3_4
    | ~ spl3_22 ),
    inference(resolution,[],[f141,f56])).

fof(f56,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f55])).

fof(f141,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
        | ~ l1_pre_topc(X2)
        | ~ m1_pre_topc(k1_pre_topc(X0,X1),X2)
        | k1_pre_topc(X0,X1) = k1_pre_topc(X2,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f140])).

fof(f142,plain,
    ( spl3_22
    | ~ spl3_11
    | ~ spl3_16
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f125,f121,f107,f83,f140])).

fof(f83,plain,
    ( spl3_11
  <=> ! [X1,X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | v1_pre_topc(k1_pre_topc(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f107,plain,
    ( spl3_16
  <=> ! [X0,X2] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v1_pre_topc(X2)
        | ~ m1_pre_topc(X2,X0)
        | k1_pre_topc(X0,k2_struct_0(X2)) = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f121,plain,
    ( spl3_19
  <=> ! [X1,X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | k2_struct_0(k1_pre_topc(X0,X1)) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f125,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
        | ~ l1_pre_topc(X2)
        | ~ m1_pre_topc(k1_pre_topc(X0,X1),X2)
        | k1_pre_topc(X0,X1) = k1_pre_topc(X2,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl3_11
    | ~ spl3_16
    | ~ spl3_19 ),
    inference(subsumption_resolution,[],[f124,f84])).

fof(f84,plain,
    ( ! [X0,X1] :
        ( v1_pre_topc(k1_pre_topc(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f83])).

fof(f124,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
        | ~ l1_pre_topc(X2)
        | ~ v1_pre_topc(k1_pre_topc(X0,X1))
        | ~ m1_pre_topc(k1_pre_topc(X0,X1),X2)
        | k1_pre_topc(X0,X1) = k1_pre_topc(X2,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl3_16
    | ~ spl3_19 ),
    inference(superposition,[],[f108,f122])).

fof(f122,plain,
    ( ! [X0,X1] :
        ( k2_struct_0(k1_pre_topc(X0,X1)) = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f121])).

fof(f108,plain,
    ( ! [X2,X0] :
        ( ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | ~ v1_pre_topc(X2)
        | ~ m1_pre_topc(X2,X0)
        | k1_pre_topc(X0,k2_struct_0(X2)) = X2 )
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f107])).

fof(f134,plain,
    ( spl3_21
    | ~ spl3_10
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f92,f83,f79,f132])).

fof(f79,plain,
    ( spl3_10
  <=> ! [X0] :
        ( ~ l1_pre_topc(X0)
        | ~ v1_pre_topc(X0)
        | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f92,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ l1_pre_topc(X1)
        | ~ l1_pre_topc(k1_pre_topc(X1,X0))
        | k1_pre_topc(X1,X0) = g1_pre_topc(u1_struct_0(k1_pre_topc(X1,X0)),u1_pre_topc(k1_pre_topc(X1,X0))) )
    | ~ spl3_10
    | ~ spl3_11 ),
    inference(resolution,[],[f84,f80])).

fof(f80,plain,
    ( ! [X0] :
        ( ~ v1_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f79])).

fof(f123,plain,
    ( spl3_19
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f119,f115,f87,f83,f121])).

fof(f115,plain,
    ( spl3_18
  <=> ! [X1,X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v1_pre_topc(k1_pre_topc(X0,X1))
        | ~ m1_pre_topc(k1_pre_topc(X0,X1),X0)
        | k2_struct_0(k1_pre_topc(X0,X1)) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f119,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | k2_struct_0(k1_pre_topc(X0,X1)) = X1 )
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_18 ),
    inference(subsumption_resolution,[],[f118,f88])).

fof(f118,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_pre_topc(k1_pre_topc(X0,X1),X0)
        | k2_struct_0(k1_pre_topc(X0,X1)) = X1 )
    | ~ spl3_11
    | ~ spl3_18 ),
    inference(subsumption_resolution,[],[f116,f84])).

fof(f116,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v1_pre_topc(k1_pre_topc(X0,X1))
        | ~ m1_pre_topc(k1_pre_topc(X0,X1),X0)
        | k2_struct_0(k1_pre_topc(X0,X1)) = X1 )
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f115])).

fof(f117,plain,(
    spl3_18 ),
    inference(avatar_split_clause,[],[f38,f115])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_pre_topc(k1_pre_topc(X0,X1))
      | ~ m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | k2_struct_0(k1_pre_topc(X0,X1)) = X1 ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_pre_topc(X2)
      | ~ m1_pre_topc(X2,X0)
      | k2_struct_0(X2) = X1
      | k1_pre_topc(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_pre_topc(X2) )
             => ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_pre_topc)).

fof(f109,plain,(
    spl3_16 ),
    inference(avatar_split_clause,[],[f39,f107])).

fof(f39,plain,(
    ! [X2,X0] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_pre_topc(X2)
      | ~ m1_pre_topc(X2,X0)
      | k1_pre_topc(X0,k2_struct_0(X2)) = X2 ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_pre_topc(X2)
      | ~ m1_pre_topc(X2,X0)
      | k2_struct_0(X2) != X1
      | k1_pre_topc(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f105,plain,
    ( spl3_15
    | ~ spl3_6
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f101,f98,f63,f103])).

fof(f98,plain,
    ( spl3_14
  <=> ! [X1,X0] :
        ( ~ l1_pre_topc(X0)
        | ~ l1_pre_topc(X1)
        | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | ~ m1_pre_topc(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f101,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X1)
        | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | ~ m1_pre_topc(X0,X1) )
    | ~ spl3_6
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f99,f64])).

fof(f99,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ l1_pre_topc(X1)
        | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | ~ m1_pre_topc(X0,X1) )
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f98])).

fof(f100,plain,(
    spl3_14 ),
    inference(avatar_split_clause,[],[f30,f98])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1)
      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

fof(f89,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f37,f87])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_pre_topc(k1_pre_topc(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_pre_topc)).

fof(f85,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f36,f83])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_pre_topc(k1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f81,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f28,f79])).

fof(f28,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ v1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
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

fof(f77,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f35,f75])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).

fof(f69,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f27,f67])).

fof(f27,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f65,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f31,f63])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f61,plain,(
    ~ spl3_5 ),
    inference(avatar_split_clause,[],[f40,f59])).

fof(f40,plain,(
    g1_pre_topc(u1_struct_0(k1_pre_topc(sK0,sK1)),u1_pre_topc(k1_pre_topc(sK0,sK1))) != k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) ),
    inference(backward_demodulation,[],[f24,f23])).

fof(f23,plain,(
    sK1 = sK2 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( g1_pre_topc(u1_struct_0(k1_pre_topc(X0,X1)),u1_pre_topc(k1_pre_topc(X0,X1))) != k1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X2)
              & X1 = X2
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( g1_pre_topc(u1_struct_0(k1_pre_topc(X0,X1)),u1_pre_topc(k1_pre_topc(X0,X1))) != k1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X2)
              & X1 = X2
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
               => ( X1 = X2
                 => g1_pre_topc(u1_struct_0(k1_pre_topc(X0,X1)),u1_pre_topc(k1_pre_topc(X0,X1))) = k1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
             => ( X1 = X2
               => g1_pre_topc(u1_struct_0(k1_pre_topc(X0,X1)),u1_pre_topc(k1_pre_topc(X0,X1))) = k1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_pre_topc)).

fof(f24,plain,(
    g1_pre_topc(u1_struct_0(k1_pre_topc(sK0,sK1)),u1_pre_topc(k1_pre_topc(sK0,sK1))) != k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f57,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f41,f55])).

fof(f41,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) ),
    inference(forward_demodulation,[],[f22,f23])).

fof(f22,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) ),
    inference(cnf_transformation,[],[f11])).

fof(f53,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f25,f51])).

fof(f25,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f11])).

fof(f45,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f26,f43])).

fof(f26,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:02:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.43  % (25051)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.45  % (25044)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.45  % (25051)Refutation found. Thanks to Tanya!
% 0.21/0.45  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f252,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(avatar_sat_refutation,[],[f45,f53,f57,f61,f65,f69,f77,f81,f85,f89,f100,f105,f109,f117,f123,f134,f142,f172,f178,f185,f190,f202,f210,f215,f223,f236,f251])).
% 0.21/0.46  fof(f251,plain,(
% 0.21/0.46    ~spl3_1 | ~spl3_3 | ~spl3_12 | spl3_35),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f250])).
% 0.21/0.46  fof(f250,plain,(
% 0.21/0.46    $false | (~spl3_1 | ~spl3_3 | ~spl3_12 | spl3_35)),
% 0.21/0.46    inference(subsumption_resolution,[],[f249,f44])).
% 0.21/0.46  fof(f44,plain,(
% 0.21/0.46    l1_pre_topc(sK0) | ~spl3_1),
% 0.21/0.46    inference(avatar_component_clause,[],[f43])).
% 0.21/0.46  fof(f43,plain,(
% 0.21/0.46    spl3_1 <=> l1_pre_topc(sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.46  fof(f249,plain,(
% 0.21/0.46    ~l1_pre_topc(sK0) | (~spl3_3 | ~spl3_12 | spl3_35)),
% 0.21/0.46    inference(subsumption_resolution,[],[f246,f52])).
% 0.21/0.46  fof(f52,plain,(
% 0.21/0.46    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_3),
% 0.21/0.46    inference(avatar_component_clause,[],[f51])).
% 0.21/0.46  fof(f51,plain,(
% 0.21/0.46    spl3_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.46  fof(f246,plain,(
% 0.21/0.46    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl3_12 | spl3_35)),
% 0.21/0.46    inference(resolution,[],[f235,f88])).
% 0.21/0.46  fof(f88,plain,(
% 0.21/0.46    ( ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl3_12),
% 0.21/0.46    inference(avatar_component_clause,[],[f87])).
% 0.21/0.46  fof(f87,plain,(
% 0.21/0.46    spl3_12 <=> ! [X1,X0] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_pre_topc(k1_pre_topc(X0,X1),X0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.46  fof(f235,plain,(
% 0.21/0.46    ~m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) | spl3_35),
% 0.21/0.46    inference(avatar_component_clause,[],[f234])).
% 0.21/0.46  fof(f234,plain,(
% 0.21/0.46    spl3_35 <=> m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).
% 0.21/0.46  fof(f236,plain,(
% 0.21/0.46    ~spl3_35 | ~spl3_1 | ~spl3_15 | spl3_33),
% 0.21/0.46    inference(avatar_split_clause,[],[f226,f221,f103,f43,f234])).
% 0.21/0.46  fof(f103,plain,(
% 0.21/0.46    spl3_15 <=> ! [X1,X0] : (~l1_pre_topc(X1) | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.21/0.46  fof(f221,plain,(
% 0.21/0.46    spl3_33 <=> m1_pre_topc(k1_pre_topc(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 0.21/0.46  fof(f226,plain,(
% 0.21/0.46    ~m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) | (~spl3_1 | ~spl3_15 | spl3_33)),
% 0.21/0.46    inference(subsumption_resolution,[],[f224,f44])).
% 0.21/0.46  fof(f224,plain,(
% 0.21/0.46    ~l1_pre_topc(sK0) | ~m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) | (~spl3_15 | spl3_33)),
% 0.21/0.46    inference(resolution,[],[f222,f104])).
% 0.21/0.46  fof(f104,plain,(
% 0.21/0.46    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~l1_pre_topc(X1) | ~m1_pre_topc(X0,X1)) ) | ~spl3_15),
% 0.21/0.46    inference(avatar_component_clause,[],[f103])).
% 0.21/0.46  fof(f222,plain,(
% 0.21/0.46    ~m1_pre_topc(k1_pre_topc(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | spl3_33),
% 0.21/0.46    inference(avatar_component_clause,[],[f221])).
% 0.21/0.46  fof(f223,plain,(
% 0.21/0.46    spl3_32 | ~spl3_33 | ~spl3_1 | ~spl3_3 | ~spl3_27),
% 0.21/0.46    inference(avatar_split_clause,[],[f195,f169,f51,f43,f221,f213])).
% 0.21/0.46  fof(f213,plain,(
% 0.21/0.46    spl3_32 <=> k1_pre_topc(sK0,sK1) = k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 0.21/0.46  fof(f169,plain,(
% 0.21/0.46    spl3_27 <=> ! [X1] : (~m1_pre_topc(k1_pre_topc(X1,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(X1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X1))) | k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) = k1_pre_topc(X1,sK1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 0.21/0.46  fof(f195,plain,(
% 0.21/0.46    ~m1_pre_topc(k1_pre_topc(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | k1_pre_topc(sK0,sK1) = k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl3_1 | ~spl3_3 | ~spl3_27)),
% 0.21/0.46    inference(subsumption_resolution,[],[f193,f44])).
% 0.21/0.46  fof(f193,plain,(
% 0.21/0.46    ~l1_pre_topc(sK0) | ~m1_pre_topc(k1_pre_topc(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | k1_pre_topc(sK0,sK1) = k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl3_3 | ~spl3_27)),
% 0.21/0.46    inference(resolution,[],[f170,f52])).
% 0.21/0.46  fof(f170,plain,(
% 0.21/0.46    ( ! [X1] : (~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~m1_pre_topc(k1_pre_topc(X1,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) = k1_pre_topc(X1,sK1)) ) | ~spl3_27),
% 0.21/0.46    inference(avatar_component_clause,[],[f169])).
% 0.21/0.46  fof(f215,plain,(
% 0.21/0.46    ~spl3_32 | spl3_5 | ~spl3_31),
% 0.21/0.46    inference(avatar_split_clause,[],[f211,f200,f59,f213])).
% 0.21/0.46  fof(f59,plain,(
% 0.21/0.46    spl3_5 <=> g1_pre_topc(u1_struct_0(k1_pre_topc(sK0,sK1)),u1_pre_topc(k1_pre_topc(sK0,sK1))) = k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.46  fof(f200,plain,(
% 0.21/0.46    spl3_31 <=> k1_pre_topc(sK0,sK1) = g1_pre_topc(u1_struct_0(k1_pre_topc(sK0,sK1)),u1_pre_topc(k1_pre_topc(sK0,sK1)))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 0.21/0.46  fof(f211,plain,(
% 0.21/0.46    k1_pre_topc(sK0,sK1) != k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (spl3_5 | ~spl3_31)),
% 0.21/0.46    inference(backward_demodulation,[],[f60,f201])).
% 0.21/0.46  fof(f201,plain,(
% 0.21/0.46    k1_pre_topc(sK0,sK1) = g1_pre_topc(u1_struct_0(k1_pre_topc(sK0,sK1)),u1_pre_topc(k1_pre_topc(sK0,sK1))) | ~spl3_31),
% 0.21/0.46    inference(avatar_component_clause,[],[f200])).
% 0.21/0.46  fof(f60,plain,(
% 0.21/0.46    g1_pre_topc(u1_struct_0(k1_pre_topc(sK0,sK1)),u1_pre_topc(k1_pre_topc(sK0,sK1))) != k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | spl3_5),
% 0.21/0.46    inference(avatar_component_clause,[],[f59])).
% 0.21/0.46  fof(f210,plain,(
% 0.21/0.46    ~spl3_1 | ~spl3_3 | ~spl3_12 | ~spl3_30),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f209])).
% 0.21/0.46  fof(f209,plain,(
% 0.21/0.46    $false | (~spl3_1 | ~spl3_3 | ~spl3_12 | ~spl3_30)),
% 0.21/0.46    inference(subsumption_resolution,[],[f208,f52])).
% 0.21/0.46  fof(f208,plain,(
% 0.21/0.46    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_1 | ~spl3_12 | ~spl3_30)),
% 0.21/0.46    inference(subsumption_resolution,[],[f207,f44])).
% 0.21/0.46  fof(f207,plain,(
% 0.21/0.46    ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_12 | ~spl3_30)),
% 0.21/0.46    inference(duplicate_literal_removal,[],[f203])).
% 0.21/0.46  fof(f203,plain,(
% 0.21/0.46    ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl3_12 | ~spl3_30)),
% 0.21/0.46    inference(resolution,[],[f198,f88])).
% 0.21/0.46  fof(f198,plain,(
% 0.21/0.46    ( ! [X0] : (~m1_pre_topc(k1_pre_topc(sK0,sK1),X0) | ~l1_pre_topc(X0)) ) | ~spl3_30),
% 0.21/0.46    inference(avatar_component_clause,[],[f197])).
% 0.21/0.46  fof(f197,plain,(
% 0.21/0.46    spl3_30 <=> ! [X0] : (~m1_pre_topc(k1_pre_topc(sK0,sK1),X0) | ~l1_pre_topc(X0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.21/0.46  fof(f202,plain,(
% 0.21/0.46    spl3_30 | spl3_31 | ~spl3_1 | ~spl3_3 | ~spl3_28),
% 0.21/0.46    inference(avatar_split_clause,[],[f181,f176,f51,f43,f200,f197])).
% 0.21/0.46  fof(f176,plain,(
% 0.21/0.46    spl3_28 <=> ! [X1,X0,X2] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_pre_topc(X0,X1) = g1_pre_topc(u1_struct_0(k1_pre_topc(X0,X1)),u1_pre_topc(k1_pre_topc(X0,X1))) | ~m1_pre_topc(k1_pre_topc(X0,X1),X2) | ~l1_pre_topc(X2))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.21/0.46  fof(f181,plain,(
% 0.21/0.46    ( ! [X0] : (k1_pre_topc(sK0,sK1) = g1_pre_topc(u1_struct_0(k1_pre_topc(sK0,sK1)),u1_pre_topc(k1_pre_topc(sK0,sK1))) | ~m1_pre_topc(k1_pre_topc(sK0,sK1),X0) | ~l1_pre_topc(X0)) ) | (~spl3_1 | ~spl3_3 | ~spl3_28)),
% 0.21/0.46    inference(subsumption_resolution,[],[f179,f44])).
% 0.21/0.46  fof(f179,plain,(
% 0.21/0.46    ( ! [X0] : (~l1_pre_topc(sK0) | k1_pre_topc(sK0,sK1) = g1_pre_topc(u1_struct_0(k1_pre_topc(sK0,sK1)),u1_pre_topc(k1_pre_topc(sK0,sK1))) | ~m1_pre_topc(k1_pre_topc(sK0,sK1),X0) | ~l1_pre_topc(X0)) ) | (~spl3_3 | ~spl3_28)),
% 0.21/0.46    inference(resolution,[],[f177,f52])).
% 0.21/0.46  fof(f177,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k1_pre_topc(X0,X1) = g1_pre_topc(u1_struct_0(k1_pre_topc(X0,X1)),u1_pre_topc(k1_pre_topc(X0,X1))) | ~m1_pre_topc(k1_pre_topc(X0,X1),X2) | ~l1_pre_topc(X2)) ) | ~spl3_28),
% 0.21/0.46    inference(avatar_component_clause,[],[f176])).
% 0.21/0.46  fof(f190,plain,(
% 0.21/0.46    ~spl3_1 | ~spl3_7 | spl3_29),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f189])).
% 0.21/0.46  fof(f189,plain,(
% 0.21/0.46    $false | (~spl3_1 | ~spl3_7 | spl3_29)),
% 0.21/0.46    inference(subsumption_resolution,[],[f187,f44])).
% 0.21/0.46  fof(f187,plain,(
% 0.21/0.46    ~l1_pre_topc(sK0) | (~spl3_7 | spl3_29)),
% 0.21/0.46    inference(resolution,[],[f184,f68])).
% 0.21/0.46  fof(f68,plain,(
% 0.21/0.46    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) ) | ~spl3_7),
% 0.21/0.46    inference(avatar_component_clause,[],[f67])).
% 0.21/0.46  fof(f67,plain,(
% 0.21/0.46    spl3_7 <=> ! [X0] : (~l1_pre_topc(X0) | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.46  fof(f184,plain,(
% 0.21/0.46    ~m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | spl3_29),
% 0.21/0.46    inference(avatar_component_clause,[],[f183])).
% 0.21/0.46  fof(f183,plain,(
% 0.21/0.46    spl3_29 <=> m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.21/0.46  fof(f185,plain,(
% 0.21/0.46    ~spl3_29 | ~spl3_9 | spl3_26),
% 0.21/0.46    inference(avatar_split_clause,[],[f173,f165,f75,f183])).
% 0.21/0.46  fof(f75,plain,(
% 0.21/0.46    spl3_9 <=> ! [X1,X0] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | l1_pre_topc(g1_pre_topc(X0,X1)))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.46  fof(f165,plain,(
% 0.21/0.46    spl3_26 <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.21/0.46  fof(f173,plain,(
% 0.21/0.46    ~m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | (~spl3_9 | spl3_26)),
% 0.21/0.46    inference(resolution,[],[f171,f76])).
% 0.21/0.46  fof(f76,plain,(
% 0.21/0.46    ( ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) ) | ~spl3_9),
% 0.21/0.46    inference(avatar_component_clause,[],[f75])).
% 0.21/0.46  fof(f171,plain,(
% 0.21/0.46    ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | spl3_26),
% 0.21/0.46    inference(avatar_component_clause,[],[f165])).
% 0.21/0.46  fof(f178,plain,(
% 0.21/0.46    spl3_28 | ~spl3_6 | ~spl3_21),
% 0.21/0.46    inference(avatar_split_clause,[],[f138,f132,f63,f176])).
% 0.21/0.46  fof(f63,plain,(
% 0.21/0.46    spl3_6 <=> ! [X1,X0] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.46  fof(f132,plain,(
% 0.21/0.46    spl3_21 <=> ! [X1,X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~l1_pre_topc(k1_pre_topc(X1,X0)) | k1_pre_topc(X1,X0) = g1_pre_topc(u1_struct_0(k1_pre_topc(X1,X0)),u1_pre_topc(k1_pre_topc(X1,X0))))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.21/0.46  fof(f138,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_pre_topc(X0,X1) = g1_pre_topc(u1_struct_0(k1_pre_topc(X0,X1)),u1_pre_topc(k1_pre_topc(X0,X1))) | ~m1_pre_topc(k1_pre_topc(X0,X1),X2) | ~l1_pre_topc(X2)) ) | (~spl3_6 | ~spl3_21)),
% 0.21/0.46    inference(resolution,[],[f133,f64])).
% 0.21/0.46  fof(f64,plain,(
% 0.21/0.46    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) ) | ~spl3_6),
% 0.21/0.46    inference(avatar_component_clause,[],[f63])).
% 0.21/0.46  fof(f133,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~l1_pre_topc(k1_pre_topc(X1,X0)) | ~l1_pre_topc(X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | k1_pre_topc(X1,X0) = g1_pre_topc(u1_struct_0(k1_pre_topc(X1,X0)),u1_pre_topc(k1_pre_topc(X1,X0)))) ) | ~spl3_21),
% 0.21/0.46    inference(avatar_component_clause,[],[f132])).
% 0.21/0.46  fof(f172,plain,(
% 0.21/0.46    spl3_27 | ~spl3_26 | ~spl3_4 | ~spl3_22),
% 0.21/0.46    inference(avatar_split_clause,[],[f148,f140,f55,f165,f169])).
% 0.21/0.46  fof(f55,plain,(
% 0.21/0.46    spl3_4 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.46  fof(f140,plain,(
% 0.21/0.46    spl3_22 <=> ! [X1,X0,X2] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~m1_pre_topc(k1_pre_topc(X0,X1),X2) | k1_pre_topc(X0,X1) = k1_pre_topc(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.21/0.46  % (25058)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.46  fof(f148,plain,(
% 0.21/0.46    ( ! [X1] : (~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_pre_topc(k1_pre_topc(X1,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) = k1_pre_topc(X1,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1)) ) | (~spl3_4 | ~spl3_22)),
% 0.21/0.46    inference(resolution,[],[f141,f56])).
% 0.21/0.46  fof(f56,plain,(
% 0.21/0.46    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | ~spl3_4),
% 0.21/0.46    inference(avatar_component_clause,[],[f55])).
% 0.21/0.46  fof(f141,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~m1_pre_topc(k1_pre_topc(X0,X1),X2) | k1_pre_topc(X0,X1) = k1_pre_topc(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl3_22),
% 0.21/0.46    inference(avatar_component_clause,[],[f140])).
% 0.21/0.46  fof(f142,plain,(
% 0.21/0.46    spl3_22 | ~spl3_11 | ~spl3_16 | ~spl3_19),
% 0.21/0.46    inference(avatar_split_clause,[],[f125,f121,f107,f83,f140])).
% 0.21/0.46  fof(f83,plain,(
% 0.21/0.46    spl3_11 <=> ! [X1,X0] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_pre_topc(k1_pre_topc(X0,X1)))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.46  fof(f107,plain,(
% 0.21/0.46    spl3_16 <=> ! [X0,X2] : (~l1_pre_topc(X0) | ~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X0))) | ~v1_pre_topc(X2) | ~m1_pre_topc(X2,X0) | k1_pre_topc(X0,k2_struct_0(X2)) = X2)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.46  fof(f121,plain,(
% 0.21/0.46    spl3_19 <=> ! [X1,X0] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_struct_0(k1_pre_topc(X0,X1)) = X1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.21/0.46  fof(f125,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~m1_pre_topc(k1_pre_topc(X0,X1),X2) | k1_pre_topc(X0,X1) = k1_pre_topc(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | (~spl3_11 | ~spl3_16 | ~spl3_19)),
% 0.21/0.46    inference(subsumption_resolution,[],[f124,f84])).
% 0.21/0.46  fof(f84,plain,(
% 0.21/0.46    ( ! [X0,X1] : (v1_pre_topc(k1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl3_11),
% 0.21/0.46    inference(avatar_component_clause,[],[f83])).
% 0.21/0.46  fof(f124,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~v1_pre_topc(k1_pre_topc(X0,X1)) | ~m1_pre_topc(k1_pre_topc(X0,X1),X2) | k1_pre_topc(X0,X1) = k1_pre_topc(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | (~spl3_16 | ~spl3_19)),
% 0.21/0.46    inference(superposition,[],[f108,f122])).
% 0.21/0.46  fof(f122,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k2_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl3_19),
% 0.21/0.46    inference(avatar_component_clause,[],[f121])).
% 0.21/0.46  fof(f108,plain,(
% 0.21/0.46    ( ! [X2,X0] : (~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v1_pre_topc(X2) | ~m1_pre_topc(X2,X0) | k1_pre_topc(X0,k2_struct_0(X2)) = X2) ) | ~spl3_16),
% 0.21/0.46    inference(avatar_component_clause,[],[f107])).
% 0.21/0.46  fof(f134,plain,(
% 0.21/0.46    spl3_21 | ~spl3_10 | ~spl3_11),
% 0.21/0.46    inference(avatar_split_clause,[],[f92,f83,f79,f132])).
% 0.21/0.46  fof(f79,plain,(
% 0.21/0.46    spl3_10 <=> ! [X0] : (~l1_pre_topc(X0) | ~v1_pre_topc(X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.46  fof(f92,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~l1_pre_topc(k1_pre_topc(X1,X0)) | k1_pre_topc(X1,X0) = g1_pre_topc(u1_struct_0(k1_pre_topc(X1,X0)),u1_pre_topc(k1_pre_topc(X1,X0)))) ) | (~spl3_10 | ~spl3_11)),
% 0.21/0.46    inference(resolution,[],[f84,f80])).
% 0.21/0.46  fof(f80,plain,(
% 0.21/0.46    ( ! [X0] : (~v1_pre_topc(X0) | ~l1_pre_topc(X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0) ) | ~spl3_10),
% 0.21/0.46    inference(avatar_component_clause,[],[f79])).
% 0.21/0.46  fof(f123,plain,(
% 0.21/0.46    spl3_19 | ~spl3_11 | ~spl3_12 | ~spl3_18),
% 0.21/0.46    inference(avatar_split_clause,[],[f119,f115,f87,f83,f121])).
% 0.21/0.46  fof(f115,plain,(
% 0.21/0.46    spl3_18 <=> ! [X1,X0] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_pre_topc(k1_pre_topc(X0,X1)) | ~m1_pre_topc(k1_pre_topc(X0,X1),X0) | k2_struct_0(k1_pre_topc(X0,X1)) = X1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.21/0.46  fof(f119,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_struct_0(k1_pre_topc(X0,X1)) = X1) ) | (~spl3_11 | ~spl3_12 | ~spl3_18)),
% 0.21/0.46    inference(subsumption_resolution,[],[f118,f88])).
% 0.21/0.46  fof(f118,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(k1_pre_topc(X0,X1),X0) | k2_struct_0(k1_pre_topc(X0,X1)) = X1) ) | (~spl3_11 | ~spl3_18)),
% 0.21/0.46    inference(subsumption_resolution,[],[f116,f84])).
% 0.21/0.46  fof(f116,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_pre_topc(k1_pre_topc(X0,X1)) | ~m1_pre_topc(k1_pre_topc(X0,X1),X0) | k2_struct_0(k1_pre_topc(X0,X1)) = X1) ) | ~spl3_18),
% 0.21/0.46    inference(avatar_component_clause,[],[f115])).
% 0.21/0.46  fof(f117,plain,(
% 0.21/0.46    spl3_18),
% 0.21/0.46    inference(avatar_split_clause,[],[f38,f115])).
% 0.21/0.46  fof(f38,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_pre_topc(k1_pre_topc(X0,X1)) | ~m1_pre_topc(k1_pre_topc(X0,X1),X0) | k2_struct_0(k1_pre_topc(X0,X1)) = X1) )),
% 0.21/0.46    inference(equality_resolution,[],[f33])).
% 0.21/0.46  fof(f33,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_pre_topc(X2) | ~m1_pre_topc(X2,X0) | k2_struct_0(X2) = X1 | k1_pre_topc(X0,X1) != X2) )),
% 0.21/0.46    inference(cnf_transformation,[],[f18])).
% 0.21/0.46  fof(f18,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (! [X2] : ((k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.46    inference(flattening,[],[f17])).
% 0.21/0.46  fof(f17,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (! [X2] : ((k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1) | (~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_pre_topc(X2)) => (k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1))))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_pre_topc)).
% 0.21/0.46  fof(f109,plain,(
% 0.21/0.46    spl3_16),
% 0.21/0.46    inference(avatar_split_clause,[],[f39,f107])).
% 0.21/0.46  fof(f39,plain,(
% 0.21/0.46    ( ! [X2,X0] : (~l1_pre_topc(X0) | ~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X0))) | ~v1_pre_topc(X2) | ~m1_pre_topc(X2,X0) | k1_pre_topc(X0,k2_struct_0(X2)) = X2) )),
% 0.21/0.46    inference(equality_resolution,[],[f32])).
% 0.21/0.46  fof(f32,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_pre_topc(X2) | ~m1_pre_topc(X2,X0) | k2_struct_0(X2) != X1 | k1_pre_topc(X0,X1) = X2) )),
% 0.21/0.46    inference(cnf_transformation,[],[f18])).
% 0.21/0.46  fof(f105,plain,(
% 0.21/0.46    spl3_15 | ~spl3_6 | ~spl3_14),
% 0.21/0.46    inference(avatar_split_clause,[],[f101,f98,f63,f103])).
% 0.21/0.46  fof(f98,plain,(
% 0.21/0.46    spl3_14 <=> ! [X1,X0] : (~l1_pre_topc(X0) | ~l1_pre_topc(X1) | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.46  fof(f101,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~l1_pre_topc(X1) | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1)) ) | (~spl3_6 | ~spl3_14)),
% 0.21/0.46    inference(subsumption_resolution,[],[f99,f64])).
% 0.21/0.46  fof(f99,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~l1_pre_topc(X1) | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1)) ) | ~spl3_14),
% 0.21/0.46    inference(avatar_component_clause,[],[f98])).
% 0.21/0.46  fof(f100,plain,(
% 0.21/0.46    spl3_14),
% 0.21/0.46    inference(avatar_split_clause,[],[f30,f98])).
% 0.21/0.46  fof(f30,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~l1_pre_topc(X1) | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f15])).
% 0.21/0.46  fof(f15,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f7])).
% 0.21/0.46  fof(f7,axiom,(
% 0.21/0.46    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).
% 0.21/0.46  fof(f89,plain,(
% 0.21/0.46    spl3_12),
% 0.21/0.46    inference(avatar_split_clause,[],[f37,f87])).
% 0.21/0.46  fof(f37,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_pre_topc(k1_pre_topc(X0,X1),X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f21])).
% 0.21/0.46  fof(f21,plain,(
% 0.21/0.46    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.46    inference(flattening,[],[f20])).
% 0.21/0.46  fof(f20,plain,(
% 0.21/0.46    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f4])).
% 0.21/0.46  fof(f4,axiom,(
% 0.21/0.46    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => (m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_pre_topc)).
% 0.21/0.46  fof(f85,plain,(
% 0.21/0.46    spl3_11),
% 0.21/0.46    inference(avatar_split_clause,[],[f36,f83])).
% 0.21/0.46  fof(f36,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_pre_topc(k1_pre_topc(X0,X1))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f21])).
% 0.21/0.46  fof(f81,plain,(
% 0.21/0.46    spl3_10),
% 0.21/0.46    inference(avatar_split_clause,[],[f28,f79])).
% 0.21/0.46  fof(f28,plain,(
% 0.21/0.46    ( ! [X0] : (~l1_pre_topc(X0) | ~v1_pre_topc(X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0) )),
% 0.21/0.46    inference(cnf_transformation,[],[f14])).
% 0.21/0.46  fof(f14,plain,(
% 0.21/0.46    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 0.21/0.46    inference(flattening,[],[f13])).
% 0.21/0.46  fof(f13,plain,(
% 0.21/0.46    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).
% 0.21/0.46  fof(f77,plain,(
% 0.21/0.46    spl3_9),
% 0.21/0.46    inference(avatar_split_clause,[],[f35,f75])).
% 0.21/0.46  fof(f35,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | l1_pre_topc(g1_pre_topc(X0,X1))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f19])).
% 0.21/0.46  fof(f19,plain,(
% 0.21/0.46    ! [X0,X1] : ((l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.46    inference(ennf_transformation,[],[f3])).
% 0.21/0.46  fof(f3,axiom,(
% 0.21/0.46    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).
% 0.21/0.46  fof(f69,plain,(
% 0.21/0.46    spl3_7),
% 0.21/0.46    inference(avatar_split_clause,[],[f27,f67])).
% 0.21/0.46  fof(f27,plain,(
% 0.21/0.46    ( ! [X0] : (~l1_pre_topc(X0) | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f12])).
% 0.21/0.46  fof(f12,plain,(
% 0.21/0.46    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f6])).
% 0.21/0.46  fof(f6,axiom,(
% 0.21/0.46    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 0.21/0.46  fof(f65,plain,(
% 0.21/0.46    spl3_6),
% 0.21/0.46    inference(avatar_split_clause,[],[f31,f63])).
% 0.21/0.46  fof(f31,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f16])).
% 0.21/0.46  fof(f16,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f5])).
% 0.21/0.46  fof(f5,axiom,(
% 0.21/0.46    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.46  fof(f61,plain,(
% 0.21/0.46    ~spl3_5),
% 0.21/0.46    inference(avatar_split_clause,[],[f40,f59])).
% 0.21/0.46  fof(f40,plain,(
% 0.21/0.46    g1_pre_topc(u1_struct_0(k1_pre_topc(sK0,sK1)),u1_pre_topc(k1_pre_topc(sK0,sK1))) != k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),
% 0.21/0.46    inference(backward_demodulation,[],[f24,f23])).
% 0.21/0.46  fof(f23,plain,(
% 0.21/0.46    sK1 = sK2),
% 0.21/0.46    inference(cnf_transformation,[],[f11])).
% 0.21/0.46  fof(f11,plain,(
% 0.21/0.46    ? [X0] : (? [X1] : (? [X2] : (g1_pre_topc(u1_struct_0(k1_pre_topc(X0,X1)),u1_pre_topc(k1_pre_topc(X0,X1))) != k1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X2) & X1 = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.21/0.46    inference(flattening,[],[f10])).
% 0.21/0.46  fof(f10,plain,(
% 0.21/0.46    ? [X0] : (? [X1] : (? [X2] : ((g1_pre_topc(u1_struct_0(k1_pre_topc(X0,X1)),u1_pre_topc(k1_pre_topc(X0,X1))) != k1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X2) & X1 = X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f9])).
% 0.21/0.46  fof(f9,negated_conjecture,(
% 0.21/0.46    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) => (X1 = X2 => g1_pre_topc(u1_struct_0(k1_pre_topc(X0,X1)),u1_pre_topc(k1_pre_topc(X0,X1))) = k1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X2)))))),
% 0.21/0.46    inference(negated_conjecture,[],[f8])).
% 0.21/0.46  fof(f8,conjecture,(
% 0.21/0.46    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) => (X1 = X2 => g1_pre_topc(u1_struct_0(k1_pre_topc(X0,X1)),u1_pre_topc(k1_pre_topc(X0,X1))) = k1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X2)))))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_pre_topc)).
% 0.21/0.46  fof(f24,plain,(
% 0.21/0.46    g1_pre_topc(u1_struct_0(k1_pre_topc(sK0,sK1)),u1_pre_topc(k1_pre_topc(sK0,sK1))) != k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK2)),
% 0.21/0.46    inference(cnf_transformation,[],[f11])).
% 0.21/0.46  fof(f57,plain,(
% 0.21/0.46    spl3_4),
% 0.21/0.46    inference(avatar_split_clause,[],[f41,f55])).
% 0.21/0.46  fof(f41,plain,(
% 0.21/0.46    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))),
% 0.21/0.46    inference(forward_demodulation,[],[f22,f23])).
% 0.21/0.46  fof(f22,plain,(
% 0.21/0.46    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))),
% 0.21/0.46    inference(cnf_transformation,[],[f11])).
% 0.21/0.46  fof(f53,plain,(
% 0.21/0.46    spl3_3),
% 0.21/0.46    inference(avatar_split_clause,[],[f25,f51])).
% 0.21/0.46  fof(f25,plain,(
% 0.21/0.46    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.46    inference(cnf_transformation,[],[f11])).
% 0.21/0.46  fof(f45,plain,(
% 0.21/0.46    spl3_1),
% 0.21/0.46    inference(avatar_split_clause,[],[f26,f43])).
% 0.21/0.46  fof(f26,plain,(
% 0.21/0.46    l1_pre_topc(sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f11])).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (25051)------------------------------
% 0.21/0.46  % (25051)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (25051)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (25051)Memory used [KB]: 10746
% 0.21/0.46  % (25051)Time elapsed: 0.061 s
% 0.21/0.46  % (25051)------------------------------
% 0.21/0.46  % (25051)------------------------------
% 0.21/0.46  % (25041)Success in time 0.109 s
%------------------------------------------------------------------------------
