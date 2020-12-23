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
% DateTime   : Thu Dec  3 12:57:24 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 208 expanded)
%              Number of leaves         :   38 (  98 expanded)
%              Depth                    :    7
%              Number of atoms          :  412 ( 627 expanded)
%              Number of equality atoms :   29 (  42 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f309,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f70,f81,f85,f89,f94,f98,f106,f110,f118,f126,f130,f145,f149,f157,f161,f178,f182,f191,f198,f231,f234,f239,f245,f259,f278,f300,f308])).

fof(f308,plain,
    ( ~ spl9_4
    | ~ spl9_18
    | spl9_46 ),
    inference(avatar_contradiction_clause,[],[f305])).

fof(f305,plain,
    ( $false
    | ~ spl9_4
    | ~ spl9_18
    | spl9_46 ),
    inference(unit_resulting_resolution,[],[f69,f299,f125])).

fof(f125,plain,
    ( ! [X2,X0,X1] :
        ( v5_relat_1(X2,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl9_18 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl9_18
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v5_relat_1(X2,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).

fof(f299,plain,
    ( ~ v5_relat_1(sK2,sK1)
    | spl9_46 ),
    inference(avatar_component_clause,[],[f298])).

fof(f298,plain,
    ( spl9_46
  <=> v5_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_46])])).

fof(f69,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl9_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f300,plain,
    ( ~ spl9_46
    | ~ spl9_36
    | ~ spl9_16
    | spl9_43 ),
    inference(avatar_split_clause,[],[f283,f276,f116,f229,f298])).

fof(f229,plain,
    ( spl9_36
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_36])])).

fof(f116,plain,
    ( spl9_16
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X1)
        | r1_tarski(k2_relat_1(X1),X0)
        | ~ v5_relat_1(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f276,plain,
    ( spl9_43
  <=> r1_tarski(k2_relat_1(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_43])])).

fof(f283,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v5_relat_1(sK2,sK1)
    | ~ spl9_16
    | spl9_43 ),
    inference(resolution,[],[f277,f117])).

fof(f117,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k2_relat_1(X1),X0)
        | ~ v1_relat_1(X1)
        | ~ v5_relat_1(X1,X0) )
    | ~ spl9_16 ),
    inference(avatar_component_clause,[],[f116])).

fof(f277,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK1)
    | spl9_43 ),
    inference(avatar_component_clause,[],[f276])).

fof(f278,plain,
    ( ~ spl9_43
    | ~ spl9_36
    | ~ spl9_29
    | ~ spl9_37
    | spl9_41 ),
    inference(avatar_split_clause,[],[f268,f257,f237,f180,f229,f276])).

fof(f180,plain,
    ( spl9_29
  <=> r2_hidden(sK3,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_29])])).

fof(f237,plain,
    ( spl9_37
  <=> ! [X1,X0] :
        ( k1_relat_1(X0) = k10_relat_1(X0,X1)
        | ~ v1_relat_1(X0)
        | ~ r1_tarski(k2_relat_1(X0),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_37])])).

fof(f257,plain,
    ( spl9_41
  <=> r2_hidden(sK3,k10_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_41])])).

fof(f268,plain,
    ( ~ v1_relat_1(sK2)
    | ~ r1_tarski(k2_relat_1(sK2),sK1)
    | ~ spl9_29
    | ~ spl9_37
    | spl9_41 ),
    inference(subsumption_resolution,[],[f267,f197])).

fof(f197,plain,
    ( r2_hidden(sK3,k1_relat_1(sK2))
    | ~ spl9_29 ),
    inference(avatar_component_clause,[],[f180])).

fof(f267,plain,
    ( ~ r2_hidden(sK3,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ r1_tarski(k2_relat_1(sK2),sK1)
    | ~ spl9_37
    | spl9_41 ),
    inference(superposition,[],[f258,f238])).

fof(f238,plain,
    ( ! [X0,X1] :
        ( k1_relat_1(X0) = k10_relat_1(X0,X1)
        | ~ v1_relat_1(X0)
        | ~ r1_tarski(k2_relat_1(X0),X1) )
    | ~ spl9_37 ),
    inference(avatar_component_clause,[],[f237])).

fof(f258,plain,
    ( ~ r2_hidden(sK3,k10_relat_1(sK2,sK1))
    | spl9_41 ),
    inference(avatar_component_clause,[],[f257])).

fof(f259,plain,
    ( ~ spl9_36
    | ~ spl9_41
    | ~ spl9_25
    | ~ spl9_38 ),
    inference(avatar_split_clause,[],[f251,f243,f155,f257,f229])).

fof(f155,plain,
    ( spl9_25
  <=> ! [X1,X0,X2] :
        ( ~ v1_relat_1(X2)
        | r2_hidden(sK8(X0,X1,X2),X1)
        | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_25])])).

fof(f243,plain,
    ( spl9_38
  <=> ! [X0] :
        ( ~ r2_hidden(sK3,k10_relat_1(sK2,X0))
        | ~ r2_hidden(sK8(sK3,X0,sK2),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_38])])).

fof(f251,plain,
    ( ~ r2_hidden(sK3,k10_relat_1(sK2,sK1))
    | ~ v1_relat_1(sK2)
    | ~ spl9_25
    | ~ spl9_38 ),
    inference(duplicate_literal_removal,[],[f250])).

fof(f250,plain,
    ( ~ r2_hidden(sK3,k10_relat_1(sK2,sK1))
    | ~ v1_relat_1(sK2)
    | ~ r2_hidden(sK3,k10_relat_1(sK2,sK1))
    | ~ spl9_25
    | ~ spl9_38 ),
    inference(resolution,[],[f244,f156])).

fof(f156,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(sK8(X0,X1,X2),X1)
        | ~ v1_relat_1(X2)
        | ~ r2_hidden(X0,k10_relat_1(X2,X1)) )
    | ~ spl9_25 ),
    inference(avatar_component_clause,[],[f155])).

fof(f244,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK8(sK3,X0,sK2),sK1)
        | ~ r2_hidden(sK3,k10_relat_1(sK2,X0)) )
    | ~ spl9_38 ),
    inference(avatar_component_clause,[],[f243])).

fof(f245,plain,
    ( spl9_38
    | ~ spl9_13
    | ~ spl9_35 ),
    inference(avatar_split_clause,[],[f235,f226,f104,f243])).

fof(f104,plain,
    ( spl9_13
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,X1)
        | m1_subset_1(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).

fof(f226,plain,
    ( spl9_35
  <=> ! [X3] :
        ( ~ r2_hidden(sK3,k10_relat_1(sK2,X3))
        | ~ m1_subset_1(sK8(sK3,X3,sK2),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_35])])).

fof(f235,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3,k10_relat_1(sK2,X0))
        | ~ r2_hidden(sK8(sK3,X0,sK2),sK1) )
    | ~ spl9_13
    | ~ spl9_35 ),
    inference(resolution,[],[f227,f105])).

fof(f105,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(X0,X1)
        | ~ r2_hidden(X0,X1) )
    | ~ spl9_13 ),
    inference(avatar_component_clause,[],[f104])).

fof(f227,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(sK8(sK3,X3,sK2),sK1)
        | ~ r2_hidden(sK3,k10_relat_1(sK2,X3)) )
    | ~ spl9_35 ),
    inference(avatar_component_clause,[],[f226])).

fof(f239,plain,
    ( spl9_37
    | ~ spl9_7
    | ~ spl9_11
    | ~ spl9_22
    | ~ spl9_23 ),
    inference(avatar_split_clause,[],[f172,f147,f143,f96,f79,f237])).

fof(f79,plain,
    ( spl9_7
  <=> ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f96,plain,
    ( spl9_11
  <=> ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f143,plain,
    ( spl9_22
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X1)
        | ~ r1_tarski(k2_relat_1(X1),X0)
        | k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_22])])).

fof(f147,plain,
    ( spl9_23
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_23])])).

fof(f172,plain,
    ( ! [X0,X1] :
        ( k1_relat_1(X0) = k10_relat_1(X0,X1)
        | ~ v1_relat_1(X0)
        | ~ r1_tarski(k2_relat_1(X0),X1) )
    | ~ spl9_7
    | ~ spl9_11
    | ~ spl9_22
    | ~ spl9_23 ),
    inference(forward_demodulation,[],[f171,f97])).

fof(f97,plain,
    ( ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0
    | ~ spl9_11 ),
    inference(avatar_component_clause,[],[f96])).

fof(f171,plain,
    ( ! [X0,X1] :
        ( k1_relat_1(X0) = k10_relat_1(X0,k1_relat_1(k6_relat_1(X1)))
        | ~ v1_relat_1(X0)
        | ~ r1_tarski(k2_relat_1(X0),X1) )
    | ~ spl9_7
    | ~ spl9_22
    | ~ spl9_23 ),
    inference(subsumption_resolution,[],[f170,f80])).

fof(f80,plain,
    ( ! [X0] : v1_relat_1(k6_relat_1(X0))
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f79])).

fof(f170,plain,
    ( ! [X0,X1] :
        ( k1_relat_1(X0) = k10_relat_1(X0,k1_relat_1(k6_relat_1(X1)))
        | ~ v1_relat_1(k6_relat_1(X1))
        | ~ v1_relat_1(X0)
        | ~ r1_tarski(k2_relat_1(X0),X1) )
    | ~ spl9_22
    | ~ spl9_23 ),
    inference(duplicate_literal_removal,[],[f168])).

fof(f168,plain,
    ( ! [X0,X1] :
        ( k1_relat_1(X0) = k10_relat_1(X0,k1_relat_1(k6_relat_1(X1)))
        | ~ v1_relat_1(k6_relat_1(X1))
        | ~ v1_relat_1(X0)
        | ~ r1_tarski(k2_relat_1(X0),X1)
        | ~ v1_relat_1(X0) )
    | ~ spl9_22
    | ~ spl9_23 ),
    inference(superposition,[],[f148,f144])).

fof(f144,plain,
    ( ! [X0,X1] :
        ( k5_relat_1(X1,k6_relat_1(X0)) = X1
        | ~ r1_tarski(k2_relat_1(X1),X0)
        | ~ v1_relat_1(X1) )
    | ~ spl9_22 ),
    inference(avatar_component_clause,[],[f143])).

fof(f148,plain,
    ( ! [X0,X1] :
        ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl9_23 ),
    inference(avatar_component_clause,[],[f147])).

fof(f234,plain,
    ( ~ spl9_4
    | ~ spl9_9
    | ~ spl9_14
    | spl9_36 ),
    inference(avatar_contradiction_clause,[],[f232])).

fof(f232,plain,
    ( $false
    | ~ spl9_4
    | ~ spl9_9
    | ~ spl9_14
    | spl9_36 ),
    inference(unit_resulting_resolution,[],[f88,f69,f230,f109])).

fof(f109,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | ~ spl9_14 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl9_14
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).

fof(f230,plain,
    ( ~ v1_relat_1(sK2)
    | spl9_36 ),
    inference(avatar_component_clause,[],[f229])).

fof(f88,plain,
    ( ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))
    | ~ spl9_9 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl9_9
  <=> ! [X1,X0] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f231,plain,
    ( spl9_35
    | ~ spl9_36
    | ~ spl9_10
    | ~ spl9_28 ),
    inference(avatar_split_clause,[],[f202,f176,f92,f229,f226])).

fof(f92,plain,
    ( spl9_10
  <=> ! [X4] :
        ( ~ m1_subset_1(X4,sK1)
        | ~ r2_hidden(k4_tarski(sK3,X4),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f176,plain,
    ( spl9_28
  <=> ! [X1,X0,X2] :
        ( ~ v1_relat_1(X2)
        | r2_hidden(k4_tarski(X0,sK8(X0,X1,X2)),X2)
        | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_28])])).

fof(f202,plain,
    ( ! [X3] :
        ( ~ v1_relat_1(sK2)
        | ~ r2_hidden(sK3,k10_relat_1(sK2,X3))
        | ~ m1_subset_1(sK8(sK3,X3,sK2),sK1) )
    | ~ spl9_10
    | ~ spl9_28 ),
    inference(resolution,[],[f177,f93])).

fof(f93,plain,
    ( ! [X4] :
        ( ~ r2_hidden(k4_tarski(sK3,X4),sK2)
        | ~ m1_subset_1(X4,sK1) )
    | ~ spl9_10 ),
    inference(avatar_component_clause,[],[f92])).

fof(f177,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(k4_tarski(X0,sK8(X0,X1,X2)),X2)
        | ~ v1_relat_1(X2)
        | ~ r2_hidden(X0,k10_relat_1(X2,X1)) )
    | ~ spl9_28 ),
    inference(avatar_component_clause,[],[f176])).

fof(f198,plain,
    ( spl9_29
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_26 ),
    inference(avatar_split_clause,[],[f196,f159,f72,f68,f180])).

fof(f72,plain,
    ( spl9_5
  <=> r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f159,plain,
    ( spl9_26
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_26])])).

fof(f196,plain,
    ( r2_hidden(sK3,k1_relat_1(sK2))
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_26 ),
    inference(subsumption_resolution,[],[f192,f69])).

fof(f192,plain,
    ( r2_hidden(sK3,k1_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl9_5
    | ~ spl9_26 ),
    inference(superposition,[],[f73,f160])).

fof(f160,plain,
    ( ! [X2,X0,X1] :
        ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl9_26 ),
    inference(avatar_component_clause,[],[f159])).

fof(f73,plain,
    ( r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2))
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f72])).

fof(f191,plain,
    ( ~ spl9_8
    | ~ spl9_19
    | spl9_29 ),
    inference(avatar_contradiction_clause,[],[f189])).

% (32378)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
fof(f189,plain,
    ( $false
    | ~ spl9_8
    | ~ spl9_19
    | spl9_29 ),
    inference(unit_resulting_resolution,[],[f84,f181,f129])).

fof(f129,plain,
    ( ! [X2,X0,X3] :
        ( r2_hidden(X2,k1_relat_1(X0))
        | ~ r2_hidden(k4_tarski(X2,X3),X0) )
    | ~ spl9_19 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl9_19
  <=> ! [X3,X0,X2] :
        ( ~ r2_hidden(k4_tarski(X2,X3),X0)
        | r2_hidden(X2,k1_relat_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).

fof(f181,plain,
    ( ~ r2_hidden(sK3,k1_relat_1(sK2))
    | spl9_29 ),
    inference(avatar_component_clause,[],[f180])).

fof(f84,plain,
    ( r2_hidden(k4_tarski(sK3,sK4),sK2)
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl9_8
  <=> r2_hidden(k4_tarski(sK3,sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f182,plain,
    ( ~ spl9_29
    | ~ spl9_4
    | spl9_5
    | ~ spl9_26 ),
    inference(avatar_split_clause,[],[f174,f159,f72,f68,f180])).

fof(f174,plain,
    ( ~ r2_hidden(sK3,k1_relat_1(sK2))
    | ~ spl9_4
    | spl9_5
    | ~ spl9_26 ),
    inference(subsumption_resolution,[],[f173,f69])).

fof(f173,plain,
    ( ~ r2_hidden(sK3,k1_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl9_5
    | ~ spl9_26 ),
    inference(superposition,[],[f90,f160])).

fof(f90,plain,
    ( ~ r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2))
    | spl9_5 ),
    inference(avatar_component_clause,[],[f72])).

fof(f178,plain,(
    spl9_28 ),
    inference(avatar_split_clause,[],[f47,f176])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(X0,sK8(X0,X1,X2)),X2)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

fof(f161,plain,(
    spl9_26 ),
    inference(avatar_split_clause,[],[f50,f159])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f157,plain,(
    spl9_25 ),
    inference(avatar_split_clause,[],[f48,f155])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | r2_hidden(sK8(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f149,plain,(
    spl9_23 ),
    inference(avatar_split_clause,[],[f35,f147])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

fof(f145,plain,(
    spl9_22 ),
    inference(avatar_split_clause,[],[f38,f143])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

fof(f130,plain,(
    spl9_19 ),
    inference(avatar_split_clause,[],[f54,f128])).

fof(f54,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f126,plain,(
    spl9_18 ),
    inference(avatar_split_clause,[],[f52,f124])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f118,plain,(
    spl9_16 ),
    inference(avatar_split_clause,[],[f40,f116])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f110,plain,(
    spl9_14 ),
    inference(avatar_split_clause,[],[f36,f108])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f106,plain,(
    spl9_13 ),
    inference(avatar_split_clause,[],[f41,f104])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f98,plain,(
    spl9_11 ),
    inference(avatar_split_clause,[],[f33,f96])).

fof(f33,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f94,plain,
    ( ~ spl9_5
    | spl9_10 ),
    inference(avatar_split_clause,[],[f25,f92,f72])).

fof(f25,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,sK1)
      | ~ r2_hidden(k4_tarski(sK3,X4),sK2)
      | ~ r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r2_hidden(X3,k1_relset_1(X0,X1,X2))
                  <~> ? [X4] :
                        ( r2_hidden(k4_tarski(X3,X4),X2)
                        & m1_subset_1(X4,X1) ) )
                  & m1_subset_1(X3,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
               => ! [X3] :
                    ( m1_subset_1(X3,X0)
                   => ( r2_hidden(X3,k1_relset_1(X0,X1,X2))
                    <=> ? [X4] :
                          ( r2_hidden(k4_tarski(X3,X4),X2)
                          & m1_subset_1(X4,X1) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
             => ! [X3] :
                  ( m1_subset_1(X3,X0)
                 => ( r2_hidden(X3,k1_relset_1(X0,X1,X2))
                  <=> ? [X4] :
                        ( r2_hidden(k4_tarski(X3,X4),X2)
                        & m1_subset_1(X4,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relset_1)).

fof(f89,plain,(
    spl9_9 ),
    inference(avatar_split_clause,[],[f37,f87])).

fof(f37,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f85,plain,
    ( spl9_5
    | spl9_8 ),
    inference(avatar_split_clause,[],[f27,f83,f72])).

fof(f27,plain,
    ( r2_hidden(k4_tarski(sK3,sK4),sK2)
    | r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f81,plain,(
    spl9_7 ),
    inference(avatar_split_clause,[],[f32,f79])).

fof(f32,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f70,plain,(
    spl9_4 ),
    inference(avatar_split_clause,[],[f29,f68])).

fof(f29,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:10:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.41  % (32379)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.45  % (32373)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.47  % (32373)Refutation not found, incomplete strategy% (32373)------------------------------
% 0.20/0.47  % (32373)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (32373)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (32373)Memory used [KB]: 10618
% 0.20/0.47  % (32373)Time elapsed: 0.063 s
% 0.20/0.47  % (32373)------------------------------
% 0.20/0.47  % (32373)------------------------------
% 0.20/0.47  % (32381)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.47  % (32381)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f309,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(avatar_sat_refutation,[],[f70,f81,f85,f89,f94,f98,f106,f110,f118,f126,f130,f145,f149,f157,f161,f178,f182,f191,f198,f231,f234,f239,f245,f259,f278,f300,f308])).
% 0.20/0.47  fof(f308,plain,(
% 0.20/0.47    ~spl9_4 | ~spl9_18 | spl9_46),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f305])).
% 0.20/0.47  fof(f305,plain,(
% 0.20/0.47    $false | (~spl9_4 | ~spl9_18 | spl9_46)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f69,f299,f125])).
% 0.20/0.47  fof(f125,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl9_18),
% 0.20/0.47    inference(avatar_component_clause,[],[f124])).
% 0.20/0.47  fof(f124,plain,(
% 0.20/0.47    spl9_18 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).
% 0.20/0.47  fof(f299,plain,(
% 0.20/0.47    ~v5_relat_1(sK2,sK1) | spl9_46),
% 0.20/0.47    inference(avatar_component_clause,[],[f298])).
% 0.20/0.47  fof(f298,plain,(
% 0.20/0.47    spl9_46 <=> v5_relat_1(sK2,sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl9_46])])).
% 0.20/0.47  fof(f69,plain,(
% 0.20/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl9_4),
% 0.20/0.47    inference(avatar_component_clause,[],[f68])).
% 0.20/0.47  fof(f68,plain,(
% 0.20/0.47    spl9_4 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 0.20/0.47  fof(f300,plain,(
% 0.20/0.47    ~spl9_46 | ~spl9_36 | ~spl9_16 | spl9_43),
% 0.20/0.47    inference(avatar_split_clause,[],[f283,f276,f116,f229,f298])).
% 0.20/0.47  fof(f229,plain,(
% 0.20/0.47    spl9_36 <=> v1_relat_1(sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl9_36])])).
% 0.20/0.47  fof(f116,plain,(
% 0.20/0.47    spl9_16 <=> ! [X1,X0] : (~v1_relat_1(X1) | r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).
% 0.20/0.47  fof(f276,plain,(
% 0.20/0.47    spl9_43 <=> r1_tarski(k2_relat_1(sK2),sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl9_43])])).
% 0.20/0.47  fof(f283,plain,(
% 0.20/0.47    ~v1_relat_1(sK2) | ~v5_relat_1(sK2,sK1) | (~spl9_16 | spl9_43)),
% 0.20/0.47    inference(resolution,[],[f277,f117])).
% 0.20/0.47  fof(f117,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1) | ~v5_relat_1(X1,X0)) ) | ~spl9_16),
% 0.20/0.47    inference(avatar_component_clause,[],[f116])).
% 0.20/0.47  fof(f277,plain,(
% 0.20/0.47    ~r1_tarski(k2_relat_1(sK2),sK1) | spl9_43),
% 0.20/0.47    inference(avatar_component_clause,[],[f276])).
% 0.20/0.47  fof(f278,plain,(
% 0.20/0.47    ~spl9_43 | ~spl9_36 | ~spl9_29 | ~spl9_37 | spl9_41),
% 0.20/0.47    inference(avatar_split_clause,[],[f268,f257,f237,f180,f229,f276])).
% 0.20/0.47  fof(f180,plain,(
% 0.20/0.47    spl9_29 <=> r2_hidden(sK3,k1_relat_1(sK2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl9_29])])).
% 0.20/0.47  fof(f237,plain,(
% 0.20/0.47    spl9_37 <=> ! [X1,X0] : (k1_relat_1(X0) = k10_relat_1(X0,X1) | ~v1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),X1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl9_37])])).
% 0.20/0.47  fof(f257,plain,(
% 0.20/0.47    spl9_41 <=> r2_hidden(sK3,k10_relat_1(sK2,sK1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl9_41])])).
% 0.20/0.47  fof(f268,plain,(
% 0.20/0.47    ~v1_relat_1(sK2) | ~r1_tarski(k2_relat_1(sK2),sK1) | (~spl9_29 | ~spl9_37 | spl9_41)),
% 0.20/0.47    inference(subsumption_resolution,[],[f267,f197])).
% 0.20/0.47  fof(f197,plain,(
% 0.20/0.47    r2_hidden(sK3,k1_relat_1(sK2)) | ~spl9_29),
% 0.20/0.47    inference(avatar_component_clause,[],[f180])).
% 0.20/0.47  fof(f267,plain,(
% 0.20/0.47    ~r2_hidden(sK3,k1_relat_1(sK2)) | ~v1_relat_1(sK2) | ~r1_tarski(k2_relat_1(sK2),sK1) | (~spl9_37 | spl9_41)),
% 0.20/0.47    inference(superposition,[],[f258,f238])).
% 0.20/0.47  fof(f238,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k1_relat_1(X0) = k10_relat_1(X0,X1) | ~v1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),X1)) ) | ~spl9_37),
% 0.20/0.47    inference(avatar_component_clause,[],[f237])).
% 0.20/0.47  fof(f258,plain,(
% 0.20/0.47    ~r2_hidden(sK3,k10_relat_1(sK2,sK1)) | spl9_41),
% 0.20/0.47    inference(avatar_component_clause,[],[f257])).
% 0.20/0.47  fof(f259,plain,(
% 0.20/0.47    ~spl9_36 | ~spl9_41 | ~spl9_25 | ~spl9_38),
% 0.20/0.47    inference(avatar_split_clause,[],[f251,f243,f155,f257,f229])).
% 0.20/0.47  fof(f155,plain,(
% 0.20/0.47    spl9_25 <=> ! [X1,X0,X2] : (~v1_relat_1(X2) | r2_hidden(sK8(X0,X1,X2),X1) | ~r2_hidden(X0,k10_relat_1(X2,X1)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl9_25])])).
% 0.20/0.47  fof(f243,plain,(
% 0.20/0.47    spl9_38 <=> ! [X0] : (~r2_hidden(sK3,k10_relat_1(sK2,X0)) | ~r2_hidden(sK8(sK3,X0,sK2),sK1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl9_38])])).
% 0.20/0.47  fof(f251,plain,(
% 0.20/0.47    ~r2_hidden(sK3,k10_relat_1(sK2,sK1)) | ~v1_relat_1(sK2) | (~spl9_25 | ~spl9_38)),
% 0.20/0.47    inference(duplicate_literal_removal,[],[f250])).
% 0.20/0.47  fof(f250,plain,(
% 0.20/0.47    ~r2_hidden(sK3,k10_relat_1(sK2,sK1)) | ~v1_relat_1(sK2) | ~r2_hidden(sK3,k10_relat_1(sK2,sK1)) | (~spl9_25 | ~spl9_38)),
% 0.20/0.47    inference(resolution,[],[f244,f156])).
% 0.20/0.47  fof(f156,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (r2_hidden(sK8(X0,X1,X2),X1) | ~v1_relat_1(X2) | ~r2_hidden(X0,k10_relat_1(X2,X1))) ) | ~spl9_25),
% 0.20/0.47    inference(avatar_component_clause,[],[f155])).
% 0.20/0.47  fof(f244,plain,(
% 0.20/0.47    ( ! [X0] : (~r2_hidden(sK8(sK3,X0,sK2),sK1) | ~r2_hidden(sK3,k10_relat_1(sK2,X0))) ) | ~spl9_38),
% 0.20/0.47    inference(avatar_component_clause,[],[f243])).
% 0.20/0.47  fof(f245,plain,(
% 0.20/0.47    spl9_38 | ~spl9_13 | ~spl9_35),
% 0.20/0.47    inference(avatar_split_clause,[],[f235,f226,f104,f243])).
% 0.20/0.47  fof(f104,plain,(
% 0.20/0.47    spl9_13 <=> ! [X1,X0] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).
% 0.20/0.47  fof(f226,plain,(
% 0.20/0.47    spl9_35 <=> ! [X3] : (~r2_hidden(sK3,k10_relat_1(sK2,X3)) | ~m1_subset_1(sK8(sK3,X3,sK2),sK1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl9_35])])).
% 0.20/0.47  fof(f235,plain,(
% 0.20/0.47    ( ! [X0] : (~r2_hidden(sK3,k10_relat_1(sK2,X0)) | ~r2_hidden(sK8(sK3,X0,sK2),sK1)) ) | (~spl9_13 | ~spl9_35)),
% 0.20/0.47    inference(resolution,[],[f227,f105])).
% 0.20/0.47  fof(f105,plain,(
% 0.20/0.47    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) ) | ~spl9_13),
% 0.20/0.47    inference(avatar_component_clause,[],[f104])).
% 0.20/0.47  fof(f227,plain,(
% 0.20/0.47    ( ! [X3] : (~m1_subset_1(sK8(sK3,X3,sK2),sK1) | ~r2_hidden(sK3,k10_relat_1(sK2,X3))) ) | ~spl9_35),
% 0.20/0.47    inference(avatar_component_clause,[],[f226])).
% 0.20/0.47  fof(f239,plain,(
% 0.20/0.47    spl9_37 | ~spl9_7 | ~spl9_11 | ~spl9_22 | ~spl9_23),
% 0.20/0.47    inference(avatar_split_clause,[],[f172,f147,f143,f96,f79,f237])).
% 0.20/0.47  fof(f79,plain,(
% 0.20/0.47    spl9_7 <=> ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).
% 0.20/0.47  fof(f96,plain,(
% 0.20/0.47    spl9_11 <=> ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).
% 0.20/0.47  fof(f143,plain,(
% 0.20/0.47    spl9_22 <=> ! [X1,X0] : (~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | k5_relat_1(X1,k6_relat_1(X0)) = X1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl9_22])])).
% 0.20/0.47  fof(f147,plain,(
% 0.20/0.47    spl9_23 <=> ! [X1,X0] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl9_23])])).
% 0.20/0.47  fof(f172,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k1_relat_1(X0) = k10_relat_1(X0,X1) | ~v1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),X1)) ) | (~spl9_7 | ~spl9_11 | ~spl9_22 | ~spl9_23)),
% 0.20/0.47    inference(forward_demodulation,[],[f171,f97])).
% 0.20/0.47  fof(f97,plain,(
% 0.20/0.47    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) ) | ~spl9_11),
% 0.20/0.47    inference(avatar_component_clause,[],[f96])).
% 0.20/0.47  fof(f171,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k1_relat_1(X0) = k10_relat_1(X0,k1_relat_1(k6_relat_1(X1))) | ~v1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),X1)) ) | (~spl9_7 | ~spl9_22 | ~spl9_23)),
% 0.20/0.47    inference(subsumption_resolution,[],[f170,f80])).
% 0.20/0.47  fof(f80,plain,(
% 0.20/0.47    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) ) | ~spl9_7),
% 0.20/0.47    inference(avatar_component_clause,[],[f79])).
% 0.20/0.47  fof(f170,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k1_relat_1(X0) = k10_relat_1(X0,k1_relat_1(k6_relat_1(X1))) | ~v1_relat_1(k6_relat_1(X1)) | ~v1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),X1)) ) | (~spl9_22 | ~spl9_23)),
% 0.20/0.47    inference(duplicate_literal_removal,[],[f168])).
% 0.20/0.47  fof(f168,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k1_relat_1(X0) = k10_relat_1(X0,k1_relat_1(k6_relat_1(X1))) | ~v1_relat_1(k6_relat_1(X1)) | ~v1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),X1) | ~v1_relat_1(X0)) ) | (~spl9_22 | ~spl9_23)),
% 0.20/0.47    inference(superposition,[],[f148,f144])).
% 0.20/0.47  fof(f144,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) ) | ~spl9_22),
% 0.20/0.47    inference(avatar_component_clause,[],[f143])).
% 0.20/0.48  fof(f148,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl9_23),
% 0.20/0.48    inference(avatar_component_clause,[],[f147])).
% 0.20/0.48  fof(f234,plain,(
% 0.20/0.48    ~spl9_4 | ~spl9_9 | ~spl9_14 | spl9_36),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f232])).
% 0.20/0.48  fof(f232,plain,(
% 0.20/0.48    $false | (~spl9_4 | ~spl9_9 | ~spl9_14 | spl9_36)),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f88,f69,f230,f109])).
% 0.20/0.48  fof(f109,plain,(
% 0.20/0.48    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | ~spl9_14),
% 0.20/0.48    inference(avatar_component_clause,[],[f108])).
% 0.20/0.48  fof(f108,plain,(
% 0.20/0.48    spl9_14 <=> ! [X1,X0] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).
% 0.20/0.48  fof(f230,plain,(
% 0.20/0.48    ~v1_relat_1(sK2) | spl9_36),
% 0.20/0.48    inference(avatar_component_clause,[],[f229])).
% 0.20/0.48  fof(f88,plain,(
% 0.20/0.48    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) ) | ~spl9_9),
% 0.20/0.48    inference(avatar_component_clause,[],[f87])).
% 0.20/0.48  fof(f87,plain,(
% 0.20/0.48    spl9_9 <=> ! [X1,X0] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).
% 0.20/0.48  fof(f231,plain,(
% 0.20/0.48    spl9_35 | ~spl9_36 | ~spl9_10 | ~spl9_28),
% 0.20/0.48    inference(avatar_split_clause,[],[f202,f176,f92,f229,f226])).
% 0.20/0.48  fof(f92,plain,(
% 0.20/0.48    spl9_10 <=> ! [X4] : (~m1_subset_1(X4,sK1) | ~r2_hidden(k4_tarski(sK3,X4),sK2))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).
% 0.20/0.48  fof(f176,plain,(
% 0.20/0.48    spl9_28 <=> ! [X1,X0,X2] : (~v1_relat_1(X2) | r2_hidden(k4_tarski(X0,sK8(X0,X1,X2)),X2) | ~r2_hidden(X0,k10_relat_1(X2,X1)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl9_28])])).
% 0.20/0.48  fof(f202,plain,(
% 0.20/0.48    ( ! [X3] : (~v1_relat_1(sK2) | ~r2_hidden(sK3,k10_relat_1(sK2,X3)) | ~m1_subset_1(sK8(sK3,X3,sK2),sK1)) ) | (~spl9_10 | ~spl9_28)),
% 0.20/0.48    inference(resolution,[],[f177,f93])).
% 0.20/0.48  fof(f93,plain,(
% 0.20/0.48    ( ! [X4] : (~r2_hidden(k4_tarski(sK3,X4),sK2) | ~m1_subset_1(X4,sK1)) ) | ~spl9_10),
% 0.20/0.48    inference(avatar_component_clause,[],[f92])).
% 0.20/0.48  fof(f177,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,sK8(X0,X1,X2)),X2) | ~v1_relat_1(X2) | ~r2_hidden(X0,k10_relat_1(X2,X1))) ) | ~spl9_28),
% 0.20/0.48    inference(avatar_component_clause,[],[f176])).
% 0.20/0.48  fof(f198,plain,(
% 0.20/0.48    spl9_29 | ~spl9_4 | ~spl9_5 | ~spl9_26),
% 0.20/0.48    inference(avatar_split_clause,[],[f196,f159,f72,f68,f180])).
% 0.20/0.48  fof(f72,plain,(
% 0.20/0.48    spl9_5 <=> r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 0.20/0.48  fof(f159,plain,(
% 0.20/0.48    spl9_26 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl9_26])])).
% 0.20/0.48  fof(f196,plain,(
% 0.20/0.48    r2_hidden(sK3,k1_relat_1(sK2)) | (~spl9_4 | ~spl9_5 | ~spl9_26)),
% 0.20/0.48    inference(subsumption_resolution,[],[f192,f69])).
% 0.20/0.48  fof(f192,plain,(
% 0.20/0.48    r2_hidden(sK3,k1_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (~spl9_5 | ~spl9_26)),
% 0.20/0.48    inference(superposition,[],[f73,f160])).
% 0.20/0.48  fof(f160,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl9_26),
% 0.20/0.48    inference(avatar_component_clause,[],[f159])).
% 0.20/0.48  fof(f73,plain,(
% 0.20/0.48    r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2)) | ~spl9_5),
% 0.20/0.48    inference(avatar_component_clause,[],[f72])).
% 0.20/0.48  fof(f191,plain,(
% 0.20/0.48    ~spl9_8 | ~spl9_19 | spl9_29),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f189])).
% 0.20/0.48  % (32378)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.48  fof(f189,plain,(
% 0.20/0.48    $false | (~spl9_8 | ~spl9_19 | spl9_29)),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f84,f181,f129])).
% 0.20/0.48  fof(f129,plain,(
% 0.20/0.48    ( ! [X2,X0,X3] : (r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(k4_tarski(X2,X3),X0)) ) | ~spl9_19),
% 0.20/0.48    inference(avatar_component_clause,[],[f128])).
% 0.20/0.48  fof(f128,plain,(
% 0.20/0.48    spl9_19 <=> ! [X3,X0,X2] : (~r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,k1_relat_1(X0)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).
% 0.20/0.48  fof(f181,plain,(
% 0.20/0.48    ~r2_hidden(sK3,k1_relat_1(sK2)) | spl9_29),
% 0.20/0.48    inference(avatar_component_clause,[],[f180])).
% 0.20/0.48  fof(f84,plain,(
% 0.20/0.48    r2_hidden(k4_tarski(sK3,sK4),sK2) | ~spl9_8),
% 0.20/0.48    inference(avatar_component_clause,[],[f83])).
% 0.20/0.48  fof(f83,plain,(
% 0.20/0.48    spl9_8 <=> r2_hidden(k4_tarski(sK3,sK4),sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).
% 0.20/0.48  fof(f182,plain,(
% 0.20/0.48    ~spl9_29 | ~spl9_4 | spl9_5 | ~spl9_26),
% 0.20/0.48    inference(avatar_split_clause,[],[f174,f159,f72,f68,f180])).
% 0.20/0.48  fof(f174,plain,(
% 0.20/0.48    ~r2_hidden(sK3,k1_relat_1(sK2)) | (~spl9_4 | spl9_5 | ~spl9_26)),
% 0.20/0.48    inference(subsumption_resolution,[],[f173,f69])).
% 0.20/0.48  fof(f173,plain,(
% 0.20/0.48    ~r2_hidden(sK3,k1_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (spl9_5 | ~spl9_26)),
% 0.20/0.48    inference(superposition,[],[f90,f160])).
% 0.20/0.48  fof(f90,plain,(
% 0.20/0.48    ~r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2)) | spl9_5),
% 0.20/0.48    inference(avatar_component_clause,[],[f72])).
% 0.20/0.48  fof(f178,plain,(
% 0.20/0.48    spl9_28),
% 0.20/0.48    inference(avatar_split_clause,[],[f47,f176])).
% 0.20/0.48  fof(f47,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | r2_hidden(k4_tarski(X0,sK8(X0,X1,X2)),X2) | ~r2_hidden(X0,k10_relat_1(X2,X1))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f22])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.20/0.48    inference(ennf_transformation,[],[f7])).
% 0.20/0.48  fof(f7,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).
% 0.20/0.48  fof(f161,plain,(
% 0.20/0.48    spl9_26),
% 0.20/0.48    inference(avatar_split_clause,[],[f50,f159])).
% 0.20/0.48  fof(f50,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f23])).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.48    inference(ennf_transformation,[],[f12])).
% 0.20/0.48  fof(f12,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.48  fof(f157,plain,(
% 0.20/0.48    spl9_25),
% 0.20/0.48    inference(avatar_split_clause,[],[f48,f155])).
% 0.20/0.48  fof(f48,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | r2_hidden(sK8(X0,X1,X2),X1) | ~r2_hidden(X0,k10_relat_1(X2,X1))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f22])).
% 0.20/0.48  fof(f149,plain,(
% 0.20/0.48    spl9_23),
% 0.20/0.48    inference(avatar_split_clause,[],[f35,f147])).
% 0.20/0.48  fof(f35,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f16])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f8])).
% 0.20/0.48  fof(f8,axiom,(
% 0.20/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).
% 0.20/0.48  fof(f145,plain,(
% 0.20/0.48    spl9_22),
% 0.20/0.48    inference(avatar_split_clause,[],[f38,f143])).
% 0.20/0.48  fof(f38,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | k5_relat_1(X1,k6_relat_1(X0)) = X1) )),
% 0.20/0.48    inference(cnf_transformation,[],[f19])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.20/0.48    inference(flattening,[],[f18])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f10])).
% 0.20/0.48  fof(f10,axiom,(
% 0.20/0.48    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).
% 0.20/0.48  fof(f130,plain,(
% 0.20/0.48    spl9_19),
% 0.20/0.48    inference(avatar_split_clause,[],[f54,f128])).
% 0.20/0.48  fof(f54,plain,(
% 0.20/0.48    ( ! [X2,X0,X3] : (~r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,k1_relat_1(X0))) )),
% 0.20/0.48    inference(equality_resolution,[],[f42])).
% 0.20/0.48  fof(f42,plain,(
% 0.20/0.48    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1) | k1_relat_1(X0) != X1) )),
% 0.20/0.48    inference(cnf_transformation,[],[f4])).
% 0.20/0.48  fof(f4,axiom,(
% 0.20/0.48    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).
% 0.20/0.48  fof(f126,plain,(
% 0.20/0.48    spl9_18),
% 0.20/0.48    inference(avatar_split_clause,[],[f52,f124])).
% 0.20/0.48  fof(f52,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f24])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.48    inference(ennf_transformation,[],[f11])).
% 0.20/0.48  fof(f11,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.48  fof(f118,plain,(
% 0.20/0.48    spl9_16),
% 0.20/0.48    inference(avatar_split_clause,[],[f40,f116])).
% 0.20/0.48  fof(f40,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f20])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.20/0.48  fof(f110,plain,(
% 0.20/0.48    spl9_14),
% 0.20/0.48    inference(avatar_split_clause,[],[f36,f108])).
% 0.20/0.48  fof(f36,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f17])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.48  fof(f106,plain,(
% 0.20/0.48    spl9_13),
% 0.20/0.48    inference(avatar_split_clause,[],[f41,f104])).
% 0.20/0.48  fof(f41,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f21])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 0.20/0.48  fof(f98,plain,(
% 0.20/0.48    spl9_11),
% 0.20/0.48    inference(avatar_split_clause,[],[f33,f96])).
% 0.20/0.48  fof(f33,plain,(
% 0.20/0.48    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.20/0.48    inference(cnf_transformation,[],[f9])).
% 0.20/0.48  fof(f9,axiom,(
% 0.20/0.48    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.20/0.48  fof(f94,plain,(
% 0.20/0.48    ~spl9_5 | spl9_10),
% 0.20/0.48    inference(avatar_split_clause,[],[f25,f92,f72])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    ( ! [X4] : (~m1_subset_1(X4,sK1) | ~r2_hidden(k4_tarski(sK3,X4),sK2) | ~r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f15])).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r2_hidden(X3,k1_relset_1(X0,X1,X2)) <~> ? [X4] : (r2_hidden(k4_tarski(X3,X4),X2) & m1_subset_1(X4,X1))) & m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f14])).
% 0.20/0.48  fof(f14,negated_conjecture,(
% 0.20/0.48    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,k1_relset_1(X0,X1,X2)) <=> ? [X4] : (r2_hidden(k4_tarski(X3,X4),X2) & m1_subset_1(X4,X1)))))))),
% 0.20/0.48    inference(negated_conjecture,[],[f13])).
% 0.20/0.48  fof(f13,conjecture,(
% 0.20/0.48    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,k1_relset_1(X0,X1,X2)) <=> ? [X4] : (r2_hidden(k4_tarski(X3,X4),X2) & m1_subset_1(X4,X1)))))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relset_1)).
% 0.20/0.48  fof(f89,plain,(
% 0.20/0.48    spl9_9),
% 0.20/0.48    inference(avatar_split_clause,[],[f37,f87])).
% 0.20/0.48  fof(f37,plain,(
% 0.20/0.48    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f6])).
% 0.20/0.48  fof(f6,axiom,(
% 0.20/0.48    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.48  fof(f85,plain,(
% 0.20/0.48    spl9_5 | spl9_8),
% 0.20/0.48    inference(avatar_split_clause,[],[f27,f83,f72])).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    r2_hidden(k4_tarski(sK3,sK4),sK2) | r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2))),
% 0.20/0.48    inference(cnf_transformation,[],[f15])).
% 0.20/0.48  fof(f81,plain,(
% 0.20/0.48    spl9_7),
% 0.20/0.48    inference(avatar_split_clause,[],[f32,f79])).
% 0.20/0.48  fof(f32,plain,(
% 0.20/0.48    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,axiom,(
% 0.20/0.48    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.20/0.48  fof(f70,plain,(
% 0.20/0.48    spl9_4),
% 0.20/0.48    inference(avatar_split_clause,[],[f29,f68])).
% 0.20/0.48  fof(f29,plain,(
% 0.20/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.48    inference(cnf_transformation,[],[f15])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (32381)------------------------------
% 0.20/0.48  % (32381)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (32381)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (32381)Memory used [KB]: 10746
% 0.20/0.48  % (32381)Time elapsed: 0.070 s
% 0.20/0.48  % (32381)------------------------------
% 0.20/0.48  % (32381)------------------------------
% 0.20/0.48  % (32371)Success in time 0.121 s
%------------------------------------------------------------------------------
