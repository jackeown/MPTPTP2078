%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:16 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  162 ( 277 expanded)
%              Number of leaves         :   40 ( 129 expanded)
%              Depth                    :    6
%              Number of atoms          :  541 ( 937 expanded)
%              Number of equality atoms :   36 (  73 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f368,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f57,f65,f69,f73,f77,f81,f85,f89,f93,f116,f120,f124,f136,f139,f145,f150,f158,f168,f181,f202,f217,f220,f227,f243,f261,f274,f288,f307,f314,f327,f355,f367])).

fof(f367,plain,
    ( spl8_31
    | ~ spl8_47
    | ~ spl8_53 ),
    inference(avatar_contradiction_clause,[],[f366])).

fof(f366,plain,
    ( $false
    | spl8_31
    | ~ spl8_47
    | ~ spl8_53 ),
    inference(subsumption_resolution,[],[f364,f198])).

fof(f198,plain,
    ( ~ r2_hidden(sK6(sK3,sK2,sK4),sK0)
    | spl8_31 ),
    inference(avatar_component_clause,[],[f197])).

fof(f197,plain,
    ( spl8_31
  <=> r2_hidden(sK6(sK3,sK2,sK4),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_31])])).

fof(f364,plain,
    ( r2_hidden(sK6(sK3,sK2,sK4),sK0)
    | ~ spl8_47
    | ~ spl8_53 ),
    inference(resolution,[],[f354,f313])).

fof(f313,plain,
    ( r2_hidden(k4_tarski(sK6(sK3,sK2,sK4),sK4),sK3)
    | ~ spl8_47 ),
    inference(avatar_component_clause,[],[f312])).

fof(f312,plain,
    ( spl8_47
  <=> r2_hidden(k4_tarski(sK6(sK3,sK2,sK4),sK4),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_47])])).

fof(f354,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(k4_tarski(X2,X3),sK3)
        | r2_hidden(X2,sK0) )
    | ~ spl8_53 ),
    inference(avatar_component_clause,[],[f353])).

fof(f353,plain,
    ( spl8_53
  <=> ! [X3,X2] :
        ( ~ r2_hidden(k4_tarski(X2,X3),sK3)
        | r2_hidden(X2,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_53])])).

fof(f355,plain,
    ( spl8_53
    | ~ spl8_10
    | ~ spl8_45 ),
    inference(avatar_split_clause,[],[f330,f305,f91,f353])).

fof(f91,plain,
    ( spl8_10
  <=> ! [X1,X3,X0,X2] :
        ( r2_hidden(X0,X2)
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f305,plain,
    ( spl8_45
  <=> ! [X0] :
        ( r2_hidden(X0,k2_zfmisc_1(sK0,sK1))
        | ~ r2_hidden(X0,sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_45])])).

fof(f330,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(k4_tarski(X2,X3),sK3)
        | r2_hidden(X2,sK0) )
    | ~ spl8_10
    | ~ spl8_45 ),
    inference(resolution,[],[f306,f92])).

fof(f92,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | r2_hidden(X0,X2) )
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f91])).

fof(f306,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k2_zfmisc_1(sK0,sK1))
        | ~ r2_hidden(X0,sK3) )
    | ~ spl8_45 ),
    inference(avatar_component_clause,[],[f305])).

fof(f327,plain,
    ( ~ spl8_19
    | ~ spl8_1
    | ~ spl8_20
    | ~ spl8_21
    | spl8_46 ),
    inference(avatar_split_clause,[],[f318,f309,f143,f134,f55,f130])).

fof(f130,plain,
    ( spl8_19
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f55,plain,
    ( spl8_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f134,plain,
    ( spl8_20
  <=> ! [X1,X3,X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | r2_hidden(sK6(X0,X1,X3),k1_relat_1(X0))
        | ~ r2_hidden(X3,k9_relat_1(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f143,plain,
    ( spl8_21
  <=> r2_hidden(sK4,k9_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).

fof(f309,plain,
    ( spl8_46
  <=> r2_hidden(sK6(sK3,sK2,sK4),k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_46])])).

fof(f318,plain,
    ( ~ v1_relat_1(sK3)
    | ~ spl8_1
    | ~ spl8_20
    | ~ spl8_21
    | spl8_46 ),
    inference(subsumption_resolution,[],[f317,f144])).

fof(f144,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ spl8_21 ),
    inference(avatar_component_clause,[],[f143])).

fof(f317,plain,
    ( ~ v1_relat_1(sK3)
    | ~ r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ spl8_1
    | ~ spl8_20
    | spl8_46 ),
    inference(subsumption_resolution,[],[f315,f56])).

fof(f56,plain,
    ( v1_funct_1(sK3)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f55])).

fof(f315,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ spl8_20
    | spl8_46 ),
    inference(resolution,[],[f310,f135])).

fof(f135,plain,
    ( ! [X0,X3,X1] :
        ( r2_hidden(sK6(X0,X1,X3),k1_relat_1(X0))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | ~ r2_hidden(X3,k9_relat_1(X0,X1)) )
    | ~ spl8_20 ),
    inference(avatar_component_clause,[],[f134])).

fof(f310,plain,
    ( ~ r2_hidden(sK6(sK3,sK2,sK4),k1_relat_1(sK3))
    | spl8_46 ),
    inference(avatar_component_clause,[],[f309])).

fof(f314,plain,
    ( ~ spl8_46
    | spl8_47
    | ~ spl8_24
    | ~ spl8_28 ),
    inference(avatar_split_clause,[],[f187,f179,f156,f312,f309])).

fof(f156,plain,
    ( spl8_24
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK3))
        | r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).

fof(f179,plain,
    ( spl8_28
  <=> sK4 = k1_funct_1(sK3,sK6(sK3,sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).

fof(f187,plain,
    ( r2_hidden(k4_tarski(sK6(sK3,sK2,sK4),sK4),sK3)
    | ~ r2_hidden(sK6(sK3,sK2,sK4),k1_relat_1(sK3))
    | ~ spl8_24
    | ~ spl8_28 ),
    inference(superposition,[],[f157,f180])).

fof(f180,plain,
    ( sK4 = k1_funct_1(sK3,sK6(sK3,sK2,sK4))
    | ~ spl8_28 ),
    inference(avatar_component_clause,[],[f179])).

fof(f157,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3)
        | ~ r2_hidden(X0,k1_relat_1(sK3)) )
    | ~ spl8_24 ),
    inference(avatar_component_clause,[],[f156])).

fof(f307,plain,
    ( spl8_45
    | ~ spl8_3
    | ~ spl8_43 ),
    inference(avatar_split_clause,[],[f297,f286,f63,f305])).

fof(f63,plain,
    ( spl8_3
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f286,plain,
    ( spl8_43
  <=> ! [X1,X0] :
        ( r2_hidden(X0,k2_zfmisc_1(sK0,sK1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_43])])).

fof(f297,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k2_zfmisc_1(sK0,sK1))
        | ~ r2_hidden(X0,sK3) )
    | ~ spl8_3
    | ~ spl8_43 ),
    inference(resolution,[],[f287,f64])).

fof(f64,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f63])).

fof(f287,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | r2_hidden(X0,k2_zfmisc_1(sK0,sK1))
        | ~ r2_hidden(X0,X1) )
    | ~ spl8_43 ),
    inference(avatar_component_clause,[],[f286])).

fof(f288,plain,
    ( spl8_43
    | ~ spl8_9
    | ~ spl8_35 ),
    inference(avatar_split_clause,[],[f275,f222,f87,f286])).

fof(f87,plain,
    ( spl8_9
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
        | m1_subset_1(X0,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f222,plain,
    ( spl8_35
  <=> ! [X1] :
        ( ~ m1_subset_1(X1,k2_zfmisc_1(sK0,sK1))
        | r2_hidden(X1,k2_zfmisc_1(sK0,sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_35])])).

fof(f275,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,k2_zfmisc_1(sK0,sK1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ r2_hidden(X0,X1) )
    | ~ spl8_9
    | ~ spl8_35 ),
    inference(resolution,[],[f223,f88])).

fof(f88,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(X0,X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
        | ~ r2_hidden(X0,X1) )
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f87])).

fof(f223,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k2_zfmisc_1(sK0,sK1))
        | r2_hidden(X1,k2_zfmisc_1(sK0,sK1)) )
    | ~ spl8_35 ),
    inference(avatar_component_clause,[],[f222])).

fof(f274,plain,
    ( ~ spl8_21
    | ~ spl8_41 ),
    inference(avatar_contradiction_clause,[],[f266])).

fof(f266,plain,
    ( $false
    | ~ spl8_21
    | ~ spl8_41 ),
    inference(unit_resulting_resolution,[],[f144,f260])).

fof(f260,plain,
    ( ! [X4,X3] : ~ r2_hidden(X3,k9_relat_1(sK3,X4))
    | ~ spl8_41 ),
    inference(avatar_component_clause,[],[f259])).

fof(f259,plain,
    ( spl8_41
  <=> ! [X3,X4] : ~ r2_hidden(X3,k9_relat_1(sK3,X4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_41])])).

fof(f261,plain,
    ( spl8_41
    | ~ spl8_19
    | ~ spl8_1
    | ~ spl8_20
    | ~ spl8_39 ),
    inference(avatar_split_clause,[],[f251,f241,f134,f55,f130,f259])).

fof(f241,plain,
    ( spl8_39
  <=> ! [X0] : ~ r2_hidden(X0,k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_39])])).

fof(f251,plain,
    ( ! [X4,X3] :
        ( ~ v1_relat_1(sK3)
        | ~ r2_hidden(X3,k9_relat_1(sK3,X4)) )
    | ~ spl8_1
    | ~ spl8_20
    | ~ spl8_39 ),
    inference(subsumption_resolution,[],[f247,f56])).

fof(f247,plain,
    ( ! [X4,X3] :
        ( ~ v1_funct_1(sK3)
        | ~ v1_relat_1(sK3)
        | ~ r2_hidden(X3,k9_relat_1(sK3,X4)) )
    | ~ spl8_20
    | ~ spl8_39 ),
    inference(resolution,[],[f242,f135])).

fof(f242,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_relat_1(sK3))
    | ~ spl8_39 ),
    inference(avatar_component_clause,[],[f241])).

fof(f243,plain,
    ( spl8_39
    | ~ spl8_24
    | ~ spl8_36 ),
    inference(avatar_split_clause,[],[f228,f225,f156,f241])).

fof(f225,plain,
    ( spl8_36
  <=> ! [X0] : ~ r2_hidden(X0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_36])])).

fof(f228,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_relat_1(sK3))
    | ~ spl8_24
    | ~ spl8_36 ),
    inference(resolution,[],[f226,f157])).

fof(f226,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK3)
    | ~ spl8_36 ),
    inference(avatar_component_clause,[],[f225])).

fof(f227,plain,
    ( spl8_35
    | spl8_36
    | ~ spl8_3
    | ~ spl8_34 ),
    inference(avatar_split_clause,[],[f218,f215,f63,f225,f222])).

fof(f215,plain,
    ( spl8_34
  <=> ! [X1,X3,X0,X2] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r2_hidden(X2,X0)
        | ~ m1_subset_1(X3,X1)
        | r2_hidden(X3,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_34])])).

fof(f218,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,sK3)
        | ~ m1_subset_1(X1,k2_zfmisc_1(sK0,sK1))
        | r2_hidden(X1,k2_zfmisc_1(sK0,sK1)) )
    | ~ spl8_3
    | ~ spl8_34 ),
    inference(resolution,[],[f216,f64])).

fof(f216,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r2_hidden(X2,X0)
        | ~ m1_subset_1(X3,X1)
        | r2_hidden(X3,X1) )
    | ~ spl8_34 ),
    inference(avatar_component_clause,[],[f215])).

fof(f220,plain,
    ( ~ spl8_19
    | ~ spl8_1
    | ~ spl8_16
    | ~ spl8_21
    | spl8_32 ),
    inference(avatar_split_clause,[],[f213,f200,f143,f118,f55,f130])).

fof(f118,plain,
    ( spl8_16
  <=> ! [X1,X3,X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | r2_hidden(sK6(X0,X1,X3),X1)
        | ~ r2_hidden(X3,k9_relat_1(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f200,plain,
    ( spl8_32
  <=> r2_hidden(sK6(sK3,sK2,sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).

fof(f213,plain,
    ( ~ v1_relat_1(sK3)
    | ~ spl8_1
    | ~ spl8_16
    | ~ spl8_21
    | spl8_32 ),
    inference(subsumption_resolution,[],[f212,f144])).

fof(f212,plain,
    ( ~ v1_relat_1(sK3)
    | ~ r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ spl8_1
    | ~ spl8_16
    | spl8_32 ),
    inference(subsumption_resolution,[],[f211,f56])).

fof(f211,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ spl8_16
    | spl8_32 ),
    inference(resolution,[],[f201,f119])).

fof(f119,plain,
    ( ! [X0,X3,X1] :
        ( r2_hidden(sK6(X0,X1,X3),X1)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | ~ r2_hidden(X3,k9_relat_1(X0,X1)) )
    | ~ spl8_16 ),
    inference(avatar_component_clause,[],[f118])).

fof(f201,plain,
    ( ~ r2_hidden(sK6(sK3,sK2,sK4),sK2)
    | spl8_32 ),
    inference(avatar_component_clause,[],[f200])).

fof(f217,plain,
    ( spl8_34
    | ~ spl8_6
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f98,f83,f75,f215])).

fof(f75,plain,
    ( spl8_6
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,X1)
        | v1_xboole_0(X1)
        | r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f83,plain,
    ( spl8_8
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
        | ~ v1_xboole_0(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f98,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r2_hidden(X2,X0)
        | ~ m1_subset_1(X3,X1)
        | r2_hidden(X3,X1) )
    | ~ spl8_6
    | ~ spl8_8 ),
    inference(resolution,[],[f84,f76])).

fof(f76,plain,
    ( ! [X0,X1] :
        ( v1_xboole_0(X1)
        | ~ m1_subset_1(X0,X1)
        | r2_hidden(X0,X1) )
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f75])).

fof(f84,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_xboole_0(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
        | ~ r2_hidden(X0,X1) )
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f83])).

fof(f202,plain,
    ( ~ spl8_31
    | ~ spl8_32
    | ~ spl8_5
    | ~ spl8_28 ),
    inference(avatar_split_clause,[],[f190,f179,f71,f200,f197])).

fof(f71,plain,
    ( spl8_5
  <=> ! [X5] :
        ( ~ r2_hidden(X5,sK0)
        | ~ r2_hidden(X5,sK2)
        | sK4 != k1_funct_1(sK3,X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f190,plain,
    ( ~ r2_hidden(sK6(sK3,sK2,sK4),sK2)
    | ~ r2_hidden(sK6(sK3,sK2,sK4),sK0)
    | ~ spl8_5
    | ~ spl8_28 ),
    inference(trivial_inequality_removal,[],[f188])).

fof(f188,plain,
    ( sK4 != sK4
    | ~ r2_hidden(sK6(sK3,sK2,sK4),sK2)
    | ~ r2_hidden(sK6(sK3,sK2,sK4),sK0)
    | ~ spl8_5
    | ~ spl8_28 ),
    inference(superposition,[],[f72,f180])).

fof(f72,plain,
    ( ! [X5] :
        ( sK4 != k1_funct_1(sK3,X5)
        | ~ r2_hidden(X5,sK2)
        | ~ r2_hidden(X5,sK0) )
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f71])).

fof(f181,plain,
    ( spl8_28
    | ~ spl8_21
    | ~ spl8_26 ),
    inference(avatar_split_clause,[],[f174,f166,f143,f179])).

fof(f166,plain,
    ( spl8_26
  <=> ! [X1,X0] :
        ( k1_funct_1(sK3,sK6(sK3,X0,X1)) = X1
        | ~ r2_hidden(X1,k9_relat_1(sK3,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).

fof(f174,plain,
    ( sK4 = k1_funct_1(sK3,sK6(sK3,sK2,sK4))
    | ~ spl8_21
    | ~ spl8_26 ),
    inference(resolution,[],[f167,f144])).

fof(f167,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k9_relat_1(sK3,X0))
        | k1_funct_1(sK3,sK6(sK3,X0,X1)) = X1 )
    | ~ spl8_26 ),
    inference(avatar_component_clause,[],[f166])).

fof(f168,plain,
    ( spl8_26
    | ~ spl8_19
    | ~ spl8_1
    | ~ spl8_22 ),
    inference(avatar_split_clause,[],[f159,f148,f55,f130,f166])).

fof(f148,plain,
    ( spl8_22
  <=> ! [X1,X3,X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | k1_funct_1(X0,sK6(X0,X1,X3)) = X3
        | ~ r2_hidden(X3,k9_relat_1(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).

fof(f159,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(sK3)
        | k1_funct_1(sK3,sK6(sK3,X0,X1)) = X1
        | ~ r2_hidden(X1,k9_relat_1(sK3,X0)) )
    | ~ spl8_1
    | ~ spl8_22 ),
    inference(resolution,[],[f149,f56])).

fof(f149,plain,
    ( ! [X0,X3,X1] :
        ( ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | k1_funct_1(X0,sK6(X0,X1,X3)) = X3
        | ~ r2_hidden(X3,k9_relat_1(X0,X1)) )
    | ~ spl8_22 ),
    inference(avatar_component_clause,[],[f148])).

fof(f158,plain,
    ( spl8_24
    | ~ spl8_19
    | ~ spl8_1
    | ~ spl8_17 ),
    inference(avatar_split_clause,[],[f146,f122,f55,f130,f156])).

fof(f122,plain,
    ( spl8_17
  <=> ! [X0,X2] :
        ( ~ v1_relat_1(X2)
        | ~ v1_funct_1(X2)
        | ~ r2_hidden(X0,k1_relat_1(X2))
        | r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f146,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK3)
        | ~ r2_hidden(X0,k1_relat_1(sK3))
        | r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3) )
    | ~ spl8_1
    | ~ spl8_17 ),
    inference(resolution,[],[f123,f56])).

fof(f123,plain,
    ( ! [X2,X0] :
        ( ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2)
        | ~ r2_hidden(X0,k1_relat_1(X2))
        | r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) )
    | ~ spl8_17 ),
    inference(avatar_component_clause,[],[f122])).

fof(f150,plain,(
    spl8_22 ),
    inference(avatar_split_clause,[],[f50,f148])).

fof(f50,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_funct_1(X0,sK6(X0,X1,X3)) = X3
      | ~ r2_hidden(X3,k9_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_funct_1(X0,sK6(X0,X1,X3)) = X3
      | ~ r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_funct_1)).

fof(f145,plain,
    ( spl8_21
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_15 ),
    inference(avatar_split_clause,[],[f141,f114,f67,f63,f143])).

fof(f67,plain,
    ( spl8_4
  <=> r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f114,plain,
    ( spl8_15
  <=> ! [X1,X3,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f141,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_15 ),
    inference(subsumption_resolution,[],[f140,f64])).

fof(f140,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl8_4
    | ~ spl8_15 ),
    inference(superposition,[],[f68,f115])).

fof(f115,plain,
    ( ! [X2,X0,X3,X1] :
        ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl8_15 ),
    inference(avatar_component_clause,[],[f114])).

fof(f68,plain,
    ( r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f67])).

fof(f139,plain,
    ( ~ spl8_3
    | ~ spl8_7
    | spl8_19 ),
    inference(avatar_contradiction_clause,[],[f137])).

fof(f137,plain,
    ( $false
    | ~ spl8_3
    | ~ spl8_7
    | spl8_19 ),
    inference(unit_resulting_resolution,[],[f64,f131,f80])).

fof(f80,plain,
    ( ! [X2,X0,X1] :
        ( v1_relat_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl8_7
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f131,plain,
    ( ~ v1_relat_1(sK3)
    | spl8_19 ),
    inference(avatar_component_clause,[],[f130])).

fof(f136,plain,(
    spl8_20 ),
    inference(avatar_split_clause,[],[f52,f134])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(sK6(X0,X1,X3),k1_relat_1(X0))
      | ~ r2_hidden(X3,k9_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(sK6(X0,X1,X3),k1_relat_1(X0))
      | ~ r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f124,plain,(
    spl8_17 ),
    inference(avatar_split_clause,[],[f53,f122])).

fof(f53,plain,(
    ! [X2,X0] :
      ( ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | k1_funct_1(X2,X0) != X1
      | r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(f120,plain,(
    spl8_16 ),
    inference(avatar_split_clause,[],[f51,f118])).

fof(f51,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(sK6(X0,X1,X3),X1)
      | ~ r2_hidden(X3,k9_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(sK6(X0,X1,X3),X1)
      | ~ r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f116,plain,(
    spl8_15 ),
    inference(avatar_split_clause,[],[f44,f114])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f93,plain,(
    spl8_10 ),
    inference(avatar_split_clause,[],[f45,f91])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f89,plain,(
    spl8_9 ),
    inference(avatar_split_clause,[],[f42,f87])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f85,plain,(
    spl8_8 ),
    inference(avatar_split_clause,[],[f43,f83])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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

fof(f81,plain,(
    spl8_7 ),
    inference(avatar_split_clause,[],[f38,f79])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f77,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f37,f75])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f73,plain,(
    spl8_5 ),
    inference(avatar_split_clause,[],[f24,f71])).

fof(f24,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,sK0)
      | ~ r2_hidden(X5,sK2)
      | sK4 != k1_funct_1(sK3,X5) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ r2_hidden(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ r2_hidden(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ~ ( k1_funct_1(X3,X5) = X4
                    & r2_hidden(X5,X2)
                    & r2_hidden(X5,X0) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ~ ( ! [X5] :
                ~ ( k1_funct_1(X3,X5) = X4
                  & r2_hidden(X5,X2)
                  & r2_hidden(X5,X0) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t115_funct_2)).

fof(f69,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f25,f67])).

fof(f25,plain,(
    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f65,plain,(
    spl8_3 ),
    inference(avatar_split_clause,[],[f28,f63])).

fof(f28,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f12])).

fof(f57,plain,(
    spl8_1 ),
    inference(avatar_split_clause,[],[f26,f55])).

fof(f26,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:12:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.45  % (8361)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.47  % (8369)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.47  % (8362)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.47  % (8370)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.47  % (8361)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.48  % (8354)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.48  % (8355)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.48  % (8356)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.48  % (8358)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f368,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(avatar_sat_refutation,[],[f57,f65,f69,f73,f77,f81,f85,f89,f93,f116,f120,f124,f136,f139,f145,f150,f158,f168,f181,f202,f217,f220,f227,f243,f261,f274,f288,f307,f314,f327,f355,f367])).
% 0.22/0.48  fof(f367,plain,(
% 0.22/0.48    spl8_31 | ~spl8_47 | ~spl8_53),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f366])).
% 0.22/0.48  fof(f366,plain,(
% 0.22/0.48    $false | (spl8_31 | ~spl8_47 | ~spl8_53)),
% 0.22/0.48    inference(subsumption_resolution,[],[f364,f198])).
% 0.22/0.48  fof(f198,plain,(
% 0.22/0.48    ~r2_hidden(sK6(sK3,sK2,sK4),sK0) | spl8_31),
% 0.22/0.48    inference(avatar_component_clause,[],[f197])).
% 0.22/0.48  fof(f197,plain,(
% 0.22/0.48    spl8_31 <=> r2_hidden(sK6(sK3,sK2,sK4),sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_31])])).
% 0.22/0.48  fof(f364,plain,(
% 0.22/0.48    r2_hidden(sK6(sK3,sK2,sK4),sK0) | (~spl8_47 | ~spl8_53)),
% 0.22/0.48    inference(resolution,[],[f354,f313])).
% 0.22/0.48  fof(f313,plain,(
% 0.22/0.48    r2_hidden(k4_tarski(sK6(sK3,sK2,sK4),sK4),sK3) | ~spl8_47),
% 0.22/0.48    inference(avatar_component_clause,[],[f312])).
% 0.22/0.48  fof(f312,plain,(
% 0.22/0.48    spl8_47 <=> r2_hidden(k4_tarski(sK6(sK3,sK2,sK4),sK4),sK3)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_47])])).
% 0.22/0.48  fof(f354,plain,(
% 0.22/0.48    ( ! [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),sK3) | r2_hidden(X2,sK0)) ) | ~spl8_53),
% 0.22/0.48    inference(avatar_component_clause,[],[f353])).
% 0.22/0.48  fof(f353,plain,(
% 0.22/0.48    spl8_53 <=> ! [X3,X2] : (~r2_hidden(k4_tarski(X2,X3),sK3) | r2_hidden(X2,sK0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_53])])).
% 0.22/0.48  fof(f355,plain,(
% 0.22/0.48    spl8_53 | ~spl8_10 | ~spl8_45),
% 0.22/0.48    inference(avatar_split_clause,[],[f330,f305,f91,f353])).
% 0.22/0.48  fof(f91,plain,(
% 0.22/0.48    spl8_10 <=> ! [X1,X3,X0,X2] : (r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 0.22/0.48  fof(f305,plain,(
% 0.22/0.48    spl8_45 <=> ! [X0] : (r2_hidden(X0,k2_zfmisc_1(sK0,sK1)) | ~r2_hidden(X0,sK3))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_45])])).
% 0.22/0.48  fof(f330,plain,(
% 0.22/0.48    ( ! [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),sK3) | r2_hidden(X2,sK0)) ) | (~spl8_10 | ~spl8_45)),
% 0.22/0.48    inference(resolution,[],[f306,f92])).
% 0.22/0.48  fof(f92,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) ) | ~spl8_10),
% 0.22/0.48    inference(avatar_component_clause,[],[f91])).
% 0.22/0.48  fof(f306,plain,(
% 0.22/0.48    ( ! [X0] : (r2_hidden(X0,k2_zfmisc_1(sK0,sK1)) | ~r2_hidden(X0,sK3)) ) | ~spl8_45),
% 0.22/0.48    inference(avatar_component_clause,[],[f305])).
% 0.22/0.48  fof(f327,plain,(
% 0.22/0.48    ~spl8_19 | ~spl8_1 | ~spl8_20 | ~spl8_21 | spl8_46),
% 0.22/0.48    inference(avatar_split_clause,[],[f318,f309,f143,f134,f55,f130])).
% 0.22/0.48  fof(f130,plain,(
% 0.22/0.48    spl8_19 <=> v1_relat_1(sK3)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).
% 0.22/0.48  fof(f55,plain,(
% 0.22/0.48    spl8_1 <=> v1_funct_1(sK3)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.22/0.48  fof(f134,plain,(
% 0.22/0.48    spl8_20 <=> ! [X1,X3,X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(sK6(X0,X1,X3),k1_relat_1(X0)) | ~r2_hidden(X3,k9_relat_1(X0,X1)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).
% 0.22/0.48  fof(f143,plain,(
% 0.22/0.48    spl8_21 <=> r2_hidden(sK4,k9_relat_1(sK3,sK2))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).
% 0.22/0.48  fof(f309,plain,(
% 0.22/0.48    spl8_46 <=> r2_hidden(sK6(sK3,sK2,sK4),k1_relat_1(sK3))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_46])])).
% 0.22/0.48  fof(f318,plain,(
% 0.22/0.48    ~v1_relat_1(sK3) | (~spl8_1 | ~spl8_20 | ~spl8_21 | spl8_46)),
% 0.22/0.48    inference(subsumption_resolution,[],[f317,f144])).
% 0.22/0.48  fof(f144,plain,(
% 0.22/0.48    r2_hidden(sK4,k9_relat_1(sK3,sK2)) | ~spl8_21),
% 0.22/0.48    inference(avatar_component_clause,[],[f143])).
% 0.22/0.48  fof(f317,plain,(
% 0.22/0.48    ~v1_relat_1(sK3) | ~r2_hidden(sK4,k9_relat_1(sK3,sK2)) | (~spl8_1 | ~spl8_20 | spl8_46)),
% 0.22/0.48    inference(subsumption_resolution,[],[f315,f56])).
% 0.22/0.48  fof(f56,plain,(
% 0.22/0.48    v1_funct_1(sK3) | ~spl8_1),
% 0.22/0.48    inference(avatar_component_clause,[],[f55])).
% 0.22/0.48  fof(f315,plain,(
% 0.22/0.48    ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~r2_hidden(sK4,k9_relat_1(sK3,sK2)) | (~spl8_20 | spl8_46)),
% 0.22/0.48    inference(resolution,[],[f310,f135])).
% 0.22/0.48  fof(f135,plain,(
% 0.22/0.48    ( ! [X0,X3,X1] : (r2_hidden(sK6(X0,X1,X3),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~r2_hidden(X3,k9_relat_1(X0,X1))) ) | ~spl8_20),
% 0.22/0.48    inference(avatar_component_clause,[],[f134])).
% 0.22/0.48  fof(f310,plain,(
% 0.22/0.48    ~r2_hidden(sK6(sK3,sK2,sK4),k1_relat_1(sK3)) | spl8_46),
% 0.22/0.48    inference(avatar_component_clause,[],[f309])).
% 0.22/0.48  fof(f314,plain,(
% 0.22/0.48    ~spl8_46 | spl8_47 | ~spl8_24 | ~spl8_28),
% 0.22/0.48    inference(avatar_split_clause,[],[f187,f179,f156,f312,f309])).
% 0.22/0.48  fof(f156,plain,(
% 0.22/0.48    spl8_24 <=> ! [X0] : (~r2_hidden(X0,k1_relat_1(sK3)) | r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).
% 0.22/0.48  fof(f179,plain,(
% 0.22/0.48    spl8_28 <=> sK4 = k1_funct_1(sK3,sK6(sK3,sK2,sK4))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).
% 0.22/0.48  fof(f187,plain,(
% 0.22/0.48    r2_hidden(k4_tarski(sK6(sK3,sK2,sK4),sK4),sK3) | ~r2_hidden(sK6(sK3,sK2,sK4),k1_relat_1(sK3)) | (~spl8_24 | ~spl8_28)),
% 0.22/0.48    inference(superposition,[],[f157,f180])).
% 0.22/0.48  fof(f180,plain,(
% 0.22/0.48    sK4 = k1_funct_1(sK3,sK6(sK3,sK2,sK4)) | ~spl8_28),
% 0.22/0.48    inference(avatar_component_clause,[],[f179])).
% 0.22/0.48  fof(f157,plain,(
% 0.22/0.48    ( ! [X0] : (r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3) | ~r2_hidden(X0,k1_relat_1(sK3))) ) | ~spl8_24),
% 0.22/0.48    inference(avatar_component_clause,[],[f156])).
% 0.22/0.48  fof(f307,plain,(
% 0.22/0.48    spl8_45 | ~spl8_3 | ~spl8_43),
% 0.22/0.48    inference(avatar_split_clause,[],[f297,f286,f63,f305])).
% 0.22/0.48  fof(f63,plain,(
% 0.22/0.48    spl8_3 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.22/0.48  fof(f286,plain,(
% 0.22/0.48    spl8_43 <=> ! [X1,X0] : (r2_hidden(X0,k2_zfmisc_1(sK0,sK1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~r2_hidden(X0,X1))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_43])])).
% 0.22/0.48  fof(f297,plain,(
% 0.22/0.48    ( ! [X0] : (r2_hidden(X0,k2_zfmisc_1(sK0,sK1)) | ~r2_hidden(X0,sK3)) ) | (~spl8_3 | ~spl8_43)),
% 0.22/0.48    inference(resolution,[],[f287,f64])).
% 0.22/0.48  fof(f64,plain,(
% 0.22/0.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl8_3),
% 0.22/0.48    inference(avatar_component_clause,[],[f63])).
% 0.22/0.48  fof(f287,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | r2_hidden(X0,k2_zfmisc_1(sK0,sK1)) | ~r2_hidden(X0,X1)) ) | ~spl8_43),
% 0.22/0.48    inference(avatar_component_clause,[],[f286])).
% 0.22/0.48  fof(f288,plain,(
% 0.22/0.48    spl8_43 | ~spl8_9 | ~spl8_35),
% 0.22/0.48    inference(avatar_split_clause,[],[f275,f222,f87,f286])).
% 0.22/0.48  fof(f87,plain,(
% 0.22/0.48    spl8_9 <=> ! [X1,X0,X2] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.22/0.48  fof(f222,plain,(
% 0.22/0.48    spl8_35 <=> ! [X1] : (~m1_subset_1(X1,k2_zfmisc_1(sK0,sK1)) | r2_hidden(X1,k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_35])])).
% 0.22/0.48  fof(f275,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r2_hidden(X0,k2_zfmisc_1(sK0,sK1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~r2_hidden(X0,X1)) ) | (~spl8_9 | ~spl8_35)),
% 0.22/0.48    inference(resolution,[],[f223,f88])).
% 0.22/0.48  fof(f88,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) ) | ~spl8_9),
% 0.22/0.48    inference(avatar_component_clause,[],[f87])).
% 0.22/0.48  fof(f223,plain,(
% 0.22/0.48    ( ! [X1] : (~m1_subset_1(X1,k2_zfmisc_1(sK0,sK1)) | r2_hidden(X1,k2_zfmisc_1(sK0,sK1))) ) | ~spl8_35),
% 0.22/0.48    inference(avatar_component_clause,[],[f222])).
% 0.22/0.48  fof(f274,plain,(
% 0.22/0.48    ~spl8_21 | ~spl8_41),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f266])).
% 0.22/0.48  fof(f266,plain,(
% 0.22/0.48    $false | (~spl8_21 | ~spl8_41)),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f144,f260])).
% 0.22/0.48  fof(f260,plain,(
% 0.22/0.48    ( ! [X4,X3] : (~r2_hidden(X3,k9_relat_1(sK3,X4))) ) | ~spl8_41),
% 0.22/0.48    inference(avatar_component_clause,[],[f259])).
% 0.22/0.48  fof(f259,plain,(
% 0.22/0.48    spl8_41 <=> ! [X3,X4] : ~r2_hidden(X3,k9_relat_1(sK3,X4))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_41])])).
% 0.22/0.48  fof(f261,plain,(
% 0.22/0.48    spl8_41 | ~spl8_19 | ~spl8_1 | ~spl8_20 | ~spl8_39),
% 0.22/0.48    inference(avatar_split_clause,[],[f251,f241,f134,f55,f130,f259])).
% 0.22/0.48  fof(f241,plain,(
% 0.22/0.48    spl8_39 <=> ! [X0] : ~r2_hidden(X0,k1_relat_1(sK3))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_39])])).
% 0.22/0.48  fof(f251,plain,(
% 0.22/0.48    ( ! [X4,X3] : (~v1_relat_1(sK3) | ~r2_hidden(X3,k9_relat_1(sK3,X4))) ) | (~spl8_1 | ~spl8_20 | ~spl8_39)),
% 0.22/0.48    inference(subsumption_resolution,[],[f247,f56])).
% 0.22/0.48  fof(f247,plain,(
% 0.22/0.48    ( ! [X4,X3] : (~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~r2_hidden(X3,k9_relat_1(sK3,X4))) ) | (~spl8_20 | ~spl8_39)),
% 0.22/0.48    inference(resolution,[],[f242,f135])).
% 0.22/0.48  fof(f242,plain,(
% 0.22/0.48    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK3))) ) | ~spl8_39),
% 0.22/0.48    inference(avatar_component_clause,[],[f241])).
% 0.22/0.48  fof(f243,plain,(
% 0.22/0.48    spl8_39 | ~spl8_24 | ~spl8_36),
% 0.22/0.48    inference(avatar_split_clause,[],[f228,f225,f156,f241])).
% 0.22/0.48  fof(f225,plain,(
% 0.22/0.48    spl8_36 <=> ! [X0] : ~r2_hidden(X0,sK3)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_36])])).
% 0.22/0.48  fof(f228,plain,(
% 0.22/0.48    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK3))) ) | (~spl8_24 | ~spl8_36)),
% 0.22/0.48    inference(resolution,[],[f226,f157])).
% 0.22/0.48  fof(f226,plain,(
% 0.22/0.48    ( ! [X0] : (~r2_hidden(X0,sK3)) ) | ~spl8_36),
% 0.22/0.48    inference(avatar_component_clause,[],[f225])).
% 0.22/0.48  fof(f227,plain,(
% 0.22/0.48    spl8_35 | spl8_36 | ~spl8_3 | ~spl8_34),
% 0.22/0.48    inference(avatar_split_clause,[],[f218,f215,f63,f225,f222])).
% 0.22/0.48  fof(f215,plain,(
% 0.22/0.48    spl8_34 <=> ! [X1,X3,X0,X2] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,X1) | r2_hidden(X3,X1))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_34])])).
% 0.22/0.48  fof(f218,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r2_hidden(X0,sK3) | ~m1_subset_1(X1,k2_zfmisc_1(sK0,sK1)) | r2_hidden(X1,k2_zfmisc_1(sK0,sK1))) ) | (~spl8_3 | ~spl8_34)),
% 0.22/0.48    inference(resolution,[],[f216,f64])).
% 0.22/0.48  fof(f216,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,X1) | r2_hidden(X3,X1)) ) | ~spl8_34),
% 0.22/0.48    inference(avatar_component_clause,[],[f215])).
% 0.22/0.48  fof(f220,plain,(
% 0.22/0.48    ~spl8_19 | ~spl8_1 | ~spl8_16 | ~spl8_21 | spl8_32),
% 0.22/0.48    inference(avatar_split_clause,[],[f213,f200,f143,f118,f55,f130])).
% 0.22/0.48  fof(f118,plain,(
% 0.22/0.48    spl8_16 <=> ! [X1,X3,X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(sK6(X0,X1,X3),X1) | ~r2_hidden(X3,k9_relat_1(X0,X1)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).
% 0.22/0.48  fof(f200,plain,(
% 0.22/0.48    spl8_32 <=> r2_hidden(sK6(sK3,sK2,sK4),sK2)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).
% 0.22/0.48  fof(f213,plain,(
% 0.22/0.48    ~v1_relat_1(sK3) | (~spl8_1 | ~spl8_16 | ~spl8_21 | spl8_32)),
% 0.22/0.48    inference(subsumption_resolution,[],[f212,f144])).
% 0.22/0.48  fof(f212,plain,(
% 0.22/0.48    ~v1_relat_1(sK3) | ~r2_hidden(sK4,k9_relat_1(sK3,sK2)) | (~spl8_1 | ~spl8_16 | spl8_32)),
% 0.22/0.48    inference(subsumption_resolution,[],[f211,f56])).
% 0.22/0.48  fof(f211,plain,(
% 0.22/0.48    ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~r2_hidden(sK4,k9_relat_1(sK3,sK2)) | (~spl8_16 | spl8_32)),
% 0.22/0.48    inference(resolution,[],[f201,f119])).
% 0.22/0.48  fof(f119,plain,(
% 0.22/0.48    ( ! [X0,X3,X1] : (r2_hidden(sK6(X0,X1,X3),X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~r2_hidden(X3,k9_relat_1(X0,X1))) ) | ~spl8_16),
% 0.22/0.48    inference(avatar_component_clause,[],[f118])).
% 0.22/0.48  fof(f201,plain,(
% 0.22/0.48    ~r2_hidden(sK6(sK3,sK2,sK4),sK2) | spl8_32),
% 0.22/0.48    inference(avatar_component_clause,[],[f200])).
% 0.22/0.48  fof(f217,plain,(
% 0.22/0.48    spl8_34 | ~spl8_6 | ~spl8_8),
% 0.22/0.48    inference(avatar_split_clause,[],[f98,f83,f75,f215])).
% 0.22/0.48  fof(f75,plain,(
% 0.22/0.48    spl8_6 <=> ! [X1,X0] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.22/0.48  fof(f83,plain,(
% 0.22/0.48    spl8_8 <=> ! [X1,X0,X2] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.22/0.48  fof(f98,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,X1) | r2_hidden(X3,X1)) ) | (~spl8_6 | ~spl8_8)),
% 0.22/0.48    inference(resolution,[],[f84,f76])).
% 0.22/0.48  fof(f76,plain,(
% 0.22/0.48    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X0,X1) | r2_hidden(X0,X1)) ) | ~spl8_6),
% 0.22/0.48    inference(avatar_component_clause,[],[f75])).
% 0.22/0.48  fof(f84,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) ) | ~spl8_8),
% 0.22/0.48    inference(avatar_component_clause,[],[f83])).
% 0.22/0.48  fof(f202,plain,(
% 0.22/0.48    ~spl8_31 | ~spl8_32 | ~spl8_5 | ~spl8_28),
% 0.22/0.48    inference(avatar_split_clause,[],[f190,f179,f71,f200,f197])).
% 0.22/0.48  fof(f71,plain,(
% 0.22/0.48    spl8_5 <=> ! [X5] : (~r2_hidden(X5,sK0) | ~r2_hidden(X5,sK2) | sK4 != k1_funct_1(sK3,X5))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.22/0.48  fof(f190,plain,(
% 0.22/0.48    ~r2_hidden(sK6(sK3,sK2,sK4),sK2) | ~r2_hidden(sK6(sK3,sK2,sK4),sK0) | (~spl8_5 | ~spl8_28)),
% 0.22/0.48    inference(trivial_inequality_removal,[],[f188])).
% 0.22/0.48  fof(f188,plain,(
% 0.22/0.48    sK4 != sK4 | ~r2_hidden(sK6(sK3,sK2,sK4),sK2) | ~r2_hidden(sK6(sK3,sK2,sK4),sK0) | (~spl8_5 | ~spl8_28)),
% 0.22/0.48    inference(superposition,[],[f72,f180])).
% 0.22/0.48  fof(f72,plain,(
% 0.22/0.48    ( ! [X5] : (sK4 != k1_funct_1(sK3,X5) | ~r2_hidden(X5,sK2) | ~r2_hidden(X5,sK0)) ) | ~spl8_5),
% 0.22/0.48    inference(avatar_component_clause,[],[f71])).
% 0.22/0.48  fof(f181,plain,(
% 0.22/0.48    spl8_28 | ~spl8_21 | ~spl8_26),
% 0.22/0.48    inference(avatar_split_clause,[],[f174,f166,f143,f179])).
% 0.22/0.48  fof(f166,plain,(
% 0.22/0.48    spl8_26 <=> ! [X1,X0] : (k1_funct_1(sK3,sK6(sK3,X0,X1)) = X1 | ~r2_hidden(X1,k9_relat_1(sK3,X0)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).
% 0.22/0.48  fof(f174,plain,(
% 0.22/0.48    sK4 = k1_funct_1(sK3,sK6(sK3,sK2,sK4)) | (~spl8_21 | ~spl8_26)),
% 0.22/0.48    inference(resolution,[],[f167,f144])).
% 0.22/0.48  fof(f167,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r2_hidden(X1,k9_relat_1(sK3,X0)) | k1_funct_1(sK3,sK6(sK3,X0,X1)) = X1) ) | ~spl8_26),
% 0.22/0.48    inference(avatar_component_clause,[],[f166])).
% 0.22/0.48  fof(f168,plain,(
% 0.22/0.48    spl8_26 | ~spl8_19 | ~spl8_1 | ~spl8_22),
% 0.22/0.48    inference(avatar_split_clause,[],[f159,f148,f55,f130,f166])).
% 0.22/0.48  fof(f148,plain,(
% 0.22/0.48    spl8_22 <=> ! [X1,X3,X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_funct_1(X0,sK6(X0,X1,X3)) = X3 | ~r2_hidden(X3,k9_relat_1(X0,X1)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).
% 0.22/0.48  fof(f159,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~v1_relat_1(sK3) | k1_funct_1(sK3,sK6(sK3,X0,X1)) = X1 | ~r2_hidden(X1,k9_relat_1(sK3,X0))) ) | (~spl8_1 | ~spl8_22)),
% 0.22/0.48    inference(resolution,[],[f149,f56])).
% 0.22/0.48  fof(f149,plain,(
% 0.22/0.48    ( ! [X0,X3,X1] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_funct_1(X0,sK6(X0,X1,X3)) = X3 | ~r2_hidden(X3,k9_relat_1(X0,X1))) ) | ~spl8_22),
% 0.22/0.48    inference(avatar_component_clause,[],[f148])).
% 0.22/0.48  fof(f158,plain,(
% 0.22/0.48    spl8_24 | ~spl8_19 | ~spl8_1 | ~spl8_17),
% 0.22/0.48    inference(avatar_split_clause,[],[f146,f122,f55,f130,f156])).
% 0.22/0.48  fof(f122,plain,(
% 0.22/0.48    spl8_17 <=> ! [X0,X2] : (~v1_relat_1(X2) | ~v1_funct_1(X2) | ~r2_hidden(X0,k1_relat_1(X2)) | r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).
% 0.22/0.48  fof(f146,plain,(
% 0.22/0.48    ( ! [X0] : (~v1_relat_1(sK3) | ~r2_hidden(X0,k1_relat_1(sK3)) | r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3)) ) | (~spl8_1 | ~spl8_17)),
% 0.22/0.48    inference(resolution,[],[f123,f56])).
% 0.22/0.48  fof(f123,plain,(
% 0.22/0.48    ( ! [X2,X0] : (~v1_funct_1(X2) | ~v1_relat_1(X2) | ~r2_hidden(X0,k1_relat_1(X2)) | r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)) ) | ~spl8_17),
% 0.22/0.48    inference(avatar_component_clause,[],[f122])).
% 0.22/0.48  fof(f150,plain,(
% 0.22/0.48    spl8_22),
% 0.22/0.48    inference(avatar_split_clause,[],[f50,f148])).
% 0.22/0.48  fof(f50,plain,(
% 0.22/0.48    ( ! [X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_funct_1(X0,sK6(X0,X1,X3)) = X3 | ~r2_hidden(X3,k9_relat_1(X0,X1))) )),
% 0.22/0.48    inference(equality_resolution,[],[f35])).
% 0.22/0.48  fof(f35,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_funct_1(X0,sK6(X0,X1,X3)) = X3 | ~r2_hidden(X3,X2) | k9_relat_1(X0,X1) != X2) )),
% 0.22/0.48    inference(cnf_transformation,[],[f14])).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.48    inference(flattening,[],[f13])).
% 0.22/0.48  fof(f13,plain,(
% 0.22/0.48    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,axiom,(
% 0.22/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_funct_1)).
% 0.22/0.48  fof(f145,plain,(
% 0.22/0.48    spl8_21 | ~spl8_3 | ~spl8_4 | ~spl8_15),
% 0.22/0.48    inference(avatar_split_clause,[],[f141,f114,f67,f63,f143])).
% 0.22/0.48  fof(f67,plain,(
% 0.22/0.48    spl8_4 <=> r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.22/0.48  fof(f114,plain,(
% 0.22/0.48    spl8_15 <=> ! [X1,X3,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).
% 0.22/0.48  fof(f141,plain,(
% 0.22/0.48    r2_hidden(sK4,k9_relat_1(sK3,sK2)) | (~spl8_3 | ~spl8_4 | ~spl8_15)),
% 0.22/0.48    inference(subsumption_resolution,[],[f140,f64])).
% 0.22/0.48  fof(f140,plain,(
% 0.22/0.48    r2_hidden(sK4,k9_relat_1(sK3,sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (~spl8_4 | ~spl8_15)),
% 0.22/0.48    inference(superposition,[],[f68,f115])).
% 0.22/0.48  fof(f115,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl8_15),
% 0.22/0.48    inference(avatar_component_clause,[],[f114])).
% 0.22/0.48  fof(f68,plain,(
% 0.22/0.48    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) | ~spl8_4),
% 0.22/0.48    inference(avatar_component_clause,[],[f67])).
% 0.22/0.48  fof(f139,plain,(
% 0.22/0.48    ~spl8_3 | ~spl8_7 | spl8_19),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f137])).
% 0.22/0.48  fof(f137,plain,(
% 0.22/0.48    $false | (~spl8_3 | ~spl8_7 | spl8_19)),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f64,f131,f80])).
% 0.22/0.48  fof(f80,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl8_7),
% 0.22/0.48    inference(avatar_component_clause,[],[f79])).
% 0.22/0.48  fof(f79,plain,(
% 0.22/0.48    spl8_7 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.22/0.48  fof(f131,plain,(
% 0.22/0.48    ~v1_relat_1(sK3) | spl8_19),
% 0.22/0.48    inference(avatar_component_clause,[],[f130])).
% 0.22/0.48  fof(f136,plain,(
% 0.22/0.48    spl8_20),
% 0.22/0.48    inference(avatar_split_clause,[],[f52,f134])).
% 0.22/0.48  fof(f52,plain,(
% 0.22/0.48    ( ! [X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(sK6(X0,X1,X3),k1_relat_1(X0)) | ~r2_hidden(X3,k9_relat_1(X0,X1))) )),
% 0.22/0.48    inference(equality_resolution,[],[f33])).
% 0.22/0.48  fof(f33,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(sK6(X0,X1,X3),k1_relat_1(X0)) | ~r2_hidden(X3,X2) | k9_relat_1(X0,X1) != X2) )),
% 0.22/0.48    inference(cnf_transformation,[],[f14])).
% 0.22/0.48  fof(f124,plain,(
% 0.22/0.48    spl8_17),
% 0.22/0.48    inference(avatar_split_clause,[],[f53,f122])).
% 0.22/0.48  fof(f53,plain,(
% 0.22/0.48    ( ! [X2,X0] : (~v1_relat_1(X2) | ~v1_funct_1(X2) | ~r2_hidden(X0,k1_relat_1(X2)) | r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)) )),
% 0.22/0.48    inference(equality_resolution,[],[f41])).
% 0.22/0.48  fof(f41,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v1_funct_1(X2) | ~r2_hidden(X0,k1_relat_1(X2)) | k1_funct_1(X2,X0) != X1 | r2_hidden(k4_tarski(X0,X1),X2)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f19])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.22/0.49    inference(flattening,[],[f18])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.22/0.49    inference(ennf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).
% 0.22/0.49  fof(f120,plain,(
% 0.22/0.49    spl8_16),
% 0.22/0.49    inference(avatar_split_clause,[],[f51,f118])).
% 0.22/0.49  fof(f51,plain,(
% 0.22/0.49    ( ! [X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(sK6(X0,X1,X3),X1) | ~r2_hidden(X3,k9_relat_1(X0,X1))) )),
% 0.22/0.49    inference(equality_resolution,[],[f34])).
% 0.22/0.49  fof(f34,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(sK6(X0,X1,X3),X1) | ~r2_hidden(X3,X2) | k9_relat_1(X0,X1) != X2) )),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  fof(f116,plain,(
% 0.22/0.49    spl8_15),
% 0.22/0.49    inference(avatar_split_clause,[],[f44,f114])).
% 0.22/0.49  fof(f44,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f23])).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.49    inference(ennf_transformation,[],[f8])).
% 0.22/0.49  fof(f8,axiom,(
% 0.22/0.49    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.22/0.49  fof(f93,plain,(
% 0.22/0.49    spl8_10),
% 0.22/0.49    inference(avatar_split_clause,[],[f45,f91])).
% 0.22/0.49  fof(f45,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.22/0.49  fof(f89,plain,(
% 0.22/0.49    spl8_9),
% 0.22/0.49    inference(avatar_split_clause,[],[f42,f87])).
% 0.22/0.49  fof(f42,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f21])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.22/0.49    inference(flattening,[],[f20])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.22/0.49    inference(ennf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 0.22/0.49  fof(f85,plain,(
% 0.22/0.49    spl8_8),
% 0.22/0.49    inference(avatar_split_clause,[],[f43,f83])).
% 0.22/0.49  fof(f43,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f22])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 0.22/0.49  fof(f81,plain,(
% 0.22/0.49    spl8_7),
% 0.22/0.49    inference(avatar_split_clause,[],[f38,f79])).
% 0.22/0.49  fof(f38,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f17])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.49    inference(ennf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.49  fof(f77,plain,(
% 0.22/0.49    spl8_6),
% 0.22/0.49    inference(avatar_split_clause,[],[f37,f75])).
% 0.22/0.49  fof(f37,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.22/0.49    inference(flattening,[],[f15])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.22/0.49  fof(f73,plain,(
% 0.22/0.49    spl8_5),
% 0.22/0.49    inference(avatar_split_clause,[],[f24,f71])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    ( ! [X5] : (~r2_hidden(X5,sK0) | ~r2_hidden(X5,sK2) | sK4 != k1_funct_1(sK3,X5)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f12])).
% 0.22/0.49  fof(f12,plain,(
% 0.22/0.49    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.22/0.49    inference(flattening,[],[f11])).
% 0.22/0.49  fof(f11,plain,(
% 0.22/0.49    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.22/0.49    inference(ennf_transformation,[],[f10])).
% 0.22/0.49  fof(f10,negated_conjecture,(
% 0.22/0.49    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.22/0.49    inference(negated_conjecture,[],[f9])).
% 0.22/0.49  fof(f9,conjecture,(
% 0.22/0.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t115_funct_2)).
% 0.22/0.49  fof(f69,plain,(
% 0.22/0.49    spl8_4),
% 0.22/0.49    inference(avatar_split_clause,[],[f25,f67])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 0.22/0.49    inference(cnf_transformation,[],[f12])).
% 0.22/0.49  fof(f65,plain,(
% 0.22/0.49    spl8_3),
% 0.22/0.49    inference(avatar_split_clause,[],[f28,f63])).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.49    inference(cnf_transformation,[],[f12])).
% 0.22/0.49  fof(f57,plain,(
% 0.22/0.49    spl8_1),
% 0.22/0.49    inference(avatar_split_clause,[],[f26,f55])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    v1_funct_1(sK3)),
% 0.22/0.49    inference(cnf_transformation,[],[f12])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (8361)------------------------------
% 0.22/0.49  % (8361)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (8361)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (8361)Memory used [KB]: 10874
% 0.22/0.49  % (8361)Time elapsed: 0.061 s
% 0.22/0.49  % (8361)------------------------------
% 0.22/0.49  % (8361)------------------------------
% 0.22/0.49  % (8371)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.49  % (8351)Success in time 0.124 s
%------------------------------------------------------------------------------
