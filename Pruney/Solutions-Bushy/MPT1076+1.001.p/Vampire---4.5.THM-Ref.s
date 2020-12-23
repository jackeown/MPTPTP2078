%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1076+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:13 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :  196 ( 346 expanded)
%              Number of leaves         :   46 ( 148 expanded)
%              Depth                    :   11
%              Number of atoms          :  843 (1572 expanded)
%              Number of equality atoms :   96 ( 162 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f288,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f59,f63,f67,f71,f75,f79,f83,f87,f91,f95,f99,f106,f118,f127,f131,f143,f147,f151,f156,f160,f166,f174,f178,f185,f195,f202,f207,f219,f237,f245,f249,f254,f268,f280,f287])).

fof(f287,plain,
    ( ~ spl6_8
    | ~ spl6_32 ),
    inference(avatar_contradiction_clause,[],[f283])).

fof(f283,plain,
    ( $false
    | ~ spl6_8
    | ~ spl6_32 ),
    inference(unit_resulting_resolution,[],[f86,f198])).

fof(f198,plain,
    ( ! [X0] : ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
    | ~ spl6_32 ),
    inference(avatar_component_clause,[],[f197])).

fof(f197,plain,
    ( spl6_32
  <=> ! [X0] : ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f86,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl6_8
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f280,plain,
    ( spl6_3
    | ~ spl6_10
    | ~ spl6_36 ),
    inference(avatar_contradiction_clause,[],[f279])).

fof(f279,plain,
    ( $false
    | spl6_3
    | ~ spl6_10
    | ~ spl6_36 ),
    inference(subsumption_resolution,[],[f269,f94])).

fof(f94,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl6_10
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f269,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | spl6_3
    | ~ spl6_36 ),
    inference(backward_demodulation,[],[f66,f230])).

fof(f230,plain,
    ( o_0_0_xboole_0 = sK1
    | ~ spl6_36 ),
    inference(avatar_component_clause,[],[f229])).

fof(f229,plain,
    ( spl6_36
  <=> o_0_0_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).

fof(f66,plain,
    ( ~ v1_xboole_0(sK1)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl6_3
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f268,plain,
    ( ~ spl6_9
    | ~ spl6_23
    | spl6_40 ),
    inference(avatar_contradiction_clause,[],[f267])).

fof(f267,plain,
    ( $false
    | ~ spl6_9
    | ~ spl6_23
    | spl6_40 ),
    inference(subsumption_resolution,[],[f264,f90])).

fof(f90,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl6_9
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f264,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl6_23
    | spl6_40 ),
    inference(resolution,[],[f253,f150])).

fof(f150,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f149])).

fof(f149,plain,
    ( spl6_23
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f253,plain,
    ( ~ m1_subset_1(k2_relset_1(sK1,sK0,sK3),k1_zfmisc_1(sK0))
    | spl6_40 ),
    inference(avatar_component_clause,[],[f252])).

fof(f252,plain,
    ( spl6_40
  <=> m1_subset_1(k2_relset_1(sK1,sK0,sK3),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).

fof(f254,plain,
    ( ~ spl6_40
    | ~ spl6_15
    | spl6_39 ),
    inference(avatar_split_clause,[],[f250,f247,f116,f252])).

fof(f116,plain,
    ( spl6_15
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f247,plain,
    ( spl6_39
  <=> r1_tarski(k2_relset_1(sK1,sK0,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).

fof(f250,plain,
    ( ~ m1_subset_1(k2_relset_1(sK1,sK0,sK3),k1_zfmisc_1(sK0))
    | ~ spl6_15
    | spl6_39 ),
    inference(resolution,[],[f248,f117])).

fof(f117,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) )
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f116])).

fof(f248,plain,
    ( ~ r1_tarski(k2_relset_1(sK1,sK0,sK3),sK0)
    | spl6_39 ),
    inference(avatar_component_clause,[],[f247])).

fof(f249,plain,
    ( ~ spl6_39
    | ~ spl6_8
    | ~ spl6_22
    | ~ spl6_33
    | spl6_37 ),
    inference(avatar_split_clause,[],[f241,f232,f200,f145,f85,f247])).

fof(f145,plain,
    ( spl6_22
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f200,plain,
    ( spl6_33
  <=> sK0 = k1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).

fof(f232,plain,
    ( spl6_37
  <=> r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).

fof(f241,plain,
    ( ~ r1_tarski(k2_relset_1(sK1,sK0,sK3),sK0)
    | ~ spl6_8
    | ~ spl6_22
    | ~ spl6_33
    | spl6_37 ),
    inference(forward_demodulation,[],[f240,f201])).

fof(f201,plain,
    ( sK0 = k1_relat_1(sK4)
    | ~ spl6_33 ),
    inference(avatar_component_clause,[],[f200])).

fof(f240,plain,
    ( ~ r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relat_1(sK4))
    | ~ spl6_8
    | ~ spl6_22
    | spl6_37 ),
    inference(subsumption_resolution,[],[f239,f86])).

fof(f239,plain,
    ( ~ r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relat_1(sK4))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl6_22
    | spl6_37 ),
    inference(superposition,[],[f233,f146])).

fof(f146,plain,
    ( ! [X2,X0,X1] :
        ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f145])).

fof(f233,plain,
    ( ~ r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4))
    | spl6_37 ),
    inference(avatar_component_clause,[],[f232])).

fof(f245,plain,
    ( ~ spl6_5
    | ~ spl6_27
    | spl6_38 ),
    inference(avatar_contradiction_clause,[],[f244])).

fof(f244,plain,
    ( $false
    | ~ spl6_5
    | ~ spl6_27
    | spl6_38 ),
    inference(subsumption_resolution,[],[f243,f74])).

fof(f74,plain,
    ( m1_subset_1(sK5,sK1)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl6_5
  <=> m1_subset_1(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f243,plain,
    ( ~ m1_subset_1(sK5,sK1)
    | ~ spl6_27
    | spl6_38 ),
    inference(trivial_inequality_removal,[],[f242])).

fof(f242,plain,
    ( k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) != k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5))
    | ~ m1_subset_1(sK5,sK1)
    | ~ spl6_27
    | spl6_38 ),
    inference(superposition,[],[f236,f173])).

fof(f173,plain,
    ( ! [X0] :
        ( k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0)
        | ~ m1_subset_1(X0,sK1) )
    | ~ spl6_27 ),
    inference(avatar_component_clause,[],[f172])).

fof(f172,plain,
    ( spl6_27
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f236,plain,
    ( k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5))
    | spl6_38 ),
    inference(avatar_component_clause,[],[f235])).

fof(f235,plain,
    ( spl6_38
  <=> k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).

fof(f237,plain,
    ( spl6_36
    | ~ spl6_37
    | ~ spl6_38
    | ~ spl6_1
    | ~ spl6_2
    | spl6_4
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_31
    | spl6_35 ),
    inference(avatar_split_clause,[],[f227,f217,f193,f89,f85,f81,f73,f69,f61,f57,f235,f232,f229])).

fof(f57,plain,
    ( spl6_1
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f61,plain,
    ( spl6_2
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f69,plain,
    ( spl6_4
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f81,plain,
    ( spl6_7
  <=> v1_funct_2(sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f193,plain,
    ( spl6_31
  <=> ! [X1,X3,X5,X0,X2,X4] :
        ( o_0_0_xboole_0 = X1
        | v1_xboole_0(X2)
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,X1,X2)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ v1_funct_1(X4)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
        | ~ m1_subset_1(X5,X1)
        | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
        | k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).

fof(f217,plain,
    ( spl6_35
  <=> k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).

fof(f227,plain,
    ( k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5))
    | ~ r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4))
    | o_0_0_xboole_0 = sK1
    | ~ spl6_1
    | ~ spl6_2
    | spl6_4
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_31
    | spl6_35 ),
    inference(subsumption_resolution,[],[f226,f74])).

fof(f226,plain,
    ( k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5))
    | ~ m1_subset_1(sK5,sK1)
    | ~ r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4))
    | o_0_0_xboole_0 = sK1
    | ~ spl6_1
    | ~ spl6_2
    | spl6_4
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_31
    | spl6_35 ),
    inference(subsumption_resolution,[],[f225,f86])).

fof(f225,plain,
    ( k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ m1_subset_1(sK5,sK1)
    | ~ r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4))
    | o_0_0_xboole_0 = sK1
    | ~ spl6_1
    | ~ spl6_2
    | spl6_4
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_31
    | spl6_35 ),
    inference(subsumption_resolution,[],[f224,f58])).

fof(f58,plain,
    ( v1_funct_1(sK4)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f57])).

fof(f224,plain,
    ( k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ m1_subset_1(sK5,sK1)
    | ~ r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4))
    | o_0_0_xboole_0 = sK1
    | ~ spl6_2
    | spl6_4
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_31
    | spl6_35 ),
    inference(subsumption_resolution,[],[f223,f90])).

fof(f223,plain,
    ( k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ m1_subset_1(sK5,sK1)
    | ~ r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4))
    | o_0_0_xboole_0 = sK1
    | ~ spl6_2
    | spl6_4
    | ~ spl6_7
    | ~ spl6_31
    | spl6_35 ),
    inference(subsumption_resolution,[],[f222,f82])).

fof(f82,plain,
    ( v1_funct_2(sK3,sK1,sK0)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f81])).

fof(f222,plain,
    ( k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ m1_subset_1(sK5,sK1)
    | ~ r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4))
    | o_0_0_xboole_0 = sK1
    | ~ spl6_2
    | spl6_4
    | ~ spl6_31
    | spl6_35 ),
    inference(subsumption_resolution,[],[f221,f62])).

fof(f62,plain,
    ( v1_funct_1(sK3)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f61])).

fof(f221,plain,
    ( k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ m1_subset_1(sK5,sK1)
    | ~ r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4))
    | o_0_0_xboole_0 = sK1
    | spl6_4
    | ~ spl6_31
    | spl6_35 ),
    inference(subsumption_resolution,[],[f220,f70])).

fof(f70,plain,
    ( ~ v1_xboole_0(sK0)
    | spl6_4 ),
    inference(avatar_component_clause,[],[f69])).

fof(f220,plain,
    ( k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5))
    | v1_xboole_0(sK0)
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ m1_subset_1(sK5,sK1)
    | ~ r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4))
    | o_0_0_xboole_0 = sK1
    | ~ spl6_31
    | spl6_35 ),
    inference(superposition,[],[f218,f194])).

fof(f194,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5))
        | v1_xboole_0(X2)
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,X1,X2)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ v1_funct_1(X4)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
        | ~ m1_subset_1(X5,X1)
        | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
        | o_0_0_xboole_0 = X1 )
    | ~ spl6_31 ),
    inference(avatar_component_clause,[],[f193])).

fof(f218,plain,
    ( k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5)
    | spl6_35 ),
    inference(avatar_component_clause,[],[f217])).

fof(f219,plain,
    ( ~ spl6_35
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | spl6_12
    | ~ spl6_34 ),
    inference(avatar_split_clause,[],[f215,f205,f104,f89,f85,f81,f73,f65,f61,f57,f217])).

fof(f104,plain,
    ( spl6_12
  <=> k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f205,plain,
    ( spl6_34
  <=> ! [X1,X3,X5,X0,X2,X4] :
        ( ~ v1_funct_2(X0,X1,X2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ v1_funct_1(X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
        | ~ v1_funct_1(X0)
        | v1_xboole_0(X1)
        | ~ m1_subset_1(X5,X1)
        | k3_funct_2(X1,X4,k8_funct_2(X1,X2,X4,X0,X3),X5) = k1_funct_1(k8_funct_2(X1,X2,X4,X0,X3),X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f215,plain,
    ( k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | spl6_12
    | ~ spl6_34 ),
    inference(subsumption_resolution,[],[f214,f82])).

fof(f214,plain,
    ( k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_5
    | ~ spl6_8
    | ~ spl6_9
    | spl6_12
    | ~ spl6_34 ),
    inference(subsumption_resolution,[],[f213,f74])).

fof(f213,plain,
    ( k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5)
    | ~ m1_subset_1(sK5,sK1)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_8
    | ~ spl6_9
    | spl6_12
    | ~ spl6_34 ),
    inference(subsumption_resolution,[],[f212,f66])).

fof(f212,plain,
    ( k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5)
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(sK5,sK1)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_8
    | ~ spl6_9
    | spl6_12
    | ~ spl6_34 ),
    inference(subsumption_resolution,[],[f211,f62])).

fof(f211,plain,
    ( k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5)
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(sK5,sK1)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ spl6_1
    | ~ spl6_8
    | ~ spl6_9
    | spl6_12
    | ~ spl6_34 ),
    inference(subsumption_resolution,[],[f210,f86])).

fof(f210,plain,
    ( k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(sK5,sK1)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ spl6_1
    | ~ spl6_9
    | spl6_12
    | ~ spl6_34 ),
    inference(subsumption_resolution,[],[f209,f58])).

fof(f209,plain,
    ( k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(sK5,sK1)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ spl6_9
    | spl6_12
    | ~ spl6_34 ),
    inference(subsumption_resolution,[],[f208,f90])).

fof(f208,plain,
    ( k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(sK5,sK1)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | spl6_12
    | ~ spl6_34 ),
    inference(superposition,[],[f105,f206])).

fof(f206,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( k3_funct_2(X1,X4,k8_funct_2(X1,X2,X4,X0,X3),X5) = k1_funct_1(k8_funct_2(X1,X2,X4,X0,X3),X5)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ v1_funct_1(X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
        | ~ v1_funct_1(X0)
        | v1_xboole_0(X1)
        | ~ m1_subset_1(X5,X1)
        | ~ v1_funct_2(X0,X1,X2) )
    | ~ spl6_34 ),
    inference(avatar_component_clause,[],[f205])).

fof(f105,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5))
    | spl6_12 ),
    inference(avatar_component_clause,[],[f104])).

fof(f207,plain,
    ( spl6_34
    | ~ spl6_25
    | ~ spl6_26
    | ~ spl6_28 ),
    inference(avatar_split_clause,[],[f181,f176,f164,f158,f205])).

fof(f158,plain,
    ( spl6_25
  <=> ! [X1,X3,X0,X2] :
        ( v1_xboole_0(X0)
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,X0,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(X3,X0)
        | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f164,plain,
    ( spl6_26
  <=> ! [X1,X3,X0,X2,X4] :
        ( ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,X0,X1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X4)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f176,plain,
    ( spl6_28
  <=> ! [X1,X3,X0,X2,X4] :
        ( ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,X0,X1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X4)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f181,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( ~ v1_funct_2(X0,X1,X2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ v1_funct_1(X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
        | ~ v1_funct_1(X0)
        | v1_xboole_0(X1)
        | ~ m1_subset_1(X5,X1)
        | k3_funct_2(X1,X4,k8_funct_2(X1,X2,X4,X0,X3),X5) = k1_funct_1(k8_funct_2(X1,X2,X4,X0,X3),X5) )
    | ~ spl6_25
    | ~ spl6_26
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f180,f54])).

fof(f54,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2)
        & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2)
        & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X4)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2)
        & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_funct_2)).

fof(f180,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( ~ v1_funct_2(X0,X1,X2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ v1_funct_1(X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
        | ~ v1_funct_1(X0)
        | v1_xboole_0(X1)
        | ~ m1_subset_1(k8_funct_2(X1,X2,X4,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))
        | ~ m1_subset_1(X5,X1)
        | k3_funct_2(X1,X4,k8_funct_2(X1,X2,X4,X0,X3),X5) = k1_funct_1(k8_funct_2(X1,X2,X4,X0,X3),X5) )
    | ~ spl6_25
    | ~ spl6_26
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f179,f165])).

fof(f165,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4))
        | ~ v1_funct_2(X3,X0,X1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X4)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ v1_funct_1(X3) )
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f164])).

fof(f179,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( ~ v1_funct_2(X0,X1,X2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ v1_funct_1(X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_1(k8_funct_2(X1,X2,X4,X0,X3))
        | v1_xboole_0(X1)
        | ~ m1_subset_1(k8_funct_2(X1,X2,X4,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))
        | ~ m1_subset_1(X5,X1)
        | k3_funct_2(X1,X4,k8_funct_2(X1,X2,X4,X0,X3),X5) = k1_funct_1(k8_funct_2(X1,X2,X4,X0,X3),X5) )
    | ~ spl6_25
    | ~ spl6_28 ),
    inference(resolution,[],[f177,f159])).

fof(f159,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2)
        | v1_xboole_0(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(X3,X0)
        | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) )
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f158])).

fof(f177,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2)
        | ~ v1_funct_2(X3,X0,X1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X4)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ v1_funct_1(X3) )
    | ~ spl6_28 ),
    inference(avatar_component_clause,[],[f176])).

fof(f202,plain,
    ( spl6_32
    | spl6_33
    | ~ spl6_6
    | ~ spl6_29 ),
    inference(avatar_split_clause,[],[f190,f183,f77,f200,f197])).

fof(f77,plain,
    ( spl6_6
  <=> v1_partfun1(sK4,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f183,plain,
    ( spl6_29
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | k1_relat_1(X0) = X1
        | ~ v1_partfun1(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f190,plain,
    ( ! [X0] :
        ( sK0 = k1_relat_1(sK4)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) )
    | ~ spl6_6
    | ~ spl6_29 ),
    inference(resolution,[],[f184,f78])).

fof(f78,plain,
    ( v1_partfun1(sK4,sK0)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f77])).

fof(f184,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_partfun1(X0,X1)
        | k1_relat_1(X0) = X1
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
    | ~ spl6_29 ),
    inference(avatar_component_clause,[],[f183])).

fof(f195,plain,
    ( spl6_31
    | ~ spl6_10
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f102,f97,f93,f193])).

fof(f97,plain,
    ( spl6_11
  <=> ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f102,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( o_0_0_xboole_0 = X1
        | v1_xboole_0(X2)
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,X1,X2)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ v1_funct_1(X4)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
        | ~ m1_subset_1(X5,X1)
        | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
        | k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) )
    | ~ spl6_10
    | ~ spl6_11 ),
    inference(backward_demodulation,[],[f45,f100])).

fof(f100,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl6_10
    | ~ spl6_11 ),
    inference(resolution,[],[f98,f94])).

fof(f98,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 )
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f97])).

fof(f45,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_xboole_0(X2)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ m1_subset_1(X5,X1)
      | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
      | k1_xboole_0 = X1
      | k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ! [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                  | k1_xboole_0 = X1
                  | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  | ~ m1_subset_1(X5,X1) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              | ~ v1_funct_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X3,X1,X2)
          | ~ v1_funct_1(X3) )
      | v1_xboole_0(X2) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ! [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                  | k1_xboole_0 = X1
                  | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  | ~ m1_subset_1(X5,X1) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              | ~ v1_funct_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X3,X1,X2)
          | ~ v1_funct_1(X3) )
      | v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X3,X1,X2)
            & v1_funct_1(X3) )
         => ! [X4] :
              ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                & v1_funct_1(X4) )
             => ! [X5] :
                  ( m1_subset_1(X5,X1)
                 => ( r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                   => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                      | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t186_funct_2)).

fof(f185,plain,
    ( spl6_29
    | ~ spl6_18
    | ~ spl6_24 ),
    inference(avatar_split_clause,[],[f162,f154,f129,f183])).

fof(f129,plain,
    ( spl6_18
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v4_relat_1(X2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f154,plain,
    ( spl6_24
  <=> ! [X1,X3,X0,X2] :
        ( ~ v4_relat_1(X0,X1)
        | k1_relat_1(X0) = X1
        | ~ v1_partfun1(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f162,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | k1_relat_1(X0) = X1
        | ~ v1_partfun1(X0,X1) )
    | ~ spl6_18
    | ~ spl6_24 ),
    inference(condensation,[],[f161])).

fof(f161,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( k1_relat_1(X0) = X1
        | ~ v1_partfun1(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X4))) )
    | ~ spl6_18
    | ~ spl6_24 ),
    inference(resolution,[],[f155,f130])).

fof(f130,plain,
    ( ! [X2,X0,X1] :
        ( v4_relat_1(X2,X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f129])).

fof(f155,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ v4_relat_1(X0,X1)
        | k1_relat_1(X0) = X1
        | ~ v1_partfun1(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) )
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f154])).

fof(f178,plain,(
    spl6_28 ),
    inference(avatar_split_clause,[],[f53,f176])).

fof(f53,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f174,plain,
    ( spl6_27
    | ~ spl6_2
    | spl6_3
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_25 ),
    inference(avatar_split_clause,[],[f170,f158,f89,f81,f65,f61,f172])).

fof(f170,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0) )
    | ~ spl6_2
    | spl6_3
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_25 ),
    inference(subsumption_resolution,[],[f169,f90])).

fof(f169,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        | ~ m1_subset_1(X0,sK1)
        | k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0) )
    | ~ spl6_2
    | spl6_3
    | ~ spl6_7
    | ~ spl6_25 ),
    inference(subsumption_resolution,[],[f168,f66])).

fof(f168,plain,
    ( ! [X0] :
        ( v1_xboole_0(sK1)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        | ~ m1_subset_1(X0,sK1)
        | k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0) )
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_25 ),
    inference(subsumption_resolution,[],[f167,f62])).

fof(f167,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK3)
        | v1_xboole_0(sK1)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        | ~ m1_subset_1(X0,sK1)
        | k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0) )
    | ~ spl6_7
    | ~ spl6_25 ),
    inference(resolution,[],[f159,f82])).

fof(f166,plain,(
    spl6_26 ),
    inference(avatar_split_clause,[],[f52,f164])).

fof(f52,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f160,plain,(
    spl6_25 ),
    inference(avatar_split_clause,[],[f51,f158])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_xboole_0(X0)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,X0)
      | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(f156,plain,
    ( spl6_24
    | ~ spl6_17
    | ~ spl6_21 ),
    inference(avatar_split_clause,[],[f152,f141,f125,f154])).

fof(f125,plain,
    ( spl6_17
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f141,plain,
    ( spl6_21
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X1)
        | ~ v4_relat_1(X1,X0)
        | k1_relat_1(X1) = X0
        | ~ v1_partfun1(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f152,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ v4_relat_1(X0,X1)
        | k1_relat_1(X0) = X1
        | ~ v1_partfun1(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) )
    | ~ spl6_17
    | ~ spl6_21 ),
    inference(resolution,[],[f142,f126])).

fof(f126,plain,
    ( ! [X2,X0,X1] :
        ( v1_relat_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f125])).

fof(f142,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | ~ v4_relat_1(X1,X0)
        | k1_relat_1(X1) = X0
        | ~ v1_partfun1(X1,X0) )
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f141])).

fof(f151,plain,(
    spl6_23 ),
    inference(avatar_split_clause,[],[f48,f149])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(f147,plain,(
    spl6_22 ),
    inference(avatar_split_clause,[],[f47,f145])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f143,plain,(
    spl6_21 ),
    inference(avatar_split_clause,[],[f42,f141])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0)
      | k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

fof(f131,plain,(
    spl6_18 ),
    inference(avatar_split_clause,[],[f49,f129])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f127,plain,(
    spl6_17 ),
    inference(avatar_split_clause,[],[f46,f125])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f118,plain,(
    spl6_15 ),
    inference(avatar_split_clause,[],[f44,f116])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f106,plain,(
    ~ spl6_12 ),
    inference(avatar_split_clause,[],[f31,f104])).

fof(f31,plain,(
    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))
                      & v1_partfun1(X4,X0)
                      & m1_subset_1(X5,X1) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))
                      & v1_partfun1(X4,X0)
                      & m1_subset_1(X5,X1) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2,X3] :
                ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
                  & v1_funct_2(X3,X1,X0)
                  & v1_funct_1(X3) )
               => ! [X4] :
                    ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                      & v1_funct_1(X4) )
                   => ! [X5] :
                        ( m1_subset_1(X5,X1)
                       => ( v1_partfun1(X4,X0)
                         => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2,X3] :
              ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
                & v1_funct_2(X3,X1,X0)
                & v1_funct_1(X3) )
             => ! [X4] :
                  ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                    & v1_funct_1(X4) )
                 => ! [X5] :
                      ( m1_subset_1(X5,X1)
                     => ( v1_partfun1(X4,X0)
                       => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t193_funct_2)).

fof(f99,plain,(
    spl6_11 ),
    inference(avatar_split_clause,[],[f40,f97])).

fof(f40,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

fof(f95,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f39,f93])).

fof(f39,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(f91,plain,(
    spl6_9 ),
    inference(avatar_split_clause,[],[f36,f89])).

fof(f36,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f15])).

fof(f87,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f33,f85])).

fof(f33,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f15])).

fof(f83,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f35,f81])).

fof(f35,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f79,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f30,f77])).

fof(f30,plain,(
    v1_partfun1(sK4,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f75,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f29,f73])).

fof(f29,plain,(
    m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f71,plain,(
    ~ spl6_4 ),
    inference(avatar_split_clause,[],[f38,f69])).

fof(f38,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f15])).

% (1207)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
fof(f67,plain,(
    ~ spl6_3 ),
    inference(avatar_split_clause,[],[f37,f65])).

fof(f37,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f63,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f34,f61])).

fof(f34,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f15])).

fof(f59,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f32,f57])).

fof(f32,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f15])).

%------------------------------------------------------------------------------
