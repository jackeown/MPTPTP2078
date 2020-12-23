%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:32 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  236 ( 411 expanded)
%              Number of leaves         :   59 ( 186 expanded)
%              Depth                    :    7
%              Number of atoms          :  831 (1475 expanded)
%              Number of equality atoms :   44 (  83 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f386,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f72,f76,f80,f84,f88,f92,f96,f100,f110,f114,f118,f122,f126,f134,f138,f142,f146,f152,f156,f162,f166,f170,f175,f180,f192,f205,f209,f213,f231,f235,f247,f251,f259,f266,f276,f305,f314,f328,f333,f338,f348,f362,f372,f379,f385])).

fof(f385,plain,
    ( ~ spl5_3
    | ~ spl5_52
    | spl5_53 ),
    inference(avatar_contradiction_clause,[],[f384])).

fof(f384,plain,
    ( $false
    | ~ spl5_3
    | ~ spl5_52
    | spl5_53 ),
    inference(subsumption_resolution,[],[f382,f79])).

fof(f79,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl5_3
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f382,plain,
    ( ~ r1_tarski(sK1,sK0)
    | ~ spl5_52
    | spl5_53 ),
    inference(resolution,[],[f368,f361])).

fof(f361,plain,
    ( ! [X0] :
        ( m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(X0,sK3)))
        | ~ r1_tarski(X0,sK0) )
    | ~ spl5_52 ),
    inference(avatar_component_clause,[],[f360])).

fof(f360,plain,
    ( spl5_52
  <=> ! [X0] :
        ( m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(X0,sK3)))
        | ~ r1_tarski(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_52])])).

fof(f368,plain,
    ( ~ m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | spl5_53 ),
    inference(avatar_component_clause,[],[f367])).

fof(f367,plain,
    ( spl5_53
  <=> m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_53])])).

fof(f379,plain,
    ( ~ spl5_3
    | ~ spl5_41
    | spl5_54 ),
    inference(avatar_contradiction_clause,[],[f378])).

fof(f378,plain,
    ( $false
    | ~ spl5_3
    | ~ spl5_41
    | spl5_54 ),
    inference(subsumption_resolution,[],[f374,f79])).

fof(f374,plain,
    ( ~ r1_tarski(sK1,sK0)
    | ~ spl5_41
    | spl5_54 ),
    inference(resolution,[],[f371,f265])).

fof(f265,plain,
    ( ! [X0] :
        ( v1_funct_2(k7_relat_1(sK4,X0),X0,sK3)
        | ~ r1_tarski(X0,sK0) )
    | ~ spl5_41 ),
    inference(avatar_component_clause,[],[f264])).

fof(f264,plain,
    ( spl5_41
  <=> ! [X0] :
        ( v1_funct_2(k7_relat_1(sK4,X0),X0,sK3)
        | ~ r1_tarski(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).

fof(f371,plain,
    ( ~ v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK3)
    | spl5_54 ),
    inference(avatar_component_clause,[],[f370])).

fof(f370,plain,
    ( spl5_54
  <=> v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_54])])).

fof(f372,plain,
    ( ~ spl5_31
    | ~ spl5_53
    | ~ spl5_54
    | spl5_30
    | ~ spl5_35
    | ~ spl5_49 ),
    inference(avatar_split_clause,[],[f349,f336,f229,f203,f370,f367,f207])).

fof(f207,plain,
    ( spl5_31
  <=> m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).

fof(f203,plain,
    ( spl5_30
  <=> v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f229,plain,
    ( spl5_35
  <=> ! [X1] : v1_funct_1(k7_relat_1(sK4,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).

fof(f336,plain,
    ( spl5_49
  <=> ! [X1,X0,X2] :
        ( ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,X1,sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK3)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | v1_funct_2(X0,X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_49])])).

fof(f349,plain,
    ( ~ v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK3)
    | ~ m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | spl5_30
    | ~ spl5_35
    | ~ spl5_49 ),
    inference(subsumption_resolution,[],[f339,f230])).

fof(f230,plain,
    ( ! [X1] : v1_funct_1(k7_relat_1(sK4,X1))
    | ~ spl5_35 ),
    inference(avatar_component_clause,[],[f229])).

fof(f339,plain,
    ( ~ v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK3)
    | ~ m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | ~ m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(k7_relat_1(sK4,sK1))
    | spl5_30
    | ~ spl5_49 ),
    inference(resolution,[],[f337,f204])).

fof(f204,plain,
    ( ~ v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2)
    | spl5_30 ),
    inference(avatar_component_clause,[],[f203])).

fof(f337,plain,
    ( ! [X2,X0,X1] :
        ( v1_funct_2(X0,X1,X2)
        | ~ v1_funct_2(X0,X1,sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK3)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ v1_funct_1(X0) )
    | ~ spl5_49 ),
    inference(avatar_component_clause,[],[f336])).

fof(f362,plain,
    ( spl5_40
    | spl5_52
    | ~ spl5_1
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_32
    | ~ spl5_38 ),
    inference(avatar_split_clause,[],[f255,f249,f211,f86,f82,f70,f360,f261])).

fof(f261,plain,
    ( spl5_40
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).

fof(f70,plain,
    ( spl5_1
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f82,plain,
    ( spl5_4
  <=> v1_funct_2(sK4,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f86,plain,
    ( spl5_5
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f211,plain,
    ( spl5_32
  <=> ! [X0] : k2_partfun1(sK0,sK3,sK4,X0) = k7_relat_1(sK4,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f249,plain,
    ( spl5_38
  <=> ! [X1,X3,X0,X2] :
        ( ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,X0,X1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ r1_tarski(X2,X0)
        | k1_xboole_0 = X1
        | m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).

fof(f255,plain,
    ( ! [X0] :
        ( m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(X0,sK3)))
        | ~ r1_tarski(X0,sK0)
        | k1_xboole_0 = sK3 )
    | ~ spl5_1
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_32
    | ~ spl5_38 ),
    inference(subsumption_resolution,[],[f254,f71])).

fof(f71,plain,
    ( v1_funct_1(sK4)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f70])).

fof(f254,plain,
    ( ! [X0] :
        ( m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(X0,sK3)))
        | ~ r1_tarski(X0,sK0)
        | k1_xboole_0 = sK3
        | ~ v1_funct_1(sK4) )
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_32
    | ~ spl5_38 ),
    inference(subsumption_resolution,[],[f253,f87])).

fof(f87,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f86])).

fof(f253,plain,
    ( ! [X0] :
        ( m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(X0,sK3)))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
        | ~ r1_tarski(X0,sK0)
        | k1_xboole_0 = sK3
        | ~ v1_funct_1(sK4) )
    | ~ spl5_4
    | ~ spl5_32
    | ~ spl5_38 ),
    inference(subsumption_resolution,[],[f252,f83])).

fof(f83,plain,
    ( v1_funct_2(sK4,sK0,sK3)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f82])).

fof(f252,plain,
    ( ! [X0] :
        ( m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(X0,sK3)))
        | ~ v1_funct_2(sK4,sK0,sK3)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
        | ~ r1_tarski(X0,sK0)
        | k1_xboole_0 = sK3
        | ~ v1_funct_1(sK4) )
    | ~ spl5_32
    | ~ spl5_38 ),
    inference(superposition,[],[f250,f212])).

fof(f212,plain,
    ( ! [X0] : k2_partfun1(sK0,sK3,sK4,X0) = k7_relat_1(sK4,X0)
    | ~ spl5_32 ),
    inference(avatar_component_clause,[],[f211])).

fof(f250,plain,
    ( ! [X2,X0,X3,X1] :
        ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ v1_funct_2(X3,X0,X1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ r1_tarski(X2,X0)
        | k1_xboole_0 = X1
        | ~ v1_funct_1(X3) )
    | ~ spl5_38 ),
    inference(avatar_component_clause,[],[f249])).

fof(f348,plain,
    ( ~ spl5_44
    | ~ spl5_15
    | ~ spl5_24
    | spl5_48 ),
    inference(avatar_split_clause,[],[f343,f326,f168,f124,f300])).

fof(f300,plain,
    ( spl5_44
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_44])])).

fof(f124,plain,
    ( spl5_15
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X1)
        | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f168,plain,
    ( spl5_24
  <=> r1_tarski(k9_relat_1(sK4,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f326,plain,
    ( spl5_48
  <=> r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_48])])).

fof(f343,plain,
    ( ~ v1_relat_1(sK4)
    | ~ spl5_15
    | ~ spl5_24
    | spl5_48 ),
    inference(subsumption_resolution,[],[f342,f169])).

fof(f169,plain,
    ( r1_tarski(k9_relat_1(sK4,sK1),sK2)
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f168])).

fof(f342,plain,
    ( ~ r1_tarski(k9_relat_1(sK4,sK1),sK2)
    | ~ v1_relat_1(sK4)
    | ~ spl5_15
    | spl5_48 ),
    inference(superposition,[],[f327,f125])).

fof(f125,plain,
    ( ! [X0,X1] :
        ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
        | ~ v1_relat_1(X1) )
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f124])).

fof(f327,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),sK2)
    | spl5_48 ),
    inference(avatar_component_clause,[],[f326])).

fof(f338,plain,
    ( spl5_49
    | ~ spl5_19
    | ~ spl5_26 ),
    inference(avatar_split_clause,[],[f184,f178,f140,f336])).

fof(f140,plain,
    ( spl5_19
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X2)
        | ~ v1_partfun1(X2,X0)
        | v1_funct_2(X2,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f178,plain,
    ( spl5_26
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK3)))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,X1,sK3)
        | v1_partfun1(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f184,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,X1,sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK3)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | v1_funct_2(X0,X1,X2) )
    | ~ spl5_19
    | ~ spl5_26 ),
    inference(duplicate_literal_removal,[],[f183])).

fof(f183,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,X1,sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK3)))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | v1_funct_2(X0,X1,X2) )
    | ~ spl5_19
    | ~ spl5_26 ),
    inference(resolution,[],[f179,f141])).

fof(f141,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_partfun1(X2,X0)
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_funct_2(X2,X0,X1) )
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f140])).

fof(f179,plain,
    ( ! [X0,X1] :
        ( v1_partfun1(X0,X1)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,X1,sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK3))) )
    | ~ spl5_26 ),
    inference(avatar_component_clause,[],[f178])).

fof(f333,plain,
    ( ~ spl5_14
    | ~ spl5_37
    | spl5_47 ),
    inference(avatar_contradiction_clause,[],[f329])).

fof(f329,plain,
    ( $false
    | ~ spl5_14
    | ~ spl5_37
    | spl5_47 ),
    inference(unit_resulting_resolution,[],[f246,f324,f121])).

fof(f121,plain,
    ( ! [X2,X0,X1] :
        ( v1_relat_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl5_14
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f324,plain,
    ( ~ v1_relat_1(k7_relat_1(sK4,sK1))
    | spl5_47 ),
    inference(avatar_component_clause,[],[f323])).

fof(f323,plain,
    ( spl5_47
  <=> v1_relat_1(k7_relat_1(sK4,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_47])])).

fof(f246,plain,
    ( ! [X0] : m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
    | ~ spl5_37 ),
    inference(avatar_component_clause,[],[f245])).

fof(f245,plain,
    ( spl5_37
  <=> ! [X0] : m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).

fof(f328,plain,
    ( ~ spl5_47
    | ~ spl5_48
    | ~ spl5_18
    | ~ spl5_35
    | ~ spl5_45 ),
    inference(avatar_split_clause,[],[f317,f303,f229,f136,f326,f323])).

fof(f136,plain,
    ( spl5_18
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X1)
        | ~ v1_funct_1(X1)
        | ~ r1_tarski(k2_relat_1(X1),X0)
        | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f303,plain,
    ( spl5_45
  <=> ! [X0] : ~ m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_45])])).

fof(f317,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),sK2)
    | ~ v1_relat_1(k7_relat_1(sK4,sK1))
    | ~ spl5_18
    | ~ spl5_35
    | ~ spl5_45 ),
    inference(subsumption_resolution,[],[f316,f230])).

fof(f316,plain,
    ( ~ v1_funct_1(k7_relat_1(sK4,sK1))
    | ~ r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),sK2)
    | ~ v1_relat_1(k7_relat_1(sK4,sK1))
    | ~ spl5_18
    | ~ spl5_45 ),
    inference(resolution,[],[f304,f137])).

fof(f137,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        | ~ v1_funct_1(X1)
        | ~ r1_tarski(k2_relat_1(X1),X0)
        | ~ v1_relat_1(X1) )
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f136])).

fof(f304,plain,
    ( ! [X0] : ~ m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
    | ~ spl5_45 ),
    inference(avatar_component_clause,[],[f303])).

fof(f314,plain,
    ( ~ spl5_5
    | ~ spl5_8
    | ~ spl5_12
    | spl5_44 ),
    inference(avatar_contradiction_clause,[],[f310])).

fof(f310,plain,
    ( $false
    | ~ spl5_5
    | ~ spl5_8
    | ~ spl5_12
    | spl5_44 ),
    inference(unit_resulting_resolution,[],[f99,f87,f301,f113])).

fof(f113,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl5_12
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f301,plain,
    ( ~ v1_relat_1(sK4)
    | spl5_44 ),
    inference(avatar_component_clause,[],[f300])).

fof(f99,plain,
    ( ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl5_8
  <=> ! [X1,X0] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f305,plain,
    ( ~ spl5_44
    | spl5_45
    | spl5_31
    | ~ spl5_39 ),
    inference(avatar_split_clause,[],[f284,f257,f207,f303,f300])).

fof(f257,plain,
    ( spl5_39
  <=> ! [X1,X3,X0,X2] :
        ( ~ m1_subset_1(k7_relat_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | m1_subset_1(k7_relat_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).

fof(f284,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
        | ~ v1_relat_1(sK4) )
    | spl5_31
    | ~ spl5_39 ),
    inference(resolution,[],[f258,f208])).

fof(f208,plain,
    ( ~ m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | spl5_31 ),
    inference(avatar_component_clause,[],[f207])).

fof(f258,plain,
    ( ! [X2,X0,X3,X1] :
        ( m1_subset_1(k7_relat_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
        | ~ m1_subset_1(k7_relat_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | ~ v1_relat_1(X0) )
    | ~ spl5_39 ),
    inference(avatar_component_clause,[],[f257])).

fof(f276,plain,
    ( spl5_2
    | ~ spl5_6
    | ~ spl5_40 ),
    inference(avatar_contradiction_clause,[],[f275])).

fof(f275,plain,
    ( $false
    | spl5_2
    | ~ spl5_6
    | ~ spl5_40 ),
    inference(subsumption_resolution,[],[f267,f91])).

fof(f91,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl5_6
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f267,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl5_2
    | ~ spl5_40 ),
    inference(backward_demodulation,[],[f75,f262])).

fof(f262,plain,
    ( k1_xboole_0 = sK3
    | ~ spl5_40 ),
    inference(avatar_component_clause,[],[f261])).

fof(f75,plain,
    ( ~ v1_xboole_0(sK3)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl5_2
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f266,plain,
    ( spl5_40
    | spl5_41
    | ~ spl5_1
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_32
    | ~ spl5_36 ),
    inference(avatar_split_clause,[],[f243,f233,f211,f86,f82,f70,f264,f261])).

fof(f233,plain,
    ( spl5_36
  <=> ! [X1,X3,X0,X2] :
        ( ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,X0,X1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ r1_tarski(X2,X0)
        | k1_xboole_0 = X1
        | v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).

fof(f243,plain,
    ( ! [X0] :
        ( v1_funct_2(k7_relat_1(sK4,X0),X0,sK3)
        | ~ r1_tarski(X0,sK0)
        | k1_xboole_0 = sK3 )
    | ~ spl5_1
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_32
    | ~ spl5_36 ),
    inference(subsumption_resolution,[],[f242,f71])).

fof(f242,plain,
    ( ! [X0] :
        ( v1_funct_2(k7_relat_1(sK4,X0),X0,sK3)
        | ~ r1_tarski(X0,sK0)
        | k1_xboole_0 = sK3
        | ~ v1_funct_1(sK4) )
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_32
    | ~ spl5_36 ),
    inference(subsumption_resolution,[],[f241,f87])).

fof(f241,plain,
    ( ! [X0] :
        ( v1_funct_2(k7_relat_1(sK4,X0),X0,sK3)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
        | ~ r1_tarski(X0,sK0)
        | k1_xboole_0 = sK3
        | ~ v1_funct_1(sK4) )
    | ~ spl5_4
    | ~ spl5_32
    | ~ spl5_36 ),
    inference(subsumption_resolution,[],[f238,f83])).

fof(f238,plain,
    ( ! [X0] :
        ( v1_funct_2(k7_relat_1(sK4,X0),X0,sK3)
        | ~ v1_funct_2(sK4,sK0,sK3)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
        | ~ r1_tarski(X0,sK0)
        | k1_xboole_0 = sK3
        | ~ v1_funct_1(sK4) )
    | ~ spl5_32
    | ~ spl5_36 ),
    inference(superposition,[],[f234,f212])).

fof(f234,plain,
    ( ! [X2,X0,X3,X1] :
        ( v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        | ~ v1_funct_2(X3,X0,X1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ r1_tarski(X2,X0)
        | k1_xboole_0 = X1
        | ~ v1_funct_1(X3) )
    | ~ spl5_36 ),
    inference(avatar_component_clause,[],[f233])).

fof(f259,plain,
    ( spl5_39
    | ~ spl5_13
    | ~ spl5_21 ),
    inference(avatar_split_clause,[],[f171,f154,f116,f257])).

fof(f116,plain,
    ( spl5_13
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X1)
        | r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f154,plain,
    ( spl5_21
  <=> ! [X1,X3,X0,X2] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ r1_tarski(k1_relat_1(X3),X1)
        | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f171,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(k7_relat_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | m1_subset_1(k7_relat_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
        | ~ v1_relat_1(X0) )
    | ~ spl5_13
    | ~ spl5_21 ),
    inference(resolution,[],[f155,f117])).

fof(f117,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
        | ~ v1_relat_1(X1) )
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f116])).

fof(f155,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r1_tarski(k1_relat_1(X3),X1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f154])).

fof(f251,plain,(
    spl5_38 ),
    inference(avatar_split_clause,[],[f62,f249])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(X2,X0)
      | k1_xboole_0 = X1
      | m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X2,X0)
       => ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
            & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
            & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_funct_2)).

fof(f247,plain,
    ( spl5_37
    | ~ spl5_1
    | ~ spl5_5
    | ~ spl5_25
    | ~ spl5_32 ),
    inference(avatar_split_clause,[],[f221,f211,f173,f86,f70,f245])).

fof(f173,plain,
    ( spl5_25
  <=> ! [X1,X3,X0,X2] :
        ( ~ v1_funct_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f221,plain,
    ( ! [X0] : m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
    | ~ spl5_1
    | ~ spl5_5
    | ~ spl5_25
    | ~ spl5_32 ),
    inference(subsumption_resolution,[],[f220,f71])).

fof(f220,plain,
    ( ! [X0] :
        ( m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
        | ~ v1_funct_1(sK4) )
    | ~ spl5_5
    | ~ spl5_25
    | ~ spl5_32 ),
    inference(subsumption_resolution,[],[f218,f87])).

fof(f218,plain,
    ( ! [X0] :
        ( m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
        | ~ v1_funct_1(sK4) )
    | ~ spl5_25
    | ~ spl5_32 ),
    inference(superposition,[],[f174,f212])).

fof(f174,plain,
    ( ! [X2,X0,X3,X1] :
        ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X2) )
    | ~ spl5_25 ),
    inference(avatar_component_clause,[],[f173])).

fof(f235,plain,(
    spl5_36 ),
    inference(avatar_split_clause,[],[f61,f233])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(X2,X0)
      | k1_xboole_0 = X1
      | v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f231,plain,
    ( spl5_35
    | ~ spl5_1
    | ~ spl5_5
    | ~ spl5_17
    | ~ spl5_32 ),
    inference(avatar_split_clause,[],[f223,f211,f132,f86,f70,f229])).

fof(f132,plain,
    ( spl5_17
  <=> ! [X1,X3,X0,X2] :
        ( ~ v1_funct_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f223,plain,
    ( ! [X1] : v1_funct_1(k7_relat_1(sK4,X1))
    | ~ spl5_1
    | ~ spl5_5
    | ~ spl5_17
    | ~ spl5_32 ),
    inference(subsumption_resolution,[],[f222,f71])).

fof(f222,plain,
    ( ! [X1] :
        ( v1_funct_1(k7_relat_1(sK4,X1))
        | ~ v1_funct_1(sK4) )
    | ~ spl5_5
    | ~ spl5_17
    | ~ spl5_32 ),
    inference(subsumption_resolution,[],[f219,f87])).

fof(f219,plain,
    ( ! [X1] :
        ( v1_funct_1(k7_relat_1(sK4,X1))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
        | ~ v1_funct_1(sK4) )
    | ~ spl5_17
    | ~ spl5_32 ),
    inference(superposition,[],[f133,f212])).

fof(f133,plain,
    ( ! [X2,X0,X3,X1] :
        ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X2) )
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f132])).

fof(f213,plain,
    ( spl5_32
    | ~ spl5_5
    | ~ spl5_28 ),
    inference(avatar_split_clause,[],[f197,f190,f86,f211])).

fof(f190,plain,
    ( spl5_28
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k2_partfun1(X0,X1,sK4,X2) = k7_relat_1(sK4,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f197,plain,
    ( ! [X0] : k2_partfun1(sK0,sK3,sK4,X0) = k7_relat_1(sK4,X0)
    | ~ spl5_5
    | ~ spl5_28 ),
    inference(resolution,[],[f191,f87])).

fof(f191,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k2_partfun1(X0,X1,sK4,X2) = k7_relat_1(sK4,X2) )
    | ~ spl5_28 ),
    inference(avatar_component_clause,[],[f190])).

fof(f209,plain,
    ( ~ spl5_31
    | ~ spl5_5
    | spl5_9
    | ~ spl5_28 ),
    inference(avatar_split_clause,[],[f199,f190,f102,f86,f207])).

fof(f102,plain,
    ( spl5_9
  <=> m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f199,plain,
    ( ~ m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl5_5
    | spl5_9
    | ~ spl5_28 ),
    inference(backward_demodulation,[],[f103,f197])).

fof(f103,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | spl5_9 ),
    inference(avatar_component_clause,[],[f102])).

fof(f205,plain,
    ( ~ spl5_30
    | ~ spl5_5
    | spl5_10
    | ~ spl5_28 ),
    inference(avatar_split_clause,[],[f200,f190,f105,f86,f203])).

fof(f105,plain,
    ( spl5_10
  <=> v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f200,plain,
    ( ~ v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2)
    | ~ spl5_5
    | spl5_10
    | ~ spl5_28 ),
    inference(backward_demodulation,[],[f106,f197])).

fof(f106,plain,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)
    | spl5_10 ),
    inference(avatar_component_clause,[],[f105])).

fof(f192,plain,
    ( spl5_28
    | ~ spl5_1
    | ~ spl5_23 ),
    inference(avatar_split_clause,[],[f181,f164,f70,f190])).

fof(f164,plain,
    ( spl5_23
  <=> ! [X1,X3,X0,X2] :
        ( ~ v1_funct_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f181,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k2_partfun1(X0,X1,sK4,X2) = k7_relat_1(sK4,X2) )
    | ~ spl5_1
    | ~ spl5_23 ),
    inference(resolution,[],[f165,f71])).

fof(f165,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ v1_funct_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) )
    | ~ spl5_23 ),
    inference(avatar_component_clause,[],[f164])).

fof(f180,plain,
    ( spl5_26
    | spl5_2
    | ~ spl5_22 ),
    inference(avatar_split_clause,[],[f176,f160,f74,f178])).

fof(f160,plain,
    ( spl5_22
  <=> ! [X1,X0,X2] :
        ( v1_xboole_0(X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,X0,X1)
        | v1_partfun1(X2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f176,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK3)))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,X1,sK3)
        | v1_partfun1(X0,X1) )
    | spl5_2
    | ~ spl5_22 ),
    inference(resolution,[],[f161,f75])).

fof(f161,plain,
    ( ! [X2,X0,X1] :
        ( v1_xboole_0(X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,X0,X1)
        | v1_partfun1(X2,X0) )
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f160])).

fof(f175,plain,(
    spl5_25 ),
    inference(avatar_split_clause,[],[f65,f173])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).

fof(f170,plain,
    ( spl5_24
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f158,f144,f94,f86,f168])).

fof(f94,plain,
    ( spl5_7
  <=> r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f144,plain,
    ( spl5_20
  <=> ! [X1,X3,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f158,plain,
    ( r1_tarski(k9_relat_1(sK4,sK1),sK2)
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_20 ),
    inference(subsumption_resolution,[],[f157,f87])).

fof(f157,plain,
    ( r1_tarski(k9_relat_1(sK4,sK1),sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
    | ~ spl5_7
    | ~ spl5_20 ),
    inference(superposition,[],[f95,f145])).

fof(f145,plain,
    ( ! [X2,X0,X3,X1] :
        ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f144])).

fof(f95,plain,
    ( r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f94])).

fof(f166,plain,(
    spl5_23 ),
    inference(avatar_split_clause,[],[f63,f164])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f162,plain,(
    spl5_22 ),
    inference(avatar_split_clause,[],[f48,f160])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f156,plain,(
    spl5_21 ),
    inference(avatar_split_clause,[],[f56,f154])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( r1_tarski(k1_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).

fof(f152,plain,
    ( ~ spl5_1
    | ~ spl5_5
    | spl5_11
    | ~ spl5_17 ),
    inference(avatar_contradiction_clause,[],[f151])).

fof(f151,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_5
    | spl5_11
    | ~ spl5_17 ),
    inference(subsumption_resolution,[],[f150,f71])).

fof(f150,plain,
    ( ~ v1_funct_1(sK4)
    | ~ spl5_5
    | spl5_11
    | ~ spl5_17 ),
    inference(subsumption_resolution,[],[f148,f87])).

fof(f148,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
    | ~ v1_funct_1(sK4)
    | spl5_11
    | ~ spl5_17 ),
    inference(resolution,[],[f133,f109])).

fof(f109,plain,
    ( ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | spl5_11 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl5_11
  <=> v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f146,plain,(
    spl5_20 ),
    inference(avatar_split_clause,[],[f55,f144])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f142,plain,(
    spl5_19 ),
    inference(avatar_split_clause,[],[f54,f140])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_partfun1(X2,X0)
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).

fof(f138,plain,(
    spl5_18 ),
    inference(avatar_split_clause,[],[f52,f136])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

fof(f134,plain,(
    spl5_17 ),
    inference(avatar_split_clause,[],[f64,f132])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f126,plain,(
    spl5_15 ),
    inference(avatar_split_clause,[],[f50,f124])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f122,plain,(
    spl5_14 ),
    inference(avatar_split_clause,[],[f53,f120])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f118,plain,(
    spl5_13 ),
    inference(avatar_split_clause,[],[f49,f116])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

fof(f114,plain,(
    spl5_12 ),
    inference(avatar_split_clause,[],[f46,f112])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f110,plain,
    ( ~ spl5_9
    | ~ spl5_10
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f38,f108,f105,f102])).

fof(f38,plain,
    ( ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | ~ v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)
    | ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( ~ m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            | ~ v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2)
            | ~ v1_funct_1(k2_partfun1(X0,X3,X4,X1)) )
          & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2)
          & r1_tarski(X1,X0)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
          & v1_funct_2(X4,X0,X3)
          & v1_funct_1(X4) )
      & ~ v1_xboole_0(X3) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( ~ m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            | ~ v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2)
            | ~ v1_funct_1(k2_partfun1(X0,X3,X4,X1)) )
          & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2)
          & r1_tarski(X1,X0)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
          & v1_funct_2(X4,X0,X3)
          & v1_funct_1(X4) )
      & ~ v1_xboole_0(X3) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ~ v1_xboole_0(X3)
       => ! [X4] :
            ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
              & v1_funct_2(X4,X0,X3)
              & v1_funct_1(X4) )
           => ( ( r1_tarski(k7_relset_1(X0,X3,X4,X1),X2)
                & r1_tarski(X1,X0) )
             => ( m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2)
                & v1_funct_1(k2_partfun1(X0,X3,X4,X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ~ v1_xboole_0(X3)
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
            & v1_funct_2(X4,X0,X3)
            & v1_funct_1(X4) )
         => ( ( r1_tarski(k7_relset_1(X0,X3,X4,X1),X2)
              & r1_tarski(X1,X0) )
           => ( m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2)
              & v1_funct_1(k2_partfun1(X0,X3,X4,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_funct_2)).

fof(f100,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f47,f98])).

fof(f47,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f96,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f43,f94])).

fof(f43,plain,(
    r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f92,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f45,f90])).

fof(f45,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f88,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f41,f86])).

fof(f41,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) ),
    inference(cnf_transformation,[],[f18])).

fof(f84,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f40,f82])).

fof(f40,plain,(
    v1_funct_2(sK4,sK0,sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f80,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f42,f78])).

fof(f42,plain,(
    r1_tarski(sK1,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f76,plain,(
    ~ spl5_2 ),
    inference(avatar_split_clause,[],[f44,f74])).

fof(f44,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f72,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f39,f70])).

fof(f39,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:22:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (24372)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.47  % (24378)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.48  % (24379)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.48  % (24386)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.48  % (24382)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.49  % (24383)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.49  % (24371)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.50  % (24373)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.50  % (24370)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (24375)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.50  % (24378)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f386,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f72,f76,f80,f84,f88,f92,f96,f100,f110,f114,f118,f122,f126,f134,f138,f142,f146,f152,f156,f162,f166,f170,f175,f180,f192,f205,f209,f213,f231,f235,f247,f251,f259,f266,f276,f305,f314,f328,f333,f338,f348,f362,f372,f379,f385])).
% 0.21/0.50  fof(f385,plain,(
% 0.21/0.50    ~spl5_3 | ~spl5_52 | spl5_53),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f384])).
% 0.21/0.50  fof(f384,plain,(
% 0.21/0.50    $false | (~spl5_3 | ~spl5_52 | spl5_53)),
% 0.21/0.50    inference(subsumption_resolution,[],[f382,f79])).
% 0.21/0.50  fof(f79,plain,(
% 0.21/0.50    r1_tarski(sK1,sK0) | ~spl5_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f78])).
% 0.21/0.50  fof(f78,plain,(
% 0.21/0.50    spl5_3 <=> r1_tarski(sK1,sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.50  fof(f382,plain,(
% 0.21/0.50    ~r1_tarski(sK1,sK0) | (~spl5_52 | spl5_53)),
% 0.21/0.50    inference(resolution,[],[f368,f361])).
% 0.21/0.50  fof(f361,plain,(
% 0.21/0.50    ( ! [X0] : (m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(X0,sK3))) | ~r1_tarski(X0,sK0)) ) | ~spl5_52),
% 0.21/0.50    inference(avatar_component_clause,[],[f360])).
% 0.21/0.50  fof(f360,plain,(
% 0.21/0.50    spl5_52 <=> ! [X0] : (m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(X0,sK3))) | ~r1_tarski(X0,sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_52])])).
% 0.21/0.50  fof(f368,plain,(
% 0.21/0.50    ~m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) | spl5_53),
% 0.21/0.50    inference(avatar_component_clause,[],[f367])).
% 0.21/0.50  fof(f367,plain,(
% 0.21/0.50    spl5_53 <=> m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_53])])).
% 0.21/0.50  fof(f379,plain,(
% 0.21/0.50    ~spl5_3 | ~spl5_41 | spl5_54),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f378])).
% 0.21/0.50  fof(f378,plain,(
% 0.21/0.50    $false | (~spl5_3 | ~spl5_41 | spl5_54)),
% 0.21/0.50    inference(subsumption_resolution,[],[f374,f79])).
% 0.21/0.50  fof(f374,plain,(
% 0.21/0.50    ~r1_tarski(sK1,sK0) | (~spl5_41 | spl5_54)),
% 0.21/0.50    inference(resolution,[],[f371,f265])).
% 0.21/0.50  fof(f265,plain,(
% 0.21/0.50    ( ! [X0] : (v1_funct_2(k7_relat_1(sK4,X0),X0,sK3) | ~r1_tarski(X0,sK0)) ) | ~spl5_41),
% 0.21/0.50    inference(avatar_component_clause,[],[f264])).
% 0.21/0.50  fof(f264,plain,(
% 0.21/0.50    spl5_41 <=> ! [X0] : (v1_funct_2(k7_relat_1(sK4,X0),X0,sK3) | ~r1_tarski(X0,sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).
% 0.21/0.50  fof(f371,plain,(
% 0.21/0.50    ~v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK3) | spl5_54),
% 0.21/0.50    inference(avatar_component_clause,[],[f370])).
% 0.21/0.50  fof(f370,plain,(
% 0.21/0.50    spl5_54 <=> v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK3)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_54])])).
% 0.21/0.50  fof(f372,plain,(
% 0.21/0.50    ~spl5_31 | ~spl5_53 | ~spl5_54 | spl5_30 | ~spl5_35 | ~spl5_49),
% 0.21/0.50    inference(avatar_split_clause,[],[f349,f336,f229,f203,f370,f367,f207])).
% 0.21/0.50  fof(f207,plain,(
% 0.21/0.50    spl5_31 <=> m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).
% 0.21/0.50  fof(f203,plain,(
% 0.21/0.50    spl5_30 <=> v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).
% 0.21/0.50  fof(f229,plain,(
% 0.21/0.50    spl5_35 <=> ! [X1] : v1_funct_1(k7_relat_1(sK4,X1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).
% 0.21/0.50  fof(f336,plain,(
% 0.21/0.50    spl5_49 <=> ! [X1,X0,X2] : (~v1_funct_1(X0) | ~v1_funct_2(X0,X1,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK3))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_funct_2(X0,X1,X2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_49])])).
% 0.21/0.50  fof(f349,plain,(
% 0.21/0.50    ~v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK3) | ~m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) | ~m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | (spl5_30 | ~spl5_35 | ~spl5_49)),
% 0.21/0.50    inference(subsumption_resolution,[],[f339,f230])).
% 0.21/0.50  fof(f230,plain,(
% 0.21/0.50    ( ! [X1] : (v1_funct_1(k7_relat_1(sK4,X1))) ) | ~spl5_35),
% 0.21/0.50    inference(avatar_component_clause,[],[f229])).
% 0.21/0.50  fof(f339,plain,(
% 0.21/0.50    ~v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK3) | ~m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) | ~m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_1(k7_relat_1(sK4,sK1)) | (spl5_30 | ~spl5_49)),
% 0.21/0.50    inference(resolution,[],[f337,f204])).
% 0.21/0.50  fof(f204,plain,(
% 0.21/0.50    ~v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2) | spl5_30),
% 0.21/0.50    inference(avatar_component_clause,[],[f203])).
% 0.21/0.50  fof(f337,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (v1_funct_2(X0,X1,X2) | ~v1_funct_2(X0,X1,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK3))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X0)) ) | ~spl5_49),
% 0.21/0.50    inference(avatar_component_clause,[],[f336])).
% 0.21/0.50  fof(f362,plain,(
% 0.21/0.50    spl5_40 | spl5_52 | ~spl5_1 | ~spl5_4 | ~spl5_5 | ~spl5_32 | ~spl5_38),
% 0.21/0.50    inference(avatar_split_clause,[],[f255,f249,f211,f86,f82,f70,f360,f261])).
% 0.21/0.50  fof(f261,plain,(
% 0.21/0.50    spl5_40 <=> k1_xboole_0 = sK3),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).
% 0.21/0.50  fof(f70,plain,(
% 0.21/0.50    spl5_1 <=> v1_funct_1(sK4)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.50  fof(f82,plain,(
% 0.21/0.50    spl5_4 <=> v1_funct_2(sK4,sK0,sK3)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.50  fof(f86,plain,(
% 0.21/0.50    spl5_5 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.50  fof(f211,plain,(
% 0.21/0.50    spl5_32 <=> ! [X0] : k2_partfun1(sK0,sK3,sK4,X0) = k7_relat_1(sK4,X0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).
% 0.21/0.50  fof(f249,plain,(
% 0.21/0.50    spl5_38 <=> ! [X1,X3,X0,X2] : (~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(X2,X0) | k1_xboole_0 = X1 | m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).
% 0.21/0.50  fof(f255,plain,(
% 0.21/0.50    ( ! [X0] : (m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(X0,sK3))) | ~r1_tarski(X0,sK0) | k1_xboole_0 = sK3) ) | (~spl5_1 | ~spl5_4 | ~spl5_5 | ~spl5_32 | ~spl5_38)),
% 0.21/0.50    inference(subsumption_resolution,[],[f254,f71])).
% 0.21/0.50  fof(f71,plain,(
% 0.21/0.50    v1_funct_1(sK4) | ~spl5_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f70])).
% 0.21/0.50  fof(f254,plain,(
% 0.21/0.50    ( ! [X0] : (m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(X0,sK3))) | ~r1_tarski(X0,sK0) | k1_xboole_0 = sK3 | ~v1_funct_1(sK4)) ) | (~spl5_4 | ~spl5_5 | ~spl5_32 | ~spl5_38)),
% 0.21/0.50    inference(subsumption_resolution,[],[f253,f87])).
% 0.21/0.50  fof(f87,plain,(
% 0.21/0.50    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) | ~spl5_5),
% 0.21/0.50    inference(avatar_component_clause,[],[f86])).
% 0.21/0.50  fof(f253,plain,(
% 0.21/0.50    ( ! [X0] : (m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(X0,sK3))) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) | ~r1_tarski(X0,sK0) | k1_xboole_0 = sK3 | ~v1_funct_1(sK4)) ) | (~spl5_4 | ~spl5_32 | ~spl5_38)),
% 0.21/0.50    inference(subsumption_resolution,[],[f252,f83])).
% 0.21/0.50  fof(f83,plain,(
% 0.21/0.50    v1_funct_2(sK4,sK0,sK3) | ~spl5_4),
% 0.21/0.50    inference(avatar_component_clause,[],[f82])).
% 0.21/0.50  fof(f252,plain,(
% 0.21/0.50    ( ! [X0] : (m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(X0,sK3))) | ~v1_funct_2(sK4,sK0,sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) | ~r1_tarski(X0,sK0) | k1_xboole_0 = sK3 | ~v1_funct_1(sK4)) ) | (~spl5_32 | ~spl5_38)),
% 0.21/0.50    inference(superposition,[],[f250,f212])).
% 0.21/0.50  fof(f212,plain,(
% 0.21/0.50    ( ! [X0] : (k2_partfun1(sK0,sK3,sK4,X0) = k7_relat_1(sK4,X0)) ) | ~spl5_32),
% 0.21/0.50    inference(avatar_component_clause,[],[f211])).
% 0.21/0.50  fof(f250,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(X2,X0) | k1_xboole_0 = X1 | ~v1_funct_1(X3)) ) | ~spl5_38),
% 0.21/0.50    inference(avatar_component_clause,[],[f249])).
% 0.21/0.50  fof(f348,plain,(
% 0.21/0.50    ~spl5_44 | ~spl5_15 | ~spl5_24 | spl5_48),
% 0.21/0.50    inference(avatar_split_clause,[],[f343,f326,f168,f124,f300])).
% 0.21/0.50  fof(f300,plain,(
% 0.21/0.50    spl5_44 <=> v1_relat_1(sK4)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_44])])).
% 0.21/0.50  fof(f124,plain,(
% 0.21/0.50    spl5_15 <=> ! [X1,X0] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.21/0.50  fof(f168,plain,(
% 0.21/0.50    spl5_24 <=> r1_tarski(k9_relat_1(sK4,sK1),sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 0.21/0.50  fof(f326,plain,(
% 0.21/0.50    spl5_48 <=> r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_48])])).
% 0.21/0.50  fof(f343,plain,(
% 0.21/0.50    ~v1_relat_1(sK4) | (~spl5_15 | ~spl5_24 | spl5_48)),
% 0.21/0.50    inference(subsumption_resolution,[],[f342,f169])).
% 0.21/0.50  fof(f169,plain,(
% 0.21/0.50    r1_tarski(k9_relat_1(sK4,sK1),sK2) | ~spl5_24),
% 0.21/0.50    inference(avatar_component_clause,[],[f168])).
% 0.21/0.50  fof(f342,plain,(
% 0.21/0.50    ~r1_tarski(k9_relat_1(sK4,sK1),sK2) | ~v1_relat_1(sK4) | (~spl5_15 | spl5_48)),
% 0.21/0.50    inference(superposition,[],[f327,f125])).
% 0.21/0.50  fof(f125,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) ) | ~spl5_15),
% 0.21/0.50    inference(avatar_component_clause,[],[f124])).
% 0.21/0.50  fof(f327,plain,(
% 0.21/0.50    ~r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),sK2) | spl5_48),
% 0.21/0.50    inference(avatar_component_clause,[],[f326])).
% 0.21/0.50  fof(f338,plain,(
% 0.21/0.50    spl5_49 | ~spl5_19 | ~spl5_26),
% 0.21/0.50    inference(avatar_split_clause,[],[f184,f178,f140,f336])).
% 0.21/0.50  fof(f140,plain,(
% 0.21/0.50    spl5_19 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v1_partfun1(X2,X0) | v1_funct_2(X2,X0,X1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 0.21/0.50  fof(f178,plain,(
% 0.21/0.50    spl5_26 <=> ! [X1,X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK3))) | ~v1_funct_1(X0) | ~v1_funct_2(X0,X1,sK3) | v1_partfun1(X0,X1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 0.21/0.50  fof(f184,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v1_funct_1(X0) | ~v1_funct_2(X0,X1,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK3))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_funct_2(X0,X1,X2)) ) | (~spl5_19 | ~spl5_26)),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f183])).
% 0.21/0.50  fof(f183,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v1_funct_1(X0) | ~v1_funct_2(X0,X1,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK3))) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_funct_2(X0,X1,X2)) ) | (~spl5_19 | ~spl5_26)),
% 0.21/0.50    inference(resolution,[],[f179,f141])).
% 0.21/0.50  fof(f141,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_2(X2,X0,X1)) ) | ~spl5_19),
% 0.21/0.50    inference(avatar_component_clause,[],[f140])).
% 0.21/0.50  fof(f179,plain,(
% 0.21/0.50    ( ! [X0,X1] : (v1_partfun1(X0,X1) | ~v1_funct_1(X0) | ~v1_funct_2(X0,X1,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK3)))) ) | ~spl5_26),
% 0.21/0.50    inference(avatar_component_clause,[],[f178])).
% 0.21/0.50  fof(f333,plain,(
% 0.21/0.50    ~spl5_14 | ~spl5_37 | spl5_47),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f329])).
% 0.21/0.50  fof(f329,plain,(
% 0.21/0.50    $false | (~spl5_14 | ~spl5_37 | spl5_47)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f246,f324,f121])).
% 0.21/0.50  fof(f121,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl5_14),
% 0.21/0.50    inference(avatar_component_clause,[],[f120])).
% 0.21/0.50  fof(f120,plain,(
% 0.21/0.50    spl5_14 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.21/0.50  fof(f324,plain,(
% 0.21/0.50    ~v1_relat_1(k7_relat_1(sK4,sK1)) | spl5_47),
% 0.21/0.50    inference(avatar_component_clause,[],[f323])).
% 0.21/0.50  fof(f323,plain,(
% 0.21/0.50    spl5_47 <=> v1_relat_1(k7_relat_1(sK4,sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_47])])).
% 0.21/0.50  fof(f246,plain,(
% 0.21/0.50    ( ! [X0] : (m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))) ) | ~spl5_37),
% 0.21/0.50    inference(avatar_component_clause,[],[f245])).
% 0.21/0.50  fof(f245,plain,(
% 0.21/0.50    spl5_37 <=> ! [X0] : m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).
% 0.21/0.50  fof(f328,plain,(
% 0.21/0.50    ~spl5_47 | ~spl5_48 | ~spl5_18 | ~spl5_35 | ~spl5_45),
% 0.21/0.50    inference(avatar_split_clause,[],[f317,f303,f229,f136,f326,f323])).
% 0.21/0.50  fof(f136,plain,(
% 0.21/0.50    spl5_18 <=> ! [X1,X0] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 0.21/0.50  fof(f303,plain,(
% 0.21/0.50    spl5_45 <=> ! [X0] : ~m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_45])])).
% 0.21/0.50  fof(f317,plain,(
% 0.21/0.50    ~r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),sK2) | ~v1_relat_1(k7_relat_1(sK4,sK1)) | (~spl5_18 | ~spl5_35 | ~spl5_45)),
% 0.21/0.50    inference(subsumption_resolution,[],[f316,f230])).
% 0.21/0.50  fof(f316,plain,(
% 0.21/0.50    ~v1_funct_1(k7_relat_1(sK4,sK1)) | ~r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),sK2) | ~v1_relat_1(k7_relat_1(sK4,sK1)) | (~spl5_18 | ~spl5_45)),
% 0.21/0.50    inference(resolution,[],[f304,f137])).
% 0.21/0.50  fof(f137,plain,(
% 0.21/0.50    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) ) | ~spl5_18),
% 0.21/0.50    inference(avatar_component_clause,[],[f136])).
% 0.21/0.50  fof(f304,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))) ) | ~spl5_45),
% 0.21/0.50    inference(avatar_component_clause,[],[f303])).
% 0.21/0.50  fof(f314,plain,(
% 0.21/0.50    ~spl5_5 | ~spl5_8 | ~spl5_12 | spl5_44),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f310])).
% 0.21/0.50  fof(f310,plain,(
% 0.21/0.50    $false | (~spl5_5 | ~spl5_8 | ~spl5_12 | spl5_44)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f99,f87,f301,f113])).
% 0.21/0.50  fof(f113,plain,(
% 0.21/0.50    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | ~spl5_12),
% 0.21/0.50    inference(avatar_component_clause,[],[f112])).
% 0.21/0.50  fof(f112,plain,(
% 0.21/0.50    spl5_12 <=> ! [X1,X0] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.21/0.50  fof(f301,plain,(
% 0.21/0.50    ~v1_relat_1(sK4) | spl5_44),
% 0.21/0.50    inference(avatar_component_clause,[],[f300])).
% 0.21/0.50  fof(f99,plain,(
% 0.21/0.50    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) ) | ~spl5_8),
% 0.21/0.50    inference(avatar_component_clause,[],[f98])).
% 0.21/0.50  fof(f98,plain,(
% 0.21/0.50    spl5_8 <=> ! [X1,X0] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.50  fof(f305,plain,(
% 0.21/0.50    ~spl5_44 | spl5_45 | spl5_31 | ~spl5_39),
% 0.21/0.50    inference(avatar_split_clause,[],[f284,f257,f207,f303,f300])).
% 0.21/0.50  fof(f257,plain,(
% 0.21/0.50    spl5_39 <=> ! [X1,X3,X0,X2] : (~m1_subset_1(k7_relat_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | m1_subset_1(k7_relat_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X3))) | ~v1_relat_1(X0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).
% 0.21/0.50  fof(f284,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) | ~v1_relat_1(sK4)) ) | (spl5_31 | ~spl5_39)),
% 0.21/0.50    inference(resolution,[],[f258,f208])).
% 0.21/0.50  fof(f208,plain,(
% 0.21/0.50    ~m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | spl5_31),
% 0.21/0.50    inference(avatar_component_clause,[],[f207])).
% 0.21/0.50  fof(f258,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_relat_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X3))) | ~m1_subset_1(k7_relat_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_relat_1(X0)) ) | ~spl5_39),
% 0.21/0.50    inference(avatar_component_clause,[],[f257])).
% 0.21/0.50  fof(f276,plain,(
% 0.21/0.50    spl5_2 | ~spl5_6 | ~spl5_40),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f275])).
% 0.21/0.50  fof(f275,plain,(
% 0.21/0.50    $false | (spl5_2 | ~spl5_6 | ~spl5_40)),
% 0.21/0.50    inference(subsumption_resolution,[],[f267,f91])).
% 0.21/0.50  fof(f91,plain,(
% 0.21/0.50    v1_xboole_0(k1_xboole_0) | ~spl5_6),
% 0.21/0.50    inference(avatar_component_clause,[],[f90])).
% 0.21/0.50  fof(f90,plain,(
% 0.21/0.50    spl5_6 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.50  fof(f267,plain,(
% 0.21/0.50    ~v1_xboole_0(k1_xboole_0) | (spl5_2 | ~spl5_40)),
% 0.21/0.50    inference(backward_demodulation,[],[f75,f262])).
% 0.21/0.50  fof(f262,plain,(
% 0.21/0.50    k1_xboole_0 = sK3 | ~spl5_40),
% 0.21/0.50    inference(avatar_component_clause,[],[f261])).
% 0.21/0.50  fof(f75,plain,(
% 0.21/0.50    ~v1_xboole_0(sK3) | spl5_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f74])).
% 0.21/0.50  fof(f74,plain,(
% 0.21/0.50    spl5_2 <=> v1_xboole_0(sK3)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.50  fof(f266,plain,(
% 0.21/0.50    spl5_40 | spl5_41 | ~spl5_1 | ~spl5_4 | ~spl5_5 | ~spl5_32 | ~spl5_36),
% 0.21/0.50    inference(avatar_split_clause,[],[f243,f233,f211,f86,f82,f70,f264,f261])).
% 0.21/0.50  fof(f233,plain,(
% 0.21/0.50    spl5_36 <=> ! [X1,X3,X0,X2] : (~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(X2,X0) | k1_xboole_0 = X1 | v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).
% 0.21/0.50  fof(f243,plain,(
% 0.21/0.50    ( ! [X0] : (v1_funct_2(k7_relat_1(sK4,X0),X0,sK3) | ~r1_tarski(X0,sK0) | k1_xboole_0 = sK3) ) | (~spl5_1 | ~spl5_4 | ~spl5_5 | ~spl5_32 | ~spl5_36)),
% 0.21/0.50    inference(subsumption_resolution,[],[f242,f71])).
% 0.21/0.50  fof(f242,plain,(
% 0.21/0.50    ( ! [X0] : (v1_funct_2(k7_relat_1(sK4,X0),X0,sK3) | ~r1_tarski(X0,sK0) | k1_xboole_0 = sK3 | ~v1_funct_1(sK4)) ) | (~spl5_4 | ~spl5_5 | ~spl5_32 | ~spl5_36)),
% 0.21/0.50    inference(subsumption_resolution,[],[f241,f87])).
% 0.21/0.50  fof(f241,plain,(
% 0.21/0.50    ( ! [X0] : (v1_funct_2(k7_relat_1(sK4,X0),X0,sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) | ~r1_tarski(X0,sK0) | k1_xboole_0 = sK3 | ~v1_funct_1(sK4)) ) | (~spl5_4 | ~spl5_32 | ~spl5_36)),
% 0.21/0.50    inference(subsumption_resolution,[],[f238,f83])).
% 0.21/0.50  fof(f238,plain,(
% 0.21/0.50    ( ! [X0] : (v1_funct_2(k7_relat_1(sK4,X0),X0,sK3) | ~v1_funct_2(sK4,sK0,sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) | ~r1_tarski(X0,sK0) | k1_xboole_0 = sK3 | ~v1_funct_1(sK4)) ) | (~spl5_32 | ~spl5_36)),
% 0.21/0.50    inference(superposition,[],[f234,f212])).
% 0.21/0.50  fof(f234,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(X2,X0) | k1_xboole_0 = X1 | ~v1_funct_1(X3)) ) | ~spl5_36),
% 0.21/0.50    inference(avatar_component_clause,[],[f233])).
% 0.21/0.50  fof(f259,plain,(
% 0.21/0.50    spl5_39 | ~spl5_13 | ~spl5_21),
% 0.21/0.50    inference(avatar_split_clause,[],[f171,f154,f116,f257])).
% 0.21/0.50  fof(f116,plain,(
% 0.21/0.50    spl5_13 <=> ! [X1,X0] : (~v1_relat_1(X1) | r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.21/0.50  fof(f154,plain,(
% 0.21/0.50    spl5_21 <=> ! [X1,X3,X0,X2] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 0.21/0.50  fof(f171,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (~m1_subset_1(k7_relat_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | m1_subset_1(k7_relat_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X3))) | ~v1_relat_1(X0)) ) | (~spl5_13 | ~spl5_21)),
% 0.21/0.50    inference(resolution,[],[f155,f117])).
% 0.21/0.50  fof(f117,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) ) | ~spl5_13),
% 0.21/0.50    inference(avatar_component_clause,[],[f116])).
% 0.21/0.50  fof(f155,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ) | ~spl5_21),
% 0.21/0.50    inference(avatar_component_clause,[],[f154])).
% 0.21/0.50  fof(f251,plain,(
% 0.21/0.50    spl5_38),
% 0.21/0.50    inference(avatar_split_clause,[],[f62,f249])).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(X2,X0) | k1_xboole_0 = X1 | m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f33])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~r1_tarski(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.21/0.50    inference(flattening,[],[f32])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ! [X0,X1,X2,X3] : ((((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | ~r1_tarski(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.21/0.50    inference(ennf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_funct_2)).
% 0.21/0.50  fof(f247,plain,(
% 0.21/0.50    spl5_37 | ~spl5_1 | ~spl5_5 | ~spl5_25 | ~spl5_32),
% 0.21/0.50    inference(avatar_split_clause,[],[f221,f211,f173,f86,f70,f245])).
% 0.21/0.50  fof(f173,plain,(
% 0.21/0.50    spl5_25 <=> ! [X1,X3,X0,X2] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 0.21/0.50  fof(f221,plain,(
% 0.21/0.50    ( ! [X0] : (m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))) ) | (~spl5_1 | ~spl5_5 | ~spl5_25 | ~spl5_32)),
% 0.21/0.50    inference(subsumption_resolution,[],[f220,f71])).
% 0.21/0.50  fof(f220,plain,(
% 0.21/0.50    ( ! [X0] : (m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) | ~v1_funct_1(sK4)) ) | (~spl5_5 | ~spl5_25 | ~spl5_32)),
% 0.21/0.50    inference(subsumption_resolution,[],[f218,f87])).
% 0.21/0.50  fof(f218,plain,(
% 0.21/0.50    ( ! [X0] : (m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) | ~v1_funct_1(sK4)) ) | (~spl5_25 | ~spl5_32)),
% 0.21/0.50    inference(superposition,[],[f174,f212])).
% 0.21/0.50  fof(f174,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) ) | ~spl5_25),
% 0.21/0.50    inference(avatar_component_clause,[],[f173])).
% 0.21/0.50  fof(f235,plain,(
% 0.21/0.50    spl5_36),
% 0.21/0.50    inference(avatar_split_clause,[],[f61,f233])).
% 0.21/0.50  fof(f61,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(X2,X0) | k1_xboole_0 = X1 | v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f33])).
% 0.21/0.50  fof(f231,plain,(
% 0.21/0.50    spl5_35 | ~spl5_1 | ~spl5_5 | ~spl5_17 | ~spl5_32),
% 0.21/0.50    inference(avatar_split_clause,[],[f223,f211,f132,f86,f70,f229])).
% 0.21/0.50  fof(f132,plain,(
% 0.21/0.50    spl5_17 <=> ! [X1,X3,X0,X2] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_1(k2_partfun1(X0,X1,X2,X3)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.21/0.50  fof(f223,plain,(
% 0.21/0.50    ( ! [X1] : (v1_funct_1(k7_relat_1(sK4,X1))) ) | (~spl5_1 | ~spl5_5 | ~spl5_17 | ~spl5_32)),
% 0.21/0.50    inference(subsumption_resolution,[],[f222,f71])).
% 0.21/0.50  fof(f222,plain,(
% 0.21/0.50    ( ! [X1] : (v1_funct_1(k7_relat_1(sK4,X1)) | ~v1_funct_1(sK4)) ) | (~spl5_5 | ~spl5_17 | ~spl5_32)),
% 0.21/0.50    inference(subsumption_resolution,[],[f219,f87])).
% 0.21/0.50  fof(f219,plain,(
% 0.21/0.50    ( ! [X1] : (v1_funct_1(k7_relat_1(sK4,X1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) | ~v1_funct_1(sK4)) ) | (~spl5_17 | ~spl5_32)),
% 0.21/0.50    inference(superposition,[],[f133,f212])).
% 0.21/0.50  fof(f133,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) ) | ~spl5_17),
% 0.21/0.50    inference(avatar_component_clause,[],[f132])).
% 0.21/0.50  fof(f213,plain,(
% 0.21/0.50    spl5_32 | ~spl5_5 | ~spl5_28),
% 0.21/0.50    inference(avatar_split_clause,[],[f197,f190,f86,f211])).
% 0.21/0.50  fof(f190,plain,(
% 0.21/0.50    spl5_28 <=> ! [X1,X0,X2] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,sK4,X2) = k7_relat_1(sK4,X2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).
% 0.21/0.50  fof(f197,plain,(
% 0.21/0.50    ( ! [X0] : (k2_partfun1(sK0,sK3,sK4,X0) = k7_relat_1(sK4,X0)) ) | (~spl5_5 | ~spl5_28)),
% 0.21/0.50    inference(resolution,[],[f191,f87])).
% 0.21/0.50  fof(f191,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,sK4,X2) = k7_relat_1(sK4,X2)) ) | ~spl5_28),
% 0.21/0.50    inference(avatar_component_clause,[],[f190])).
% 0.21/0.50  fof(f209,plain,(
% 0.21/0.50    ~spl5_31 | ~spl5_5 | spl5_9 | ~spl5_28),
% 0.21/0.50    inference(avatar_split_clause,[],[f199,f190,f102,f86,f207])).
% 0.21/0.50  fof(f102,plain,(
% 0.21/0.50    spl5_9 <=> m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.21/0.50  fof(f199,plain,(
% 0.21/0.50    ~m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | (~spl5_5 | spl5_9 | ~spl5_28)),
% 0.21/0.50    inference(backward_demodulation,[],[f103,f197])).
% 0.21/0.50  fof(f103,plain,(
% 0.21/0.50    ~m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | spl5_9),
% 0.21/0.50    inference(avatar_component_clause,[],[f102])).
% 0.21/0.50  fof(f205,plain,(
% 0.21/0.50    ~spl5_30 | ~spl5_5 | spl5_10 | ~spl5_28),
% 0.21/0.50    inference(avatar_split_clause,[],[f200,f190,f105,f86,f203])).
% 0.21/0.50  fof(f105,plain,(
% 0.21/0.50    spl5_10 <=> v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.21/0.50  fof(f200,plain,(
% 0.21/0.50    ~v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2) | (~spl5_5 | spl5_10 | ~spl5_28)),
% 0.21/0.50    inference(backward_demodulation,[],[f106,f197])).
% 0.21/0.50  fof(f106,plain,(
% 0.21/0.50    ~v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2) | spl5_10),
% 0.21/0.50    inference(avatar_component_clause,[],[f105])).
% 0.21/0.50  fof(f192,plain,(
% 0.21/0.50    spl5_28 | ~spl5_1 | ~spl5_23),
% 0.21/0.50    inference(avatar_split_clause,[],[f181,f164,f70,f190])).
% 0.21/0.50  fof(f164,plain,(
% 0.21/0.50    spl5_23 <=> ! [X1,X3,X0,X2] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 0.21/0.50  fof(f181,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,sK4,X2) = k7_relat_1(sK4,X2)) ) | (~spl5_1 | ~spl5_23)),
% 0.21/0.50    inference(resolution,[],[f165,f71])).
% 0.21/0.50  fof(f165,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) ) | ~spl5_23),
% 0.21/0.50    inference(avatar_component_clause,[],[f164])).
% 0.21/0.50  fof(f180,plain,(
% 0.21/0.50    spl5_26 | spl5_2 | ~spl5_22),
% 0.21/0.50    inference(avatar_split_clause,[],[f176,f160,f74,f178])).
% 0.21/0.50  fof(f160,plain,(
% 0.21/0.50    spl5_22 <=> ! [X1,X0,X2] : (v1_xboole_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 0.21/0.50  fof(f176,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK3))) | ~v1_funct_1(X0) | ~v1_funct_2(X0,X1,sK3) | v1_partfun1(X0,X1)) ) | (spl5_2 | ~spl5_22)),
% 0.21/0.50    inference(resolution,[],[f161,f75])).
% 0.21/0.50  fof(f161,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0)) ) | ~spl5_22),
% 0.21/0.50    inference(avatar_component_clause,[],[f160])).
% 0.21/0.50  fof(f175,plain,(
% 0.21/0.50    spl5_25),
% 0.21/0.50    inference(avatar_split_clause,[],[f65,f173])).
% 0.21/0.50  fof(f65,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f37])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.21/0.50    inference(flattening,[],[f36])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.21/0.50    inference(ennf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).
% 0.21/0.50  fof(f170,plain,(
% 0.21/0.50    spl5_24 | ~spl5_5 | ~spl5_7 | ~spl5_20),
% 0.21/0.50    inference(avatar_split_clause,[],[f158,f144,f94,f86,f168])).
% 0.21/0.50  fof(f94,plain,(
% 0.21/0.50    spl5_7 <=> r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.50  fof(f144,plain,(
% 0.21/0.50    spl5_20 <=> ! [X1,X3,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 0.21/0.50  fof(f158,plain,(
% 0.21/0.50    r1_tarski(k9_relat_1(sK4,sK1),sK2) | (~spl5_5 | ~spl5_7 | ~spl5_20)),
% 0.21/0.50    inference(subsumption_resolution,[],[f157,f87])).
% 0.21/0.50  fof(f157,plain,(
% 0.21/0.50    r1_tarski(k9_relat_1(sK4,sK1),sK2) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) | (~spl5_7 | ~spl5_20)),
% 0.21/0.50    inference(superposition,[],[f95,f145])).
% 0.21/0.50  fof(f145,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl5_20),
% 0.21/0.50    inference(avatar_component_clause,[],[f144])).
% 0.21/0.50  fof(f95,plain,(
% 0.21/0.50    r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2) | ~spl5_7),
% 0.21/0.50    inference(avatar_component_clause,[],[f94])).
% 0.21/0.50  fof(f166,plain,(
% 0.21/0.50    spl5_23),
% 0.21/0.50    inference(avatar_split_clause,[],[f63,f164])).
% 0.21/0.50  fof(f63,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f35])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.21/0.50    inference(flattening,[],[f34])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.21/0.50    inference(ennf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 0.21/0.50  fof(f162,plain,(
% 0.21/0.50    spl5_22),
% 0.21/0.50    inference(avatar_split_clause,[],[f48,f160])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.21/0.50    inference(flattening,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,axiom,(
% 0.21/0.50    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.21/0.50  fof(f156,plain,(
% 0.21/0.50    spl5_21),
% 0.21/0.50    inference(avatar_split_clause,[],[f56,f154])).
% 0.21/0.50  fof(f56,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 0.21/0.50    inference(flattening,[],[f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => (r1_tarski(k1_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).
% 0.21/0.50  fof(f152,plain,(
% 0.21/0.50    ~spl5_1 | ~spl5_5 | spl5_11 | ~spl5_17),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f151])).
% 0.21/0.50  fof(f151,plain,(
% 0.21/0.50    $false | (~spl5_1 | ~spl5_5 | spl5_11 | ~spl5_17)),
% 0.21/0.50    inference(subsumption_resolution,[],[f150,f71])).
% 0.21/0.50  fof(f150,plain,(
% 0.21/0.50    ~v1_funct_1(sK4) | (~spl5_5 | spl5_11 | ~spl5_17)),
% 0.21/0.50    inference(subsumption_resolution,[],[f148,f87])).
% 0.21/0.50  fof(f148,plain,(
% 0.21/0.50    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) | ~v1_funct_1(sK4) | (spl5_11 | ~spl5_17)),
% 0.21/0.50    inference(resolution,[],[f133,f109])).
% 0.21/0.50  fof(f109,plain,(
% 0.21/0.50    ~v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) | spl5_11),
% 0.21/0.50    inference(avatar_component_clause,[],[f108])).
% 0.21/0.50  fof(f108,plain,(
% 0.21/0.50    spl5_11 <=> v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.21/0.50  fof(f146,plain,(
% 0.21/0.50    spl5_20),
% 0.21/0.50    inference(avatar_split_clause,[],[f55,f144])).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.21/0.50  fof(f142,plain,(
% 0.21/0.50    spl5_19),
% 0.21/0.50    inference(avatar_split_clause,[],[f54,f140])).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v1_partfun1(X2,X0) | v1_funct_2(X2,X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(flattening,[],[f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_partfun1(X2,X0) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).
% 0.21/0.50  fof(f138,plain,(
% 0.21/0.50    spl5_18),
% 0.21/0.50    inference(avatar_split_clause,[],[f52,f136])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(flattening,[],[f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.50    inference(ennf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,axiom,(
% 0.21/0.50    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).
% 0.21/0.50  fof(f134,plain,(
% 0.21/0.50    spl5_17),
% 0.21/0.50    inference(avatar_split_clause,[],[f64,f132])).
% 0.21/0.50  fof(f64,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_1(k2_partfun1(X0,X1,X2,X3))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f37])).
% 0.21/0.50  fof(f126,plain,(
% 0.21/0.50    spl5_15),
% 0.21/0.50    inference(avatar_split_clause,[],[f50,f124])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.21/0.50  fof(f122,plain,(
% 0.21/0.50    spl5_14),
% 0.21/0.50    inference(avatar_split_clause,[],[f53,f120])).
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.50  fof(f118,plain,(
% 0.21/0.50    spl5_13),
% 0.21/0.50    inference(avatar_split_clause,[],[f49,f116])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).
% 0.21/0.50  fof(f114,plain,(
% 0.21/0.50    spl5_12),
% 0.21/0.50    inference(avatar_split_clause,[],[f46,f112])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.50  fof(f110,plain,(
% 0.21/0.50    ~spl5_9 | ~spl5_10 | ~spl5_11),
% 0.21/0.50    inference(avatar_split_clause,[],[f38,f108,f105,f102])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ~v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) | ~v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2) | ~m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ? [X0,X1,X2,X3] : (? [X4] : ((~m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,X4,X1))) & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) & ~v1_xboole_0(X3))),
% 0.21/0.50    inference(flattening,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ? [X0,X1,X2,X3] : (? [X4] : (((~m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,X4,X1))) & (r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4))) & ~v1_xboole_0(X3))),
% 0.21/0.50    inference(ennf_transformation,[],[f16])).
% 0.21/0.50  fof(f16,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1,X2,X3] : (~v1_xboole_0(X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) => ((r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0)) => (m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) & v1_funct_1(k2_partfun1(X0,X3,X4,X1))))))),
% 0.21/0.50    inference(negated_conjecture,[],[f15])).
% 0.21/0.50  fof(f15,conjecture,(
% 0.21/0.50    ! [X0,X1,X2,X3] : (~v1_xboole_0(X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) => ((r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0)) => (m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) & v1_funct_1(k2_partfun1(X0,X3,X4,X1))))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_funct_2)).
% 0.21/0.50  fof(f100,plain,(
% 0.21/0.50    spl5_8),
% 0.21/0.50    inference(avatar_split_clause,[],[f47,f98])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.50  fof(f96,plain,(
% 0.21/0.50    spl5_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f43,f94])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f92,plain,(
% 0.21/0.50    spl5_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f45,f90])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    v1_xboole_0(k1_xboole_0)),
% 0.21/0.50    inference(cnf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    v1_xboole_0(k1_xboole_0)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.50  fof(f88,plain,(
% 0.21/0.50    spl5_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f41,f86])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f84,plain,(
% 0.21/0.50    spl5_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f40,f82])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    v1_funct_2(sK4,sK0,sK3)),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f80,plain,(
% 0.21/0.50    spl5_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f42,f78])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    r1_tarski(sK1,sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f76,plain,(
% 0.21/0.50    ~spl5_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f44,f74])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    ~v1_xboole_0(sK3)),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f72,plain,(
% 0.21/0.50    spl5_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f39,f70])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    v1_funct_1(sK4)),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (24378)------------------------------
% 0.21/0.50  % (24378)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (24378)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (24378)Memory used [KB]: 10874
% 0.21/0.50  % (24378)Time elapsed: 0.077 s
% 0.21/0.50  % (24378)------------------------------
% 0.21/0.50  % (24378)------------------------------
% 0.21/0.51  % (24367)Success in time 0.147 s
%------------------------------------------------------------------------------
