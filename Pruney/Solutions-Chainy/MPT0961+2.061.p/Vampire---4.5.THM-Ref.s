%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:19 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 287 expanded)
%              Number of leaves         :   35 ( 128 expanded)
%              Depth                    :    9
%              Number of atoms          :  464 ( 906 expanded)
%              Number of equality atoms :   85 ( 196 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f346,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f56,f64,f71,f75,f79,f83,f87,f95,f99,f104,f115,f122,f128,f141,f149,f170,f196,f212,f234,f249,f255,f284,f299,f304,f321,f336,f344])).

fof(f344,plain,
    ( spl2_44
    | ~ spl2_49 ),
    inference(avatar_contradiction_clause,[],[f337])).

fof(f337,plain,
    ( $false
    | spl2_44
    | ~ spl2_49 ),
    inference(unit_resulting_resolution,[],[f298,f335])).

fof(f335,plain,
    ( ! [X4] : v1_funct_2(k1_xboole_0,k1_xboole_0,X4)
    | ~ spl2_49 ),
    inference(avatar_component_clause,[],[f334])).

fof(f334,plain,
    ( spl2_49
  <=> ! [X4] : v1_funct_2(k1_xboole_0,k1_xboole_0,X4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_49])])).

fof(f298,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | spl2_44 ),
    inference(avatar_component_clause,[],[f297])).

fof(f297,plain,
    ( spl2_44
  <=> v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_44])])).

fof(f336,plain,
    ( spl2_49
    | ~ spl2_4
    | spl2_5
    | ~ spl2_6
    | ~ spl2_8
    | ~ spl2_20
    | ~ spl2_30
    | ~ spl2_36
    | ~ spl2_45 ),
    inference(avatar_split_clause,[],[f314,f302,f232,f194,f139,f81,f73,f69,f66,f334])).

fof(f66,plain,
    ( spl2_4
  <=> m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f69,plain,
    ( spl2_5
  <=> v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f73,plain,
    ( spl2_6
  <=> ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f81,plain,
    ( spl2_8
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | r2_hidden(sK1(X0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f139,plain,
    ( spl2_20
  <=> ! [X0] : ~ r2_hidden(X0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f194,plain,
    ( spl2_30
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 != k1_relat_1(X1)
        | v1_funct_2(X1,k1_xboole_0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).

fof(f232,plain,
    ( spl2_36
  <=> ! [X1,X0] :
        ( k1_xboole_0 = X0
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        | v1_funct_2(X1,k1_relat_1(X1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_36])])).

fof(f302,plain,
    ( spl2_45
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_45])])).

fof(f314,plain,
    ( ! [X4] : v1_funct_2(k1_xboole_0,k1_xboole_0,X4)
    | ~ spl2_4
    | spl2_5
    | ~ spl2_6
    | ~ spl2_8
    | ~ spl2_20
    | ~ spl2_30
    | ~ spl2_36
    | ~ spl2_45 ),
    inference(subsumption_resolution,[],[f311,f261])).

fof(f261,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl2_4
    | spl2_5
    | ~ spl2_6
    | ~ spl2_8
    | ~ spl2_20
    | ~ spl2_36 ),
    inference(backward_demodulation,[],[f250,f256])).

fof(f256,plain,
    ( k1_xboole_0 = sK0
    | ~ spl2_8
    | ~ spl2_20 ),
    inference(resolution,[],[f140,f82])).

fof(f82,plain,
    ( ! [X0] :
        ( r2_hidden(sK1(X0),X0)
        | k1_xboole_0 = X0 )
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f81])).

fof(f140,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK0)
    | ~ spl2_20 ),
    inference(avatar_component_clause,[],[f139])).

fof(f250,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl2_4
    | spl2_5
    | ~ spl2_6
    | ~ spl2_36 ),
    inference(forward_demodulation,[],[f244,f74])).

fof(f74,plain,
    ( ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f73])).

fof(f244,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k1_xboole_0)))
    | ~ spl2_4
    | spl2_5
    | ~ spl2_36 ),
    inference(backward_demodulation,[],[f121,f242])).

fof(f242,plain,
    ( k1_xboole_0 = k2_relat_1(sK0)
    | ~ spl2_4
    | spl2_5
    | ~ spl2_36 ),
    inference(subsumption_resolution,[],[f239,f70])).

fof(f70,plain,
    ( ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
    | spl2_5 ),
    inference(avatar_component_clause,[],[f69])).

fof(f239,plain,
    ( k1_xboole_0 = k2_relat_1(sK0)
    | v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
    | ~ spl2_4
    | ~ spl2_36 ),
    inference(resolution,[],[f233,f121])).

fof(f233,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        | k1_xboole_0 = X0
        | v1_funct_2(X1,k1_relat_1(X1),X0) )
    | ~ spl2_36 ),
    inference(avatar_component_clause,[],[f232])).

fof(f121,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f66])).

fof(f311,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
        | v1_funct_2(k1_xboole_0,k1_xboole_0,X4) )
    | ~ spl2_30
    | ~ spl2_45 ),
    inference(trivial_inequality_removal,[],[f308])).

fof(f308,plain,
    ( ! [X4] :
        ( k1_xboole_0 != k1_xboole_0
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
        | v1_funct_2(k1_xboole_0,k1_xboole_0,X4) )
    | ~ spl2_30
    | ~ spl2_45 ),
    inference(superposition,[],[f195,f303])).

fof(f303,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl2_45 ),
    inference(avatar_component_clause,[],[f302])).

fof(f195,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 != k1_relat_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
        | v1_funct_2(X1,k1_xboole_0,X0) )
    | ~ spl2_30 ),
    inference(avatar_component_clause,[],[f194])).

fof(f321,plain,
    ( spl2_16
    | ~ spl2_4
    | spl2_5
    | ~ spl2_6
    | ~ spl2_8
    | ~ spl2_20
    | ~ spl2_36 ),
    inference(avatar_split_clause,[],[f261,f232,f139,f81,f73,f69,f66,f113])).

fof(f113,plain,
    ( spl2_16
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f304,plain,
    ( spl2_45
    | ~ spl2_15
    | spl2_42 ),
    inference(avatar_split_clause,[],[f286,f282,f110,f302])).

fof(f110,plain,
    ( spl2_15
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | v1_funct_2(k1_xboole_0,X0,k1_xboole_0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f282,plain,
    ( spl2_42
  <=> v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_42])])).

fof(f286,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl2_15
    | spl2_42 ),
    inference(resolution,[],[f111,f283])).

fof(f283,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | spl2_42 ),
    inference(avatar_component_clause,[],[f282])).

fof(f111,plain,
    ( ! [X0] :
        ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
        | k1_xboole_0 = X0 )
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f110])).

fof(f299,plain,
    ( ~ spl2_44
    | ~ spl2_15
    | spl2_42 ),
    inference(avatar_split_clause,[],[f291,f282,f110,f297])).

fof(f291,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl2_15
    | spl2_42 ),
    inference(backward_demodulation,[],[f283,f286])).

fof(f284,plain,
    ( ~ spl2_42
    | ~ spl2_8
    | ~ spl2_20
    | spl2_38 ),
    inference(avatar_split_clause,[],[f263,f253,f139,f81,f282])).

fof(f253,plain,
    ( spl2_38
  <=> v1_funct_2(sK0,k1_relat_1(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_38])])).

fof(f263,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ spl2_8
    | ~ spl2_20
    | spl2_38 ),
    inference(backward_demodulation,[],[f254,f256])).

fof(f254,plain,
    ( ~ v1_funct_2(sK0,k1_relat_1(sK0),k1_xboole_0)
    | spl2_38 ),
    inference(avatar_component_clause,[],[f253])).

fof(f255,plain,
    ( ~ spl2_38
    | ~ spl2_4
    | spl2_5
    | ~ spl2_36 ),
    inference(avatar_split_clause,[],[f246,f232,f69,f66,f253])).

fof(f246,plain,
    ( ~ v1_funct_2(sK0,k1_relat_1(sK0),k1_xboole_0)
    | ~ spl2_4
    | spl2_5
    | ~ spl2_36 ),
    inference(backward_demodulation,[],[f70,f242])).

fof(f249,plain,
    ( ~ spl2_3
    | ~ spl2_4
    | spl2_5
    | ~ spl2_6
    | spl2_19
    | ~ spl2_36 ),
    inference(avatar_contradiction_clause,[],[f248])).

fof(f248,plain,
    ( $false
    | ~ spl2_3
    | ~ spl2_4
    | spl2_5
    | ~ spl2_6
    | spl2_19
    | ~ spl2_36 ),
    inference(subsumption_resolution,[],[f247,f63])).

fof(f63,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl2_3
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f247,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl2_4
    | spl2_5
    | ~ spl2_6
    | spl2_19
    | ~ spl2_36 ),
    inference(forward_demodulation,[],[f243,f74])).

fof(f243,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1(sK0),k1_xboole_0))
    | ~ spl2_4
    | spl2_5
    | spl2_19
    | ~ spl2_36 ),
    inference(backward_demodulation,[],[f137,f242])).

fof(f137,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))
    | spl2_19 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl2_19
  <=> v1_xboole_0(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f234,plain,
    ( spl2_36
    | ~ spl2_33 ),
    inference(avatar_split_clause,[],[f214,f210,f232])).

fof(f210,plain,
    ( spl2_33
  <=> ! [X1,X0,X2] :
        ( k1_relat_1(X2) != X0
        | k1_xboole_0 = X1
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_funct_2(X2,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_33])])).

fof(f214,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = X0
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        | v1_funct_2(X1,k1_relat_1(X1),X0) )
    | ~ spl2_33 ),
    inference(equality_resolution,[],[f211])).

fof(f211,plain,
    ( ! [X2,X0,X1] :
        ( k1_relat_1(X2) != X0
        | k1_xboole_0 = X1
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_funct_2(X2,X0,X1) )
    | ~ spl2_33 ),
    inference(avatar_component_clause,[],[f210])).

fof(f212,plain,
    ( spl2_33
    | ~ spl2_17
    | ~ spl2_25 ),
    inference(avatar_split_clause,[],[f181,f168,f126,f210])).

fof(f126,plain,
    ( spl2_17
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f168,plain,
    ( spl2_25
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_xboole_0 = X1
        | k1_relset_1(X0,X1,X2) != X0
        | v1_funct_2(X2,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).

fof(f181,plain,
    ( ! [X2,X0,X1] :
        ( k1_relat_1(X2) != X0
        | k1_xboole_0 = X1
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_funct_2(X2,X0,X1) )
    | ~ spl2_17
    | ~ spl2_25 ),
    inference(duplicate_literal_removal,[],[f180])).

fof(f180,plain,
    ( ! [X2,X0,X1] :
        ( k1_relat_1(X2) != X0
        | k1_xboole_0 = X1
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_funct_2(X2,X0,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl2_17
    | ~ spl2_25 ),
    inference(superposition,[],[f169,f127])).

fof(f127,plain,
    ( ! [X2,X0,X1] :
        ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f126])).

fof(f169,plain,
    ( ! [X2,X0,X1] :
        ( k1_relset_1(X0,X1,X2) != X0
        | k1_xboole_0 = X1
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_funct_2(X2,X0,X1) )
    | ~ spl2_25 ),
    inference(avatar_component_clause,[],[f168])).

fof(f196,plain,
    ( spl2_30
    | ~ spl2_7
    | ~ spl2_17
    | ~ spl2_22 ),
    inference(avatar_split_clause,[],[f164,f147,f126,f77,f194])).

fof(f77,plain,
    ( spl2_7
  <=> ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f147,plain,
    ( spl2_22
  <=> ! [X1,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
        | v1_funct_2(X2,k1_xboole_0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f164,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 != k1_relat_1(X1)
        | v1_funct_2(X1,k1_xboole_0,X0) )
    | ~ spl2_7
    | ~ spl2_17
    | ~ spl2_22 ),
    inference(duplicate_literal_removal,[],[f163])).

fof(f163,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 != k1_relat_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
        | v1_funct_2(X1,k1_xboole_0,X0) )
    | ~ spl2_7
    | ~ spl2_17
    | ~ spl2_22 ),
    inference(forward_demodulation,[],[f162,f78])).

fof(f78,plain,
    ( ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f77])).

fof(f162,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 != k1_relat_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
        | v1_funct_2(X1,k1_xboole_0,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) )
    | ~ spl2_17
    | ~ spl2_22 ),
    inference(superposition,[],[f148,f127])).

fof(f148,plain,
    ( ! [X2,X1] :
        ( k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
        | v1_funct_2(X2,k1_xboole_0,X1) )
    | ~ spl2_22 ),
    inference(avatar_component_clause,[],[f147])).

fof(f170,plain,(
    spl2_25 ),
    inference(avatar_split_clause,[],[f38,f168])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f149,plain,(
    spl2_22 ),
    inference(avatar_split_clause,[],[f50,f147])).

fof(f50,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(forward_demodulation,[],[f44,f42])).

fof(f42,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f44,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f141,plain,
    ( ~ spl2_19
    | spl2_20
    | ~ spl2_4
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f129,f97,f66,f139,f136])).

fof(f97,plain,
    ( spl2_12
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
        | ~ v1_xboole_0(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f129,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) )
    | ~ spl2_4
    | ~ spl2_12 ),
    inference(resolution,[],[f121,f98])).

fof(f98,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
        | ~ r2_hidden(X0,X1)
        | ~ v1_xboole_0(X2) )
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f97])).

fof(f128,plain,(
    spl2_17 ),
    inference(avatar_split_clause,[],[f32,f126])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f122,plain,
    ( spl2_4
    | ~ spl2_9
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f117,f102,f85,f66])).

fof(f85,plain,
    ( spl2_9
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,X1)
        | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f102,plain,
    ( spl2_13
  <=> r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f117,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | ~ spl2_9
    | ~ spl2_13 ),
    inference(resolution,[],[f103,f86])).

fof(f86,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | m1_subset_1(X0,k1_zfmisc_1(X1)) )
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f85])).

fof(f103,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f102])).

fof(f115,plain,
    ( spl2_15
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f52,f113,f110])).

fof(f52,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 = X0
      | v1_funct_2(k1_xboole_0,X0,k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f47,f41])).

fof(f41,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f47,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | k1_xboole_0 = X0
      | v1_funct_2(k1_xboole_0,X0,k1_xboole_0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | k1_xboole_0 = X0
      | k1_xboole_0 != X2
      | v1_funct_2(X2,X0,k1_xboole_0) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != X2
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f104,plain,
    ( spl2_13
    | ~ spl2_1
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f100,f93,f54,f102])).

fof(f54,plain,
    ( spl2_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f93,plain,
    ( spl2_11
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f100,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))
    | ~ spl2_1
    | ~ spl2_11 ),
    inference(resolution,[],[f94,f55])).

fof(f55,plain,
    ( v1_relat_1(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f54])).

fof(f94,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) )
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f93])).

fof(f99,plain,(
    spl2_12 ),
    inference(avatar_split_clause,[],[f40,f97])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f95,plain,(
    spl2_11 ),
    inference(avatar_split_clause,[],[f25,f93])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

% (26972)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
fof(f87,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f27,f85])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f83,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f26,f81])).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | r2_hidden(sK1(X0),X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f79,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f42,f77])).

fof(f75,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f41,f73])).

fof(f71,plain,
    ( ~ spl2_4
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f48,f69,f66])).

fof(f48,plain,
    ( ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
    | ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) ),
    inference(subsumption_resolution,[],[f21,f23])).

fof(f23,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        | ~ v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        | ~ v1_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        | ~ v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        | ~ v1_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
          & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
          & v1_funct_1(X0) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(f21,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
    | ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) ),
    inference(cnf_transformation,[],[f13])).

fof(f64,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f24,f62])).

fof(f24,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f56,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f22,f54])).

fof(f22,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:43:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.45  % (26967)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.47  % (26975)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.48  % (26959)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.49  % (26968)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.49  % (26969)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.49  % (26978)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.49  % (26971)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (26971)Refutation not found, incomplete strategy% (26971)------------------------------
% 0.21/0.50  % (26971)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (26971)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (26971)Memory used [KB]: 6140
% 0.21/0.50  % (26971)Time elapsed: 0.056 s
% 0.21/0.50  % (26971)------------------------------
% 0.21/0.50  % (26971)------------------------------
% 0.21/0.50  % (26965)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.50  % (26974)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.50  % (26970)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.50  % (26962)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.50  % (26959)Refutation not found, incomplete strategy% (26959)------------------------------
% 0.21/0.50  % (26959)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (26959)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (26959)Memory used [KB]: 6140
% 0.21/0.50  % (26959)Time elapsed: 0.080 s
% 0.21/0.50  % (26959)------------------------------
% 0.21/0.50  % (26959)------------------------------
% 0.21/0.50  % (26960)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (26977)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.50  % (26962)Refutation not found, incomplete strategy% (26962)------------------------------
% 0.21/0.50  % (26962)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (26962)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (26962)Memory used [KB]: 10618
% 0.21/0.50  % (26962)Time elapsed: 0.090 s
% 0.21/0.50  % (26962)------------------------------
% 0.21/0.50  % (26962)------------------------------
% 0.21/0.50  % (26960)Refutation not found, incomplete strategy% (26960)------------------------------
% 0.21/0.50  % (26960)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (26960)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (26960)Memory used [KB]: 10618
% 0.21/0.50  % (26960)Time elapsed: 0.083 s
% 0.21/0.50  % (26960)------------------------------
% 0.21/0.50  % (26960)------------------------------
% 0.21/0.50  % (26963)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.50  % (26968)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f346,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f56,f64,f71,f75,f79,f83,f87,f95,f99,f104,f115,f122,f128,f141,f149,f170,f196,f212,f234,f249,f255,f284,f299,f304,f321,f336,f344])).
% 0.21/0.50  fof(f344,plain,(
% 0.21/0.50    spl2_44 | ~spl2_49),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f337])).
% 0.21/0.50  fof(f337,plain,(
% 0.21/0.50    $false | (spl2_44 | ~spl2_49)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f298,f335])).
% 0.21/0.50  fof(f335,plain,(
% 0.21/0.50    ( ! [X4] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X4)) ) | ~spl2_49),
% 0.21/0.50    inference(avatar_component_clause,[],[f334])).
% 0.21/0.50  fof(f334,plain,(
% 0.21/0.50    spl2_49 <=> ! [X4] : v1_funct_2(k1_xboole_0,k1_xboole_0,X4)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_49])])).
% 0.21/0.50  fof(f298,plain,(
% 0.21/0.50    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | spl2_44),
% 0.21/0.50    inference(avatar_component_clause,[],[f297])).
% 0.21/0.50  fof(f297,plain,(
% 0.21/0.50    spl2_44 <=> v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_44])])).
% 0.21/0.50  fof(f336,plain,(
% 0.21/0.50    spl2_49 | ~spl2_4 | spl2_5 | ~spl2_6 | ~spl2_8 | ~spl2_20 | ~spl2_30 | ~spl2_36 | ~spl2_45),
% 0.21/0.50    inference(avatar_split_clause,[],[f314,f302,f232,f194,f139,f81,f73,f69,f66,f334])).
% 0.21/0.50  fof(f66,plain,(
% 0.21/0.50    spl2_4 <=> m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.50  fof(f69,plain,(
% 0.21/0.50    spl2_5 <=> v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.50  fof(f73,plain,(
% 0.21/0.50    spl2_6 <=> ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.50  fof(f81,plain,(
% 0.21/0.50    spl2_8 <=> ! [X0] : (k1_xboole_0 = X0 | r2_hidden(sK1(X0),X0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.50  fof(f139,plain,(
% 0.21/0.50    spl2_20 <=> ! [X0] : ~r2_hidden(X0,sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 0.21/0.50  fof(f194,plain,(
% 0.21/0.50    spl2_30 <=> ! [X1,X0] : (~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 != k1_relat_1(X1) | v1_funct_2(X1,k1_xboole_0,X0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).
% 0.21/0.50  fof(f232,plain,(
% 0.21/0.50    spl2_36 <=> ! [X1,X0] : (k1_xboole_0 = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | v1_funct_2(X1,k1_relat_1(X1),X0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_36])])).
% 0.21/0.50  fof(f302,plain,(
% 0.21/0.50    spl2_45 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_45])])).
% 0.21/0.50  fof(f314,plain,(
% 0.21/0.50    ( ! [X4] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X4)) ) | (~spl2_4 | spl2_5 | ~spl2_6 | ~spl2_8 | ~spl2_20 | ~spl2_30 | ~spl2_36 | ~spl2_45)),
% 0.21/0.50    inference(subsumption_resolution,[],[f311,f261])).
% 0.21/0.50  fof(f261,plain,(
% 0.21/0.50    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (~spl2_4 | spl2_5 | ~spl2_6 | ~spl2_8 | ~spl2_20 | ~spl2_36)),
% 0.21/0.50    inference(backward_demodulation,[],[f250,f256])).
% 0.21/0.50  fof(f256,plain,(
% 0.21/0.50    k1_xboole_0 = sK0 | (~spl2_8 | ~spl2_20)),
% 0.21/0.50    inference(resolution,[],[f140,f82])).
% 0.21/0.50  fof(f82,plain,(
% 0.21/0.50    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) ) | ~spl2_8),
% 0.21/0.50    inference(avatar_component_clause,[],[f81])).
% 0.21/0.50  fof(f140,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(X0,sK0)) ) | ~spl2_20),
% 0.21/0.50    inference(avatar_component_clause,[],[f139])).
% 0.21/0.50  fof(f250,plain,(
% 0.21/0.50    m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) | (~spl2_4 | spl2_5 | ~spl2_6 | ~spl2_36)),
% 0.21/0.50    inference(forward_demodulation,[],[f244,f74])).
% 0.21/0.50  fof(f74,plain,(
% 0.21/0.50    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) ) | ~spl2_6),
% 0.21/0.50    inference(avatar_component_clause,[],[f73])).
% 0.21/0.50  fof(f244,plain,(
% 0.21/0.50    m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k1_xboole_0))) | (~spl2_4 | spl2_5 | ~spl2_36)),
% 0.21/0.50    inference(backward_demodulation,[],[f121,f242])).
% 0.21/0.50  fof(f242,plain,(
% 0.21/0.50    k1_xboole_0 = k2_relat_1(sK0) | (~spl2_4 | spl2_5 | ~spl2_36)),
% 0.21/0.50    inference(subsumption_resolution,[],[f239,f70])).
% 0.21/0.50  fof(f70,plain,(
% 0.21/0.50    ~v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | spl2_5),
% 0.21/0.50    inference(avatar_component_clause,[],[f69])).
% 0.21/0.50  fof(f239,plain,(
% 0.21/0.50    k1_xboole_0 = k2_relat_1(sK0) | v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | (~spl2_4 | ~spl2_36)),
% 0.21/0.50    inference(resolution,[],[f233,f121])).
% 0.21/0.50  fof(f233,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | k1_xboole_0 = X0 | v1_funct_2(X1,k1_relat_1(X1),X0)) ) | ~spl2_36),
% 0.21/0.50    inference(avatar_component_clause,[],[f232])).
% 0.21/0.50  fof(f121,plain,(
% 0.21/0.50    m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | ~spl2_4),
% 0.21/0.50    inference(avatar_component_clause,[],[f66])).
% 0.21/0.50  fof(f311,plain,(
% 0.21/0.50    ( ! [X4] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | v1_funct_2(k1_xboole_0,k1_xboole_0,X4)) ) | (~spl2_30 | ~spl2_45)),
% 0.21/0.50    inference(trivial_inequality_removal,[],[f308])).
% 0.21/0.50  fof(f308,plain,(
% 0.21/0.50    ( ! [X4] : (k1_xboole_0 != k1_xboole_0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | v1_funct_2(k1_xboole_0,k1_xboole_0,X4)) ) | (~spl2_30 | ~spl2_45)),
% 0.21/0.50    inference(superposition,[],[f195,f303])).
% 0.21/0.50  fof(f303,plain,(
% 0.21/0.50    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl2_45),
% 0.21/0.50    inference(avatar_component_clause,[],[f302])).
% 0.21/0.50  fof(f195,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k1_xboole_0 != k1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | v1_funct_2(X1,k1_xboole_0,X0)) ) | ~spl2_30),
% 0.21/0.50    inference(avatar_component_clause,[],[f194])).
% 0.21/0.50  fof(f321,plain,(
% 0.21/0.50    spl2_16 | ~spl2_4 | spl2_5 | ~spl2_6 | ~spl2_8 | ~spl2_20 | ~spl2_36),
% 0.21/0.50    inference(avatar_split_clause,[],[f261,f232,f139,f81,f73,f69,f66,f113])).
% 0.21/0.50  fof(f113,plain,(
% 0.21/0.50    spl2_16 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.21/0.50  fof(f304,plain,(
% 0.21/0.50    spl2_45 | ~spl2_15 | spl2_42),
% 0.21/0.50    inference(avatar_split_clause,[],[f286,f282,f110,f302])).
% 0.21/0.50  fof(f110,plain,(
% 0.21/0.50    spl2_15 <=> ! [X0] : (k1_xboole_0 = X0 | v1_funct_2(k1_xboole_0,X0,k1_xboole_0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.21/0.50  fof(f282,plain,(
% 0.21/0.50    spl2_42 <=> v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_42])])).
% 0.21/0.50  fof(f286,plain,(
% 0.21/0.50    k1_xboole_0 = k1_relat_1(k1_xboole_0) | (~spl2_15 | spl2_42)),
% 0.21/0.50    inference(resolution,[],[f111,f283])).
% 0.21/0.50  fof(f283,plain,(
% 0.21/0.50    ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) | spl2_42),
% 0.21/0.50    inference(avatar_component_clause,[],[f282])).
% 0.21/0.50  fof(f111,plain,(
% 0.21/0.50    ( ! [X0] : (v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0) ) | ~spl2_15),
% 0.21/0.50    inference(avatar_component_clause,[],[f110])).
% 0.21/0.50  fof(f299,plain,(
% 0.21/0.50    ~spl2_44 | ~spl2_15 | spl2_42),
% 0.21/0.50    inference(avatar_split_clause,[],[f291,f282,f110,f297])).
% 0.21/0.50  fof(f291,plain,(
% 0.21/0.50    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl2_15 | spl2_42)),
% 0.21/0.50    inference(backward_demodulation,[],[f283,f286])).
% 0.21/0.50  fof(f284,plain,(
% 0.21/0.50    ~spl2_42 | ~spl2_8 | ~spl2_20 | spl2_38),
% 0.21/0.50    inference(avatar_split_clause,[],[f263,f253,f139,f81,f282])).
% 0.21/0.50  fof(f253,plain,(
% 0.21/0.50    spl2_38 <=> v1_funct_2(sK0,k1_relat_1(sK0),k1_xboole_0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_38])])).
% 0.21/0.50  fof(f263,plain,(
% 0.21/0.50    ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) | (~spl2_8 | ~spl2_20 | spl2_38)),
% 0.21/0.50    inference(backward_demodulation,[],[f254,f256])).
% 0.21/0.50  fof(f254,plain,(
% 0.21/0.50    ~v1_funct_2(sK0,k1_relat_1(sK0),k1_xboole_0) | spl2_38),
% 0.21/0.50    inference(avatar_component_clause,[],[f253])).
% 0.21/0.50  fof(f255,plain,(
% 0.21/0.50    ~spl2_38 | ~spl2_4 | spl2_5 | ~spl2_36),
% 0.21/0.50    inference(avatar_split_clause,[],[f246,f232,f69,f66,f253])).
% 0.21/0.50  fof(f246,plain,(
% 0.21/0.50    ~v1_funct_2(sK0,k1_relat_1(sK0),k1_xboole_0) | (~spl2_4 | spl2_5 | ~spl2_36)),
% 0.21/0.50    inference(backward_demodulation,[],[f70,f242])).
% 0.21/0.50  fof(f249,plain,(
% 0.21/0.50    ~spl2_3 | ~spl2_4 | spl2_5 | ~spl2_6 | spl2_19 | ~spl2_36),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f248])).
% 0.21/0.50  fof(f248,plain,(
% 0.21/0.50    $false | (~spl2_3 | ~spl2_4 | spl2_5 | ~spl2_6 | spl2_19 | ~spl2_36)),
% 0.21/0.50    inference(subsumption_resolution,[],[f247,f63])).
% 0.21/0.50  fof(f63,plain,(
% 0.21/0.50    v1_xboole_0(k1_xboole_0) | ~spl2_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f62])).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    spl2_3 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.50  fof(f247,plain,(
% 0.21/0.50    ~v1_xboole_0(k1_xboole_0) | (~spl2_4 | spl2_5 | ~spl2_6 | spl2_19 | ~spl2_36)),
% 0.21/0.50    inference(forward_demodulation,[],[f243,f74])).
% 0.21/0.50  fof(f243,plain,(
% 0.21/0.50    ~v1_xboole_0(k2_zfmisc_1(k1_relat_1(sK0),k1_xboole_0)) | (~spl2_4 | spl2_5 | spl2_19 | ~spl2_36)),
% 0.21/0.50    inference(backward_demodulation,[],[f137,f242])).
% 0.21/0.50  fof(f137,plain,(
% 0.21/0.50    ~v1_xboole_0(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) | spl2_19),
% 0.21/0.50    inference(avatar_component_clause,[],[f136])).
% 0.21/0.50  fof(f136,plain,(
% 0.21/0.50    spl2_19 <=> v1_xboole_0(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 0.21/0.50  fof(f234,plain,(
% 0.21/0.50    spl2_36 | ~spl2_33),
% 0.21/0.50    inference(avatar_split_clause,[],[f214,f210,f232])).
% 0.21/0.50  fof(f210,plain,(
% 0.21/0.50    spl2_33 <=> ! [X1,X0,X2] : (k1_relat_1(X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_2(X2,X0,X1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_33])])).
% 0.21/0.50  fof(f214,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k1_xboole_0 = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | v1_funct_2(X1,k1_relat_1(X1),X0)) ) | ~spl2_33),
% 0.21/0.50    inference(equality_resolution,[],[f211])).
% 0.21/0.50  fof(f211,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k1_relat_1(X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_2(X2,X0,X1)) ) | ~spl2_33),
% 0.21/0.50    inference(avatar_component_clause,[],[f210])).
% 0.21/0.50  fof(f212,plain,(
% 0.21/0.50    spl2_33 | ~spl2_17 | ~spl2_25),
% 0.21/0.50    inference(avatar_split_clause,[],[f181,f168,f126,f210])).
% 0.21/0.50  fof(f126,plain,(
% 0.21/0.50    spl2_17 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.21/0.50  fof(f168,plain,(
% 0.21/0.50    spl2_25 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).
% 0.21/0.50  fof(f181,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k1_relat_1(X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_2(X2,X0,X1)) ) | (~spl2_17 | ~spl2_25)),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f180])).
% 0.21/0.50  fof(f180,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k1_relat_1(X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | (~spl2_17 | ~spl2_25)),
% 0.21/0.50    inference(superposition,[],[f169,f127])).
% 0.21/0.50  fof(f127,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl2_17),
% 0.21/0.50    inference(avatar_component_clause,[],[f126])).
% 0.21/0.50  fof(f169,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_2(X2,X0,X1)) ) | ~spl2_25),
% 0.21/0.50    inference(avatar_component_clause,[],[f168])).
% 0.21/0.50  fof(f196,plain,(
% 0.21/0.50    spl2_30 | ~spl2_7 | ~spl2_17 | ~spl2_22),
% 0.21/0.50    inference(avatar_split_clause,[],[f164,f147,f126,f77,f194])).
% 0.21/0.50  fof(f77,plain,(
% 0.21/0.50    spl2_7 <=> ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.50  fof(f147,plain,(
% 0.21/0.50    spl2_22 <=> ! [X1,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | v1_funct_2(X2,k1_xboole_0,X1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 0.21/0.50  fof(f164,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 != k1_relat_1(X1) | v1_funct_2(X1,k1_xboole_0,X0)) ) | (~spl2_7 | ~spl2_17 | ~spl2_22)),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f163])).
% 0.21/0.50  fof(f163,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 != k1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | v1_funct_2(X1,k1_xboole_0,X0)) ) | (~spl2_7 | ~spl2_17 | ~spl2_22)),
% 0.21/0.50    inference(forward_demodulation,[],[f162,f78])).
% 0.21/0.50  fof(f78,plain,(
% 0.21/0.50    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) ) | ~spl2_7),
% 0.21/0.50    inference(avatar_component_clause,[],[f77])).
% 0.21/0.50  fof(f162,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k1_xboole_0 != k1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | v1_funct_2(X1,k1_xboole_0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))) ) | (~spl2_17 | ~spl2_22)),
% 0.21/0.50    inference(superposition,[],[f148,f127])).
% 0.21/0.50  fof(f148,plain,(
% 0.21/0.50    ( ! [X2,X1] : (k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) | v1_funct_2(X2,k1_xboole_0,X1)) ) | ~spl2_22),
% 0.21/0.50    inference(avatar_component_clause,[],[f147])).
% 0.21/0.50  fof(f170,plain,(
% 0.21/0.50    spl2_25),
% 0.21/0.50    inference(avatar_split_clause,[],[f38,f168])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(flattening,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.50  fof(f149,plain,(
% 0.21/0.50    spl2_22),
% 0.21/0.50    inference(avatar_split_clause,[],[f50,f147])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | v1_funct_2(X2,k1_xboole_0,X1)) )),
% 0.21/0.50    inference(forward_demodulation,[],[f44,f42])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.21/0.50    inference(equality_resolution,[],[f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | v1_funct_2(X2,k1_xboole_0,X1)) )),
% 0.21/0.50    inference(equality_resolution,[],[f36])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  fof(f141,plain,(
% 0.21/0.50    ~spl2_19 | spl2_20 | ~spl2_4 | ~spl2_12),
% 0.21/0.50    inference(avatar_split_clause,[],[f129,f97,f66,f139,f136])).
% 0.21/0.50  fof(f97,plain,(
% 0.21/0.50    spl2_12 <=> ! [X1,X0,X2] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.21/0.50  fof(f129,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(X0,sK0) | ~v1_xboole_0(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) ) | (~spl2_4 | ~spl2_12)),
% 0.21/0.50    inference(resolution,[],[f121,f98])).
% 0.21/0.50  fof(f98,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1) | ~v1_xboole_0(X2)) ) | ~spl2_12),
% 0.21/0.50    inference(avatar_component_clause,[],[f97])).
% 0.21/0.50  fof(f128,plain,(
% 0.21/0.50    spl2_17),
% 0.21/0.50    inference(avatar_split_clause,[],[f32,f126])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.50  fof(f122,plain,(
% 0.21/0.50    spl2_4 | ~spl2_9 | ~spl2_13),
% 0.21/0.50    inference(avatar_split_clause,[],[f117,f102,f85,f66])).
% 0.21/0.50  fof(f85,plain,(
% 0.21/0.50    spl2_9 <=> ! [X1,X0] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.21/0.50  fof(f102,plain,(
% 0.21/0.50    spl2_13 <=> r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.21/0.50  fof(f117,plain,(
% 0.21/0.50    m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | (~spl2_9 | ~spl2_13)),
% 0.21/0.50    inference(resolution,[],[f103,f86])).
% 0.21/0.50  fof(f86,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) ) | ~spl2_9),
% 0.21/0.50    inference(avatar_component_clause,[],[f85])).
% 0.21/0.50  fof(f103,plain,(
% 0.21/0.50    r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) | ~spl2_13),
% 0.21/0.50    inference(avatar_component_clause,[],[f102])).
% 0.21/0.50  fof(f115,plain,(
% 0.21/0.50    spl2_15 | ~spl2_16),
% 0.21/0.50    inference(avatar_split_clause,[],[f52,f113,f110])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X0 | v1_funct_2(k1_xboole_0,X0,k1_xboole_0)) )),
% 0.21/0.50    inference(forward_demodulation,[],[f47,f41])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.50    inference(equality_resolution,[],[f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f3])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | k1_xboole_0 = X0 | v1_funct_2(k1_xboole_0,X0,k1_xboole_0)) )),
% 0.21/0.50    inference(equality_resolution,[],[f46])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | k1_xboole_0 = X0 | k1_xboole_0 != X2 | v1_funct_2(X2,X0,k1_xboole_0)) )),
% 0.21/0.50    inference(equality_resolution,[],[f34])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X1 | k1_xboole_0 = X0 | k1_xboole_0 != X2 | v1_funct_2(X2,X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  fof(f104,plain,(
% 0.21/0.50    spl2_13 | ~spl2_1 | ~spl2_11),
% 0.21/0.50    inference(avatar_split_clause,[],[f100,f93,f54,f102])).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    spl2_1 <=> v1_relat_1(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.50  fof(f93,plain,(
% 0.21/0.50    spl2_11 <=> ! [X0] : (~v1_relat_1(X0) | r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.21/0.51  fof(f100,plain,(
% 0.21/0.51    r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) | (~spl2_1 | ~spl2_11)),
% 0.21/0.51    inference(resolution,[],[f94,f55])).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    v1_relat_1(sK0) | ~spl2_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f54])).
% 0.21/0.51  fof(f94,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_relat_1(X0) | r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) ) | ~spl2_11),
% 0.21/0.51    inference(avatar_component_clause,[],[f93])).
% 0.21/0.51  fof(f99,plain,(
% 0.21/0.51    spl2_12),
% 0.21/0.51    inference(avatar_split_clause,[],[f40,f97])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 0.21/0.51  fof(f95,plain,(
% 0.21/0.51    spl2_11),
% 0.21/0.51    inference(avatar_split_clause,[],[f25,f93])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_relat_1(X0) | r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).
% 0.21/0.51  % (26972)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.51  fof(f87,plain,(
% 0.21/0.51    spl2_9),
% 0.21/0.51    inference(avatar_split_clause,[],[f27,f85])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.51  fof(f83,plain,(
% 0.21/0.51    spl2_8),
% 0.21/0.51    inference(avatar_split_clause,[],[f26,f81])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ( ! [X0] : (k1_xboole_0 = X0 | r2_hidden(sK1(X0),X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.21/0.51  fof(f79,plain,(
% 0.21/0.51    spl2_7),
% 0.21/0.51    inference(avatar_split_clause,[],[f42,f77])).
% 0.21/0.51  fof(f75,plain,(
% 0.21/0.51    spl2_6),
% 0.21/0.51    inference(avatar_split_clause,[],[f41,f73])).
% 0.21/0.51  fof(f71,plain,(
% 0.21/0.51    ~spl2_4 | ~spl2_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f48,f69,f66])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    ~v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | ~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))),
% 0.21/0.51    inference(subsumption_resolution,[],[f21,f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    v1_funct_1(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ? [X0] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f12])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ? [X0] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,negated_conjecture,(
% 0.21/0.51    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.21/0.51    inference(negated_conjecture,[],[f10])).
% 0.21/0.51  fof(f10,conjecture,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ~v1_funct_1(sK0) | ~v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | ~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))),
% 0.21/0.51    inference(cnf_transformation,[],[f13])).
% 0.21/0.51  fof(f64,plain,(
% 0.21/0.51    spl2_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f24,f62])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    v1_xboole_0(k1_xboole_0)),
% 0.21/0.51    inference(cnf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    v1_xboole_0(k1_xboole_0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    spl2_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f22,f54])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    v1_relat_1(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f13])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (26968)------------------------------
% 0.21/0.51  % (26968)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (26968)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (26968)Memory used [KB]: 10746
% 0.21/0.51  % (26968)Time elapsed: 0.089 s
% 0.21/0.51  % (26968)------------------------------
% 0.21/0.51  % (26968)------------------------------
% 0.21/0.51  % (26961)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.51  % (26964)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.51  % (26958)Success in time 0.15 s
%------------------------------------------------------------------------------
