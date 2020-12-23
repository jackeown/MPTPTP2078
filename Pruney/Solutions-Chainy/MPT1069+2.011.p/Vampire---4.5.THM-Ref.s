%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:43 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  240 ( 429 expanded)
%              Number of leaves         :   57 ( 189 expanded)
%              Depth                    :   11
%              Number of atoms          :  942 (1734 expanded)
%              Number of equality atoms :  101 ( 213 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f632,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f69,f73,f77,f81,f85,f89,f93,f97,f101,f105,f113,f117,f122,f126,f134,f138,f143,f147,f153,f157,f162,f166,f174,f182,f186,f198,f202,f231,f244,f257,f260,f263,f335,f349,f406,f418,f454,f501,f509,f524,f528,f556,f597,f631])).

fof(f631,plain,
    ( spl6_57
    | spl6_3
    | ~ spl6_24
    | ~ spl6_67
    | ~ spl6_68 ),
    inference(avatar_split_clause,[],[f601,f595,f499,f164,f75,f416])).

fof(f416,plain,
    ( spl6_57
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_57])])).

fof(f75,plain,
    ( spl6_3
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f164,plain,
    ( spl6_24
  <=> ! [X1,X0] :
        ( v1_xboole_0(X0)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k1_xboole_0,X1,X0)
        | v1_xboole_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f499,plain,
    ( spl6_67
  <=> v1_funct_2(k1_xboole_0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_67])])).

fof(f595,plain,
    ( spl6_68
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_68])])).

fof(f601,plain,
    ( v1_xboole_0(sK1)
    | spl6_3
    | ~ spl6_24
    | ~ spl6_67
    | ~ spl6_68 ),
    inference(subsumption_resolution,[],[f600,f500])).

fof(f500,plain,
    ( v1_funct_2(k1_xboole_0,sK1,sK2)
    | ~ spl6_67 ),
    inference(avatar_component_clause,[],[f499])).

fof(f600,plain,
    ( ~ v1_funct_2(k1_xboole_0,sK1,sK2)
    | v1_xboole_0(sK1)
    | spl6_3
    | ~ spl6_24
    | ~ spl6_68 ),
    inference(subsumption_resolution,[],[f598,f76])).

fof(f76,plain,
    ( ~ v1_xboole_0(sK2)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f75])).

fof(f598,plain,
    ( v1_xboole_0(sK2)
    | ~ v1_funct_2(k1_xboole_0,sK1,sK2)
    | v1_xboole_0(sK1)
    | ~ spl6_24
    | ~ spl6_68 ),
    inference(resolution,[],[f596,f165])).

fof(f165,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | v1_xboole_0(X0)
        | ~ v1_funct_2(k1_xboole_0,X1,X0)
        | v1_xboole_0(X1) )
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f164])).

fof(f596,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl6_68 ),
    inference(avatar_component_clause,[],[f595])).

fof(f597,plain,
    ( spl6_68
    | ~ spl6_8
    | ~ spl6_13
    | ~ spl6_37 ),
    inference(avatar_split_clause,[],[f571,f235,f115,f95,f595])).

fof(f95,plain,
    ( spl6_8
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f115,plain,
    ( spl6_13
  <=> ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f235,plain,
    ( spl6_37
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).

fof(f571,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl6_8
    | ~ spl6_13
    | ~ spl6_37 ),
    inference(backward_demodulation,[],[f96,f568])).

fof(f568,plain,
    ( k1_xboole_0 = sK3
    | ~ spl6_13
    | ~ spl6_37 ),
    inference(resolution,[],[f236,f116])).

fof(f116,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 )
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f115])).

fof(f236,plain,
    ( v1_xboole_0(sK3)
    | ~ spl6_37 ),
    inference(avatar_component_clause,[],[f235])).

fof(f96,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f95])).

fof(f556,plain,
    ( spl6_3
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_22
    | ~ spl6_65 ),
    inference(avatar_contradiction_clause,[],[f555])).

fof(f555,plain,
    ( $false
    | spl6_3
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_22
    | ~ spl6_65 ),
    inference(subsumption_resolution,[],[f537,f100])).

fof(f100,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl6_9
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f537,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl6_3
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_22
    | ~ spl6_65 ),
    inference(backward_demodulation,[],[f76,f536])).

fof(f536,plain,
    ( k1_xboole_0 = sK2
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_22
    | ~ spl6_65 ),
    inference(subsumption_resolution,[],[f535,f88])).

fof(f88,plain,
    ( v1_funct_2(sK3,sK1,sK2)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl6_6
  <=> v1_funct_2(sK3,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f535,plain,
    ( ~ v1_funct_2(sK3,sK1,sK2)
    | k1_xboole_0 = sK2
    | ~ spl6_8
    | ~ spl6_22
    | ~ spl6_65 ),
    inference(subsumption_resolution,[],[f534,f96])).

fof(f534,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(sK3,sK1,sK2)
    | k1_xboole_0 = sK2
    | ~ spl6_22
    | ~ spl6_65 ),
    inference(resolution,[],[f453,f156])).

fof(f156,plain,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4))
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f155])).

fof(f155,plain,
    ( spl6_22
  <=> r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f453,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relset_1(sK1,X0,sK3),k1_relat_1(sK4))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ v1_funct_2(sK3,sK1,X0)
        | k1_xboole_0 = X0 )
    | ~ spl6_65 ),
    inference(avatar_component_clause,[],[f452])).

fof(f452,plain,
    ( spl6_65
  <=> ! [X0] :
        ( ~ v1_funct_2(sK3,sK1,X0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ r1_tarski(k2_relset_1(sK1,X0,sK3),k1_relat_1(sK4))
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_65])])).

fof(f528,plain,
    ( spl6_51
    | spl6_52
    | ~ spl6_2
    | ~ spl6_26
    | spl6_41 ),
    inference(avatar_split_clause,[],[f455,f252,f172,f71,f328,f325])).

fof(f325,plain,
    ( spl6_51
  <=> k1_xboole_0 = k1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_51])])).

fof(f328,plain,
    ( spl6_52
  <=> ! [X0] :
        ( ~ v1_funct_2(sK3,X0,k1_relat_1(sK4))
        | ~ r2_hidden(sK5,X0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_relat_1(sK4)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_52])])).

fof(f71,plain,
    ( spl6_2
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f172,plain,
    ( spl6_26
  <=> ! [X1,X3,X0,X2] :
        ( ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,X0,X1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ r2_hidden(X2,X0)
        | k1_xboole_0 = X1
        | r2_hidden(k1_funct_1(X3,X2),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f252,plain,
    ( spl6_41
  <=> r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).

fof(f455,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK3,X0,k1_relat_1(sK4))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_relat_1(sK4))))
        | ~ r2_hidden(sK5,X0)
        | k1_xboole_0 = k1_relat_1(sK4) )
    | ~ spl6_2
    | ~ spl6_26
    | spl6_41 ),
    inference(subsumption_resolution,[],[f386,f72])).

fof(f72,plain,
    ( v1_funct_1(sK3)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f71])).

fof(f386,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK3,X0,k1_relat_1(sK4))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_relat_1(sK4))))
        | ~ r2_hidden(sK5,X0)
        | k1_xboole_0 = k1_relat_1(sK4)
        | ~ v1_funct_1(sK3) )
    | ~ spl6_26
    | spl6_41 ),
    inference(resolution,[],[f253,f173])).

fof(f173,plain,
    ( ! [X2,X0,X3,X1] :
        ( r2_hidden(k1_funct_1(X3,X2),X1)
        | ~ v1_funct_2(X3,X0,X1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ r2_hidden(X2,X0)
        | k1_xboole_0 = X1
        | ~ v1_funct_1(X3) )
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f172])).

fof(f253,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4))
    | spl6_41 ),
    inference(avatar_component_clause,[],[f252])).

fof(f524,plain,
    ( spl6_37
    | ~ spl6_38
    | ~ spl6_19
    | ~ spl6_31 ),
    inference(avatar_split_clause,[],[f393,f196,f141,f238,f235])).

fof(f238,plain,
    ( spl6_38
  <=> r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).

fof(f141,plain,
    ( spl6_19
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f196,plain,
    ( spl6_31
  <=> ! [X1] :
        ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),X1)
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).

fof(f393,plain,
    ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_xboole_0)
    | v1_xboole_0(sK3)
    | ~ spl6_19
    | ~ spl6_31 ),
    inference(resolution,[],[f197,f142])).

fof(f142,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
        | v1_xboole_0(X0) )
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f141])).

fof(f197,plain,
    ( ! [X1] :
        ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
        | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),X1) )
    | ~ spl6_31 ),
    inference(avatar_component_clause,[],[f196])).

fof(f509,plain,
    ( spl6_5
    | ~ spl6_13
    | ~ spl6_57 ),
    inference(avatar_contradiction_clause,[],[f508])).

fof(f508,plain,
    ( $false
    | spl6_5
    | ~ spl6_13
    | ~ spl6_57 ),
    inference(subsumption_resolution,[],[f506,f84])).

fof(f84,plain,
    ( k1_xboole_0 != sK1
    | spl6_5 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl6_5
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f506,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_13
    | ~ spl6_57 ),
    inference(resolution,[],[f417,f116])).

fof(f417,plain,
    ( v1_xboole_0(sK1)
    | ~ spl6_57 ),
    inference(avatar_component_clause,[],[f416])).

fof(f501,plain,
    ( spl6_67
    | ~ spl6_6
    | ~ spl6_13
    | ~ spl6_37 ),
    inference(avatar_split_clause,[],[f470,f235,f115,f87,f499])).

fof(f470,plain,
    ( v1_funct_2(k1_xboole_0,sK1,sK2)
    | ~ spl6_6
    | ~ spl6_13
    | ~ spl6_37 ),
    inference(backward_demodulation,[],[f88,f468])).

fof(f468,plain,
    ( k1_xboole_0 = sK3
    | ~ spl6_13
    | ~ spl6_37 ),
    inference(resolution,[],[f236,f116])).

fof(f454,plain,
    ( spl6_65
    | ~ spl6_2
    | ~ spl6_28
    | spl6_54 ),
    inference(avatar_split_clause,[],[f425,f401,f180,f71,f452])).

fof(f180,plain,
    ( spl6_28
  <=> ! [X1,X3,X0,X2] :
        ( ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,X0,X1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
        | k1_xboole_0 = X1
        | v1_funct_2(X3,X0,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f401,plain,
    ( spl6_54
  <=> v1_funct_2(sK3,sK1,k1_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_54])])).

fof(f425,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK3,sK1,X0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ r1_tarski(k2_relset_1(sK1,X0,sK3),k1_relat_1(sK4))
        | k1_xboole_0 = X0 )
    | ~ spl6_2
    | ~ spl6_28
    | spl6_54 ),
    inference(subsumption_resolution,[],[f424,f72])).

fof(f424,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK3,sK1,X0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ r1_tarski(k2_relset_1(sK1,X0,sK3),k1_relat_1(sK4))
        | k1_xboole_0 = X0
        | ~ v1_funct_1(sK3) )
    | ~ spl6_28
    | spl6_54 ),
    inference(resolution,[],[f402,f181])).

fof(f181,plain,
    ( ! [X2,X0,X3,X1] :
        ( v1_funct_2(X3,X0,X2)
        | ~ v1_funct_2(X3,X0,X1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
        | k1_xboole_0 = X1
        | ~ v1_funct_1(X3) )
    | ~ spl6_28 ),
    inference(avatar_component_clause,[],[f180])).

fof(f402,plain,
    ( ~ v1_funct_2(sK3,sK1,k1_relat_1(sK4))
    | spl6_54 ),
    inference(avatar_component_clause,[],[f401])).

fof(f418,plain,
    ( spl6_57
    | ~ spl6_4
    | ~ spl6_14
    | spl6_55 ),
    inference(avatar_split_clause,[],[f412,f404,f120,f79,f416])).

fof(f79,plain,
    ( spl6_4
  <=> m1_subset_1(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f120,plain,
    ( spl6_14
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,X1)
        | v1_xboole_0(X1)
        | r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f404,plain,
    ( spl6_55
  <=> r2_hidden(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_55])])).

fof(f412,plain,
    ( v1_xboole_0(sK1)
    | ~ spl6_4
    | ~ spl6_14
    | spl6_55 ),
    inference(subsumption_resolution,[],[f411,f80])).

fof(f80,plain,
    ( m1_subset_1(sK5,sK1)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f79])).

fof(f411,plain,
    ( v1_xboole_0(sK1)
    | ~ m1_subset_1(sK5,sK1)
    | ~ spl6_14
    | spl6_55 ),
    inference(resolution,[],[f405,f121])).

fof(f121,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,X1)
        | v1_xboole_0(X1)
        | ~ m1_subset_1(X0,X1) )
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f120])).

fof(f405,plain,
    ( ~ r2_hidden(sK5,sK1)
    | spl6_55 ),
    inference(avatar_component_clause,[],[f404])).

fof(f406,plain,
    ( ~ spl6_54
    | ~ spl6_55
    | ~ spl6_22
    | ~ spl6_31
    | ~ spl6_52 ),
    inference(avatar_split_clause,[],[f399,f328,f196,f155,f404,f401])).

fof(f399,plain,
    ( ~ r2_hidden(sK5,sK1)
    | ~ v1_funct_2(sK3,sK1,k1_relat_1(sK4))
    | ~ spl6_22
    | ~ spl6_31
    | ~ spl6_52 ),
    inference(subsumption_resolution,[],[f398,f156])).

fof(f398,plain,
    ( ~ r2_hidden(sK5,sK1)
    | ~ v1_funct_2(sK3,sK1,k1_relat_1(sK4))
    | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4))
    | ~ spl6_31
    | ~ spl6_52 ),
    inference(resolution,[],[f329,f197])).

fof(f329,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_relat_1(sK4))))
        | ~ r2_hidden(sK5,X0)
        | ~ v1_funct_2(sK3,X0,k1_relat_1(sK4)) )
    | ~ spl6_52 ),
    inference(avatar_component_clause,[],[f328])).

fof(f349,plain,
    ( spl6_3
    | ~ spl6_9
    | ~ spl6_30 ),
    inference(avatar_contradiction_clause,[],[f348])).

fof(f348,plain,
    ( $false
    | spl6_3
    | ~ spl6_9
    | ~ spl6_30 ),
    inference(subsumption_resolution,[],[f336,f100])).

fof(f336,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl6_3
    | ~ spl6_30 ),
    inference(backward_demodulation,[],[f76,f194])).

fof(f194,plain,
    ( k1_xboole_0 = sK2
    | ~ spl6_30 ),
    inference(avatar_component_clause,[],[f193])).

fof(f193,plain,
    ( spl6_30
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f335,plain,
    ( ~ spl6_22
    | spl6_38
    | ~ spl6_51 ),
    inference(avatar_contradiction_clause,[],[f334])).

fof(f334,plain,
    ( $false
    | ~ spl6_22
    | spl6_38
    | ~ spl6_51 ),
    inference(subsumption_resolution,[],[f331,f239])).

fof(f239,plain,
    ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_xboole_0)
    | spl6_38 ),
    inference(avatar_component_clause,[],[f238])).

fof(f331,plain,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_xboole_0)
    | ~ spl6_22
    | ~ spl6_51 ),
    inference(backward_demodulation,[],[f156,f326])).

fof(f326,plain,
    ( k1_xboole_0 = k1_relat_1(sK4)
    | ~ spl6_51 ),
    inference(avatar_component_clause,[],[f325])).

fof(f263,plain,
    ( ~ spl6_7
    | ~ spl6_17
    | spl6_42 ),
    inference(avatar_contradiction_clause,[],[f261])).

fof(f261,plain,
    ( $false
    | ~ spl6_7
    | ~ spl6_17
    | spl6_42 ),
    inference(unit_resulting_resolution,[],[f92,f256,f133])).

fof(f133,plain,
    ( ! [X2,X0,X1] :
        ( v5_relat_1(X2,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl6_17
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v5_relat_1(X2,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f256,plain,
    ( ~ v5_relat_1(sK4,sK0)
    | spl6_42 ),
    inference(avatar_component_clause,[],[f255])).

fof(f255,plain,
    ( spl6_42
  <=> v5_relat_1(sK4,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).

fof(f92,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl6_7
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f260,plain,
    ( ~ spl6_7
    | ~ spl6_15
    | spl6_40 ),
    inference(avatar_contradiction_clause,[],[f258])).

fof(f258,plain,
    ( $false
    | ~ spl6_7
    | ~ spl6_15
    | spl6_40 ),
    inference(unit_resulting_resolution,[],[f92,f250,f125])).

fof(f125,plain,
    ( ! [X2,X0,X1] :
        ( v1_relat_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl6_15
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f250,plain,
    ( ~ v1_relat_1(sK4)
    | spl6_40 ),
    inference(avatar_component_clause,[],[f249])).

fof(f249,plain,
    ( spl6_40
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).

fof(f257,plain,
    ( ~ spl6_40
    | ~ spl6_41
    | ~ spl6_42
    | ~ spl6_1
    | ~ spl6_23
    | spl6_39 ),
    inference(avatar_split_clause,[],[f247,f242,f160,f67,f255,f252,f249])).

fof(f67,plain,
    ( spl6_1
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f160,plain,
    ( spl6_23
  <=> ! [X1,X0,X2] :
        ( ~ v1_relat_1(X1)
        | ~ v5_relat_1(X1,X0)
        | ~ v1_funct_1(X1)
        | ~ r2_hidden(X2,k1_relat_1(X1))
        | k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f242,plain,
    ( spl6_39
  <=> k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).

fof(f247,plain,
    ( ~ v5_relat_1(sK4,sK0)
    | ~ r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | ~ spl6_1
    | ~ spl6_23
    | spl6_39 ),
    inference(subsumption_resolution,[],[f246,f68])).

fof(f68,plain,
    ( v1_funct_1(sK4)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f67])).

fof(f246,plain,
    ( ~ v5_relat_1(sK4,sK0)
    | ~ v1_funct_1(sK4)
    | ~ r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | ~ spl6_23
    | spl6_39 ),
    inference(trivial_inequality_removal,[],[f245])).

fof(f245,plain,
    ( k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | ~ v5_relat_1(sK4,sK0)
    | ~ v1_funct_1(sK4)
    | ~ r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | ~ spl6_23
    | spl6_39 ),
    inference(superposition,[],[f243,f161])).

fof(f161,plain,
    ( ! [X2,X0,X1] :
        ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
        | ~ v5_relat_1(X1,X0)
        | ~ v1_funct_1(X1)
        | ~ r2_hidden(X2,k1_relat_1(X1))
        | ~ v1_relat_1(X1) )
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f160])).

fof(f243,plain,
    ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | spl6_39 ),
    inference(avatar_component_clause,[],[f242])).

fof(f244,plain,
    ( ~ spl6_39
    | ~ spl6_4
    | spl6_12
    | ~ spl6_36 ),
    inference(avatar_split_clause,[],[f233,f229,f111,f79,f242])).

fof(f111,plain,
    ( spl6_12
  <=> k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f229,plain,
    ( spl6_36
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).

fof(f233,plain,
    ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | ~ spl6_4
    | spl6_12
    | ~ spl6_36 ),
    inference(backward_demodulation,[],[f112,f232])).

fof(f232,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | ~ spl6_4
    | ~ spl6_36 ),
    inference(resolution,[],[f230,f80])).

fof(f230,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0)) )
    | ~ spl6_36 ),
    inference(avatar_component_clause,[],[f229])).

fof(f112,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5))
    | spl6_12 ),
    inference(avatar_component_clause,[],[f111])).

fof(f231,plain,
    ( spl6_36
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_32 ),
    inference(avatar_split_clause,[],[f212,f200,f103,f95,f91,f87,f83,f75,f71,f67,f229])).

fof(f103,plain,
    ( spl6_10
  <=> r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f200,plain,
    ( spl6_32
  <=> ! [X1,X3,X5,X0,X2,X4] :
        ( v1_xboole_0(X2)
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,X1,X2)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ v1_funct_1(X4)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
        | ~ m1_subset_1(X5,X1)
        | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
        | k1_xboole_0 = X1
        | k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f212,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0)) )
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_32 ),
    inference(subsumption_resolution,[],[f211,f84])).

fof(f211,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | k1_xboole_0 = sK1
        | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0)) )
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_32 ),
    inference(subsumption_resolution,[],[f210,f76])).

fof(f210,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | v1_xboole_0(sK2)
        | k1_xboole_0 = sK1
        | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0)) )
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_32 ),
    inference(subsumption_resolution,[],[f209,f92])).

fof(f209,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
        | ~ m1_subset_1(X0,sK1)
        | v1_xboole_0(sK2)
        | k1_xboole_0 = sK1
        | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0)) )
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_32 ),
    inference(subsumption_resolution,[],[f208,f68])).

fof(f208,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK4)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
        | ~ m1_subset_1(X0,sK1)
        | v1_xboole_0(sK2)
        | k1_xboole_0 = sK1
        | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0)) )
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_32 ),
    inference(subsumption_resolution,[],[f207,f96])).

fof(f207,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
        | ~ v1_funct_1(sK4)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
        | ~ m1_subset_1(X0,sK1)
        | v1_xboole_0(sK2)
        | k1_xboole_0 = sK1
        | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0)) )
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_10
    | ~ spl6_32 ),
    inference(subsumption_resolution,[],[f206,f88])).

fof(f206,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK3,sK1,sK2)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
        | ~ v1_funct_1(sK4)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
        | ~ m1_subset_1(X0,sK1)
        | v1_xboole_0(sK2)
        | k1_xboole_0 = sK1
        | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0)) )
    | ~ spl6_2
    | ~ spl6_10
    | ~ spl6_32 ),
    inference(subsumption_resolution,[],[f203,f72])).

fof(f203,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK3)
        | ~ v1_funct_2(sK3,sK1,sK2)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
        | ~ v1_funct_1(sK4)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
        | ~ m1_subset_1(X0,sK1)
        | v1_xboole_0(sK2)
        | k1_xboole_0 = sK1
        | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0)) )
    | ~ spl6_10
    | ~ spl6_32 ),
    inference(resolution,[],[f201,f104])).

fof(f104,plain,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f103])).

fof(f201,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,X1,X2)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ v1_funct_1(X4)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
        | ~ m1_subset_1(X5,X1)
        | v1_xboole_0(X2)
        | k1_xboole_0 = X1
        | k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) )
    | ~ spl6_32 ),
    inference(avatar_component_clause,[],[f200])).

fof(f202,plain,(
    spl6_32 ),
    inference(avatar_split_clause,[],[f53,f200])).

fof(f53,plain,(
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
      | k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ! [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
                  | k1_xboole_0 = X1
                  | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  | ~ m1_subset_1(X5,X1) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              | ~ v1_funct_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X3,X1,X2)
          | ~ v1_funct_1(X3) )
      | v1_xboole_0(X2) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ! [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
                  | k1_xboole_0 = X1
                  | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  | ~ m1_subset_1(X5,X1) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              | ~ v1_funct_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X3,X1,X2)
          | ~ v1_funct_1(X3) )
      | v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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
                   => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
                      | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t185_funct_2)).

fof(f198,plain,
    ( spl6_30
    | spl6_31
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_29 ),
    inference(avatar_split_clause,[],[f191,f184,f95,f87,f71,f196,f193])).

fof(f184,plain,
    ( spl6_29
  <=> ! [X1,X3,X0,X2] :
        ( ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,X0,X1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
        | k1_xboole_0 = X1
        | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f191,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),X1)
        | k1_xboole_0 = sK2
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) )
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_29 ),
    inference(subsumption_resolution,[],[f190,f72])).

fof(f190,plain,
    ( ! [X1] :
        ( ~ v1_funct_1(sK3)
        | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),X1)
        | k1_xboole_0 = sK2
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) )
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_29 ),
    inference(subsumption_resolution,[],[f188,f88])).

fof(f188,plain,
    ( ! [X1] :
        ( ~ v1_funct_2(sK3,sK1,sK2)
        | ~ v1_funct_1(sK3)
        | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),X1)
        | k1_xboole_0 = sK2
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) )
    | ~ spl6_8
    | ~ spl6_29 ),
    inference(resolution,[],[f185,f96])).

fof(f185,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X3,X0,X1)
        | ~ v1_funct_1(X3)
        | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
        | k1_xboole_0 = X1
        | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) )
    | ~ spl6_29 ),
    inference(avatar_component_clause,[],[f184])).

fof(f186,plain,(
    spl6_29 ),
    inference(avatar_split_clause,[],[f62,f184])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | k1_xboole_0 = X1
      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(X3,X0,X2)
        & v1_funct_1(X3) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(X3,X0,X2)
        & v1_funct_1(X3) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(k2_relset_1(X0,X1,X3),X2)
       => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
            & v1_funct_2(X3,X0,X2)
            & v1_funct_1(X3) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_2)).

fof(f182,plain,(
    spl6_28 ),
    inference(avatar_split_clause,[],[f61,f180])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | k1_xboole_0 = X1
      | v1_funct_2(X3,X0,X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f174,plain,(
    spl6_26 ),
    inference(avatar_split_clause,[],[f58,f172])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X1
      | r2_hidden(k1_funct_1(X3,X2),X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

fof(f166,plain,
    ( spl6_24
    | ~ spl6_9
    | ~ spl6_21 ),
    inference(avatar_split_clause,[],[f158,f151,f99,f164])).

fof(f151,plain,
    ( spl6_21
  <=> ! [X1,X0,X2] :
        ( v1_xboole_0(X0)
        | v1_xboole_0(X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_xboole_0(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f158,plain,
    ( ! [X0,X1] :
        ( v1_xboole_0(X0)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k1_xboole_0,X1,X0)
        | v1_xboole_0(X1) )
    | ~ spl6_9
    | ~ spl6_21 ),
    inference(resolution,[],[f152,f100])).

fof(f152,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_xboole_0(X2)
        | v1_xboole_0(X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | v1_xboole_0(X0) )
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f151])).

fof(f162,plain,(
    spl6_23 ),
    inference(avatar_split_clause,[],[f52,f160])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_partfun1)).

fof(f157,plain,
    ( spl6_22
    | ~ spl6_7
    | ~ spl6_10
    | ~ spl6_20 ),
    inference(avatar_split_clause,[],[f149,f145,f103,f91,f155])).

fof(f145,plain,
    ( spl6_20
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f149,plain,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4))
    | ~ spl6_7
    | ~ spl6_10
    | ~ spl6_20 ),
    inference(subsumption_resolution,[],[f148,f92])).

fof(f148,plain,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ spl6_10
    | ~ spl6_20 ),
    inference(superposition,[],[f104,f146])).

fof(f146,plain,
    ( ! [X2,X0,X1] :
        ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f145])).

fof(f153,plain,(
    spl6_21 ),
    inference(avatar_split_clause,[],[f65,f151])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_xboole_0(X2) ) ),
    inference(subsumption_resolution,[],[f51,f47])).

fof(f47,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_funct_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_1)).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_funct_2(X2,X0,X1)
            & ~ v1_xboole_0(X2)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_funct_2(X2,X0,X1)
            & ~ v1_xboole_0(X2)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_funct_2(X2,X0,X1)
              & ~ v1_xboole_0(X2)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc6_funct_2)).

fof(f147,plain,(
    spl6_20 ),
    inference(avatar_split_clause,[],[f55,f145])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f143,plain,
    ( spl6_19
    | ~ spl6_9
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f139,f136,f99,f141])).

fof(f136,plain,
    ( spl6_18
  <=> ! [X1,X0,X2] :
        ( ~ v1_xboole_0(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | v1_xboole_0(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f139,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
        | v1_xboole_0(X0) )
    | ~ spl6_9
    | ~ spl6_18 ),
    inference(resolution,[],[f137,f100])).

fof(f137,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_xboole_0(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | v1_xboole_0(X2) )
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f136])).

fof(f138,plain,(
    spl6_18 ),
    inference(avatar_split_clause,[],[f49,f136])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

fof(f134,plain,(
    spl6_17 ),
    inference(avatar_split_clause,[],[f57,f132])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f126,plain,(
    spl6_15 ),
    inference(avatar_split_clause,[],[f54,f124])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f122,plain,(
    spl6_14 ),
    inference(avatar_split_clause,[],[f50,f120])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f117,plain,(
    spl6_13 ),
    inference(avatar_split_clause,[],[f48,f115])).

fof(f48,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f113,plain,(
    ~ spl6_12 ),
    inference(avatar_split_clause,[],[f39,f111])).

fof(f39,plain,(
    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(X2) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
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
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
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

fof(f105,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f37,f103])).

fof(f37,plain,(
    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
    inference(cnf_transformation,[],[f17])).

fof(f101,plain,(
    spl6_9 ),
    inference(avatar_split_clause,[],[f46,f99])).

fof(f46,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f97,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f44,f95])).

fof(f44,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f17])).

fof(f93,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f41,f91])).

fof(f41,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f89,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f43,f87])).

fof(f43,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f85,plain,(
    ~ spl6_5 ),
    inference(avatar_split_clause,[],[f38,f83])).

fof(f38,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f17])).

fof(f81,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f36,f79])).

fof(f36,plain,(
    m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f77,plain,(
    ~ spl6_3 ),
    inference(avatar_split_clause,[],[f45,f75])).

fof(f45,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f73,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f42,f71])).

fof(f42,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f17])).

fof(f69,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f40,f67])).

fof(f40,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:08:50 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.44  % (31991)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.46  % (31991)Refutation found. Thanks to Tanya!
% 0.22/0.46  % SZS status Theorem for theBenchmark
% 0.22/0.46  % SZS output start Proof for theBenchmark
% 0.22/0.46  fof(f632,plain,(
% 0.22/0.46    $false),
% 0.22/0.46    inference(avatar_sat_refutation,[],[f69,f73,f77,f81,f85,f89,f93,f97,f101,f105,f113,f117,f122,f126,f134,f138,f143,f147,f153,f157,f162,f166,f174,f182,f186,f198,f202,f231,f244,f257,f260,f263,f335,f349,f406,f418,f454,f501,f509,f524,f528,f556,f597,f631])).
% 0.22/0.46  fof(f631,plain,(
% 0.22/0.46    spl6_57 | spl6_3 | ~spl6_24 | ~spl6_67 | ~spl6_68),
% 0.22/0.46    inference(avatar_split_clause,[],[f601,f595,f499,f164,f75,f416])).
% 0.22/0.46  fof(f416,plain,(
% 0.22/0.46    spl6_57 <=> v1_xboole_0(sK1)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_57])])).
% 0.22/0.46  fof(f75,plain,(
% 0.22/0.46    spl6_3 <=> v1_xboole_0(sK2)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.22/0.46  fof(f164,plain,(
% 0.22/0.46    spl6_24 <=> ! [X1,X0] : (v1_xboole_0(X0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k1_xboole_0,X1,X0) | v1_xboole_0(X1))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 0.22/0.46  fof(f499,plain,(
% 0.22/0.46    spl6_67 <=> v1_funct_2(k1_xboole_0,sK1,sK2)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_67])])).
% 0.22/0.46  fof(f595,plain,(
% 0.22/0.46    spl6_68 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_68])])).
% 0.22/0.46  fof(f601,plain,(
% 0.22/0.46    v1_xboole_0(sK1) | (spl6_3 | ~spl6_24 | ~spl6_67 | ~spl6_68)),
% 0.22/0.46    inference(subsumption_resolution,[],[f600,f500])).
% 0.22/0.46  fof(f500,plain,(
% 0.22/0.46    v1_funct_2(k1_xboole_0,sK1,sK2) | ~spl6_67),
% 0.22/0.46    inference(avatar_component_clause,[],[f499])).
% 0.22/0.46  fof(f600,plain,(
% 0.22/0.46    ~v1_funct_2(k1_xboole_0,sK1,sK2) | v1_xboole_0(sK1) | (spl6_3 | ~spl6_24 | ~spl6_68)),
% 0.22/0.46    inference(subsumption_resolution,[],[f598,f76])).
% 0.22/0.46  fof(f76,plain,(
% 0.22/0.46    ~v1_xboole_0(sK2) | spl6_3),
% 0.22/0.46    inference(avatar_component_clause,[],[f75])).
% 0.22/0.46  fof(f598,plain,(
% 0.22/0.46    v1_xboole_0(sK2) | ~v1_funct_2(k1_xboole_0,sK1,sK2) | v1_xboole_0(sK1) | (~spl6_24 | ~spl6_68)),
% 0.22/0.46    inference(resolution,[],[f596,f165])).
% 0.22/0.46  fof(f165,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_xboole_0(X0) | ~v1_funct_2(k1_xboole_0,X1,X0) | v1_xboole_0(X1)) ) | ~spl6_24),
% 0.22/0.46    inference(avatar_component_clause,[],[f164])).
% 0.22/0.46  fof(f596,plain,(
% 0.22/0.46    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl6_68),
% 0.22/0.46    inference(avatar_component_clause,[],[f595])).
% 0.22/0.46  fof(f597,plain,(
% 0.22/0.46    spl6_68 | ~spl6_8 | ~spl6_13 | ~spl6_37),
% 0.22/0.46    inference(avatar_split_clause,[],[f571,f235,f115,f95,f595])).
% 0.22/0.46  fof(f95,plain,(
% 0.22/0.46    spl6_8 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.22/0.46  fof(f115,plain,(
% 0.22/0.46    spl6_13 <=> ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.22/0.46  fof(f235,plain,(
% 0.22/0.46    spl6_37 <=> v1_xboole_0(sK3)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).
% 0.22/0.46  fof(f571,plain,(
% 0.22/0.46    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | (~spl6_8 | ~spl6_13 | ~spl6_37)),
% 0.22/0.46    inference(backward_demodulation,[],[f96,f568])).
% 0.22/0.46  fof(f568,plain,(
% 0.22/0.46    k1_xboole_0 = sK3 | (~spl6_13 | ~spl6_37)),
% 0.22/0.46    inference(resolution,[],[f236,f116])).
% 0.22/0.46  fof(f116,plain,(
% 0.22/0.46    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) ) | ~spl6_13),
% 0.22/0.46    inference(avatar_component_clause,[],[f115])).
% 0.22/0.46  fof(f236,plain,(
% 0.22/0.46    v1_xboole_0(sK3) | ~spl6_37),
% 0.22/0.46    inference(avatar_component_clause,[],[f235])).
% 0.22/0.46  fof(f96,plain,(
% 0.22/0.46    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl6_8),
% 0.22/0.46    inference(avatar_component_clause,[],[f95])).
% 0.22/0.46  fof(f556,plain,(
% 0.22/0.46    spl6_3 | ~spl6_6 | ~spl6_8 | ~spl6_9 | ~spl6_22 | ~spl6_65),
% 0.22/0.46    inference(avatar_contradiction_clause,[],[f555])).
% 0.22/0.46  fof(f555,plain,(
% 0.22/0.46    $false | (spl6_3 | ~spl6_6 | ~spl6_8 | ~spl6_9 | ~spl6_22 | ~spl6_65)),
% 0.22/0.46    inference(subsumption_resolution,[],[f537,f100])).
% 0.22/0.46  fof(f100,plain,(
% 0.22/0.46    v1_xboole_0(k1_xboole_0) | ~spl6_9),
% 0.22/0.46    inference(avatar_component_clause,[],[f99])).
% 0.22/0.46  fof(f99,plain,(
% 0.22/0.46    spl6_9 <=> v1_xboole_0(k1_xboole_0)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.22/0.46  fof(f537,plain,(
% 0.22/0.46    ~v1_xboole_0(k1_xboole_0) | (spl6_3 | ~spl6_6 | ~spl6_8 | ~spl6_22 | ~spl6_65)),
% 0.22/0.46    inference(backward_demodulation,[],[f76,f536])).
% 0.22/0.46  fof(f536,plain,(
% 0.22/0.46    k1_xboole_0 = sK2 | (~spl6_6 | ~spl6_8 | ~spl6_22 | ~spl6_65)),
% 0.22/0.46    inference(subsumption_resolution,[],[f535,f88])).
% 0.22/0.46  fof(f88,plain,(
% 0.22/0.46    v1_funct_2(sK3,sK1,sK2) | ~spl6_6),
% 0.22/0.46    inference(avatar_component_clause,[],[f87])).
% 0.22/0.46  fof(f87,plain,(
% 0.22/0.46    spl6_6 <=> v1_funct_2(sK3,sK1,sK2)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.22/0.46  fof(f535,plain,(
% 0.22/0.46    ~v1_funct_2(sK3,sK1,sK2) | k1_xboole_0 = sK2 | (~spl6_8 | ~spl6_22 | ~spl6_65)),
% 0.22/0.46    inference(subsumption_resolution,[],[f534,f96])).
% 0.22/0.46  fof(f534,plain,(
% 0.22/0.46    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(sK3,sK1,sK2) | k1_xboole_0 = sK2 | (~spl6_22 | ~spl6_65)),
% 0.22/0.46    inference(resolution,[],[f453,f156])).
% 0.22/0.46  fof(f156,plain,(
% 0.22/0.46    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4)) | ~spl6_22),
% 0.22/0.46    inference(avatar_component_clause,[],[f155])).
% 0.22/0.46  fof(f155,plain,(
% 0.22/0.46    spl6_22 <=> r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 0.22/0.46  fof(f453,plain,(
% 0.22/0.46    ( ! [X0] : (~r1_tarski(k2_relset_1(sK1,X0,sK3),k1_relat_1(sK4)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(sK3,sK1,X0) | k1_xboole_0 = X0) ) | ~spl6_65),
% 0.22/0.46    inference(avatar_component_clause,[],[f452])).
% 0.22/0.46  fof(f452,plain,(
% 0.22/0.46    spl6_65 <=> ! [X0] : (~v1_funct_2(sK3,sK1,X0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~r1_tarski(k2_relset_1(sK1,X0,sK3),k1_relat_1(sK4)) | k1_xboole_0 = X0)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_65])])).
% 0.22/0.46  fof(f528,plain,(
% 0.22/0.46    spl6_51 | spl6_52 | ~spl6_2 | ~spl6_26 | spl6_41),
% 0.22/0.46    inference(avatar_split_clause,[],[f455,f252,f172,f71,f328,f325])).
% 0.22/0.46  fof(f325,plain,(
% 0.22/0.46    spl6_51 <=> k1_xboole_0 = k1_relat_1(sK4)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_51])])).
% 0.22/0.46  fof(f328,plain,(
% 0.22/0.46    spl6_52 <=> ! [X0] : (~v1_funct_2(sK3,X0,k1_relat_1(sK4)) | ~r2_hidden(sK5,X0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_relat_1(sK4)))))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_52])])).
% 0.22/0.46  fof(f71,plain,(
% 0.22/0.46    spl6_2 <=> v1_funct_1(sK3)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.22/0.46  fof(f172,plain,(
% 0.22/0.46    spl6_26 <=> ! [X1,X3,X0,X2] : (~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X2,X0) | k1_xboole_0 = X1 | r2_hidden(k1_funct_1(X3,X2),X1))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).
% 0.22/0.46  fof(f252,plain,(
% 0.22/0.46    spl6_41 <=> r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).
% 0.22/0.46  fof(f455,plain,(
% 0.22/0.46    ( ! [X0] : (~v1_funct_2(sK3,X0,k1_relat_1(sK4)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_relat_1(sK4)))) | ~r2_hidden(sK5,X0) | k1_xboole_0 = k1_relat_1(sK4)) ) | (~spl6_2 | ~spl6_26 | spl6_41)),
% 0.22/0.46    inference(subsumption_resolution,[],[f386,f72])).
% 0.22/0.46  fof(f72,plain,(
% 0.22/0.46    v1_funct_1(sK3) | ~spl6_2),
% 0.22/0.46    inference(avatar_component_clause,[],[f71])).
% 0.22/0.46  fof(f386,plain,(
% 0.22/0.46    ( ! [X0] : (~v1_funct_2(sK3,X0,k1_relat_1(sK4)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_relat_1(sK4)))) | ~r2_hidden(sK5,X0) | k1_xboole_0 = k1_relat_1(sK4) | ~v1_funct_1(sK3)) ) | (~spl6_26 | spl6_41)),
% 0.22/0.46    inference(resolution,[],[f253,f173])).
% 0.22/0.46  fof(f173,plain,(
% 0.22/0.46    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),X1) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X2,X0) | k1_xboole_0 = X1 | ~v1_funct_1(X3)) ) | ~spl6_26),
% 0.22/0.46    inference(avatar_component_clause,[],[f172])).
% 0.22/0.46  fof(f253,plain,(
% 0.22/0.46    ~r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4)) | spl6_41),
% 0.22/0.46    inference(avatar_component_clause,[],[f252])).
% 0.22/0.46  fof(f524,plain,(
% 0.22/0.46    spl6_37 | ~spl6_38 | ~spl6_19 | ~spl6_31),
% 0.22/0.46    inference(avatar_split_clause,[],[f393,f196,f141,f238,f235])).
% 0.22/0.46  fof(f238,plain,(
% 0.22/0.46    spl6_38 <=> r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_xboole_0)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).
% 0.22/0.46  fof(f141,plain,(
% 0.22/0.46    spl6_19 <=> ! [X1,X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) | v1_xboole_0(X0))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 0.22/0.46  fof(f196,plain,(
% 0.22/0.46    spl6_31 <=> ! [X1] : (~r1_tarski(k2_relset_1(sK1,sK2,sK3),X1) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).
% 0.22/0.46  fof(f393,plain,(
% 0.22/0.46    ~r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_xboole_0) | v1_xboole_0(sK3) | (~spl6_19 | ~spl6_31)),
% 0.22/0.46    inference(resolution,[],[f197,f142])).
% 0.22/0.46  fof(f142,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) | v1_xboole_0(X0)) ) | ~spl6_19),
% 0.22/0.46    inference(avatar_component_clause,[],[f141])).
% 0.22/0.46  fof(f197,plain,(
% 0.22/0.46    ( ! [X1] : (m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~r1_tarski(k2_relset_1(sK1,sK2,sK3),X1)) ) | ~spl6_31),
% 0.22/0.46    inference(avatar_component_clause,[],[f196])).
% 0.22/0.46  fof(f509,plain,(
% 0.22/0.46    spl6_5 | ~spl6_13 | ~spl6_57),
% 0.22/0.46    inference(avatar_contradiction_clause,[],[f508])).
% 0.22/0.46  fof(f508,plain,(
% 0.22/0.46    $false | (spl6_5 | ~spl6_13 | ~spl6_57)),
% 0.22/0.46    inference(subsumption_resolution,[],[f506,f84])).
% 0.22/0.46  fof(f84,plain,(
% 0.22/0.46    k1_xboole_0 != sK1 | spl6_5),
% 0.22/0.46    inference(avatar_component_clause,[],[f83])).
% 0.22/0.46  fof(f83,plain,(
% 0.22/0.46    spl6_5 <=> k1_xboole_0 = sK1),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.22/0.46  fof(f506,plain,(
% 0.22/0.46    k1_xboole_0 = sK1 | (~spl6_13 | ~spl6_57)),
% 0.22/0.46    inference(resolution,[],[f417,f116])).
% 0.22/0.46  fof(f417,plain,(
% 0.22/0.46    v1_xboole_0(sK1) | ~spl6_57),
% 0.22/0.46    inference(avatar_component_clause,[],[f416])).
% 0.22/0.46  fof(f501,plain,(
% 0.22/0.46    spl6_67 | ~spl6_6 | ~spl6_13 | ~spl6_37),
% 0.22/0.46    inference(avatar_split_clause,[],[f470,f235,f115,f87,f499])).
% 0.22/0.46  fof(f470,plain,(
% 0.22/0.46    v1_funct_2(k1_xboole_0,sK1,sK2) | (~spl6_6 | ~spl6_13 | ~spl6_37)),
% 0.22/0.46    inference(backward_demodulation,[],[f88,f468])).
% 0.22/0.46  fof(f468,plain,(
% 0.22/0.46    k1_xboole_0 = sK3 | (~spl6_13 | ~spl6_37)),
% 0.22/0.46    inference(resolution,[],[f236,f116])).
% 0.22/0.46  fof(f454,plain,(
% 0.22/0.46    spl6_65 | ~spl6_2 | ~spl6_28 | spl6_54),
% 0.22/0.46    inference(avatar_split_clause,[],[f425,f401,f180,f71,f452])).
% 0.22/0.46  fof(f180,plain,(
% 0.22/0.46    spl6_28 <=> ! [X1,X3,X0,X2] : (~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | k1_xboole_0 = X1 | v1_funct_2(X3,X0,X2))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).
% 0.22/0.46  fof(f401,plain,(
% 0.22/0.46    spl6_54 <=> v1_funct_2(sK3,sK1,k1_relat_1(sK4))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_54])])).
% 0.22/0.46  fof(f425,plain,(
% 0.22/0.46    ( ! [X0] : (~v1_funct_2(sK3,sK1,X0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~r1_tarski(k2_relset_1(sK1,X0,sK3),k1_relat_1(sK4)) | k1_xboole_0 = X0) ) | (~spl6_2 | ~spl6_28 | spl6_54)),
% 0.22/0.46    inference(subsumption_resolution,[],[f424,f72])).
% 0.22/0.46  fof(f424,plain,(
% 0.22/0.46    ( ! [X0] : (~v1_funct_2(sK3,sK1,X0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~r1_tarski(k2_relset_1(sK1,X0,sK3),k1_relat_1(sK4)) | k1_xboole_0 = X0 | ~v1_funct_1(sK3)) ) | (~spl6_28 | spl6_54)),
% 0.22/0.46    inference(resolution,[],[f402,f181])).
% 0.22/0.46  fof(f181,plain,(
% 0.22/0.46    ( ! [X2,X0,X3,X1] : (v1_funct_2(X3,X0,X2) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | k1_xboole_0 = X1 | ~v1_funct_1(X3)) ) | ~spl6_28),
% 0.22/0.46    inference(avatar_component_clause,[],[f180])).
% 0.22/0.46  fof(f402,plain,(
% 0.22/0.46    ~v1_funct_2(sK3,sK1,k1_relat_1(sK4)) | spl6_54),
% 0.22/0.46    inference(avatar_component_clause,[],[f401])).
% 0.22/0.46  fof(f418,plain,(
% 0.22/0.46    spl6_57 | ~spl6_4 | ~spl6_14 | spl6_55),
% 0.22/0.46    inference(avatar_split_clause,[],[f412,f404,f120,f79,f416])).
% 0.22/0.46  fof(f79,plain,(
% 0.22/0.46    spl6_4 <=> m1_subset_1(sK5,sK1)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.22/0.46  fof(f120,plain,(
% 0.22/0.46    spl6_14 <=> ! [X1,X0] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 0.22/0.46  fof(f404,plain,(
% 0.22/0.46    spl6_55 <=> r2_hidden(sK5,sK1)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl6_55])])).
% 0.22/0.46  fof(f412,plain,(
% 0.22/0.46    v1_xboole_0(sK1) | (~spl6_4 | ~spl6_14 | spl6_55)),
% 0.22/0.46    inference(subsumption_resolution,[],[f411,f80])).
% 0.22/0.46  fof(f80,plain,(
% 0.22/0.46    m1_subset_1(sK5,sK1) | ~spl6_4),
% 0.22/0.46    inference(avatar_component_clause,[],[f79])).
% 0.22/0.46  fof(f411,plain,(
% 0.22/0.46    v1_xboole_0(sK1) | ~m1_subset_1(sK5,sK1) | (~spl6_14 | spl6_55)),
% 0.22/0.46    inference(resolution,[],[f405,f121])).
% 0.22/0.46  fof(f121,plain,(
% 0.22/0.46    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) ) | ~spl6_14),
% 0.22/0.46    inference(avatar_component_clause,[],[f120])).
% 0.22/0.46  fof(f405,plain,(
% 0.22/0.46    ~r2_hidden(sK5,sK1) | spl6_55),
% 0.22/0.46    inference(avatar_component_clause,[],[f404])).
% 0.22/0.46  fof(f406,plain,(
% 0.22/0.46    ~spl6_54 | ~spl6_55 | ~spl6_22 | ~spl6_31 | ~spl6_52),
% 0.22/0.46    inference(avatar_split_clause,[],[f399,f328,f196,f155,f404,f401])).
% 0.22/0.46  fof(f399,plain,(
% 0.22/0.46    ~r2_hidden(sK5,sK1) | ~v1_funct_2(sK3,sK1,k1_relat_1(sK4)) | (~spl6_22 | ~spl6_31 | ~spl6_52)),
% 0.22/0.46    inference(subsumption_resolution,[],[f398,f156])).
% 0.22/0.46  fof(f398,plain,(
% 0.22/0.46    ~r2_hidden(sK5,sK1) | ~v1_funct_2(sK3,sK1,k1_relat_1(sK4)) | ~r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4)) | (~spl6_31 | ~spl6_52)),
% 0.22/0.46    inference(resolution,[],[f329,f197])).
% 0.22/0.46  fof(f329,plain,(
% 0.22/0.46    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_relat_1(sK4)))) | ~r2_hidden(sK5,X0) | ~v1_funct_2(sK3,X0,k1_relat_1(sK4))) ) | ~spl6_52),
% 0.22/0.46    inference(avatar_component_clause,[],[f328])).
% 0.22/0.46  fof(f349,plain,(
% 0.22/0.46    spl6_3 | ~spl6_9 | ~spl6_30),
% 0.22/0.46    inference(avatar_contradiction_clause,[],[f348])).
% 0.22/0.46  fof(f348,plain,(
% 0.22/0.46    $false | (spl6_3 | ~spl6_9 | ~spl6_30)),
% 0.22/0.46    inference(subsumption_resolution,[],[f336,f100])).
% 0.22/0.47  fof(f336,plain,(
% 0.22/0.47    ~v1_xboole_0(k1_xboole_0) | (spl6_3 | ~spl6_30)),
% 0.22/0.47    inference(backward_demodulation,[],[f76,f194])).
% 0.22/0.47  fof(f194,plain,(
% 0.22/0.47    k1_xboole_0 = sK2 | ~spl6_30),
% 0.22/0.47    inference(avatar_component_clause,[],[f193])).
% 0.22/0.47  fof(f193,plain,(
% 0.22/0.47    spl6_30 <=> k1_xboole_0 = sK2),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).
% 0.22/0.47  fof(f335,plain,(
% 0.22/0.47    ~spl6_22 | spl6_38 | ~spl6_51),
% 0.22/0.47    inference(avatar_contradiction_clause,[],[f334])).
% 0.22/0.47  fof(f334,plain,(
% 0.22/0.47    $false | (~spl6_22 | spl6_38 | ~spl6_51)),
% 0.22/0.47    inference(subsumption_resolution,[],[f331,f239])).
% 0.22/0.47  fof(f239,plain,(
% 0.22/0.47    ~r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_xboole_0) | spl6_38),
% 0.22/0.47    inference(avatar_component_clause,[],[f238])).
% 0.22/0.47  fof(f331,plain,(
% 0.22/0.47    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_xboole_0) | (~spl6_22 | ~spl6_51)),
% 0.22/0.47    inference(backward_demodulation,[],[f156,f326])).
% 0.22/0.47  fof(f326,plain,(
% 0.22/0.47    k1_xboole_0 = k1_relat_1(sK4) | ~spl6_51),
% 0.22/0.47    inference(avatar_component_clause,[],[f325])).
% 0.22/0.47  fof(f263,plain,(
% 0.22/0.47    ~spl6_7 | ~spl6_17 | spl6_42),
% 0.22/0.47    inference(avatar_contradiction_clause,[],[f261])).
% 0.22/0.47  fof(f261,plain,(
% 0.22/0.47    $false | (~spl6_7 | ~spl6_17 | spl6_42)),
% 0.22/0.47    inference(unit_resulting_resolution,[],[f92,f256,f133])).
% 0.22/0.47  fof(f133,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl6_17),
% 0.22/0.47    inference(avatar_component_clause,[],[f132])).
% 0.22/0.47  fof(f132,plain,(
% 0.22/0.47    spl6_17 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 0.22/0.47  fof(f256,plain,(
% 0.22/0.47    ~v5_relat_1(sK4,sK0) | spl6_42),
% 0.22/0.47    inference(avatar_component_clause,[],[f255])).
% 0.22/0.47  fof(f255,plain,(
% 0.22/0.47    spl6_42 <=> v5_relat_1(sK4,sK0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).
% 0.22/0.47  fof(f92,plain,(
% 0.22/0.47    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~spl6_7),
% 0.22/0.47    inference(avatar_component_clause,[],[f91])).
% 0.22/0.47  fof(f91,plain,(
% 0.22/0.47    spl6_7 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.22/0.47  fof(f260,plain,(
% 0.22/0.47    ~spl6_7 | ~spl6_15 | spl6_40),
% 0.22/0.47    inference(avatar_contradiction_clause,[],[f258])).
% 0.22/0.47  fof(f258,plain,(
% 0.22/0.47    $false | (~spl6_7 | ~spl6_15 | spl6_40)),
% 0.22/0.47    inference(unit_resulting_resolution,[],[f92,f250,f125])).
% 0.22/0.47  fof(f125,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl6_15),
% 0.22/0.47    inference(avatar_component_clause,[],[f124])).
% 0.22/0.47  fof(f124,plain,(
% 0.22/0.47    spl6_15 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.22/0.47  fof(f250,plain,(
% 0.22/0.47    ~v1_relat_1(sK4) | spl6_40),
% 0.22/0.47    inference(avatar_component_clause,[],[f249])).
% 0.22/0.47  fof(f249,plain,(
% 0.22/0.47    spl6_40 <=> v1_relat_1(sK4)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).
% 0.22/0.47  fof(f257,plain,(
% 0.22/0.47    ~spl6_40 | ~spl6_41 | ~spl6_42 | ~spl6_1 | ~spl6_23 | spl6_39),
% 0.22/0.47    inference(avatar_split_clause,[],[f247,f242,f160,f67,f255,f252,f249])).
% 0.22/0.47  fof(f67,plain,(
% 0.22/0.47    spl6_1 <=> v1_funct_1(sK4)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.22/0.47  fof(f160,plain,(
% 0.22/0.47    spl6_23 <=> ! [X1,X0,X2] : (~v1_relat_1(X1) | ~v5_relat_1(X1,X0) | ~v1_funct_1(X1) | ~r2_hidden(X2,k1_relat_1(X1)) | k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 0.22/0.47  fof(f242,plain,(
% 0.22/0.47    spl6_39 <=> k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).
% 0.22/0.47  fof(f247,plain,(
% 0.22/0.47    ~v5_relat_1(sK4,sK0) | ~r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4)) | ~v1_relat_1(sK4) | (~spl6_1 | ~spl6_23 | spl6_39)),
% 0.22/0.47    inference(subsumption_resolution,[],[f246,f68])).
% 0.22/0.47  fof(f68,plain,(
% 0.22/0.47    v1_funct_1(sK4) | ~spl6_1),
% 0.22/0.47    inference(avatar_component_clause,[],[f67])).
% 0.22/0.47  fof(f246,plain,(
% 0.22/0.47    ~v5_relat_1(sK4,sK0) | ~v1_funct_1(sK4) | ~r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4)) | ~v1_relat_1(sK4) | (~spl6_23 | spl6_39)),
% 0.22/0.47    inference(trivial_inequality_removal,[],[f245])).
% 0.22/0.47  fof(f245,plain,(
% 0.22/0.47    k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | ~v5_relat_1(sK4,sK0) | ~v1_funct_1(sK4) | ~r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4)) | ~v1_relat_1(sK4) | (~spl6_23 | spl6_39)),
% 0.22/0.47    inference(superposition,[],[f243,f161])).
% 0.22/0.47  fof(f161,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~v5_relat_1(X1,X0) | ~v1_funct_1(X1) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_relat_1(X1)) ) | ~spl6_23),
% 0.22/0.47    inference(avatar_component_clause,[],[f160])).
% 0.22/0.47  fof(f243,plain,(
% 0.22/0.47    k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | spl6_39),
% 0.22/0.47    inference(avatar_component_clause,[],[f242])).
% 0.22/0.47  fof(f244,plain,(
% 0.22/0.47    ~spl6_39 | ~spl6_4 | spl6_12 | ~spl6_36),
% 0.22/0.47    inference(avatar_split_clause,[],[f233,f229,f111,f79,f242])).
% 0.22/0.47  fof(f111,plain,(
% 0.22/0.47    spl6_12 <=> k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.22/0.47  fof(f229,plain,(
% 0.22/0.47    spl6_36 <=> ! [X0] : (~m1_subset_1(X0,sK1) | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0)))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).
% 0.22/0.47  fof(f233,plain,(
% 0.22/0.47    k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | (~spl6_4 | spl6_12 | ~spl6_36)),
% 0.22/0.47    inference(backward_demodulation,[],[f112,f232])).
% 0.22/0.47  fof(f232,plain,(
% 0.22/0.47    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | (~spl6_4 | ~spl6_36)),
% 0.22/0.47    inference(resolution,[],[f230,f80])).
% 0.22/0.47  fof(f230,plain,(
% 0.22/0.47    ( ! [X0] : (~m1_subset_1(X0,sK1) | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))) ) | ~spl6_36),
% 0.22/0.47    inference(avatar_component_clause,[],[f229])).
% 0.22/0.47  fof(f112,plain,(
% 0.22/0.47    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) | spl6_12),
% 0.22/0.47    inference(avatar_component_clause,[],[f111])).
% 0.22/0.47  fof(f231,plain,(
% 0.22/0.47    spl6_36 | ~spl6_1 | ~spl6_2 | spl6_3 | spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_10 | ~spl6_32),
% 0.22/0.47    inference(avatar_split_clause,[],[f212,f200,f103,f95,f91,f87,f83,f75,f71,f67,f229])).
% 0.22/0.47  fof(f103,plain,(
% 0.22/0.47    spl6_10 <=> r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.22/0.47  fof(f200,plain,(
% 0.22/0.47    spl6_32 <=> ! [X1,X3,X5,X0,X2,X4] : (v1_xboole_0(X2) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~m1_subset_1(X5,X1) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | k1_xboole_0 = X1 | k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).
% 0.22/0.47  fof(f212,plain,(
% 0.22/0.47    ( ! [X0] : (~m1_subset_1(X0,sK1) | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))) ) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_10 | ~spl6_32)),
% 0.22/0.47    inference(subsumption_resolution,[],[f211,f84])).
% 0.22/0.47  fof(f211,plain,(
% 0.22/0.47    ( ! [X0] : (~m1_subset_1(X0,sK1) | k1_xboole_0 = sK1 | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))) ) | (~spl6_1 | ~spl6_2 | spl6_3 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_10 | ~spl6_32)),
% 0.22/0.47    inference(subsumption_resolution,[],[f210,f76])).
% 0.22/0.47  fof(f210,plain,(
% 0.22/0.47    ( ! [X0] : (~m1_subset_1(X0,sK1) | v1_xboole_0(sK2) | k1_xboole_0 = sK1 | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))) ) | (~spl6_1 | ~spl6_2 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_10 | ~spl6_32)),
% 0.22/0.47    inference(subsumption_resolution,[],[f209,f92])).
% 0.22/0.47  fof(f209,plain,(
% 0.22/0.47    ( ! [X0] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~m1_subset_1(X0,sK1) | v1_xboole_0(sK2) | k1_xboole_0 = sK1 | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))) ) | (~spl6_1 | ~spl6_2 | ~spl6_6 | ~spl6_8 | ~spl6_10 | ~spl6_32)),
% 0.22/0.47    inference(subsumption_resolution,[],[f208,f68])).
% 0.22/0.47  fof(f208,plain,(
% 0.22/0.47    ( ! [X0] : (~v1_funct_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~m1_subset_1(X0,sK1) | v1_xboole_0(sK2) | k1_xboole_0 = sK1 | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))) ) | (~spl6_2 | ~spl6_6 | ~spl6_8 | ~spl6_10 | ~spl6_32)),
% 0.22/0.47    inference(subsumption_resolution,[],[f207,f96])).
% 0.22/0.47  fof(f207,plain,(
% 0.22/0.47    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~m1_subset_1(X0,sK1) | v1_xboole_0(sK2) | k1_xboole_0 = sK1 | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))) ) | (~spl6_2 | ~spl6_6 | ~spl6_10 | ~spl6_32)),
% 0.22/0.47    inference(subsumption_resolution,[],[f206,f88])).
% 0.22/0.47  fof(f206,plain,(
% 0.22/0.47    ( ! [X0] : (~v1_funct_2(sK3,sK1,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~m1_subset_1(X0,sK1) | v1_xboole_0(sK2) | k1_xboole_0 = sK1 | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))) ) | (~spl6_2 | ~spl6_10 | ~spl6_32)),
% 0.22/0.47    inference(subsumption_resolution,[],[f203,f72])).
% 0.22/0.47  fof(f203,plain,(
% 0.22/0.47    ( ! [X0] : (~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK1,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~m1_subset_1(X0,sK1) | v1_xboole_0(sK2) | k1_xboole_0 = sK1 | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))) ) | (~spl6_10 | ~spl6_32)),
% 0.22/0.47    inference(resolution,[],[f201,f104])).
% 0.22/0.47  fof(f104,plain,(
% 0.22/0.47    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) | ~spl6_10),
% 0.22/0.47    inference(avatar_component_clause,[],[f103])).
% 0.22/0.47  fof(f201,plain,(
% 0.22/0.47    ( ! [X4,X2,X0,X5,X3,X1] : (~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~m1_subset_1(X5,X1) | v1_xboole_0(X2) | k1_xboole_0 = X1 | k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))) ) | ~spl6_32),
% 0.22/0.47    inference(avatar_component_clause,[],[f200])).
% 0.22/0.47  fof(f202,plain,(
% 0.22/0.47    spl6_32),
% 0.22/0.47    inference(avatar_split_clause,[],[f53,f200])).
% 0.22/0.47  fof(f53,plain,(
% 0.22/0.47    ( ! [X4,X2,X0,X5,X3,X1] : (v1_xboole_0(X2) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~m1_subset_1(X5,X1) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | k1_xboole_0 = X1 | k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f28])).
% 0.22/0.47  fof(f28,plain,(
% 0.22/0.47    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3)) | v1_xboole_0(X2))),
% 0.22/0.47    inference(flattening,[],[f27])).
% 0.22/0.47  fof(f27,plain,(
% 0.22/0.47    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3))) | v1_xboole_0(X2))),
% 0.22/0.47    inference(ennf_transformation,[],[f11])).
% 0.22/0.47  fof(f11,axiom,(
% 0.22/0.47    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t185_funct_2)).
% 0.22/0.47  fof(f198,plain,(
% 0.22/0.47    spl6_30 | spl6_31 | ~spl6_2 | ~spl6_6 | ~spl6_8 | ~spl6_29),
% 0.22/0.47    inference(avatar_split_clause,[],[f191,f184,f95,f87,f71,f196,f193])).
% 0.22/0.47  fof(f184,plain,(
% 0.22/0.47    spl6_29 <=> ! [X1,X3,X0,X2] : (~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | k1_xboole_0 = X1 | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).
% 0.22/0.47  fof(f191,plain,(
% 0.22/0.47    ( ! [X1] : (~r1_tarski(k2_relset_1(sK1,sK2,sK3),X1) | k1_xboole_0 = sK2 | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))) ) | (~spl6_2 | ~spl6_6 | ~spl6_8 | ~spl6_29)),
% 0.22/0.47    inference(subsumption_resolution,[],[f190,f72])).
% 0.22/0.47  fof(f190,plain,(
% 0.22/0.47    ( ! [X1] : (~v1_funct_1(sK3) | ~r1_tarski(k2_relset_1(sK1,sK2,sK3),X1) | k1_xboole_0 = sK2 | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))) ) | (~spl6_6 | ~spl6_8 | ~spl6_29)),
% 0.22/0.47    inference(subsumption_resolution,[],[f188,f88])).
% 0.22/0.47  fof(f188,plain,(
% 0.22/0.47    ( ! [X1] : (~v1_funct_2(sK3,sK1,sK2) | ~v1_funct_1(sK3) | ~r1_tarski(k2_relset_1(sK1,sK2,sK3),X1) | k1_xboole_0 = sK2 | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))) ) | (~spl6_8 | ~spl6_29)),
% 0.22/0.47    inference(resolution,[],[f185,f96])).
% 0.22/0.47  fof(f185,plain,(
% 0.22/0.47    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | k1_xboole_0 = X1 | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) ) | ~spl6_29),
% 0.22/0.47    inference(avatar_component_clause,[],[f184])).
% 0.22/0.47  fof(f186,plain,(
% 0.22/0.47    spl6_29),
% 0.22/0.47    inference(avatar_split_clause,[],[f62,f184])).
% 0.22/0.47  fof(f62,plain,(
% 0.22/0.47    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | k1_xboole_0 = X1 | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f35])).
% 0.22/0.47  fof(f35,plain,(
% 0.22/0.47    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.22/0.47    inference(flattening,[],[f34])).
% 0.22/0.47  fof(f34,plain,(
% 0.22/0.47    ! [X0,X1,X2,X3] : ((((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | ~r1_tarski(k2_relset_1(X0,X1,X3),X2)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.22/0.47    inference(ennf_transformation,[],[f13])).
% 0.22/0.47  fof(f13,axiom,(
% 0.22/0.47    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_2)).
% 0.22/0.47  fof(f182,plain,(
% 0.22/0.47    spl6_28),
% 0.22/0.47    inference(avatar_split_clause,[],[f61,f180])).
% 0.22/0.47  fof(f61,plain,(
% 0.22/0.47    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | k1_xboole_0 = X1 | v1_funct_2(X3,X0,X2)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f35])).
% 0.22/0.47  fof(f174,plain,(
% 0.22/0.47    spl6_26),
% 0.22/0.47    inference(avatar_split_clause,[],[f58,f172])).
% 0.22/0.47  fof(f58,plain,(
% 0.22/0.47    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X2,X0) | k1_xboole_0 = X1 | r2_hidden(k1_funct_1(X3,X2),X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f33])).
% 0.22/0.47  fof(f33,plain,(
% 0.22/0.47    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.22/0.47    inference(flattening,[],[f32])).
% 0.22/0.47  fof(f32,plain,(
% 0.22/0.47    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.22/0.47    inference(ennf_transformation,[],[f12])).
% 0.22/0.47  fof(f12,axiom,(
% 0.22/0.47    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).
% 0.22/0.47  fof(f166,plain,(
% 0.22/0.47    spl6_24 | ~spl6_9 | ~spl6_21),
% 0.22/0.47    inference(avatar_split_clause,[],[f158,f151,f99,f164])).
% 0.22/0.47  fof(f151,plain,(
% 0.22/0.47    spl6_21 <=> ! [X1,X0,X2] : (v1_xboole_0(X0) | v1_xboole_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_xboole_0(X2))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 0.22/0.47  fof(f158,plain,(
% 0.22/0.47    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k1_xboole_0,X1,X0) | v1_xboole_0(X1)) ) | (~spl6_9 | ~spl6_21)),
% 0.22/0.47    inference(resolution,[],[f152,f100])).
% 0.22/0.47  fof(f152,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | v1_xboole_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | v1_xboole_0(X0)) ) | ~spl6_21),
% 0.22/0.47    inference(avatar_component_clause,[],[f151])).
% 0.22/0.47  fof(f162,plain,(
% 0.22/0.47    spl6_23),
% 0.22/0.47    inference(avatar_split_clause,[],[f52,f160])).
% 0.22/0.47  fof(f52,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | ~v5_relat_1(X1,X0) | ~v1_funct_1(X1) | ~r2_hidden(X2,k1_relat_1(X1)) | k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f26])).
% 0.22/0.47  fof(f26,plain,(
% 0.22/0.47    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.47    inference(flattening,[],[f25])).
% 0.22/0.47  fof(f25,plain,(
% 0.22/0.47    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.22/0.47    inference(ennf_transformation,[],[f10])).
% 0.22/0.47  fof(f10,axiom,(
% 0.22/0.47    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_partfun1)).
% 0.22/0.47  fof(f157,plain,(
% 0.22/0.47    spl6_22 | ~spl6_7 | ~spl6_10 | ~spl6_20),
% 0.22/0.47    inference(avatar_split_clause,[],[f149,f145,f103,f91,f155])).
% 0.22/0.47  fof(f145,plain,(
% 0.22/0.47    spl6_20 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 0.22/0.47  fof(f149,plain,(
% 0.22/0.47    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4)) | (~spl6_7 | ~spl6_10 | ~spl6_20)),
% 0.22/0.47    inference(subsumption_resolution,[],[f148,f92])).
% 0.22/0.47  fof(f148,plain,(
% 0.22/0.47    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | (~spl6_10 | ~spl6_20)),
% 0.22/0.47    inference(superposition,[],[f104,f146])).
% 0.22/0.47  fof(f146,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl6_20),
% 0.22/0.47    inference(avatar_component_clause,[],[f145])).
% 0.22/0.47  fof(f153,plain,(
% 0.22/0.47    spl6_21),
% 0.22/0.47    inference(avatar_split_clause,[],[f65,f151])).
% 0.22/0.47  fof(f65,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_xboole_0(X2)) )),
% 0.22/0.47    inference(subsumption_resolution,[],[f51,f47])).
% 0.22/0.47  fof(f47,plain,(
% 0.22/0.47    ( ! [X0] : (~v1_xboole_0(X0) | v1_funct_1(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f18])).
% 0.22/0.47  fof(f18,plain,(
% 0.22/0.47    ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f4])).
% 0.22/0.47  fof(f4,axiom,(
% 0.22/0.47    ! [X0] : (v1_xboole_0(X0) => v1_funct_1(X0))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_1)).
% 0.22/0.47  fof(f51,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~v1_xboole_0(X2)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f24])).
% 0.22/0.47  fof(f24,plain,(
% 0.22/0.47    ! [X0,X1] : (! [X2] : ((v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 0.22/0.47    inference(flattening,[],[f23])).
% 0.22/0.47  fof(f23,plain,(
% 0.22/0.47    ! [X0,X1] : (! [X2] : (((v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 0.22/0.47    inference(ennf_transformation,[],[f9])).
% 0.22/0.47  fof(f9,axiom,(
% 0.22/0.47    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)))))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc6_funct_2)).
% 0.22/0.47  fof(f147,plain,(
% 0.22/0.47    spl6_20),
% 0.22/0.47    inference(avatar_split_clause,[],[f55,f145])).
% 0.22/0.47  fof(f55,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f30])).
% 0.22/0.47  fof(f30,plain,(
% 0.22/0.47    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.47    inference(ennf_transformation,[],[f8])).
% 0.22/0.47  fof(f8,axiom,(
% 0.22/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.47  fof(f143,plain,(
% 0.22/0.47    spl6_19 | ~spl6_9 | ~spl6_18),
% 0.22/0.47    inference(avatar_split_clause,[],[f139,f136,f99,f141])).
% 0.22/0.47  fof(f136,plain,(
% 0.22/0.47    spl6_18 <=> ! [X1,X0,X2] : (~v1_xboole_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_xboole_0(X2))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 0.22/0.47  fof(f139,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) | v1_xboole_0(X0)) ) | (~spl6_9 | ~spl6_18)),
% 0.22/0.47    inference(resolution,[],[f137,f100])).
% 0.22/0.47  fof(f137,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_xboole_0(X2)) ) | ~spl6_18),
% 0.22/0.47    inference(avatar_component_clause,[],[f136])).
% 0.22/0.47  fof(f138,plain,(
% 0.22/0.47    spl6_18),
% 0.22/0.47    inference(avatar_split_clause,[],[f49,f136])).
% 0.22/0.47  fof(f49,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_xboole_0(X2)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f20])).
% 0.22/0.47  fof(f20,plain,(
% 0.22/0.47    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f7])).
% 0.22/0.47  fof(f7,axiom,(
% 0.22/0.47    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).
% 0.22/0.47  fof(f134,plain,(
% 0.22/0.47    spl6_17),
% 0.22/0.47    inference(avatar_split_clause,[],[f57,f132])).
% 0.22/0.47  fof(f57,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f31])).
% 0.22/0.47  fof(f31,plain,(
% 0.22/0.47    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.47    inference(ennf_transformation,[],[f6])).
% 0.22/0.47  fof(f6,axiom,(
% 0.22/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.47  fof(f126,plain,(
% 0.22/0.47    spl6_15),
% 0.22/0.47    inference(avatar_split_clause,[],[f54,f124])).
% 0.22/0.47  fof(f54,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f29])).
% 0.22/0.47  fof(f29,plain,(
% 0.22/0.47    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.47    inference(ennf_transformation,[],[f5])).
% 0.22/0.47  fof(f5,axiom,(
% 0.22/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.47  fof(f122,plain,(
% 0.22/0.47    spl6_14),
% 0.22/0.47    inference(avatar_split_clause,[],[f50,f120])).
% 0.22/0.47  fof(f50,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f22])).
% 0.22/0.47  fof(f22,plain,(
% 0.22/0.47    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.22/0.47    inference(flattening,[],[f21])).
% 0.22/0.47  fof(f21,plain,(
% 0.22/0.47    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.22/0.47    inference(ennf_transformation,[],[f3])).
% 0.22/0.47  fof(f3,axiom,(
% 0.22/0.47    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.22/0.47  fof(f117,plain,(
% 0.22/0.47    spl6_13),
% 0.22/0.47    inference(avatar_split_clause,[],[f48,f115])).
% 0.22/0.47  fof(f48,plain,(
% 0.22/0.47    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.22/0.47    inference(cnf_transformation,[],[f19])).
% 0.22/0.47  fof(f19,plain,(
% 0.22/0.47    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f2])).
% 0.22/0.47  fof(f2,axiom,(
% 0.22/0.47    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.22/0.47  fof(f113,plain,(
% 0.22/0.47    ~spl6_12),
% 0.22/0.47    inference(avatar_split_clause,[],[f39,f111])).
% 0.22/0.47  fof(f39,plain,(
% 0.22/0.47    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5))),
% 0.22/0.47    inference(cnf_transformation,[],[f17])).
% 0.22/0.47  fof(f17,plain,(
% 0.22/0.47    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2))),
% 0.22/0.47    inference(flattening,[],[f16])).
% 0.22/0.47  fof(f16,plain,(
% 0.22/0.47    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2))),
% 0.22/0.47    inference(ennf_transformation,[],[f15])).
% 0.22/0.47  fof(f15,negated_conjecture,(
% 0.22/0.47    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 0.22/0.47    inference(negated_conjecture,[],[f14])).
% 0.22/0.47  fof(f14,conjecture,(
% 0.22/0.47    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t186_funct_2)).
% 0.22/0.47  fof(f105,plain,(
% 0.22/0.47    spl6_10),
% 0.22/0.47    inference(avatar_split_clause,[],[f37,f103])).
% 0.22/0.47  fof(f37,plain,(
% 0.22/0.47    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))),
% 0.22/0.47    inference(cnf_transformation,[],[f17])).
% 0.22/0.47  fof(f101,plain,(
% 0.22/0.47    spl6_9),
% 0.22/0.47    inference(avatar_split_clause,[],[f46,f99])).
% 0.22/0.47  fof(f46,plain,(
% 0.22/0.47    v1_xboole_0(k1_xboole_0)),
% 0.22/0.47    inference(cnf_transformation,[],[f1])).
% 0.22/0.47  fof(f1,axiom,(
% 0.22/0.47    v1_xboole_0(k1_xboole_0)),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.47  fof(f97,plain,(
% 0.22/0.47    spl6_8),
% 0.22/0.47    inference(avatar_split_clause,[],[f44,f95])).
% 0.22/0.47  fof(f44,plain,(
% 0.22/0.47    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.22/0.47    inference(cnf_transformation,[],[f17])).
% 0.22/0.47  fof(f93,plain,(
% 0.22/0.47    spl6_7),
% 0.22/0.47    inference(avatar_split_clause,[],[f41,f91])).
% 0.22/0.47  fof(f41,plain,(
% 0.22/0.47    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.22/0.47    inference(cnf_transformation,[],[f17])).
% 0.22/0.47  fof(f89,plain,(
% 0.22/0.47    spl6_6),
% 0.22/0.47    inference(avatar_split_clause,[],[f43,f87])).
% 0.22/0.47  fof(f43,plain,(
% 0.22/0.47    v1_funct_2(sK3,sK1,sK2)),
% 0.22/0.47    inference(cnf_transformation,[],[f17])).
% 0.22/0.47  fof(f85,plain,(
% 0.22/0.47    ~spl6_5),
% 0.22/0.47    inference(avatar_split_clause,[],[f38,f83])).
% 0.22/0.47  fof(f38,plain,(
% 0.22/0.47    k1_xboole_0 != sK1),
% 0.22/0.47    inference(cnf_transformation,[],[f17])).
% 0.22/0.47  fof(f81,plain,(
% 0.22/0.47    spl6_4),
% 0.22/0.47    inference(avatar_split_clause,[],[f36,f79])).
% 0.22/0.47  fof(f36,plain,(
% 0.22/0.47    m1_subset_1(sK5,sK1)),
% 0.22/0.47    inference(cnf_transformation,[],[f17])).
% 0.22/0.47  fof(f77,plain,(
% 0.22/0.47    ~spl6_3),
% 0.22/0.47    inference(avatar_split_clause,[],[f45,f75])).
% 0.22/0.47  fof(f45,plain,(
% 0.22/0.47    ~v1_xboole_0(sK2)),
% 0.22/0.47    inference(cnf_transformation,[],[f17])).
% 0.22/0.47  fof(f73,plain,(
% 0.22/0.47    spl6_2),
% 0.22/0.47    inference(avatar_split_clause,[],[f42,f71])).
% 0.22/0.47  fof(f42,plain,(
% 0.22/0.47    v1_funct_1(sK3)),
% 0.22/0.47    inference(cnf_transformation,[],[f17])).
% 0.22/0.47  fof(f69,plain,(
% 0.22/0.47    spl6_1),
% 0.22/0.47    inference(avatar_split_clause,[],[f40,f67])).
% 0.22/0.47  fof(f40,plain,(
% 0.22/0.47    v1_funct_1(sK4)),
% 0.22/0.47    inference(cnf_transformation,[],[f17])).
% 0.22/0.47  % SZS output end Proof for theBenchmark
% 0.22/0.47  % (31991)------------------------------
% 0.22/0.47  % (31991)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (31991)Termination reason: Refutation
% 0.22/0.47  
% 0.22/0.47  % (31991)Memory used [KB]: 11001
% 0.22/0.47  % (31991)Time elapsed: 0.050 s
% 0.22/0.47  % (31991)------------------------------
% 0.22/0.47  % (31991)------------------------------
% 0.22/0.47  % (31981)Success in time 0.104 s
%------------------------------------------------------------------------------
