%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0840+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:45 EST 2020

% Result     : Theorem 0.13s
% Output     : Refutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :  198 ( 332 expanded)
%              Number of leaves         :   50 ( 156 expanded)
%              Depth                    :    6
%              Number of atoms          :  667 (1211 expanded)
%              Number of equality atoms :   11 (  20 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1436,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f58,f62,f70,f74,f78,f89,f93,f97,f101,f106,f110,f114,f118,f130,f135,f150,f161,f165,f172,f179,f188,f204,f213,f229,f258,f294,f426,f429,f432,f438,f461,f486,f523,f542,f559,f795,f1374,f1403,f1421,f1429,f1434])).

fof(f1434,plain,
    ( spl13_1
    | ~ spl13_6
    | ~ spl13_14
    | ~ spl13_214 ),
    inference(avatar_contradiction_clause,[],[f1432])).

fof(f1432,plain,
    ( $false
    | spl13_1
    | ~ spl13_6
    | ~ spl13_14
    | ~ spl13_214 ),
    inference(unit_resulting_resolution,[],[f77,f57,f1399,f109])).

fof(f109,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,X1)
        | v1_xboole_0(X1)
        | ~ m1_subset_1(X0,X1) )
    | ~ spl13_14 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl13_14
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,X1)
        | v1_xboole_0(X1)
        | r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_14])])).

fof(f1399,plain,
    ( ! [X2] : ~ r2_hidden(X2,sK2)
    | ~ spl13_214 ),
    inference(avatar_component_clause,[],[f1398])).

fof(f1398,plain,
    ( spl13_214
  <=> ! [X2] : ~ r2_hidden(X2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_214])])).

fof(f57,plain,
    ( ~ v1_xboole_0(sK2)
    | spl13_1 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl13_1
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1])])).

fof(f77,plain,
    ( ! [X0] : m1_subset_1(sK12(X0),X0)
    | ~ spl13_6 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl13_6
  <=> ! [X0] : m1_subset_1(sK12(X0),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_6])])).

fof(f1429,plain,
    ( spl13_2
    | ~ spl13_6
    | ~ spl13_14
    | ~ spl13_213 ),
    inference(avatar_contradiction_clause,[],[f1427])).

fof(f1427,plain,
    ( $false
    | spl13_2
    | ~ spl13_6
    | ~ spl13_14
    | ~ spl13_213 ),
    inference(unit_resulting_resolution,[],[f77,f61,f1396,f109])).

fof(f1396,plain,
    ( ! [X3] : ~ r2_hidden(X3,sK1)
    | ~ spl13_213 ),
    inference(avatar_component_clause,[],[f1395])).

fof(f1395,plain,
    ( spl13_213
  <=> ! [X3] : ~ r2_hidden(X3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_213])])).

fof(f61,plain,
    ( ~ v1_xboole_0(sK1)
    | spl13_2 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl13_2
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_2])])).

fof(f1421,plain,
    ( ~ spl13_67
    | spl13_77
    | ~ spl13_215 ),
    inference(avatar_contradiction_clause,[],[f1420])).

fof(f1420,plain,
    ( $false
    | ~ spl13_67
    | spl13_77
    | ~ spl13_215 ),
    inference(subsumption_resolution,[],[f1411,f558])).

fof(f558,plain,
    ( ~ r2_hidden(sK10(sK3,sK4,sK5,sK6),sK1)
    | spl13_77 ),
    inference(avatar_component_clause,[],[f557])).

fof(f557,plain,
    ( spl13_77
  <=> r2_hidden(sK10(sK3,sK4,sK5,sK6),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_77])])).

fof(f1411,plain,
    ( r2_hidden(sK10(sK3,sK4,sK5,sK6),sK1)
    | ~ spl13_67
    | ~ spl13_215 ),
    inference(resolution,[],[f1402,f437])).

fof(f437,plain,
    ( r2_hidden(k4_tarski(sK10(sK3,sK4,sK5,sK6),sK6),sK4)
    | ~ spl13_67 ),
    inference(avatar_component_clause,[],[f436])).

fof(f436,plain,
    ( spl13_67
  <=> r2_hidden(k4_tarski(sK10(sK3,sK4,sK5,sK6),sK6),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_67])])).

fof(f1402,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK4)
        | r2_hidden(X0,sK1) )
    | ~ spl13_215 ),
    inference(avatar_component_clause,[],[f1401])).

fof(f1401,plain,
    ( spl13_215
  <=> ! [X1,X0] :
        ( r2_hidden(X0,sK1)
        | ~ r2_hidden(k4_tarski(X0,X1),sK4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_215])])).

fof(f1403,plain,
    ( spl13_213
    | spl13_214
    | spl13_215
    | ~ spl13_4
    | ~ spl13_210 ),
    inference(avatar_split_clause,[],[f1379,f1372,f68,f1401,f1398,f1395])).

fof(f68,plain,
    ( spl13_4
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_4])])).

fof(f1372,plain,
    ( spl13_210
  <=> ! [X1,X3,X5,X0,X2,X4,X6] :
        ( r2_hidden(X0,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
        | ~ r2_hidden(k4_tarski(X0,X4),X2)
        | ~ r2_hidden(X5,X3)
        | ~ r2_hidden(X6,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_210])])).

fof(f1379,plain,
    ( ! [X2,X0,X3,X1] :
        ( r2_hidden(X0,sK1)
        | ~ r2_hidden(k4_tarski(X0,X1),sK4)
        | ~ r2_hidden(X2,sK2)
        | ~ r2_hidden(X3,sK1) )
    | ~ spl13_4
    | ~ spl13_210 ),
    inference(resolution,[],[f1373,f69])).

fof(f69,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl13_4 ),
    inference(avatar_component_clause,[],[f68])).

fof(f1373,plain,
    ( ! [X6,X4,X2,X0,X5,X3,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
        | r2_hidden(X0,X1)
        | ~ r2_hidden(k4_tarski(X0,X4),X2)
        | ~ r2_hidden(X5,X3)
        | ~ r2_hidden(X6,X1) )
    | ~ spl13_210 ),
    inference(avatar_component_clause,[],[f1372])).

fof(f1374,plain,
    ( spl13_210
    | ~ spl13_23
    | ~ spl13_116 ),
    inference(avatar_split_clause,[],[f800,f793,f148,f1372])).

fof(f148,plain,
    ( spl13_23
  <=> ! [X1,X3,X0,X2] :
        ( ~ r2_hidden(X0,X2)
        | ~ r2_hidden(X1,X3)
        | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_23])])).

fof(f793,plain,
    ( spl13_116
  <=> ! [X1,X3,X5,X0,X2,X4] :
        ( r2_hidden(X0,X1)
        | ~ r2_hidden(X2,k2_zfmisc_1(X1,X3))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
        | ~ r2_hidden(k4_tarski(X0,X5),X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_116])])).

fof(f800,plain,
    ( ! [X6,X4,X2,X0,X5,X3,X1] :
        ( r2_hidden(X0,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
        | ~ r2_hidden(k4_tarski(X0,X4),X2)
        | ~ r2_hidden(X5,X3)
        | ~ r2_hidden(X6,X1) )
    | ~ spl13_23
    | ~ spl13_116 ),
    inference(resolution,[],[f794,f149])).

fof(f149,plain,
    ( ! [X2,X0,X3,X1] :
        ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
    | ~ spl13_23 ),
    inference(avatar_component_clause,[],[f148])).

fof(f794,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( ~ r2_hidden(X2,k2_zfmisc_1(X1,X3))
        | r2_hidden(X0,X1)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
        | ~ r2_hidden(k4_tarski(X0,X5),X4) )
    | ~ spl13_116 ),
    inference(avatar_component_clause,[],[f793])).

fof(f795,plain,
    ( spl13_116
    | ~ spl13_19
    | ~ spl13_71 ),
    inference(avatar_split_clause,[],[f528,f521,f128,f793])).

fof(f128,plain,
    ( spl13_19
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
        | m1_subset_1(X0,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_19])])).

fof(f521,plain,
    ( spl13_71
  <=> ! [X1,X3,X0,X2,X4] :
        ( r2_hidden(X0,X1)
        | ~ m1_subset_1(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3))
        | ~ r2_hidden(X4,k2_zfmisc_1(X1,X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_71])])).

fof(f528,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( r2_hidden(X0,X1)
        | ~ r2_hidden(X2,k2_zfmisc_1(X1,X3))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
        | ~ r2_hidden(k4_tarski(X0,X5),X4) )
    | ~ spl13_19
    | ~ spl13_71 ),
    inference(resolution,[],[f522,f129])).

fof(f129,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(X0,X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
        | ~ r2_hidden(X0,X1) )
    | ~ spl13_19 ),
    inference(avatar_component_clause,[],[f128])).

fof(f522,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( ~ m1_subset_1(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3))
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X4,k2_zfmisc_1(X1,X3)) )
    | ~ spl13_71 ),
    inference(avatar_component_clause,[],[f521])).

fof(f559,plain,
    ( ~ spl13_77
    | ~ spl13_12
    | spl13_74 ),
    inference(avatar_split_clause,[],[f551,f540,f99,f557])).

fof(f99,plain,
    ( spl13_12
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,X1)
        | m1_subset_1(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_12])])).

fof(f540,plain,
    ( spl13_74
  <=> m1_subset_1(sK10(sK3,sK4,sK5,sK6),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_74])])).

fof(f551,plain,
    ( ~ r2_hidden(sK10(sK3,sK4,sK5,sK6),sK1)
    | ~ spl13_12
    | spl13_74 ),
    inference(resolution,[],[f541,f100])).

fof(f100,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(X0,X1)
        | ~ r2_hidden(X0,X1) )
    | ~ spl13_12 ),
    inference(avatar_component_clause,[],[f99])).

fof(f541,plain,
    ( ~ m1_subset_1(sK10(sK3,sK4,sK5,sK6),sK1)
    | spl13_74 ),
    inference(avatar_component_clause,[],[f540])).

fof(f542,plain,
    ( ~ spl13_74
    | ~ spl13_13
    | ~ spl13_65
    | ~ spl13_67 ),
    inference(avatar_split_clause,[],[f497,f436,f421,f104,f540])).

fof(f104,plain,
    ( spl13_13
  <=> ! [X7] :
        ( ~ m1_subset_1(X7,sK1)
        | ~ r2_hidden(k4_tarski(X7,sK6),sK4)
        | ~ r2_hidden(k4_tarski(sK5,X7),sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_13])])).

fof(f421,plain,
    ( spl13_65
  <=> r2_hidden(k4_tarski(sK5,sK10(sK3,sK4,sK5,sK6)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_65])])).

fof(f497,plain,
    ( ~ m1_subset_1(sK10(sK3,sK4,sK5,sK6),sK1)
    | ~ spl13_13
    | ~ spl13_65
    | ~ spl13_67 ),
    inference(subsumption_resolution,[],[f494,f437])).

fof(f494,plain,
    ( ~ r2_hidden(k4_tarski(sK10(sK3,sK4,sK5,sK6),sK6),sK4)
    | ~ m1_subset_1(sK10(sK3,sK4,sK5,sK6),sK1)
    | ~ spl13_13
    | ~ spl13_65 ),
    inference(resolution,[],[f105,f422])).

fof(f422,plain,
    ( r2_hidden(k4_tarski(sK5,sK10(sK3,sK4,sK5,sK6)),sK3)
    | ~ spl13_65 ),
    inference(avatar_component_clause,[],[f421])).

fof(f105,plain,
    ( ! [X7] :
        ( ~ r2_hidden(k4_tarski(sK5,X7),sK3)
        | ~ r2_hidden(k4_tarski(X7,sK6),sK4)
        | ~ m1_subset_1(X7,sK1) )
    | ~ spl13_13 ),
    inference(avatar_component_clause,[],[f104])).

fof(f523,plain,
    ( spl13_71
    | ~ spl13_9
    | ~ spl13_40 ),
    inference(avatar_split_clause,[],[f261,f256,f87,f521])).

fof(f87,plain,
    ( spl13_9
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,X1)
        | ~ v1_xboole_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_9])])).

fof(f256,plain,
    ( spl13_40
  <=> ! [X1,X3,X0,X2] :
        ( r2_hidden(X0,X1)
        | v1_xboole_0(k2_zfmisc_1(X1,X2))
        | ~ m1_subset_1(k4_tarski(X0,X3),k2_zfmisc_1(X1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_40])])).

fof(f261,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( r2_hidden(X0,X1)
        | ~ m1_subset_1(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3))
        | ~ r2_hidden(X4,k2_zfmisc_1(X1,X3)) )
    | ~ spl13_9
    | ~ spl13_40 ),
    inference(resolution,[],[f257,f88])).

fof(f88,plain,
    ( ! [X0,X1] :
        ( ~ v1_xboole_0(X1)
        | ~ r2_hidden(X0,X1) )
    | ~ spl13_9 ),
    inference(avatar_component_clause,[],[f87])).

fof(f257,plain,
    ( ! [X2,X0,X3,X1] :
        ( v1_xboole_0(k2_zfmisc_1(X1,X2))
        | r2_hidden(X0,X1)
        | ~ m1_subset_1(k4_tarski(X0,X3),k2_zfmisc_1(X1,X2)) )
    | ~ spl13_40 ),
    inference(avatar_component_clause,[],[f256])).

fof(f486,plain,
    ( ~ spl13_10
    | ~ spl13_11
    | ~ spl13_68 ),
    inference(avatar_contradiction_clause,[],[f485])).

fof(f485,plain,
    ( $false
    | ~ spl13_10
    | ~ spl13_11
    | ~ spl13_68 ),
    inference(subsumption_resolution,[],[f479,f96])).

fof(f96,plain,
    ( r2_hidden(k4_tarski(sK7,sK6),sK4)
    | ~ spl13_11 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl13_11
  <=> r2_hidden(k4_tarski(sK7,sK6),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_11])])).

fof(f479,plain,
    ( ~ r2_hidden(k4_tarski(sK7,sK6),sK4)
    | ~ spl13_10
    | ~ spl13_68 ),
    inference(resolution,[],[f460,f92])).

fof(f92,plain,
    ( r2_hidden(k4_tarski(sK5,sK7),sK3)
    | ~ spl13_10 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl13_10
  <=> r2_hidden(k4_tarski(sK5,sK7),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_10])])).

fof(f460,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(sK5,X0),sK3)
        | ~ r2_hidden(k4_tarski(X0,sK6),sK4) )
    | ~ spl13_68 ),
    inference(avatar_component_clause,[],[f459])).

fof(f459,plain,
    ( spl13_68
  <=> ! [X0] :
        ( ~ r2_hidden(k4_tarski(sK5,X0),sK3)
        | ~ r2_hidden(k4_tarski(X0,sK6),sK4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_68])])).

fof(f461,plain,
    ( ~ spl13_64
    | spl13_68
    | ~ spl13_66
    | ~ spl13_33
    | spl13_36 ),
    inference(avatar_split_clause,[],[f443,f227,f211,f424,f459,f418])).

fof(f418,plain,
    ( spl13_64
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_64])])).

fof(f424,plain,
    ( spl13_66
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_66])])).

fof(f211,plain,
    ( spl13_33
  <=> ! [X1,X3,X5,X0,X4] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | ~ r2_hidden(k4_tarski(X3,X5),X0)
        | ~ r2_hidden(k4_tarski(X5,X4),X1)
        | r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_33])])).

fof(f227,plain,
    ( spl13_36
  <=> r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_36])])).

fof(f443,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK4)
        | ~ r2_hidden(k4_tarski(sK5,X0),sK3)
        | ~ r2_hidden(k4_tarski(X0,sK6),sK4)
        | ~ v1_relat_1(sK3) )
    | ~ spl13_33
    | spl13_36 ),
    inference(resolution,[],[f228,f212])).

fof(f212,plain,
    ( ! [X4,X0,X5,X3,X1] :
        ( r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1))
        | ~ v1_relat_1(X1)
        | ~ r2_hidden(k4_tarski(X3,X5),X0)
        | ~ r2_hidden(k4_tarski(X5,X4),X1)
        | ~ v1_relat_1(X0) )
    | ~ spl13_33 ),
    inference(avatar_component_clause,[],[f211])).

fof(f228,plain,
    ( ~ r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4))
    | spl13_36 ),
    inference(avatar_component_clause,[],[f227])).

fof(f438,plain,
    ( ~ spl13_64
    | spl13_67
    | ~ spl13_66
    | ~ spl13_27
    | ~ spl13_36 ),
    inference(avatar_split_clause,[],[f296,f227,f170,f424,f436,f418])).

fof(f170,plain,
    ( spl13_27
  <=> ! [X1,X3,X0,X4] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | r2_hidden(k4_tarski(sK10(X0,X1,X3,X4),X4),X1)
        | ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_27])])).

fof(f296,plain,
    ( ~ v1_relat_1(sK4)
    | r2_hidden(k4_tarski(sK10(sK3,sK4,sK5,sK6),sK6),sK4)
    | ~ v1_relat_1(sK3)
    | ~ spl13_27
    | ~ spl13_36 ),
    inference(resolution,[],[f293,f171])).

fof(f171,plain,
    ( ! [X4,X0,X3,X1] :
        ( ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1))
        | ~ v1_relat_1(X1)
        | r2_hidden(k4_tarski(sK10(X0,X1,X3,X4),X4),X1)
        | ~ v1_relat_1(X0) )
    | ~ spl13_27 ),
    inference(avatar_component_clause,[],[f170])).

fof(f293,plain,
    ( r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4))
    | ~ spl13_36 ),
    inference(avatar_component_clause,[],[f227])).

fof(f432,plain,
    ( ~ spl13_4
    | ~ spl13_16
    | spl13_66 ),
    inference(avatar_contradiction_clause,[],[f430])).

fof(f430,plain,
    ( $false
    | ~ spl13_4
    | ~ spl13_16
    | spl13_66 ),
    inference(unit_resulting_resolution,[],[f69,f425,f117])).

fof(f117,plain,
    ( ! [X2,X0,X1] :
        ( v1_relat_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl13_16 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl13_16
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_16])])).

fof(f425,plain,
    ( ~ v1_relat_1(sK4)
    | spl13_66 ),
    inference(avatar_component_clause,[],[f424])).

fof(f429,plain,
    ( ~ spl13_5
    | ~ spl13_16
    | spl13_64 ),
    inference(avatar_contradiction_clause,[],[f427])).

fof(f427,plain,
    ( $false
    | ~ spl13_5
    | ~ spl13_16
    | spl13_64 ),
    inference(unit_resulting_resolution,[],[f73,f419,f117])).

fof(f419,plain,
    ( ~ v1_relat_1(sK3)
    | spl13_64 ),
    inference(avatar_component_clause,[],[f418])).

fof(f73,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl13_5 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl13_5
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_5])])).

fof(f426,plain,
    ( ~ spl13_64
    | spl13_65
    | ~ spl13_66
    | ~ spl13_30
    | ~ spl13_36 ),
    inference(avatar_split_clause,[],[f295,f227,f186,f424,f421,f418])).

fof(f186,plain,
    ( spl13_30
  <=> ! [X1,X3,X0,X4] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | r2_hidden(k4_tarski(X3,sK10(X0,X1,X3,X4)),X0)
        | ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_30])])).

fof(f295,plain,
    ( ~ v1_relat_1(sK4)
    | r2_hidden(k4_tarski(sK5,sK10(sK3,sK4,sK5,sK6)),sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl13_30
    | ~ spl13_36 ),
    inference(resolution,[],[f293,f187])).

fof(f187,plain,
    ( ! [X4,X0,X3,X1] :
        ( ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1))
        | ~ v1_relat_1(X1)
        | r2_hidden(k4_tarski(X3,sK10(X0,X1,X3,X4)),X0)
        | ~ v1_relat_1(X0) )
    | ~ spl13_30 ),
    inference(avatar_component_clause,[],[f186])).

fof(f294,plain,
    ( spl13_36
    | ~ spl13_4
    | ~ spl13_5
    | ~ spl13_7
    | ~ spl13_25 ),
    inference(avatar_split_clause,[],[f274,f159,f80,f72,f68,f227])).

fof(f80,plain,
    ( spl13_7
  <=> r2_hidden(k4_tarski(sK5,sK6),k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_7])])).

fof(f159,plain,
    ( spl13_25
  <=> ! [X1,X3,X5,X0,X2,X4] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_25])])).

fof(f274,plain,
    ( r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4))
    | ~ spl13_4
    | ~ spl13_5
    | ~ spl13_7
    | ~ spl13_25 ),
    inference(subsumption_resolution,[],[f273,f73])).

fof(f273,plain,
    ( r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl13_4
    | ~ spl13_7
    | ~ spl13_25 ),
    inference(subsumption_resolution,[],[f272,f69])).

fof(f272,plain,
    ( r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl13_7
    | ~ spl13_25 ),
    inference(superposition,[],[f81,f160])).

fof(f160,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl13_25 ),
    inference(avatar_component_clause,[],[f159])).

fof(f81,plain,
    ( r2_hidden(k4_tarski(sK5,sK6),k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4))
    | ~ spl13_7 ),
    inference(avatar_component_clause,[],[f80])).

fof(f258,plain,
    ( spl13_40
    | ~ spl13_14
    | ~ spl13_20 ),
    inference(avatar_split_clause,[],[f141,f133,f108,f256])).

fof(f133,plain,
    ( spl13_20
  <=> ! [X1,X3,X0,X2] :
        ( r2_hidden(X0,X2)
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_20])])).

fof(f141,plain,
    ( ! [X2,X0,X3,X1] :
        ( r2_hidden(X0,X1)
        | v1_xboole_0(k2_zfmisc_1(X1,X2))
        | ~ m1_subset_1(k4_tarski(X0,X3),k2_zfmisc_1(X1,X2)) )
    | ~ spl13_14
    | ~ spl13_20 ),
    inference(resolution,[],[f134,f109])).

fof(f134,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | r2_hidden(X0,X2) )
    | ~ spl13_20 ),
    inference(avatar_component_clause,[],[f133])).

fof(f229,plain,
    ( ~ spl13_36
    | ~ spl13_4
    | ~ spl13_5
    | spl13_7
    | ~ spl13_25 ),
    inference(avatar_split_clause,[],[f196,f159,f80,f72,f68,f227])).

fof(f196,plain,
    ( ~ r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4))
    | ~ spl13_4
    | ~ spl13_5
    | spl13_7
    | ~ spl13_25 ),
    inference(subsumption_resolution,[],[f195,f73])).

fof(f195,plain,
    ( ~ r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl13_4
    | spl13_7
    | ~ spl13_25 ),
    inference(subsumption_resolution,[],[f192,f69])).

fof(f192,plain,
    ( ~ r2_hidden(k4_tarski(sK5,sK6),k5_relat_1(sK3,sK4))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl13_7
    | ~ spl13_25 ),
    inference(superposition,[],[f102,f160])).

fof(f102,plain,
    ( ~ r2_hidden(k4_tarski(sK5,sK6),k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4))
    | spl13_7 ),
    inference(avatar_component_clause,[],[f80])).

fof(f213,plain,
    ( spl13_33
    | ~ spl13_15
    | ~ spl13_32 ),
    inference(avatar_split_clause,[],[f205,f202,f112,f211])).

fof(f112,plain,
    ( spl13_15
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | v1_relat_1(k5_relat_1(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_15])])).

fof(f202,plain,
    ( spl13_32
  <=> ! [X1,X3,X5,X0,X4] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(k5_relat_1(X0,X1))
        | ~ r2_hidden(k4_tarski(X3,X5),X0)
        | ~ r2_hidden(k4_tarski(X5,X4),X1)
        | r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_32])])).

fof(f205,plain,
    ( ! [X4,X0,X5,X3,X1] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | ~ r2_hidden(k4_tarski(X3,X5),X0)
        | ~ r2_hidden(k4_tarski(X5,X4),X1)
        | r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1)) )
    | ~ spl13_15
    | ~ spl13_32 ),
    inference(subsumption_resolution,[],[f203,f113])).

fof(f113,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(k5_relat_1(X0,X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl13_15 ),
    inference(avatar_component_clause,[],[f112])).

fof(f203,plain,
    ( ! [X4,X0,X5,X3,X1] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(k5_relat_1(X0,X1))
        | ~ r2_hidden(k4_tarski(X3,X5),X0)
        | ~ r2_hidden(k4_tarski(X5,X4),X1)
        | r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1)) )
    | ~ spl13_32 ),
    inference(avatar_component_clause,[],[f202])).

fof(f204,plain,(
    spl13_32 ),
    inference(avatar_split_clause,[],[f52,f202])).

fof(f52,plain,(
    ! [X4,X0,X5,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X3,X5),X0)
      | ~ r2_hidden(k4_tarski(X5,X4),X1)
      | r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(k4_tarski(X3,X5),X0)
      | ~ r2_hidden(k4_tarski(X5,X4),X1)
      | r2_hidden(k4_tarski(X3,X4),X2)
      | k5_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_relat_1)).

fof(f188,plain,
    ( spl13_30
    | ~ spl13_15
    | ~ spl13_28 ),
    inference(avatar_split_clause,[],[f180,f177,f112,f186])).

fof(f177,plain,
    ( spl13_28
  <=> ! [X1,X3,X0,X4] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(k5_relat_1(X0,X1))
        | r2_hidden(k4_tarski(X3,sK10(X0,X1,X3,X4)),X0)
        | ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_28])])).

fof(f180,plain,
    ( ! [X4,X0,X3,X1] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | r2_hidden(k4_tarski(X3,sK10(X0,X1,X3,X4)),X0)
        | ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1)) )
    | ~ spl13_15
    | ~ spl13_28 ),
    inference(subsumption_resolution,[],[f178,f113])).

fof(f178,plain,
    ( ! [X4,X0,X3,X1] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(k5_relat_1(X0,X1))
        | r2_hidden(k4_tarski(X3,sK10(X0,X1,X3,X4)),X0)
        | ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1)) )
    | ~ spl13_28 ),
    inference(avatar_component_clause,[],[f177])).

fof(f179,plain,(
    spl13_28 ),
    inference(avatar_split_clause,[],[f54,f177])).

fof(f54,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | r2_hidden(k4_tarski(X3,sK10(X0,X1,X3,X4)),X0)
      | ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(X3,sK10(X0,X1,X3,X4)),X0)
      | ~ r2_hidden(k4_tarski(X3,X4),X2)
      | k5_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f172,plain,
    ( spl13_27
    | ~ spl13_15
    | ~ spl13_26 ),
    inference(avatar_split_clause,[],[f166,f163,f112,f170])).

fof(f163,plain,
    ( spl13_26
  <=> ! [X1,X3,X0,X4] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(k5_relat_1(X0,X1))
        | r2_hidden(k4_tarski(sK10(X0,X1,X3,X4),X4),X1)
        | ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_26])])).

fof(f166,plain,
    ( ! [X4,X0,X3,X1] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | r2_hidden(k4_tarski(sK10(X0,X1,X3,X4),X4),X1)
        | ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1)) )
    | ~ spl13_15
    | ~ spl13_26 ),
    inference(subsumption_resolution,[],[f164,f113])).

fof(f164,plain,
    ( ! [X4,X0,X3,X1] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(k5_relat_1(X0,X1))
        | r2_hidden(k4_tarski(sK10(X0,X1,X3,X4),X4),X1)
        | ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1)) )
    | ~ spl13_26 ),
    inference(avatar_component_clause,[],[f163])).

fof(f165,plain,(
    spl13_26 ),
    inference(avatar_split_clause,[],[f53,f163])).

fof(f53,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | r2_hidden(k4_tarski(sK10(X0,X1,X3,X4),X4),X1)
      | ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(sK10(X0,X1,X3,X4),X4),X1)
      | ~ r2_hidden(k4_tarski(X3,X4),X2)
      | k5_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f161,plain,(
    spl13_25 ),
    inference(avatar_split_clause,[],[f51,f159])).

fof(f51,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

fof(f150,plain,(
    spl13_23 ),
    inference(avatar_split_clause,[],[f50,f148])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X1,X3)
      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_zfmisc_1)).

fof(f135,plain,(
    spl13_20 ),
    inference(avatar_split_clause,[],[f48,f133])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f130,plain,(
    spl13_19 ),
    inference(avatar_split_clause,[],[f47,f128])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f118,plain,(
    spl13_16 ),
    inference(avatar_split_clause,[],[f46,f116])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f114,plain,(
    spl13_15 ),
    inference(avatar_split_clause,[],[f44,f112])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | v1_relat_1(k5_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f110,plain,(
    spl13_14 ),
    inference(avatar_split_clause,[],[f43,f108])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f106,plain,
    ( ~ spl13_7
    | spl13_13 ),
    inference(avatar_split_clause,[],[f26,f104,f80])).

fof(f26,plain,(
    ! [X7] :
      ( ~ m1_subset_1(X7,sK1)
      | ~ r2_hidden(k4_tarski(sK5,X7),sK3)
      | ~ r2_hidden(k4_tarski(X7,sK6),sK4)
      | ~ r2_hidden(k4_tarski(sK5,sK6),k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5,X6] :
                          ( r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,X4))
                        <~> ? [X7] :
                              ( r2_hidden(k4_tarski(X7,X6),X4)
                              & r2_hidden(k4_tarski(X5,X7),X3)
                              & m1_subset_1(X7,X1) ) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
              & ~ v1_xboole_0(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( ~ v1_xboole_0(X2)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                   => ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                       => ! [X5,X6] :
                            ( r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,X4))
                          <=> ? [X7] :
                                ( r2_hidden(k4_tarski(X7,X6),X4)
                                & r2_hidden(k4_tarski(X5,X7),X3)
                                & m1_subset_1(X7,X1) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ~ v1_xboole_0(X2)
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                 => ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                     => ! [X5,X6] :
                          ( r2_hidden(k4_tarski(X5,X6),k4_relset_1(X0,X1,X1,X2,X3,X4))
                        <=> ? [X7] :
                              ( r2_hidden(k4_tarski(X7,X6),X4)
                              & r2_hidden(k4_tarski(X5,X7),X3)
                              & m1_subset_1(X7,X1) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_relset_1)).

fof(f101,plain,(
    spl13_12 ),
    inference(avatar_split_clause,[],[f42,f99])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f97,plain,
    ( spl13_7
    | spl13_11 ),
    inference(avatar_split_clause,[],[f29,f95,f80])).

fof(f29,plain,
    ( r2_hidden(k4_tarski(sK7,sK6),sK4)
    | r2_hidden(k4_tarski(sK5,sK6),k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f13])).

fof(f93,plain,
    ( spl13_7
    | spl13_10 ),
    inference(avatar_split_clause,[],[f28,f91,f80])).

fof(f28,plain,
    ( r2_hidden(k4_tarski(sK5,sK7),sK3)
    | r2_hidden(k4_tarski(sK5,sK6),k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f13])).

fof(f89,plain,(
    spl13_9 ),
    inference(avatar_split_clause,[],[f45,f87])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

fof(f78,plain,(
    spl13_6 ),
    inference(avatar_split_clause,[],[f41,f76])).

fof(f41,plain,(
    ! [X0] : m1_subset_1(sK12(X0),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f74,plain,(
    spl13_5 ),
    inference(avatar_split_clause,[],[f31,f72])).

fof(f31,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f13])).

fof(f70,plain,(
    spl13_4 ),
    inference(avatar_split_clause,[],[f30,f68])).

fof(f30,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f13])).

fof(f62,plain,(
    ~ spl13_2 ),
    inference(avatar_split_clause,[],[f33,f60])).

fof(f33,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f58,plain,(
    ~ spl13_1 ),
    inference(avatar_split_clause,[],[f32,f56])).

fof(f32,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f13])).

%------------------------------------------------------------------------------
