%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:58 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  282 ( 599 expanded)
%              Number of leaves         :   63 ( 281 expanded)
%              Depth                    :    9
%              Number of atoms          : 1118 (2154 expanded)
%              Number of equality atoms :  120 ( 212 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f856,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f81,f86,f91,f96,f104,f108,f112,f116,f124,f132,f140,f147,f155,f174,f178,f182,f190,f207,f215,f226,f241,f261,f268,f276,f280,f333,f385,f436,f457,f496,f500,f516,f521,f530,f540,f558,f628,f657,f718,f756,f788,f793,f811,f815,f834,f839,f851,f855])).

fof(f855,plain,
    ( ~ spl3_4
    | ~ spl3_32
    | spl3_67
    | ~ spl3_99 ),
    inference(avatar_contradiction_clause,[],[f854])).

fof(f854,plain,
    ( $false
    | ~ spl3_4
    | ~ spl3_32
    | spl3_67
    | ~ spl3_99 ),
    inference(subsumption_resolution,[],[f853,f267])).

fof(f267,plain,
    ( ! [X0] : r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0))
    | ~ spl3_32 ),
    inference(avatar_component_clause,[],[f266])).

fof(f266,plain,
    ( spl3_32
  <=> ! [X0] : r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f853,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0))
    | ~ spl3_4
    | spl3_67
    | ~ spl3_99 ),
    inference(backward_demodulation,[],[f529,f852])).

fof(f852,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1)
    | ~ spl3_4
    | ~ spl3_99 ),
    inference(resolution,[],[f850,f95])).

fof(f95,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl3_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f850,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k6_partfun1(sK0) = k1_partfun1(sK0,sK0,X0,X1,k2_funct_1(sK1),sK1) )
    | ~ spl3_99 ),
    inference(avatar_component_clause,[],[f849])).

fof(f849,plain,
    ( spl3_99
  <=> ! [X1,X0] :
        ( k6_partfun1(sK0) = k1_partfun1(sK0,sK0,X0,X1,k2_funct_1(sK1),sK1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_99])])).

fof(f529,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0))
    | spl3_67 ),
    inference(avatar_component_clause,[],[f527])).

fof(f527,plain,
    ( spl3_67
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_67])])).

fof(f851,plain,
    ( spl3_99
    | ~ spl3_1
    | ~ spl3_84
    | ~ spl3_97 ),
    inference(avatar_split_clause,[],[f843,f837,f753,f78,f849])).

fof(f78,plain,
    ( spl3_1
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f753,plain,
    ( spl3_84
  <=> k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_84])])).

fof(f837,plain,
    ( spl3_97
  <=> ! [X1,X0,X2] :
        ( ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | k5_relat_1(k2_funct_1(sK1),X0) = k1_partfun1(sK0,sK0,X1,X2,k2_funct_1(sK1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_97])])).

fof(f843,plain,
    ( ! [X0,X1] :
        ( k6_partfun1(sK0) = k1_partfun1(sK0,sK0,X0,X1,k2_funct_1(sK1),sK1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl3_1
    | ~ spl3_84
    | ~ spl3_97 ),
    inference(forward_demodulation,[],[f840,f755])).

fof(f755,plain,
    ( k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1)
    | ~ spl3_84 ),
    inference(avatar_component_clause,[],[f753])).

fof(f840,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k5_relat_1(k2_funct_1(sK1),sK1) = k1_partfun1(sK0,sK0,X0,X1,k2_funct_1(sK1),sK1) )
    | ~ spl3_1
    | ~ spl3_97 ),
    inference(resolution,[],[f838,f80])).

fof(f80,plain,
    ( v1_funct_1(sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f78])).

fof(f838,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | k5_relat_1(k2_funct_1(sK1),X0) = k1_partfun1(sK0,sK0,X1,X2,k2_funct_1(sK1),X0) )
    | ~ spl3_97 ),
    inference(avatar_component_clause,[],[f837])).

fof(f839,plain,
    ( spl3_97
    | ~ spl3_70
    | ~ spl3_96 ),
    inference(avatar_split_clause,[],[f835,f832,f555,f837])).

fof(f555,plain,
    ( spl3_70
  <=> m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_70])])).

fof(f832,plain,
    ( spl3_96
  <=> ! [X11,X13,X15,X12,X14] :
        ( ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X12,X13)))
        | ~ v1_funct_1(X11)
        | ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X14,X15)))
        | k1_partfun1(X14,X15,X12,X13,k2_funct_1(sK1),X11) = k5_relat_1(k2_funct_1(sK1),X11) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_96])])).

fof(f835,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | k5_relat_1(k2_funct_1(sK1),X0) = k1_partfun1(sK0,sK0,X1,X2,k2_funct_1(sK1),X0) )
    | ~ spl3_70
    | ~ spl3_96 ),
    inference(resolution,[],[f833,f556])).

fof(f556,plain,
    ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl3_70 ),
    inference(avatar_component_clause,[],[f555])).

fof(f833,plain,
    ( ! [X14,X12,X15,X13,X11] :
        ( ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X14,X15)))
        | ~ v1_funct_1(X11)
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X12,X13)))
        | k1_partfun1(X14,X15,X12,X13,k2_funct_1(sK1),X11) = k5_relat_1(k2_funct_1(sK1),X11) )
    | ~ spl3_96 ),
    inference(avatar_component_clause,[],[f832])).

fof(f834,plain,
    ( spl3_96
    | ~ spl3_64
    | ~ spl3_80 ),
    inference(avatar_split_clause,[],[f784,f655,f513,f832])).

fof(f513,plain,
    ( spl3_64
  <=> v1_funct_1(k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_64])])).

fof(f655,plain,
    ( spl3_80
  <=> ! [X1,X3,X5,X0,X2,X4] :
        ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | ~ v1_funct_1(X5)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_80])])).

fof(f784,plain,
    ( ! [X14,X12,X15,X13,X11] :
        ( ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X12,X13)))
        | ~ v1_funct_1(X11)
        | ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X14,X15)))
        | k1_partfun1(X14,X15,X12,X13,k2_funct_1(sK1),X11) = k5_relat_1(k2_funct_1(sK1),X11) )
    | ~ spl3_64
    | ~ spl3_80 ),
    inference(resolution,[],[f656,f515])).

fof(f515,plain,
    ( v1_funct_1(k2_funct_1(sK1))
    | ~ spl3_64 ),
    inference(avatar_component_clause,[],[f513])).

fof(f656,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( ~ v1_funct_1(X4)
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | ~ v1_funct_1(X5)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) )
    | ~ spl3_80 ),
    inference(avatar_component_clause,[],[f655])).

fof(f815,plain,
    ( ~ spl3_32
    | spl3_66
    | ~ spl3_70
    | ~ spl3_93 ),
    inference(avatar_contradiction_clause,[],[f814])).

fof(f814,plain,
    ( $false
    | ~ spl3_32
    | spl3_66
    | ~ spl3_70
    | ~ spl3_93 ),
    inference(subsumption_resolution,[],[f813,f267])).

fof(f813,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0))
    | spl3_66
    | ~ spl3_70
    | ~ spl3_93 ),
    inference(backward_demodulation,[],[f525,f812])).

fof(f812,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1))
    | ~ spl3_70
    | ~ spl3_93 ),
    inference(resolution,[],[f810,f556])).

fof(f810,plain,
    ( ! [X6,X5] :
        ( ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
        | k6_partfun1(sK0) = k1_partfun1(sK0,sK0,X5,X6,sK1,k2_funct_1(sK1)) )
    | ~ spl3_93 ),
    inference(avatar_component_clause,[],[f809])).

fof(f809,plain,
    ( spl3_93
  <=> ! [X5,X6] :
        ( k6_partfun1(sK0) = k1_partfun1(sK0,sK0,X5,X6,sK1,k2_funct_1(sK1))
        | ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_93])])).

fof(f525,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0))
    | spl3_66 ),
    inference(avatar_component_clause,[],[f523])).

fof(f523,plain,
    ( spl3_66
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_66])])).

fof(f811,plain,
    ( spl3_93
    | ~ spl3_48
    | ~ spl3_64
    | ~ spl3_90 ),
    inference(avatar_split_clause,[],[f797,f791,f513,f382,f809])).

fof(f382,plain,
    ( spl3_48
  <=> k6_partfun1(sK0) = k5_relat_1(sK1,k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).

fof(f791,plain,
    ( spl3_90
  <=> ! [X1,X0,X2] :
        ( ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | k5_relat_1(sK1,X0) = k1_partfun1(sK0,sK0,X1,X2,sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_90])])).

fof(f797,plain,
    ( ! [X6,X5] :
        ( k6_partfun1(sK0) = k1_partfun1(sK0,sK0,X5,X6,sK1,k2_funct_1(sK1))
        | ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X5,X6))) )
    | ~ spl3_48
    | ~ spl3_64
    | ~ spl3_90 ),
    inference(forward_demodulation,[],[f796,f384])).

fof(f384,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK1,k2_funct_1(sK1))
    | ~ spl3_48 ),
    inference(avatar_component_clause,[],[f382])).

fof(f796,plain,
    ( ! [X6,X5] :
        ( ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
        | k5_relat_1(sK1,k2_funct_1(sK1)) = k1_partfun1(sK0,sK0,X5,X6,sK1,k2_funct_1(sK1)) )
    | ~ spl3_64
    | ~ spl3_90 ),
    inference(resolution,[],[f792,f515])).

fof(f792,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | k5_relat_1(sK1,X0) = k1_partfun1(sK0,sK0,X1,X2,sK1,X0) )
    | ~ spl3_90 ),
    inference(avatar_component_clause,[],[f791])).

fof(f793,plain,
    ( spl3_90
    | ~ spl3_4
    | ~ spl3_89 ),
    inference(avatar_split_clause,[],[f789,f786,f93,f791])).

fof(f786,plain,
    ( spl3_89
  <=> ! [X1,X3,X0,X2,X4] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
        | k1_partfun1(X3,X4,X1,X2,sK1,X0) = k5_relat_1(sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_89])])).

fof(f789,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | k5_relat_1(sK1,X0) = k1_partfun1(sK0,sK0,X1,X2,sK1,X0) )
    | ~ spl3_4
    | ~ spl3_89 ),
    inference(resolution,[],[f787,f95])).

fof(f787,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | k1_partfun1(X3,X4,X1,X2,sK1,X0) = k5_relat_1(sK1,X0) )
    | ~ spl3_89 ),
    inference(avatar_component_clause,[],[f786])).

fof(f788,plain,
    ( spl3_89
    | ~ spl3_1
    | ~ spl3_80 ),
    inference(avatar_split_clause,[],[f782,f655,f78,f786])).

fof(f782,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
        | k1_partfun1(X3,X4,X1,X2,sK1,X0) = k5_relat_1(sK1,X0) )
    | ~ spl3_1
    | ~ spl3_80 ),
    inference(resolution,[],[f656,f80])).

fof(f756,plain,
    ( spl3_84
    | ~ spl3_15
    | ~ spl3_25
    | ~ spl3_41
    | ~ spl3_69
    | ~ spl3_70 ),
    inference(avatar_split_clause,[],[f732,f555,f551,f330,f212,f145,f753])).

fof(f145,plain,
    ( spl3_15
  <=> ! [X1,X0,X2] :
        ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f212,plain,
    ( spl3_25
  <=> k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f330,plain,
    ( spl3_41
  <=> k6_partfun1(k2_relat_1(sK1)) = k6_partfun1(k1_relat_1(k2_funct_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).

fof(f551,plain,
    ( spl3_69
  <=> sK0 = k1_relset_1(sK0,sK0,k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_69])])).

fof(f732,plain,
    ( k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1)
    | ~ spl3_15
    | ~ spl3_25
    | ~ spl3_41
    | ~ spl3_69
    | ~ spl3_70 ),
    inference(backward_demodulation,[],[f214,f728])).

fof(f728,plain,
    ( k6_partfun1(sK0) = k6_partfun1(k2_relat_1(sK1))
    | ~ spl3_15
    | ~ spl3_41
    | ~ spl3_69
    | ~ spl3_70 ),
    inference(backward_demodulation,[],[f332,f724])).

fof(f724,plain,
    ( sK0 = k1_relat_1(k2_funct_1(sK1))
    | ~ spl3_15
    | ~ spl3_69
    | ~ spl3_70 ),
    inference(forward_demodulation,[],[f721,f553])).

fof(f553,plain,
    ( sK0 = k1_relset_1(sK0,sK0,k2_funct_1(sK1))
    | ~ spl3_69 ),
    inference(avatar_component_clause,[],[f551])).

fof(f721,plain,
    ( k1_relat_1(k2_funct_1(sK1)) = k1_relset_1(sK0,sK0,k2_funct_1(sK1))
    | ~ spl3_15
    | ~ spl3_70 ),
    inference(resolution,[],[f556,f146])).

fof(f146,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) )
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f145])).

fof(f332,plain,
    ( k6_partfun1(k2_relat_1(sK1)) = k6_partfun1(k1_relat_1(k2_funct_1(sK1)))
    | ~ spl3_41 ),
    inference(avatar_component_clause,[],[f330])).

fof(f214,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(k2_relat_1(sK1))
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f212])).

fof(f718,plain,
    ( spl3_70
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_65
    | ~ spl3_78 ),
    inference(avatar_split_clause,[],[f634,f626,f518,f93,f88,f83,f78,f555])).

fof(f83,plain,
    ( spl3_2
  <=> v1_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f88,plain,
    ( spl3_3
  <=> v3_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f518,plain,
    ( spl3_65
  <=> k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_65])])).

fof(f626,plain,
    ( spl3_78
  <=> ! [X1,X0] :
        ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        | ~ v3_funct_2(X1,X0,X0)
        | ~ v1_funct_2(X1,X0,X0)
        | ~ v1_funct_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_78])])).

fof(f634,plain,
    ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_65
    | ~ spl3_78 ),
    inference(forward_demodulation,[],[f633,f520])).

fof(f520,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ spl3_65 ),
    inference(avatar_component_clause,[],[f518])).

fof(f633,plain,
    ( m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_78 ),
    inference(subsumption_resolution,[],[f632,f80])).

fof(f632,plain,
    ( m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_78 ),
    inference(subsumption_resolution,[],[f631,f90])).

fof(f90,plain,
    ( v3_funct_2(sK1,sK0,sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f88])).

fof(f631,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_78 ),
    inference(subsumption_resolution,[],[f629,f95])).

fof(f629,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_funct_2(sK1,sK0,sK0)
    | m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ spl3_2
    | ~ spl3_78 ),
    inference(resolution,[],[f627,f85])).

fof(f85,plain,
    ( v1_funct_2(sK1,sK0,sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f83])).

fof(f627,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(X1,X0,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        | ~ v3_funct_2(X1,X0,X0)
        | m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        | ~ v1_funct_1(X1) )
    | ~ spl3_78 ),
    inference(avatar_component_clause,[],[f626])).

fof(f657,plain,(
    spl3_80 ),
    inference(avatar_split_clause,[],[f73,f655])).

fof(f73,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f628,plain,(
    spl3_78 ),
    inference(avatar_split_clause,[],[f66,f626])).

fof(f66,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_2)).

fof(f558,plain,
    ( spl3_69
    | ~ spl3_70
    | ~ spl3_34
    | ~ spl3_64
    | ~ spl3_68 ),
    inference(avatar_split_clause,[],[f549,f537,f513,f274,f555,f551])).

fof(f274,plain,
    ( spl3_34
  <=> ! [X1,X0] :
        ( k1_relset_1(X0,X0,X1) = X0
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        | ~ v1_funct_2(X1,X0,X0)
        | ~ v1_funct_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f537,plain,
    ( spl3_68
  <=> v1_funct_2(k2_funct_1(sK1),sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_68])])).

fof(f549,plain,
    ( ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK0 = k1_relset_1(sK0,sK0,k2_funct_1(sK1))
    | ~ spl3_34
    | ~ spl3_64
    | ~ spl3_68 ),
    inference(subsumption_resolution,[],[f544,f515])).

fof(f544,plain,
    ( ~ m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK0 = k1_relset_1(sK0,sK0,k2_funct_1(sK1))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ spl3_34
    | ~ spl3_68 ),
    inference(resolution,[],[f539,f275])).

fof(f275,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(X1,X0,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        | k1_relset_1(X0,X0,X1) = X0
        | ~ v1_funct_1(X1) )
    | ~ spl3_34 ),
    inference(avatar_component_clause,[],[f274])).

fof(f539,plain,
    ( v1_funct_2(k2_funct_1(sK1),sK0,sK0)
    | ~ spl3_68 ),
    inference(avatar_component_clause,[],[f537])).

fof(f540,plain,
    ( spl3_68
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_62
    | ~ spl3_65 ),
    inference(avatar_split_clause,[],[f535,f518,f498,f93,f88,f83,f78,f537])).

fof(f498,plain,
    ( spl3_62
  <=> ! [X1,X0] :
        ( v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        | ~ v3_funct_2(X1,X0,X0)
        | ~ v1_funct_2(X1,X0,X0)
        | ~ v1_funct_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_62])])).

fof(f535,plain,
    ( v1_funct_2(k2_funct_1(sK1),sK0,sK0)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_62
    | ~ spl3_65 ),
    inference(forward_demodulation,[],[f534,f520])).

fof(f534,plain,
    ( v1_funct_2(k2_funct_2(sK0,sK1),sK0,sK0)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_62 ),
    inference(subsumption_resolution,[],[f533,f80])).

fof(f533,plain,
    ( v1_funct_2(k2_funct_2(sK0,sK1),sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_62 ),
    inference(subsumption_resolution,[],[f532,f90])).

fof(f532,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | v1_funct_2(k2_funct_2(sK0,sK1),sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_62 ),
    inference(subsumption_resolution,[],[f531,f95])).

fof(f531,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_funct_2(sK1,sK0,sK0)
    | v1_funct_2(k2_funct_2(sK0,sK1),sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl3_2
    | ~ spl3_62 ),
    inference(resolution,[],[f499,f85])).

fof(f499,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(X1,X0,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        | ~ v3_funct_2(X1,X0,X0)
        | v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        | ~ v1_funct_1(X1) )
    | ~ spl3_62 ),
    inference(avatar_component_clause,[],[f498])).

fof(f530,plain,
    ( ~ spl3_66
    | ~ spl3_67
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_61 ),
    inference(avatar_split_clause,[],[f511,f494,f93,f88,f83,f78,f527,f523])).

fof(f494,plain,
    ( spl3_61
  <=> ! [X1,X0] :
        ( k2_funct_2(X0,X1) = k2_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        | ~ v3_funct_2(X1,X0,X0)
        | ~ v1_funct_2(X1,X0,X0)
        | ~ v1_funct_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_61])])).

fof(f511,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_61 ),
    inference(forward_demodulation,[],[f510,f508])).

fof(f508,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_61 ),
    inference(subsumption_resolution,[],[f507,f80])).

fof(f507,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_61 ),
    inference(subsumption_resolution,[],[f506,f90])).

fof(f506,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_61 ),
    inference(subsumption_resolution,[],[f505,f95])).

fof(f505,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_funct_2(sK1,sK0,sK0)
    | k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ spl3_2
    | ~ spl3_61 ),
    inference(resolution,[],[f495,f85])).

fof(f495,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(X1,X0,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        | ~ v3_funct_2(X1,X0,X0)
        | k2_funct_2(X0,X1) = k2_funct_1(X1)
        | ~ v1_funct_1(X1) )
    | ~ spl3_61 ),
    inference(avatar_component_clause,[],[f494])).

fof(f510,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_61 ),
    inference(backward_demodulation,[],[f52,f508])).

fof(f52,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,
    ( ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) )
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK1,sK0,sK0)
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f44])).

fof(f44,plain,
    ( ? [X0,X1] :
        ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
        | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v3_funct_2(sK1,sK0,sK0)
      & v1_funct_2(sK1,sK0,sK0)
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X1,X0,X0)
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_funct_2)).

fof(f521,plain,
    ( spl3_65
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_61 ),
    inference(avatar_split_clause,[],[f508,f494,f93,f88,f83,f78,f518])).

fof(f516,plain,
    ( spl3_64
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_57
    | ~ spl3_61 ),
    inference(avatar_split_clause,[],[f509,f494,f454,f93,f88,f83,f78,f513])).

fof(f454,plain,
    ( spl3_57
  <=> v1_funct_1(k2_funct_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).

fof(f509,plain,
    ( v1_funct_1(k2_funct_1(sK1))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_57
    | ~ spl3_61 ),
    inference(backward_demodulation,[],[f456,f508])).

fof(f456,plain,
    ( v1_funct_1(k2_funct_2(sK0,sK1))
    | ~ spl3_57 ),
    inference(avatar_component_clause,[],[f454])).

fof(f500,plain,(
    spl3_62 ),
    inference(avatar_split_clause,[],[f64,f498])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k2_funct_2(X0,X1),X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f496,plain,(
    spl3_61 ),
    inference(avatar_split_clause,[],[f62,f494])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_2(X0,X1) = k2_funct_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

fof(f457,plain,
    ( spl3_57
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_55 ),
    inference(avatar_split_clause,[],[f452,f434,f93,f88,f83,f78,f454])).

fof(f434,plain,
    ( spl3_55
  <=> ! [X1,X0] :
        ( v1_funct_1(k2_funct_2(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        | ~ v3_funct_2(X1,X0,X0)
        | ~ v1_funct_2(X1,X0,X0)
        | ~ v1_funct_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_55])])).

fof(f452,plain,
    ( v1_funct_1(k2_funct_2(sK0,sK1))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_55 ),
    inference(subsumption_resolution,[],[f451,f80])).

fof(f451,plain,
    ( v1_funct_1(k2_funct_2(sK0,sK1))
    | ~ v1_funct_1(sK1)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_55 ),
    inference(subsumption_resolution,[],[f450,f90])).

fof(f450,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | v1_funct_1(k2_funct_2(sK0,sK1))
    | ~ v1_funct_1(sK1)
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_55 ),
    inference(subsumption_resolution,[],[f449,f95])).

fof(f449,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v3_funct_2(sK1,sK0,sK0)
    | v1_funct_1(k2_funct_2(sK0,sK1))
    | ~ v1_funct_1(sK1)
    | ~ spl3_2
    | ~ spl3_55 ),
    inference(resolution,[],[f435,f85])).

fof(f435,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(X1,X0,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        | ~ v3_funct_2(X1,X0,X0)
        | v1_funct_1(k2_funct_2(X0,X1))
        | ~ v1_funct_1(X1) )
    | ~ spl3_55 ),
    inference(avatar_component_clause,[],[f434])).

fof(f436,plain,(
    spl3_55 ),
    inference(avatar_split_clause,[],[f63,f434])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k2_funct_2(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f385,plain,
    ( spl3_48
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_16
    | ~ spl3_26
    | ~ spl3_34 ),
    inference(avatar_split_clause,[],[f365,f274,f223,f152,f93,f83,f78,f382])).

fof(f152,plain,
    ( spl3_16
  <=> k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f223,plain,
    ( spl3_26
  <=> k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f365,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK1,k2_funct_1(sK1))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_16
    | ~ spl3_26
    | ~ spl3_34 ),
    inference(backward_demodulation,[],[f225,f360])).

fof(f360,plain,
    ( sK0 = k1_relat_1(sK1)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_16
    | ~ spl3_34 ),
    inference(backward_demodulation,[],[f154,f359])).

fof(f359,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK1)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_34 ),
    inference(subsumption_resolution,[],[f358,f80])).

fof(f358,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK1)
    | ~ v1_funct_1(sK1)
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_34 ),
    inference(subsumption_resolution,[],[f357,f95])).

fof(f357,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK0 = k1_relset_1(sK0,sK0,sK1)
    | ~ v1_funct_1(sK1)
    | ~ spl3_2
    | ~ spl3_34 ),
    inference(resolution,[],[f275,f85])).

fof(f154,plain,
    ( k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1)
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f152])).

fof(f225,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1))
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f223])).

fof(f333,plain,
    ( spl3_41
    | ~ spl3_1
    | ~ spl3_10
    | ~ spl3_23
    | ~ spl3_24
    | ~ spl3_25
    | ~ spl3_35 ),
    inference(avatar_split_clause,[],[f328,f278,f212,f204,f187,f121,f78,f330])).

fof(f121,plain,
    ( spl3_10
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f187,plain,
    ( spl3_23
  <=> v2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f204,plain,
    ( spl3_24
  <=> sK1 = k2_funct_1(k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f278,plain,
    ( spl3_35
  <=> ! [X0] :
        ( k5_relat_1(k2_funct_1(X0),k2_funct_1(k2_funct_1(X0))) = k6_partfun1(k1_relat_1(k2_funct_1(X0)))
        | ~ v2_funct_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).

fof(f328,plain,
    ( k6_partfun1(k2_relat_1(sK1)) = k6_partfun1(k1_relat_1(k2_funct_1(sK1)))
    | ~ spl3_1
    | ~ spl3_10
    | ~ spl3_23
    | ~ spl3_24
    | ~ spl3_25
    | ~ spl3_35 ),
    inference(forward_demodulation,[],[f327,f214])).

fof(f327,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(k1_relat_1(k2_funct_1(sK1)))
    | ~ spl3_1
    | ~ spl3_10
    | ~ spl3_23
    | ~ spl3_24
    | ~ spl3_35 ),
    inference(forward_demodulation,[],[f326,f206])).

fof(f206,plain,
    ( sK1 = k2_funct_1(k2_funct_1(sK1))
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f204])).

fof(f326,plain,
    ( k5_relat_1(k2_funct_1(sK1),k2_funct_1(k2_funct_1(sK1))) = k6_partfun1(k1_relat_1(k2_funct_1(sK1)))
    | ~ spl3_1
    | ~ spl3_10
    | ~ spl3_23
    | ~ spl3_35 ),
    inference(subsumption_resolution,[],[f325,f123])).

fof(f123,plain,
    ( v1_relat_1(sK1)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f121])).

fof(f325,plain,
    ( k5_relat_1(k2_funct_1(sK1),k2_funct_1(k2_funct_1(sK1))) = k6_partfun1(k1_relat_1(k2_funct_1(sK1)))
    | ~ v1_relat_1(sK1)
    | ~ spl3_1
    | ~ spl3_23
    | ~ spl3_35 ),
    inference(subsumption_resolution,[],[f322,f80])).

fof(f322,plain,
    ( k5_relat_1(k2_funct_1(sK1),k2_funct_1(k2_funct_1(sK1))) = k6_partfun1(k1_relat_1(k2_funct_1(sK1)))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl3_23
    | ~ spl3_35 ),
    inference(resolution,[],[f279,f189])).

fof(f189,plain,
    ( v2_funct_1(sK1)
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f187])).

fof(f279,plain,
    ( ! [X0] :
        ( ~ v2_funct_1(X0)
        | k5_relat_1(k2_funct_1(X0),k2_funct_1(k2_funct_1(X0))) = k6_partfun1(k1_relat_1(k2_funct_1(X0)))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl3_35 ),
    inference(avatar_component_clause,[],[f278])).

fof(f280,plain,
    ( spl3_35
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_12
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f219,f180,f130,f106,f102,f278])).

fof(f102,plain,
    ( spl3_6
  <=> ! [X0] :
        ( v1_relat_1(k2_funct_1(X0))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f106,plain,
    ( spl3_7
  <=> ! [X0] :
        ( v1_funct_1(k2_funct_1(X0))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f130,plain,
    ( spl3_12
  <=> ! [X0] :
        ( v2_funct_1(k2_funct_1(X0))
        | ~ v2_funct_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f180,plain,
    ( spl3_22
  <=> ! [X0] :
        ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
        | ~ v2_funct_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f219,plain,
    ( ! [X0] :
        ( k5_relat_1(k2_funct_1(X0),k2_funct_1(k2_funct_1(X0))) = k6_partfun1(k1_relat_1(k2_funct_1(X0)))
        | ~ v2_funct_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_12
    | ~ spl3_22 ),
    inference(subsumption_resolution,[],[f218,f103])).

fof(f103,plain,
    ( ! [X0] :
        ( v1_relat_1(k2_funct_1(X0))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f102])).

fof(f218,plain,
    ( ! [X0] :
        ( k5_relat_1(k2_funct_1(X0),k2_funct_1(k2_funct_1(X0))) = k6_partfun1(k1_relat_1(k2_funct_1(X0)))
        | ~ v1_relat_1(k2_funct_1(X0))
        | ~ v2_funct_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl3_7
    | ~ spl3_12
    | ~ spl3_22 ),
    inference(subsumption_resolution,[],[f216,f107])).

fof(f107,plain,
    ( ! [X0] :
        ( v1_funct_1(k2_funct_1(X0))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f106])).

fof(f216,plain,
    ( ! [X0] :
        ( k5_relat_1(k2_funct_1(X0),k2_funct_1(k2_funct_1(X0))) = k6_partfun1(k1_relat_1(k2_funct_1(X0)))
        | ~ v1_funct_1(k2_funct_1(X0))
        | ~ v1_relat_1(k2_funct_1(X0))
        | ~ v2_funct_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl3_12
    | ~ spl3_22 ),
    inference(resolution,[],[f181,f131])).

fof(f131,plain,
    ( ! [X0] :
        ( v2_funct_1(k2_funct_1(X0))
        | ~ v2_funct_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f130])).

fof(f181,plain,
    ( ! [X0] :
        ( ~ v2_funct_1(X0)
        | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f180])).

fof(f276,plain,(
    spl3_34 ),
    inference(avatar_split_clause,[],[f67,f274])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).

fof(f268,plain,
    ( spl3_32
    | ~ spl3_8
    | ~ spl3_31 ),
    inference(avatar_split_clause,[],[f262,f259,f110,f266])).

fof(f110,plain,
    ( spl3_8
  <=> ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f259,plain,
    ( spl3_31
  <=> ! [X5,X4] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X5)))
        | r2_relset_1(X5,X5,k6_partfun1(X5),k6_partfun1(X5)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f262,plain,
    ( ! [X0] : r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0))
    | ~ spl3_8
    | ~ spl3_31 ),
    inference(resolution,[],[f260,f111])).

fof(f111,plain,
    ( ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f110])).

fof(f260,plain,
    ( ! [X4,X5] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X5)))
        | r2_relset_1(X5,X5,k6_partfun1(X5),k6_partfun1(X5)) )
    | ~ spl3_31 ),
    inference(avatar_component_clause,[],[f259])).

fof(f261,plain,
    ( spl3_31
    | ~ spl3_8
    | ~ spl3_28 ),
    inference(avatar_split_clause,[],[f244,f239,f110,f259])).

fof(f239,plain,
    ( spl3_28
  <=> ! [X1,X3,X0,X2] :
        ( r2_relset_1(X0,X1,X2,X2)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f244,plain,
    ( ! [X4,X5] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X5)))
        | r2_relset_1(X5,X5,k6_partfun1(X5),k6_partfun1(X5)) )
    | ~ spl3_8
    | ~ spl3_28 ),
    inference(resolution,[],[f240,f111])).

fof(f240,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | r2_relset_1(X0,X1,X2,X2) )
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f239])).

fof(f241,plain,(
    spl3_28 ),
    inference(avatar_split_clause,[],[f72,f239])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

fof(f226,plain,
    ( spl3_26
    | ~ spl3_1
    | ~ spl3_10
    | ~ spl3_22
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f221,f187,f180,f121,f78,f223])).

fof(f221,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1))
    | ~ spl3_1
    | ~ spl3_10
    | ~ spl3_22
    | ~ spl3_23 ),
    inference(subsumption_resolution,[],[f220,f123])).

fof(f220,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ spl3_1
    | ~ spl3_22
    | ~ spl3_23 ),
    inference(subsumption_resolution,[],[f217,f80])).

fof(f217,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl3_22
    | ~ spl3_23 ),
    inference(resolution,[],[f181,f189])).

fof(f215,plain,
    ( spl3_25
    | ~ spl3_1
    | ~ spl3_10
    | ~ spl3_21
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f198,f187,f176,f121,f78,f212])).

fof(f176,plain,
    ( spl3_21
  <=> ! [X0] :
        ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
        | ~ v2_funct_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f198,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(k2_relat_1(sK1))
    | ~ spl3_1
    | ~ spl3_10
    | ~ spl3_21
    | ~ spl3_23 ),
    inference(subsumption_resolution,[],[f197,f123])).

fof(f197,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(k2_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ spl3_1
    | ~ spl3_21
    | ~ spl3_23 ),
    inference(subsumption_resolution,[],[f194,f80])).

fof(f194,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(k2_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl3_21
    | ~ spl3_23 ),
    inference(resolution,[],[f189,f177])).

fof(f177,plain,
    ( ! [X0] :
        ( ~ v2_funct_1(X0)
        | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f176])).

fof(f207,plain,
    ( spl3_24
    | ~ spl3_1
    | ~ spl3_10
    | ~ spl3_14
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f202,f187,f138,f121,f78,f204])).

fof(f138,plain,
    ( spl3_14
  <=> ! [X0] :
        ( k2_funct_1(k2_funct_1(X0)) = X0
        | ~ v2_funct_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f202,plain,
    ( sK1 = k2_funct_1(k2_funct_1(sK1))
    | ~ spl3_1
    | ~ spl3_10
    | ~ spl3_14
    | ~ spl3_23 ),
    inference(subsumption_resolution,[],[f201,f123])).

fof(f201,plain,
    ( sK1 = k2_funct_1(k2_funct_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ spl3_1
    | ~ spl3_14
    | ~ spl3_23 ),
    inference(subsumption_resolution,[],[f196,f80])).

fof(f196,plain,
    ( sK1 = k2_funct_1(k2_funct_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl3_14
    | ~ spl3_23 ),
    inference(resolution,[],[f189,f139])).

fof(f139,plain,
    ( ! [X0] :
        ( ~ v2_funct_1(X0)
        | k2_funct_1(k2_funct_1(X0)) = X0
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f138])).

fof(f190,plain,
    ( spl3_23
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f185,f172,f93,f88,f78,f187])).

fof(f172,plain,
    ( spl3_20
  <=> ! [X1,X0,X2] :
        ( v2_funct_1(X2)
        | ~ v3_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f185,plain,
    ( v2_funct_1(sK1)
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_20 ),
    inference(subsumption_resolution,[],[f184,f95])).

fof(f184,plain,
    ( v2_funct_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_20 ),
    inference(subsumption_resolution,[],[f183,f80])).

fof(f183,plain,
    ( v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl3_3
    | ~ spl3_20 ),
    inference(resolution,[],[f173,f90])).

fof(f173,plain,
    ( ! [X2,X0,X1] :
        ( ~ v3_funct_2(X2,X0,X1)
        | v2_funct_1(X2)
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f172])).

fof(f182,plain,(
    spl3_22 ),
    inference(avatar_split_clause,[],[f76,f180])).

fof(f76,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f59,f53])).

fof(f53,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f59,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

fof(f178,plain,(
    spl3_21 ),
    inference(avatar_split_clause,[],[f75,f176])).

fof(f75,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f60,f53])).

fof(f60,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f174,plain,(
    spl3_20 ),
    inference(avatar_split_clause,[],[f71,f172])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

fof(f155,plain,
    ( spl3_16
    | ~ spl3_4
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f148,f145,f93,f152])).

fof(f148,plain,
    ( k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1)
    | ~ spl3_4
    | ~ spl3_15 ),
    inference(resolution,[],[f146,f95])).

fof(f147,plain,(
    spl3_15 ),
    inference(avatar_split_clause,[],[f69,f145])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f140,plain,(
    spl3_14 ),
    inference(avatar_split_clause,[],[f58,f138])).

fof(f58,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

fof(f132,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f57,f130])).

fof(f57,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => v2_funct_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_1)).

fof(f124,plain,
    ( spl3_10
    | ~ spl3_4
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f117,f114,f93,f121])).

fof(f114,plain,
    ( spl3_9
  <=> ! [X1,X0,X2] :
        ( v1_relat_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f117,plain,
    ( v1_relat_1(sK1)
    | ~ spl3_4
    | ~ spl3_9 ),
    inference(resolution,[],[f115,f95])).

fof(f115,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_relat_1(X2) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f114])).

fof(f116,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f68,f114])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f112,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f74,f110])).

fof(f74,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f54,f53])).

fof(f54,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

fof(f108,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f56,f106])).

fof(f56,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f104,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f55,f102])).

fof(f55,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f96,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f51,f93])).

fof(f51,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f45])).

fof(f91,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f50,f88])).

fof(f50,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f86,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f49,f83])).

fof(f49,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f81,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f48,f78])).

fof(f48,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f45])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:00:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.41  % (15857)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.46  % (15852)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.46  % (15855)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.47  % (15861)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.47  % (15854)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.47  % (15851)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.47  % (15853)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.47  % (15863)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.48  % (15856)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.48  % (15850)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.48  % (15848)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.48  % (15854)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f856,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(avatar_sat_refutation,[],[f81,f86,f91,f96,f104,f108,f112,f116,f124,f132,f140,f147,f155,f174,f178,f182,f190,f207,f215,f226,f241,f261,f268,f276,f280,f333,f385,f436,f457,f496,f500,f516,f521,f530,f540,f558,f628,f657,f718,f756,f788,f793,f811,f815,f834,f839,f851,f855])).
% 0.20/0.48  fof(f855,plain,(
% 0.20/0.48    ~spl3_4 | ~spl3_32 | spl3_67 | ~spl3_99),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f854])).
% 0.20/0.48  fof(f854,plain,(
% 0.20/0.48    $false | (~spl3_4 | ~spl3_32 | spl3_67 | ~spl3_99)),
% 0.20/0.48    inference(subsumption_resolution,[],[f853,f267])).
% 0.20/0.48  fof(f267,plain,(
% 0.20/0.48    ( ! [X0] : (r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0))) ) | ~spl3_32),
% 0.20/0.48    inference(avatar_component_clause,[],[f266])).
% 0.20/0.48  fof(f266,plain,(
% 0.20/0.48    spl3_32 <=> ! [X0] : r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 0.20/0.48  fof(f853,plain,(
% 0.20/0.48    ~r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) | (~spl3_4 | spl3_67 | ~spl3_99)),
% 0.20/0.48    inference(backward_demodulation,[],[f529,f852])).
% 0.20/0.48  fof(f852,plain,(
% 0.20/0.48    k6_partfun1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) | (~spl3_4 | ~spl3_99)),
% 0.20/0.48    inference(resolution,[],[f850,f95])).
% 0.20/0.48  fof(f95,plain,(
% 0.20/0.48    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl3_4),
% 0.20/0.48    inference(avatar_component_clause,[],[f93])).
% 0.20/0.48  fof(f93,plain,(
% 0.20/0.48    spl3_4 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.48  fof(f850,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k6_partfun1(sK0) = k1_partfun1(sK0,sK0,X0,X1,k2_funct_1(sK1),sK1)) ) | ~spl3_99),
% 0.20/0.48    inference(avatar_component_clause,[],[f849])).
% 0.20/0.48  fof(f849,plain,(
% 0.20/0.48    spl3_99 <=> ! [X1,X0] : (k6_partfun1(sK0) = k1_partfun1(sK0,sK0,X0,X1,k2_funct_1(sK1),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_99])])).
% 0.20/0.48  fof(f529,plain,(
% 0.20/0.48    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0)) | spl3_67),
% 0.20/0.48    inference(avatar_component_clause,[],[f527])).
% 0.20/0.48  fof(f527,plain,(
% 0.20/0.48    spl3_67 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_67])])).
% 0.20/0.48  fof(f851,plain,(
% 0.20/0.48    spl3_99 | ~spl3_1 | ~spl3_84 | ~spl3_97),
% 0.20/0.48    inference(avatar_split_clause,[],[f843,f837,f753,f78,f849])).
% 0.20/0.48  fof(f78,plain,(
% 0.20/0.48    spl3_1 <=> v1_funct_1(sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.48  fof(f753,plain,(
% 0.20/0.48    spl3_84 <=> k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_84])])).
% 0.20/0.48  fof(f837,plain,(
% 0.20/0.48    spl3_97 <=> ! [X1,X0,X2] : (~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k5_relat_1(k2_funct_1(sK1),X0) = k1_partfun1(sK0,sK0,X1,X2,k2_funct_1(sK1),X0))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_97])])).
% 0.20/0.48  fof(f843,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k6_partfun1(sK0) = k1_partfun1(sK0,sK0,X0,X1,k2_funct_1(sK1),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | (~spl3_1 | ~spl3_84 | ~spl3_97)),
% 0.20/0.48    inference(forward_demodulation,[],[f840,f755])).
% 0.20/0.48  fof(f755,plain,(
% 0.20/0.48    k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1) | ~spl3_84),
% 0.20/0.48    inference(avatar_component_clause,[],[f753])).
% 0.20/0.48  fof(f840,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k5_relat_1(k2_funct_1(sK1),sK1) = k1_partfun1(sK0,sK0,X0,X1,k2_funct_1(sK1),sK1)) ) | (~spl3_1 | ~spl3_97)),
% 0.20/0.48    inference(resolution,[],[f838,f80])).
% 0.20/0.48  fof(f80,plain,(
% 0.20/0.48    v1_funct_1(sK1) | ~spl3_1),
% 0.20/0.48    inference(avatar_component_clause,[],[f78])).
% 0.20/0.48  fof(f838,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k5_relat_1(k2_funct_1(sK1),X0) = k1_partfun1(sK0,sK0,X1,X2,k2_funct_1(sK1),X0)) ) | ~spl3_97),
% 0.20/0.48    inference(avatar_component_clause,[],[f837])).
% 0.20/0.48  fof(f839,plain,(
% 0.20/0.48    spl3_97 | ~spl3_70 | ~spl3_96),
% 0.20/0.48    inference(avatar_split_clause,[],[f835,f832,f555,f837])).
% 0.20/0.48  fof(f555,plain,(
% 0.20/0.48    spl3_70 <=> m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_70])])).
% 0.20/0.48  fof(f832,plain,(
% 0.20/0.48    spl3_96 <=> ! [X11,X13,X15,X12,X14] : (~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X12,X13))) | ~v1_funct_1(X11) | ~m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X14,X15))) | k1_partfun1(X14,X15,X12,X13,k2_funct_1(sK1),X11) = k5_relat_1(k2_funct_1(sK1),X11))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_96])])).
% 0.20/0.48  fof(f835,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k5_relat_1(k2_funct_1(sK1),X0) = k1_partfun1(sK0,sK0,X1,X2,k2_funct_1(sK1),X0)) ) | (~spl3_70 | ~spl3_96)),
% 0.20/0.48    inference(resolution,[],[f833,f556])).
% 0.20/0.48  fof(f556,plain,(
% 0.20/0.48    m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl3_70),
% 0.20/0.48    inference(avatar_component_clause,[],[f555])).
% 0.20/0.48  fof(f833,plain,(
% 0.20/0.48    ( ! [X14,X12,X15,X13,X11] : (~m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X14,X15))) | ~v1_funct_1(X11) | ~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X12,X13))) | k1_partfun1(X14,X15,X12,X13,k2_funct_1(sK1),X11) = k5_relat_1(k2_funct_1(sK1),X11)) ) | ~spl3_96),
% 0.20/0.48    inference(avatar_component_clause,[],[f832])).
% 0.20/0.48  fof(f834,plain,(
% 0.20/0.48    spl3_96 | ~spl3_64 | ~spl3_80),
% 0.20/0.48    inference(avatar_split_clause,[],[f784,f655,f513,f832])).
% 0.20/0.48  fof(f513,plain,(
% 0.20/0.48    spl3_64 <=> v1_funct_1(k2_funct_1(sK1))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_64])])).
% 0.20/0.48  fof(f655,plain,(
% 0.20/0.48    spl3_80 <=> ! [X1,X3,X5,X0,X2,X4] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_80])])).
% 0.20/0.48  fof(f784,plain,(
% 0.20/0.48    ( ! [X14,X12,X15,X13,X11] : (~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X12,X13))) | ~v1_funct_1(X11) | ~m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X14,X15))) | k1_partfun1(X14,X15,X12,X13,k2_funct_1(sK1),X11) = k5_relat_1(k2_funct_1(sK1),X11)) ) | (~spl3_64 | ~spl3_80)),
% 0.20/0.48    inference(resolution,[],[f656,f515])).
% 0.20/0.48  fof(f515,plain,(
% 0.20/0.48    v1_funct_1(k2_funct_1(sK1)) | ~spl3_64),
% 0.20/0.48    inference(avatar_component_clause,[],[f513])).
% 0.20/0.48  fof(f656,plain,(
% 0.20/0.48    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)) ) | ~spl3_80),
% 0.20/0.48    inference(avatar_component_clause,[],[f655])).
% 0.20/0.48  fof(f815,plain,(
% 0.20/0.48    ~spl3_32 | spl3_66 | ~spl3_70 | ~spl3_93),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f814])).
% 0.20/0.48  fof(f814,plain,(
% 0.20/0.48    $false | (~spl3_32 | spl3_66 | ~spl3_70 | ~spl3_93)),
% 0.20/0.48    inference(subsumption_resolution,[],[f813,f267])).
% 0.20/0.48  fof(f813,plain,(
% 0.20/0.48    ~r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) | (spl3_66 | ~spl3_70 | ~spl3_93)),
% 0.20/0.48    inference(backward_demodulation,[],[f525,f812])).
% 0.20/0.48  fof(f812,plain,(
% 0.20/0.48    k6_partfun1(sK0) = k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) | (~spl3_70 | ~spl3_93)),
% 0.20/0.48    inference(resolution,[],[f810,f556])).
% 0.20/0.48  fof(f810,plain,(
% 0.20/0.48    ( ! [X6,X5] : (~m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | k6_partfun1(sK0) = k1_partfun1(sK0,sK0,X5,X6,sK1,k2_funct_1(sK1))) ) | ~spl3_93),
% 0.20/0.48    inference(avatar_component_clause,[],[f809])).
% 0.20/0.48  fof(f809,plain,(
% 0.20/0.48    spl3_93 <=> ! [X5,X6] : (k6_partfun1(sK0) = k1_partfun1(sK0,sK0,X5,X6,sK1,k2_funct_1(sK1)) | ~m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X5,X6))))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_93])])).
% 0.20/0.48  fof(f525,plain,(
% 0.20/0.48    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) | spl3_66),
% 0.20/0.48    inference(avatar_component_clause,[],[f523])).
% 0.20/0.48  fof(f523,plain,(
% 0.20/0.48    spl3_66 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_66])])).
% 0.20/0.48  fof(f811,plain,(
% 0.20/0.48    spl3_93 | ~spl3_48 | ~spl3_64 | ~spl3_90),
% 0.20/0.48    inference(avatar_split_clause,[],[f797,f791,f513,f382,f809])).
% 0.20/0.48  fof(f382,plain,(
% 0.20/0.48    spl3_48 <=> k6_partfun1(sK0) = k5_relat_1(sK1,k2_funct_1(sK1))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).
% 0.20/0.48  fof(f791,plain,(
% 0.20/0.48    spl3_90 <=> ! [X1,X0,X2] : (~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k5_relat_1(sK1,X0) = k1_partfun1(sK0,sK0,X1,X2,sK1,X0))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_90])])).
% 0.20/0.48  fof(f797,plain,(
% 0.20/0.48    ( ! [X6,X5] : (k6_partfun1(sK0) = k1_partfun1(sK0,sK0,X5,X6,sK1,k2_funct_1(sK1)) | ~m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X5,X6)))) ) | (~spl3_48 | ~spl3_64 | ~spl3_90)),
% 0.20/0.48    inference(forward_demodulation,[],[f796,f384])).
% 0.20/0.48  fof(f384,plain,(
% 0.20/0.48    k6_partfun1(sK0) = k5_relat_1(sK1,k2_funct_1(sK1)) | ~spl3_48),
% 0.20/0.48    inference(avatar_component_clause,[],[f382])).
% 0.20/0.48  fof(f796,plain,(
% 0.20/0.48    ( ! [X6,X5] : (~m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | k5_relat_1(sK1,k2_funct_1(sK1)) = k1_partfun1(sK0,sK0,X5,X6,sK1,k2_funct_1(sK1))) ) | (~spl3_64 | ~spl3_90)),
% 0.20/0.48    inference(resolution,[],[f792,f515])).
% 0.20/0.48  fof(f792,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k5_relat_1(sK1,X0) = k1_partfun1(sK0,sK0,X1,X2,sK1,X0)) ) | ~spl3_90),
% 0.20/0.48    inference(avatar_component_clause,[],[f791])).
% 0.20/0.48  fof(f793,plain,(
% 0.20/0.48    spl3_90 | ~spl3_4 | ~spl3_89),
% 0.20/0.48    inference(avatar_split_clause,[],[f789,f786,f93,f791])).
% 0.20/0.48  fof(f786,plain,(
% 0.20/0.48    spl3_89 <=> ! [X1,X3,X0,X2,X4] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | k1_partfun1(X3,X4,X1,X2,sK1,X0) = k5_relat_1(sK1,X0))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_89])])).
% 0.20/0.48  fof(f789,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k5_relat_1(sK1,X0) = k1_partfun1(sK0,sK0,X1,X2,sK1,X0)) ) | (~spl3_4 | ~spl3_89)),
% 0.20/0.48    inference(resolution,[],[f787,f95])).
% 0.20/0.48  fof(f787,plain,(
% 0.20/0.48    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k1_partfun1(X3,X4,X1,X2,sK1,X0) = k5_relat_1(sK1,X0)) ) | ~spl3_89),
% 0.20/0.48    inference(avatar_component_clause,[],[f786])).
% 0.20/0.48  fof(f788,plain,(
% 0.20/0.48    spl3_89 | ~spl3_1 | ~spl3_80),
% 0.20/0.48    inference(avatar_split_clause,[],[f782,f655,f78,f786])).
% 0.20/0.48  fof(f782,plain,(
% 0.20/0.48    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | k1_partfun1(X3,X4,X1,X2,sK1,X0) = k5_relat_1(sK1,X0)) ) | (~spl3_1 | ~spl3_80)),
% 0.20/0.48    inference(resolution,[],[f656,f80])).
% 0.20/0.48  fof(f756,plain,(
% 0.20/0.48    spl3_84 | ~spl3_15 | ~spl3_25 | ~spl3_41 | ~spl3_69 | ~spl3_70),
% 0.20/0.48    inference(avatar_split_clause,[],[f732,f555,f551,f330,f212,f145,f753])).
% 0.20/0.48  fof(f145,plain,(
% 0.20/0.48    spl3_15 <=> ! [X1,X0,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.20/0.48  fof(f212,plain,(
% 0.20/0.48    spl3_25 <=> k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(k2_relat_1(sK1))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.20/0.48  fof(f330,plain,(
% 0.20/0.48    spl3_41 <=> k6_partfun1(k2_relat_1(sK1)) = k6_partfun1(k1_relat_1(k2_funct_1(sK1)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).
% 0.20/0.48  fof(f551,plain,(
% 0.20/0.48    spl3_69 <=> sK0 = k1_relset_1(sK0,sK0,k2_funct_1(sK1))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_69])])).
% 0.20/0.48  fof(f732,plain,(
% 0.20/0.48    k6_partfun1(sK0) = k5_relat_1(k2_funct_1(sK1),sK1) | (~spl3_15 | ~spl3_25 | ~spl3_41 | ~spl3_69 | ~spl3_70)),
% 0.20/0.48    inference(backward_demodulation,[],[f214,f728])).
% 0.20/0.48  fof(f728,plain,(
% 0.20/0.48    k6_partfun1(sK0) = k6_partfun1(k2_relat_1(sK1)) | (~spl3_15 | ~spl3_41 | ~spl3_69 | ~spl3_70)),
% 0.20/0.48    inference(backward_demodulation,[],[f332,f724])).
% 0.20/0.48  fof(f724,plain,(
% 0.20/0.48    sK0 = k1_relat_1(k2_funct_1(sK1)) | (~spl3_15 | ~spl3_69 | ~spl3_70)),
% 0.20/0.48    inference(forward_demodulation,[],[f721,f553])).
% 0.20/0.48  fof(f553,plain,(
% 0.20/0.48    sK0 = k1_relset_1(sK0,sK0,k2_funct_1(sK1)) | ~spl3_69),
% 0.20/0.48    inference(avatar_component_clause,[],[f551])).
% 0.20/0.48  fof(f721,plain,(
% 0.20/0.48    k1_relat_1(k2_funct_1(sK1)) = k1_relset_1(sK0,sK0,k2_funct_1(sK1)) | (~spl3_15 | ~spl3_70)),
% 0.20/0.48    inference(resolution,[],[f556,f146])).
% 0.20/0.48  fof(f146,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) ) | ~spl3_15),
% 0.20/0.48    inference(avatar_component_clause,[],[f145])).
% 0.20/0.48  fof(f332,plain,(
% 0.20/0.48    k6_partfun1(k2_relat_1(sK1)) = k6_partfun1(k1_relat_1(k2_funct_1(sK1))) | ~spl3_41),
% 0.20/0.48    inference(avatar_component_clause,[],[f330])).
% 0.20/0.48  fof(f214,plain,(
% 0.20/0.48    k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(k2_relat_1(sK1)) | ~spl3_25),
% 0.20/0.48    inference(avatar_component_clause,[],[f212])).
% 0.20/0.48  fof(f718,plain,(
% 0.20/0.48    spl3_70 | ~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_65 | ~spl3_78),
% 0.20/0.48    inference(avatar_split_clause,[],[f634,f626,f518,f93,f88,f83,f78,f555])).
% 0.20/0.48  fof(f83,plain,(
% 0.20/0.48    spl3_2 <=> v1_funct_2(sK1,sK0,sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.48  fof(f88,plain,(
% 0.20/0.48    spl3_3 <=> v3_funct_2(sK1,sK0,sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.48  fof(f518,plain,(
% 0.20/0.48    spl3_65 <=> k2_funct_2(sK0,sK1) = k2_funct_1(sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_65])])).
% 0.20/0.48  fof(f626,plain,(
% 0.20/0.48    spl3_78 <=> ! [X1,X0] : (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_78])])).
% 0.20/0.48  fof(f634,plain,(
% 0.20/0.48    m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | (~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_65 | ~spl3_78)),
% 0.20/0.48    inference(forward_demodulation,[],[f633,f520])).
% 0.20/0.48  fof(f520,plain,(
% 0.20/0.48    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~spl3_65),
% 0.20/0.48    inference(avatar_component_clause,[],[f518])).
% 0.20/0.48  fof(f633,plain,(
% 0.20/0.48    m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | (~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_78)),
% 0.20/0.48    inference(subsumption_resolution,[],[f632,f80])).
% 0.20/0.48  fof(f632,plain,(
% 0.20/0.48    m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1) | (~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_78)),
% 0.20/0.48    inference(subsumption_resolution,[],[f631,f90])).
% 0.20/0.48  fof(f90,plain,(
% 0.20/0.48    v3_funct_2(sK1,sK0,sK0) | ~spl3_3),
% 0.20/0.48    inference(avatar_component_clause,[],[f88])).
% 0.20/0.48  fof(f631,plain,(
% 0.20/0.48    ~v3_funct_2(sK1,sK0,sK0) | m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1) | (~spl3_2 | ~spl3_4 | ~spl3_78)),
% 0.20/0.48    inference(subsumption_resolution,[],[f629,f95])).
% 0.20/0.48  fof(f629,plain,(
% 0.20/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v3_funct_2(sK1,sK0,sK0) | m1_subset_1(k2_funct_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1) | (~spl3_2 | ~spl3_78)),
% 0.20/0.48    inference(resolution,[],[f627,f85])).
% 0.20/0.48  fof(f85,plain,(
% 0.20/0.48    v1_funct_2(sK1,sK0,sK0) | ~spl3_2),
% 0.20/0.48    inference(avatar_component_clause,[],[f83])).
% 0.20/0.48  fof(f627,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~v1_funct_2(X1,X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_1(X1)) ) | ~spl3_78),
% 0.20/0.48    inference(avatar_component_clause,[],[f626])).
% 0.20/0.48  fof(f657,plain,(
% 0.20/0.48    spl3_80),
% 0.20/0.48    inference(avatar_split_clause,[],[f73,f655])).
% 0.20/0.48  fof(f73,plain,(
% 0.20/0.48    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f43])).
% 0.20/0.48  fof(f43,plain,(
% 0.20/0.48    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 0.20/0.48    inference(flattening,[],[f42])).
% 0.20/0.48  fof(f42,plain,(
% 0.20/0.48    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 0.20/0.48    inference(ennf_transformation,[],[f12])).
% 0.20/0.48  fof(f12,axiom,(
% 0.20/0.48    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 0.20/0.48  fof(f628,plain,(
% 0.20/0.48    spl3_78),
% 0.20/0.48    inference(avatar_split_clause,[],[f66,f626])).
% 0.20/0.48  fof(f66,plain,(
% 0.20/0.48    ( ! [X0,X1] : (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f33])).
% 0.20/0.48  fof(f33,plain,(
% 0.20/0.48    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.20/0.48    inference(flattening,[],[f32])).
% 0.20/0.48  fof(f32,plain,(
% 0.20/0.48    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 0.20/0.48    inference(ennf_transformation,[],[f11])).
% 0.20/0.48  fof(f11,axiom,(
% 0.20/0.48    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_2)).
% 0.20/0.48  fof(f558,plain,(
% 0.20/0.48    spl3_69 | ~spl3_70 | ~spl3_34 | ~spl3_64 | ~spl3_68),
% 0.20/0.48    inference(avatar_split_clause,[],[f549,f537,f513,f274,f555,f551])).
% 0.20/0.48  fof(f274,plain,(
% 0.20/0.48    spl3_34 <=> ! [X1,X0] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 0.20/0.48  fof(f537,plain,(
% 0.20/0.48    spl3_68 <=> v1_funct_2(k2_funct_1(sK1),sK0,sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_68])])).
% 0.20/0.48  fof(f549,plain,(
% 0.20/0.48    ~m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | sK0 = k1_relset_1(sK0,sK0,k2_funct_1(sK1)) | (~spl3_34 | ~spl3_64 | ~spl3_68)),
% 0.20/0.48    inference(subsumption_resolution,[],[f544,f515])).
% 0.20/0.48  fof(f544,plain,(
% 0.20/0.48    ~m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | sK0 = k1_relset_1(sK0,sK0,k2_funct_1(sK1)) | ~v1_funct_1(k2_funct_1(sK1)) | (~spl3_34 | ~spl3_68)),
% 0.20/0.48    inference(resolution,[],[f539,f275])).
% 0.20/0.48  fof(f275,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~v1_funct_2(X1,X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | k1_relset_1(X0,X0,X1) = X0 | ~v1_funct_1(X1)) ) | ~spl3_34),
% 0.20/0.48    inference(avatar_component_clause,[],[f274])).
% 0.20/0.48  fof(f539,plain,(
% 0.20/0.48    v1_funct_2(k2_funct_1(sK1),sK0,sK0) | ~spl3_68),
% 0.20/0.48    inference(avatar_component_clause,[],[f537])).
% 0.20/0.48  fof(f540,plain,(
% 0.20/0.48    spl3_68 | ~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_62 | ~spl3_65),
% 0.20/0.48    inference(avatar_split_clause,[],[f535,f518,f498,f93,f88,f83,f78,f537])).
% 0.20/0.48  fof(f498,plain,(
% 0.20/0.48    spl3_62 <=> ! [X1,X0] : (v1_funct_2(k2_funct_2(X0,X1),X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_62])])).
% 0.20/0.48  fof(f535,plain,(
% 0.20/0.48    v1_funct_2(k2_funct_1(sK1),sK0,sK0) | (~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_62 | ~spl3_65)),
% 0.20/0.48    inference(forward_demodulation,[],[f534,f520])).
% 0.20/0.48  fof(f534,plain,(
% 0.20/0.48    v1_funct_2(k2_funct_2(sK0,sK1),sK0,sK0) | (~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_62)),
% 0.20/0.48    inference(subsumption_resolution,[],[f533,f80])).
% 0.20/0.48  fof(f533,plain,(
% 0.20/0.48    v1_funct_2(k2_funct_2(sK0,sK1),sK0,sK0) | ~v1_funct_1(sK1) | (~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_62)),
% 0.20/0.48    inference(subsumption_resolution,[],[f532,f90])).
% 0.20/0.48  fof(f532,plain,(
% 0.20/0.48    ~v3_funct_2(sK1,sK0,sK0) | v1_funct_2(k2_funct_2(sK0,sK1),sK0,sK0) | ~v1_funct_1(sK1) | (~spl3_2 | ~spl3_4 | ~spl3_62)),
% 0.20/0.48    inference(subsumption_resolution,[],[f531,f95])).
% 0.20/0.48  fof(f531,plain,(
% 0.20/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v3_funct_2(sK1,sK0,sK0) | v1_funct_2(k2_funct_2(sK0,sK1),sK0,sK0) | ~v1_funct_1(sK1) | (~spl3_2 | ~spl3_62)),
% 0.20/0.48    inference(resolution,[],[f499,f85])).
% 0.20/0.48  fof(f499,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~v1_funct_2(X1,X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | v1_funct_2(k2_funct_2(X0,X1),X0,X0) | ~v1_funct_1(X1)) ) | ~spl3_62),
% 0.20/0.48    inference(avatar_component_clause,[],[f498])).
% 0.20/0.48  fof(f530,plain,(
% 0.20/0.48    ~spl3_66 | ~spl3_67 | ~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_61),
% 0.20/0.48    inference(avatar_split_clause,[],[f511,f494,f93,f88,f83,f78,f527,f523])).
% 0.20/0.48  fof(f494,plain,(
% 0.20/0.48    spl3_61 <=> ! [X1,X0] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_61])])).
% 0.20/0.48  fof(f511,plain,(
% 0.20/0.48    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) | (~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_61)),
% 0.20/0.48    inference(forward_demodulation,[],[f510,f508])).
% 0.20/0.48  fof(f508,plain,(
% 0.20/0.48    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | (~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_61)),
% 0.20/0.48    inference(subsumption_resolution,[],[f507,f80])).
% 0.20/0.48  fof(f507,plain,(
% 0.20/0.48    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~v1_funct_1(sK1) | (~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_61)),
% 0.20/0.48    inference(subsumption_resolution,[],[f506,f90])).
% 0.20/0.48  fof(f506,plain,(
% 0.20/0.48    ~v3_funct_2(sK1,sK0,sK0) | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~v1_funct_1(sK1) | (~spl3_2 | ~spl3_4 | ~spl3_61)),
% 0.20/0.48    inference(subsumption_resolution,[],[f505,f95])).
% 0.20/0.48  fof(f505,plain,(
% 0.20/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v3_funct_2(sK1,sK0,sK0) | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~v1_funct_1(sK1) | (~spl3_2 | ~spl3_61)),
% 0.20/0.48    inference(resolution,[],[f495,f85])).
% 0.20/0.48  fof(f495,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~v1_funct_2(X1,X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | k2_funct_2(X0,X1) = k2_funct_1(X1) | ~v1_funct_1(X1)) ) | ~spl3_61),
% 0.20/0.48    inference(avatar_component_clause,[],[f494])).
% 0.20/0.48  fof(f510,plain,(
% 0.20/0.48    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | (~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_61)),
% 0.20/0.48    inference(backward_demodulation,[],[f52,f508])).
% 0.20/0.48  fof(f52,plain,(
% 0.20/0.48    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))),
% 0.20/0.48    inference(cnf_transformation,[],[f45])).
% 0.20/0.48  fof(f45,plain,(
% 0.20/0.48    (~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f44])).
% 0.20/0.48  fof(f44,plain,(
% 0.20/0.48    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.20/0.48    inference(flattening,[],[f20])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 0.20/0.48    inference(ennf_transformation,[],[f17])).
% 0.20/0.48  fof(f17,negated_conjecture,(
% 0.20/0.48    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 0.20/0.48    inference(negated_conjecture,[],[f16])).
% 0.20/0.48  fof(f16,conjecture,(
% 0.20/0.48    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_funct_2)).
% 0.20/0.48  fof(f521,plain,(
% 0.20/0.48    spl3_65 | ~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_61),
% 0.20/0.48    inference(avatar_split_clause,[],[f508,f494,f93,f88,f83,f78,f518])).
% 0.20/0.48  fof(f516,plain,(
% 0.20/0.48    spl3_64 | ~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_57 | ~spl3_61),
% 0.20/0.48    inference(avatar_split_clause,[],[f509,f494,f454,f93,f88,f83,f78,f513])).
% 0.20/0.48  fof(f454,plain,(
% 0.20/0.48    spl3_57 <=> v1_funct_1(k2_funct_2(sK0,sK1))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).
% 0.20/0.48  fof(f509,plain,(
% 0.20/0.48    v1_funct_1(k2_funct_1(sK1)) | (~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_57 | ~spl3_61)),
% 0.20/0.48    inference(backward_demodulation,[],[f456,f508])).
% 0.20/0.48  fof(f456,plain,(
% 0.20/0.48    v1_funct_1(k2_funct_2(sK0,sK1)) | ~spl3_57),
% 0.20/0.48    inference(avatar_component_clause,[],[f454])).
% 0.20/0.48  fof(f500,plain,(
% 0.20/0.48    spl3_62),
% 0.20/0.48    inference(avatar_split_clause,[],[f64,f498])).
% 0.20/0.48  fof(f64,plain,(
% 0.20/0.48    ( ! [X0,X1] : (v1_funct_2(k2_funct_2(X0,X1),X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f33])).
% 0.20/0.48  fof(f496,plain,(
% 0.20/0.48    spl3_61),
% 0.20/0.48    inference(avatar_split_clause,[],[f62,f494])).
% 0.20/0.48  fof(f62,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f31])).
% 0.20/0.48  fof(f31,plain,(
% 0.20/0.48    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.20/0.48    inference(flattening,[],[f30])).
% 0.20/0.48  fof(f30,plain,(
% 0.20/0.48    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 0.20/0.48    inference(ennf_transformation,[],[f13])).
% 0.20/0.48  fof(f13,axiom,(
% 0.20/0.48    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_2(X0,X1) = k2_funct_1(X1))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).
% 0.20/0.48  fof(f457,plain,(
% 0.20/0.48    spl3_57 | ~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_55),
% 0.20/0.48    inference(avatar_split_clause,[],[f452,f434,f93,f88,f83,f78,f454])).
% 0.20/0.48  fof(f434,plain,(
% 0.20/0.48    spl3_55 <=> ! [X1,X0] : (v1_funct_1(k2_funct_2(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_55])])).
% 0.20/0.48  fof(f452,plain,(
% 0.20/0.48    v1_funct_1(k2_funct_2(sK0,sK1)) | (~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_55)),
% 0.20/0.48    inference(subsumption_resolution,[],[f451,f80])).
% 0.20/0.48  fof(f451,plain,(
% 0.20/0.48    v1_funct_1(k2_funct_2(sK0,sK1)) | ~v1_funct_1(sK1) | (~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_55)),
% 0.20/0.48    inference(subsumption_resolution,[],[f450,f90])).
% 0.20/0.48  fof(f450,plain,(
% 0.20/0.48    ~v3_funct_2(sK1,sK0,sK0) | v1_funct_1(k2_funct_2(sK0,sK1)) | ~v1_funct_1(sK1) | (~spl3_2 | ~spl3_4 | ~spl3_55)),
% 0.20/0.48    inference(subsumption_resolution,[],[f449,f95])).
% 0.20/0.48  fof(f449,plain,(
% 0.20/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v3_funct_2(sK1,sK0,sK0) | v1_funct_1(k2_funct_2(sK0,sK1)) | ~v1_funct_1(sK1) | (~spl3_2 | ~spl3_55)),
% 0.20/0.48    inference(resolution,[],[f435,f85])).
% 0.20/0.48  fof(f435,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~v1_funct_2(X1,X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | v1_funct_1(k2_funct_2(X0,X1)) | ~v1_funct_1(X1)) ) | ~spl3_55),
% 0.20/0.48    inference(avatar_component_clause,[],[f434])).
% 0.20/0.48  fof(f436,plain,(
% 0.20/0.48    spl3_55),
% 0.20/0.48    inference(avatar_split_clause,[],[f63,f434])).
% 0.20/0.48  fof(f63,plain,(
% 0.20/0.48    ( ! [X0,X1] : (v1_funct_1(k2_funct_2(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f33])).
% 0.20/0.48  fof(f385,plain,(
% 0.20/0.48    spl3_48 | ~spl3_1 | ~spl3_2 | ~spl3_4 | ~spl3_16 | ~spl3_26 | ~spl3_34),
% 0.20/0.48    inference(avatar_split_clause,[],[f365,f274,f223,f152,f93,f83,f78,f382])).
% 0.20/0.48  fof(f152,plain,(
% 0.20/0.48    spl3_16 <=> k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.20/0.48  fof(f223,plain,(
% 0.20/0.48    spl3_26 <=> k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.20/0.48  fof(f365,plain,(
% 0.20/0.48    k6_partfun1(sK0) = k5_relat_1(sK1,k2_funct_1(sK1)) | (~spl3_1 | ~spl3_2 | ~spl3_4 | ~spl3_16 | ~spl3_26 | ~spl3_34)),
% 0.20/0.48    inference(backward_demodulation,[],[f225,f360])).
% 0.20/0.48  fof(f360,plain,(
% 0.20/0.48    sK0 = k1_relat_1(sK1) | (~spl3_1 | ~spl3_2 | ~spl3_4 | ~spl3_16 | ~spl3_34)),
% 0.20/0.48    inference(backward_demodulation,[],[f154,f359])).
% 0.20/0.48  fof(f359,plain,(
% 0.20/0.48    sK0 = k1_relset_1(sK0,sK0,sK1) | (~spl3_1 | ~spl3_2 | ~spl3_4 | ~spl3_34)),
% 0.20/0.48    inference(subsumption_resolution,[],[f358,f80])).
% 0.20/0.48  fof(f358,plain,(
% 0.20/0.48    sK0 = k1_relset_1(sK0,sK0,sK1) | ~v1_funct_1(sK1) | (~spl3_2 | ~spl3_4 | ~spl3_34)),
% 0.20/0.48    inference(subsumption_resolution,[],[f357,f95])).
% 0.20/0.48  fof(f357,plain,(
% 0.20/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | sK0 = k1_relset_1(sK0,sK0,sK1) | ~v1_funct_1(sK1) | (~spl3_2 | ~spl3_34)),
% 0.20/0.48    inference(resolution,[],[f275,f85])).
% 0.20/0.48  fof(f154,plain,(
% 0.20/0.48    k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1) | ~spl3_16),
% 0.20/0.48    inference(avatar_component_clause,[],[f152])).
% 0.20/0.48  fof(f225,plain,(
% 0.20/0.48    k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) | ~spl3_26),
% 0.20/0.48    inference(avatar_component_clause,[],[f223])).
% 0.20/0.48  fof(f333,plain,(
% 0.20/0.48    spl3_41 | ~spl3_1 | ~spl3_10 | ~spl3_23 | ~spl3_24 | ~spl3_25 | ~spl3_35),
% 0.20/0.48    inference(avatar_split_clause,[],[f328,f278,f212,f204,f187,f121,f78,f330])).
% 0.20/0.48  fof(f121,plain,(
% 0.20/0.48    spl3_10 <=> v1_relat_1(sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.20/0.48  fof(f187,plain,(
% 0.20/0.48    spl3_23 <=> v2_funct_1(sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.20/0.48  fof(f204,plain,(
% 0.20/0.48    spl3_24 <=> sK1 = k2_funct_1(k2_funct_1(sK1))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.20/0.48  fof(f278,plain,(
% 0.20/0.48    spl3_35 <=> ! [X0] : (k5_relat_1(k2_funct_1(X0),k2_funct_1(k2_funct_1(X0))) = k6_partfun1(k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).
% 0.20/0.48  fof(f328,plain,(
% 0.20/0.48    k6_partfun1(k2_relat_1(sK1)) = k6_partfun1(k1_relat_1(k2_funct_1(sK1))) | (~spl3_1 | ~spl3_10 | ~spl3_23 | ~spl3_24 | ~spl3_25 | ~spl3_35)),
% 0.20/0.48    inference(forward_demodulation,[],[f327,f214])).
% 0.20/0.48  fof(f327,plain,(
% 0.20/0.48    k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(k1_relat_1(k2_funct_1(sK1))) | (~spl3_1 | ~spl3_10 | ~spl3_23 | ~spl3_24 | ~spl3_35)),
% 0.20/0.48    inference(forward_demodulation,[],[f326,f206])).
% 0.20/0.48  fof(f206,plain,(
% 0.20/0.48    sK1 = k2_funct_1(k2_funct_1(sK1)) | ~spl3_24),
% 0.20/0.48    inference(avatar_component_clause,[],[f204])).
% 0.20/0.48  fof(f326,plain,(
% 0.20/0.48    k5_relat_1(k2_funct_1(sK1),k2_funct_1(k2_funct_1(sK1))) = k6_partfun1(k1_relat_1(k2_funct_1(sK1))) | (~spl3_1 | ~spl3_10 | ~spl3_23 | ~spl3_35)),
% 0.20/0.48    inference(subsumption_resolution,[],[f325,f123])).
% 0.20/0.48  fof(f123,plain,(
% 0.20/0.48    v1_relat_1(sK1) | ~spl3_10),
% 0.20/0.48    inference(avatar_component_clause,[],[f121])).
% 0.20/0.48  fof(f325,plain,(
% 0.20/0.48    k5_relat_1(k2_funct_1(sK1),k2_funct_1(k2_funct_1(sK1))) = k6_partfun1(k1_relat_1(k2_funct_1(sK1))) | ~v1_relat_1(sK1) | (~spl3_1 | ~spl3_23 | ~spl3_35)),
% 0.20/0.48    inference(subsumption_resolution,[],[f322,f80])).
% 0.20/0.48  fof(f322,plain,(
% 0.20/0.48    k5_relat_1(k2_funct_1(sK1),k2_funct_1(k2_funct_1(sK1))) = k6_partfun1(k1_relat_1(k2_funct_1(sK1))) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | (~spl3_23 | ~spl3_35)),
% 0.20/0.48    inference(resolution,[],[f279,f189])).
% 0.20/0.48  fof(f189,plain,(
% 0.20/0.48    v2_funct_1(sK1) | ~spl3_23),
% 0.20/0.48    inference(avatar_component_clause,[],[f187])).
% 0.20/0.48  fof(f279,plain,(
% 0.20/0.48    ( ! [X0] : (~v2_funct_1(X0) | k5_relat_1(k2_funct_1(X0),k2_funct_1(k2_funct_1(X0))) = k6_partfun1(k1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl3_35),
% 0.20/0.48    inference(avatar_component_clause,[],[f278])).
% 0.20/0.48  fof(f280,plain,(
% 0.20/0.48    spl3_35 | ~spl3_6 | ~spl3_7 | ~spl3_12 | ~spl3_22),
% 0.20/0.48    inference(avatar_split_clause,[],[f219,f180,f130,f106,f102,f278])).
% 0.20/0.48  fof(f102,plain,(
% 0.20/0.48    spl3_6 <=> ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.48  fof(f106,plain,(
% 0.20/0.48    spl3_7 <=> ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.48  fof(f130,plain,(
% 0.20/0.48    spl3_12 <=> ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.20/0.48  fof(f180,plain,(
% 0.20/0.48    spl3_22 <=> ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.20/0.48  fof(f219,plain,(
% 0.20/0.48    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),k2_funct_1(k2_funct_1(X0))) = k6_partfun1(k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | (~spl3_6 | ~spl3_7 | ~spl3_12 | ~spl3_22)),
% 0.20/0.48    inference(subsumption_resolution,[],[f218,f103])).
% 0.20/0.48  fof(f103,plain,(
% 0.20/0.48    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl3_6),
% 0.20/0.48    inference(avatar_component_clause,[],[f102])).
% 0.20/0.48  fof(f218,plain,(
% 0.20/0.48    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),k2_funct_1(k2_funct_1(X0))) = k6_partfun1(k1_relat_1(k2_funct_1(X0))) | ~v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | (~spl3_7 | ~spl3_12 | ~spl3_22)),
% 0.20/0.48    inference(subsumption_resolution,[],[f216,f107])).
% 0.20/0.48  fof(f107,plain,(
% 0.20/0.48    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl3_7),
% 0.20/0.48    inference(avatar_component_clause,[],[f106])).
% 0.20/0.48  fof(f216,plain,(
% 0.20/0.48    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),k2_funct_1(k2_funct_1(X0))) = k6_partfun1(k1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(k2_funct_1(X0)) | ~v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | (~spl3_12 | ~spl3_22)),
% 0.20/0.48    inference(resolution,[],[f181,f131])).
% 0.20/0.48  fof(f131,plain,(
% 0.20/0.48    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl3_12),
% 0.20/0.48    inference(avatar_component_clause,[],[f130])).
% 0.20/0.48  fof(f181,plain,(
% 0.20/0.48    ( ! [X0] : (~v2_funct_1(X0) | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl3_22),
% 0.20/0.48    inference(avatar_component_clause,[],[f180])).
% 0.20/0.48  fof(f276,plain,(
% 0.20/0.48    spl3_34),
% 0.20/0.48    inference(avatar_split_clause,[],[f67,f274])).
% 0.20/0.48  fof(f67,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f35])).
% 0.20/0.48  fof(f35,plain,(
% 0.20/0.48    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.20/0.48    inference(flattening,[],[f34])).
% 0.20/0.48  fof(f34,plain,(
% 0.20/0.48    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 0.20/0.48    inference(ennf_transformation,[],[f15])).
% 0.20/0.48  fof(f15,axiom,(
% 0.20/0.48    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k1_relset_1(X0,X0,X1) = X0)),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).
% 0.20/0.48  fof(f268,plain,(
% 0.20/0.48    spl3_32 | ~spl3_8 | ~spl3_31),
% 0.20/0.48    inference(avatar_split_clause,[],[f262,f259,f110,f266])).
% 0.20/0.48  fof(f110,plain,(
% 0.20/0.48    spl3_8 <=> ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.48  fof(f259,plain,(
% 0.20/0.48    spl3_31 <=> ! [X5,X4] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X5))) | r2_relset_1(X5,X5,k6_partfun1(X5),k6_partfun1(X5)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 0.20/0.48  fof(f262,plain,(
% 0.20/0.48    ( ! [X0] : (r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0))) ) | (~spl3_8 | ~spl3_31)),
% 0.20/0.48    inference(resolution,[],[f260,f111])).
% 0.20/0.48  fof(f111,plain,(
% 0.20/0.48    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) ) | ~spl3_8),
% 0.20/0.48    inference(avatar_component_clause,[],[f110])).
% 0.20/0.48  fof(f260,plain,(
% 0.20/0.48    ( ! [X4,X5] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X5))) | r2_relset_1(X5,X5,k6_partfun1(X5),k6_partfun1(X5))) ) | ~spl3_31),
% 0.20/0.48    inference(avatar_component_clause,[],[f259])).
% 0.20/0.48  fof(f261,plain,(
% 0.20/0.48    spl3_31 | ~spl3_8 | ~spl3_28),
% 0.20/0.48    inference(avatar_split_clause,[],[f244,f239,f110,f259])).
% 0.20/0.48  fof(f239,plain,(
% 0.20/0.48    spl3_28 <=> ! [X1,X3,X0,X2] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.20/0.48  fof(f244,plain,(
% 0.20/0.48    ( ! [X4,X5] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X5))) | r2_relset_1(X5,X5,k6_partfun1(X5),k6_partfun1(X5))) ) | (~spl3_8 | ~spl3_28)),
% 0.20/0.48    inference(resolution,[],[f240,f111])).
% 0.20/0.48  fof(f240,plain,(
% 0.20/0.48    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X2,X2)) ) | ~spl3_28),
% 0.20/0.48    inference(avatar_component_clause,[],[f239])).
% 0.20/0.48  fof(f241,plain,(
% 0.20/0.48    spl3_28),
% 0.20/0.48    inference(avatar_split_clause,[],[f72,f239])).
% 0.20/0.48  fof(f72,plain,(
% 0.20/0.48    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f41])).
% 0.20/0.48  fof(f41,plain,(
% 0.20/0.48    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.48    inference(flattening,[],[f40])).
% 0.20/0.48  fof(f40,plain,(
% 0.20/0.48    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.20/0.48    inference(ennf_transformation,[],[f8])).
% 0.20/0.48  fof(f8,axiom,(
% 0.20/0.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).
% 0.20/0.48  fof(f226,plain,(
% 0.20/0.48    spl3_26 | ~spl3_1 | ~spl3_10 | ~spl3_22 | ~spl3_23),
% 0.20/0.48    inference(avatar_split_clause,[],[f221,f187,f180,f121,f78,f223])).
% 0.20/0.48  fof(f221,plain,(
% 0.20/0.48    k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) | (~spl3_1 | ~spl3_10 | ~spl3_22 | ~spl3_23)),
% 0.20/0.48    inference(subsumption_resolution,[],[f220,f123])).
% 0.20/0.48  fof(f220,plain,(
% 0.20/0.48    k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) | ~v1_relat_1(sK1) | (~spl3_1 | ~spl3_22 | ~spl3_23)),
% 0.20/0.48    inference(subsumption_resolution,[],[f217,f80])).
% 0.20/0.48  fof(f217,plain,(
% 0.20/0.48    k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | (~spl3_22 | ~spl3_23)),
% 0.20/0.48    inference(resolution,[],[f181,f189])).
% 0.20/0.48  fof(f215,plain,(
% 0.20/0.48    spl3_25 | ~spl3_1 | ~spl3_10 | ~spl3_21 | ~spl3_23),
% 0.20/0.48    inference(avatar_split_clause,[],[f198,f187,f176,f121,f78,f212])).
% 0.20/0.48  fof(f176,plain,(
% 0.20/0.48    spl3_21 <=> ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.20/0.48  fof(f198,plain,(
% 0.20/0.48    k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(k2_relat_1(sK1)) | (~spl3_1 | ~spl3_10 | ~spl3_21 | ~spl3_23)),
% 0.20/0.48    inference(subsumption_resolution,[],[f197,f123])).
% 0.20/0.48  fof(f197,plain,(
% 0.20/0.48    k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(k2_relat_1(sK1)) | ~v1_relat_1(sK1) | (~spl3_1 | ~spl3_21 | ~spl3_23)),
% 0.20/0.48    inference(subsumption_resolution,[],[f194,f80])).
% 0.20/0.48  fof(f194,plain,(
% 0.20/0.48    k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(k2_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | (~spl3_21 | ~spl3_23)),
% 0.20/0.48    inference(resolution,[],[f189,f177])).
% 0.20/0.48  fof(f177,plain,(
% 0.20/0.48    ( ! [X0] : (~v2_funct_1(X0) | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl3_21),
% 0.20/0.48    inference(avatar_component_clause,[],[f176])).
% 0.20/0.48  fof(f207,plain,(
% 0.20/0.48    spl3_24 | ~spl3_1 | ~spl3_10 | ~spl3_14 | ~spl3_23),
% 0.20/0.48    inference(avatar_split_clause,[],[f202,f187,f138,f121,f78,f204])).
% 0.20/0.48  fof(f138,plain,(
% 0.20/0.48    spl3_14 <=> ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.20/0.48  fof(f202,plain,(
% 0.20/0.48    sK1 = k2_funct_1(k2_funct_1(sK1)) | (~spl3_1 | ~spl3_10 | ~spl3_14 | ~spl3_23)),
% 0.20/0.48    inference(subsumption_resolution,[],[f201,f123])).
% 0.20/0.48  fof(f201,plain,(
% 0.20/0.48    sK1 = k2_funct_1(k2_funct_1(sK1)) | ~v1_relat_1(sK1) | (~spl3_1 | ~spl3_14 | ~spl3_23)),
% 0.20/0.48    inference(subsumption_resolution,[],[f196,f80])).
% 0.20/0.48  fof(f196,plain,(
% 0.20/0.48    sK1 = k2_funct_1(k2_funct_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | (~spl3_14 | ~spl3_23)),
% 0.20/0.48    inference(resolution,[],[f189,f139])).
% 0.20/0.48  fof(f139,plain,(
% 0.20/0.48    ( ! [X0] : (~v2_funct_1(X0) | k2_funct_1(k2_funct_1(X0)) = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl3_14),
% 0.20/0.48    inference(avatar_component_clause,[],[f138])).
% 0.20/0.48  fof(f190,plain,(
% 0.20/0.48    spl3_23 | ~spl3_1 | ~spl3_3 | ~spl3_4 | ~spl3_20),
% 0.20/0.48    inference(avatar_split_clause,[],[f185,f172,f93,f88,f78,f187])).
% 0.20/0.48  fof(f172,plain,(
% 0.20/0.48    spl3_20 <=> ! [X1,X0,X2] : (v2_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.20/0.48  fof(f185,plain,(
% 0.20/0.48    v2_funct_1(sK1) | (~spl3_1 | ~spl3_3 | ~spl3_4 | ~spl3_20)),
% 0.20/0.48    inference(subsumption_resolution,[],[f184,f95])).
% 0.20/0.48  fof(f184,plain,(
% 0.20/0.48    v2_funct_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | (~spl3_1 | ~spl3_3 | ~spl3_20)),
% 0.20/0.48    inference(subsumption_resolution,[],[f183,f80])).
% 0.20/0.48  fof(f183,plain,(
% 0.20/0.48    v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | (~spl3_3 | ~spl3_20)),
% 0.20/0.48    inference(resolution,[],[f173,f90])).
% 0.20/0.48  fof(f173,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~v3_funct_2(X2,X0,X1) | v2_funct_1(X2) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl3_20),
% 0.20/0.48    inference(avatar_component_clause,[],[f172])).
% 0.20/0.48  fof(f182,plain,(
% 0.20/0.49    spl3_22),
% 0.20/0.49    inference(avatar_split_clause,[],[f76,f180])).
% 0.20/0.49  fof(f76,plain,(
% 0.20/0.49    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.49    inference(definition_unfolding,[],[f59,f53])).
% 0.20/0.49  fof(f53,plain,(
% 0.20/0.49    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f14])).
% 0.20/0.49  fof(f14,axiom,(
% 0.20/0.49    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.20/0.49  fof(f59,plain,(
% 0.20/0.49    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f29])).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.49    inference(flattening,[],[f28])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).
% 0.20/0.49  fof(f178,plain,(
% 0.20/0.49    spl3_21),
% 0.20/0.49    inference(avatar_split_clause,[],[f75,f176])).
% 0.20/0.49  fof(f75,plain,(
% 0.20/0.49    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.49    inference(definition_unfolding,[],[f60,f53])).
% 0.20/0.49  fof(f60,plain,(
% 0.20/0.49    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f29])).
% 0.20/0.49  fof(f174,plain,(
% 0.20/0.49    spl3_20),
% 0.20/0.49    inference(avatar_split_clause,[],[f71,f172])).
% 0.20/0.49  fof(f71,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (v2_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f39])).
% 0.20/0.49  fof(f39,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.49    inference(flattening,[],[f38])).
% 0.20/0.49  fof(f38,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (((v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.49    inference(ennf_transformation,[],[f18])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_1(X2) & v1_funct_1(X2))))),
% 0.20/0.49    inference(pure_predicate_removal,[],[f10])).
% 0.20/0.49  fof(f10,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).
% 0.20/0.49  fof(f155,plain,(
% 0.20/0.49    spl3_16 | ~spl3_4 | ~spl3_15),
% 0.20/0.49    inference(avatar_split_clause,[],[f148,f145,f93,f152])).
% 0.20/0.49  fof(f148,plain,(
% 0.20/0.49    k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1) | (~spl3_4 | ~spl3_15)),
% 0.20/0.49    inference(resolution,[],[f146,f95])).
% 0.20/0.49  fof(f147,plain,(
% 0.20/0.49    spl3_15),
% 0.20/0.49    inference(avatar_split_clause,[],[f69,f145])).
% 0.20/0.49  fof(f69,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f37])).
% 0.20/0.49  fof(f37,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.49    inference(ennf_transformation,[],[f7])).
% 0.20/0.49  fof(f7,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.49  fof(f140,plain,(
% 0.20/0.49    spl3_14),
% 0.20/0.49    inference(avatar_split_clause,[],[f58,f138])).
% 0.20/0.49  fof(f58,plain,(
% 0.20/0.49    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f27])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.49    inference(flattening,[],[f26])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f5])).
% 0.20/0.49  fof(f5,axiom,(
% 0.20/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).
% 0.20/0.49  fof(f132,plain,(
% 0.20/0.49    spl3_12),
% 0.20/0.49    inference(avatar_split_clause,[],[f57,f130])).
% 0.20/0.49  fof(f57,plain,(
% 0.20/0.49    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f25])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.49    inference(flattening,[],[f24])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => v2_funct_1(k2_funct_1(X0))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_1)).
% 0.20/0.49  fof(f124,plain,(
% 0.20/0.49    spl3_10 | ~spl3_4 | ~spl3_9),
% 0.20/0.49    inference(avatar_split_clause,[],[f117,f114,f93,f121])).
% 0.20/0.49  fof(f114,plain,(
% 0.20/0.49    spl3_9 <=> ! [X1,X0,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.49  fof(f117,plain,(
% 0.20/0.49    v1_relat_1(sK1) | (~spl3_4 | ~spl3_9)),
% 0.20/0.49    inference(resolution,[],[f115,f95])).
% 0.20/0.49  fof(f115,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) ) | ~spl3_9),
% 0.20/0.49    inference(avatar_component_clause,[],[f114])).
% 0.20/0.49  fof(f116,plain,(
% 0.20/0.49    spl3_9),
% 0.20/0.49    inference(avatar_split_clause,[],[f68,f114])).
% 0.20/0.49  fof(f68,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f36])).
% 0.20/0.49  fof(f36,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.49    inference(ennf_transformation,[],[f6])).
% 0.20/0.49  fof(f6,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.49  fof(f112,plain,(
% 0.20/0.49    spl3_8),
% 0.20/0.49    inference(avatar_split_clause,[],[f74,f110])).
% 0.20/0.49  fof(f74,plain,(
% 0.20/0.49    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.20/0.49    inference(definition_unfolding,[],[f54,f53])).
% 0.20/0.49  fof(f54,plain,(
% 0.20/0.49    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f9])).
% 0.20/0.49  fof(f9,axiom,(
% 0.20/0.49    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).
% 0.20/0.49  fof(f108,plain,(
% 0.20/0.49    spl3_7),
% 0.20/0.49    inference(avatar_split_clause,[],[f56,f106])).
% 0.20/0.49  fof(f56,plain,(
% 0.20/0.49    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f23])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.49    inference(flattening,[],[f22])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.20/0.49  fof(f104,plain,(
% 0.20/0.49    spl3_6),
% 0.20/0.49    inference(avatar_split_clause,[],[f55,f102])).
% 0.20/0.49  fof(f55,plain,(
% 0.20/0.49    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f23])).
% 0.20/0.49  fof(f96,plain,(
% 0.20/0.49    spl3_4),
% 0.20/0.49    inference(avatar_split_clause,[],[f51,f93])).
% 0.20/0.49  fof(f51,plain,(
% 0.20/0.49    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.20/0.49    inference(cnf_transformation,[],[f45])).
% 0.20/0.49  fof(f91,plain,(
% 0.20/0.49    spl3_3),
% 0.20/0.49    inference(avatar_split_clause,[],[f50,f88])).
% 0.20/0.49  fof(f50,plain,(
% 0.20/0.49    v3_funct_2(sK1,sK0,sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f45])).
% 0.20/0.49  fof(f86,plain,(
% 0.20/0.49    spl3_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f49,f83])).
% 0.20/0.49  fof(f49,plain,(
% 0.20/0.49    v1_funct_2(sK1,sK0,sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f45])).
% 0.20/0.49  fof(f81,plain,(
% 0.20/0.49    spl3_1),
% 0.20/0.49    inference(avatar_split_clause,[],[f48,f78])).
% 0.20/0.49  fof(f48,plain,(
% 0.20/0.49    v1_funct_1(sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f45])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (15854)------------------------------
% 0.20/0.49  % (15854)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (15854)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (15854)Memory used [KB]: 6652
% 0.20/0.49  % (15854)Time elapsed: 0.071 s
% 0.20/0.49  % (15854)------------------------------
% 0.20/0.49  % (15854)------------------------------
% 0.20/0.49  % (15846)Success in time 0.13 s
%------------------------------------------------------------------------------
