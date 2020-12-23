%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:17 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  330 ( 693 expanded)
%              Number of leaves         :   75 ( 319 expanded)
%              Depth                    :   11
%              Number of atoms          : 1329 (2523 expanded)
%              Number of equality atoms :  141 ( 311 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f567,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f88,f92,f96,f100,f104,f108,f112,f116,f124,f128,f132,f136,f140,f144,f148,f162,f166,f170,f178,f182,f189,f193,f205,f213,f217,f221,f232,f236,f239,f264,f279,f291,f295,f299,f303,f308,f318,f322,f326,f334,f338,f362,f366,f375,f379,f383,f392,f402,f410,f425,f429,f472,f514,f519,f526,f541,f549,f559,f566])).

fof(f566,plain,
    ( ~ spl3_1
    | ~ spl3_47
    | ~ spl3_75
    | ~ spl3_77
    | spl3_78 ),
    inference(avatar_contradiction_clause,[],[f565])).

fof(f565,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_47
    | ~ spl3_75
    | ~ spl3_77
    | spl3_78 ),
    inference(subsumption_resolution,[],[f564,f87])).

fof(f87,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl3_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f564,plain,
    ( ~ v1_funct_1(sK2)
    | ~ spl3_47
    | ~ spl3_75
    | ~ spl3_77
    | spl3_78 ),
    inference(subsumption_resolution,[],[f563,f548])).

fof(f548,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl3_77 ),
    inference(avatar_component_clause,[],[f547])).

fof(f547,plain,
    ( spl3_77
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_77])])).

fof(f563,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v1_funct_1(sK2)
    | ~ spl3_47
    | ~ spl3_75
    | spl3_78 ),
    inference(subsumption_resolution,[],[f561,f540])).

fof(f540,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl3_75 ),
    inference(avatar_component_clause,[],[f539])).

fof(f539,plain,
    ( spl3_75
  <=> v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_75])])).

fof(f561,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v1_funct_1(sK2)
    | ~ spl3_47
    | spl3_78 ),
    inference(resolution,[],[f558,f325])).

fof(f325,plain,
    ( ! [X2,X0,X1] :
        ( r2_funct_2(X1,X2,X0,X0)
        | ~ v1_funct_2(X0,X1,X2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ v1_funct_1(X0) )
    | ~ spl3_47 ),
    inference(avatar_component_clause,[],[f324])).

fof(f324,plain,
    ( spl3_47
  <=> ! [X1,X0,X2] :
        ( ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,X1,X2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | r2_funct_2(X1,X2,X0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).

fof(f558,plain,
    ( ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2)
    | spl3_78 ),
    inference(avatar_component_clause,[],[f557])).

fof(f557,plain,
    ( spl3_78
  <=> r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_78])])).

fof(f559,plain,
    ( ~ spl3_78
    | spl3_59
    | ~ spl3_71
    | ~ spl3_72 ),
    inference(avatar_split_clause,[],[f537,f512,f509,f400,f557])).

fof(f400,plain,
    ( spl3_59
  <=> r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_59])])).

fof(f509,plain,
    ( spl3_71
  <=> sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_71])])).

fof(f512,plain,
    ( spl3_72
  <=> k2_struct_0(sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_72])])).

fof(f537,plain,
    ( ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2)
    | spl3_59
    | ~ spl3_71
    | ~ spl3_72 ),
    inference(backward_demodulation,[],[f533,f510])).

fof(f510,plain,
    ( sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_71 ),
    inference(avatar_component_clause,[],[f509])).

fof(f533,plain,
    ( ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),sK2)
    | spl3_59
    | ~ spl3_72 ),
    inference(backward_demodulation,[],[f401,f515])).

fof(f515,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl3_72 ),
    inference(avatar_component_clause,[],[f512])).

fof(f401,plain,
    ( ~ r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),sK2)
    | spl3_59 ),
    inference(avatar_component_clause,[],[f400])).

fof(f549,plain,
    ( spl3_77
    | ~ spl3_41
    | ~ spl3_72 ),
    inference(avatar_split_clause,[],[f529,f512,f297,f547])).

fof(f297,plain,
    ( spl3_41
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).

fof(f529,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl3_41
    | ~ spl3_72 ),
    inference(backward_demodulation,[],[f298,f515])).

fof(f298,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
    | ~ spl3_41 ),
    inference(avatar_component_clause,[],[f297])).

fof(f541,plain,
    ( spl3_75
    | ~ spl3_40
    | ~ spl3_72 ),
    inference(avatar_split_clause,[],[f528,f512,f293,f539])).

fof(f293,plain,
    ( spl3_40
  <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).

fof(f528,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl3_40
    | ~ spl3_72 ),
    inference(backward_demodulation,[],[f294,f515])).

fof(f294,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ spl3_40 ),
    inference(avatar_component_clause,[],[f293])).

fof(f526,plain,
    ( ~ spl3_24
    | ~ spl3_41
    | spl3_73 ),
    inference(avatar_contradiction_clause,[],[f524])).

fof(f524,plain,
    ( $false
    | ~ spl3_24
    | ~ spl3_41
    | spl3_73 ),
    inference(unit_resulting_resolution,[],[f298,f518,f192])).

fof(f192,plain,
    ( ! [X2,X0,X1] :
        ( v4_relat_1(X2,X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f191])).

fof(f191,plain,
    ( spl3_24
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v4_relat_1(X2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f518,plain,
    ( ~ v4_relat_1(sK2,k2_struct_0(sK0))
    | spl3_73 ),
    inference(avatar_component_clause,[],[f517])).

fof(f517,plain,
    ( spl3_73
  <=> v4_relat_1(sK2,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_73])])).

fof(f519,plain,
    ( spl3_72
    | ~ spl3_73
    | ~ spl3_31
    | ~ spl3_33
    | ~ spl3_64 ),
    inference(avatar_split_clause,[],[f460,f427,f230,f219,f517,f512])).

fof(f219,plain,
    ( spl3_31
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X1)
        | ~ v4_relat_1(X1,X0)
        | k1_relat_1(X1) = X0
        | ~ v1_partfun1(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f230,plain,
    ( spl3_33
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f427,plain,
    ( spl3_64
  <=> v1_partfun1(sK2,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_64])])).

fof(f460,plain,
    ( ~ v4_relat_1(sK2,k2_struct_0(sK0))
    | k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl3_31
    | ~ spl3_33
    | ~ spl3_64 ),
    inference(subsumption_resolution,[],[f459,f255])).

fof(f255,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_33 ),
    inference(avatar_component_clause,[],[f230])).

fof(f459,plain,
    ( ~ v4_relat_1(sK2,k2_struct_0(sK0))
    | k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_31
    | ~ spl3_64 ),
    inference(resolution,[],[f428,f220])).

fof(f220,plain,
    ( ! [X0,X1] :
        ( ~ v1_partfun1(X1,X0)
        | ~ v4_relat_1(X1,X0)
        | k1_relat_1(X1) = X0
        | ~ v1_relat_1(X1) )
    | ~ spl3_31 ),
    inference(avatar_component_clause,[],[f219])).

fof(f428,plain,
    ( v1_partfun1(sK2,k2_struct_0(sK0))
    | ~ spl3_64 ),
    inference(avatar_component_clause,[],[f427])).

fof(f514,plain,
    ( ~ spl3_36
    | spl3_71
    | ~ spl3_72
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_32
    | ~ spl3_33
    | ~ spl3_49
    | ~ spl3_55
    | ~ spl3_57
    | ~ spl3_58
    | ~ spl3_60
    | ~ spl3_63 ),
    inference(avatar_split_clause,[],[f457,f423,f408,f390,f381,f373,f332,f230,f227,f90,f86,f512,f509,f253])).

fof(f253,plain,
    ( spl3_36
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f90,plain,
    ( spl3_2
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f227,plain,
    ( spl3_32
  <=> sK2 = k2_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f332,plain,
    ( spl3_49
  <=> k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).

fof(f373,plain,
    ( spl3_55
  <=> v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_55])])).

fof(f381,plain,
    ( spl3_57
  <=> ! [X1,X0,X2] :
        ( ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,X0,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k2_relset_1(X0,X1,X2) != X1
        | ~ v2_funct_1(X2)
        | k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).

fof(f390,plain,
    ( spl3_58
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_58])])).

fof(f408,plain,
    ( spl3_60
  <=> k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_60])])).

fof(f423,plain,
    ( spl3_63
  <=> ! [X1] :
        ( ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1)
        | v2_funct_1(k2_funct_1(X1))
        | ~ v2_funct_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_63])])).

fof(f457,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_32
    | ~ spl3_33
    | ~ spl3_49
    | ~ spl3_55
    | ~ spl3_57
    | ~ spl3_58
    | ~ spl3_60
    | ~ spl3_63 ),
    inference(inner_rewriting,[],[f454])).

fof(f454,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | sK2 = k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_32
    | ~ spl3_33
    | ~ spl3_49
    | ~ spl3_55
    | ~ spl3_57
    | ~ spl3_58
    | ~ spl3_60
    | ~ spl3_63 ),
    inference(backward_demodulation,[],[f451,f333])).

fof(f333,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | ~ spl3_49 ),
    inference(avatar_component_clause,[],[f332])).

fof(f451,plain,
    ( sK2 = k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))
    | k2_struct_0(sK0) != k2_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_32
    | ~ spl3_33
    | ~ spl3_55
    | ~ spl3_57
    | ~ spl3_58
    | ~ spl3_60
    | ~ spl3_63 ),
    inference(forward_demodulation,[],[f450,f228])).

fof(f228,plain,
    ( sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ spl3_32 ),
    inference(avatar_component_clause,[],[f227])).

fof(f450,plain,
    ( k2_struct_0(sK0) != k2_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_33
    | ~ spl3_55
    | ~ spl3_57
    | ~ spl3_58
    | ~ spl3_60
    | ~ spl3_63 ),
    inference(forward_demodulation,[],[f449,f409])).

fof(f409,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ spl3_60 ),
    inference(avatar_component_clause,[],[f408])).

fof(f449,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))
    | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_33
    | ~ spl3_55
    | ~ spl3_57
    | ~ spl3_58
    | ~ spl3_63 ),
    inference(subsumption_resolution,[],[f448,f439])).

fof(f439,plain,
    ( v2_funct_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_33
    | ~ spl3_63 ),
    inference(subsumption_resolution,[],[f434,f87])).

fof(f434,plain,
    ( v2_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl3_2
    | ~ spl3_33
    | ~ spl3_63 ),
    inference(subsumption_resolution,[],[f431,f255])).

fof(f431,plain,
    ( ~ v1_relat_1(sK2)
    | v2_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl3_2
    | ~ spl3_63 ),
    inference(resolution,[],[f424,f91])).

fof(f91,plain,
    ( v2_funct_1(sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f90])).

fof(f424,plain,
    ( ! [X1] :
        ( ~ v2_funct_1(X1)
        | ~ v1_relat_1(X1)
        | v2_funct_1(k2_funct_1(X1))
        | ~ v1_funct_1(X1) )
    | ~ spl3_63 ),
    inference(avatar_component_clause,[],[f423])).

fof(f448,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ spl3_55
    | ~ spl3_57
    | ~ spl3_58 ),
    inference(subsumption_resolution,[],[f403,f374])).

fof(f374,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0))
    | ~ spl3_55 ),
    inference(avatar_component_clause,[],[f373])).

fof(f403,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ spl3_57
    | ~ spl3_58 ),
    inference(resolution,[],[f391,f382])).

fof(f382,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2)
        | k2_relset_1(X0,X1,X2) != X1
        | ~ v2_funct_1(X2)
        | k2_funct_1(X2) = k2_tops_2(X0,X1,X2) )
    | ~ spl3_57 ),
    inference(avatar_component_clause,[],[f381])).

fof(f391,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0))))
    | ~ spl3_58 ),
    inference(avatar_component_clause,[],[f390])).

fof(f472,plain,
    ( spl3_48
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_33
    | ~ spl3_63 ),
    inference(avatar_split_clause,[],[f439,f423,f230,f90,f86,f329])).

fof(f329,plain,
    ( spl3_48
  <=> v2_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).

fof(f429,plain,
    ( spl3_64
    | ~ spl3_1
    | ~ spl3_40
    | ~ spl3_41
    | ~ spl3_54 ),
    inference(avatar_split_clause,[],[f421,f364,f297,f293,f86,f427])).

fof(f364,plain,
    ( spl3_54
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(sK2))))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,X1,k2_relat_1(sK2))
        | v1_partfun1(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_54])])).

fof(f421,plain,
    ( v1_partfun1(sK2,k2_struct_0(sK0))
    | ~ spl3_1
    | ~ spl3_40
    | ~ spl3_41
    | ~ spl3_54 ),
    inference(subsumption_resolution,[],[f420,f294])).

fof(f420,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | v1_partfun1(sK2,k2_struct_0(sK0))
    | ~ spl3_1
    | ~ spl3_41
    | ~ spl3_54 ),
    inference(subsumption_resolution,[],[f419,f87])).

fof(f419,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | v1_partfun1(sK2,k2_struct_0(sK0))
    | ~ spl3_41
    | ~ spl3_54 ),
    inference(resolution,[],[f365,f298])).

fof(f365,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(sK2))))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,X1,k2_relat_1(sK2))
        | v1_partfun1(X0,X1) )
    | ~ spl3_54 ),
    inference(avatar_component_clause,[],[f364])).

fof(f425,plain,
    ( spl3_63
    | ~ spl3_10
    | ~ spl3_14
    | ~ spl3_15
    | ~ spl3_30
    | ~ spl3_38
    | ~ spl3_50 ),
    inference(avatar_split_clause,[],[f350,f336,f262,f215,f142,f138,f122,f423])).

fof(f122,plain,
    ( spl3_10
  <=> ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f138,plain,
    ( spl3_14
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | v1_relat_1(k2_funct_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f142,plain,
    ( spl3_15
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | v1_funct_1(k2_funct_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f215,plain,
    ( spl3_30
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v2_funct_1(X0)
        | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f262,plain,
    ( spl3_38
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v2_funct_1(X0)
        | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).

fof(f336,plain,
    ( spl3_50
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(X1)
        | ~ v2_funct_1(k5_relat_1(X1,X0))
        | k2_relat_1(X1) != k1_relat_1(X0)
        | v2_funct_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_50])])).

fof(f350,plain,
    ( ! [X1] :
        ( ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1)
        | v2_funct_1(k2_funct_1(X1))
        | ~ v2_funct_1(X1) )
    | ~ spl3_10
    | ~ spl3_14
    | ~ spl3_15
    | ~ spl3_30
    | ~ spl3_38
    | ~ spl3_50 ),
    inference(subsumption_resolution,[],[f349,f216])).

fof(f216,plain,
    ( ! [X0] :
        ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        | ~ v1_funct_1(X0)
        | ~ v2_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f215])).

fof(f349,plain,
    ( ! [X1] :
        ( ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1)
        | k1_relat_1(X1) != k2_relat_1(k2_funct_1(X1))
        | v2_funct_1(k2_funct_1(X1))
        | ~ v2_funct_1(X1) )
    | ~ spl3_10
    | ~ spl3_14
    | ~ spl3_15
    | ~ spl3_38
    | ~ spl3_50 ),
    inference(subsumption_resolution,[],[f348,f143])).

% (3785)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
fof(f143,plain,
    ( ! [X0] :
        ( v1_funct_1(k2_funct_1(X0))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f142])).

fof(f348,plain,
    ( ! [X1] :
        ( ~ v1_funct_1(X1)
        | ~ v1_funct_1(k2_funct_1(X1))
        | ~ v1_relat_1(X1)
        | k1_relat_1(X1) != k2_relat_1(k2_funct_1(X1))
        | v2_funct_1(k2_funct_1(X1))
        | ~ v2_funct_1(X1) )
    | ~ spl3_10
    | ~ spl3_14
    | ~ spl3_38
    | ~ spl3_50 ),
    inference(subsumption_resolution,[],[f347,f139])).

fof(f139,plain,
    ( ! [X0] :
        ( v1_relat_1(k2_funct_1(X0))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f138])).

fof(f347,plain,
    ( ! [X1] :
        ( ~ v1_funct_1(X1)
        | ~ v1_relat_1(k2_funct_1(X1))
        | ~ v1_funct_1(k2_funct_1(X1))
        | ~ v1_relat_1(X1)
        | k1_relat_1(X1) != k2_relat_1(k2_funct_1(X1))
        | v2_funct_1(k2_funct_1(X1))
        | ~ v2_funct_1(X1) )
    | ~ spl3_10
    | ~ spl3_38
    | ~ spl3_50 ),
    inference(subsumption_resolution,[],[f345,f123])).

fof(f123,plain,
    ( ! [X0] : v2_funct_1(k6_relat_1(X0))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f122])).

fof(f345,plain,
    ( ! [X1] :
        ( ~ v2_funct_1(k6_relat_1(k2_relat_1(X1)))
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(k2_funct_1(X1))
        | ~ v1_funct_1(k2_funct_1(X1))
        | ~ v1_relat_1(X1)
        | k1_relat_1(X1) != k2_relat_1(k2_funct_1(X1))
        | v2_funct_1(k2_funct_1(X1))
        | ~ v2_funct_1(X1) )
    | ~ spl3_38
    | ~ spl3_50 ),
    inference(duplicate_literal_removal,[],[f344])).

fof(f344,plain,
    ( ! [X1] :
        ( ~ v2_funct_1(k6_relat_1(k2_relat_1(X1)))
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(k2_funct_1(X1))
        | ~ v1_funct_1(k2_funct_1(X1))
        | ~ v1_relat_1(X1)
        | k1_relat_1(X1) != k2_relat_1(k2_funct_1(X1))
        | v2_funct_1(k2_funct_1(X1))
        | ~ v1_funct_1(X1)
        | ~ v2_funct_1(X1)
        | ~ v1_relat_1(X1) )
    | ~ spl3_38
    | ~ spl3_50 ),
    inference(superposition,[],[f337,f263])).

fof(f263,plain,
    ( ! [X0] :
        ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        | ~ v1_funct_1(X0)
        | ~ v2_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl3_38 ),
    inference(avatar_component_clause,[],[f262])).

fof(f337,plain,
    ( ! [X0,X1] :
        ( ~ v2_funct_1(k5_relat_1(X1,X0))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X0)
        | k2_relat_1(X1) != k1_relat_1(X0)
        | v2_funct_1(X1) )
    | ~ spl3_50 ),
    inference(avatar_component_clause,[],[f336])).

fof(f410,plain,
    ( spl3_60
    | ~ spl3_34
    | ~ spl3_58 ),
    inference(avatar_split_clause,[],[f406,f390,f234,f408])).

fof(f234,plain,
    ( spl3_34
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f406,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ spl3_34
    | ~ spl3_58 ),
    inference(resolution,[],[f391,f235])).

fof(f235,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) )
    | ~ spl3_34 ),
    inference(avatar_component_clause,[],[f234])).

fof(f402,plain,
    ( ~ spl3_59
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_40
    | ~ spl3_41
    | spl3_43
    | ~ spl3_46
    | ~ spl3_57 ),
    inference(avatar_split_clause,[],[f398,f381,f320,f306,f297,f293,f90,f86,f400])).

fof(f306,plain,
    ( spl3_43
  <=> r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).

fof(f320,plain,
    ( spl3_46
  <=> k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).

fof(f398,plain,
    ( ~ r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),sK2)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_40
    | ~ spl3_41
    | spl3_43
    | ~ spl3_46
    | ~ spl3_57 ),
    inference(backward_demodulation,[],[f307,f397])).

fof(f397,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_40
    | ~ spl3_41
    | ~ spl3_46
    | ~ spl3_57 ),
    inference(subsumption_resolution,[],[f396,f91])).

fof(f396,plain,
    ( ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ spl3_1
    | ~ spl3_40
    | ~ spl3_41
    | ~ spl3_46
    | ~ spl3_57 ),
    inference(subsumption_resolution,[],[f395,f321])).

fof(f321,plain,
    ( k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ spl3_46 ),
    inference(avatar_component_clause,[],[f320])).

fof(f395,plain,
    ( k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ spl3_1
    | ~ spl3_40
    | ~ spl3_41
    | ~ spl3_57 ),
    inference(subsumption_resolution,[],[f394,f87])).

fof(f394,plain,
    ( ~ v1_funct_1(sK2)
    | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ spl3_40
    | ~ spl3_41
    | ~ spl3_57 ),
    inference(subsumption_resolution,[],[f393,f294])).

fof(f393,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ spl3_41
    | ~ spl3_57 ),
    inference(resolution,[],[f382,f298])).

fof(f307,plain,
    ( ~ r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),sK2)
    | spl3_43 ),
    inference(avatar_component_clause,[],[f306])).

fof(f392,plain,
    ( spl3_58
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_40
    | ~ spl3_41
    | ~ spl3_46
    | ~ spl3_56 ),
    inference(avatar_split_clause,[],[f388,f377,f320,f297,f293,f90,f86,f390])).

fof(f377,plain,
    ( spl3_56
  <=> ! [X1,X0,X2] :
        ( ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,X0,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v2_funct_1(X2)
        | k2_relset_1(X0,X1,X2) != X1
        | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).

fof(f388,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0))))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_40
    | ~ spl3_41
    | ~ spl3_46
    | ~ spl3_56 ),
    inference(subsumption_resolution,[],[f387,f321])).

fof(f387,plain,
    ( k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0))))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_40
    | ~ spl3_41
    | ~ spl3_56 ),
    inference(subsumption_resolution,[],[f386,f91])).

fof(f386,plain,
    ( ~ v2_funct_1(sK2)
    | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0))))
    | ~ spl3_1
    | ~ spl3_40
    | ~ spl3_41
    | ~ spl3_56 ),
    inference(subsumption_resolution,[],[f385,f87])).

fof(f385,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0))))
    | ~ spl3_40
    | ~ spl3_41
    | ~ spl3_56 ),
    inference(subsumption_resolution,[],[f384,f294])).

fof(f384,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0))))
    | ~ spl3_41
    | ~ spl3_56 ),
    inference(resolution,[],[f378,f298])).

fof(f378,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2)
        | ~ v2_funct_1(X2)
        | k2_relset_1(X0,X1,X2) != X1
        | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
    | ~ spl3_56 ),
    inference(avatar_component_clause,[],[f377])).

fof(f383,plain,(
    spl3_57 ),
    inference(avatar_split_clause,[],[f79,f381])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

fof(f379,plain,(
    spl3_56 ),
    inference(avatar_split_clause,[],[f78,f377])).

% (3793)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

fof(f375,plain,
    ( spl3_55
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_40
    | ~ spl3_41
    | ~ spl3_46
    | ~ spl3_53 ),
    inference(avatar_split_clause,[],[f371,f360,f320,f297,f293,f90,f86,f373])).

fof(f360,plain,
    ( spl3_53
  <=> ! [X1,X0,X2] :
        ( ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,X0,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v2_funct_1(X2)
        | k2_relset_1(X0,X1,X2) != X1
        | v1_funct_2(k2_funct_1(X2),X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_53])])).

fof(f371,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_40
    | ~ spl3_41
    | ~ spl3_46
    | ~ spl3_53 ),
    inference(subsumption_resolution,[],[f370,f321])).

fof(f370,plain,
    ( k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_40
    | ~ spl3_41
    | ~ spl3_53 ),
    inference(subsumption_resolution,[],[f369,f91])).

fof(f369,plain,
    ( ~ v2_funct_1(sK2)
    | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0))
    | ~ spl3_1
    | ~ spl3_40
    | ~ spl3_41
    | ~ spl3_53 ),
    inference(subsumption_resolution,[],[f368,f87])).

fof(f368,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0))
    | ~ spl3_40
    | ~ spl3_41
    | ~ spl3_53 ),
    inference(subsumption_resolution,[],[f367,f294])).

fof(f367,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0))
    | ~ spl3_41
    | ~ spl3_53 ),
    inference(resolution,[],[f361,f298])).

fof(f361,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2)
        | ~ v2_funct_1(X2)
        | k2_relset_1(X0,X1,X2) != X1
        | v1_funct_2(k2_funct_1(X2),X1,X0) )
    | ~ spl3_53 ),
    inference(avatar_component_clause,[],[f360])).

fof(f366,plain,
    ( spl3_54
    | spl3_42
    | ~ spl3_45 ),
    inference(avatar_split_clause,[],[f327,f316,f301,f364])).

fof(f301,plain,
    ( spl3_42
  <=> v1_xboole_0(k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).

fof(f316,plain,
    ( spl3_45
  <=> ! [X1,X0,X2] :
        ( v1_xboole_0(X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,X0,X1)
        | v1_partfun1(X2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).

fof(f327,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(sK2))))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,X1,k2_relat_1(sK2))
        | v1_partfun1(X0,X1) )
    | spl3_42
    | ~ spl3_45 ),
    inference(resolution,[],[f317,f302])).

fof(f302,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK2))
    | spl3_42 ),
    inference(avatar_component_clause,[],[f301])).

fof(f317,plain,
    ( ! [X2,X0,X1] :
        ( v1_xboole_0(X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,X0,X1)
        | v1_partfun1(X2,X0) )
    | ~ spl3_45 ),
    inference(avatar_component_clause,[],[f316])).

fof(f362,plain,(
    spl3_53 ),
    inference(avatar_split_clause,[],[f77,f360])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | v1_funct_2(k2_funct_1(X2),X1,X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f338,plain,(
    spl3_50 ),
    inference(avatar_split_clause,[],[f67,f336])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | k2_relat_1(X1) != k1_relat_1(X0)
      | v2_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k2_relat_1(X1) = k1_relat_1(X0)
              & v2_funct_1(k5_relat_1(X1,X0)) )
           => ( v2_funct_1(X0)
              & v2_funct_1(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_1)).

fof(f334,plain,
    ( ~ spl3_35
    | ~ spl3_48
    | ~ spl3_36
    | spl3_49
    | ~ spl3_29
    | ~ spl3_32 ),
    inference(avatar_split_clause,[],[f242,f227,f211,f332,f253,f329,f250])).

fof(f250,plain,
    ( spl3_35
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).

fof(f211,plain,
    ( spl3_29
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v2_funct_1(X0)
        | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f242,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_29
    | ~ spl3_32 ),
    inference(superposition,[],[f212,f228])).

fof(f212,plain,
    ( ! [X0] :
        ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
        | ~ v1_funct_1(X0)
        | ~ v2_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f211])).

fof(f326,plain,(
    spl3_47 ),
    inference(avatar_split_clause,[],[f83,f324])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,X1,X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | r2_funct_2(X1,X2,X0,X0) ) ),
    inference(duplicate_literal_removal,[],[f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,X1,X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X0,X1,X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | r2_funct_2(X1,X2,X0,X0) ) ),
    inference(condensation,[],[f80])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_funct_2(X0,X1,X2,X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => r2_funct_2(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).

fof(f322,plain,
    ( spl3_46
    | ~ spl3_19
    | ~ spl3_21
    | ~ spl3_34 ),
    inference(avatar_split_clause,[],[f267,f234,f176,f168,f320])).

fof(f168,plain,
    ( spl3_19
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f176,plain,
    ( spl3_21
  <=> k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f267,plain,
    ( k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ spl3_19
    | ~ spl3_21
    | ~ spl3_34 ),
    inference(backward_demodulation,[],[f265,f266])).

fof(f266,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2)
    | ~ spl3_19
    | ~ spl3_21
    | ~ spl3_34 ),
    inference(backward_demodulation,[],[f177,f265])).

fof(f177,plain,
    ( k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f176])).

fof(f265,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2)
    | ~ spl3_19
    | ~ spl3_34 ),
    inference(resolution,[],[f235,f169])).

fof(f169,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f168])).

fof(f318,plain,(
    spl3_45 ),
    inference(avatar_split_clause,[],[f69,f316])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
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

fof(f308,plain,
    ( ~ spl3_43
    | ~ spl3_19
    | ~ spl3_21
    | spl3_22
    | ~ spl3_34 ),
    inference(avatar_split_clause,[],[f269,f234,f180,f176,f168,f306])).

fof(f180,plain,
    ( spl3_22
  <=> r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f269,plain,
    ( ~ r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),sK2)
    | ~ spl3_19
    | ~ spl3_21
    | spl3_22
    | ~ spl3_34 ),
    inference(backward_demodulation,[],[f181,f266])).

fof(f181,plain,
    ( ~ r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2)
    | spl3_22 ),
    inference(avatar_component_clause,[],[f180])).

fof(f303,plain,
    ( ~ spl3_42
    | ~ spl3_19
    | ~ spl3_21
    | spl3_23
    | ~ spl3_34 ),
    inference(avatar_split_clause,[],[f268,f234,f187,f176,f168,f301])).

fof(f187,plain,
    ( spl3_23
  <=> v1_xboole_0(k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f268,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK2))
    | ~ spl3_19
    | ~ spl3_21
    | spl3_23
    | ~ spl3_34 ),
    inference(backward_demodulation,[],[f188,f266])).

fof(f188,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1))
    | spl3_23 ),
    inference(avatar_component_clause,[],[f187])).

fof(f299,plain,
    ( spl3_41
    | ~ spl3_19
    | ~ spl3_21
    | ~ spl3_34 ),
    inference(avatar_split_clause,[],[f270,f234,f176,f168,f297])).

fof(f270,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
    | ~ spl3_19
    | ~ spl3_21
    | ~ spl3_34 ),
    inference(backward_demodulation,[],[f169,f266])).

fof(f295,plain,
    ( spl3_40
    | ~ spl3_18
    | ~ spl3_19
    | ~ spl3_21
    | ~ spl3_34 ),
    inference(avatar_split_clause,[],[f271,f234,f176,f168,f164,f293])).

fof(f164,plain,
    ( spl3_18
  <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f271,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ spl3_18
    | ~ spl3_19
    | ~ spl3_21
    | ~ spl3_34 ),
    inference(backward_demodulation,[],[f165,f266])).

fof(f165,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f164])).

fof(f291,plain,
    ( ~ spl3_1
    | ~ spl3_15
    | ~ spl3_33
    | spl3_36 ),
    inference(avatar_contradiction_clause,[],[f290])).

fof(f290,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_15
    | ~ spl3_33
    | spl3_36 ),
    inference(subsumption_resolution,[],[f289,f255])).

fof(f289,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl3_1
    | ~ spl3_15
    | spl3_36 ),
    inference(subsumption_resolution,[],[f286,f87])).

fof(f286,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_15
    | spl3_36 ),
    inference(resolution,[],[f254,f143])).

fof(f254,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | spl3_36 ),
    inference(avatar_component_clause,[],[f253])).

fof(f279,plain,
    ( ~ spl3_1
    | ~ spl3_14
    | ~ spl3_33
    | spl3_35 ),
    inference(avatar_contradiction_clause,[],[f278])).

fof(f278,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_14
    | ~ spl3_33
    | spl3_35 ),
    inference(subsumption_resolution,[],[f277,f255])).

fof(f277,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl3_1
    | ~ spl3_14
    | spl3_35 ),
    inference(subsumption_resolution,[],[f274,f87])).

fof(f274,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_14
    | spl3_35 ),
    inference(resolution,[],[f251,f139])).

% (3777)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
fof(f251,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | spl3_35 ),
    inference(avatar_component_clause,[],[f250])).

fof(f264,plain,(
    spl3_38 ),
    inference(avatar_split_clause,[],[f66,f262])).

fof(f66,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(f239,plain,
    ( ~ spl3_16
    | ~ spl3_19
    | spl3_33 ),
    inference(avatar_contradiction_clause,[],[f237])).

fof(f237,plain,
    ( $false
    | ~ spl3_16
    | ~ spl3_19
    | spl3_33 ),
    inference(unit_resulting_resolution,[],[f169,f231,f147])).

fof(f147,plain,
    ( ! [X2,X0,X1] :
        ( v1_relat_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl3_16
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f231,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_33 ),
    inference(avatar_component_clause,[],[f230])).

fof(f236,plain,(
    spl3_34 ),
    inference(avatar_split_clause,[],[f73,f234])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f232,plain,
    ( spl3_32
    | ~ spl3_33
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_27 ),
    inference(avatar_split_clause,[],[f224,f203,f90,f86,f230,f227])).

fof(f203,plain,
    ( spl3_27
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v2_funct_1(X0)
        | k2_funct_1(k2_funct_1(X0)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f224,plain,
    ( ~ v1_relat_1(sK2)
    | sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_27 ),
    inference(subsumption_resolution,[],[f222,f87])).

fof(f222,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ spl3_2
    | ~ spl3_27 ),
    inference(resolution,[],[f204,f91])).

fof(f204,plain,
    ( ! [X0] :
        ( ~ v2_funct_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | k2_funct_1(k2_funct_1(X0)) = X0 )
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f203])).

fof(f221,plain,(
    spl3_31 ),
    inference(avatar_split_clause,[],[f71,f219])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0)
      | k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

fof(f217,plain,(
    spl3_30 ),
    inference(avatar_split_clause,[],[f64,f215])).

fof(f64,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f213,plain,(
    spl3_29 ),
    inference(avatar_split_clause,[],[f63,f211])).

fof(f63,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f205,plain,(
    spl3_27 ),
    inference(avatar_split_clause,[],[f62,f203])).

fof(f62,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k2_funct_1(k2_funct_1(X0)) = X0 ) ),
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

fof(f193,plain,(
    spl3_24 ),
    inference(avatar_split_clause,[],[f74,f191])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f189,plain,
    ( ~ spl3_23
    | spl3_3
    | ~ spl3_4
    | ~ spl3_13
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f185,f160,f134,f98,f94,f187])).

fof(f94,plain,
    ( spl3_3
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f98,plain,
    ( spl3_4
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f134,plain,
    ( spl3_13
  <=> ! [X0] :
        ( v2_struct_0(X0)
        | ~ l1_struct_0(X0)
        | ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f160,plain,
    ( spl3_17
  <=> u1_struct_0(sK1) = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f185,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1))
    | spl3_3
    | ~ spl3_4
    | ~ spl3_13
    | ~ spl3_17 ),
    inference(forward_demodulation,[],[f184,f161])).

fof(f161,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f160])).

fof(f184,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | spl3_3
    | ~ spl3_4
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f183,f99])).

fof(f99,plain,
    ( l1_struct_0(sK1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f98])).

fof(f183,plain,
    ( ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(u1_struct_0(sK1))
    | spl3_3
    | ~ spl3_13 ),
    inference(resolution,[],[f135,f95])).

fof(f95,plain,
    ( ~ v2_struct_0(sK1)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f94])).

fof(f135,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ l1_struct_0(X0)
        | ~ v1_xboole_0(u1_struct_0(X0)) )
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f134])).

fof(f182,plain,
    ( ~ spl3_22
    | ~ spl3_4
    | ~ spl3_5
    | spl3_11
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f158,f130,f126,f102,f98,f180])).

fof(f102,plain,
    ( spl3_5
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f126,plain,
    ( spl3_11
  <=> r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f130,plain,
    ( spl3_12
  <=> ! [X0] :
        ( ~ l1_struct_0(X0)
        | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f158,plain,
    ( ~ r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2)
    | ~ spl3_4
    | ~ spl3_5
    | spl3_11
    | ~ spl3_12 ),
    inference(backward_demodulation,[],[f151,f150])).

fof(f150,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_5
    | ~ spl3_12 ),
    inference(resolution,[],[f131,f103])).

fof(f103,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f102])).

fof(f131,plain,
    ( ! [X0] :
        ( ~ l1_struct_0(X0)
        | k2_struct_0(X0) = u1_struct_0(X0) )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f130])).

fof(f151,plain,
    ( ~ r2_funct_2(u1_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2)
    | ~ spl3_4
    | spl3_11
    | ~ spl3_12 ),
    inference(backward_demodulation,[],[f127,f149])).

fof(f149,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl3_4
    | ~ spl3_12 ),
    inference(resolution,[],[f131,f99])).

fof(f127,plain,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)
    | spl3_11 ),
    inference(avatar_component_clause,[],[f126])).

fof(f178,plain,
    ( spl3_21
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_8
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f157,f130,f114,f102,f98,f176])).

fof(f114,plain,
    ( spl3_8
  <=> k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f157,plain,
    ( k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_8
    | ~ spl3_12 ),
    inference(backward_demodulation,[],[f152,f150])).

fof(f152,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_4
    | ~ spl3_8
    | ~ spl3_12 ),
    inference(backward_demodulation,[],[f115,f149])).

fof(f115,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f114])).

fof(f170,plain,
    ( spl3_19
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_7
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f156,f130,f110,f102,f98,f168])).

fof(f110,plain,
    ( spl3_7
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f156,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_7
    | ~ spl3_12 ),
    inference(backward_demodulation,[],[f153,f150])).

fof(f153,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_4
    | ~ spl3_7
    | ~ spl3_12 ),
    inference(backward_demodulation,[],[f111,f149])).

fof(f111,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f110])).

fof(f166,plain,
    ( spl3_18
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f155,f130,f106,f102,f98,f164])).

fof(f106,plain,
    ( spl3_6
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f155,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_12 ),
    inference(backward_demodulation,[],[f154,f150])).

fof(f154,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_12 ),
    inference(backward_demodulation,[],[f107,f149])).

fof(f107,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f106])).

fof(f162,plain,
    ( spl3_17
    | ~ spl3_4
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f149,f130,f98,f160])).

fof(f148,plain,(
    spl3_16 ),
    inference(avatar_split_clause,[],[f72,f146])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f144,plain,(
    spl3_15 ),
    inference(avatar_split_clause,[],[f61,f142])).

fof(f61,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | v1_funct_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f140,plain,(
    spl3_14 ),
    inference(avatar_split_clause,[],[f60,f138])).

fof(f60,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | v1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f136,plain,(
    spl3_13 ),
    inference(avatar_split_clause,[],[f59,f134])).

fof(f59,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f132,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f58,f130])).

fof(f58,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f128,plain,(
    ~ spl3_11 ),
    inference(avatar_split_clause,[],[f52,f126])).

fof(f52,plain,(
    ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( ( l1_struct_0(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( ( v2_funct_1(X2)
                    & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
                 => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( ( l1_struct_0(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
               => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tops_2)).

fof(f124,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f57,f122])).

fof(f57,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f116,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f50,f114])).

fof(f50,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f112,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f49,f110])).

fof(f49,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f20])).

fof(f108,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f48,f106])).

fof(f48,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f104,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f55,f102])).

fof(f55,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f100,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f54,f98])).

fof(f54,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f96,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f53,f94])).

fof(f53,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f92,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f51,f90])).

fof(f51,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f88,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f47,f86])).

fof(f47,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n019.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 12:48:07 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.47  % (3784)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.47  % (3780)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.47  % (3781)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.48  % (3784)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (3776)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (3789)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.49  % (3786)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.49  % (3778)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.49  % (3775)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.49  % (3782)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.49  % (3776)Refutation not found, incomplete strategy% (3776)------------------------------
% 0.21/0.49  % (3776)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (3776)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (3776)Memory used [KB]: 10746
% 0.21/0.49  % (3776)Time elapsed: 0.073 s
% 0.21/0.49  % (3776)------------------------------
% 0.21/0.49  % (3776)------------------------------
% 0.21/0.49  % (3783)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f567,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f88,f92,f96,f100,f104,f108,f112,f116,f124,f128,f132,f136,f140,f144,f148,f162,f166,f170,f178,f182,f189,f193,f205,f213,f217,f221,f232,f236,f239,f264,f279,f291,f295,f299,f303,f308,f318,f322,f326,f334,f338,f362,f366,f375,f379,f383,f392,f402,f410,f425,f429,f472,f514,f519,f526,f541,f549,f559,f566])).
% 0.21/0.49  fof(f566,plain,(
% 0.21/0.49    ~spl3_1 | ~spl3_47 | ~spl3_75 | ~spl3_77 | spl3_78),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f565])).
% 0.21/0.49  fof(f565,plain,(
% 0.21/0.49    $false | (~spl3_1 | ~spl3_47 | ~spl3_75 | ~spl3_77 | spl3_78)),
% 0.21/0.49    inference(subsumption_resolution,[],[f564,f87])).
% 0.21/0.49  fof(f87,plain,(
% 0.21/0.49    v1_funct_1(sK2) | ~spl3_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f86])).
% 0.21/0.49  fof(f86,plain,(
% 0.21/0.49    spl3_1 <=> v1_funct_1(sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.49  fof(f564,plain,(
% 0.21/0.49    ~v1_funct_1(sK2) | (~spl3_47 | ~spl3_75 | ~spl3_77 | spl3_78)),
% 0.21/0.49    inference(subsumption_resolution,[],[f563,f548])).
% 0.21/0.49  fof(f548,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~spl3_77),
% 0.21/0.49    inference(avatar_component_clause,[],[f547])).
% 0.21/0.49  fof(f547,plain,(
% 0.21/0.49    spl3_77 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_77])])).
% 0.21/0.49  fof(f563,plain,(
% 0.21/0.49    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v1_funct_1(sK2) | (~spl3_47 | ~spl3_75 | spl3_78)),
% 0.21/0.49    inference(subsumption_resolution,[],[f561,f540])).
% 0.21/0.49  fof(f540,plain,(
% 0.21/0.49    v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~spl3_75),
% 0.21/0.49    inference(avatar_component_clause,[],[f539])).
% 0.21/0.49  fof(f539,plain,(
% 0.21/0.49    spl3_75 <=> v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_75])])).
% 0.21/0.49  fof(f561,plain,(
% 0.21/0.49    ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v1_funct_1(sK2) | (~spl3_47 | spl3_78)),
% 0.21/0.49    inference(resolution,[],[f558,f325])).
% 0.21/0.49  fof(f325,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r2_funct_2(X1,X2,X0,X0) | ~v1_funct_2(X0,X1,X2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X0)) ) | ~spl3_47),
% 0.21/0.49    inference(avatar_component_clause,[],[f324])).
% 0.21/0.49  fof(f324,plain,(
% 0.21/0.49    spl3_47 <=> ! [X1,X0,X2] : (~v1_funct_1(X0) | ~v1_funct_2(X0,X1,X2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | r2_funct_2(X1,X2,X0,X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).
% 0.21/0.49  fof(f558,plain,(
% 0.21/0.49    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2) | spl3_78),
% 0.21/0.49    inference(avatar_component_clause,[],[f557])).
% 0.21/0.49  fof(f557,plain,(
% 0.21/0.49    spl3_78 <=> r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_78])])).
% 0.21/0.49  fof(f559,plain,(
% 0.21/0.49    ~spl3_78 | spl3_59 | ~spl3_71 | ~spl3_72),
% 0.21/0.49    inference(avatar_split_clause,[],[f537,f512,f509,f400,f557])).
% 0.21/0.49  fof(f400,plain,(
% 0.21/0.49    spl3_59 <=> r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_59])])).
% 0.21/0.49  fof(f509,plain,(
% 0.21/0.49    spl3_71 <=> sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_71])])).
% 0.21/0.49  fof(f512,plain,(
% 0.21/0.49    spl3_72 <=> k2_struct_0(sK0) = k1_relat_1(sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_72])])).
% 0.21/0.49  fof(f537,plain,(
% 0.21/0.49    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2) | (spl3_59 | ~spl3_71 | ~spl3_72)),
% 0.21/0.49    inference(backward_demodulation,[],[f533,f510])).
% 0.21/0.49  fof(f510,plain,(
% 0.21/0.49    sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~spl3_71),
% 0.21/0.49    inference(avatar_component_clause,[],[f509])).
% 0.21/0.49  fof(f533,plain,(
% 0.21/0.49    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),sK2) | (spl3_59 | ~spl3_72)),
% 0.21/0.49    inference(backward_demodulation,[],[f401,f515])).
% 0.21/0.49  fof(f515,plain,(
% 0.21/0.49    k2_struct_0(sK0) = k1_relat_1(sK2) | ~spl3_72),
% 0.21/0.49    inference(avatar_component_clause,[],[f512])).
% 0.21/0.49  fof(f401,plain,(
% 0.21/0.49    ~r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),sK2) | spl3_59),
% 0.21/0.49    inference(avatar_component_clause,[],[f400])).
% 0.21/0.49  fof(f549,plain,(
% 0.21/0.49    spl3_77 | ~spl3_41 | ~spl3_72),
% 0.21/0.49    inference(avatar_split_clause,[],[f529,f512,f297,f547])).
% 0.21/0.49  fof(f297,plain,(
% 0.21/0.49    spl3_41 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).
% 0.21/0.49  fof(f529,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | (~spl3_41 | ~spl3_72)),
% 0.21/0.49    inference(backward_demodulation,[],[f298,f515])).
% 0.21/0.49  fof(f298,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | ~spl3_41),
% 0.21/0.49    inference(avatar_component_clause,[],[f297])).
% 0.21/0.49  fof(f541,plain,(
% 0.21/0.49    spl3_75 | ~spl3_40 | ~spl3_72),
% 0.21/0.49    inference(avatar_split_clause,[],[f528,f512,f293,f539])).
% 0.21/0.49  fof(f293,plain,(
% 0.21/0.49    spl3_40 <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).
% 0.21/0.49  fof(f528,plain,(
% 0.21/0.49    v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | (~spl3_40 | ~spl3_72)),
% 0.21/0.49    inference(backward_demodulation,[],[f294,f515])).
% 0.21/0.49  fof(f294,plain,(
% 0.21/0.49    v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | ~spl3_40),
% 0.21/0.49    inference(avatar_component_clause,[],[f293])).
% 0.21/0.49  fof(f526,plain,(
% 0.21/0.49    ~spl3_24 | ~spl3_41 | spl3_73),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f524])).
% 0.21/0.49  fof(f524,plain,(
% 0.21/0.49    $false | (~spl3_24 | ~spl3_41 | spl3_73)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f298,f518,f192])).
% 0.21/0.49  fof(f192,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl3_24),
% 0.21/0.49    inference(avatar_component_clause,[],[f191])).
% 0.21/0.49  fof(f191,plain,(
% 0.21/0.49    spl3_24 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.21/0.49  fof(f518,plain,(
% 0.21/0.49    ~v4_relat_1(sK2,k2_struct_0(sK0)) | spl3_73),
% 0.21/0.49    inference(avatar_component_clause,[],[f517])).
% 0.21/0.49  fof(f517,plain,(
% 0.21/0.49    spl3_73 <=> v4_relat_1(sK2,k2_struct_0(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_73])])).
% 0.21/0.49  fof(f519,plain,(
% 0.21/0.49    spl3_72 | ~spl3_73 | ~spl3_31 | ~spl3_33 | ~spl3_64),
% 0.21/0.49    inference(avatar_split_clause,[],[f460,f427,f230,f219,f517,f512])).
% 0.21/0.49  fof(f219,plain,(
% 0.21/0.49    spl3_31 <=> ! [X1,X0] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 0.21/0.49  fof(f230,plain,(
% 0.21/0.49    spl3_33 <=> v1_relat_1(sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 0.21/0.49  fof(f427,plain,(
% 0.21/0.49    spl3_64 <=> v1_partfun1(sK2,k2_struct_0(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_64])])).
% 0.21/0.49  fof(f460,plain,(
% 0.21/0.49    ~v4_relat_1(sK2,k2_struct_0(sK0)) | k2_struct_0(sK0) = k1_relat_1(sK2) | (~spl3_31 | ~spl3_33 | ~spl3_64)),
% 0.21/0.49    inference(subsumption_resolution,[],[f459,f255])).
% 0.21/0.49  fof(f255,plain,(
% 0.21/0.49    v1_relat_1(sK2) | ~spl3_33),
% 0.21/0.49    inference(avatar_component_clause,[],[f230])).
% 0.21/0.49  fof(f459,plain,(
% 0.21/0.49    ~v4_relat_1(sK2,k2_struct_0(sK0)) | k2_struct_0(sK0) = k1_relat_1(sK2) | ~v1_relat_1(sK2) | (~spl3_31 | ~spl3_64)),
% 0.21/0.49    inference(resolution,[],[f428,f220])).
% 0.21/0.49  fof(f220,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | k1_relat_1(X1) = X0 | ~v1_relat_1(X1)) ) | ~spl3_31),
% 0.21/0.49    inference(avatar_component_clause,[],[f219])).
% 0.21/0.49  fof(f428,plain,(
% 0.21/0.49    v1_partfun1(sK2,k2_struct_0(sK0)) | ~spl3_64),
% 0.21/0.49    inference(avatar_component_clause,[],[f427])).
% 0.21/0.49  fof(f514,plain,(
% 0.21/0.49    ~spl3_36 | spl3_71 | ~spl3_72 | ~spl3_1 | ~spl3_2 | ~spl3_32 | ~spl3_33 | ~spl3_49 | ~spl3_55 | ~spl3_57 | ~spl3_58 | ~spl3_60 | ~spl3_63),
% 0.21/0.49    inference(avatar_split_clause,[],[f457,f423,f408,f390,f381,f373,f332,f230,f227,f90,f86,f512,f509,f253])).
% 0.21/0.49  fof(f253,plain,(
% 0.21/0.49    spl3_36 <=> v1_funct_1(k2_funct_1(sK2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 0.21/0.49  fof(f90,plain,(
% 0.21/0.49    spl3_2 <=> v2_funct_1(sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.49  fof(f227,plain,(
% 0.21/0.49    spl3_32 <=> sK2 = k2_funct_1(k2_funct_1(sK2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 0.21/0.49  fof(f332,plain,(
% 0.21/0.49    spl3_49 <=> k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).
% 0.21/0.49  fof(f373,plain,(
% 0.21/0.49    spl3_55 <=> v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_55])])).
% 0.21/0.49  fof(f381,plain,(
% 0.21/0.49    spl3_57 <=> ! [X1,X0,X2] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | k2_funct_1(X2) = k2_tops_2(X0,X1,X2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).
% 0.21/0.49  fof(f390,plain,(
% 0.21/0.49    spl3_58 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0))))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_58])])).
% 0.21/0.49  fof(f408,plain,(
% 0.21/0.49    spl3_60 <=> k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_60])])).
% 0.21/0.49  fof(f423,plain,(
% 0.21/0.49    spl3_63 <=> ! [X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | v2_funct_1(k2_funct_1(X1)) | ~v2_funct_1(X1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_63])])).
% 0.21/0.49  fof(f457,plain,(
% 0.21/0.49    k2_struct_0(sK0) != k1_relat_1(sK2) | sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_2 | ~spl3_32 | ~spl3_33 | ~spl3_49 | ~spl3_55 | ~spl3_57 | ~spl3_58 | ~spl3_60 | ~spl3_63)),
% 0.21/0.49    inference(inner_rewriting,[],[f454])).
% 0.21/0.49  fof(f454,plain,(
% 0.21/0.49    k2_struct_0(sK0) != k1_relat_1(sK2) | sK2 = k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_2 | ~spl3_32 | ~spl3_33 | ~spl3_49 | ~spl3_55 | ~spl3_57 | ~spl3_58 | ~spl3_60 | ~spl3_63)),
% 0.21/0.49    inference(backward_demodulation,[],[f451,f333])).
% 0.21/0.49  fof(f333,plain,(
% 0.21/0.49    k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) | ~spl3_49),
% 0.21/0.49    inference(avatar_component_clause,[],[f332])).
% 0.21/0.49  fof(f451,plain,(
% 0.21/0.49    sK2 = k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) | k2_struct_0(sK0) != k2_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_2 | ~spl3_32 | ~spl3_33 | ~spl3_55 | ~spl3_57 | ~spl3_58 | ~spl3_60 | ~spl3_63)),
% 0.21/0.49    inference(forward_demodulation,[],[f450,f228])).
% 0.21/0.49  fof(f228,plain,(
% 0.21/0.49    sK2 = k2_funct_1(k2_funct_1(sK2)) | ~spl3_32),
% 0.21/0.49    inference(avatar_component_clause,[],[f227])).
% 0.21/0.49  fof(f450,plain,(
% 0.21/0.49    k2_struct_0(sK0) != k2_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) | (~spl3_1 | ~spl3_2 | ~spl3_33 | ~spl3_55 | ~spl3_57 | ~spl3_58 | ~spl3_60 | ~spl3_63)),
% 0.21/0.49    inference(forward_demodulation,[],[f449,f409])).
% 0.21/0.49  fof(f409,plain,(
% 0.21/0.49    k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) | ~spl3_60),
% 0.21/0.49    inference(avatar_component_clause,[],[f408])).
% 0.21/0.49  fof(f449,plain,(
% 0.21/0.49    ~v1_funct_1(k2_funct_1(sK2)) | k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) | (~spl3_1 | ~spl3_2 | ~spl3_33 | ~spl3_55 | ~spl3_57 | ~spl3_58 | ~spl3_63)),
% 0.21/0.49    inference(subsumption_resolution,[],[f448,f439])).
% 0.21/0.49  fof(f439,plain,(
% 0.21/0.49    v2_funct_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_2 | ~spl3_33 | ~spl3_63)),
% 0.21/0.49    inference(subsumption_resolution,[],[f434,f87])).
% 0.21/0.49  fof(f434,plain,(
% 0.21/0.49    v2_funct_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | (~spl3_2 | ~spl3_33 | ~spl3_63)),
% 0.21/0.49    inference(subsumption_resolution,[],[f431,f255])).
% 0.21/0.49  fof(f431,plain,(
% 0.21/0.49    ~v1_relat_1(sK2) | v2_funct_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | (~spl3_2 | ~spl3_63)),
% 0.21/0.49    inference(resolution,[],[f424,f91])).
% 0.21/0.49  fof(f91,plain,(
% 0.21/0.49    v2_funct_1(sK2) | ~spl3_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f90])).
% 0.21/0.49  fof(f424,plain,(
% 0.21/0.49    ( ! [X1] : (~v2_funct_1(X1) | ~v1_relat_1(X1) | v2_funct_1(k2_funct_1(X1)) | ~v1_funct_1(X1)) ) | ~spl3_63),
% 0.21/0.49    inference(avatar_component_clause,[],[f423])).
% 0.21/0.49  fof(f448,plain,(
% 0.21/0.49    ~v1_funct_1(k2_funct_1(sK2)) | k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) | ~v2_funct_1(k2_funct_1(sK2)) | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) | (~spl3_55 | ~spl3_57 | ~spl3_58)),
% 0.21/0.49    inference(subsumption_resolution,[],[f403,f374])).
% 0.21/0.49  fof(f374,plain,(
% 0.21/0.49    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) | ~spl3_55),
% 0.21/0.49    inference(avatar_component_clause,[],[f373])).
% 0.21/0.49  fof(f403,plain,(
% 0.21/0.49    ~v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) | ~v1_funct_1(k2_funct_1(sK2)) | k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) | ~v2_funct_1(k2_funct_1(sK2)) | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) | (~spl3_57 | ~spl3_58)),
% 0.21/0.49    inference(resolution,[],[f391,f382])).
% 0.21/0.49  fof(f382,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | k2_funct_1(X2) = k2_tops_2(X0,X1,X2)) ) | ~spl3_57),
% 0.21/0.49    inference(avatar_component_clause,[],[f381])).
% 0.21/0.49  fof(f391,plain,(
% 0.21/0.49    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) | ~spl3_58),
% 0.21/0.49    inference(avatar_component_clause,[],[f390])).
% 0.21/0.49  fof(f472,plain,(
% 0.21/0.49    spl3_48 | ~spl3_1 | ~spl3_2 | ~spl3_33 | ~spl3_63),
% 0.21/0.49    inference(avatar_split_clause,[],[f439,f423,f230,f90,f86,f329])).
% 0.21/0.49  fof(f329,plain,(
% 0.21/0.49    spl3_48 <=> v2_funct_1(k2_funct_1(sK2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).
% 0.21/0.49  fof(f429,plain,(
% 0.21/0.49    spl3_64 | ~spl3_1 | ~spl3_40 | ~spl3_41 | ~spl3_54),
% 0.21/0.49    inference(avatar_split_clause,[],[f421,f364,f297,f293,f86,f427])).
% 0.21/0.49  fof(f364,plain,(
% 0.21/0.49    spl3_54 <=> ! [X1,X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(sK2)))) | ~v1_funct_1(X0) | ~v1_funct_2(X0,X1,k2_relat_1(sK2)) | v1_partfun1(X0,X1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_54])])).
% 0.21/0.49  fof(f421,plain,(
% 0.21/0.49    v1_partfun1(sK2,k2_struct_0(sK0)) | (~spl3_1 | ~spl3_40 | ~spl3_41 | ~spl3_54)),
% 0.21/0.49    inference(subsumption_resolution,[],[f420,f294])).
% 0.21/0.49  fof(f420,plain,(
% 0.21/0.49    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | v1_partfun1(sK2,k2_struct_0(sK0)) | (~spl3_1 | ~spl3_41 | ~spl3_54)),
% 0.21/0.49    inference(subsumption_resolution,[],[f419,f87])).
% 0.21/0.49  fof(f419,plain,(
% 0.21/0.49    ~v1_funct_1(sK2) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | v1_partfun1(sK2,k2_struct_0(sK0)) | (~spl3_41 | ~spl3_54)),
% 0.21/0.49    inference(resolution,[],[f365,f298])).
% 0.21/0.49  fof(f365,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(sK2)))) | ~v1_funct_1(X0) | ~v1_funct_2(X0,X1,k2_relat_1(sK2)) | v1_partfun1(X0,X1)) ) | ~spl3_54),
% 0.21/0.49    inference(avatar_component_clause,[],[f364])).
% 0.21/0.49  fof(f425,plain,(
% 0.21/0.49    spl3_63 | ~spl3_10 | ~spl3_14 | ~spl3_15 | ~spl3_30 | ~spl3_38 | ~spl3_50),
% 0.21/0.49    inference(avatar_split_clause,[],[f350,f336,f262,f215,f142,f138,f122,f423])).
% 0.21/0.49  fof(f122,plain,(
% 0.21/0.49    spl3_10 <=> ! [X0] : v2_funct_1(k6_relat_1(X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.49  fof(f138,plain,(
% 0.21/0.49    spl3_14 <=> ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | v1_relat_1(k2_funct_1(X0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.49  fof(f142,plain,(
% 0.21/0.49    spl3_15 <=> ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | v1_funct_1(k2_funct_1(X0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.21/0.49  fof(f215,plain,(
% 0.21/0.49    spl3_30 <=> ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.21/0.49  fof(f262,plain,(
% 0.21/0.49    spl3_38 <=> ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).
% 0.21/0.49  fof(f336,plain,(
% 0.21/0.49    spl3_50 <=> ! [X1,X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)) | k2_relat_1(X1) != k1_relat_1(X0) | v2_funct_1(X1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_50])])).
% 0.21/0.49  fof(f350,plain,(
% 0.21/0.49    ( ! [X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | v2_funct_1(k2_funct_1(X1)) | ~v2_funct_1(X1)) ) | (~spl3_10 | ~spl3_14 | ~spl3_15 | ~spl3_30 | ~spl3_38 | ~spl3_50)),
% 0.21/0.49    inference(subsumption_resolution,[],[f349,f216])).
% 0.21/0.49  fof(f216,plain,(
% 0.21/0.49    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl3_30),
% 0.21/0.49    inference(avatar_component_clause,[],[f215])).
% 0.21/0.49  fof(f349,plain,(
% 0.21/0.49    ( ! [X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | k1_relat_1(X1) != k2_relat_1(k2_funct_1(X1)) | v2_funct_1(k2_funct_1(X1)) | ~v2_funct_1(X1)) ) | (~spl3_10 | ~spl3_14 | ~spl3_15 | ~spl3_38 | ~spl3_50)),
% 0.21/0.49    inference(subsumption_resolution,[],[f348,f143])).
% 0.21/0.49  % (3785)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.49  fof(f143,plain,(
% 0.21/0.49    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl3_15),
% 0.21/0.49    inference(avatar_component_clause,[],[f142])).
% 0.21/0.49  fof(f348,plain,(
% 0.21/0.49    ( ! [X1] : (~v1_funct_1(X1) | ~v1_funct_1(k2_funct_1(X1)) | ~v1_relat_1(X1) | k1_relat_1(X1) != k2_relat_1(k2_funct_1(X1)) | v2_funct_1(k2_funct_1(X1)) | ~v2_funct_1(X1)) ) | (~spl3_10 | ~spl3_14 | ~spl3_38 | ~spl3_50)),
% 0.21/0.49    inference(subsumption_resolution,[],[f347,f139])).
% 0.21/0.49  fof(f139,plain,(
% 0.21/0.49    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl3_14),
% 0.21/0.49    inference(avatar_component_clause,[],[f138])).
% 0.21/0.49  fof(f347,plain,(
% 0.21/0.49    ( ! [X1] : (~v1_funct_1(X1) | ~v1_relat_1(k2_funct_1(X1)) | ~v1_funct_1(k2_funct_1(X1)) | ~v1_relat_1(X1) | k1_relat_1(X1) != k2_relat_1(k2_funct_1(X1)) | v2_funct_1(k2_funct_1(X1)) | ~v2_funct_1(X1)) ) | (~spl3_10 | ~spl3_38 | ~spl3_50)),
% 0.21/0.49    inference(subsumption_resolution,[],[f345,f123])).
% 0.21/0.49  fof(f123,plain,(
% 0.21/0.49    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) ) | ~spl3_10),
% 0.21/0.49    inference(avatar_component_clause,[],[f122])).
% 0.21/0.49  fof(f345,plain,(
% 0.21/0.49    ( ! [X1] : (~v2_funct_1(k6_relat_1(k2_relat_1(X1))) | ~v1_funct_1(X1) | ~v1_relat_1(k2_funct_1(X1)) | ~v1_funct_1(k2_funct_1(X1)) | ~v1_relat_1(X1) | k1_relat_1(X1) != k2_relat_1(k2_funct_1(X1)) | v2_funct_1(k2_funct_1(X1)) | ~v2_funct_1(X1)) ) | (~spl3_38 | ~spl3_50)),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f344])).
% 0.21/0.49  fof(f344,plain,(
% 0.21/0.49    ( ! [X1] : (~v2_funct_1(k6_relat_1(k2_relat_1(X1))) | ~v1_funct_1(X1) | ~v1_relat_1(k2_funct_1(X1)) | ~v1_funct_1(k2_funct_1(X1)) | ~v1_relat_1(X1) | k1_relat_1(X1) != k2_relat_1(k2_funct_1(X1)) | v2_funct_1(k2_funct_1(X1)) | ~v1_funct_1(X1) | ~v2_funct_1(X1) | ~v1_relat_1(X1)) ) | (~spl3_38 | ~spl3_50)),
% 0.21/0.49    inference(superposition,[],[f337,f263])).
% 0.21/0.49  fof(f263,plain,(
% 0.21/0.49    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl3_38),
% 0.21/0.49    inference(avatar_component_clause,[],[f262])).
% 0.21/0.49  fof(f337,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X0) | k2_relat_1(X1) != k1_relat_1(X0) | v2_funct_1(X1)) ) | ~spl3_50),
% 0.21/0.49    inference(avatar_component_clause,[],[f336])).
% 0.21/0.49  fof(f410,plain,(
% 0.21/0.49    spl3_60 | ~spl3_34 | ~spl3_58),
% 0.21/0.49    inference(avatar_split_clause,[],[f406,f390,f234,f408])).
% 0.21/0.49  fof(f234,plain,(
% 0.21/0.49    spl3_34 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 0.21/0.49  fof(f406,plain,(
% 0.21/0.49    k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) | (~spl3_34 | ~spl3_58)),
% 0.21/0.49    inference(resolution,[],[f391,f235])).
% 0.21/0.49  fof(f235,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) ) | ~spl3_34),
% 0.21/0.49    inference(avatar_component_clause,[],[f234])).
% 0.21/0.49  fof(f402,plain,(
% 0.21/0.49    ~spl3_59 | ~spl3_1 | ~spl3_2 | ~spl3_40 | ~spl3_41 | spl3_43 | ~spl3_46 | ~spl3_57),
% 0.21/0.49    inference(avatar_split_clause,[],[f398,f381,f320,f306,f297,f293,f90,f86,f400])).
% 0.21/0.49  fof(f306,plain,(
% 0.21/0.49    spl3_43 <=> r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).
% 0.21/0.49  fof(f320,plain,(
% 0.21/0.49    spl3_46 <=> k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).
% 0.21/0.49  fof(f398,plain,(
% 0.21/0.49    ~r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),sK2) | (~spl3_1 | ~spl3_2 | ~spl3_40 | ~spl3_41 | spl3_43 | ~spl3_46 | ~spl3_57)),
% 0.21/0.49    inference(backward_demodulation,[],[f307,f397])).
% 0.21/0.49  fof(f397,plain,(
% 0.21/0.49    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | (~spl3_1 | ~spl3_2 | ~spl3_40 | ~spl3_41 | ~spl3_46 | ~spl3_57)),
% 0.21/0.49    inference(subsumption_resolution,[],[f396,f91])).
% 0.21/0.49  fof(f396,plain,(
% 0.21/0.49    ~v2_funct_1(sK2) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | (~spl3_1 | ~spl3_40 | ~spl3_41 | ~spl3_46 | ~spl3_57)),
% 0.21/0.49    inference(subsumption_resolution,[],[f395,f321])).
% 0.21/0.49  fof(f321,plain,(
% 0.21/0.49    k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | ~spl3_46),
% 0.21/0.49    inference(avatar_component_clause,[],[f320])).
% 0.21/0.49  fof(f395,plain,(
% 0.21/0.49    k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | ~v2_funct_1(sK2) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | (~spl3_1 | ~spl3_40 | ~spl3_41 | ~spl3_57)),
% 0.21/0.49    inference(subsumption_resolution,[],[f394,f87])).
% 0.21/0.49  fof(f394,plain,(
% 0.21/0.49    ~v1_funct_1(sK2) | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | ~v2_funct_1(sK2) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | (~spl3_40 | ~spl3_41 | ~spl3_57)),
% 0.21/0.49    inference(subsumption_resolution,[],[f393,f294])).
% 0.21/0.49  fof(f393,plain,(
% 0.21/0.49    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | ~v2_funct_1(sK2) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | (~spl3_41 | ~spl3_57)),
% 0.21/0.49    inference(resolution,[],[f382,f298])).
% 0.21/0.49  fof(f307,plain,(
% 0.21/0.49    ~r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),sK2) | spl3_43),
% 0.21/0.49    inference(avatar_component_clause,[],[f306])).
% 0.21/0.49  fof(f392,plain,(
% 0.21/0.49    spl3_58 | ~spl3_1 | ~spl3_2 | ~spl3_40 | ~spl3_41 | ~spl3_46 | ~spl3_56),
% 0.21/0.49    inference(avatar_split_clause,[],[f388,f377,f320,f297,f293,f90,f86,f390])).
% 0.21/0.49  fof(f377,plain,(
% 0.21/0.49    spl3_56 <=> ! [X1,X0,X2] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).
% 0.21/0.49  fof(f388,plain,(
% 0.21/0.49    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) | (~spl3_1 | ~spl3_2 | ~spl3_40 | ~spl3_41 | ~spl3_46 | ~spl3_56)),
% 0.21/0.49    inference(subsumption_resolution,[],[f387,f321])).
% 0.21/0.49  fof(f387,plain,(
% 0.21/0.49    k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) | (~spl3_1 | ~spl3_2 | ~spl3_40 | ~spl3_41 | ~spl3_56)),
% 0.21/0.49    inference(subsumption_resolution,[],[f386,f91])).
% 0.21/0.49  fof(f386,plain,(
% 0.21/0.49    ~v2_funct_1(sK2) | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) | (~spl3_1 | ~spl3_40 | ~spl3_41 | ~spl3_56)),
% 0.21/0.49    inference(subsumption_resolution,[],[f385,f87])).
% 0.21/0.49  fof(f385,plain,(
% 0.21/0.49    ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) | (~spl3_40 | ~spl3_41 | ~spl3_56)),
% 0.21/0.49    inference(subsumption_resolution,[],[f384,f294])).
% 0.21/0.49  fof(f384,plain,(
% 0.21/0.49    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) | (~spl3_41 | ~spl3_56)),
% 0.21/0.49    inference(resolution,[],[f378,f298])).
% 0.21/0.49  fof(f378,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) ) | ~spl3_56),
% 0.21/0.49    inference(avatar_component_clause,[],[f377])).
% 0.21/0.49  fof(f383,plain,(
% 0.21/0.49    spl3_57),
% 0.21/0.49    inference(avatar_split_clause,[],[f79,f381])).
% 0.21/0.49  fof(f79,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | k2_funct_1(X2) = k2_tops_2(X0,X1,X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f44])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.49    inference(flattening,[],[f43])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.21/0.49    inference(ennf_transformation,[],[f16])).
% 0.21/0.49  fof(f16,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).
% 0.21/0.49  fof(f379,plain,(
% 0.21/0.49    spl3_56),
% 0.21/0.49    inference(avatar_split_clause,[],[f78,f377])).
% 0.21/0.49  % (3793)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f42])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.49    inference(flattening,[],[f41])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.21/0.49    inference(ennf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).
% 0.21/0.49  fof(f375,plain,(
% 0.21/0.49    spl3_55 | ~spl3_1 | ~spl3_2 | ~spl3_40 | ~spl3_41 | ~spl3_46 | ~spl3_53),
% 0.21/0.49    inference(avatar_split_clause,[],[f371,f360,f320,f297,f293,f90,f86,f373])).
% 0.21/0.49  fof(f360,plain,(
% 0.21/0.49    spl3_53 <=> ! [X1,X0,X2] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | v1_funct_2(k2_funct_1(X2),X1,X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_53])])).
% 0.21/0.49  fof(f371,plain,(
% 0.21/0.49    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) | (~spl3_1 | ~spl3_2 | ~spl3_40 | ~spl3_41 | ~spl3_46 | ~spl3_53)),
% 0.21/0.49    inference(subsumption_resolution,[],[f370,f321])).
% 0.21/0.49  fof(f370,plain,(
% 0.21/0.49    k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) | (~spl3_1 | ~spl3_2 | ~spl3_40 | ~spl3_41 | ~spl3_53)),
% 0.21/0.49    inference(subsumption_resolution,[],[f369,f91])).
% 0.21/0.49  fof(f369,plain,(
% 0.21/0.49    ~v2_funct_1(sK2) | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) | (~spl3_1 | ~spl3_40 | ~spl3_41 | ~spl3_53)),
% 0.21/0.49    inference(subsumption_resolution,[],[f368,f87])).
% 0.21/0.49  fof(f368,plain,(
% 0.21/0.49    ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) | (~spl3_40 | ~spl3_41 | ~spl3_53)),
% 0.21/0.49    inference(subsumption_resolution,[],[f367,f294])).
% 0.21/0.49  fof(f367,plain,(
% 0.21/0.49    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) | (~spl3_41 | ~spl3_53)),
% 0.21/0.49    inference(resolution,[],[f361,f298])).
% 0.21/0.49  fof(f361,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | v1_funct_2(k2_funct_1(X2),X1,X0)) ) | ~spl3_53),
% 0.21/0.49    inference(avatar_component_clause,[],[f360])).
% 0.21/0.49  fof(f366,plain,(
% 0.21/0.49    spl3_54 | spl3_42 | ~spl3_45),
% 0.21/0.49    inference(avatar_split_clause,[],[f327,f316,f301,f364])).
% 0.21/0.49  fof(f301,plain,(
% 0.21/0.49    spl3_42 <=> v1_xboole_0(k2_relat_1(sK2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).
% 0.21/0.49  fof(f316,plain,(
% 0.21/0.49    spl3_45 <=> ! [X1,X0,X2] : (v1_xboole_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).
% 0.21/0.49  fof(f327,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(sK2)))) | ~v1_funct_1(X0) | ~v1_funct_2(X0,X1,k2_relat_1(sK2)) | v1_partfun1(X0,X1)) ) | (spl3_42 | ~spl3_45)),
% 0.21/0.49    inference(resolution,[],[f317,f302])).
% 0.21/0.49  fof(f302,plain,(
% 0.21/0.49    ~v1_xboole_0(k2_relat_1(sK2)) | spl3_42),
% 0.21/0.49    inference(avatar_component_clause,[],[f301])).
% 0.21/0.49  fof(f317,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0)) ) | ~spl3_45),
% 0.21/0.49    inference(avatar_component_clause,[],[f316])).
% 0.21/0.49  fof(f362,plain,(
% 0.21/0.49    spl3_53),
% 0.21/0.49    inference(avatar_split_clause,[],[f77,f360])).
% 0.21/0.49  fof(f77,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | v1_funct_2(k2_funct_1(X2),X1,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f42])).
% 0.21/0.49  fof(f338,plain,(
% 0.21/0.49    spl3_50),
% 0.21/0.49    inference(avatar_split_clause,[],[f67,f336])).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)) | k2_relat_1(X1) != k1_relat_1(X0) | v2_funct_1(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : ((v2_funct_1(X0) & v2_funct_1(X1)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(flattening,[],[f32])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (((v2_funct_1(X0) & v2_funct_1(X1)) | (k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_1)).
% 0.21/0.49  fof(f334,plain,(
% 0.21/0.49    ~spl3_35 | ~spl3_48 | ~spl3_36 | spl3_49 | ~spl3_29 | ~spl3_32),
% 0.21/0.49    inference(avatar_split_clause,[],[f242,f227,f211,f332,f253,f329,f250])).
% 0.21/0.49  fof(f250,plain,(
% 0.21/0.49    spl3_35 <=> v1_relat_1(k2_funct_1(sK2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).
% 0.21/0.49  fof(f211,plain,(
% 0.21/0.49    spl3_29 <=> ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.21/0.49  fof(f242,plain,(
% 0.21/0.49    k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) | ~v1_funct_1(k2_funct_1(sK2)) | ~v2_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl3_29 | ~spl3_32)),
% 0.21/0.49    inference(superposition,[],[f212,f228])).
% 0.21/0.49  fof(f212,plain,(
% 0.21/0.49    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl3_29),
% 0.21/0.49    inference(avatar_component_clause,[],[f211])).
% 0.21/0.49  fof(f326,plain,(
% 0.21/0.49    spl3_47),
% 0.21/0.49    inference(avatar_split_clause,[],[f83,f324])).
% 0.21/0.49  fof(f83,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v1_funct_1(X0) | ~v1_funct_2(X0,X1,X2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | r2_funct_2(X1,X2,X0,X0)) )),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f82])).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v1_funct_1(X0) | ~v1_funct_2(X0,X1,X2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X0,X1,X2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | r2_funct_2(X1,X2,X0,X0)) )),
% 0.21/0.49    inference(condensation,[],[f80])).
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_funct_2(X0,X1,X2,X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f46])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.49    inference(flattening,[],[f45])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.21/0.49    inference(ennf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => r2_funct_2(X0,X1,X2,X2))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).
% 0.21/0.49  fof(f322,plain,(
% 0.21/0.49    spl3_46 | ~spl3_19 | ~spl3_21 | ~spl3_34),
% 0.21/0.49    inference(avatar_split_clause,[],[f267,f234,f176,f168,f320])).
% 0.21/0.49  fof(f168,plain,(
% 0.21/0.49    spl3_19 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.21/0.49  fof(f176,plain,(
% 0.21/0.49    spl3_21 <=> k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.21/0.49  fof(f267,plain,(
% 0.21/0.49    k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | (~spl3_19 | ~spl3_21 | ~spl3_34)),
% 0.21/0.49    inference(backward_demodulation,[],[f265,f266])).
% 0.21/0.49  fof(f266,plain,(
% 0.21/0.49    k2_struct_0(sK1) = k2_relat_1(sK2) | (~spl3_19 | ~spl3_21 | ~spl3_34)),
% 0.21/0.49    inference(backward_demodulation,[],[f177,f265])).
% 0.21/0.49  fof(f177,plain,(
% 0.21/0.49    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~spl3_21),
% 0.21/0.49    inference(avatar_component_clause,[],[f176])).
% 0.21/0.49  fof(f265,plain,(
% 0.21/0.49    k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) | (~spl3_19 | ~spl3_34)),
% 0.21/0.49    inference(resolution,[],[f235,f169])).
% 0.21/0.49  fof(f169,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~spl3_19),
% 0.21/0.49    inference(avatar_component_clause,[],[f168])).
% 0.21/0.49  fof(f318,plain,(
% 0.21/0.49    spl3_45),
% 0.21/0.49    inference(avatar_split_clause,[],[f69,f316])).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.21/0.49    inference(flattening,[],[f34])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,axiom,(
% 0.21/0.49    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.21/0.49  fof(f308,plain,(
% 0.21/0.49    ~spl3_43 | ~spl3_19 | ~spl3_21 | spl3_22 | ~spl3_34),
% 0.21/0.49    inference(avatar_split_clause,[],[f269,f234,f180,f176,f168,f306])).
% 0.21/0.49  fof(f180,plain,(
% 0.21/0.49    spl3_22 <=> r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.21/0.49  fof(f269,plain,(
% 0.21/0.49    ~r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),sK2) | (~spl3_19 | ~spl3_21 | spl3_22 | ~spl3_34)),
% 0.21/0.49    inference(backward_demodulation,[],[f181,f266])).
% 0.21/0.49  fof(f181,plain,(
% 0.21/0.49    ~r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2) | spl3_22),
% 0.21/0.49    inference(avatar_component_clause,[],[f180])).
% 0.21/0.49  fof(f303,plain,(
% 0.21/0.49    ~spl3_42 | ~spl3_19 | ~spl3_21 | spl3_23 | ~spl3_34),
% 0.21/0.49    inference(avatar_split_clause,[],[f268,f234,f187,f176,f168,f301])).
% 0.21/0.49  fof(f187,plain,(
% 0.21/0.49    spl3_23 <=> v1_xboole_0(k2_struct_0(sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.21/0.49  fof(f268,plain,(
% 0.21/0.49    ~v1_xboole_0(k2_relat_1(sK2)) | (~spl3_19 | ~spl3_21 | spl3_23 | ~spl3_34)),
% 0.21/0.49    inference(backward_demodulation,[],[f188,f266])).
% 0.21/0.49  fof(f188,plain,(
% 0.21/0.49    ~v1_xboole_0(k2_struct_0(sK1)) | spl3_23),
% 0.21/0.49    inference(avatar_component_clause,[],[f187])).
% 0.21/0.49  fof(f299,plain,(
% 0.21/0.49    spl3_41 | ~spl3_19 | ~spl3_21 | ~spl3_34),
% 0.21/0.49    inference(avatar_split_clause,[],[f270,f234,f176,f168,f297])).
% 0.21/0.49  fof(f270,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | (~spl3_19 | ~spl3_21 | ~spl3_34)),
% 0.21/0.49    inference(backward_demodulation,[],[f169,f266])).
% 0.21/0.49  fof(f295,plain,(
% 0.21/0.49    spl3_40 | ~spl3_18 | ~spl3_19 | ~spl3_21 | ~spl3_34),
% 0.21/0.49    inference(avatar_split_clause,[],[f271,f234,f176,f168,f164,f293])).
% 0.21/0.49  fof(f164,plain,(
% 0.21/0.49    spl3_18 <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.21/0.49  fof(f271,plain,(
% 0.21/0.49    v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | (~spl3_18 | ~spl3_19 | ~spl3_21 | ~spl3_34)),
% 0.21/0.49    inference(backward_demodulation,[],[f165,f266])).
% 0.21/0.49  fof(f165,plain,(
% 0.21/0.49    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~spl3_18),
% 0.21/0.49    inference(avatar_component_clause,[],[f164])).
% 0.21/0.49  fof(f291,plain,(
% 0.21/0.49    ~spl3_1 | ~spl3_15 | ~spl3_33 | spl3_36),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f290])).
% 0.21/0.49  fof(f290,plain,(
% 0.21/0.49    $false | (~spl3_1 | ~spl3_15 | ~spl3_33 | spl3_36)),
% 0.21/0.49    inference(subsumption_resolution,[],[f289,f255])).
% 0.21/0.49  fof(f289,plain,(
% 0.21/0.49    ~v1_relat_1(sK2) | (~spl3_1 | ~spl3_15 | spl3_36)),
% 0.21/0.49    inference(subsumption_resolution,[],[f286,f87])).
% 0.21/0.49  fof(f286,plain,(
% 0.21/0.49    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl3_15 | spl3_36)),
% 0.21/0.49    inference(resolution,[],[f254,f143])).
% 0.21/0.49  fof(f254,plain,(
% 0.21/0.49    ~v1_funct_1(k2_funct_1(sK2)) | spl3_36),
% 0.21/0.49    inference(avatar_component_clause,[],[f253])).
% 0.21/0.49  fof(f279,plain,(
% 0.21/0.49    ~spl3_1 | ~spl3_14 | ~spl3_33 | spl3_35),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f278])).
% 0.21/0.49  fof(f278,plain,(
% 0.21/0.49    $false | (~spl3_1 | ~spl3_14 | ~spl3_33 | spl3_35)),
% 0.21/0.49    inference(subsumption_resolution,[],[f277,f255])).
% 0.21/0.49  fof(f277,plain,(
% 0.21/0.49    ~v1_relat_1(sK2) | (~spl3_1 | ~spl3_14 | spl3_35)),
% 0.21/0.49    inference(subsumption_resolution,[],[f274,f87])).
% 0.21/0.49  fof(f274,plain,(
% 0.21/0.49    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl3_14 | spl3_35)),
% 0.21/0.49    inference(resolution,[],[f251,f139])).
% 0.21/0.49  % (3777)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.49  fof(f251,plain,(
% 0.21/0.49    ~v1_relat_1(k2_funct_1(sK2)) | spl3_35),
% 0.21/0.49    inference(avatar_component_clause,[],[f250])).
% 0.21/0.49  fof(f264,plain,(
% 0.21/0.49    spl3_38),
% 0.21/0.49    inference(avatar_split_clause,[],[f66,f262])).
% 0.21/0.49  fof(f66,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(flattening,[],[f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).
% 0.21/0.49  fof(f239,plain,(
% 0.21/0.49    ~spl3_16 | ~spl3_19 | spl3_33),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f237])).
% 0.21/0.49  fof(f237,plain,(
% 0.21/0.49    $false | (~spl3_16 | ~spl3_19 | spl3_33)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f169,f231,f147])).
% 0.21/0.49  fof(f147,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl3_16),
% 0.21/0.49    inference(avatar_component_clause,[],[f146])).
% 0.21/0.49  fof(f146,plain,(
% 0.21/0.49    spl3_16 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.49  fof(f231,plain,(
% 0.21/0.49    ~v1_relat_1(sK2) | spl3_33),
% 0.21/0.49    inference(avatar_component_clause,[],[f230])).
% 0.21/0.49  fof(f236,plain,(
% 0.21/0.49    spl3_34),
% 0.21/0.49    inference(avatar_split_clause,[],[f73,f234])).
% 0.21/0.49  fof(f73,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f39])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.49  fof(f232,plain,(
% 0.21/0.49    spl3_32 | ~spl3_33 | ~spl3_1 | ~spl3_2 | ~spl3_27),
% 0.21/0.49    inference(avatar_split_clause,[],[f224,f203,f90,f86,f230,f227])).
% 0.21/0.49  fof(f203,plain,(
% 0.21/0.49    spl3_27 <=> ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k2_funct_1(k2_funct_1(X0)) = X0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 0.21/0.49  fof(f224,plain,(
% 0.21/0.49    ~v1_relat_1(sK2) | sK2 = k2_funct_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_2 | ~spl3_27)),
% 0.21/0.49    inference(subsumption_resolution,[],[f222,f87])).
% 0.21/0.49  fof(f222,plain,(
% 0.21/0.49    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | sK2 = k2_funct_1(k2_funct_1(sK2)) | (~spl3_2 | ~spl3_27)),
% 0.21/0.49    inference(resolution,[],[f204,f91])).
% 0.21/0.49  fof(f204,plain,(
% 0.21/0.49    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_funct_1(k2_funct_1(X0)) = X0) ) | ~spl3_27),
% 0.21/0.49    inference(avatar_component_clause,[],[f203])).
% 0.21/0.49  fof(f221,plain,(
% 0.21/0.49    spl3_31),
% 0.21/0.49    inference(avatar_split_clause,[],[f71,f219])).
% 0.21/0.49  fof(f71,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f37])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(flattening,[],[f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.49    inference(ennf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,axiom,(
% 0.21/0.49    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).
% 0.21/0.49  fof(f217,plain,(
% 0.21/0.49    spl3_30),
% 0.21/0.49    inference(avatar_split_clause,[],[f64,f215])).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(flattening,[],[f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 0.21/0.50  fof(f213,plain,(
% 0.21/0.50    spl3_29),
% 0.21/0.50    inference(avatar_split_clause,[],[f63,f211])).
% 0.21/0.50  fof(f63,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f29])).
% 0.21/0.50  fof(f205,plain,(
% 0.21/0.50    spl3_27),
% 0.21/0.50    inference(avatar_split_clause,[],[f62,f203])).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k2_funct_1(k2_funct_1(X0)) = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(flattening,[],[f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).
% 0.21/0.50  fof(f193,plain,(
% 0.21/0.50    spl3_24),
% 0.21/0.50    inference(avatar_split_clause,[],[f74,f191])).
% 0.21/0.50  fof(f74,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f40])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.50  fof(f189,plain,(
% 0.21/0.50    ~spl3_23 | spl3_3 | ~spl3_4 | ~spl3_13 | ~spl3_17),
% 0.21/0.50    inference(avatar_split_clause,[],[f185,f160,f134,f98,f94,f187])).
% 0.21/0.50  fof(f94,plain,(
% 0.21/0.50    spl3_3 <=> v2_struct_0(sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.50  fof(f98,plain,(
% 0.21/0.50    spl3_4 <=> l1_struct_0(sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.50  fof(f134,plain,(
% 0.21/0.50    spl3_13 <=> ! [X0] : (v2_struct_0(X0) | ~l1_struct_0(X0) | ~v1_xboole_0(u1_struct_0(X0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.50  fof(f160,plain,(
% 0.21/0.50    spl3_17 <=> u1_struct_0(sK1) = k2_struct_0(sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.21/0.50  fof(f185,plain,(
% 0.21/0.50    ~v1_xboole_0(k2_struct_0(sK1)) | (spl3_3 | ~spl3_4 | ~spl3_13 | ~spl3_17)),
% 0.21/0.50    inference(forward_demodulation,[],[f184,f161])).
% 0.21/0.50  fof(f161,plain,(
% 0.21/0.50    u1_struct_0(sK1) = k2_struct_0(sK1) | ~spl3_17),
% 0.21/0.50    inference(avatar_component_clause,[],[f160])).
% 0.21/0.50  fof(f184,plain,(
% 0.21/0.50    ~v1_xboole_0(u1_struct_0(sK1)) | (spl3_3 | ~spl3_4 | ~spl3_13)),
% 0.21/0.50    inference(subsumption_resolution,[],[f183,f99])).
% 0.21/0.50  fof(f99,plain,(
% 0.21/0.50    l1_struct_0(sK1) | ~spl3_4),
% 0.21/0.50    inference(avatar_component_clause,[],[f98])).
% 0.21/0.50  fof(f183,plain,(
% 0.21/0.50    ~l1_struct_0(sK1) | ~v1_xboole_0(u1_struct_0(sK1)) | (spl3_3 | ~spl3_13)),
% 0.21/0.50    inference(resolution,[],[f135,f95])).
% 0.21/0.50  fof(f95,plain,(
% 0.21/0.50    ~v2_struct_0(sK1) | spl3_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f94])).
% 0.21/0.50  fof(f135,plain,(
% 0.21/0.50    ( ! [X0] : (v2_struct_0(X0) | ~l1_struct_0(X0) | ~v1_xboole_0(u1_struct_0(X0))) ) | ~spl3_13),
% 0.21/0.50    inference(avatar_component_clause,[],[f134])).
% 0.21/0.50  fof(f182,plain,(
% 0.21/0.50    ~spl3_22 | ~spl3_4 | ~spl3_5 | spl3_11 | ~spl3_12),
% 0.21/0.50    inference(avatar_split_clause,[],[f158,f130,f126,f102,f98,f180])).
% 0.21/0.50  fof(f102,plain,(
% 0.21/0.50    spl3_5 <=> l1_struct_0(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.50  fof(f126,plain,(
% 0.21/0.50    spl3_11 <=> r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.50  fof(f130,plain,(
% 0.21/0.50    spl3_12 <=> ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.50  fof(f158,plain,(
% 0.21/0.50    ~r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2) | (~spl3_4 | ~spl3_5 | spl3_11 | ~spl3_12)),
% 0.21/0.50    inference(backward_demodulation,[],[f151,f150])).
% 0.21/0.50  fof(f150,plain,(
% 0.21/0.50    u1_struct_0(sK0) = k2_struct_0(sK0) | (~spl3_5 | ~spl3_12)),
% 0.21/0.50    inference(resolution,[],[f131,f103])).
% 0.21/0.50  fof(f103,plain,(
% 0.21/0.50    l1_struct_0(sK0) | ~spl3_5),
% 0.21/0.50    inference(avatar_component_clause,[],[f102])).
% 0.21/0.50  fof(f131,plain,(
% 0.21/0.50    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) ) | ~spl3_12),
% 0.21/0.50    inference(avatar_component_clause,[],[f130])).
% 0.21/0.50  fof(f151,plain,(
% 0.21/0.50    ~r2_funct_2(u1_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2) | (~spl3_4 | spl3_11 | ~spl3_12)),
% 0.21/0.50    inference(backward_demodulation,[],[f127,f149])).
% 0.21/0.50  fof(f149,plain,(
% 0.21/0.50    u1_struct_0(sK1) = k2_struct_0(sK1) | (~spl3_4 | ~spl3_12)),
% 0.21/0.50    inference(resolution,[],[f131,f99])).
% 0.21/0.50  fof(f127,plain,(
% 0.21/0.50    ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) | spl3_11),
% 0.21/0.50    inference(avatar_component_clause,[],[f126])).
% 0.21/0.50  fof(f178,plain,(
% 0.21/0.50    spl3_21 | ~spl3_4 | ~spl3_5 | ~spl3_8 | ~spl3_12),
% 0.21/0.50    inference(avatar_split_clause,[],[f157,f130,f114,f102,f98,f176])).
% 0.21/0.50  fof(f114,plain,(
% 0.21/0.50    spl3_8 <=> k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.50  fof(f157,plain,(
% 0.21/0.50    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_4 | ~spl3_5 | ~spl3_8 | ~spl3_12)),
% 0.21/0.50    inference(backward_demodulation,[],[f152,f150])).
% 0.21/0.50  fof(f152,plain,(
% 0.21/0.50    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_4 | ~spl3_8 | ~spl3_12)),
% 0.21/0.50    inference(backward_demodulation,[],[f115,f149])).
% 0.21/0.50  fof(f115,plain,(
% 0.21/0.50    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) | ~spl3_8),
% 0.21/0.50    inference(avatar_component_clause,[],[f114])).
% 0.21/0.50  fof(f170,plain,(
% 0.21/0.50    spl3_19 | ~spl3_4 | ~spl3_5 | ~spl3_7 | ~spl3_12),
% 0.21/0.50    inference(avatar_split_clause,[],[f156,f130,f110,f102,f98,f168])).
% 0.21/0.50  fof(f110,plain,(
% 0.21/0.50    spl3_7 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.50  fof(f156,plain,(
% 0.21/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_4 | ~spl3_5 | ~spl3_7 | ~spl3_12)),
% 0.21/0.50    inference(backward_demodulation,[],[f153,f150])).
% 0.21/0.50  fof(f153,plain,(
% 0.21/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_4 | ~spl3_7 | ~spl3_12)),
% 0.21/0.50    inference(backward_demodulation,[],[f111,f149])).
% 0.21/0.50  fof(f111,plain,(
% 0.21/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl3_7),
% 0.21/0.50    inference(avatar_component_clause,[],[f110])).
% 0.21/0.50  fof(f166,plain,(
% 0.21/0.50    spl3_18 | ~spl3_4 | ~spl3_5 | ~spl3_6 | ~spl3_12),
% 0.21/0.50    inference(avatar_split_clause,[],[f155,f130,f106,f102,f98,f164])).
% 0.21/0.50  fof(f106,plain,(
% 0.21/0.50    spl3_6 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.50  fof(f155,plain,(
% 0.21/0.50    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | (~spl3_4 | ~spl3_5 | ~spl3_6 | ~spl3_12)),
% 0.21/0.50    inference(backward_demodulation,[],[f154,f150])).
% 0.21/0.50  fof(f154,plain,(
% 0.21/0.50    v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) | (~spl3_4 | ~spl3_6 | ~spl3_12)),
% 0.21/0.50    inference(backward_demodulation,[],[f107,f149])).
% 0.21/0.50  fof(f107,plain,(
% 0.21/0.50    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl3_6),
% 0.21/0.50    inference(avatar_component_clause,[],[f106])).
% 0.21/0.50  fof(f162,plain,(
% 0.21/0.50    spl3_17 | ~spl3_4 | ~spl3_12),
% 0.21/0.50    inference(avatar_split_clause,[],[f149,f130,f98,f160])).
% 0.21/0.50  fof(f148,plain,(
% 0.21/0.50    spl3_16),
% 0.21/0.50    inference(avatar_split_clause,[],[f72,f146])).
% 0.21/0.50  fof(f72,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f38])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.50  fof(f144,plain,(
% 0.21/0.50    spl3_15),
% 0.21/0.50    inference(avatar_split_clause,[],[f61,f142])).
% 0.21/0.50  fof(f61,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | v1_funct_1(k2_funct_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(flattening,[],[f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.21/0.50  fof(f140,plain,(
% 0.21/0.50    spl3_14),
% 0.21/0.50    inference(avatar_split_clause,[],[f60,f138])).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | v1_relat_1(k2_funct_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f25])).
% 0.21/0.50  fof(f136,plain,(
% 0.21/0.50    spl3_13),
% 0.21/0.50    inference(avatar_split_clause,[],[f59,f134])).
% 0.21/0.50  fof(f59,plain,(
% 0.21/0.50    ( ! [X0] : (v2_struct_0(X0) | ~l1_struct_0(X0) | ~v1_xboole_0(u1_struct_0(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,axiom,(
% 0.21/0.50    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.21/0.50  fof(f132,plain,(
% 0.21/0.50    spl3_12),
% 0.21/0.50    inference(avatar_split_clause,[],[f58,f130])).
% 0.21/0.50  fof(f58,plain,(
% 0.21/0.50    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,axiom,(
% 0.21/0.50    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.50  fof(f128,plain,(
% 0.21/0.50    ~spl3_11),
% 0.21/0.50    inference(avatar_split_clause,[],[f52,f126])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f18])).
% 0.21/0.50  fof(f18,negated_conjecture,(
% 0.21/0.50    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 0.21/0.50    inference(negated_conjecture,[],[f17])).
% 0.21/0.50  fof(f17,conjecture,(
% 0.21/0.50    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tops_2)).
% 0.21/0.50  fof(f124,plain,(
% 0.21/0.50    spl3_10),
% 0.21/0.50    inference(avatar_split_clause,[],[f57,f122])).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).
% 0.21/0.50  fof(f116,plain,(
% 0.21/0.50    spl3_8),
% 0.21/0.50    inference(avatar_split_clause,[],[f50,f114])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f112,plain,(
% 0.21/0.50    spl3_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f49,f110])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f108,plain,(
% 0.21/0.50    spl3_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f48,f106])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f104,plain,(
% 0.21/0.50    spl3_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f55,f102])).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    l1_struct_0(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f100,plain,(
% 0.21/0.50    spl3_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f54,f98])).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    l1_struct_0(sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f96,plain,(
% 0.21/0.50    ~spl3_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f53,f94])).
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    ~v2_struct_0(sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f92,plain,(
% 0.21/0.50    spl3_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f51,f90])).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    v2_funct_1(sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f88,plain,(
% 0.21/0.50    spl3_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f47,f86])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    v1_funct_1(sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (3784)------------------------------
% 0.21/0.50  % (3784)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (3784)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (3784)Memory used [KB]: 10874
% 0.21/0.50  % (3784)Time elapsed: 0.066 s
% 0.21/0.50  % (3784)------------------------------
% 0.21/0.50  % (3784)------------------------------
% 0.21/0.50  % (3771)Success in time 0.139 s
%------------------------------------------------------------------------------
