%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:02 EST 2020

% Result     : Theorem 1.46s
% Output     : Refutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :  260 ( 570 expanded)
%              Number of leaves         :   59 ( 225 expanded)
%              Depth                    :    9
%              Number of atoms          :  943 (2628 expanded)
%              Number of equality atoms :  199 ( 754 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f990,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f93,f102,f106,f110,f136,f138,f149,f154,f156,f183,f217,f219,f275,f282,f308,f329,f331,f333,f359,f460,f467,f479,f497,f502,f540,f555,f675,f683,f708,f753,f772,f777,f782,f789,f866,f876,f916,f924,f929,f940,f946,f950,f967,f989])).

fof(f989,plain,
    ( ~ spl4_22
    | ~ spl4_81 ),
    inference(avatar_contradiction_clause,[],[f984])).

fof(f984,plain,
    ( $false
    | ~ spl4_22
    | ~ spl4_81 ),
    inference(subsumption_resolution,[],[f46,f969])).

fof(f969,plain,
    ( sK3 = k2_funct_1(sK2)
    | ~ spl4_22
    | ~ spl4_81 ),
    inference(forward_demodulation,[],[f740,f295])).

fof(f295,plain,
    ( sK2 = k2_funct_1(sK3)
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f293])).

fof(f293,plain,
    ( spl4_22
  <=> sK2 = k2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f740,plain,
    ( sK3 = k2_funct_1(k2_funct_1(sK3))
    | ~ spl4_81 ),
    inference(avatar_component_clause,[],[f738])).

fof(f738,plain,
    ( spl4_81
  <=> sK3 = k2_funct_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_81])])).

fof(f46,plain,(
    sK3 != k2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
           => ( ( v2_funct_1(X2)
                & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
                & k2_relset_1(X0,X1,X2) = X1 )
             => ( k2_funct_1(X2) = X3
                | k1_xboole_0 = X1
                | k1_xboole_0 = X0 ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( ( v2_funct_1(X2)
              & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
              & k2_relset_1(X0,X1,X2) = X1 )
           => ( k2_funct_1(X2) = X3
              | k1_xboole_0 = X1
              | k1_xboole_0 = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).

fof(f967,plain,
    ( ~ spl4_22
    | spl4_84
    | ~ spl4_88 ),
    inference(avatar_contradiction_clause,[],[f966])).

fof(f966,plain,
    ( $false
    | ~ spl4_22
    | spl4_84
    | ~ spl4_88 ),
    inference(subsumption_resolution,[],[f808,f952])).

fof(f952,plain,
    ( sK0 != k1_relat_1(sK2)
    | ~ spl4_22
    | spl4_84 ),
    inference(forward_demodulation,[],[f752,f295])).

fof(f752,plain,
    ( sK0 != k1_relat_1(k2_funct_1(sK3))
    | spl4_84 ),
    inference(avatar_component_clause,[],[f750])).

fof(f750,plain,
    ( spl4_84
  <=> sK0 = k1_relat_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_84])])).

fof(f808,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl4_88 ),
    inference(forward_demodulation,[],[f794,f75])).

fof(f75,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f55,f51])).

fof(f51,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f55,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f794,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k6_partfun1(sK0))
    | ~ spl4_88 ),
    inference(superposition,[],[f75,f788])).

fof(f788,plain,
    ( k6_partfun1(sK0) = k6_partfun1(k1_relat_1(sK2))
    | ~ spl4_88 ),
    inference(avatar_component_clause,[],[f786])).

fof(f786,plain,
    ( spl4_88
  <=> k6_partfun1(sK0) = k6_partfun1(k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_88])])).

fof(f950,plain,
    ( ~ spl4_6
    | ~ spl4_22
    | spl4_83 ),
    inference(avatar_contradiction_clause,[],[f949])).

fof(f949,plain,
    ( $false
    | ~ spl4_6
    | ~ spl4_22
    | spl4_83 ),
    inference(trivial_inequality_removal,[],[f948])).

fof(f948,plain,
    ( k6_partfun1(sK1) != k6_partfun1(sK1)
    | ~ spl4_6
    | ~ spl4_22
    | spl4_83 ),
    inference(forward_demodulation,[],[f947,f134])).

fof(f134,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl4_6
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f947,plain,
    ( k6_partfun1(k2_relat_1(sK2)) != k6_partfun1(sK1)
    | ~ spl4_22
    | spl4_83 ),
    inference(forward_demodulation,[],[f748,f295])).

fof(f748,plain,
    ( k6_partfun1(sK1) != k6_partfun1(k2_relat_1(k2_funct_1(sK3)))
    | spl4_83 ),
    inference(avatar_component_clause,[],[f746])).

fof(f746,plain,
    ( spl4_83
  <=> k6_partfun1(sK1) = k6_partfun1(k2_relat_1(k2_funct_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_83])])).

fof(f946,plain,
    ( ~ spl4_22
    | spl4_82 ),
    inference(avatar_contradiction_clause,[],[f945])).

fof(f945,plain,
    ( $false
    | ~ spl4_22
    | spl4_82 ),
    inference(subsumption_resolution,[],[f43,f943])).

fof(f943,plain,
    ( ~ v2_funct_1(sK2)
    | ~ spl4_22
    | spl4_82 ),
    inference(forward_demodulation,[],[f744,f295])).

fof(f744,plain,
    ( ~ v2_funct_1(k2_funct_1(sK3))
    | spl4_82 ),
    inference(avatar_component_clause,[],[f742])).

fof(f742,plain,
    ( spl4_82
  <=> v2_funct_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_82])])).

fof(f43,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f940,plain,
    ( ~ spl4_22
    | spl4_78 ),
    inference(avatar_contradiction_clause,[],[f938])).

fof(f938,plain,
    ( $false
    | ~ spl4_22
    | spl4_78 ),
    inference(unit_resulting_resolution,[],[f60,f49,f932,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f932,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl4_22
    | spl4_78 ),
    inference(forward_demodulation,[],[f725,f295])).

fof(f725,plain,
    ( ~ v1_relat_1(k2_funct_1(sK3))
    | spl4_78 ),
    inference(avatar_component_clause,[],[f723])).

fof(f723,plain,
    ( spl4_78
  <=> v1_relat_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_78])])).

fof(f49,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f19])).

fof(f60,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f929,plain,
    ( ~ spl4_22
    | spl4_77 ),
    inference(avatar_contradiction_clause,[],[f928])).

fof(f928,plain,
    ( $false
    | ~ spl4_22
    | spl4_77 ),
    inference(subsumption_resolution,[],[f47,f926])).

fof(f926,plain,
    ( ~ v1_funct_1(sK2)
    | ~ spl4_22
    | spl4_77 ),
    inference(superposition,[],[f721,f295])).

fof(f721,plain,
    ( ~ v1_funct_1(k2_funct_1(sK3))
    | spl4_77 ),
    inference(avatar_component_clause,[],[f719])).

fof(f719,plain,
    ( spl4_77
  <=> v1_funct_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_77])])).

fof(f47,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f924,plain,
    ( spl4_24
    | ~ spl4_45 ),
    inference(avatar_contradiction_clause,[],[f923])).

fof(f923,plain,
    ( $false
    | spl4_24
    | ~ spl4_45 ),
    inference(trivial_inequality_removal,[],[f922])).

fof(f922,plain,
    ( k6_partfun1(sK0) != k6_partfun1(sK0)
    | spl4_24
    | ~ spl4_45 ),
    inference(forward_demodulation,[],[f303,f477])).

fof(f477,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ spl4_45 ),
    inference(avatar_component_clause,[],[f475])).

fof(f475,plain,
    ( spl4_45
  <=> sK0 = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).

fof(f303,plain,
    ( k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3))
    | spl4_24 ),
    inference(avatar_component_clause,[],[f301])).

fof(f301,plain,
    ( spl4_24
  <=> k6_partfun1(sK0) = k6_partfun1(k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f916,plain,
    ( spl4_25
    | ~ spl4_94 ),
    inference(avatar_contradiction_clause,[],[f906])).

fof(f906,plain,
    ( $false
    | spl4_25
    | ~ spl4_94 ),
    inference(subsumption_resolution,[],[f307,f895])).

fof(f895,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl4_94 ),
    inference(forward_demodulation,[],[f881,f75])).

fof(f881,plain,
    ( k1_relat_1(sK3) = k2_relat_1(k6_partfun1(sK1))
    | ~ spl4_94 ),
    inference(superposition,[],[f75,f875])).

fof(f875,plain,
    ( k6_partfun1(sK1) = k6_partfun1(k1_relat_1(sK3))
    | ~ spl4_94 ),
    inference(avatar_component_clause,[],[f873])).

fof(f873,plain,
    ( spl4_94
  <=> k6_partfun1(sK1) = k6_partfun1(k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_94])])).

fof(f307,plain,
    ( sK1 != k1_relat_1(sK3)
    | spl4_25 ),
    inference(avatar_component_clause,[],[f305])).

fof(f305,plain,
    ( spl4_25
  <=> sK1 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f876,plain,
    ( ~ spl4_49
    | spl4_94
    | ~ spl4_48
    | ~ spl4_93 ),
    inference(avatar_split_clause,[],[f871,f864,f494,f873,f499])).

fof(f499,plain,
    ( spl4_49
  <=> v1_funct_2(sK3,k1_relat_1(sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).

fof(f494,plain,
    ( spl4_48
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).

fof(f864,plain,
    ( spl4_93
  <=> ! [X0] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
        | k6_partfun1(X0) = k6_partfun1(sK1)
        | ~ v1_funct_2(sK3,X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_93])])).

fof(f871,plain,
    ( k6_partfun1(sK1) = k6_partfun1(k1_relat_1(sK3))
    | ~ v1_funct_2(sK3,k1_relat_1(sK3),sK0)
    | ~ spl4_48
    | ~ spl4_93 ),
    inference(resolution,[],[f865,f496])).

fof(f496,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK0)))
    | ~ spl4_48 ),
    inference(avatar_component_clause,[],[f494])).

fof(f865,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
        | k6_partfun1(X0) = k6_partfun1(sK1)
        | ~ v1_funct_2(sK3,X0,sK0) )
    | ~ spl4_93 ),
    inference(avatar_component_clause,[],[f864])).

fof(f866,plain,
    ( spl4_93
    | spl4_53
    | ~ spl4_86 ),
    inference(avatar_split_clause,[],[f862,f775,f537,f864])).

fof(f537,plain,
    ( spl4_53
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_53])])).

fof(f775,plain,
    ( spl4_86
  <=> ! [X5,X6] :
        ( k6_partfun1(sK1) = k6_partfun1(X6)
        | k1_xboole_0 = X5
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X6,X5)))
        | ~ v1_funct_2(sK3,X6,X5)
        | sK0 != X5 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_86])])).

fof(f862,plain,
    ( ! [X0] :
        ( k1_xboole_0 = sK0
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
        | ~ v1_funct_2(sK3,X0,sK0)
        | k6_partfun1(X0) = k6_partfun1(sK1) )
    | ~ spl4_86 ),
    inference(equality_resolution,[],[f776])).

fof(f776,plain,
    ( ! [X6,X5] :
        ( sK0 != X5
        | k1_xboole_0 = X5
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X6,X5)))
        | ~ v1_funct_2(sK3,X6,X5)
        | k6_partfun1(sK1) = k6_partfun1(X6) )
    | ~ spl4_86 ),
    inference(avatar_component_clause,[],[f775])).

fof(f789,plain,
    ( ~ spl4_9
    | spl4_88
    | ~ spl4_8
    | ~ spl4_87 ),
    inference(avatar_split_clause,[],[f784,f780,f146,f786,f151])).

fof(f151,plain,
    ( spl4_9
  <=> v1_funct_2(sK2,k1_relat_1(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f146,plain,
    ( spl4_8
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f780,plain,
    ( spl4_87
  <=> ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
        | k6_partfun1(X0) = k6_partfun1(sK0)
        | ~ v1_funct_2(sK2,X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_87])])).

fof(f784,plain,
    ( k6_partfun1(sK0) = k6_partfun1(k1_relat_1(sK2))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),sK1)
    | ~ spl4_8
    | ~ spl4_87 ),
    inference(resolution,[],[f781,f148])).

fof(f148,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f146])).

fof(f781,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
        | k6_partfun1(X0) = k6_partfun1(sK0)
        | ~ v1_funct_2(sK2,X0,sK1) )
    | ~ spl4_87 ),
    inference(avatar_component_clause,[],[f780])).

fof(f782,plain,
    ( spl4_87
    | spl4_27
    | ~ spl4_85 ),
    inference(avatar_split_clause,[],[f778,f770,f318,f780])).

fof(f318,plain,
    ( spl4_27
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f770,plain,
    ( spl4_85
  <=> ! [X3,X4] :
        ( k6_partfun1(sK0) = k6_partfun1(X4)
        | k1_xboole_0 = X3
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X4,X3)))
        | ~ v1_funct_2(sK2,X4,X3)
        | sK1 != X3 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_85])])).

fof(f778,plain,
    ( ! [X0] :
        ( k1_xboole_0 = sK1
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
        | ~ v1_funct_2(sK2,X0,sK1)
        | k6_partfun1(X0) = k6_partfun1(sK0) )
    | ~ spl4_85 ),
    inference(equality_resolution,[],[f771])).

fof(f771,plain,
    ( ! [X4,X3] :
        ( sK1 != X3
        | k1_xboole_0 = X3
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X4,X3)))
        | ~ v1_funct_2(sK2,X4,X3)
        | k6_partfun1(sK0) = k6_partfun1(X4) )
    | ~ spl4_85 ),
    inference(avatar_component_clause,[],[f770])).

fof(f777,plain,
    ( ~ spl4_23
    | ~ spl4_13
    | spl4_86
    | ~ spl4_45
    | ~ spl4_52 ),
    inference(avatar_split_clause,[],[f773,f533,f475,f775,f203,f297])).

fof(f297,plain,
    ( spl4_23
  <=> v2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f203,plain,
    ( spl4_13
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f533,plain,
    ( spl4_52
  <=> k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).

fof(f773,plain,
    ( ! [X6,X5] :
        ( k6_partfun1(sK1) = k6_partfun1(X6)
        | sK0 != X5
        | ~ v1_funct_2(sK3,X6,X5)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X6,X5)))
        | ~ v1_funct_1(sK3)
        | ~ v2_funct_1(sK3)
        | k1_xboole_0 = X5 )
    | ~ spl4_45
    | ~ spl4_52 ),
    inference(forward_demodulation,[],[f766,f535])).

fof(f535,plain,
    ( k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ spl4_52 ),
    inference(avatar_component_clause,[],[f533])).

fof(f766,plain,
    ( ! [X6,X5] :
        ( sK0 != X5
        | ~ v1_funct_2(sK3,X6,X5)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X6,X5)))
        | ~ v1_funct_1(sK3)
        | ~ v2_funct_1(sK3)
        | k1_xboole_0 = X5
        | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(X6) )
    | ~ spl4_45 ),
    inference(superposition,[],[f311,f477])).

fof(f311,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) != X1
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k1_xboole_0 = X1
      | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) ) ),
    inference(duplicate_literal_removal,[],[f310])).

fof(f310,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) != X1
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k1_xboole_0 = X1
      | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f62,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k1_xboole_0 = X1
      | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
            & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).

fof(f772,plain,
    ( ~ spl4_28
    | ~ spl4_7
    | spl4_85
    | ~ spl4_6
    | ~ spl4_26 ),
    inference(avatar_split_clause,[],[f768,f314,f132,f770,f142,f322])).

fof(f322,plain,
    ( spl4_28
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f142,plain,
    ( spl4_7
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f314,plain,
    ( spl4_26
  <=> k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f768,plain,
    ( ! [X4,X3] :
        ( k6_partfun1(sK0) = k6_partfun1(X4)
        | sK1 != X3
        | ~ v1_funct_2(sK2,X4,X3)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X4,X3)))
        | ~ v1_funct_1(sK2)
        | ~ v2_funct_1(sK2)
        | k1_xboole_0 = X3 )
    | ~ spl4_6
    | ~ spl4_26 ),
    inference(forward_demodulation,[],[f765,f316])).

fof(f316,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f314])).

fof(f765,plain,
    ( ! [X4,X3] :
        ( sK1 != X3
        | ~ v1_funct_2(sK2,X4,X3)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X4,X3)))
        | ~ v1_funct_1(sK2)
        | ~ v2_funct_1(sK2)
        | k1_xboole_0 = X3
        | k6_partfun1(X4) = k5_relat_1(sK2,k2_funct_1(sK2)) )
    | ~ spl4_6 ),
    inference(superposition,[],[f311,f134])).

fof(f753,plain,
    ( spl4_81
    | ~ spl4_78
    | ~ spl4_82
    | ~ spl4_13
    | ~ spl4_1
    | ~ spl4_77
    | ~ spl4_83
    | ~ spl4_84
    | ~ spl4_45
    | ~ spl4_52 ),
    inference(avatar_split_clause,[],[f736,f533,f475,f750,f746,f719,f86,f203,f742,f723,f738])).

fof(f86,plain,
    ( spl4_1
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f736,plain,
    ( sK0 != k1_relat_1(k2_funct_1(sK3))
    | k6_partfun1(sK1) != k6_partfun1(k2_relat_1(k2_funct_1(sK3)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | sK3 = k2_funct_1(k2_funct_1(sK3))
    | ~ spl4_45
    | ~ spl4_52 ),
    inference(forward_demodulation,[],[f717,f477])).

fof(f717,plain,
    ( k6_partfun1(sK1) != k6_partfun1(k2_relat_1(k2_funct_1(sK3)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(k2_funct_1(sK3))
    | k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | sK3 = k2_funct_1(k2_funct_1(sK3))
    | ~ spl4_52 ),
    inference(superposition,[],[f77,f535])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X0)
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v1_relat_1(X0)
      | k2_funct_1(X0) = X1 ) ),
    inference(definition_unfolding,[],[f59,f51])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X0)
      | k2_relat_1(X1) != k1_relat_1(X0)
      | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
      | k2_funct_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0))
              & k2_relat_1(X1) = k1_relat_1(X0)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).

fof(f708,plain,(
    ~ spl4_53 ),
    inference(avatar_contradiction_clause,[],[f684])).

fof(f684,plain,
    ( $false
    | ~ spl4_53 ),
    inference(subsumption_resolution,[],[f44,f539])).

fof(f539,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_53 ),
    inference(avatar_component_clause,[],[f537])).

fof(f44,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f19])).

fof(f683,plain,(
    spl4_75 ),
    inference(avatar_contradiction_clause,[],[f680])).

fof(f680,plain,
    ( $false
    | spl4_75 ),
    inference(unit_resulting_resolution,[],[f74,f674])).

fof(f674,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | spl4_75 ),
    inference(avatar_component_clause,[],[f672])).

fof(f672,plain,
    ( spl4_75
  <=> v2_funct_1(k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_75])])).

fof(f74,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f50,f51])).

fof(f50,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_funct_1)).

fof(f675,plain,
    ( ~ spl4_43
    | ~ spl4_12
    | ~ spl4_13
    | spl4_53
    | spl4_23
    | ~ spl4_75
    | ~ spl4_11
    | ~ spl4_55 ),
    inference(avatar_split_clause,[],[f668,f553,f180,f672,f297,f537,f203,f199,f457])).

fof(f457,plain,
    ( spl4_43
  <=> v1_funct_2(sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).

fof(f199,plain,
    ( spl4_12
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f180,plain,
    ( spl4_11
  <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f553,plain,
    ( spl4_55
  <=> ! [X1,X0] :
        ( ~ v1_funct_1(X0)
        | v2_funct_1(X0)
        | k1_xboole_0 = X1
        | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
        | ~ v1_funct_2(X0,sK1,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_55])])).

fof(f668,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | v2_funct_1(sK3)
    | k1_xboole_0 = sK0
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ spl4_11
    | ~ spl4_55 ),
    inference(superposition,[],[f554,f182])).

fof(f182,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f180])).

fof(f554,plain,
    ( ! [X0,X1] :
        ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0))
        | v2_funct_1(X0)
        | k1_xboole_0 = X1
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
        | ~ v1_funct_2(X0,sK1,X1) )
    | ~ spl4_55 ),
    inference(avatar_component_clause,[],[f553])).

fof(f555,plain,
    ( ~ spl4_7
    | spl4_55
    | ~ spl4_5
    | ~ spl4_29 ),
    inference(avatar_split_clause,[],[f551,f326,f128,f553,f142])).

fof(f128,plain,
    ( spl4_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f326,plain,
    ( spl4_29
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f551,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(sK2,sK0,sK1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,sK1,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
      | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0))
      | ~ v1_funct_1(sK2)
      | k1_xboole_0 = X1
      | v2_funct_1(X0) ) ),
    inference(trivial_inequality_removal,[],[f546])).

fof(f546,plain,(
    ! [X0,X1] :
      ( sK1 != sK1
      | ~ v1_funct_2(sK2,sK0,sK1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,sK1,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
      | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0))
      | ~ v1_funct_1(sK2)
      | k1_xboole_0 = X1
      | v2_funct_1(X0) ) ),
    inference(superposition,[],[f68,f41])).

fof(f41,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f68,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X3) != X1
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X1,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | ~ v1_funct_1(X3)
      | k1_xboole_0 = X2
      | v2_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( v2_funct_1(X4)
            & v2_funct_1(X3) )
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | k2_relset_1(X0,X1,X3) != X1
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( v2_funct_1(X4)
            & v2_funct_1(X3) )
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | k2_relset_1(X0,X1,X3) != X1
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( ( k2_relset_1(X0,X1,X3) = X1
              & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) )
           => ( ( v2_funct_1(X4)
                & v2_funct_1(X3) )
              | ( k1_xboole_0 != X1
                & k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_funct_2)).

fof(f540,plain,
    ( spl4_52
    | spl4_53
    | ~ spl4_23
    | ~ spl4_13
    | ~ spl4_12
    | ~ spl4_43
    | ~ spl4_42 ),
    inference(avatar_split_clause,[],[f472,f453,f457,f199,f203,f297,f537,f533])).

fof(f453,plain,
    ( spl4_42
  <=> sK0 = k2_relset_1(sK1,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).

fof(f472,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | k1_xboole_0 = sK0
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ spl4_42 ),
    inference(trivial_inequality_removal,[],[f470])).

fof(f470,plain,
    ( sK0 != sK0
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | k1_xboole_0 = sK0
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ spl4_42 ),
    inference(superposition,[],[f62,f455])).

fof(f455,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ spl4_42 ),
    inference(avatar_component_clause,[],[f453])).

fof(f502,plain,
    ( ~ spl4_1
    | ~ spl4_13
    | spl4_49
    | ~ spl4_45 ),
    inference(avatar_split_clause,[],[f483,f475,f499,f203,f86])).

fof(f483,plain,
    ( v1_funct_2(sK3,k1_relat_1(sK3),sK0)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_45 ),
    inference(superposition,[],[f57,f477])).

fof(f57,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(f497,plain,
    ( ~ spl4_1
    | ~ spl4_13
    | spl4_48
    | ~ spl4_45 ),
    inference(avatar_split_clause,[],[f482,f475,f494,f203,f86])).

fof(f482,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK0)))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_45 ),
    inference(superposition,[],[f58,f477])).

fof(f58,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f479,plain,
    ( ~ spl4_12
    | spl4_45
    | ~ spl4_42 ),
    inference(avatar_split_clause,[],[f471,f453,f475,f199])).

fof(f471,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_42 ),
    inference(superposition,[],[f61,f455])).

fof(f467,plain,(
    spl4_43 ),
    inference(avatar_contradiction_clause,[],[f466])).

fof(f466,plain,
    ( $false
    | spl4_43 ),
    inference(subsumption_resolution,[],[f39,f459])).

fof(f459,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | spl4_43 ),
    inference(avatar_component_clause,[],[f457])).

fof(f39,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f460,plain,
    ( spl4_42
    | ~ spl4_13
    | ~ spl4_5
    | ~ spl4_29
    | ~ spl4_7
    | ~ spl4_12
    | ~ spl4_43 ),
    inference(avatar_split_clause,[],[f448,f457,f199,f142,f326,f128,f203,f453])).

fof(f448,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | sK0 = k2_relset_1(sK1,sK0,sK3) ),
    inference(resolution,[],[f64,f42])).

fof(f42,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X1,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_1(X2)
      | k2_relset_1(X0,X1,X2) = X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
           => k2_relset_1(X0,X1,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).

fof(f359,plain,(
    ~ spl4_27 ),
    inference(avatar_contradiction_clause,[],[f343])).

fof(f343,plain,
    ( $false
    | ~ spl4_27 ),
    inference(subsumption_resolution,[],[f45,f320])).

fof(f320,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_27 ),
    inference(avatar_component_clause,[],[f318])).

fof(f45,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f19])).

fof(f333,plain,(
    spl4_29 ),
    inference(avatar_contradiction_clause,[],[f332])).

fof(f332,plain,
    ( $false
    | spl4_29 ),
    inference(subsumption_resolution,[],[f48,f328])).

fof(f328,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | spl4_29 ),
    inference(avatar_component_clause,[],[f326])).

fof(f48,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f331,plain,(
    spl4_28 ),
    inference(avatar_contradiction_clause,[],[f330])).

fof(f330,plain,
    ( $false
    | spl4_28 ),
    inference(subsumption_resolution,[],[f43,f324])).

fof(f324,plain,
    ( ~ v2_funct_1(sK2)
    | spl4_28 ),
    inference(avatar_component_clause,[],[f322])).

fof(f329,plain,
    ( spl4_26
    | spl4_27
    | ~ spl4_28
    | ~ spl4_7
    | ~ spl4_5
    | ~ spl4_29 ),
    inference(avatar_split_clause,[],[f312,f326,f128,f142,f322,f318,f314])).

fof(f312,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k1_xboole_0 = sK1
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(trivial_inequality_removal,[],[f309])).

fof(f309,plain,
    ( sK1 != sK1
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k1_xboole_0 = sK1
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(superposition,[],[f62,f41])).

fof(f308,plain,
    ( spl4_22
    | ~ spl4_1
    | ~ spl4_23
    | ~ spl4_7
    | ~ spl4_3
    | ~ spl4_13
    | ~ spl4_24
    | ~ spl4_25
    | ~ spl4_6
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f291,f226,f132,f305,f301,f203,f95,f142,f297,f86,f293])).

fof(f95,plain,
    ( spl4_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f226,plain,
    ( spl4_16
  <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f291,plain,
    ( sK1 != k1_relat_1(sK3)
    | k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | sK2 = k2_funct_1(sK3)
    | ~ spl4_6
    | ~ spl4_16 ),
    inference(forward_demodulation,[],[f290,f134])).

fof(f290,plain,
    ( k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | sK2 = k2_funct_1(sK3)
    | ~ spl4_16 ),
    inference(superposition,[],[f77,f228])).

fof(f228,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f226])).

fof(f282,plain,
    ( ~ spl4_7
    | ~ spl4_12
    | ~ spl4_13
    | ~ spl4_5
    | spl4_16
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f279,f180,f226,f128,f203,f199,f142])).

fof(f279,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_11 ),
    inference(superposition,[],[f71,f182])).

fof(f71,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f275,plain,(
    spl4_10 ),
    inference(avatar_contradiction_clause,[],[f262])).

fof(f262,plain,
    ( $false
    | spl4_10 ),
    inference(unit_resulting_resolution,[],[f47,f38,f40,f49,f178,f73])).

fof(f73,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f178,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl4_10 ),
    inference(avatar_component_clause,[],[f176])).

fof(f176,plain,
    ( spl4_10
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f40,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f38,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f219,plain,(
    spl4_13 ),
    inference(avatar_contradiction_clause,[],[f218])).

fof(f218,plain,
    ( $false
    | spl4_13 ),
    inference(subsumption_resolution,[],[f38,f205])).

fof(f205,plain,
    ( ~ v1_funct_1(sK3)
    | spl4_13 ),
    inference(avatar_component_clause,[],[f203])).

fof(f217,plain,(
    spl4_12 ),
    inference(avatar_contradiction_clause,[],[f216])).

fof(f216,plain,
    ( $false
    | spl4_12 ),
    inference(subsumption_resolution,[],[f40,f201])).

fof(f201,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl4_12 ),
    inference(avatar_component_clause,[],[f199])).

fof(f183,plain,
    ( ~ spl4_10
    | spl4_11 ),
    inference(avatar_split_clause,[],[f174,f180,f176])).

fof(f174,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f160,f42])).

fof(f160,plain,(
    ! [X2,X3] :
      ( ~ r2_relset_1(X3,X3,X2,k6_partfun1(X3))
      | k6_partfun1(X3) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X3))) ) ),
    inference(resolution,[],[f70,f53])).

fof(f53,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f156,plain,(
    spl4_7 ),
    inference(avatar_contradiction_clause,[],[f155])).

fof(f155,plain,
    ( $false
    | spl4_7 ),
    inference(subsumption_resolution,[],[f47,f144])).

fof(f144,plain,
    ( ~ v1_funct_1(sK2)
    | spl4_7 ),
    inference(avatar_component_clause,[],[f142])).

fof(f154,plain,
    ( ~ spl4_3
    | ~ spl4_7
    | spl4_9
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f140,f132,f151,f142,f95])).

fof(f140,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_6 ),
    inference(superposition,[],[f57,f134])).

fof(f149,plain,
    ( ~ spl4_3
    | ~ spl4_7
    | spl4_8
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f139,f132,f146,f142,f95])).

fof(f139,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_6 ),
    inference(superposition,[],[f58,f134])).

fof(f138,plain,(
    spl4_5 ),
    inference(avatar_contradiction_clause,[],[f137])).

fof(f137,plain,
    ( $false
    | spl4_5 ),
    inference(subsumption_resolution,[],[f49,f130])).

fof(f130,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl4_5 ),
    inference(avatar_component_clause,[],[f128])).

fof(f136,plain,
    ( ~ spl4_5
    | spl4_6 ),
    inference(avatar_split_clause,[],[f126,f132,f128])).

fof(f126,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f41,f61])).

fof(f110,plain,(
    spl4_4 ),
    inference(avatar_contradiction_clause,[],[f107])).

fof(f107,plain,
    ( $false
    | spl4_4 ),
    inference(unit_resulting_resolution,[],[f60,f101])).

fof(f101,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl4_4 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl4_4
  <=> v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f106,plain,(
    spl4_2 ),
    inference(avatar_contradiction_clause,[],[f103])).

fof(f103,plain,
    ( $false
    | spl4_2 ),
    inference(unit_resulting_resolution,[],[f60,f92])).

fof(f92,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl4_2
  <=> v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f102,plain,
    ( spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f83,f99,f95])).

fof(f83,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK2) ),
    inference(resolution,[],[f56,f49])).

fof(f93,plain,
    ( spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f82,f90,f86])).

fof(f82,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK3) ),
    inference(resolution,[],[f56,f40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:45:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (28631)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.51  % (28627)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.52  % (28638)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.52  % (28646)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.52  % (28641)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.30/0.53  % (28637)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.30/0.53  % (28628)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.30/0.53  % (28647)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.30/0.54  % (28633)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.30/0.54  % (28630)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.30/0.54  % (28632)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.30/0.54  % (28635)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.30/0.54  % (28653)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.30/0.54  % (28645)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.30/0.54  % (28656)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.30/0.54  % (28648)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.46/0.55  % (28639)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.46/0.55  % (28640)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.46/0.55  % (28629)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.46/0.55  % (28652)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.46/0.55  % (28634)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.46/0.56  % (28644)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.46/0.57  % (28654)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.46/0.57  % (28651)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.46/0.57  % (28655)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.46/0.57  % (28636)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.46/0.57  % (28642)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.46/0.58  % (28650)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.46/0.59  % (28643)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.46/0.59  % (28643)Refutation not found, incomplete strategy% (28643)------------------------------
% 1.46/0.59  % (28643)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.59  % (28643)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.59  
% 1.46/0.59  % (28643)Memory used [KB]: 10746
% 1.46/0.59  % (28643)Time elapsed: 0.182 s
% 1.46/0.59  % (28643)------------------------------
% 1.46/0.59  % (28643)------------------------------
% 1.46/0.59  % (28649)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.46/0.62  % (28640)Refutation found. Thanks to Tanya!
% 1.46/0.62  % SZS status Theorem for theBenchmark
% 2.02/0.63  % SZS output start Proof for theBenchmark
% 2.02/0.63  fof(f990,plain,(
% 2.02/0.63    $false),
% 2.02/0.63    inference(avatar_sat_refutation,[],[f93,f102,f106,f110,f136,f138,f149,f154,f156,f183,f217,f219,f275,f282,f308,f329,f331,f333,f359,f460,f467,f479,f497,f502,f540,f555,f675,f683,f708,f753,f772,f777,f782,f789,f866,f876,f916,f924,f929,f940,f946,f950,f967,f989])).
% 2.02/0.63  fof(f989,plain,(
% 2.02/0.63    ~spl4_22 | ~spl4_81),
% 2.02/0.63    inference(avatar_contradiction_clause,[],[f984])).
% 2.02/0.63  fof(f984,plain,(
% 2.02/0.63    $false | (~spl4_22 | ~spl4_81)),
% 2.02/0.63    inference(subsumption_resolution,[],[f46,f969])).
% 2.02/0.63  fof(f969,plain,(
% 2.02/0.63    sK3 = k2_funct_1(sK2) | (~spl4_22 | ~spl4_81)),
% 2.02/0.63    inference(forward_demodulation,[],[f740,f295])).
% 2.02/0.63  fof(f295,plain,(
% 2.02/0.63    sK2 = k2_funct_1(sK3) | ~spl4_22),
% 2.02/0.63    inference(avatar_component_clause,[],[f293])).
% 2.02/0.63  fof(f293,plain,(
% 2.02/0.63    spl4_22 <=> sK2 = k2_funct_1(sK3)),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 2.02/0.63  fof(f740,plain,(
% 2.02/0.63    sK3 = k2_funct_1(k2_funct_1(sK3)) | ~spl4_81),
% 2.02/0.63    inference(avatar_component_clause,[],[f738])).
% 2.02/0.63  fof(f738,plain,(
% 2.02/0.63    spl4_81 <=> sK3 = k2_funct_1(k2_funct_1(sK3))),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_81])])).
% 2.02/0.63  fof(f46,plain,(
% 2.02/0.63    sK3 != k2_funct_1(sK2)),
% 2.02/0.63    inference(cnf_transformation,[],[f19])).
% 2.02/0.63  fof(f19,plain,(
% 2.02/0.63    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.02/0.63    inference(flattening,[],[f18])).
% 2.02/0.63  fof(f18,plain,(
% 2.02/0.63    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.02/0.63    inference(ennf_transformation,[],[f17])).
% 2.02/0.63  fof(f17,negated_conjecture,(
% 2.02/0.63    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.02/0.63    inference(negated_conjecture,[],[f16])).
% 2.02/0.63  fof(f16,conjecture,(
% 2.02/0.63    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.02/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).
% 2.02/0.63  fof(f967,plain,(
% 2.02/0.63    ~spl4_22 | spl4_84 | ~spl4_88),
% 2.02/0.63    inference(avatar_contradiction_clause,[],[f966])).
% 2.02/0.63  fof(f966,plain,(
% 2.02/0.63    $false | (~spl4_22 | spl4_84 | ~spl4_88)),
% 2.02/0.63    inference(subsumption_resolution,[],[f808,f952])).
% 2.02/0.63  fof(f952,plain,(
% 2.02/0.63    sK0 != k1_relat_1(sK2) | (~spl4_22 | spl4_84)),
% 2.02/0.63    inference(forward_demodulation,[],[f752,f295])).
% 2.02/0.63  fof(f752,plain,(
% 2.02/0.63    sK0 != k1_relat_1(k2_funct_1(sK3)) | spl4_84),
% 2.02/0.63    inference(avatar_component_clause,[],[f750])).
% 2.02/0.63  fof(f750,plain,(
% 2.02/0.63    spl4_84 <=> sK0 = k1_relat_1(k2_funct_1(sK3))),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_84])])).
% 2.02/0.63  fof(f808,plain,(
% 2.02/0.63    sK0 = k1_relat_1(sK2) | ~spl4_88),
% 2.02/0.63    inference(forward_demodulation,[],[f794,f75])).
% 2.02/0.63  fof(f75,plain,(
% 2.02/0.63    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 2.02/0.63    inference(definition_unfolding,[],[f55,f51])).
% 2.02/0.63  fof(f51,plain,(
% 2.02/0.63    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.02/0.63    inference(cnf_transformation,[],[f11])).
% 2.02/0.63  fof(f11,axiom,(
% 2.02/0.63    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.02/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 2.02/0.63  fof(f55,plain,(
% 2.02/0.63    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 2.02/0.63    inference(cnf_transformation,[],[f3])).
% 2.02/0.63  fof(f3,axiom,(
% 2.02/0.63    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 2.02/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 2.02/0.63  fof(f794,plain,(
% 2.02/0.63    k1_relat_1(sK2) = k2_relat_1(k6_partfun1(sK0)) | ~spl4_88),
% 2.02/0.63    inference(superposition,[],[f75,f788])).
% 2.02/0.63  fof(f788,plain,(
% 2.02/0.63    k6_partfun1(sK0) = k6_partfun1(k1_relat_1(sK2)) | ~spl4_88),
% 2.02/0.63    inference(avatar_component_clause,[],[f786])).
% 2.02/0.63  fof(f786,plain,(
% 2.02/0.63    spl4_88 <=> k6_partfun1(sK0) = k6_partfun1(k1_relat_1(sK2))),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_88])])).
% 2.02/0.63  fof(f950,plain,(
% 2.02/0.63    ~spl4_6 | ~spl4_22 | spl4_83),
% 2.02/0.63    inference(avatar_contradiction_clause,[],[f949])).
% 2.02/0.63  fof(f949,plain,(
% 2.02/0.63    $false | (~spl4_6 | ~spl4_22 | spl4_83)),
% 2.02/0.63    inference(trivial_inequality_removal,[],[f948])).
% 2.02/0.63  fof(f948,plain,(
% 2.02/0.63    k6_partfun1(sK1) != k6_partfun1(sK1) | (~spl4_6 | ~spl4_22 | spl4_83)),
% 2.02/0.63    inference(forward_demodulation,[],[f947,f134])).
% 2.02/0.63  fof(f134,plain,(
% 2.02/0.63    sK1 = k2_relat_1(sK2) | ~spl4_6),
% 2.02/0.63    inference(avatar_component_clause,[],[f132])).
% 2.02/0.63  fof(f132,plain,(
% 2.02/0.63    spl4_6 <=> sK1 = k2_relat_1(sK2)),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 2.02/0.63  fof(f947,plain,(
% 2.02/0.63    k6_partfun1(k2_relat_1(sK2)) != k6_partfun1(sK1) | (~spl4_22 | spl4_83)),
% 2.02/0.63    inference(forward_demodulation,[],[f748,f295])).
% 2.02/0.63  fof(f748,plain,(
% 2.02/0.63    k6_partfun1(sK1) != k6_partfun1(k2_relat_1(k2_funct_1(sK3))) | spl4_83),
% 2.02/0.63    inference(avatar_component_clause,[],[f746])).
% 2.02/0.63  fof(f746,plain,(
% 2.02/0.63    spl4_83 <=> k6_partfun1(sK1) = k6_partfun1(k2_relat_1(k2_funct_1(sK3)))),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_83])])).
% 2.02/0.63  fof(f946,plain,(
% 2.02/0.63    ~spl4_22 | spl4_82),
% 2.02/0.63    inference(avatar_contradiction_clause,[],[f945])).
% 2.02/0.63  fof(f945,plain,(
% 2.02/0.63    $false | (~spl4_22 | spl4_82)),
% 2.02/0.63    inference(subsumption_resolution,[],[f43,f943])).
% 2.02/0.63  fof(f943,plain,(
% 2.02/0.63    ~v2_funct_1(sK2) | (~spl4_22 | spl4_82)),
% 2.02/0.63    inference(forward_demodulation,[],[f744,f295])).
% 2.02/0.63  fof(f744,plain,(
% 2.02/0.63    ~v2_funct_1(k2_funct_1(sK3)) | spl4_82),
% 2.02/0.63    inference(avatar_component_clause,[],[f742])).
% 2.02/0.63  fof(f742,plain,(
% 2.02/0.63    spl4_82 <=> v2_funct_1(k2_funct_1(sK3))),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_82])])).
% 2.02/0.63  fof(f43,plain,(
% 2.02/0.63    v2_funct_1(sK2)),
% 2.02/0.63    inference(cnf_transformation,[],[f19])).
% 2.02/0.63  fof(f940,plain,(
% 2.02/0.63    ~spl4_22 | spl4_78),
% 2.02/0.63    inference(avatar_contradiction_clause,[],[f938])).
% 2.02/0.63  fof(f938,plain,(
% 2.02/0.63    $false | (~spl4_22 | spl4_78)),
% 2.02/0.63    inference(unit_resulting_resolution,[],[f60,f49,f932,f56])).
% 2.02/0.63  fof(f56,plain,(
% 2.02/0.63    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 2.02/0.63    inference(cnf_transformation,[],[f20])).
% 2.02/0.63  fof(f20,plain,(
% 2.02/0.63    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.02/0.63    inference(ennf_transformation,[],[f1])).
% 2.02/0.63  fof(f1,axiom,(
% 2.02/0.63    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.02/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 2.02/0.63  fof(f932,plain,(
% 2.02/0.63    ~v1_relat_1(sK2) | (~spl4_22 | spl4_78)),
% 2.02/0.63    inference(forward_demodulation,[],[f725,f295])).
% 2.02/0.63  fof(f725,plain,(
% 2.02/0.63    ~v1_relat_1(k2_funct_1(sK3)) | spl4_78),
% 2.02/0.63    inference(avatar_component_clause,[],[f723])).
% 2.02/0.63  fof(f723,plain,(
% 2.02/0.63    spl4_78 <=> v1_relat_1(k2_funct_1(sK3))),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_78])])).
% 2.02/0.63  fof(f49,plain,(
% 2.02/0.63    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.02/0.63    inference(cnf_transformation,[],[f19])).
% 2.02/0.63  fof(f60,plain,(
% 2.02/0.63    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.02/0.63    inference(cnf_transformation,[],[f2])).
% 2.02/0.63  fof(f2,axiom,(
% 2.02/0.63    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.02/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 2.02/0.63  fof(f929,plain,(
% 2.02/0.63    ~spl4_22 | spl4_77),
% 2.02/0.63    inference(avatar_contradiction_clause,[],[f928])).
% 2.02/0.63  fof(f928,plain,(
% 2.02/0.63    $false | (~spl4_22 | spl4_77)),
% 2.02/0.63    inference(subsumption_resolution,[],[f47,f926])).
% 2.02/0.63  fof(f926,plain,(
% 2.02/0.63    ~v1_funct_1(sK2) | (~spl4_22 | spl4_77)),
% 2.02/0.63    inference(superposition,[],[f721,f295])).
% 2.02/0.63  fof(f721,plain,(
% 2.02/0.63    ~v1_funct_1(k2_funct_1(sK3)) | spl4_77),
% 2.02/0.63    inference(avatar_component_clause,[],[f719])).
% 2.02/0.63  fof(f719,plain,(
% 2.02/0.63    spl4_77 <=> v1_funct_1(k2_funct_1(sK3))),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_77])])).
% 2.02/0.63  fof(f47,plain,(
% 2.02/0.63    v1_funct_1(sK2)),
% 2.02/0.63    inference(cnf_transformation,[],[f19])).
% 2.02/0.63  fof(f924,plain,(
% 2.02/0.63    spl4_24 | ~spl4_45),
% 2.02/0.63    inference(avatar_contradiction_clause,[],[f923])).
% 2.02/0.63  fof(f923,plain,(
% 2.02/0.63    $false | (spl4_24 | ~spl4_45)),
% 2.02/0.63    inference(trivial_inequality_removal,[],[f922])).
% 2.02/0.63  fof(f922,plain,(
% 2.02/0.63    k6_partfun1(sK0) != k6_partfun1(sK0) | (spl4_24 | ~spl4_45)),
% 2.02/0.63    inference(forward_demodulation,[],[f303,f477])).
% 2.02/0.63  fof(f477,plain,(
% 2.02/0.63    sK0 = k2_relat_1(sK3) | ~spl4_45),
% 2.02/0.63    inference(avatar_component_clause,[],[f475])).
% 2.02/0.63  fof(f475,plain,(
% 2.02/0.63    spl4_45 <=> sK0 = k2_relat_1(sK3)),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).
% 2.02/0.63  fof(f303,plain,(
% 2.02/0.63    k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3)) | spl4_24),
% 2.02/0.63    inference(avatar_component_clause,[],[f301])).
% 2.02/0.63  fof(f301,plain,(
% 2.02/0.63    spl4_24 <=> k6_partfun1(sK0) = k6_partfun1(k2_relat_1(sK3))),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 2.02/0.63  fof(f916,plain,(
% 2.02/0.63    spl4_25 | ~spl4_94),
% 2.02/0.63    inference(avatar_contradiction_clause,[],[f906])).
% 2.02/0.63  fof(f906,plain,(
% 2.02/0.63    $false | (spl4_25 | ~spl4_94)),
% 2.02/0.63    inference(subsumption_resolution,[],[f307,f895])).
% 2.02/0.63  fof(f895,plain,(
% 2.02/0.63    sK1 = k1_relat_1(sK3) | ~spl4_94),
% 2.02/0.63    inference(forward_demodulation,[],[f881,f75])).
% 2.02/0.63  fof(f881,plain,(
% 2.02/0.63    k1_relat_1(sK3) = k2_relat_1(k6_partfun1(sK1)) | ~spl4_94),
% 2.02/0.63    inference(superposition,[],[f75,f875])).
% 2.02/0.63  fof(f875,plain,(
% 2.02/0.63    k6_partfun1(sK1) = k6_partfun1(k1_relat_1(sK3)) | ~spl4_94),
% 2.02/0.63    inference(avatar_component_clause,[],[f873])).
% 2.02/0.63  fof(f873,plain,(
% 2.02/0.63    spl4_94 <=> k6_partfun1(sK1) = k6_partfun1(k1_relat_1(sK3))),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_94])])).
% 2.02/0.63  fof(f307,plain,(
% 2.02/0.63    sK1 != k1_relat_1(sK3) | spl4_25),
% 2.02/0.63    inference(avatar_component_clause,[],[f305])).
% 2.02/0.63  fof(f305,plain,(
% 2.02/0.63    spl4_25 <=> sK1 = k1_relat_1(sK3)),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 2.02/0.63  fof(f876,plain,(
% 2.02/0.63    ~spl4_49 | spl4_94 | ~spl4_48 | ~spl4_93),
% 2.02/0.63    inference(avatar_split_clause,[],[f871,f864,f494,f873,f499])).
% 2.02/0.63  fof(f499,plain,(
% 2.02/0.63    spl4_49 <=> v1_funct_2(sK3,k1_relat_1(sK3),sK0)),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).
% 2.02/0.63  fof(f494,plain,(
% 2.02/0.63    spl4_48 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK0)))),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).
% 2.02/0.63  fof(f864,plain,(
% 2.02/0.63    spl4_93 <=> ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) | k6_partfun1(X0) = k6_partfun1(sK1) | ~v1_funct_2(sK3,X0,sK0))),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_93])])).
% 2.02/0.63  fof(f871,plain,(
% 2.02/0.63    k6_partfun1(sK1) = k6_partfun1(k1_relat_1(sK3)) | ~v1_funct_2(sK3,k1_relat_1(sK3),sK0) | (~spl4_48 | ~spl4_93)),
% 2.02/0.63    inference(resolution,[],[f865,f496])).
% 2.02/0.63  fof(f496,plain,(
% 2.02/0.63    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK0))) | ~spl4_48),
% 2.02/0.63    inference(avatar_component_clause,[],[f494])).
% 2.02/0.63  fof(f865,plain,(
% 2.02/0.63    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) | k6_partfun1(X0) = k6_partfun1(sK1) | ~v1_funct_2(sK3,X0,sK0)) ) | ~spl4_93),
% 2.02/0.63    inference(avatar_component_clause,[],[f864])).
% 2.02/0.63  fof(f866,plain,(
% 2.02/0.63    spl4_93 | spl4_53 | ~spl4_86),
% 2.02/0.63    inference(avatar_split_clause,[],[f862,f775,f537,f864])).
% 2.02/0.63  fof(f537,plain,(
% 2.02/0.63    spl4_53 <=> k1_xboole_0 = sK0),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_53])])).
% 2.02/0.63  fof(f775,plain,(
% 2.02/0.63    spl4_86 <=> ! [X5,X6] : (k6_partfun1(sK1) = k6_partfun1(X6) | k1_xboole_0 = X5 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X6,X5))) | ~v1_funct_2(sK3,X6,X5) | sK0 != X5)),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_86])])).
% 2.02/0.63  fof(f862,plain,(
% 2.02/0.63    ( ! [X0] : (k1_xboole_0 = sK0 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) | ~v1_funct_2(sK3,X0,sK0) | k6_partfun1(X0) = k6_partfun1(sK1)) ) | ~spl4_86),
% 2.02/0.63    inference(equality_resolution,[],[f776])).
% 2.02/0.63  fof(f776,plain,(
% 2.02/0.63    ( ! [X6,X5] : (sK0 != X5 | k1_xboole_0 = X5 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X6,X5))) | ~v1_funct_2(sK3,X6,X5) | k6_partfun1(sK1) = k6_partfun1(X6)) ) | ~spl4_86),
% 2.02/0.63    inference(avatar_component_clause,[],[f775])).
% 2.02/0.63  fof(f789,plain,(
% 2.02/0.63    ~spl4_9 | spl4_88 | ~spl4_8 | ~spl4_87),
% 2.02/0.63    inference(avatar_split_clause,[],[f784,f780,f146,f786,f151])).
% 2.02/0.63  fof(f151,plain,(
% 2.02/0.63    spl4_9 <=> v1_funct_2(sK2,k1_relat_1(sK2),sK1)),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 2.02/0.63  fof(f146,plain,(
% 2.02/0.63    spl4_8 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 2.02/0.63  fof(f780,plain,(
% 2.02/0.63    spl4_87 <=> ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | k6_partfun1(X0) = k6_partfun1(sK0) | ~v1_funct_2(sK2,X0,sK1))),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_87])])).
% 2.02/0.63  fof(f784,plain,(
% 2.02/0.63    k6_partfun1(sK0) = k6_partfun1(k1_relat_1(sK2)) | ~v1_funct_2(sK2,k1_relat_1(sK2),sK1) | (~spl4_8 | ~spl4_87)),
% 2.02/0.63    inference(resolution,[],[f781,f148])).
% 2.02/0.63  fof(f148,plain,(
% 2.02/0.63    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) | ~spl4_8),
% 2.02/0.63    inference(avatar_component_clause,[],[f146])).
% 2.02/0.63  fof(f781,plain,(
% 2.02/0.63    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | k6_partfun1(X0) = k6_partfun1(sK0) | ~v1_funct_2(sK2,X0,sK1)) ) | ~spl4_87),
% 2.02/0.63    inference(avatar_component_clause,[],[f780])).
% 2.02/0.63  fof(f782,plain,(
% 2.02/0.63    spl4_87 | spl4_27 | ~spl4_85),
% 2.02/0.63    inference(avatar_split_clause,[],[f778,f770,f318,f780])).
% 2.02/0.63  fof(f318,plain,(
% 2.02/0.63    spl4_27 <=> k1_xboole_0 = sK1),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 2.02/0.63  fof(f770,plain,(
% 2.02/0.63    spl4_85 <=> ! [X3,X4] : (k6_partfun1(sK0) = k6_partfun1(X4) | k1_xboole_0 = X3 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X4,X3))) | ~v1_funct_2(sK2,X4,X3) | sK1 != X3)),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_85])])).
% 2.02/0.63  fof(f778,plain,(
% 2.02/0.63    ( ! [X0] : (k1_xboole_0 = sK1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | ~v1_funct_2(sK2,X0,sK1) | k6_partfun1(X0) = k6_partfun1(sK0)) ) | ~spl4_85),
% 2.02/0.63    inference(equality_resolution,[],[f771])).
% 2.02/0.63  fof(f771,plain,(
% 2.02/0.63    ( ! [X4,X3] : (sK1 != X3 | k1_xboole_0 = X3 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X4,X3))) | ~v1_funct_2(sK2,X4,X3) | k6_partfun1(sK0) = k6_partfun1(X4)) ) | ~spl4_85),
% 2.02/0.63    inference(avatar_component_clause,[],[f770])).
% 2.02/0.63  fof(f777,plain,(
% 2.02/0.63    ~spl4_23 | ~spl4_13 | spl4_86 | ~spl4_45 | ~spl4_52),
% 2.02/0.63    inference(avatar_split_clause,[],[f773,f533,f475,f775,f203,f297])).
% 2.02/0.63  fof(f297,plain,(
% 2.02/0.63    spl4_23 <=> v2_funct_1(sK3)),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 2.02/0.63  fof(f203,plain,(
% 2.02/0.63    spl4_13 <=> v1_funct_1(sK3)),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 2.02/0.63  fof(f533,plain,(
% 2.02/0.63    spl4_52 <=> k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).
% 2.02/0.63  fof(f773,plain,(
% 2.02/0.63    ( ! [X6,X5] : (k6_partfun1(sK1) = k6_partfun1(X6) | sK0 != X5 | ~v1_funct_2(sK3,X6,X5) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X6,X5))) | ~v1_funct_1(sK3) | ~v2_funct_1(sK3) | k1_xboole_0 = X5) ) | (~spl4_45 | ~spl4_52)),
% 2.02/0.63    inference(forward_demodulation,[],[f766,f535])).
% 2.02/0.63  fof(f535,plain,(
% 2.02/0.63    k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~spl4_52),
% 2.02/0.63    inference(avatar_component_clause,[],[f533])).
% 2.02/0.63  fof(f766,plain,(
% 2.02/0.63    ( ! [X6,X5] : (sK0 != X5 | ~v1_funct_2(sK3,X6,X5) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X6,X5))) | ~v1_funct_1(sK3) | ~v2_funct_1(sK3) | k1_xboole_0 = X5 | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(X6)) ) | ~spl4_45),
% 2.02/0.63    inference(superposition,[],[f311,f477])).
% 2.02/0.63  fof(f311,plain,(
% 2.02/0.63    ( ! [X2,X0,X1] : (k2_relat_1(X2) != X1 | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v2_funct_1(X2) | k1_xboole_0 = X1 | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) )),
% 2.02/0.63    inference(duplicate_literal_removal,[],[f310])).
% 2.02/0.63  fof(f310,plain,(
% 2.02/0.63    ( ! [X2,X0,X1] : (k2_relat_1(X2) != X1 | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v2_funct_1(X2) | k1_xboole_0 = X1 | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.02/0.63    inference(superposition,[],[f62,f61])).
% 2.02/0.63  fof(f61,plain,(
% 2.02/0.63    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.02/0.63    inference(cnf_transformation,[],[f25])).
% 2.02/0.63  fof(f25,plain,(
% 2.02/0.63    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.02/0.63    inference(ennf_transformation,[],[f6])).
% 2.02/0.63  fof(f6,axiom,(
% 2.02/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 2.02/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 2.02/0.63  fof(f62,plain,(
% 2.02/0.63    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v2_funct_1(X2) | k1_xboole_0 = X1 | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) )),
% 2.02/0.63    inference(cnf_transformation,[],[f27])).
% 2.02/0.63  fof(f27,plain,(
% 2.02/0.63    ! [X0,X1,X2] : ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.02/0.63    inference(flattening,[],[f26])).
% 2.02/0.63  fof(f26,plain,(
% 2.02/0.63    ! [X0,X1,X2] : ((((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.02/0.63    inference(ennf_transformation,[],[f14])).
% 2.02/0.63  fof(f14,axiom,(
% 2.02/0.63    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 2.02/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).
% 2.02/0.63  fof(f772,plain,(
% 2.02/0.63    ~spl4_28 | ~spl4_7 | spl4_85 | ~spl4_6 | ~spl4_26),
% 2.02/0.63    inference(avatar_split_clause,[],[f768,f314,f132,f770,f142,f322])).
% 2.02/0.63  fof(f322,plain,(
% 2.02/0.63    spl4_28 <=> v2_funct_1(sK2)),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 2.02/0.63  fof(f142,plain,(
% 2.02/0.63    spl4_7 <=> v1_funct_1(sK2)),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 2.02/0.63  fof(f314,plain,(
% 2.02/0.63    spl4_26 <=> k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 2.02/0.63  fof(f768,plain,(
% 2.02/0.63    ( ! [X4,X3] : (k6_partfun1(sK0) = k6_partfun1(X4) | sK1 != X3 | ~v1_funct_2(sK2,X4,X3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X4,X3))) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k1_xboole_0 = X3) ) | (~spl4_6 | ~spl4_26)),
% 2.02/0.63    inference(forward_demodulation,[],[f765,f316])).
% 2.02/0.63  fof(f316,plain,(
% 2.02/0.63    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~spl4_26),
% 2.02/0.63    inference(avatar_component_clause,[],[f314])).
% 2.02/0.63  fof(f765,plain,(
% 2.02/0.63    ( ! [X4,X3] : (sK1 != X3 | ~v1_funct_2(sK2,X4,X3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X4,X3))) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k1_xboole_0 = X3 | k6_partfun1(X4) = k5_relat_1(sK2,k2_funct_1(sK2))) ) | ~spl4_6),
% 2.02/0.63    inference(superposition,[],[f311,f134])).
% 2.02/0.63  fof(f753,plain,(
% 2.02/0.63    spl4_81 | ~spl4_78 | ~spl4_82 | ~spl4_13 | ~spl4_1 | ~spl4_77 | ~spl4_83 | ~spl4_84 | ~spl4_45 | ~spl4_52),
% 2.02/0.63    inference(avatar_split_clause,[],[f736,f533,f475,f750,f746,f719,f86,f203,f742,f723,f738])).
% 2.02/0.63  fof(f86,plain,(
% 2.02/0.63    spl4_1 <=> v1_relat_1(sK3)),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 2.02/0.63  fof(f736,plain,(
% 2.02/0.63    sK0 != k1_relat_1(k2_funct_1(sK3)) | k6_partfun1(sK1) != k6_partfun1(k2_relat_1(k2_funct_1(sK3))) | ~v1_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v2_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3)) | sK3 = k2_funct_1(k2_funct_1(sK3)) | (~spl4_45 | ~spl4_52)),
% 2.02/0.63    inference(forward_demodulation,[],[f717,f477])).
% 2.02/0.63  fof(f717,plain,(
% 2.02/0.63    k6_partfun1(sK1) != k6_partfun1(k2_relat_1(k2_funct_1(sK3))) | ~v1_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v2_funct_1(k2_funct_1(sK3)) | k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3)) | sK3 = k2_funct_1(k2_funct_1(sK3)) | ~spl4_52),
% 2.02/0.63    inference(superposition,[],[f77,f535])).
% 2.02/0.63  fof(f77,plain,(
% 2.02/0.63    ( ! [X0,X1] : (k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(X0) | k2_relat_1(X1) != k1_relat_1(X0) | ~v1_relat_1(X0) | k2_funct_1(X0) = X1) )),
% 2.02/0.63    inference(definition_unfolding,[],[f59,f51])).
% 2.02/0.63  fof(f59,plain,(
% 2.02/0.63    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(X0) | k2_relat_1(X1) != k1_relat_1(X0) | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_funct_1(X0) = X1) )),
% 2.02/0.63    inference(cnf_transformation,[],[f24])).
% 2.02/0.63  fof(f24,plain,(
% 2.02/0.63    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.02/0.63    inference(flattening,[],[f23])).
% 2.02/0.63  fof(f23,plain,(
% 2.02/0.63    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.02/0.63    inference(ennf_transformation,[],[f5])).
% 2.02/0.63  fof(f5,axiom,(
% 2.02/0.63    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 2.02/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).
% 2.02/0.63  fof(f708,plain,(
% 2.02/0.63    ~spl4_53),
% 2.02/0.63    inference(avatar_contradiction_clause,[],[f684])).
% 2.02/0.63  fof(f684,plain,(
% 2.02/0.63    $false | ~spl4_53),
% 2.02/0.63    inference(subsumption_resolution,[],[f44,f539])).
% 2.02/0.63  fof(f539,plain,(
% 2.02/0.63    k1_xboole_0 = sK0 | ~spl4_53),
% 2.02/0.63    inference(avatar_component_clause,[],[f537])).
% 2.02/0.63  fof(f44,plain,(
% 2.02/0.63    k1_xboole_0 != sK0),
% 2.02/0.63    inference(cnf_transformation,[],[f19])).
% 2.02/0.63  fof(f683,plain,(
% 2.02/0.63    spl4_75),
% 2.02/0.63    inference(avatar_contradiction_clause,[],[f680])).
% 2.02/0.63  fof(f680,plain,(
% 2.02/0.63    $false | spl4_75),
% 2.02/0.63    inference(unit_resulting_resolution,[],[f74,f674])).
% 2.02/0.63  fof(f674,plain,(
% 2.02/0.63    ~v2_funct_1(k6_partfun1(sK0)) | spl4_75),
% 2.02/0.63    inference(avatar_component_clause,[],[f672])).
% 2.02/0.63  fof(f672,plain,(
% 2.02/0.63    spl4_75 <=> v2_funct_1(k6_partfun1(sK0))),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_75])])).
% 2.02/0.63  fof(f74,plain,(
% 2.02/0.63    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 2.02/0.63    inference(definition_unfolding,[],[f50,f51])).
% 2.02/0.63  fof(f50,plain,(
% 2.02/0.63    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 2.02/0.63    inference(cnf_transformation,[],[f4])).
% 2.02/0.63  fof(f4,axiom,(
% 2.02/0.63    ! [X0] : v2_funct_1(k6_relat_1(X0))),
% 2.02/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_funct_1)).
% 2.02/0.63  fof(f675,plain,(
% 2.02/0.63    ~spl4_43 | ~spl4_12 | ~spl4_13 | spl4_53 | spl4_23 | ~spl4_75 | ~spl4_11 | ~spl4_55),
% 2.02/0.63    inference(avatar_split_clause,[],[f668,f553,f180,f672,f297,f537,f203,f199,f457])).
% 2.02/0.63  fof(f457,plain,(
% 2.02/0.63    spl4_43 <=> v1_funct_2(sK3,sK1,sK0)),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).
% 2.02/0.63  fof(f199,plain,(
% 2.02/0.63    spl4_12 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 2.02/0.63  fof(f180,plain,(
% 2.02/0.63    spl4_11 <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 2.02/0.63  fof(f553,plain,(
% 2.02/0.63    spl4_55 <=> ! [X1,X0] : (~v1_funct_1(X0) | v2_funct_1(X0) | k1_xboole_0 = X1 | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~v1_funct_2(X0,sK1,X1))),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_55])])).
% 2.02/0.63  fof(f668,plain,(
% 2.02/0.63    ~v2_funct_1(k6_partfun1(sK0)) | v2_funct_1(sK3) | k1_xboole_0 = sK0 | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | (~spl4_11 | ~spl4_55)),
% 2.02/0.63    inference(superposition,[],[f554,f182])).
% 2.02/0.63  fof(f182,plain,(
% 2.02/0.63    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) | ~spl4_11),
% 2.02/0.63    inference(avatar_component_clause,[],[f180])).
% 2.02/0.63  fof(f554,plain,(
% 2.02/0.63    ( ! [X0,X1] : (~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0)) | v2_funct_1(X0) | k1_xboole_0 = X1 | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~v1_funct_2(X0,sK1,X1)) ) | ~spl4_55),
% 2.02/0.63    inference(avatar_component_clause,[],[f553])).
% 2.02/0.63  fof(f555,plain,(
% 2.02/0.63    ~spl4_7 | spl4_55 | ~spl4_5 | ~spl4_29),
% 2.02/0.63    inference(avatar_split_clause,[],[f551,f326,f128,f553,f142])).
% 2.02/0.63  fof(f128,plain,(
% 2.02/0.63    spl4_5 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 2.02/0.63  fof(f326,plain,(
% 2.02/0.63    spl4_29 <=> v1_funct_2(sK2,sK0,sK1)),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 2.02/0.63  fof(f551,plain,(
% 2.02/0.63    ( ! [X0,X1] : (~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(X0) | ~v1_funct_2(X0,sK1,X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0)) | ~v1_funct_1(sK2) | k1_xboole_0 = X1 | v2_funct_1(X0)) )),
% 2.02/0.63    inference(trivial_inequality_removal,[],[f546])).
% 2.02/0.63  fof(f546,plain,(
% 2.02/0.63    ( ! [X0,X1] : (sK1 != sK1 | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(X0) | ~v1_funct_2(X0,sK1,X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0)) | ~v1_funct_1(sK2) | k1_xboole_0 = X1 | v2_funct_1(X0)) )),
% 2.02/0.63    inference(superposition,[],[f68,f41])).
% 2.02/0.63  fof(f41,plain,(
% 2.02/0.63    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 2.02/0.63    inference(cnf_transformation,[],[f19])).
% 2.02/0.63  fof(f68,plain,(
% 2.02/0.63    ( ! [X4,X2,X0,X3,X1] : (k2_relset_1(X0,X1,X3) != X1 | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X1,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~v1_funct_1(X3) | k1_xboole_0 = X2 | v2_funct_1(X4)) )),
% 2.02/0.63    inference(cnf_transformation,[],[f31])).
% 2.02/0.63  fof(f31,plain,(
% 2.02/0.63    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 2.02/0.63    inference(flattening,[],[f30])).
% 2.02/0.63  fof(f30,plain,(
% 2.02/0.63    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 2.02/0.63    inference(ennf_transformation,[],[f13])).
% 2.02/0.63  fof(f13,axiom,(
% 2.02/0.63    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 2.02/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_funct_2)).
% 2.02/0.63  fof(f540,plain,(
% 2.02/0.63    spl4_52 | spl4_53 | ~spl4_23 | ~spl4_13 | ~spl4_12 | ~spl4_43 | ~spl4_42),
% 2.02/0.63    inference(avatar_split_clause,[],[f472,f453,f457,f199,f203,f297,f537,f533])).
% 2.02/0.63  fof(f453,plain,(
% 2.02/0.63    spl4_42 <=> sK0 = k2_relset_1(sK1,sK0,sK3)),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).
% 2.02/0.63  fof(f472,plain,(
% 2.02/0.63    ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~v2_funct_1(sK3) | k1_xboole_0 = sK0 | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~spl4_42),
% 2.02/0.63    inference(trivial_inequality_removal,[],[f470])).
% 2.02/0.63  fof(f470,plain,(
% 2.02/0.63    sK0 != sK0 | ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~v2_funct_1(sK3) | k1_xboole_0 = sK0 | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~spl4_42),
% 2.02/0.63    inference(superposition,[],[f62,f455])).
% 2.02/0.63  fof(f455,plain,(
% 2.02/0.63    sK0 = k2_relset_1(sK1,sK0,sK3) | ~spl4_42),
% 2.02/0.63    inference(avatar_component_clause,[],[f453])).
% 2.02/0.63  fof(f502,plain,(
% 2.02/0.63    ~spl4_1 | ~spl4_13 | spl4_49 | ~spl4_45),
% 2.02/0.63    inference(avatar_split_clause,[],[f483,f475,f499,f203,f86])).
% 2.02/0.63  fof(f483,plain,(
% 2.02/0.63    v1_funct_2(sK3,k1_relat_1(sK3),sK0) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl4_45),
% 2.02/0.63    inference(superposition,[],[f57,f477])).
% 2.02/0.63  fof(f57,plain,(
% 2.02/0.63    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.02/0.63    inference(cnf_transformation,[],[f22])).
% 2.02/0.63  fof(f22,plain,(
% 2.02/0.63    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.02/0.63    inference(flattening,[],[f21])).
% 2.02/0.63  fof(f21,plain,(
% 2.02/0.63    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.02/0.63    inference(ennf_transformation,[],[f15])).
% 2.02/0.63  fof(f15,axiom,(
% 2.02/0.63    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 2.02/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).
% 2.02/0.63  fof(f497,plain,(
% 2.02/0.63    ~spl4_1 | ~spl4_13 | spl4_48 | ~spl4_45),
% 2.02/0.63    inference(avatar_split_clause,[],[f482,f475,f494,f203,f86])).
% 2.02/0.63  fof(f482,plain,(
% 2.02/0.63    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK0))) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl4_45),
% 2.02/0.63    inference(superposition,[],[f58,f477])).
% 2.02/0.63  fof(f58,plain,(
% 2.02/0.63    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.02/0.63    inference(cnf_transformation,[],[f22])).
% 2.02/0.63  fof(f479,plain,(
% 2.02/0.63    ~spl4_12 | spl4_45 | ~spl4_42),
% 2.02/0.63    inference(avatar_split_clause,[],[f471,f453,f475,f199])).
% 2.02/0.63  fof(f471,plain,(
% 2.02/0.63    sK0 = k2_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_42),
% 2.02/0.63    inference(superposition,[],[f61,f455])).
% 2.02/0.63  fof(f467,plain,(
% 2.02/0.63    spl4_43),
% 2.02/0.63    inference(avatar_contradiction_clause,[],[f466])).
% 2.02/0.63  fof(f466,plain,(
% 2.02/0.63    $false | spl4_43),
% 2.02/0.63    inference(subsumption_resolution,[],[f39,f459])).
% 2.02/0.63  fof(f459,plain,(
% 2.02/0.63    ~v1_funct_2(sK3,sK1,sK0) | spl4_43),
% 2.02/0.63    inference(avatar_component_clause,[],[f457])).
% 2.02/0.63  fof(f39,plain,(
% 2.02/0.63    v1_funct_2(sK3,sK1,sK0)),
% 2.02/0.63    inference(cnf_transformation,[],[f19])).
% 2.02/0.63  fof(f460,plain,(
% 2.02/0.63    spl4_42 | ~spl4_13 | ~spl4_5 | ~spl4_29 | ~spl4_7 | ~spl4_12 | ~spl4_43),
% 2.02/0.63    inference(avatar_split_clause,[],[f448,f457,f199,f142,f326,f128,f203,f453])).
% 2.02/0.63  fof(f448,plain,(
% 2.02/0.63    ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | sK0 = k2_relset_1(sK1,sK0,sK3)),
% 2.02/0.63    inference(resolution,[],[f64,f42])).
% 2.02/0.63  fof(f42,plain,(
% 2.02/0.63    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 2.02/0.63    inference(cnf_transformation,[],[f19])).
% 2.02/0.63  fof(f64,plain,(
% 2.02/0.63    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(X2) | k2_relset_1(X0,X1,X2) = X1) )),
% 2.02/0.63    inference(cnf_transformation,[],[f29])).
% 2.02/0.63  fof(f29,plain,(
% 2.02/0.63    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.02/0.63    inference(flattening,[],[f28])).
% 2.02/0.63  fof(f28,plain,(
% 2.02/0.63    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.02/0.63    inference(ennf_transformation,[],[f12])).
% 2.02/0.63  fof(f12,axiom,(
% 2.02/0.63    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 2.02/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).
% 2.02/0.63  fof(f359,plain,(
% 2.02/0.63    ~spl4_27),
% 2.02/0.63    inference(avatar_contradiction_clause,[],[f343])).
% 2.02/0.63  fof(f343,plain,(
% 2.02/0.63    $false | ~spl4_27),
% 2.02/0.63    inference(subsumption_resolution,[],[f45,f320])).
% 2.02/0.63  fof(f320,plain,(
% 2.02/0.63    k1_xboole_0 = sK1 | ~spl4_27),
% 2.02/0.63    inference(avatar_component_clause,[],[f318])).
% 2.02/0.63  fof(f45,plain,(
% 2.02/0.63    k1_xboole_0 != sK1),
% 2.02/0.63    inference(cnf_transformation,[],[f19])).
% 2.02/0.63  fof(f333,plain,(
% 2.02/0.63    spl4_29),
% 2.02/0.63    inference(avatar_contradiction_clause,[],[f332])).
% 2.02/0.63  fof(f332,plain,(
% 2.02/0.63    $false | spl4_29),
% 2.02/0.63    inference(subsumption_resolution,[],[f48,f328])).
% 2.02/0.63  fof(f328,plain,(
% 2.02/0.63    ~v1_funct_2(sK2,sK0,sK1) | spl4_29),
% 2.02/0.63    inference(avatar_component_clause,[],[f326])).
% 2.02/0.63  fof(f48,plain,(
% 2.02/0.63    v1_funct_2(sK2,sK0,sK1)),
% 2.02/0.63    inference(cnf_transformation,[],[f19])).
% 2.02/0.63  fof(f331,plain,(
% 2.02/0.63    spl4_28),
% 2.02/0.63    inference(avatar_contradiction_clause,[],[f330])).
% 2.02/0.63  fof(f330,plain,(
% 2.02/0.63    $false | spl4_28),
% 2.02/0.63    inference(subsumption_resolution,[],[f43,f324])).
% 2.02/0.63  fof(f324,plain,(
% 2.02/0.63    ~v2_funct_1(sK2) | spl4_28),
% 2.02/0.63    inference(avatar_component_clause,[],[f322])).
% 2.02/0.63  fof(f329,plain,(
% 2.02/0.63    spl4_26 | spl4_27 | ~spl4_28 | ~spl4_7 | ~spl4_5 | ~spl4_29),
% 2.02/0.63    inference(avatar_split_clause,[],[f312,f326,f128,f142,f322,f318,f314])).
% 2.02/0.63  fof(f312,plain,(
% 2.02/0.63    ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k1_xboole_0 = sK1 | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 2.02/0.63    inference(trivial_inequality_removal,[],[f309])).
% 2.02/0.63  fof(f309,plain,(
% 2.02/0.63    sK1 != sK1 | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k1_xboole_0 = sK1 | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 2.02/0.63    inference(superposition,[],[f62,f41])).
% 2.02/0.63  fof(f308,plain,(
% 2.02/0.63    spl4_22 | ~spl4_1 | ~spl4_23 | ~spl4_7 | ~spl4_3 | ~spl4_13 | ~spl4_24 | ~spl4_25 | ~spl4_6 | ~spl4_16),
% 2.02/0.63    inference(avatar_split_clause,[],[f291,f226,f132,f305,f301,f203,f95,f142,f297,f86,f293])).
% 2.02/0.63  fof(f95,plain,(
% 2.02/0.63    spl4_3 <=> v1_relat_1(sK2)),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 2.02/0.63  fof(f226,plain,(
% 2.02/0.63    spl4_16 <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 2.02/0.63  fof(f291,plain,(
% 2.02/0.63    sK1 != k1_relat_1(sK3) | k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v2_funct_1(sK3) | ~v1_relat_1(sK3) | sK2 = k2_funct_1(sK3) | (~spl4_6 | ~spl4_16)),
% 2.02/0.63    inference(forward_demodulation,[],[f290,f134])).
% 2.02/0.63  fof(f290,plain,(
% 2.02/0.63    k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v1_relat_1(sK3) | sK2 = k2_funct_1(sK3) | ~spl4_16),
% 2.02/0.63    inference(superposition,[],[f77,f228])).
% 2.02/0.63  fof(f228,plain,(
% 2.02/0.63    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~spl4_16),
% 2.02/0.63    inference(avatar_component_clause,[],[f226])).
% 2.02/0.63  fof(f282,plain,(
% 2.02/0.63    ~spl4_7 | ~spl4_12 | ~spl4_13 | ~spl4_5 | spl4_16 | ~spl4_11),
% 2.02/0.63    inference(avatar_split_clause,[],[f279,f180,f226,f128,f203,f199,f142])).
% 2.02/0.63  fof(f279,plain,(
% 2.02/0.63    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | ~spl4_11),
% 2.02/0.63    inference(superposition,[],[f71,f182])).
% 2.02/0.63  fof(f71,plain,(
% 2.02/0.63    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 2.02/0.63    inference(cnf_transformation,[],[f35])).
% 2.02/0.63  fof(f35,plain,(
% 2.02/0.63    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.02/0.63    inference(flattening,[],[f34])).
% 2.02/0.63  fof(f34,plain,(
% 2.02/0.63    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.02/0.63    inference(ennf_transformation,[],[f10])).
% 2.02/0.63  fof(f10,axiom,(
% 2.02/0.63    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 2.02/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 2.02/0.63  fof(f275,plain,(
% 2.02/0.63    spl4_10),
% 2.02/0.63    inference(avatar_contradiction_clause,[],[f262])).
% 2.02/0.63  fof(f262,plain,(
% 2.02/0.63    $false | spl4_10),
% 2.02/0.63    inference(unit_resulting_resolution,[],[f47,f38,f40,f49,f178,f73])).
% 2.02/0.63  fof(f73,plain,(
% 2.02/0.63    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 2.02/0.63    inference(cnf_transformation,[],[f37])).
% 2.02/0.63  fof(f37,plain,(
% 2.02/0.63    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.02/0.63    inference(flattening,[],[f36])).
% 2.02/0.63  fof(f36,plain,(
% 2.02/0.63    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.02/0.63    inference(ennf_transformation,[],[f8])).
% 2.02/0.63  fof(f8,axiom,(
% 2.02/0.63    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 2.02/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 2.02/0.63  fof(f178,plain,(
% 2.02/0.63    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl4_10),
% 2.02/0.63    inference(avatar_component_clause,[],[f176])).
% 2.02/0.63  fof(f176,plain,(
% 2.02/0.63    spl4_10 <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 2.02/0.63  fof(f40,plain,(
% 2.02/0.63    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.02/0.63    inference(cnf_transformation,[],[f19])).
% 2.02/0.63  fof(f38,plain,(
% 2.02/0.63    v1_funct_1(sK3)),
% 2.02/0.63    inference(cnf_transformation,[],[f19])).
% 2.02/0.63  fof(f219,plain,(
% 2.02/0.63    spl4_13),
% 2.02/0.63    inference(avatar_contradiction_clause,[],[f218])).
% 2.02/0.63  fof(f218,plain,(
% 2.02/0.63    $false | spl4_13),
% 2.02/0.63    inference(subsumption_resolution,[],[f38,f205])).
% 2.02/0.63  fof(f205,plain,(
% 2.02/0.63    ~v1_funct_1(sK3) | spl4_13),
% 2.02/0.63    inference(avatar_component_clause,[],[f203])).
% 2.02/0.63  fof(f217,plain,(
% 2.02/0.63    spl4_12),
% 2.02/0.63    inference(avatar_contradiction_clause,[],[f216])).
% 2.02/0.63  fof(f216,plain,(
% 2.02/0.63    $false | spl4_12),
% 2.02/0.63    inference(subsumption_resolution,[],[f40,f201])).
% 2.02/0.63  fof(f201,plain,(
% 2.02/0.63    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl4_12),
% 2.02/0.63    inference(avatar_component_clause,[],[f199])).
% 2.02/0.63  fof(f183,plain,(
% 2.02/0.63    ~spl4_10 | spl4_11),
% 2.02/0.63    inference(avatar_split_clause,[],[f174,f180,f176])).
% 2.02/0.63  fof(f174,plain,(
% 2.02/0.63    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.02/0.63    inference(resolution,[],[f160,f42])).
% 2.02/0.63  fof(f160,plain,(
% 2.02/0.63    ( ! [X2,X3] : (~r2_relset_1(X3,X3,X2,k6_partfun1(X3)) | k6_partfun1(X3) = X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X3)))) )),
% 2.02/0.63    inference(resolution,[],[f70,f53])).
% 2.02/0.63  fof(f53,plain,(
% 2.02/0.63    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.02/0.63    inference(cnf_transformation,[],[f9])).
% 2.02/0.63  fof(f9,axiom,(
% 2.02/0.63    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 2.02/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 2.02/0.63  fof(f70,plain,(
% 2.02/0.63    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 = X3 | ~r2_relset_1(X0,X1,X2,X3)) )),
% 2.02/0.63    inference(cnf_transformation,[],[f33])).
% 2.02/0.63  fof(f33,plain,(
% 2.02/0.63    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.02/0.63    inference(flattening,[],[f32])).
% 2.02/0.63  fof(f32,plain,(
% 2.02/0.63    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.02/0.63    inference(ennf_transformation,[],[f7])).
% 2.02/0.63  fof(f7,axiom,(
% 2.02/0.63    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.02/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 2.02/0.63  fof(f156,plain,(
% 2.02/0.63    spl4_7),
% 2.02/0.63    inference(avatar_contradiction_clause,[],[f155])).
% 2.02/0.63  fof(f155,plain,(
% 2.02/0.63    $false | spl4_7),
% 2.02/0.63    inference(subsumption_resolution,[],[f47,f144])).
% 2.02/0.63  fof(f144,plain,(
% 2.02/0.63    ~v1_funct_1(sK2) | spl4_7),
% 2.02/0.63    inference(avatar_component_clause,[],[f142])).
% 2.02/0.63  fof(f154,plain,(
% 2.02/0.63    ~spl4_3 | ~spl4_7 | spl4_9 | ~spl4_6),
% 2.02/0.63    inference(avatar_split_clause,[],[f140,f132,f151,f142,f95])).
% 2.02/0.63  fof(f140,plain,(
% 2.02/0.63    v1_funct_2(sK2,k1_relat_1(sK2),sK1) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl4_6),
% 2.02/0.63    inference(superposition,[],[f57,f134])).
% 2.02/0.63  fof(f149,plain,(
% 2.02/0.63    ~spl4_3 | ~spl4_7 | spl4_8 | ~spl4_6),
% 2.02/0.63    inference(avatar_split_clause,[],[f139,f132,f146,f142,f95])).
% 2.02/0.63  fof(f139,plain,(
% 2.02/0.63    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl4_6),
% 2.02/0.63    inference(superposition,[],[f58,f134])).
% 2.02/0.63  fof(f138,plain,(
% 2.02/0.63    spl4_5),
% 2.02/0.63    inference(avatar_contradiction_clause,[],[f137])).
% 2.02/0.63  fof(f137,plain,(
% 2.02/0.63    $false | spl4_5),
% 2.02/0.63    inference(subsumption_resolution,[],[f49,f130])).
% 2.02/0.63  fof(f130,plain,(
% 2.02/0.63    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl4_5),
% 2.02/0.63    inference(avatar_component_clause,[],[f128])).
% 2.02/0.63  fof(f136,plain,(
% 2.02/0.63    ~spl4_5 | spl4_6),
% 2.02/0.63    inference(avatar_split_clause,[],[f126,f132,f128])).
% 2.02/0.63  fof(f126,plain,(
% 2.02/0.63    sK1 = k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.02/0.63    inference(superposition,[],[f41,f61])).
% 2.02/0.63  fof(f110,plain,(
% 2.02/0.63    spl4_4),
% 2.02/0.63    inference(avatar_contradiction_clause,[],[f107])).
% 2.02/0.63  fof(f107,plain,(
% 2.02/0.63    $false | spl4_4),
% 2.02/0.63    inference(unit_resulting_resolution,[],[f60,f101])).
% 2.02/0.63  fof(f101,plain,(
% 2.02/0.63    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl4_4),
% 2.02/0.63    inference(avatar_component_clause,[],[f99])).
% 2.02/0.63  fof(f99,plain,(
% 2.02/0.63    spl4_4 <=> v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 2.02/0.63  fof(f106,plain,(
% 2.02/0.63    spl4_2),
% 2.02/0.63    inference(avatar_contradiction_clause,[],[f103])).
% 2.02/0.63  fof(f103,plain,(
% 2.02/0.63    $false | spl4_2),
% 2.02/0.63    inference(unit_resulting_resolution,[],[f60,f92])).
% 2.02/0.63  fof(f92,plain,(
% 2.02/0.63    ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | spl4_2),
% 2.02/0.63    inference(avatar_component_clause,[],[f90])).
% 2.02/0.63  fof(f90,plain,(
% 2.02/0.63    spl4_2 <=> v1_relat_1(k2_zfmisc_1(sK1,sK0))),
% 2.02/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 2.02/0.63  fof(f102,plain,(
% 2.02/0.63    spl4_3 | ~spl4_4),
% 2.02/0.63    inference(avatar_split_clause,[],[f83,f99,f95])).
% 2.02/0.63  fof(f83,plain,(
% 2.02/0.63    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | v1_relat_1(sK2)),
% 2.02/0.63    inference(resolution,[],[f56,f49])).
% 2.02/0.63  fof(f93,plain,(
% 2.02/0.63    spl4_1 | ~spl4_2),
% 2.02/0.63    inference(avatar_split_clause,[],[f82,f90,f86])).
% 2.02/0.63  fof(f82,plain,(
% 2.02/0.63    ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | v1_relat_1(sK3)),
% 2.02/0.63    inference(resolution,[],[f56,f40])).
% 2.02/0.63  % SZS output end Proof for theBenchmark
% 2.02/0.63  % (28640)------------------------------
% 2.02/0.63  % (28640)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.02/0.63  % (28640)Termination reason: Refutation
% 2.02/0.63  
% 2.02/0.63  % (28640)Memory used [KB]: 7036
% 2.02/0.63  % (28640)Time elapsed: 0.178 s
% 2.02/0.63  % (28640)------------------------------
% 2.02/0.63  % (28640)------------------------------
% 2.02/0.63  % (28626)Success in time 0.269 s
%------------------------------------------------------------------------------
