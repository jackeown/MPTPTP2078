%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1027+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:03 EST 2020

% Result     : Theorem 1.72s
% Output     : Refutation 1.72s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 200 expanded)
%              Number of leaves         :   23 (  82 expanded)
%              Depth                    :   11
%              Number of atoms          :  312 ( 681 expanded)
%              Number of equality atoms :   96 ( 249 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3187,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1813,f1817,f1819,f1821,f2230,f2234,f2494,f2501,f3007,f3048,f3066,f3087,f3092,f3105,f3157,f3179,f3186])).

fof(f3186,plain,
    ( spl14_68
    | ~ spl14_9
    | ~ spl14_99 ),
    inference(avatar_split_clause,[],[f3185,f3174,f1845,f2468])).

fof(f2468,plain,
    ( spl14_68
  <=> v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_68])])).

fof(f1845,plain,
    ( spl14_9
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_9])])).

fof(f3174,plain,
    ( spl14_99
  <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_99])])).

fof(f3185,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl14_9
    | ~ spl14_99 ),
    inference(subsumption_resolution,[],[f3184,f1846])).

fof(f1846,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl14_9 ),
    inference(avatar_component_clause,[],[f1845])).

fof(f3184,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl14_99 ),
    inference(trivial_inequality_removal,[],[f3182])).

fof(f3182,plain,
    ( k1_xboole_0 != k1_xboole_0
    | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl14_99 ),
    inference(superposition,[],[f2845,f3175])).

fof(f3175,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl14_99 ),
    inference(avatar_component_clause,[],[f3174])).

fof(f2845,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(forward_demodulation,[],[f1798,f1803])).

fof(f1803,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f1773])).

fof(f1773,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f1684])).

fof(f1684,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f1683])).

fof(f1683,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f329])).

fof(f329,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f1798,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f1729])).

fof(f1729,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f1661])).

fof(f1661,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f1611])).

fof(f1611,plain,(
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
    inference(flattening,[],[f1610])).

fof(f1610,plain,(
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
    inference(ennf_transformation,[],[f1476])).

fof(f1476,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f3179,plain,
    ( spl14_99
    | ~ spl14_79
    | ~ spl14_92 ),
    inference(avatar_split_clause,[],[f3178,f3059,f2713,f3174])).

fof(f2713,plain,
    ( spl14_79
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_79])])).

fof(f3059,plain,
    ( spl14_92
  <=> sK0 = k1_relset_1(sK0,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_92])])).

fof(f3178,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl14_79
    | ~ spl14_92 ),
    inference(forward_demodulation,[],[f3060,f2714])).

fof(f2714,plain,
    ( k1_xboole_0 = sK0
    | ~ spl14_79 ),
    inference(avatar_component_clause,[],[f2713])).

fof(f3060,plain,
    ( sK0 = k1_relset_1(sK0,k1_xboole_0,k1_xboole_0)
    | ~ spl14_92 ),
    inference(avatar_component_clause,[],[f3059])).

fof(f3157,plain,
    ( ~ spl14_68
    | ~ spl14_79
    | spl14_93 ),
    inference(avatar_split_clause,[],[f3129,f3064,f2713,f2468])).

fof(f3064,plain,
    ( spl14_93
  <=> v1_funct_2(k1_xboole_0,sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_93])])).

fof(f3129,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl14_79
    | spl14_93 ),
    inference(backward_demodulation,[],[f3065,f2714])).

fof(f3065,plain,
    ( ~ v1_funct_2(k1_xboole_0,sK0,k1_xboole_0)
    | spl14_93 ),
    inference(avatar_component_clause,[],[f3064])).

fof(f3105,plain,
    ( spl14_79
    | spl14_93 ),
    inference(avatar_split_clause,[],[f3104,f3064,f2713])).

fof(f3104,plain,
    ( k1_xboole_0 = sK0
    | spl14_93 ),
    inference(resolution,[],[f3065,f2146])).

fof(f2146,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(subsumption_resolution,[],[f1796,f1779])).

fof(f1779,plain,(
    ! [X0,X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f1248])).

fof(f1248,axiom,(
    ! [X0,X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relset_1)).

fof(f1796,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f1795])).

fof(f1795,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k1_xboole_0,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f1731])).

fof(f1731,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X2
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f1661])).

fof(f3092,plain,
    ( spl14_92
    | ~ spl14_52
    | ~ spl14_88 ),
    inference(avatar_split_clause,[],[f3091,f3005,f2232,f3059])).

fof(f2232,plain,
    ( spl14_52
  <=> sK0 = k1_relset_1(sK0,sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_52])])).

fof(f3005,plain,
    ( spl14_88
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_88])])).

fof(f3091,plain,
    ( sK0 = k1_relset_1(sK0,k1_xboole_0,k1_xboole_0)
    | ~ spl14_52
    | ~ spl14_88 ),
    inference(forward_demodulation,[],[f2233,f3006])).

fof(f3006,plain,
    ( k1_xboole_0 = sK1
    | ~ spl14_88 ),
    inference(avatar_component_clause,[],[f3005])).

fof(f2233,plain,
    ( sK0 = k1_relset_1(sK0,sK1,k1_xboole_0)
    | ~ spl14_52 ),
    inference(avatar_component_clause,[],[f2232])).

fof(f3087,plain,
    ( spl14_31
    | ~ spl14_75 ),
    inference(avatar_split_clause,[],[f3086,f2616,f2033])).

fof(f2033,plain,
    ( spl14_31
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_31])])).

fof(f2616,plain,
    ( spl14_75
  <=> r1_tarski(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_75])])).

fof(f3086,plain,
    ( k1_xboole_0 = sK2
    | ~ spl14_75 ),
    inference(resolution,[],[f2617,f1867])).

fof(f1867,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f1775,f1802])).

fof(f1802,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f1774])).

fof(f1774,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f1684])).

fof(f1775,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1645])).

fof(f1645,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X0))
        & ~ r1_tarski(X0,k2_zfmisc_1(X0,X1)) ) ) ),
    inference(ennf_transformation,[],[f351])).

fof(f351,axiom,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k2_zfmisc_1(X1,X0))
        | r1_tarski(X0,k2_zfmisc_1(X0,X1)) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t135_zfmisc_1)).

fof(f2617,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl14_75 ),
    inference(avatar_component_clause,[],[f2616])).

fof(f3066,plain,
    ( ~ spl14_93
    | spl14_51
    | ~ spl14_88 ),
    inference(avatar_split_clause,[],[f3062,f3005,f2228,f3064])).

fof(f2228,plain,
    ( spl14_51
  <=> v1_funct_2(k1_xboole_0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_51])])).

fof(f3062,plain,
    ( ~ v1_funct_2(k1_xboole_0,sK0,k1_xboole_0)
    | spl14_51
    | ~ spl14_88 ),
    inference(forward_demodulation,[],[f2229,f3006])).

fof(f2229,plain,
    ( ~ v1_funct_2(k1_xboole_0,sK0,sK1)
    | spl14_51 ),
    inference(avatar_component_clause,[],[f2228])).

fof(f3048,plain,
    ( spl14_75
    | ~ spl14_11
    | ~ spl14_88 ),
    inference(avatar_split_clause,[],[f3026,f3005,f1859,f2616])).

fof(f1859,plain,
    ( spl14_11
  <=> r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_11])])).

fof(f3026,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl14_11
    | ~ spl14_88 ),
    inference(forward_demodulation,[],[f3011,f1802])).

fof(f3011,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK0,k1_xboole_0))
    | ~ spl14_11
    | ~ spl14_88 ),
    inference(backward_demodulation,[],[f1860,f3006])).

fof(f1860,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))
    | ~ spl14_11 ),
    inference(avatar_component_clause,[],[f1859])).

fof(f3007,plain,
    ( spl14_88
    | spl14_2
    | ~ spl14_3
    | ~ spl14_4 ),
    inference(avatar_split_clause,[],[f3003,f1815,f1811,f1808,f3005])).

fof(f1808,plain,
    ( spl14_2
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_2])])).

fof(f1811,plain,
    ( spl14_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_3])])).

fof(f1815,plain,
    ( spl14_4
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_4])])).

fof(f3003,plain,
    ( k1_xboole_0 = sK1
    | spl14_2
    | ~ spl14_3
    | ~ spl14_4 ),
    inference(subsumption_resolution,[],[f3002,f1809])).

fof(f1809,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | spl14_2 ),
    inference(avatar_component_clause,[],[f1808])).

fof(f3002,plain,
    ( k1_xboole_0 = sK1
    | v1_funct_2(sK2,sK0,sK1)
    | ~ spl14_3
    | ~ spl14_4 ),
    inference(subsumption_resolution,[],[f2996,f1816])).

fof(f1816,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl14_4 ),
    inference(avatar_component_clause,[],[f1815])).

fof(f2996,plain,
    ( sK0 != k1_relset_1(sK0,sK1,sK2)
    | k1_xboole_0 = sK1
    | v1_funct_2(sK2,sK0,sK1)
    | ~ spl14_3 ),
    inference(resolution,[],[f1728,f1818])).

fof(f1818,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl14_3 ),
    inference(avatar_component_clause,[],[f1811])).

fof(f1728,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f1661])).

fof(f2501,plain,
    ( spl14_11
    | ~ spl14_3 ),
    inference(avatar_split_clause,[],[f2498,f1811,f1859])).

fof(f2498,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))
    | ~ spl14_3 ),
    inference(resolution,[],[f1738,f1818])).

fof(f1738,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1664])).

fof(f1664,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f609])).

fof(f609,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f2494,plain,(
    spl14_9 ),
    inference(avatar_split_clause,[],[f2492,f1845])).

fof(f2492,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[],[f1779,f1803])).

fof(f2234,plain,
    ( spl14_52
    | ~ spl14_4
    | ~ spl14_31 ),
    inference(avatar_split_clause,[],[f2211,f2033,f1815,f2232])).

fof(f2211,plain,
    ( sK0 = k1_relset_1(sK0,sK1,k1_xboole_0)
    | ~ spl14_4
    | ~ spl14_31 ),
    inference(backward_demodulation,[],[f1816,f2200])).

fof(f2200,plain,
    ( k1_xboole_0 = sK2
    | ~ spl14_31 ),
    inference(avatar_component_clause,[],[f2033])).

fof(f2230,plain,
    ( ~ spl14_51
    | spl14_2
    | ~ spl14_31 ),
    inference(avatar_split_clause,[],[f2210,f2033,f1808,f2228])).

fof(f2210,plain,
    ( ~ v1_funct_2(k1_xboole_0,sK0,sK1)
    | spl14_2
    | ~ spl14_31 ),
    inference(backward_demodulation,[],[f1809,f2200])).

fof(f1821,plain,(
    spl14_1 ),
    inference(avatar_split_clause,[],[f1687,f1805])).

fof(f1805,plain,
    ( spl14_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_1])])).

fof(f1687,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f1653])).

fof(f1653,plain,
    ( ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_2(sK2,sK0,sK1)
      | ~ v1_funct_1(sK2) )
    & sK0 = k1_relset_1(sK0,sK1,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f1582,f1652])).

fof(f1652,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2) )
        & k1_relset_1(X0,X1,X2) = X0
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
   => ( ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_2(sK2,sK0,sK1)
        | ~ v1_funct_1(sK2) )
      & sK0 = k1_relset_1(sK0,sK1,sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f1582,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2) )
      & k1_relset_1(X0,X1,X2) = X0
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f1581])).

fof(f1581,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2) )
      & k1_relset_1(X0,X1,X2) = X0
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1517])).

fof(f1517,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => ( k1_relset_1(X0,X1,X2) = X0
         => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X2,X0,X1)
            & v1_funct_1(X2) ) ) ) ),
    inference(negated_conjecture,[],[f1516])).

fof(f1516,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( k1_relset_1(X0,X1,X2) = X0
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_funct_2)).

fof(f1819,plain,(
    spl14_3 ),
    inference(avatar_split_clause,[],[f1688,f1811])).

fof(f1688,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f1653])).

fof(f1817,plain,(
    spl14_4 ),
    inference(avatar_split_clause,[],[f1689,f1815])).

fof(f1689,plain,(
    sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f1653])).

fof(f1813,plain,
    ( ~ spl14_1
    | ~ spl14_2
    | ~ spl14_3 ),
    inference(avatar_split_clause,[],[f1690,f1811,f1808,f1805])).

fof(f1690,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f1653])).
%------------------------------------------------------------------------------
