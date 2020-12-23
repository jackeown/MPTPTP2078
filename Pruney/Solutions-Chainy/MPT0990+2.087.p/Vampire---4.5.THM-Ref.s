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
% DateTime   : Thu Dec  3 13:02:43 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  236 ( 524 expanded)
%              Number of leaves         :   51 ( 188 expanded)
%              Depth                    :    9
%              Number of atoms          :  964 (2837 expanded)
%              Number of equality atoms :  167 ( 728 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1693,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f129,f131,f170,f174,f176,f178,f238,f241,f246,f309,f340,f370,f372,f374,f518,f543,f575,f580,f655,f657,f687,f780,f826,f841,f874,f901,f958,f1507,f1569,f1572,f1593,f1595,f1615,f1680])).

fof(f1680,plain,(
    ~ spl6_21 ),
    inference(avatar_contradiction_clause,[],[f1633])).

fof(f1633,plain,
    ( $false
    | ~ spl6_21 ),
    inference(subsumption_resolution,[],[f69,f352])).

fof(f352,plain,
    ( sK3 = k2_funct_1(sK2)
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f350])).

fof(f350,plain,
    ( spl6_21
  <=> sK3 = k2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f69,plain,(
    sK3 != k2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
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
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).

fof(f1615,plain,(
    ~ spl6_129 ),
    inference(avatar_contradiction_clause,[],[f1614])).

fof(f1614,plain,
    ( $false
    | ~ spl6_129 ),
    inference(subsumption_resolution,[],[f72,f1187])).

fof(f1187,plain,
    ( ! [X23] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X23)))
    | ~ spl6_129 ),
    inference(avatar_component_clause,[],[f1186])).

fof(f1186,plain,
    ( spl6_129
  <=> ! [X23] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X23))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_129])])).

fof(f72,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f24])).

fof(f1595,plain,
    ( ~ spl6_50
    | spl6_171
    | ~ spl6_179 ),
    inference(avatar_contradiction_clause,[],[f1594])).

fof(f1594,plain,
    ( $false
    | ~ spl6_50
    | spl6_171
    | ~ spl6_179 ),
    inference(subsumption_resolution,[],[f579,f1573])).

fof(f1573,plain,
    ( ~ v2_funct_1(k6_relat_1(sK0))
    | spl6_171
    | ~ spl6_179 ),
    inference(superposition,[],[f1506,f1564])).

fof(f1564,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl6_179 ),
    inference(avatar_component_clause,[],[f1562])).

fof(f1562,plain,
    ( spl6_179
  <=> k6_relat_1(sK0) = k5_relat_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_179])])).

fof(f1506,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | spl6_171 ),
    inference(avatar_component_clause,[],[f1504])).

fof(f1504,plain,
    ( spl6_171
  <=> v2_funct_1(k5_relat_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_171])])).

fof(f579,plain,
    ( v2_funct_1(k6_relat_1(sK0))
    | ~ spl6_50 ),
    inference(avatar_component_clause,[],[f577])).

fof(f577,plain,
    ( spl6_50
  <=> v2_funct_1(k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_50])])).

fof(f1593,plain,
    ( spl6_21
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_23
    | ~ spl6_73
    | ~ spl6_5
    | ~ spl6_85
    | ~ spl6_2
    | ~ spl6_47
    | ~ spl6_179 ),
    inference(avatar_split_clause,[],[f1592,f1562,f561,f125,f869,f163,f745,f363,f159,f155,f350])).

fof(f155,plain,
    ( spl6_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f159,plain,
    ( spl6_4
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f363,plain,
    ( spl6_23
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f745,plain,
    ( spl6_73
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_73])])).

fof(f163,plain,
    ( spl6_5
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f869,plain,
    ( spl6_85
  <=> sK1 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_85])])).

fof(f125,plain,
    ( spl6_2
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f561,plain,
    ( spl6_47
  <=> k6_relat_1(sK0) = k6_relat_1(k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_47])])).

fof(f1592,plain,
    ( sK1 != k1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | sK3 = k2_funct_1(sK2)
    | ~ spl6_2
    | ~ spl6_47
    | ~ spl6_179 ),
    inference(forward_demodulation,[],[f1591,f127])).

fof(f127,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f125])).

fof(f1591,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK2)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_relat_1(sK2)
    | sK3 = k2_funct_1(sK2)
    | ~ spl6_47
    | ~ spl6_179 ),
    inference(trivial_inequality_removal,[],[f1590])).

fof(f1590,plain,
    ( k6_relat_1(sK0) != k6_relat_1(sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK2)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_relat_1(sK2)
    | sK3 = k2_funct_1(sK2)
    | ~ spl6_47
    | ~ spl6_179 ),
    inference(forward_demodulation,[],[f1579,f563])).

fof(f563,plain,
    ( k6_relat_1(sK0) = k6_relat_1(k1_relat_1(sK2))
    | ~ spl6_47 ),
    inference(avatar_component_clause,[],[f561])).

fof(f1579,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK2)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_relat_1(sK2)
    | sK3 = k2_funct_1(sK2)
    | ~ spl6_179 ),
    inference(superposition,[],[f84,f1564])).

fof(f84,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X0)
      | k2_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k2_funct_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | k2_relat_1(X0) != k1_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | k2_relat_1(X0) != k1_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
              & k2_relat_1(X0) = k1_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_funct_1)).

fof(f1572,plain,(
    spl6_180 ),
    inference(avatar_contradiction_clause,[],[f1570])).

fof(f1570,plain,
    ( $false
    | spl6_180 ),
    inference(unit_resulting_resolution,[],[f70,f61,f63,f72,f1568,f385])).

fof(f385,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(duplicate_literal_removal,[],[f384])).

fof(f384,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(superposition,[],[f105,f103])).

fof(f103,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f105,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f1568,plain,
    ( ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl6_180 ),
    inference(avatar_component_clause,[],[f1566])).

fof(f1566,plain,
    ( spl6_180
  <=> m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_180])])).

fof(f63,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f24])).

fof(f61,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f70,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f1569,plain,
    ( spl6_129
    | spl6_179
    | ~ spl6_180
    | ~ spl6_19
    | ~ spl6_24
    | ~ spl6_87 ),
    inference(avatar_split_clause,[],[f1550,f899,f367,f337,f1566,f1562,f1186])).

fof(f337,plain,
    ( spl6_19
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f367,plain,
    ( spl6_24
  <=> r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f899,plain,
    ( spl6_87
  <=> ! [X16,X15,X17,X14] :
        ( m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(X14,X15)))
        | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X17,X15)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X14,X16))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_87])])).

fof(f1550,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) )
    | ~ spl6_19
    | ~ spl6_24
    | ~ spl6_87 ),
    inference(resolution,[],[f1132,f369])).

fof(f369,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f367])).

fof(f1132,plain,
    ( ! [X6,X4,X5] :
        ( ~ r2_relset_1(X4,sK0,X6,k6_relat_1(sK0))
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,sK0)))
        | k6_relat_1(sK0) = X6
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) )
    | ~ spl6_19
    | ~ spl6_87 ),
    inference(resolution,[],[f1129,f102])).

fof(f102,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f1129,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl6_19
    | ~ spl6_87 ),
    inference(resolution,[],[f900,f339])).

fof(f339,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f337])).

fof(f900,plain,
    ( ! [X14,X17,X15,X16] :
        ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X17,X15)))
        | m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(X14,X15)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X14,X16))) )
    | ~ spl6_87 ),
    inference(avatar_component_clause,[],[f899])).

fof(f1507,plain,
    ( spl6_63
    | spl6_62
    | ~ spl6_23
    | ~ spl6_171
    | ~ spl6_59
    | ~ spl6_95 ),
    inference(avatar_split_clause,[],[f1502,f956,f652,f1504,f363,f680,f684])).

fof(f684,plain,
    ( spl6_63
  <=> v2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_63])])).

fof(f680,plain,
    ( spl6_62
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_62])])).

fof(f652,plain,
    ( spl6_59
  <=> v1_funct_2(sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_59])])).

fof(f956,plain,
    ( spl6_95
  <=> ! [X1,X0] :
        ( ~ v2_funct_1(k5_relat_1(sK2,X1))
        | ~ v1_funct_2(X1,sK1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ v1_funct_1(X1)
        | k1_xboole_0 = X0
        | v2_funct_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_95])])).

fof(f1502,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | ~ v1_funct_1(sK3)
    | k1_xboole_0 = sK0
    | v2_funct_1(sK3)
    | ~ spl6_95 ),
    inference(resolution,[],[f957,f63])).

fof(f957,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ v1_funct_2(X1,sK1,X0)
        | ~ v2_funct_1(k5_relat_1(sK2,X1))
        | ~ v1_funct_1(X1)
        | k1_xboole_0 = X0
        | v2_funct_1(X1) )
    | ~ spl6_95 ),
    inference(avatar_component_clause,[],[f956])).

fof(f958,plain,
    ( ~ spl6_5
    | ~ spl6_1
    | spl6_95
    | ~ spl6_81 ),
    inference(avatar_split_clause,[],[f954,f824,f956,f121,f163])).

fof(f121,plain,
    ( spl6_1
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f824,plain,
    ( spl6_81
  <=> ! [X1,X0] :
        ( ~ v1_funct_1(X0)
        | v2_funct_1(X0)
        | k1_xboole_0 = X1
        | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
        | ~ v1_funct_2(X0,sK1,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_81])])).

fof(f954,plain,
    ( ! [X0,X1] :
        ( ~ v2_funct_1(k5_relat_1(sK2,X1))
        | v2_funct_1(X1)
        | k1_xboole_0 = X0
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ v1_funct_2(X1,sK1,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_1(sK2) )
    | ~ spl6_81 ),
    inference(duplicate_literal_removal,[],[f953])).

fof(f953,plain,
    ( ! [X0,X1] :
        ( ~ v2_funct_1(k5_relat_1(sK2,X1))
        | v2_funct_1(X1)
        | k1_xboole_0 = X0
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ v1_funct_2(X1,sK1,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ v1_funct_1(sK2) )
    | ~ spl6_81 ),
    inference(superposition,[],[f825,f103])).

fof(f825,plain,
    ( ! [X0,X1] :
        ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0))
        | v2_funct_1(X0)
        | k1_xboole_0 = X1
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
        | ~ v1_funct_2(X0,sK1,X1) )
    | ~ spl6_81 ),
    inference(avatar_component_clause,[],[f824])).

fof(f901,plain,
    ( ~ spl6_5
    | ~ spl6_13
    | spl6_87
    | ~ spl6_45 ),
    inference(avatar_split_clause,[],[f890,f515,f899,f232,f163])).

fof(f232,plain,
    ( spl6_13
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f515,plain,
    ( spl6_45
  <=> k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).

fof(f890,plain,
    ( ! [X14,X17,X15,X16] :
        ( m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(X14,X15)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X14,X16)))
        | ~ v1_funct_1(k2_funct_1(sK2))
        | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X17,X15)))
        | ~ v1_funct_1(sK2) )
    | ~ spl6_45 ),
    inference(superposition,[],[f385,f517])).

fof(f517,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ spl6_45 ),
    inference(avatar_component_clause,[],[f515])).

fof(f874,plain,
    ( ~ spl6_73
    | ~ spl6_63
    | ~ spl6_23
    | spl6_85
    | ~ spl6_6
    | ~ spl6_61 ),
    inference(avatar_split_clause,[],[f873,f676,f167,f869,f363,f684,f745])).

fof(f167,plain,
    ( spl6_6
  <=> sK1 = k1_relat_1(k6_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f676,plain,
    ( spl6_61
  <=> k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_61])])).

fof(f873,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl6_6
    | ~ spl6_61 ),
    inference(forward_demodulation,[],[f857,f169])).

fof(f169,plain,
    ( sK1 = k1_relat_1(k6_relat_1(sK1))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f167])).

fof(f857,plain,
    ( k1_relat_1(k6_relat_1(sK1)) = k1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl6_61 ),
    inference(superposition,[],[f79,f678])).

fof(f678,plain,
    ( k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ spl6_61 ),
    inference(avatar_component_clause,[],[f676])).

fof(f79,plain,(
    ! [X0] :
      ( k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          & k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_funct_1)).

fof(f841,plain,(
    spl6_73 ),
    inference(avatar_contradiction_clause,[],[f838])).

fof(f838,plain,
    ( $false
    | spl6_73 ),
    inference(subsumption_resolution,[],[f114,f747])).

fof(f747,plain,
    ( ~ v1_relat_1(sK3)
    | spl6_73 ),
    inference(avatar_component_clause,[],[f745])).

fof(f114,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f88,f63])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f826,plain,
    ( ~ spl6_5
    | spl6_81
    | ~ spl6_1
    | ~ spl6_17 ),
    inference(avatar_split_clause,[],[f822,f304,f121,f824,f163])).

fof(f304,plain,
    ( spl6_17
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f822,plain,(
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
    inference(trivial_inequality_removal,[],[f817])).

fof(f817,plain,(
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
    inference(superposition,[],[f100,f64])).

fof(f64,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f100,plain,(
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
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
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
    inference(flattening,[],[f53])).

fof(f53,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_funct_2)).

fof(f780,plain,(
    ~ spl6_62 ),
    inference(avatar_contradiction_clause,[],[f755])).

fof(f755,plain,
    ( $false
    | ~ spl6_62 ),
    inference(subsumption_resolution,[],[f67,f682])).

fof(f682,plain,
    ( k1_xboole_0 = sK0
    | ~ spl6_62 ),
    inference(avatar_component_clause,[],[f680])).

fof(f67,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f24])).

fof(f687,plain,
    ( spl6_61
    | spl6_62
    | ~ spl6_63
    | ~ spl6_23
    | ~ spl6_22
    | ~ spl6_59
    | ~ spl6_58 ),
    inference(avatar_split_clause,[],[f669,f648,f652,f359,f363,f684,f680,f676])).

fof(f359,plain,
    ( spl6_22
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f648,plain,
    ( spl6_58
  <=> sK0 = k2_relset_1(sK1,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_58])])).

fof(f669,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | k1_xboole_0 = sK0
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ spl6_58 ),
    inference(trivial_inequality_removal,[],[f659])).

fof(f659,plain,
    ( sK0 != sK0
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | k1_xboole_0 = sK0
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ spl6_58 ),
    inference(superposition,[],[f108,f650])).

fof(f650,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ spl6_58 ),
    inference(avatar_component_clause,[],[f648])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k1_xboole_0 = X1
      | k6_relat_1(X0) = k5_relat_1(X2,k2_funct_1(X2)) ) ),
    inference(definition_unfolding,[],[f94,f73])).

fof(f73,plain,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | k1_xboole_0 = X1
      | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
            & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).

fof(f657,plain,(
    spl6_59 ),
    inference(avatar_contradiction_clause,[],[f656])).

fof(f656,plain,
    ( $false
    | spl6_59 ),
    inference(subsumption_resolution,[],[f62,f654])).

fof(f654,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | spl6_59 ),
    inference(avatar_component_clause,[],[f652])).

fof(f62,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f655,plain,
    ( spl6_58
    | ~ spl6_23
    | ~ spl6_1
    | ~ spl6_17
    | ~ spl6_5
    | ~ spl6_22
    | ~ spl6_59 ),
    inference(avatar_split_clause,[],[f643,f652,f359,f163,f304,f121,f363,f648])).

fof(f643,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | sK0 = k2_relset_1(sK1,sK0,sK3) ),
    inference(resolution,[],[f109,f106])).

fof(f106,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) ),
    inference(definition_unfolding,[],[f65,f73])).

fof(f65,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f109,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_relat_1(X1))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X1,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_1(X2)
      | k2_relset_1(X0,X1,X2) = X1 ) ),
    inference(definition_unfolding,[],[f96,f73])).

fof(f96,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X1,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | k2_relset_1(X0,X1,X2) = X1 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
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
    inference(flattening,[],[f51])).

fof(f51,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).

fof(f580,plain,
    ( ~ spl6_3
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_11
    | ~ spl6_4
    | ~ spl6_5
    | spl6_50
    | ~ spl6_45 ),
    inference(avatar_split_clause,[],[f558,f515,f577,f163,f159,f224,f232,f228,f155])).

fof(f228,plain,
    ( spl6_12
  <=> v2_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f224,plain,
    ( spl6_11
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f558,plain,
    ( v2_funct_1(k6_relat_1(sK0))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl6_45 ),
    inference(superposition,[],[f86,f517])).

fof(f86,plain,(
    ! [X0,X1] :
      ( v2_funct_1(k5_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( v2_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( v2_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v2_funct_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X1)
        & v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_funct_1)).

fof(f575,plain,
    ( ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | spl6_47
    | ~ spl6_45 ),
    inference(avatar_split_clause,[],[f556,f515,f561,f163,f159,f155])).

fof(f556,plain,
    ( k6_relat_1(sK0) = k6_relat_1(k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl6_45 ),
    inference(superposition,[],[f77,f517])).

fof(f77,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

fof(f543,plain,(
    ~ spl6_35 ),
    inference(avatar_contradiction_clause,[],[f519])).

fof(f519,plain,
    ( $false
    | ~ spl6_35 ),
    inference(subsumption_resolution,[],[f68,f447])).

fof(f447,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_35 ),
    inference(avatar_component_clause,[],[f445])).

fof(f445,plain,
    ( spl6_35
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).

fof(f68,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f24])).

fof(f518,plain,
    ( spl6_45
    | spl6_35
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_1
    | ~ spl6_17 ),
    inference(avatar_split_clause,[],[f513,f304,f121,f163,f159,f445,f515])).

fof(f513,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k1_xboole_0 = sK1
    | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(trivial_inequality_removal,[],[f510])).

fof(f510,plain,
    ( sK1 != sK1
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k1_xboole_0 = sK1
    | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(superposition,[],[f108,f64])).

fof(f374,plain,(
    spl6_23 ),
    inference(avatar_contradiction_clause,[],[f373])).

fof(f373,plain,
    ( $false
    | spl6_23 ),
    inference(subsumption_resolution,[],[f61,f365])).

fof(f365,plain,
    ( ~ v1_funct_1(sK3)
    | spl6_23 ),
    inference(avatar_component_clause,[],[f363])).

fof(f372,plain,(
    spl6_22 ),
    inference(avatar_contradiction_clause,[],[f371])).

fof(f371,plain,
    ( $false
    | spl6_22 ),
    inference(subsumption_resolution,[],[f63,f361])).

fof(f361,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl6_22 ),
    inference(avatar_component_clause,[],[f359])).

fof(f370,plain,
    ( ~ spl6_5
    | ~ spl6_22
    | ~ spl6_23
    | ~ spl6_1
    | spl6_24 ),
    inference(avatar_split_clause,[],[f355,f367,f121,f363,f359,f163])).

fof(f355,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f106,f103])).

fof(f340,plain,
    ( spl6_19
    | ~ spl6_5
    | ~ spl6_4
    | ~ spl6_1
    | ~ spl6_17 ),
    inference(avatar_split_clause,[],[f335,f304,f121,f159,f163,f337])).

fof(f335,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(trivial_inequality_removal,[],[f332])).

fof(f332,plain,
    ( sK1 != sK1
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(superposition,[],[f93,f64])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

fof(f309,plain,(
    spl6_17 ),
    inference(avatar_contradiction_clause,[],[f308])).

fof(f308,plain,
    ( $false
    | spl6_17 ),
    inference(subsumption_resolution,[],[f71,f306])).

fof(f306,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | spl6_17 ),
    inference(avatar_component_clause,[],[f304])).

fof(f71,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f246,plain,(
    spl6_13 ),
    inference(avatar_contradiction_clause,[],[f244])).

fof(f244,plain,
    ( $false
    | spl6_13 ),
    inference(unit_resulting_resolution,[],[f115,f70,f234,f75])).

fof(f75,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f234,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | spl6_13 ),
    inference(avatar_component_clause,[],[f232])).

fof(f115,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f88,f72])).

fof(f241,plain,(
    spl6_12 ),
    inference(avatar_contradiction_clause,[],[f239])).

fof(f239,plain,
    ( $false
    | spl6_12 ),
    inference(unit_resulting_resolution,[],[f115,f66,f70,f230,f76])).

fof(f76,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => v2_funct_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_1)).

fof(f230,plain,
    ( ~ v2_funct_1(k2_funct_1(sK2))
    | spl6_12 ),
    inference(avatar_component_clause,[],[f228])).

fof(f66,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f238,plain,(
    spl6_11 ),
    inference(avatar_contradiction_clause,[],[f236])).

fof(f236,plain,
    ( $false
    | spl6_11 ),
    inference(unit_resulting_resolution,[],[f115,f70,f226,f74])).

fof(f74,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f226,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | spl6_11 ),
    inference(avatar_component_clause,[],[f224])).

fof(f178,plain,(
    spl6_5 ),
    inference(avatar_contradiction_clause,[],[f177])).

fof(f177,plain,
    ( $false
    | spl6_5 ),
    inference(subsumption_resolution,[],[f70,f165])).

fof(f165,plain,
    ( ~ v1_funct_1(sK2)
    | spl6_5 ),
    inference(avatar_component_clause,[],[f163])).

fof(f176,plain,(
    spl6_4 ),
    inference(avatar_contradiction_clause,[],[f175])).

fof(f175,plain,
    ( $false
    | spl6_4 ),
    inference(subsumption_resolution,[],[f66,f161])).

fof(f161,plain,
    ( ~ v2_funct_1(sK2)
    | spl6_4 ),
    inference(avatar_component_clause,[],[f159])).

fof(f174,plain,(
    spl6_3 ),
    inference(avatar_contradiction_clause,[],[f171])).

fof(f171,plain,
    ( $false
    | spl6_3 ),
    inference(subsumption_resolution,[],[f115,f157])).

fof(f157,plain,
    ( ~ v1_relat_1(sK2)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f155])).

fof(f170,plain,
    ( ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | spl6_6
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f148,f125,f167,f163,f159,f155])).

fof(f148,plain,
    ( sK1 = k1_relat_1(k6_relat_1(sK1))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl6_2 ),
    inference(superposition,[],[f145,f127])).

fof(f145,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k6_relat_1(k2_relat_1(X0)))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f142])).

fof(f142,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k6_relat_1(k2_relat_1(X0)))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f81,f78])).

fof(f78,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f81,plain,(
    ! [X0] :
      ( k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
          & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_funct_1)).

fof(f131,plain,(
    spl6_1 ),
    inference(avatar_contradiction_clause,[],[f130])).

fof(f130,plain,
    ( $false
    | spl6_1 ),
    inference(subsumption_resolution,[],[f72,f123])).

fof(f123,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f121])).

fof(f129,plain,
    ( ~ spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f119,f125,f121])).

fof(f119,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f64,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 14:10:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.22/0.48  % (21674)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.48  % (21682)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.51  % (21681)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.51  % (21665)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.51  % (21663)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.52  % (21662)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.52  % (21673)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.52  % (21666)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.53  % (21661)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.53  % (21664)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.54  % (21685)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.54  % (21668)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.54  % (21689)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.54  % (21676)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.54  % (21688)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.54  % (21686)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.55  % (21684)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.55  % (21671)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.55  % (21677)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.55  % (21678)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.55  % (21680)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.55  % (21677)Refutation not found, incomplete strategy% (21677)------------------------------
% 0.22/0.55  % (21677)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (21677)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (21677)Memory used [KB]: 10746
% 0.22/0.55  % (21677)Time elapsed: 0.149 s
% 0.22/0.55  % (21677)------------------------------
% 0.22/0.55  % (21677)------------------------------
% 0.22/0.55  % (21683)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.55  % (21691)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.55  % (21669)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.55  % (21675)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.56  % (21670)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.56  % (21672)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.56  % (21687)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.56  % (21667)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.56  % (21679)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.57  % (21674)Refutation found. Thanks to Tanya!
% 0.22/0.57  % SZS status Theorem for theBenchmark
% 0.22/0.59  % SZS output start Proof for theBenchmark
% 0.22/0.59  fof(f1693,plain,(
% 0.22/0.59    $false),
% 0.22/0.59    inference(avatar_sat_refutation,[],[f129,f131,f170,f174,f176,f178,f238,f241,f246,f309,f340,f370,f372,f374,f518,f543,f575,f580,f655,f657,f687,f780,f826,f841,f874,f901,f958,f1507,f1569,f1572,f1593,f1595,f1615,f1680])).
% 0.22/0.59  fof(f1680,plain,(
% 0.22/0.59    ~spl6_21),
% 0.22/0.59    inference(avatar_contradiction_clause,[],[f1633])).
% 0.22/0.59  fof(f1633,plain,(
% 0.22/0.59    $false | ~spl6_21),
% 0.22/0.59    inference(subsumption_resolution,[],[f69,f352])).
% 0.22/0.59  fof(f352,plain,(
% 0.22/0.59    sK3 = k2_funct_1(sK2) | ~spl6_21),
% 0.22/0.59    inference(avatar_component_clause,[],[f350])).
% 0.22/0.59  fof(f350,plain,(
% 0.22/0.59    spl6_21 <=> sK3 = k2_funct_1(sK2)),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 0.22/0.59  fof(f69,plain,(
% 0.22/0.59    sK3 != k2_funct_1(sK2)),
% 0.22/0.59    inference(cnf_transformation,[],[f24])).
% 0.22/0.59  fof(f24,plain,(
% 0.22/0.59    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.22/0.59    inference(flattening,[],[f23])).
% 0.22/0.59  fof(f23,plain,(
% 0.22/0.59    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.22/0.59    inference(ennf_transformation,[],[f22])).
% 0.22/0.59  fof(f22,negated_conjecture,(
% 0.22/0.59    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 0.22/0.59    inference(negated_conjecture,[],[f21])).
% 0.22/0.59  fof(f21,conjecture,(
% 0.22/0.59    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).
% 0.22/0.59  fof(f1615,plain,(
% 0.22/0.59    ~spl6_129),
% 0.22/0.59    inference(avatar_contradiction_clause,[],[f1614])).
% 0.22/0.59  fof(f1614,plain,(
% 0.22/0.59    $false | ~spl6_129),
% 0.22/0.59    inference(subsumption_resolution,[],[f72,f1187])).
% 0.22/0.59  fof(f1187,plain,(
% 0.22/0.59    ( ! [X23] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X23)))) ) | ~spl6_129),
% 0.22/0.59    inference(avatar_component_clause,[],[f1186])).
% 0.22/0.59  fof(f1186,plain,(
% 0.22/0.59    spl6_129 <=> ! [X23] : ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X23)))),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_129])])).
% 0.22/0.59  fof(f72,plain,(
% 0.22/0.59    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.59    inference(cnf_transformation,[],[f24])).
% 0.22/0.59  fof(f1595,plain,(
% 0.22/0.59    ~spl6_50 | spl6_171 | ~spl6_179),
% 0.22/0.59    inference(avatar_contradiction_clause,[],[f1594])).
% 0.22/0.59  fof(f1594,plain,(
% 0.22/0.59    $false | (~spl6_50 | spl6_171 | ~spl6_179)),
% 0.22/0.59    inference(subsumption_resolution,[],[f579,f1573])).
% 0.22/0.59  fof(f1573,plain,(
% 0.22/0.59    ~v2_funct_1(k6_relat_1(sK0)) | (spl6_171 | ~spl6_179)),
% 0.22/0.59    inference(superposition,[],[f1506,f1564])).
% 0.22/0.59  fof(f1564,plain,(
% 0.22/0.59    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | ~spl6_179),
% 0.22/0.59    inference(avatar_component_clause,[],[f1562])).
% 0.22/0.59  fof(f1562,plain,(
% 0.22/0.59    spl6_179 <=> k6_relat_1(sK0) = k5_relat_1(sK2,sK3)),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_179])])).
% 0.22/0.59  fof(f1506,plain,(
% 0.22/0.59    ~v2_funct_1(k5_relat_1(sK2,sK3)) | spl6_171),
% 0.22/0.59    inference(avatar_component_clause,[],[f1504])).
% 0.22/0.59  fof(f1504,plain,(
% 0.22/0.59    spl6_171 <=> v2_funct_1(k5_relat_1(sK2,sK3))),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_171])])).
% 0.22/0.59  fof(f579,plain,(
% 0.22/0.59    v2_funct_1(k6_relat_1(sK0)) | ~spl6_50),
% 0.22/0.59    inference(avatar_component_clause,[],[f577])).
% 0.22/0.59  fof(f577,plain,(
% 0.22/0.59    spl6_50 <=> v2_funct_1(k6_relat_1(sK0))),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_50])])).
% 0.22/0.59  fof(f1593,plain,(
% 0.22/0.59    spl6_21 | ~spl6_3 | ~spl6_4 | ~spl6_23 | ~spl6_73 | ~spl6_5 | ~spl6_85 | ~spl6_2 | ~spl6_47 | ~spl6_179),
% 0.22/0.59    inference(avatar_split_clause,[],[f1592,f1562,f561,f125,f869,f163,f745,f363,f159,f155,f350])).
% 0.22/0.59  fof(f155,plain,(
% 0.22/0.59    spl6_3 <=> v1_relat_1(sK2)),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.22/0.59  fof(f159,plain,(
% 0.22/0.59    spl6_4 <=> v2_funct_1(sK2)),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.22/0.59  fof(f363,plain,(
% 0.22/0.59    spl6_23 <=> v1_funct_1(sK3)),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 0.22/0.59  fof(f745,plain,(
% 0.22/0.59    spl6_73 <=> v1_relat_1(sK3)),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_73])])).
% 0.22/0.59  fof(f163,plain,(
% 0.22/0.59    spl6_5 <=> v1_funct_1(sK2)),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.22/0.59  fof(f869,plain,(
% 0.22/0.59    spl6_85 <=> sK1 = k1_relat_1(sK3)),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_85])])).
% 0.22/0.59  fof(f125,plain,(
% 0.22/0.59    spl6_2 <=> sK1 = k2_relat_1(sK2)),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.22/0.59  fof(f561,plain,(
% 0.22/0.59    spl6_47 <=> k6_relat_1(sK0) = k6_relat_1(k1_relat_1(sK2))),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_47])])).
% 0.22/0.59  fof(f1592,plain,(
% 0.22/0.59    sK1 != k1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | sK3 = k2_funct_1(sK2) | (~spl6_2 | ~spl6_47 | ~spl6_179)),
% 0.22/0.59    inference(forward_demodulation,[],[f1591,f127])).
% 0.22/0.59  fof(f127,plain,(
% 0.22/0.59    sK1 = k2_relat_1(sK2) | ~spl6_2),
% 0.22/0.59    inference(avatar_component_clause,[],[f125])).
% 0.22/0.59  fof(f1591,plain,(
% 0.22/0.59    ~v1_funct_1(sK2) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v2_funct_1(sK2) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v1_relat_1(sK2) | sK3 = k2_funct_1(sK2) | (~spl6_47 | ~spl6_179)),
% 0.22/0.59    inference(trivial_inequality_removal,[],[f1590])).
% 0.22/0.59  fof(f1590,plain,(
% 0.22/0.59    k6_relat_1(sK0) != k6_relat_1(sK0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v2_funct_1(sK2) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v1_relat_1(sK2) | sK3 = k2_funct_1(sK2) | (~spl6_47 | ~spl6_179)),
% 0.22/0.59    inference(forward_demodulation,[],[f1579,f563])).
% 0.22/0.59  fof(f563,plain,(
% 0.22/0.59    k6_relat_1(sK0) = k6_relat_1(k1_relat_1(sK2)) | ~spl6_47),
% 0.22/0.59    inference(avatar_component_clause,[],[f561])).
% 0.22/0.59  fof(f1579,plain,(
% 0.22/0.59    k6_relat_1(sK0) != k6_relat_1(k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v2_funct_1(sK2) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v1_relat_1(sK2) | sK3 = k2_funct_1(sK2) | ~spl6_179),
% 0.22/0.59    inference(superposition,[],[f84,f1564])).
% 0.22/0.59  fof(f84,plain,(
% 0.22/0.59    ( ! [X0,X1] : (k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(X0) | k2_relat_1(X0) != k1_relat_1(X1) | ~v1_relat_1(X0) | k2_funct_1(X0) = X1) )),
% 0.22/0.59    inference(cnf_transformation,[],[f38])).
% 0.22/0.59  fof(f38,plain,(
% 0.22/0.59    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | k2_relat_1(X0) != k1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.59    inference(flattening,[],[f37])).
% 0.22/0.59  fof(f37,plain,(
% 0.22/0.59    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | k2_relat_1(X0) != k1_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.59    inference(ennf_transformation,[],[f10])).
% 0.22/0.59  fof(f10,axiom,(
% 0.22/0.59    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_funct_1)).
% 0.22/0.59  fof(f1572,plain,(
% 0.22/0.59    spl6_180),
% 0.22/0.59    inference(avatar_contradiction_clause,[],[f1570])).
% 0.22/0.59  fof(f1570,plain,(
% 0.22/0.59    $false | spl6_180),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f70,f61,f63,f72,f1568,f385])).
% 0.22/0.59  fof(f385,plain,(
% 0.22/0.59    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 0.22/0.59    inference(duplicate_literal_removal,[],[f384])).
% 0.22/0.59  fof(f384,plain,(
% 0.22/0.59    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 0.22/0.59    inference(superposition,[],[f105,f103])).
% 0.22/0.59  fof(f103,plain,(
% 0.22/0.59    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f58])).
% 0.22/0.59  fof(f58,plain,(
% 0.22/0.59    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 0.22/0.59    inference(flattening,[],[f57])).
% 0.22/0.59  fof(f57,plain,(
% 0.22/0.59    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 0.22/0.59    inference(ennf_transformation,[],[f15])).
% 0.22/0.59  fof(f15,axiom,(
% 0.22/0.59    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 0.22/0.59  fof(f105,plain,(
% 0.22/0.59    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f60])).
% 0.22/0.59  fof(f60,plain,(
% 0.22/0.59    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 0.22/0.59    inference(flattening,[],[f59])).
% 0.22/0.59  fof(f59,plain,(
% 0.22/0.59    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 0.22/0.59    inference(ennf_transformation,[],[f14])).
% 0.22/0.59  fof(f14,axiom,(
% 0.22/0.59    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 0.22/0.59  fof(f1568,plain,(
% 0.22/0.59    ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl6_180),
% 0.22/0.59    inference(avatar_component_clause,[],[f1566])).
% 0.22/0.59  fof(f1566,plain,(
% 0.22/0.59    spl6_180 <=> m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_180])])).
% 0.22/0.59  fof(f63,plain,(
% 0.22/0.59    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.22/0.59    inference(cnf_transformation,[],[f24])).
% 0.22/0.59  fof(f61,plain,(
% 0.22/0.59    v1_funct_1(sK3)),
% 0.22/0.59    inference(cnf_transformation,[],[f24])).
% 0.22/0.59  fof(f70,plain,(
% 0.22/0.59    v1_funct_1(sK2)),
% 0.22/0.59    inference(cnf_transformation,[],[f24])).
% 0.22/0.59  fof(f1569,plain,(
% 0.22/0.59    spl6_129 | spl6_179 | ~spl6_180 | ~spl6_19 | ~spl6_24 | ~spl6_87),
% 0.22/0.59    inference(avatar_split_clause,[],[f1550,f899,f367,f337,f1566,f1562,f1186])).
% 0.22/0.59  fof(f337,plain,(
% 0.22/0.59    spl6_19 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 0.22/0.59  fof(f367,plain,(
% 0.22/0.59    spl6_24 <=> r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 0.22/0.59  fof(f899,plain,(
% 0.22/0.59    spl6_87 <=> ! [X16,X15,X17,X14] : (m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(X14,X15))) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X17,X15))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X14,X16))))),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_87])])).
% 0.22/0.59  fof(f1550,plain,(
% 0.22/0.59    ( ! [X1] : (~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))) ) | (~spl6_19 | ~spl6_24 | ~spl6_87)),
% 0.22/0.59    inference(resolution,[],[f1132,f369])).
% 0.22/0.59  fof(f369,plain,(
% 0.22/0.59    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | ~spl6_24),
% 0.22/0.59    inference(avatar_component_clause,[],[f367])).
% 0.22/0.59  fof(f1132,plain,(
% 0.22/0.59    ( ! [X6,X4,X5] : (~r2_relset_1(X4,sK0,X6,k6_relat_1(sK0)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,sK0))) | k6_relat_1(sK0) = X6 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))) ) | (~spl6_19 | ~spl6_87)),
% 0.22/0.59    inference(resolution,[],[f1129,f102])).
% 0.22/0.59  fof(f102,plain,(
% 0.22/0.59    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 = X3 | ~r2_relset_1(X0,X1,X2,X3)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f56])).
% 0.22/0.59  fof(f56,plain,(
% 0.22/0.59    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.59    inference(flattening,[],[f55])).
% 0.22/0.59  fof(f55,plain,(
% 0.22/0.59    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.22/0.59    inference(ennf_transformation,[],[f13])).
% 0.22/0.59  fof(f13,axiom,(
% 0.22/0.59    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 0.22/0.59  fof(f1129,plain,(
% 0.22/0.59    ( ! [X0,X1] : (m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | (~spl6_19 | ~spl6_87)),
% 0.22/0.59    inference(resolution,[],[f900,f339])).
% 0.22/0.59  fof(f339,plain,(
% 0.22/0.59    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl6_19),
% 0.22/0.59    inference(avatar_component_clause,[],[f337])).
% 0.22/0.59  fof(f900,plain,(
% 0.22/0.59    ( ! [X14,X17,X15,X16] : (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X17,X15))) | m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(X14,X15))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X14,X16)))) ) | ~spl6_87),
% 0.22/0.59    inference(avatar_component_clause,[],[f899])).
% 0.22/0.59  fof(f1507,plain,(
% 0.22/0.59    spl6_63 | spl6_62 | ~spl6_23 | ~spl6_171 | ~spl6_59 | ~spl6_95),
% 0.22/0.59    inference(avatar_split_clause,[],[f1502,f956,f652,f1504,f363,f680,f684])).
% 0.22/0.59  fof(f684,plain,(
% 0.22/0.59    spl6_63 <=> v2_funct_1(sK3)),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_63])])).
% 0.22/0.59  fof(f680,plain,(
% 0.22/0.59    spl6_62 <=> k1_xboole_0 = sK0),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_62])])).
% 0.22/0.59  fof(f652,plain,(
% 0.22/0.59    spl6_59 <=> v1_funct_2(sK3,sK1,sK0)),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_59])])).
% 0.22/0.59  fof(f956,plain,(
% 0.22/0.59    spl6_95 <=> ! [X1,X0] : (~v2_funct_1(k5_relat_1(sK2,X1)) | ~v1_funct_2(X1,sK1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_1(X1) | k1_xboole_0 = X0 | v2_funct_1(X1))),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_95])])).
% 0.22/0.59  fof(f1502,plain,(
% 0.22/0.59    ~v1_funct_2(sK3,sK1,sK0) | ~v2_funct_1(k5_relat_1(sK2,sK3)) | ~v1_funct_1(sK3) | k1_xboole_0 = sK0 | v2_funct_1(sK3) | ~spl6_95),
% 0.22/0.59    inference(resolution,[],[f957,f63])).
% 0.22/0.59  fof(f957,plain,(
% 0.22/0.59    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v2_funct_1(k5_relat_1(sK2,X1)) | ~v1_funct_1(X1) | k1_xboole_0 = X0 | v2_funct_1(X1)) ) | ~spl6_95),
% 0.22/0.59    inference(avatar_component_clause,[],[f956])).
% 0.22/0.59  fof(f958,plain,(
% 0.22/0.59    ~spl6_5 | ~spl6_1 | spl6_95 | ~spl6_81),
% 0.22/0.59    inference(avatar_split_clause,[],[f954,f824,f956,f121,f163])).
% 0.22/0.59  fof(f121,plain,(
% 0.22/0.59    spl6_1 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.22/0.59  fof(f824,plain,(
% 0.22/0.59    spl6_81 <=> ! [X1,X0] : (~v1_funct_1(X0) | v2_funct_1(X0) | k1_xboole_0 = X1 | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~v1_funct_2(X0,sK1,X1))),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_81])])).
% 0.22/0.59  fof(f954,plain,(
% 0.22/0.59    ( ! [X0,X1] : (~v2_funct_1(k5_relat_1(sK2,X1)) | v2_funct_1(X1) | k1_xboole_0 = X0 | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)) ) | ~spl6_81),
% 0.22/0.59    inference(duplicate_literal_removal,[],[f953])).
% 0.22/0.59  fof(f953,plain,(
% 0.22/0.59    ( ! [X0,X1] : (~v2_funct_1(k5_relat_1(sK2,X1)) | v2_funct_1(X1) | k1_xboole_0 = X0 | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_1(sK2)) ) | ~spl6_81),
% 0.22/0.59    inference(superposition,[],[f825,f103])).
% 0.22/0.59  fof(f825,plain,(
% 0.22/0.59    ( ! [X0,X1] : (~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0)) | v2_funct_1(X0) | k1_xboole_0 = X1 | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~v1_funct_2(X0,sK1,X1)) ) | ~spl6_81),
% 0.22/0.59    inference(avatar_component_clause,[],[f824])).
% 0.22/0.59  fof(f901,plain,(
% 0.22/0.59    ~spl6_5 | ~spl6_13 | spl6_87 | ~spl6_45),
% 0.22/0.59    inference(avatar_split_clause,[],[f890,f515,f899,f232,f163])).
% 0.22/0.59  fof(f232,plain,(
% 0.22/0.59    spl6_13 <=> v1_funct_1(k2_funct_1(sK2))),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.22/0.59  fof(f515,plain,(
% 0.22/0.59    spl6_45 <=> k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).
% 0.22/0.59  fof(f890,plain,(
% 0.22/0.59    ( ! [X14,X17,X15,X16] : (m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(X14,X15))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X14,X16))) | ~v1_funct_1(k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X17,X15))) | ~v1_funct_1(sK2)) ) | ~spl6_45),
% 0.22/0.59    inference(superposition,[],[f385,f517])).
% 0.22/0.59  fof(f517,plain,(
% 0.22/0.59    k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~spl6_45),
% 0.22/0.59    inference(avatar_component_clause,[],[f515])).
% 0.22/0.59  fof(f874,plain,(
% 0.22/0.59    ~spl6_73 | ~spl6_63 | ~spl6_23 | spl6_85 | ~spl6_6 | ~spl6_61),
% 0.22/0.59    inference(avatar_split_clause,[],[f873,f676,f167,f869,f363,f684,f745])).
% 0.22/0.59  fof(f167,plain,(
% 0.22/0.59    spl6_6 <=> sK1 = k1_relat_1(k6_relat_1(sK1))),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.22/0.59  fof(f676,plain,(
% 0.22/0.59    spl6_61 <=> k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_61])])).
% 0.22/0.59  fof(f873,plain,(
% 0.22/0.59    sK1 = k1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v2_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl6_6 | ~spl6_61)),
% 0.22/0.59    inference(forward_demodulation,[],[f857,f169])).
% 0.22/0.59  fof(f169,plain,(
% 0.22/0.59    sK1 = k1_relat_1(k6_relat_1(sK1)) | ~spl6_6),
% 0.22/0.59    inference(avatar_component_clause,[],[f167])).
% 0.22/0.59  fof(f857,plain,(
% 0.22/0.59    k1_relat_1(k6_relat_1(sK1)) = k1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v2_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl6_61),
% 0.22/0.59    inference(superposition,[],[f79,f678])).
% 0.22/0.59  fof(f678,plain,(
% 0.22/0.59    k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~spl6_61),
% 0.22/0.59    inference(avatar_component_clause,[],[f676])).
% 0.22/0.59  fof(f79,plain,(
% 0.22/0.59    ( ! [X0] : (k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f32])).
% 0.22/0.59  fof(f32,plain,(
% 0.22/0.59    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.59    inference(flattening,[],[f31])).
% 0.22/0.59  fof(f31,plain,(
% 0.22/0.59    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.59    inference(ennf_transformation,[],[f6])).
% 0.22/0.59  fof(f6,axiom,(
% 0.22/0.59    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0))))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_funct_1)).
% 0.22/0.59  fof(f841,plain,(
% 0.22/0.59    spl6_73),
% 0.22/0.59    inference(avatar_contradiction_clause,[],[f838])).
% 0.22/0.59  fof(f838,plain,(
% 0.22/0.59    $false | spl6_73),
% 0.22/0.59    inference(subsumption_resolution,[],[f114,f747])).
% 0.22/0.59  fof(f747,plain,(
% 0.22/0.59    ~v1_relat_1(sK3) | spl6_73),
% 0.22/0.59    inference(avatar_component_clause,[],[f745])).
% 0.22/0.59  fof(f114,plain,(
% 0.22/0.59    v1_relat_1(sK3)),
% 0.22/0.59    inference(resolution,[],[f88,f63])).
% 0.22/0.59  fof(f88,plain,(
% 0.22/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f43])).
% 0.22/0.59  fof(f43,plain,(
% 0.22/0.59    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.59    inference(ennf_transformation,[],[f11])).
% 0.22/0.59  fof(f11,axiom,(
% 0.22/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.59  fof(f826,plain,(
% 0.22/0.59    ~spl6_5 | spl6_81 | ~spl6_1 | ~spl6_17),
% 0.22/0.59    inference(avatar_split_clause,[],[f822,f304,f121,f824,f163])).
% 0.22/0.59  fof(f304,plain,(
% 0.22/0.59    spl6_17 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 0.22/0.59  fof(f822,plain,(
% 0.22/0.59    ( ! [X0,X1] : (~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(X0) | ~v1_funct_2(X0,sK1,X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0)) | ~v1_funct_1(sK2) | k1_xboole_0 = X1 | v2_funct_1(X0)) )),
% 0.22/0.59    inference(trivial_inequality_removal,[],[f817])).
% 0.22/0.59  fof(f817,plain,(
% 0.22/0.59    ( ! [X0,X1] : (sK1 != sK1 | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(X0) | ~v1_funct_2(X0,sK1,X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0)) | ~v1_funct_1(sK2) | k1_xboole_0 = X1 | v2_funct_1(X0)) )),
% 0.22/0.59    inference(superposition,[],[f100,f64])).
% 0.22/0.59  fof(f64,plain,(
% 0.22/0.59    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.22/0.59    inference(cnf_transformation,[],[f24])).
% 0.22/0.59  fof(f100,plain,(
% 0.22/0.59    ( ! [X4,X2,X0,X3,X1] : (k2_relset_1(X0,X1,X3) != X1 | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X1,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~v1_funct_1(X3) | k1_xboole_0 = X2 | v2_funct_1(X4)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f54])).
% 0.22/0.59  fof(f54,plain,(
% 0.22/0.59    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.22/0.59    inference(flattening,[],[f53])).
% 0.22/0.59  fof(f53,plain,(
% 0.22/0.59    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.22/0.59    inference(ennf_transformation,[],[f18])).
% 0.22/0.59  fof(f18,axiom,(
% 0.22/0.59    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_funct_2)).
% 0.22/0.59  fof(f780,plain,(
% 0.22/0.59    ~spl6_62),
% 0.22/0.59    inference(avatar_contradiction_clause,[],[f755])).
% 0.22/0.59  fof(f755,plain,(
% 0.22/0.59    $false | ~spl6_62),
% 0.22/0.59    inference(subsumption_resolution,[],[f67,f682])).
% 0.22/0.59  fof(f682,plain,(
% 0.22/0.59    k1_xboole_0 = sK0 | ~spl6_62),
% 0.22/0.59    inference(avatar_component_clause,[],[f680])).
% 0.22/0.59  fof(f67,plain,(
% 0.22/0.59    k1_xboole_0 != sK0),
% 0.22/0.59    inference(cnf_transformation,[],[f24])).
% 0.22/0.59  fof(f687,plain,(
% 0.22/0.59    spl6_61 | spl6_62 | ~spl6_63 | ~spl6_23 | ~spl6_22 | ~spl6_59 | ~spl6_58),
% 0.22/0.59    inference(avatar_split_clause,[],[f669,f648,f652,f359,f363,f684,f680,f676])).
% 0.22/0.59  fof(f359,plain,(
% 0.22/0.59    spl6_22 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 0.22/0.59  fof(f648,plain,(
% 0.22/0.59    spl6_58 <=> sK0 = k2_relset_1(sK1,sK0,sK3)),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_58])])).
% 0.22/0.59  fof(f669,plain,(
% 0.22/0.59    ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~v2_funct_1(sK3) | k1_xboole_0 = sK0 | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~spl6_58),
% 0.22/0.59    inference(trivial_inequality_removal,[],[f659])).
% 0.22/0.59  fof(f659,plain,(
% 0.22/0.59    sK0 != sK0 | ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~v2_funct_1(sK3) | k1_xboole_0 = sK0 | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~spl6_58),
% 0.22/0.59    inference(superposition,[],[f108,f650])).
% 0.22/0.59  fof(f650,plain,(
% 0.22/0.59    sK0 = k2_relset_1(sK1,sK0,sK3) | ~spl6_58),
% 0.22/0.59    inference(avatar_component_clause,[],[f648])).
% 0.22/0.59  fof(f108,plain,(
% 0.22/0.59    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v2_funct_1(X2) | k1_xboole_0 = X1 | k6_relat_1(X0) = k5_relat_1(X2,k2_funct_1(X2))) )),
% 0.22/0.59    inference(definition_unfolding,[],[f94,f73])).
% 0.22/0.59  fof(f73,plain,(
% 0.22/0.59    ( ! [X0] : (k6_partfun1(X0) = k6_relat_1(X0)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f16])).
% 0.22/0.59  fof(f16,axiom,(
% 0.22/0.59    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0)),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.22/0.59  fof(f94,plain,(
% 0.22/0.59    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | k1_xboole_0 = X1 | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) )),
% 0.22/0.59    inference(cnf_transformation,[],[f50])).
% 0.22/0.59  fof(f50,plain,(
% 0.22/0.59    ! [X0,X1,X2] : ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.59    inference(flattening,[],[f49])).
% 0.22/0.59  fof(f49,plain,(
% 0.22/0.59    ! [X0,X1,X2] : ((((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.22/0.59    inference(ennf_transformation,[],[f20])).
% 0.22/0.59  fof(f20,axiom,(
% 0.22/0.59    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).
% 0.22/0.59  fof(f657,plain,(
% 0.22/0.59    spl6_59),
% 0.22/0.59    inference(avatar_contradiction_clause,[],[f656])).
% 0.22/0.59  fof(f656,plain,(
% 0.22/0.59    $false | spl6_59),
% 0.22/0.59    inference(subsumption_resolution,[],[f62,f654])).
% 0.22/0.59  fof(f654,plain,(
% 0.22/0.59    ~v1_funct_2(sK3,sK1,sK0) | spl6_59),
% 0.22/0.59    inference(avatar_component_clause,[],[f652])).
% 0.22/0.59  fof(f62,plain,(
% 0.22/0.59    v1_funct_2(sK3,sK1,sK0)),
% 0.22/0.59    inference(cnf_transformation,[],[f24])).
% 0.22/0.59  fof(f655,plain,(
% 0.22/0.59    spl6_58 | ~spl6_23 | ~spl6_1 | ~spl6_17 | ~spl6_5 | ~spl6_22 | ~spl6_59),
% 0.22/0.59    inference(avatar_split_clause,[],[f643,f652,f359,f163,f304,f121,f363,f648])).
% 0.22/0.59  fof(f643,plain,(
% 0.22/0.59    ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | sK0 = k2_relset_1(sK1,sK0,sK3)),
% 0.22/0.59    inference(resolution,[],[f109,f106])).
% 0.22/0.59  fof(f106,plain,(
% 0.22/0.59    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))),
% 0.22/0.59    inference(definition_unfolding,[],[f65,f73])).
% 0.22/0.59  fof(f65,plain,(
% 0.22/0.59    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 0.22/0.59    inference(cnf_transformation,[],[f24])).
% 0.22/0.59  fof(f109,plain,(
% 0.22/0.59    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_relat_1(X1)) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(X2) | k2_relset_1(X0,X1,X2) = X1) )),
% 0.22/0.59    inference(definition_unfolding,[],[f96,f73])).
% 0.22/0.59  fof(f96,plain,(
% 0.22/0.59    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | k2_relset_1(X0,X1,X2) = X1) )),
% 0.22/0.59    inference(cnf_transformation,[],[f52])).
% 0.22/0.59  fof(f52,plain,(
% 0.22/0.59    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.59    inference(flattening,[],[f51])).
% 0.22/0.59  fof(f51,plain,(
% 0.22/0.59    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.22/0.59    inference(ennf_transformation,[],[f17])).
% 0.22/0.59  fof(f17,axiom,(
% 0.22/0.59    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).
% 0.22/0.59  fof(f580,plain,(
% 0.22/0.59    ~spl6_3 | ~spl6_12 | ~spl6_13 | ~spl6_11 | ~spl6_4 | ~spl6_5 | spl6_50 | ~spl6_45),
% 0.22/0.59    inference(avatar_split_clause,[],[f558,f515,f577,f163,f159,f224,f232,f228,f155])).
% 0.22/0.59  fof(f228,plain,(
% 0.22/0.59    spl6_12 <=> v2_funct_1(k2_funct_1(sK2))),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.22/0.59  fof(f224,plain,(
% 0.22/0.59    spl6_11 <=> v1_relat_1(k2_funct_1(sK2))),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.22/0.59  fof(f558,plain,(
% 0.22/0.59    v2_funct_1(k6_relat_1(sK0)) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | ~v2_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2) | ~spl6_45),
% 0.22/0.59    inference(superposition,[],[f86,f517])).
% 0.22/0.59  fof(f86,plain,(
% 0.22/0.59    ( ! [X0,X1] : (v2_funct_1(k5_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f40])).
% 0.22/0.59  fof(f40,plain,(
% 0.22/0.59    ! [X0,X1] : ((v2_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.59    inference(flattening,[],[f39])).
% 0.22/0.59  fof(f39,plain,(
% 0.22/0.59    ! [X0,X1] : ((v2_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))) | (~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.59    inference(ennf_transformation,[],[f2])).
% 0.22/0.59  fof(f2,axiom,(
% 0.22/0.59    ! [X0,X1] : ((v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_funct_1)).
% 0.22/0.59  fof(f575,plain,(
% 0.22/0.59    ~spl6_3 | ~spl6_4 | ~spl6_5 | spl6_47 | ~spl6_45),
% 0.22/0.59    inference(avatar_split_clause,[],[f556,f515,f561,f163,f159,f155])).
% 0.22/0.59  fof(f556,plain,(
% 0.22/0.59    k6_relat_1(sK0) = k6_relat_1(k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl6_45),
% 0.22/0.59    inference(superposition,[],[f77,f517])).
% 0.22/0.59  fof(f77,plain,(
% 0.22/0.59    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f30])).
% 0.22/0.59  fof(f30,plain,(
% 0.22/0.59    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.59    inference(flattening,[],[f29])).
% 0.22/0.59  fof(f29,plain,(
% 0.22/0.59    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.59    inference(ennf_transformation,[],[f8])).
% 0.22/0.59  fof(f8,axiom,(
% 0.22/0.59    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).
% 0.22/0.59  fof(f543,plain,(
% 0.22/0.59    ~spl6_35),
% 0.22/0.59    inference(avatar_contradiction_clause,[],[f519])).
% 0.22/0.59  fof(f519,plain,(
% 0.22/0.59    $false | ~spl6_35),
% 0.22/0.59    inference(subsumption_resolution,[],[f68,f447])).
% 0.22/0.59  fof(f447,plain,(
% 0.22/0.59    k1_xboole_0 = sK1 | ~spl6_35),
% 0.22/0.59    inference(avatar_component_clause,[],[f445])).
% 0.22/0.59  fof(f445,plain,(
% 0.22/0.59    spl6_35 <=> k1_xboole_0 = sK1),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).
% 0.22/0.59  fof(f68,plain,(
% 0.22/0.59    k1_xboole_0 != sK1),
% 0.22/0.59    inference(cnf_transformation,[],[f24])).
% 0.22/0.59  fof(f518,plain,(
% 0.22/0.59    spl6_45 | spl6_35 | ~spl6_4 | ~spl6_5 | ~spl6_1 | ~spl6_17),
% 0.22/0.59    inference(avatar_split_clause,[],[f513,f304,f121,f163,f159,f445,f515])).
% 0.22/0.59  fof(f513,plain,(
% 0.22/0.59    ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k1_xboole_0 = sK1 | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 0.22/0.59    inference(trivial_inequality_removal,[],[f510])).
% 0.22/0.59  fof(f510,plain,(
% 0.22/0.59    sK1 != sK1 | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k1_xboole_0 = sK1 | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 0.22/0.59    inference(superposition,[],[f108,f64])).
% 0.22/0.59  fof(f374,plain,(
% 0.22/0.59    spl6_23),
% 0.22/0.59    inference(avatar_contradiction_clause,[],[f373])).
% 0.22/0.59  fof(f373,plain,(
% 0.22/0.59    $false | spl6_23),
% 0.22/0.59    inference(subsumption_resolution,[],[f61,f365])).
% 0.22/0.59  fof(f365,plain,(
% 0.22/0.59    ~v1_funct_1(sK3) | spl6_23),
% 0.22/0.59    inference(avatar_component_clause,[],[f363])).
% 0.22/0.59  fof(f372,plain,(
% 0.22/0.59    spl6_22),
% 0.22/0.59    inference(avatar_contradiction_clause,[],[f371])).
% 0.22/0.59  fof(f371,plain,(
% 0.22/0.59    $false | spl6_22),
% 0.22/0.59    inference(subsumption_resolution,[],[f63,f361])).
% 0.22/0.59  fof(f361,plain,(
% 0.22/0.59    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl6_22),
% 0.22/0.59    inference(avatar_component_clause,[],[f359])).
% 0.22/0.59  fof(f370,plain,(
% 0.22/0.59    ~spl6_5 | ~spl6_22 | ~spl6_23 | ~spl6_1 | spl6_24),
% 0.22/0.59    inference(avatar_split_clause,[],[f355,f367,f121,f363,f359,f163])).
% 0.22/0.59  fof(f355,plain,(
% 0.22/0.59    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2)),
% 0.22/0.59    inference(superposition,[],[f106,f103])).
% 0.22/0.59  fof(f340,plain,(
% 0.22/0.59    spl6_19 | ~spl6_5 | ~spl6_4 | ~spl6_1 | ~spl6_17),
% 0.22/0.59    inference(avatar_split_clause,[],[f335,f304,f121,f159,f163,f337])).
% 0.22/0.59  fof(f335,plain,(
% 0.22/0.59    ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.22/0.59    inference(trivial_inequality_removal,[],[f332])).
% 0.22/0.59  fof(f332,plain,(
% 0.22/0.59    sK1 != sK1 | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.22/0.59    inference(superposition,[],[f93,f64])).
% 0.22/0.59  fof(f93,plain,(
% 0.22/0.59    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 0.22/0.59    inference(cnf_transformation,[],[f48])).
% 0.22/0.59  fof(f48,plain,(
% 0.22/0.59    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.59    inference(flattening,[],[f47])).
% 0.22/0.59  fof(f47,plain,(
% 0.22/0.59    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.22/0.59    inference(ennf_transformation,[],[f19])).
% 0.22/0.59  fof(f19,axiom,(
% 0.22/0.59    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 0.22/0.59  fof(f309,plain,(
% 0.22/0.59    spl6_17),
% 0.22/0.59    inference(avatar_contradiction_clause,[],[f308])).
% 0.22/0.59  fof(f308,plain,(
% 0.22/0.59    $false | spl6_17),
% 0.22/0.59    inference(subsumption_resolution,[],[f71,f306])).
% 0.22/0.59  fof(f306,plain,(
% 0.22/0.59    ~v1_funct_2(sK2,sK0,sK1) | spl6_17),
% 0.22/0.59    inference(avatar_component_clause,[],[f304])).
% 0.22/0.59  fof(f71,plain,(
% 0.22/0.59    v1_funct_2(sK2,sK0,sK1)),
% 0.22/0.59    inference(cnf_transformation,[],[f24])).
% 0.22/0.59  fof(f246,plain,(
% 0.22/0.59    spl6_13),
% 0.22/0.59    inference(avatar_contradiction_clause,[],[f244])).
% 0.22/0.59  fof(f244,plain,(
% 0.22/0.59    $false | spl6_13),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f115,f70,f234,f75])).
% 0.22/0.59  fof(f75,plain,(
% 0.22/0.59    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f26])).
% 0.22/0.59  fof(f26,plain,(
% 0.22/0.59    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.59    inference(flattening,[],[f25])).
% 0.22/0.59  fof(f25,plain,(
% 0.22/0.59    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.59    inference(ennf_transformation,[],[f1])).
% 0.22/0.59  fof(f1,axiom,(
% 0.22/0.59    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.22/0.59  fof(f234,plain,(
% 0.22/0.59    ~v1_funct_1(k2_funct_1(sK2)) | spl6_13),
% 0.22/0.59    inference(avatar_component_clause,[],[f232])).
% 0.22/0.59  fof(f115,plain,(
% 0.22/0.59    v1_relat_1(sK2)),
% 0.22/0.59    inference(resolution,[],[f88,f72])).
% 0.22/0.59  fof(f241,plain,(
% 0.22/0.59    spl6_12),
% 0.22/0.59    inference(avatar_contradiction_clause,[],[f239])).
% 0.22/0.59  fof(f239,plain,(
% 0.22/0.59    $false | spl6_12),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f115,f66,f70,f230,f76])).
% 0.22/0.59  fof(f76,plain,(
% 0.22/0.59    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f28])).
% 0.22/0.59  fof(f28,plain,(
% 0.22/0.59    ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.59    inference(flattening,[],[f27])).
% 0.22/0.59  fof(f27,plain,(
% 0.22/0.59    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.59    inference(ennf_transformation,[],[f9])).
% 0.22/0.59  fof(f9,axiom,(
% 0.22/0.59    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => v2_funct_1(k2_funct_1(X0))))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_1)).
% 0.22/0.59  fof(f230,plain,(
% 0.22/0.59    ~v2_funct_1(k2_funct_1(sK2)) | spl6_12),
% 0.22/0.59    inference(avatar_component_clause,[],[f228])).
% 0.22/0.59  fof(f66,plain,(
% 0.22/0.59    v2_funct_1(sK2)),
% 0.22/0.59    inference(cnf_transformation,[],[f24])).
% 0.22/0.59  fof(f238,plain,(
% 0.22/0.59    spl6_11),
% 0.22/0.59    inference(avatar_contradiction_clause,[],[f236])).
% 0.22/0.59  fof(f236,plain,(
% 0.22/0.59    $false | spl6_11),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f115,f70,f226,f74])).
% 0.22/0.59  fof(f74,plain,(
% 0.22/0.59    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f26])).
% 0.22/0.59  fof(f226,plain,(
% 0.22/0.59    ~v1_relat_1(k2_funct_1(sK2)) | spl6_11),
% 0.22/0.59    inference(avatar_component_clause,[],[f224])).
% 0.22/0.59  fof(f178,plain,(
% 0.22/0.59    spl6_5),
% 0.22/0.59    inference(avatar_contradiction_clause,[],[f177])).
% 0.22/0.59  fof(f177,plain,(
% 0.22/0.59    $false | spl6_5),
% 0.22/0.59    inference(subsumption_resolution,[],[f70,f165])).
% 0.22/0.59  fof(f165,plain,(
% 0.22/0.59    ~v1_funct_1(sK2) | spl6_5),
% 0.22/0.59    inference(avatar_component_clause,[],[f163])).
% 0.22/0.59  fof(f176,plain,(
% 0.22/0.59    spl6_4),
% 0.22/0.59    inference(avatar_contradiction_clause,[],[f175])).
% 0.22/0.59  fof(f175,plain,(
% 0.22/0.59    $false | spl6_4),
% 0.22/0.59    inference(subsumption_resolution,[],[f66,f161])).
% 0.22/0.59  fof(f161,plain,(
% 0.22/0.59    ~v2_funct_1(sK2) | spl6_4),
% 0.22/0.59    inference(avatar_component_clause,[],[f159])).
% 0.22/0.59  fof(f174,plain,(
% 0.22/0.59    spl6_3),
% 0.22/0.59    inference(avatar_contradiction_clause,[],[f171])).
% 0.22/0.59  fof(f171,plain,(
% 0.22/0.59    $false | spl6_3),
% 0.22/0.59    inference(subsumption_resolution,[],[f115,f157])).
% 0.22/0.59  fof(f157,plain,(
% 0.22/0.59    ~v1_relat_1(sK2) | spl6_3),
% 0.22/0.59    inference(avatar_component_clause,[],[f155])).
% 0.22/0.59  fof(f170,plain,(
% 0.22/0.59    ~spl6_3 | ~spl6_4 | ~spl6_5 | spl6_6 | ~spl6_2),
% 0.22/0.59    inference(avatar_split_clause,[],[f148,f125,f167,f163,f159,f155])).
% 0.22/0.59  fof(f148,plain,(
% 0.22/0.59    sK1 = k1_relat_1(k6_relat_1(sK1)) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl6_2),
% 0.22/0.59    inference(superposition,[],[f145,f127])).
% 0.22/0.59  fof(f145,plain,(
% 0.22/0.59    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k6_relat_1(k2_relat_1(X0))) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.59    inference(duplicate_literal_removal,[],[f142])).
% 0.22/0.59  fof(f142,plain,(
% 0.22/0.59    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k6_relat_1(k2_relat_1(X0))) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.59    inference(superposition,[],[f81,f78])).
% 0.22/0.59  fof(f78,plain,(
% 0.22/0.59    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f30])).
% 0.22/0.59  fof(f81,plain,(
% 0.22/0.59    ( ! [X0] : (k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f34])).
% 0.22/0.59  fof(f34,plain,(
% 0.22/0.59    ! [X0] : ((k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.59    inference(flattening,[],[f33])).
% 0.22/0.59  fof(f33,plain,(
% 0.22/0.59    ! [X0] : (((k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.59    inference(ennf_transformation,[],[f7])).
% 0.22/0.59  fof(f7,axiom,(
% 0.22/0.59    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0))))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_funct_1)).
% 0.22/0.59  fof(f131,plain,(
% 0.22/0.59    spl6_1),
% 0.22/0.59    inference(avatar_contradiction_clause,[],[f130])).
% 0.22/0.59  fof(f130,plain,(
% 0.22/0.59    $false | spl6_1),
% 0.22/0.59    inference(subsumption_resolution,[],[f72,f123])).
% 0.22/0.59  fof(f123,plain,(
% 0.22/0.59    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl6_1),
% 0.22/0.59    inference(avatar_component_clause,[],[f121])).
% 0.22/0.59  fof(f129,plain,(
% 0.22/0.59    ~spl6_1 | spl6_2),
% 0.22/0.59    inference(avatar_split_clause,[],[f119,f125,f121])).
% 0.22/0.59  fof(f119,plain,(
% 0.22/0.59    sK1 = k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.59    inference(superposition,[],[f64,f89])).
% 0.22/0.59  fof(f89,plain,(
% 0.22/0.59    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.59    inference(cnf_transformation,[],[f44])).
% 0.22/0.59  fof(f44,plain,(
% 0.22/0.59    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.59    inference(ennf_transformation,[],[f12])).
% 0.22/0.59  fof(f12,axiom,(
% 0.22/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.22/0.59  % SZS output end Proof for theBenchmark
% 0.22/0.59  % (21674)------------------------------
% 0.22/0.59  % (21674)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.59  % (21674)Termination reason: Refutation
% 0.22/0.60  
% 0.22/0.60  % (21674)Memory used [KB]: 8443
% 0.22/0.60  % (21674)Time elapsed: 0.149 s
% 0.22/0.60  % (21674)------------------------------
% 0.22/0.60  % (21674)------------------------------
% 0.22/0.60  % (21659)Success in time 0.237 s
%------------------------------------------------------------------------------
