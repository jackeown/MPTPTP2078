%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:43 EST 2020

% Result     : Theorem 1.57s
% Output     : Refutation 1.57s
% Verified   : 
% Statistics : Number of formulae       :  242 ( 527 expanded)
%              Number of leaves         :   51 ( 181 expanded)
%              Depth                    :   12
%              Number of atoms          :  765 (2370 expanded)
%              Number of equality atoms :  159 ( 304 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1069,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f187,f200,f202,f215,f220,f222,f224,f226,f285,f297,f301,f329,f331,f403,f417,f419,f497,f503,f524,f645,f670,f677,f699,f704,f711,f714,f728,f812,f828,f844,f853,f854,f860,f1062,f1068])).

fof(f1068,plain,
    ( ~ spl3_27
    | ~ spl3_31
    | spl3_37 ),
    inference(avatar_contradiction_clause,[],[f1067])).

fof(f1067,plain,
    ( $false
    | ~ spl3_27
    | ~ spl3_31
    | spl3_37 ),
    inference(subsumption_resolution,[],[f58,f1047])).

fof(f1047,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | ~ spl3_27
    | ~ spl3_31
    | spl3_37 ),
    inference(forward_demodulation,[],[f1046,f317])).

fof(f317,plain,
    ( k1_xboole_0 = sK0
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f315])).

fof(f315,plain,
    ( spl3_27
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f1046,plain,
    ( k1_relat_1(k1_xboole_0) != sK0
    | ~ spl3_31
    | spl3_37 ),
    inference(forward_demodulation,[],[f400,f359])).

fof(f359,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_31 ),
    inference(avatar_component_clause,[],[f357])).

fof(f357,plain,
    ( spl3_31
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f400,plain,
    ( sK0 != k1_relat_1(sK1)
    | spl3_37 ),
    inference(avatar_component_clause,[],[f399])).

fof(f399,plain,
    ( spl3_37
  <=> sK0 = k1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).

fof(f58,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f1062,plain,
    ( ~ spl3_27
    | spl3_29
    | ~ spl3_34 ),
    inference(avatar_contradiction_clause,[],[f1055])).

fof(f1055,plain,
    ( $false
    | ~ spl3_27
    | spl3_29
    | ~ spl3_34 ),
    inference(unit_resulting_resolution,[],[f249,f60,f1036,f94])).

fof(f94,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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

fof(f1036,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl3_27
    | spl3_29
    | ~ spl3_34 ),
    inference(forward_demodulation,[],[f1035,f317])).

fof(f1035,plain,
    ( sK0 != k1_relset_1(sK0,sK0,k1_xboole_0)
    | spl3_29
    | ~ spl3_34 ),
    inference(forward_demodulation,[],[f325,f374])).

fof(f374,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_34 ),
    inference(avatar_component_clause,[],[f372])).

fof(f372,plain,
    ( spl3_34
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f325,plain,
    ( sK0 != k1_relset_1(sK0,sK0,sK2)
    | spl3_29 ),
    inference(avatar_component_clause,[],[f324])).

fof(f324,plain,
    ( spl3_29
  <=> sK0 = k1_relset_1(sK0,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f60,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f249,plain,(
    ! [X0] : v1_funct_2(k1_xboole_0,k1_xboole_0,X0) ),
    inference(resolution,[],[f248,f60])).

fof(f248,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      | v1_funct_2(k1_xboole_0,k1_xboole_0,X0) ) ),
    inference(trivial_inequality_removal,[],[f247])).

fof(f247,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_xboole_0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      | v1_funct_2(k1_xboole_0,k1_xboole_0,X0) ) ),
    inference(superposition,[],[f244,f58])).

fof(f244,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(duplicate_literal_removal,[],[f243])).

fof(f243,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(superposition,[],[f95,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f95,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f860,plain,
    ( ~ spl3_28
    | spl3_29
    | spl3_27 ),
    inference(avatar_split_clause,[],[f509,f315,f324,f320])).

fof(f320,plain,
    ( spl3_28
  <=> v1_funct_2(sK2,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f509,plain,
    ( k1_xboole_0 = sK0
    | sK0 = k1_relset_1(sK0,sK0,sK2)
    | ~ v1_funct_2(sK2,sK0,sK0) ),
    inference(resolution,[],[f51,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f51,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X2,X0,X0)
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X2,X0,X0)
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X1,X0,X0)
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v3_funct_2(X2,X0,X0)
              & v1_funct_2(X2,X0,X0)
              & v1_funct_1(X2) )
           => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
             => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v3_funct_2(X2,X0,X0)
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
         => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
           => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_funct_2)).

fof(f854,plain,
    ( spl3_31
    | ~ spl3_20
    | ~ spl3_27
    | ~ spl3_61 ),
    inference(avatar_split_clause,[],[f732,f696,f315,f262,f357])).

fof(f262,plain,
    ( spl3_20
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f696,plain,
    ( spl3_61
  <=> sK0 = k2_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_61])])).

fof(f732,plain,
    ( k1_xboole_0 != sK0
    | ~ v1_relat_1(sK1)
    | k1_xboole_0 = sK1
    | ~ spl3_61 ),
    inference(superposition,[],[f65,f697])).

fof(f697,plain,
    ( sK0 = k2_relat_1(sK1)
    | ~ spl3_61 ),
    inference(avatar_component_clause,[],[f696])).

fof(f65,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f853,plain,
    ( spl3_34
    | ~ spl3_23
    | ~ spl3_27
    | ~ spl3_77 ),
    inference(avatar_split_clause,[],[f840,f809,f315,f274,f372])).

fof(f274,plain,
    ( spl3_23
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f809,plain,
    ( spl3_77
  <=> sK0 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_77])])).

fof(f840,plain,
    ( k1_xboole_0 != sK0
    | ~ v1_relat_1(sK2)
    | k1_xboole_0 = sK2
    | ~ spl3_77 ),
    inference(superposition,[],[f65,f810])).

fof(f810,plain,
    ( sK0 = k2_relat_1(sK2)
    | ~ spl3_77 ),
    inference(avatar_component_clause,[],[f809])).

fof(f844,plain,
    ( ~ spl3_40
    | ~ spl3_76 ),
    inference(avatar_contradiction_clause,[],[f841])).

fof(f841,plain,
    ( $false
    | ~ spl3_40
    | ~ spl3_76 ),
    inference(subsumption_resolution,[],[f143,f829])).

fof(f829,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,sK2)
    | ~ spl3_40
    | ~ spl3_76 ),
    inference(superposition,[],[f530,f807])).

fof(f807,plain,
    ( sK2 = k2_funct_1(sK1)
    | ~ spl3_76 ),
    inference(avatar_component_clause,[],[f805])).

fof(f805,plain,
    ( spl3_76
  <=> sK2 = k2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_76])])).

fof(f530,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1))
    | ~ spl3_40 ),
    inference(superposition,[],[f53,f523])).

fof(f523,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ spl3_40 ),
    inference(avatar_component_clause,[],[f521])).

fof(f521,plain,
    ( spl3_40
  <=> k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).

fof(f53,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f143,plain,(
    r2_relset_1(sK0,sK0,sK2,sK2) ),
    inference(resolution,[],[f100,f51])).

fof(f100,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f99])).

fof(f99,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 != X3
      | r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f828,plain,
    ( ~ spl3_16
    | spl3_77 ),
    inference(avatar_contradiction_clause,[],[f826])).

fof(f826,plain,
    ( $false
    | ~ spl3_16
    | spl3_77 ),
    inference(unit_resulting_resolution,[],[f104,f219,f114,f811,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

fof(f811,plain,
    ( sK0 != k2_relat_1(sK2)
    | spl3_77 ),
    inference(avatar_component_clause,[],[f809])).

fof(f114,plain,(
    v5_relat_1(sK2,sK0) ),
    inference(resolution,[],[f75,f51])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f219,plain,
    ( v2_funct_2(sK2,sK0)
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f217])).

fof(f217,plain,
    ( spl3_16
  <=> v2_funct_2(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f104,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f72,f51])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f812,plain,
    ( spl3_76
    | ~ spl3_20
    | ~ spl3_8
    | ~ spl3_13
    | ~ spl3_23
    | ~ spl3_10
    | ~ spl3_77
    | ~ spl3_37
    | ~ spl3_61
    | ~ spl3_63 ),
    inference(avatar_split_clause,[],[f803,f725,f696,f399,f809,f184,f274,f197,f176,f262,f805])).

fof(f176,plain,
    ( spl3_8
  <=> v2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f197,plain,
    ( spl3_13
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f184,plain,
    ( spl3_10
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f725,plain,
    ( spl3_63
  <=> k6_relat_1(sK0) = k5_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_63])])).

fof(f803,plain,
    ( sK0 != k2_relat_1(sK2)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | sK2 = k2_funct_1(sK1)
    | ~ spl3_37
    | ~ spl3_61
    | ~ spl3_63 ),
    inference(forward_demodulation,[],[f802,f401])).

fof(f401,plain,
    ( sK0 = k1_relat_1(sK1)
    | ~ spl3_37 ),
    inference(avatar_component_clause,[],[f399])).

fof(f802,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK1)
    | k2_relat_1(sK2) != k1_relat_1(sK1)
    | ~ v1_relat_1(sK1)
    | sK2 = k2_funct_1(sK1)
    | ~ spl3_61
    | ~ spl3_63 ),
    inference(trivial_inequality_removal,[],[f801])).

fof(f801,plain,
    ( k6_relat_1(sK0) != k6_relat_1(sK0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK1)
    | k2_relat_1(sK2) != k1_relat_1(sK1)
    | ~ v1_relat_1(sK1)
    | sK2 = k2_funct_1(sK1)
    | ~ spl3_61
    | ~ spl3_63 ),
    inference(forward_demodulation,[],[f800,f697])).

fof(f800,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK1)
    | k2_relat_1(sK2) != k1_relat_1(sK1)
    | ~ v1_relat_1(sK1)
    | sK2 = k2_funct_1(sK1)
    | ~ spl3_63 ),
    inference(superposition,[],[f68,f727])).

fof(f727,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK1)
    | ~ spl3_63 ),
    inference(avatar_component_clause,[],[f725])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X0)
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k2_funct_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0)
              & k1_relat_1(X0) = k2_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).

fof(f728,plain,
    ( ~ spl3_23
    | ~ spl3_11
    | ~ spl3_13
    | spl3_63
    | ~ spl3_39
    | ~ spl3_59 ),
    inference(avatar_split_clause,[],[f723,f688,f413,f725,f197,f189,f274])).

fof(f189,plain,
    ( spl3_11
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f413,plain,
    ( spl3_39
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).

fof(f688,plain,
    ( spl3_59
  <=> sK1 = k2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_59])])).

fof(f723,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK1)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_39
    | ~ spl3_59 ),
    inference(forward_demodulation,[],[f720,f415])).

fof(f415,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl3_39 ),
    inference(avatar_component_clause,[],[f413])).

fof(f720,plain,
    ( k6_relat_1(k1_relat_1(sK2)) = k5_relat_1(sK2,sK1)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_59 ),
    inference(superposition,[],[f66,f690])).

fof(f690,plain,
    ( sK1 = k2_funct_1(sK2)
    | ~ spl3_59 ),
    inference(avatar_component_clause,[],[f688])).

fof(f66,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

fof(f714,plain,
    ( ~ spl3_15
    | spl3_61 ),
    inference(avatar_contradiction_clause,[],[f712])).

fof(f712,plain,
    ( $false
    | ~ spl3_15
    | spl3_61 ),
    inference(unit_resulting_resolution,[],[f103,f214,f113,f698,f70])).

fof(f698,plain,
    ( sK0 != k2_relat_1(sK1)
    | spl3_61 ),
    inference(avatar_component_clause,[],[f696])).

fof(f113,plain,(
    v5_relat_1(sK1,sK0) ),
    inference(resolution,[],[f75,f57])).

fof(f57,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f22])).

fof(f214,plain,
    ( v2_funct_2(sK1,sK0)
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f212])).

fof(f212,plain,
    ( spl3_15
  <=> v2_funct_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f103,plain,(
    v1_relat_1(sK1) ),
    inference(resolution,[],[f72,f57])).

fof(f711,plain,
    ( ~ spl3_24
    | ~ spl3_16
    | ~ spl3_62 ),
    inference(avatar_split_clause,[],[f710,f702,f217,f278])).

fof(f278,plain,
    ( spl3_24
  <=> v5_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f702,plain,
    ( spl3_62
  <=> ! [X0] :
        ( k6_relat_1(X0) != k6_relat_1(sK0)
        | ~ v2_funct_2(sK2,X0)
        | ~ v5_relat_1(sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_62])])).

fof(f710,plain,
    ( ~ v2_funct_2(sK2,sK0)
    | ~ v5_relat_1(sK2,sK0)
    | ~ spl3_62 ),
    inference(equality_resolution,[],[f703])).

fof(f703,plain,
    ( ! [X0] :
        ( k6_relat_1(X0) != k6_relat_1(sK0)
        | ~ v2_funct_2(sK2,X0)
        | ~ v5_relat_1(sK2,X0) )
    | ~ spl3_62 ),
    inference(avatar_component_clause,[],[f702])).

fof(f704,plain,
    ( ~ spl3_23
    | spl3_62
    | spl3_60 ),
    inference(avatar_split_clause,[],[f700,f692,f702,f274])).

fof(f692,plain,
    ( spl3_60
  <=> k6_relat_1(sK0) = k6_relat_1(k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_60])])).

fof(f700,plain,
    ( ! [X0] :
        ( k6_relat_1(X0) != k6_relat_1(sK0)
        | ~ v5_relat_1(sK2,X0)
        | ~ v1_relat_1(sK2)
        | ~ v2_funct_2(sK2,X0) )
    | spl3_60 ),
    inference(superposition,[],[f694,f70])).

fof(f694,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK2))
    | spl3_60 ),
    inference(avatar_component_clause,[],[f692])).

fof(f699,plain,
    ( spl3_59
    | ~ spl3_23
    | ~ spl3_11
    | ~ spl3_10
    | ~ spl3_20
    | ~ spl3_13
    | ~ spl3_60
    | ~ spl3_61
    | ~ spl3_39
    | ~ spl3_55 ),
    inference(avatar_split_clause,[],[f686,f633,f413,f696,f692,f197,f262,f184,f189,f274,f688])).

fof(f633,plain,
    ( spl3_55
  <=> k6_relat_1(sK0) = k5_relat_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_55])])).

fof(f686,plain,
    ( sK0 != k2_relat_1(sK1)
    | k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | sK1 = k2_funct_1(sK2)
    | ~ spl3_39
    | ~ spl3_55 ),
    inference(forward_demodulation,[],[f685,f415])).

fof(f685,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v2_funct_1(sK2)
    | k1_relat_1(sK2) != k2_relat_1(sK1)
    | ~ v1_relat_1(sK2)
    | sK1 = k2_funct_1(sK2)
    | ~ spl3_55 ),
    inference(superposition,[],[f68,f635])).

fof(f635,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK1,sK2)
    | ~ spl3_55 ),
    inference(avatar_component_clause,[],[f633])).

fof(f677,plain,
    ( ~ spl3_10
    | ~ spl3_38
    | ~ spl3_13
    | ~ spl3_36
    | spl3_55
    | ~ spl3_57 ),
    inference(avatar_split_clause,[],[f674,f642,f633,f395,f197,f409,f184])).

fof(f409,plain,
    ( spl3_38
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).

fof(f395,plain,
    ( spl3_36
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f642,plain,
    ( spl3_57
  <=> k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k6_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).

fof(f674,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK1,sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ spl3_57 ),
    inference(superposition,[],[f87,f644])).

fof(f644,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k6_relat_1(sK0)
    | ~ spl3_57 ),
    inference(avatar_component_clause,[],[f642])).

fof(f87,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f670,plain,(
    spl3_56 ),
    inference(avatar_contradiction_clause,[],[f651])).

fof(f651,plain,
    ( $false
    | spl3_56 ),
    inference(unit_resulting_resolution,[],[f54,f48,f51,f57,f640,f89])).

fof(f89,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
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

fof(f640,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl3_56 ),
    inference(avatar_component_clause,[],[f638])).

fof(f638,plain,
    ( spl3_56
  <=> m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).

fof(f48,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f54,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f645,plain,
    ( ~ spl3_56
    | spl3_57 ),
    inference(avatar_split_clause,[],[f626,f642,f638])).

fof(f626,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k6_relat_1(sK0)
    | ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f381,f90])).

fof(f90,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_relat_1(sK0)) ),
    inference(definition_unfolding,[],[f52,f61])).

fof(f61,plain,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f52,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f381,plain,(
    ! [X4,X3] :
      ( ~ r2_relset_1(X4,X4,X3,k6_relat_1(X4))
      | k6_relat_1(X4) = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X4))) ) ),
    inference(resolution,[],[f86,f91])).

fof(f91,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f63,f61])).

fof(f63,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f524,plain,
    ( spl3_40
    | ~ spl3_10
    | ~ spl3_9
    | ~ spl3_25 ),
    inference(avatar_split_clause,[],[f518,f307,f180,f184,f521])).

fof(f180,plain,
    ( spl3_9
  <=> v3_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f307,plain,
    ( spl3_25
  <=> v1_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f518,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(resolution,[],[f71,f57])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1)
      | k2_funct_2(X0,X1) = k2_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_2(X0,X1) = k2_funct_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

fof(f503,plain,(
    spl3_38 ),
    inference(avatar_contradiction_clause,[],[f502])).

fof(f502,plain,
    ( $false
    | spl3_38 ),
    inference(subsumption_resolution,[],[f51,f411])).

fof(f411,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl3_38 ),
    inference(avatar_component_clause,[],[f409])).

fof(f497,plain,
    ( ~ spl3_25
    | spl3_26
    | spl3_27 ),
    inference(avatar_split_clause,[],[f491,f315,f311,f307])).

fof(f311,plain,
    ( spl3_26
  <=> sK0 = k1_relset_1(sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f491,plain,
    ( k1_xboole_0 = sK0
    | sK0 = k1_relset_1(sK0,sK0,sK1)
    | ~ v1_funct_2(sK1,sK0,sK0) ),
    inference(resolution,[],[f57,f81])).

fof(f419,plain,(
    spl3_36 ),
    inference(avatar_contradiction_clause,[],[f418])).

fof(f418,plain,
    ( $false
    | spl3_36 ),
    inference(subsumption_resolution,[],[f57,f397])).

fof(f397,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl3_36 ),
    inference(avatar_component_clause,[],[f395])).

fof(f417,plain,
    ( ~ spl3_38
    | spl3_39
    | ~ spl3_29 ),
    inference(avatar_split_clause,[],[f406,f324,f413,f409])).

fof(f406,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl3_29 ),
    inference(superposition,[],[f73,f326])).

fof(f326,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK2)
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f324])).

fof(f403,plain,
    ( ~ spl3_36
    | spl3_37
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f392,f311,f399,f395])).

fof(f392,plain,
    ( sK0 = k1_relat_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl3_26 ),
    inference(superposition,[],[f73,f313])).

fof(f313,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK1)
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f311])).

fof(f331,plain,(
    spl3_28 ),
    inference(avatar_contradiction_clause,[],[f330])).

fof(f330,plain,
    ( $false
    | spl3_28 ),
    inference(subsumption_resolution,[],[f49,f322])).

fof(f322,plain,
    ( ~ v1_funct_2(sK2,sK0,sK0)
    | spl3_28 ),
    inference(avatar_component_clause,[],[f320])).

fof(f49,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f329,plain,(
    spl3_25 ),
    inference(avatar_contradiction_clause,[],[f328])).

fof(f328,plain,
    ( $false
    | spl3_25 ),
    inference(subsumption_resolution,[],[f55,f309])).

fof(f309,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | spl3_25 ),
    inference(avatar_component_clause,[],[f307])).

fof(f55,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f301,plain,(
    spl3_23 ),
    inference(avatar_contradiction_clause,[],[f298])).

fof(f298,plain,
    ( $false
    | spl3_23 ),
    inference(subsumption_resolution,[],[f104,f276])).

fof(f276,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_23 ),
    inference(avatar_component_clause,[],[f274])).

fof(f297,plain,(
    spl3_24 ),
    inference(avatar_contradiction_clause,[],[f294])).

fof(f294,plain,
    ( $false
    | spl3_24 ),
    inference(subsumption_resolution,[],[f114,f280])).

fof(f280,plain,
    ( ~ v5_relat_1(sK2,sK0)
    | spl3_24 ),
    inference(avatar_component_clause,[],[f278])).

fof(f285,plain,(
    spl3_20 ),
    inference(avatar_contradiction_clause,[],[f282])).

fof(f282,plain,
    ( $false
    | spl3_20 ),
    inference(subsumption_resolution,[],[f103,f264])).

fof(f264,plain,
    ( ~ v1_relat_1(sK1)
    | spl3_20 ),
    inference(avatar_component_clause,[],[f262])).

fof(f226,plain,(
    spl3_12 ),
    inference(avatar_contradiction_clause,[],[f225])).

fof(f225,plain,
    ( $false
    | spl3_12 ),
    inference(subsumption_resolution,[],[f50,f195])).

fof(f195,plain,
    ( ~ v3_funct_2(sK2,sK0,sK0)
    | spl3_12 ),
    inference(avatar_component_clause,[],[f193])).

fof(f193,plain,
    ( spl3_12
  <=> v3_funct_2(sK2,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f50,plain,(
    v3_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f224,plain,(
    spl3_10 ),
    inference(avatar_contradiction_clause,[],[f223])).

fof(f223,plain,
    ( $false
    | spl3_10 ),
    inference(subsumption_resolution,[],[f54,f186])).

fof(f186,plain,
    ( ~ v1_funct_1(sK1)
    | spl3_10 ),
    inference(avatar_component_clause,[],[f184])).

fof(f222,plain,(
    spl3_9 ),
    inference(avatar_contradiction_clause,[],[f221])).

fof(f221,plain,
    ( $false
    | spl3_9 ),
    inference(subsumption_resolution,[],[f56,f182])).

fof(f182,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | spl3_9 ),
    inference(avatar_component_clause,[],[f180])).

fof(f56,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f220,plain,
    ( spl3_16
    | ~ spl3_12
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f206,f197,f193,f217])).

fof(f206,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v3_funct_2(sK2,sK0,sK0)
    | v2_funct_2(sK2,sK0) ),
    inference(resolution,[],[f83,f51])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | v2_funct_2(X2,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

fof(f215,plain,
    ( spl3_15
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f205,f184,f180,f212])).

fof(f205,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | v2_funct_2(sK1,sK0) ),
    inference(resolution,[],[f83,f57])).

fof(f202,plain,(
    spl3_13 ),
    inference(avatar_contradiction_clause,[],[f201])).

fof(f201,plain,
    ( $false
    | spl3_13 ),
    inference(subsumption_resolution,[],[f48,f199])).

fof(f199,plain,
    ( ~ v1_funct_1(sK2)
    | spl3_13 ),
    inference(avatar_component_clause,[],[f197])).

fof(f200,plain,
    ( spl3_11
    | ~ spl3_12
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f162,f197,f193,f189])).

fof(f162,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v3_funct_2(sK2,sK0,sK0)
    | v2_funct_1(sK2) ),
    inference(resolution,[],[f82,f51])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | v2_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f187,plain,
    ( spl3_8
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f161,f184,f180,f176])).

fof(f161,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | v2_funct_1(sK1) ),
    inference(resolution,[],[f82,f57])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:10:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.53  % (20171)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.53  % (20190)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.53  % (20174)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.53  % (20182)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.53  % (20188)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.53  % (20172)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (20169)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.53  % (20184)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.54  % (20180)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.54  % (20168)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.54  % (20166)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.54  % (20197)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.55  % (20185)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.55  % (20189)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.55  % (20183)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.41/0.55  % (20170)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.41/0.55  % (20177)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.41/0.55  % (20181)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.41/0.55  % (20176)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.41/0.56  % (20175)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.41/0.56  % (20195)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.41/0.56  % (20193)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.41/0.56  % (20194)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.41/0.57  % (20191)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.57/0.57  % (20167)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.57/0.57  % (20196)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.57/0.57  % (20183)Refutation not found, incomplete strategy% (20183)------------------------------
% 1.57/0.57  % (20183)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.57  % (20183)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.57  
% 1.57/0.57  % (20183)Memory used [KB]: 10746
% 1.57/0.57  % (20183)Time elapsed: 0.147 s
% 1.57/0.57  % (20183)------------------------------
% 1.57/0.57  % (20183)------------------------------
% 1.57/0.57  % (20180)Refutation found. Thanks to Tanya!
% 1.57/0.57  % SZS status Theorem for theBenchmark
% 1.57/0.58  % (20187)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.57/0.58  % (20178)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.57/0.58  % (20192)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.57/0.58  % (20173)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.57/0.58  % SZS output start Proof for theBenchmark
% 1.57/0.59  fof(f1069,plain,(
% 1.57/0.59    $false),
% 1.57/0.59    inference(avatar_sat_refutation,[],[f187,f200,f202,f215,f220,f222,f224,f226,f285,f297,f301,f329,f331,f403,f417,f419,f497,f503,f524,f645,f670,f677,f699,f704,f711,f714,f728,f812,f828,f844,f853,f854,f860,f1062,f1068])).
% 1.57/0.59  fof(f1068,plain,(
% 1.57/0.59    ~spl3_27 | ~spl3_31 | spl3_37),
% 1.57/0.59    inference(avatar_contradiction_clause,[],[f1067])).
% 1.57/0.59  fof(f1067,plain,(
% 1.57/0.59    $false | (~spl3_27 | ~spl3_31 | spl3_37)),
% 1.57/0.59    inference(subsumption_resolution,[],[f58,f1047])).
% 1.57/0.59  fof(f1047,plain,(
% 1.57/0.59    k1_xboole_0 != k1_relat_1(k1_xboole_0) | (~spl3_27 | ~spl3_31 | spl3_37)),
% 1.57/0.59    inference(forward_demodulation,[],[f1046,f317])).
% 1.57/0.59  fof(f317,plain,(
% 1.57/0.59    k1_xboole_0 = sK0 | ~spl3_27),
% 1.57/0.59    inference(avatar_component_clause,[],[f315])).
% 1.57/0.59  fof(f315,plain,(
% 1.57/0.59    spl3_27 <=> k1_xboole_0 = sK0),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 1.57/0.59  fof(f1046,plain,(
% 1.57/0.59    k1_relat_1(k1_xboole_0) != sK0 | (~spl3_31 | spl3_37)),
% 1.57/0.59    inference(forward_demodulation,[],[f400,f359])).
% 1.57/0.59  fof(f359,plain,(
% 1.57/0.59    k1_xboole_0 = sK1 | ~spl3_31),
% 1.57/0.59    inference(avatar_component_clause,[],[f357])).
% 1.57/0.59  fof(f357,plain,(
% 1.57/0.59    spl3_31 <=> k1_xboole_0 = sK1),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 1.57/0.59  fof(f400,plain,(
% 1.57/0.59    sK0 != k1_relat_1(sK1) | spl3_37),
% 1.57/0.59    inference(avatar_component_clause,[],[f399])).
% 1.57/0.59  fof(f399,plain,(
% 1.57/0.59    spl3_37 <=> sK0 = k1_relat_1(sK1)),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).
% 1.57/0.59  fof(f58,plain,(
% 1.57/0.59    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.57/0.59    inference(cnf_transformation,[],[f3])).
% 1.57/0.59  fof(f3,axiom,(
% 1.57/0.59    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.57/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 1.57/0.59  fof(f1062,plain,(
% 1.57/0.59    ~spl3_27 | spl3_29 | ~spl3_34),
% 1.57/0.59    inference(avatar_contradiction_clause,[],[f1055])).
% 1.57/0.59  fof(f1055,plain,(
% 1.57/0.59    $false | (~spl3_27 | spl3_29 | ~spl3_34)),
% 1.57/0.59    inference(unit_resulting_resolution,[],[f249,f60,f1036,f94])).
% 1.57/0.59  fof(f94,plain,(
% 1.57/0.59    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1)) )),
% 1.57/0.59    inference(equality_resolution,[],[f79])).
% 1.57/0.59  fof(f79,plain,(
% 1.57/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 1.57/0.59    inference(cnf_transformation,[],[f37])).
% 1.57/0.59  fof(f37,plain,(
% 1.57/0.59    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.57/0.59    inference(flattening,[],[f36])).
% 1.57/0.59  fof(f36,plain,(
% 1.57/0.59    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.57/0.59    inference(ennf_transformation,[],[f12])).
% 1.57/0.59  fof(f12,axiom,(
% 1.57/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.57/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.57/0.59  fof(f1036,plain,(
% 1.57/0.59    k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl3_27 | spl3_29 | ~spl3_34)),
% 1.57/0.59    inference(forward_demodulation,[],[f1035,f317])).
% 1.57/0.59  fof(f1035,plain,(
% 1.57/0.59    sK0 != k1_relset_1(sK0,sK0,k1_xboole_0) | (spl3_29 | ~spl3_34)),
% 1.57/0.59    inference(forward_demodulation,[],[f325,f374])).
% 1.57/0.59  fof(f374,plain,(
% 1.57/0.59    k1_xboole_0 = sK2 | ~spl3_34),
% 1.57/0.59    inference(avatar_component_clause,[],[f372])).
% 1.57/0.59  fof(f372,plain,(
% 1.57/0.59    spl3_34 <=> k1_xboole_0 = sK2),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 1.57/0.59  fof(f325,plain,(
% 1.57/0.59    sK0 != k1_relset_1(sK0,sK0,sK2) | spl3_29),
% 1.57/0.59    inference(avatar_component_clause,[],[f324])).
% 1.57/0.59  fof(f324,plain,(
% 1.57/0.59    spl3_29 <=> sK0 = k1_relset_1(sK0,sK0,sK2)),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 1.57/0.59  fof(f60,plain,(
% 1.57/0.59    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.57/0.59    inference(cnf_transformation,[],[f1])).
% 1.57/0.59  fof(f1,axiom,(
% 1.57/0.59    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.57/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 1.57/0.59  fof(f249,plain,(
% 1.57/0.59    ( ! [X0] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) )),
% 1.57/0.59    inference(resolution,[],[f248,f60])).
% 1.57/0.59  fof(f248,plain,(
% 1.57/0.59    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) | v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) )),
% 1.57/0.59    inference(trivial_inequality_removal,[],[f247])).
% 1.57/0.59  fof(f247,plain,(
% 1.57/0.59    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) | v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) )),
% 1.57/0.59    inference(superposition,[],[f244,f58])).
% 1.57/0.59  fof(f244,plain,(
% 1.57/0.59    ( ! [X2,X1] : (k1_xboole_0 != k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | v1_funct_2(X2,k1_xboole_0,X1)) )),
% 1.57/0.59    inference(duplicate_literal_removal,[],[f243])).
% 1.57/0.59  fof(f243,plain,(
% 1.57/0.59    ( ! [X2,X1] : (k1_xboole_0 != k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 1.57/0.59    inference(superposition,[],[f95,f73])).
% 1.57/0.59  fof(f73,plain,(
% 1.57/0.59    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.57/0.59    inference(cnf_transformation,[],[f34])).
% 1.57/0.59  fof(f34,plain,(
% 1.57/0.59    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.57/0.59    inference(ennf_transformation,[],[f9])).
% 1.57/0.59  fof(f9,axiom,(
% 1.57/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.57/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.57/0.59  fof(f95,plain,(
% 1.57/0.59    ( ! [X2,X1] : (k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | v1_funct_2(X2,k1_xboole_0,X1)) )),
% 1.57/0.59    inference(equality_resolution,[],[f78])).
% 1.57/0.59  fof(f78,plain,(
% 1.57/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)) )),
% 1.57/0.59    inference(cnf_transformation,[],[f37])).
% 1.57/0.59  fof(f860,plain,(
% 1.57/0.59    ~spl3_28 | spl3_29 | spl3_27),
% 1.57/0.59    inference(avatar_split_clause,[],[f509,f315,f324,f320])).
% 1.57/0.59  fof(f320,plain,(
% 1.57/0.59    spl3_28 <=> v1_funct_2(sK2,sK0,sK0)),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 1.57/0.59  fof(f509,plain,(
% 1.57/0.59    k1_xboole_0 = sK0 | sK0 = k1_relset_1(sK0,sK0,sK2) | ~v1_funct_2(sK2,sK0,sK0)),
% 1.57/0.59    inference(resolution,[],[f51,f81])).
% 1.57/0.59  fof(f81,plain,(
% 1.57/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 1.57/0.59    inference(cnf_transformation,[],[f37])).
% 1.57/0.59  fof(f51,plain,(
% 1.57/0.59    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.57/0.59    inference(cnf_transformation,[],[f22])).
% 1.57/0.59  fof(f22,plain,(
% 1.57/0.59    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 1.57/0.59    inference(flattening,[],[f21])).
% 1.57/0.59  fof(f21,plain,(
% 1.57/0.59    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 1.57/0.59    inference(ennf_transformation,[],[f20])).
% 1.57/0.59  fof(f20,negated_conjecture,(
% 1.57/0.59    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 1.57/0.59    inference(negated_conjecture,[],[f19])).
% 1.57/0.59  fof(f19,conjecture,(
% 1.57/0.59    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 1.57/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_funct_2)).
% 1.57/0.59  fof(f854,plain,(
% 1.57/0.59    spl3_31 | ~spl3_20 | ~spl3_27 | ~spl3_61),
% 1.57/0.59    inference(avatar_split_clause,[],[f732,f696,f315,f262,f357])).
% 1.57/0.59  fof(f262,plain,(
% 1.57/0.59    spl3_20 <=> v1_relat_1(sK1)),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 1.57/0.59  fof(f696,plain,(
% 1.57/0.59    spl3_61 <=> sK0 = k2_relat_1(sK1)),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_61])])).
% 1.57/0.59  fof(f732,plain,(
% 1.57/0.59    k1_xboole_0 != sK0 | ~v1_relat_1(sK1) | k1_xboole_0 = sK1 | ~spl3_61),
% 1.57/0.59    inference(superposition,[],[f65,f697])).
% 1.57/0.59  fof(f697,plain,(
% 1.57/0.59    sK0 = k2_relat_1(sK1) | ~spl3_61),
% 1.57/0.59    inference(avatar_component_clause,[],[f696])).
% 1.57/0.59  fof(f65,plain,(
% 1.57/0.59    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0) | k1_xboole_0 = X0) )),
% 1.57/0.59    inference(cnf_transformation,[],[f24])).
% 1.57/0.59  fof(f24,plain,(
% 1.57/0.59    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.57/0.59    inference(flattening,[],[f23])).
% 1.57/0.59  fof(f23,plain,(
% 1.57/0.59    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.57/0.59    inference(ennf_transformation,[],[f4])).
% 1.57/0.59  fof(f4,axiom,(
% 1.57/0.59    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 1.57/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 1.57/0.59  fof(f853,plain,(
% 1.57/0.59    spl3_34 | ~spl3_23 | ~spl3_27 | ~spl3_77),
% 1.57/0.59    inference(avatar_split_clause,[],[f840,f809,f315,f274,f372])).
% 1.57/0.59  fof(f274,plain,(
% 1.57/0.59    spl3_23 <=> v1_relat_1(sK2)),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 1.57/0.59  fof(f809,plain,(
% 1.57/0.59    spl3_77 <=> sK0 = k2_relat_1(sK2)),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_77])])).
% 1.57/0.59  fof(f840,plain,(
% 1.57/0.59    k1_xboole_0 != sK0 | ~v1_relat_1(sK2) | k1_xboole_0 = sK2 | ~spl3_77),
% 1.57/0.59    inference(superposition,[],[f65,f810])).
% 1.57/0.59  fof(f810,plain,(
% 1.57/0.59    sK0 = k2_relat_1(sK2) | ~spl3_77),
% 1.57/0.59    inference(avatar_component_clause,[],[f809])).
% 1.57/0.59  fof(f844,plain,(
% 1.57/0.59    ~spl3_40 | ~spl3_76),
% 1.57/0.59    inference(avatar_contradiction_clause,[],[f841])).
% 1.57/0.59  fof(f841,plain,(
% 1.57/0.59    $false | (~spl3_40 | ~spl3_76)),
% 1.57/0.59    inference(subsumption_resolution,[],[f143,f829])).
% 1.57/0.59  fof(f829,plain,(
% 1.57/0.59    ~r2_relset_1(sK0,sK0,sK2,sK2) | (~spl3_40 | ~spl3_76)),
% 1.57/0.59    inference(superposition,[],[f530,f807])).
% 1.57/0.59  fof(f807,plain,(
% 1.57/0.59    sK2 = k2_funct_1(sK1) | ~spl3_76),
% 1.57/0.59    inference(avatar_component_clause,[],[f805])).
% 1.57/0.59  fof(f805,plain,(
% 1.57/0.59    spl3_76 <=> sK2 = k2_funct_1(sK1)),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_76])])).
% 1.57/0.59  fof(f530,plain,(
% 1.57/0.59    ~r2_relset_1(sK0,sK0,sK2,k2_funct_1(sK1)) | ~spl3_40),
% 1.57/0.59    inference(superposition,[],[f53,f523])).
% 1.57/0.59  fof(f523,plain,(
% 1.57/0.59    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~spl3_40),
% 1.57/0.59    inference(avatar_component_clause,[],[f521])).
% 1.57/0.59  fof(f521,plain,(
% 1.57/0.59    spl3_40 <=> k2_funct_2(sK0,sK1) = k2_funct_1(sK1)),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).
% 1.57/0.59  fof(f53,plain,(
% 1.57/0.59    ~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))),
% 1.57/0.59    inference(cnf_transformation,[],[f22])).
% 1.57/0.59  fof(f143,plain,(
% 1.57/0.59    r2_relset_1(sK0,sK0,sK2,sK2)),
% 1.57/0.59    inference(resolution,[],[f100,f51])).
% 1.57/0.59  fof(f100,plain,(
% 1.57/0.59    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 1.57/0.59    inference(duplicate_literal_removal,[],[f99])).
% 1.57/0.59  fof(f99,plain,(
% 1.57/0.59    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 1.57/0.59    inference(equality_resolution,[],[f85])).
% 1.57/0.59  fof(f85,plain,(
% 1.57/0.59    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 != X3 | r2_relset_1(X0,X1,X2,X3)) )),
% 1.57/0.59    inference(cnf_transformation,[],[f43])).
% 1.57/0.59  fof(f43,plain,(
% 1.57/0.59    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.57/0.59    inference(flattening,[],[f42])).
% 1.57/0.59  fof(f42,plain,(
% 1.57/0.59    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.57/0.59    inference(ennf_transformation,[],[f10])).
% 1.57/0.59  fof(f10,axiom,(
% 1.57/0.59    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.57/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.57/0.59  fof(f828,plain,(
% 1.57/0.59    ~spl3_16 | spl3_77),
% 1.57/0.59    inference(avatar_contradiction_clause,[],[f826])).
% 1.57/0.59  fof(f826,plain,(
% 1.57/0.59    $false | (~spl3_16 | spl3_77)),
% 1.57/0.59    inference(unit_resulting_resolution,[],[f104,f219,f114,f811,f70])).
% 1.57/0.59  fof(f70,plain,(
% 1.57/0.59    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1) | ~v2_funct_2(X1,X0)) )),
% 1.57/0.59    inference(cnf_transformation,[],[f30])).
% 1.57/0.59  fof(f30,plain,(
% 1.57/0.59    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.57/0.59    inference(flattening,[],[f29])).
% 1.57/0.59  fof(f29,plain,(
% 1.57/0.59    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.57/0.59    inference(ennf_transformation,[],[f13])).
% 1.57/0.59  fof(f13,axiom,(
% 1.57/0.59    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 1.57/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).
% 1.57/0.59  fof(f811,plain,(
% 1.57/0.59    sK0 != k2_relat_1(sK2) | spl3_77),
% 1.57/0.59    inference(avatar_component_clause,[],[f809])).
% 1.57/0.59  fof(f114,plain,(
% 1.57/0.59    v5_relat_1(sK2,sK0)),
% 1.57/0.59    inference(resolution,[],[f75,f51])).
% 1.57/0.59  fof(f75,plain,(
% 1.57/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.57/0.59    inference(cnf_transformation,[],[f35])).
% 1.57/0.59  fof(f35,plain,(
% 1.57/0.59    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.57/0.59    inference(ennf_transformation,[],[f8])).
% 1.57/0.59  fof(f8,axiom,(
% 1.57/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.57/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.57/0.59  fof(f219,plain,(
% 1.57/0.59    v2_funct_2(sK2,sK0) | ~spl3_16),
% 1.57/0.59    inference(avatar_component_clause,[],[f217])).
% 1.57/0.59  fof(f217,plain,(
% 1.57/0.59    spl3_16 <=> v2_funct_2(sK2,sK0)),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 1.57/0.59  fof(f104,plain,(
% 1.57/0.59    v1_relat_1(sK2)),
% 1.57/0.59    inference(resolution,[],[f72,f51])).
% 1.57/0.59  fof(f72,plain,(
% 1.57/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.57/0.59    inference(cnf_transformation,[],[f33])).
% 1.57/0.59  fof(f33,plain,(
% 1.57/0.59    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.57/0.59    inference(ennf_transformation,[],[f7])).
% 1.57/0.59  fof(f7,axiom,(
% 1.57/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.57/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.57/0.59  fof(f812,plain,(
% 1.57/0.59    spl3_76 | ~spl3_20 | ~spl3_8 | ~spl3_13 | ~spl3_23 | ~spl3_10 | ~spl3_77 | ~spl3_37 | ~spl3_61 | ~spl3_63),
% 1.57/0.59    inference(avatar_split_clause,[],[f803,f725,f696,f399,f809,f184,f274,f197,f176,f262,f805])).
% 1.57/0.59  fof(f176,plain,(
% 1.57/0.59    spl3_8 <=> v2_funct_1(sK1)),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 1.57/0.59  fof(f197,plain,(
% 1.57/0.59    spl3_13 <=> v1_funct_1(sK2)),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 1.57/0.59  fof(f184,plain,(
% 1.57/0.59    spl3_10 <=> v1_funct_1(sK1)),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 1.57/0.59  fof(f725,plain,(
% 1.57/0.59    spl3_63 <=> k6_relat_1(sK0) = k5_relat_1(sK2,sK1)),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_63])])).
% 1.57/0.59  fof(f803,plain,(
% 1.57/0.59    sK0 != k2_relat_1(sK2) | ~v1_funct_1(sK1) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v2_funct_1(sK1) | ~v1_relat_1(sK1) | sK2 = k2_funct_1(sK1) | (~spl3_37 | ~spl3_61 | ~spl3_63)),
% 1.57/0.59    inference(forward_demodulation,[],[f802,f401])).
% 1.57/0.59  fof(f401,plain,(
% 1.57/0.59    sK0 = k1_relat_1(sK1) | ~spl3_37),
% 1.57/0.59    inference(avatar_component_clause,[],[f399])).
% 1.57/0.59  fof(f802,plain,(
% 1.57/0.59    ~v1_funct_1(sK1) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v2_funct_1(sK1) | k2_relat_1(sK2) != k1_relat_1(sK1) | ~v1_relat_1(sK1) | sK2 = k2_funct_1(sK1) | (~spl3_61 | ~spl3_63)),
% 1.57/0.59    inference(trivial_inequality_removal,[],[f801])).
% 1.57/0.59  fof(f801,plain,(
% 1.57/0.59    k6_relat_1(sK0) != k6_relat_1(sK0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v2_funct_1(sK1) | k2_relat_1(sK2) != k1_relat_1(sK1) | ~v1_relat_1(sK1) | sK2 = k2_funct_1(sK1) | (~spl3_61 | ~spl3_63)),
% 1.57/0.59    inference(forward_demodulation,[],[f800,f697])).
% 1.57/0.59  fof(f800,plain,(
% 1.57/0.59    k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v2_funct_1(sK1) | k2_relat_1(sK2) != k1_relat_1(sK1) | ~v1_relat_1(sK1) | sK2 = k2_funct_1(sK1) | ~spl3_63),
% 1.57/0.59    inference(superposition,[],[f68,f727])).
% 1.57/0.59  fof(f727,plain,(
% 1.57/0.59    k6_relat_1(sK0) = k5_relat_1(sK2,sK1) | ~spl3_63),
% 1.57/0.59    inference(avatar_component_clause,[],[f725])).
% 1.57/0.59  fof(f68,plain,(
% 1.57/0.59    ( ! [X0,X1] : (k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v1_relat_1(X0) | k2_funct_1(X0) = X1) )),
% 1.57/0.59    inference(cnf_transformation,[],[f28])).
% 1.57/0.59  fof(f28,plain,(
% 1.57/0.59    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.57/0.59    inference(flattening,[],[f27])).
% 1.57/0.59  fof(f27,plain,(
% 1.57/0.59    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.57/0.59    inference(ennf_transformation,[],[f6])).
% 1.57/0.59  fof(f6,axiom,(
% 1.57/0.59    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 1.57/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).
% 1.57/0.59  fof(f728,plain,(
% 1.57/0.59    ~spl3_23 | ~spl3_11 | ~spl3_13 | spl3_63 | ~spl3_39 | ~spl3_59),
% 1.57/0.59    inference(avatar_split_clause,[],[f723,f688,f413,f725,f197,f189,f274])).
% 1.57/0.59  fof(f189,plain,(
% 1.57/0.59    spl3_11 <=> v2_funct_1(sK2)),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 1.57/0.59  fof(f413,plain,(
% 1.57/0.59    spl3_39 <=> sK0 = k1_relat_1(sK2)),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).
% 1.57/0.59  fof(f688,plain,(
% 1.57/0.59    spl3_59 <=> sK1 = k2_funct_1(sK2)),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_59])])).
% 1.57/0.59  fof(f723,plain,(
% 1.57/0.59    k6_relat_1(sK0) = k5_relat_1(sK2,sK1) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl3_39 | ~spl3_59)),
% 1.57/0.59    inference(forward_demodulation,[],[f720,f415])).
% 1.57/0.59  fof(f415,plain,(
% 1.57/0.59    sK0 = k1_relat_1(sK2) | ~spl3_39),
% 1.57/0.59    inference(avatar_component_clause,[],[f413])).
% 1.57/0.59  fof(f720,plain,(
% 1.57/0.59    k6_relat_1(k1_relat_1(sK2)) = k5_relat_1(sK2,sK1) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl3_59),
% 1.57/0.59    inference(superposition,[],[f66,f690])).
% 1.57/0.59  fof(f690,plain,(
% 1.57/0.59    sK1 = k2_funct_1(sK2) | ~spl3_59),
% 1.57/0.59    inference(avatar_component_clause,[],[f688])).
% 1.57/0.59  fof(f66,plain,(
% 1.57/0.59    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.57/0.59    inference(cnf_transformation,[],[f26])).
% 1.57/0.59  fof(f26,plain,(
% 1.57/0.59    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.57/0.59    inference(flattening,[],[f25])).
% 1.57/0.59  fof(f25,plain,(
% 1.57/0.59    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.57/0.59    inference(ennf_transformation,[],[f5])).
% 1.57/0.59  fof(f5,axiom,(
% 1.57/0.59    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 1.57/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).
% 1.57/0.59  fof(f714,plain,(
% 1.57/0.59    ~spl3_15 | spl3_61),
% 1.57/0.59    inference(avatar_contradiction_clause,[],[f712])).
% 1.57/0.59  fof(f712,plain,(
% 1.57/0.59    $false | (~spl3_15 | spl3_61)),
% 1.57/0.59    inference(unit_resulting_resolution,[],[f103,f214,f113,f698,f70])).
% 1.57/0.59  fof(f698,plain,(
% 1.57/0.59    sK0 != k2_relat_1(sK1) | spl3_61),
% 1.57/0.59    inference(avatar_component_clause,[],[f696])).
% 1.57/0.59  fof(f113,plain,(
% 1.57/0.59    v5_relat_1(sK1,sK0)),
% 1.57/0.59    inference(resolution,[],[f75,f57])).
% 1.57/0.59  fof(f57,plain,(
% 1.57/0.59    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.57/0.59    inference(cnf_transformation,[],[f22])).
% 1.57/0.59  fof(f214,plain,(
% 1.57/0.59    v2_funct_2(sK1,sK0) | ~spl3_15),
% 1.57/0.59    inference(avatar_component_clause,[],[f212])).
% 1.57/0.59  fof(f212,plain,(
% 1.57/0.59    spl3_15 <=> v2_funct_2(sK1,sK0)),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 1.57/0.59  fof(f103,plain,(
% 1.57/0.59    v1_relat_1(sK1)),
% 1.57/0.59    inference(resolution,[],[f72,f57])).
% 1.57/0.59  fof(f711,plain,(
% 1.57/0.59    ~spl3_24 | ~spl3_16 | ~spl3_62),
% 1.57/0.59    inference(avatar_split_clause,[],[f710,f702,f217,f278])).
% 1.57/0.59  fof(f278,plain,(
% 1.57/0.59    spl3_24 <=> v5_relat_1(sK2,sK0)),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 1.57/0.59  fof(f702,plain,(
% 1.57/0.59    spl3_62 <=> ! [X0] : (k6_relat_1(X0) != k6_relat_1(sK0) | ~v2_funct_2(sK2,X0) | ~v5_relat_1(sK2,X0))),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_62])])).
% 1.57/0.59  fof(f710,plain,(
% 1.57/0.59    ~v2_funct_2(sK2,sK0) | ~v5_relat_1(sK2,sK0) | ~spl3_62),
% 1.57/0.59    inference(equality_resolution,[],[f703])).
% 1.57/0.59  fof(f703,plain,(
% 1.57/0.59    ( ! [X0] : (k6_relat_1(X0) != k6_relat_1(sK0) | ~v2_funct_2(sK2,X0) | ~v5_relat_1(sK2,X0)) ) | ~spl3_62),
% 1.57/0.59    inference(avatar_component_clause,[],[f702])).
% 1.57/0.59  fof(f704,plain,(
% 1.57/0.59    ~spl3_23 | spl3_62 | spl3_60),
% 1.57/0.59    inference(avatar_split_clause,[],[f700,f692,f702,f274])).
% 1.57/0.59  fof(f692,plain,(
% 1.57/0.59    spl3_60 <=> k6_relat_1(sK0) = k6_relat_1(k2_relat_1(sK2))),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_60])])).
% 1.57/0.59  fof(f700,plain,(
% 1.57/0.59    ( ! [X0] : (k6_relat_1(X0) != k6_relat_1(sK0) | ~v5_relat_1(sK2,X0) | ~v1_relat_1(sK2) | ~v2_funct_2(sK2,X0)) ) | spl3_60),
% 1.57/0.59    inference(superposition,[],[f694,f70])).
% 1.57/0.59  fof(f694,plain,(
% 1.57/0.59    k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK2)) | spl3_60),
% 1.57/0.59    inference(avatar_component_clause,[],[f692])).
% 1.57/0.59  fof(f699,plain,(
% 1.57/0.59    spl3_59 | ~spl3_23 | ~spl3_11 | ~spl3_10 | ~spl3_20 | ~spl3_13 | ~spl3_60 | ~spl3_61 | ~spl3_39 | ~spl3_55),
% 1.57/0.59    inference(avatar_split_clause,[],[f686,f633,f413,f696,f692,f197,f262,f184,f189,f274,f688])).
% 1.57/0.59  fof(f633,plain,(
% 1.57/0.59    spl3_55 <=> k6_relat_1(sK0) = k5_relat_1(sK1,sK2)),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_55])])).
% 1.57/0.59  fof(f686,plain,(
% 1.57/0.59    sK0 != k2_relat_1(sK1) | k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK1) | ~v1_funct_1(sK1) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | sK1 = k2_funct_1(sK2) | (~spl3_39 | ~spl3_55)),
% 1.57/0.59    inference(forward_demodulation,[],[f685,f415])).
% 1.57/0.59  fof(f685,plain,(
% 1.57/0.59    k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK1) | ~v1_funct_1(sK1) | ~v2_funct_1(sK2) | k1_relat_1(sK2) != k2_relat_1(sK1) | ~v1_relat_1(sK2) | sK1 = k2_funct_1(sK2) | ~spl3_55),
% 1.57/0.59    inference(superposition,[],[f68,f635])).
% 1.57/0.59  fof(f635,plain,(
% 1.57/0.59    k6_relat_1(sK0) = k5_relat_1(sK1,sK2) | ~spl3_55),
% 1.57/0.59    inference(avatar_component_clause,[],[f633])).
% 1.57/0.59  fof(f677,plain,(
% 1.57/0.59    ~spl3_10 | ~spl3_38 | ~spl3_13 | ~spl3_36 | spl3_55 | ~spl3_57),
% 1.57/0.59    inference(avatar_split_clause,[],[f674,f642,f633,f395,f197,f409,f184])).
% 1.57/0.59  fof(f409,plain,(
% 1.57/0.59    spl3_38 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).
% 1.57/0.59  fof(f395,plain,(
% 1.57/0.59    spl3_36 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 1.57/0.59  fof(f642,plain,(
% 1.57/0.59    spl3_57 <=> k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k6_relat_1(sK0)),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).
% 1.57/0.59  fof(f674,plain,(
% 1.57/0.59    k6_relat_1(sK0) = k5_relat_1(sK1,sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1) | ~spl3_57),
% 1.57/0.59    inference(superposition,[],[f87,f644])).
% 1.57/0.59  fof(f644,plain,(
% 1.57/0.59    k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k6_relat_1(sK0) | ~spl3_57),
% 1.57/0.59    inference(avatar_component_clause,[],[f642])).
% 1.57/0.59  fof(f87,plain,(
% 1.57/0.59    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 1.57/0.59    inference(cnf_transformation,[],[f45])).
% 1.57/0.59  fof(f45,plain,(
% 1.57/0.59    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.57/0.59    inference(flattening,[],[f44])).
% 1.57/0.59  fof(f44,plain,(
% 1.57/0.59    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.57/0.59    inference(ennf_transformation,[],[f16])).
% 1.57/0.59  fof(f16,axiom,(
% 1.57/0.59    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.57/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.57/0.59  fof(f670,plain,(
% 1.57/0.59    spl3_56),
% 1.57/0.59    inference(avatar_contradiction_clause,[],[f651])).
% 1.57/0.59  fof(f651,plain,(
% 1.57/0.59    $false | spl3_56),
% 1.57/0.59    inference(unit_resulting_resolution,[],[f54,f48,f51,f57,f640,f89])).
% 1.57/0.59  fof(f89,plain,(
% 1.57/0.59    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 1.57/0.59    inference(cnf_transformation,[],[f47])).
% 1.57/0.59  fof(f47,plain,(
% 1.57/0.59    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.57/0.59    inference(flattening,[],[f46])).
% 1.57/0.59  fof(f46,plain,(
% 1.57/0.59    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.57/0.59    inference(ennf_transformation,[],[f14])).
% 1.57/0.59  fof(f14,axiom,(
% 1.57/0.59    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.57/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.57/0.59  fof(f640,plain,(
% 1.57/0.59    ~m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl3_56),
% 1.57/0.59    inference(avatar_component_clause,[],[f638])).
% 1.57/0.59  fof(f638,plain,(
% 1.57/0.59    spl3_56 <=> m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.57/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).
% 1.57/0.59  fof(f48,plain,(
% 1.57/0.59    v1_funct_1(sK2)),
% 1.57/0.59    inference(cnf_transformation,[],[f22])).
% 1.57/0.59  fof(f54,plain,(
% 1.57/0.59    v1_funct_1(sK1)),
% 1.57/0.59    inference(cnf_transformation,[],[f22])).
% 1.57/0.59  fof(f645,plain,(
% 1.57/0.59    ~spl3_56 | spl3_57),
% 1.57/0.59    inference(avatar_split_clause,[],[f626,f642,f638])).
% 1.57/0.59  fof(f626,plain,(
% 1.57/0.59    k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k6_relat_1(sK0) | ~m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.57/0.59    inference(resolution,[],[f381,f90])).
% 1.57/0.59  fof(f90,plain,(
% 1.57/0.59    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_relat_1(sK0))),
% 1.57/0.59    inference(definition_unfolding,[],[f52,f61])).
% 1.57/0.59  fof(f61,plain,(
% 1.57/0.59    ( ! [X0] : (k6_partfun1(X0) = k6_relat_1(X0)) )),
% 1.57/0.59    inference(cnf_transformation,[],[f18])).
% 1.57/0.59  fof(f18,axiom,(
% 1.57/0.59    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0)),
% 1.57/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.57/0.59  fof(f52,plain,(
% 1.57/0.59    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))),
% 1.57/0.59    inference(cnf_transformation,[],[f22])).
% 1.57/0.59  fof(f381,plain,(
% 1.57/0.59    ( ! [X4,X3] : (~r2_relset_1(X4,X4,X3,k6_relat_1(X4)) | k6_relat_1(X4) = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X4)))) )),
% 1.57/0.59    inference(resolution,[],[f86,f91])).
% 1.57/0.59  fof(f91,plain,(
% 1.57/0.59    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.57/0.59    inference(definition_unfolding,[],[f63,f61])).
% 1.57/0.59  fof(f63,plain,(
% 1.57/0.59    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.57/0.59    inference(cnf_transformation,[],[f15])).
% 1.57/0.59  fof(f15,axiom,(
% 1.57/0.59    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 1.57/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 1.57/0.59  fof(f86,plain,(
% 1.57/0.59    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 = X3 | ~r2_relset_1(X0,X1,X2,X3)) )),
% 1.57/0.59    inference(cnf_transformation,[],[f43])).
% 1.57/0.60  fof(f524,plain,(
% 1.57/0.60    spl3_40 | ~spl3_10 | ~spl3_9 | ~spl3_25),
% 1.57/0.60    inference(avatar_split_clause,[],[f518,f307,f180,f184,f521])).
% 1.57/0.60  fof(f180,plain,(
% 1.57/0.60    spl3_9 <=> v3_funct_2(sK1,sK0,sK0)),
% 1.57/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 1.57/0.60  fof(f307,plain,(
% 1.57/0.60    spl3_25 <=> v1_funct_2(sK1,sK0,sK0)),
% 1.57/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 1.57/0.60  fof(f518,plain,(
% 1.57/0.60    ~v1_funct_2(sK1,sK0,sK0) | ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | k2_funct_2(sK0,sK1) = k2_funct_1(sK1)),
% 1.57/0.60    inference(resolution,[],[f71,f57])).
% 1.57/0.60  fof(f71,plain,(
% 1.57/0.60    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_1(X1) | k2_funct_2(X0,X1) = k2_funct_1(X1)) )),
% 1.57/0.60    inference(cnf_transformation,[],[f32])).
% 1.57/0.60  fof(f32,plain,(
% 1.57/0.60    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 1.57/0.60    inference(flattening,[],[f31])).
% 1.57/0.60  fof(f31,plain,(
% 1.57/0.60    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 1.57/0.60    inference(ennf_transformation,[],[f17])).
% 1.57/0.60  fof(f17,axiom,(
% 1.57/0.60    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_2(X0,X1) = k2_funct_1(X1))),
% 1.57/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).
% 1.57/0.60  fof(f503,plain,(
% 1.57/0.60    spl3_38),
% 1.57/0.60    inference(avatar_contradiction_clause,[],[f502])).
% 1.57/0.60  fof(f502,plain,(
% 1.57/0.60    $false | spl3_38),
% 1.57/0.60    inference(subsumption_resolution,[],[f51,f411])).
% 1.57/0.60  fof(f411,plain,(
% 1.57/0.60    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl3_38),
% 1.57/0.60    inference(avatar_component_clause,[],[f409])).
% 1.57/0.60  fof(f497,plain,(
% 1.57/0.60    ~spl3_25 | spl3_26 | spl3_27),
% 1.57/0.60    inference(avatar_split_clause,[],[f491,f315,f311,f307])).
% 1.57/0.60  fof(f311,plain,(
% 1.57/0.60    spl3_26 <=> sK0 = k1_relset_1(sK0,sK0,sK1)),
% 1.57/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 1.57/0.60  fof(f491,plain,(
% 1.57/0.60    k1_xboole_0 = sK0 | sK0 = k1_relset_1(sK0,sK0,sK1) | ~v1_funct_2(sK1,sK0,sK0)),
% 1.57/0.60    inference(resolution,[],[f57,f81])).
% 1.57/0.60  fof(f419,plain,(
% 1.57/0.60    spl3_36),
% 1.57/0.60    inference(avatar_contradiction_clause,[],[f418])).
% 1.57/0.60  fof(f418,plain,(
% 1.57/0.60    $false | spl3_36),
% 1.57/0.60    inference(subsumption_resolution,[],[f57,f397])).
% 1.57/0.60  fof(f397,plain,(
% 1.57/0.60    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl3_36),
% 1.57/0.60    inference(avatar_component_clause,[],[f395])).
% 1.57/0.60  fof(f417,plain,(
% 1.57/0.60    ~spl3_38 | spl3_39 | ~spl3_29),
% 1.57/0.60    inference(avatar_split_clause,[],[f406,f324,f413,f409])).
% 1.57/0.60  fof(f406,plain,(
% 1.57/0.60    sK0 = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl3_29),
% 1.57/0.60    inference(superposition,[],[f73,f326])).
% 1.57/0.60  fof(f326,plain,(
% 1.57/0.60    sK0 = k1_relset_1(sK0,sK0,sK2) | ~spl3_29),
% 1.57/0.60    inference(avatar_component_clause,[],[f324])).
% 1.57/0.60  fof(f403,plain,(
% 1.57/0.60    ~spl3_36 | spl3_37 | ~spl3_26),
% 1.57/0.60    inference(avatar_split_clause,[],[f392,f311,f399,f395])).
% 1.57/0.60  fof(f392,plain,(
% 1.57/0.60    sK0 = k1_relat_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl3_26),
% 1.57/0.60    inference(superposition,[],[f73,f313])).
% 1.57/0.60  fof(f313,plain,(
% 1.57/0.60    sK0 = k1_relset_1(sK0,sK0,sK1) | ~spl3_26),
% 1.57/0.60    inference(avatar_component_clause,[],[f311])).
% 1.57/0.60  fof(f331,plain,(
% 1.57/0.60    spl3_28),
% 1.57/0.60    inference(avatar_contradiction_clause,[],[f330])).
% 1.57/0.60  fof(f330,plain,(
% 1.57/0.60    $false | spl3_28),
% 1.57/0.60    inference(subsumption_resolution,[],[f49,f322])).
% 1.57/0.60  fof(f322,plain,(
% 1.57/0.60    ~v1_funct_2(sK2,sK0,sK0) | spl3_28),
% 1.57/0.60    inference(avatar_component_clause,[],[f320])).
% 1.57/0.60  fof(f49,plain,(
% 1.57/0.60    v1_funct_2(sK2,sK0,sK0)),
% 1.57/0.60    inference(cnf_transformation,[],[f22])).
% 1.57/0.60  fof(f329,plain,(
% 1.57/0.60    spl3_25),
% 1.57/0.60    inference(avatar_contradiction_clause,[],[f328])).
% 1.57/0.60  fof(f328,plain,(
% 1.57/0.60    $false | spl3_25),
% 1.57/0.60    inference(subsumption_resolution,[],[f55,f309])).
% 1.57/0.60  fof(f309,plain,(
% 1.57/0.60    ~v1_funct_2(sK1,sK0,sK0) | spl3_25),
% 1.57/0.60    inference(avatar_component_clause,[],[f307])).
% 1.57/0.60  fof(f55,plain,(
% 1.57/0.60    v1_funct_2(sK1,sK0,sK0)),
% 1.57/0.60    inference(cnf_transformation,[],[f22])).
% 1.57/0.60  fof(f301,plain,(
% 1.57/0.60    spl3_23),
% 1.57/0.60    inference(avatar_contradiction_clause,[],[f298])).
% 1.57/0.60  fof(f298,plain,(
% 1.57/0.60    $false | spl3_23),
% 1.57/0.60    inference(subsumption_resolution,[],[f104,f276])).
% 1.57/0.60  fof(f276,plain,(
% 1.57/0.60    ~v1_relat_1(sK2) | spl3_23),
% 1.57/0.60    inference(avatar_component_clause,[],[f274])).
% 1.57/0.60  fof(f297,plain,(
% 1.57/0.60    spl3_24),
% 1.57/0.60    inference(avatar_contradiction_clause,[],[f294])).
% 1.57/0.60  fof(f294,plain,(
% 1.57/0.60    $false | spl3_24),
% 1.57/0.60    inference(subsumption_resolution,[],[f114,f280])).
% 1.57/0.60  fof(f280,plain,(
% 1.57/0.60    ~v5_relat_1(sK2,sK0) | spl3_24),
% 1.57/0.60    inference(avatar_component_clause,[],[f278])).
% 1.57/0.60  fof(f285,plain,(
% 1.57/0.60    spl3_20),
% 1.57/0.60    inference(avatar_contradiction_clause,[],[f282])).
% 1.57/0.60  fof(f282,plain,(
% 1.57/0.60    $false | spl3_20),
% 1.57/0.60    inference(subsumption_resolution,[],[f103,f264])).
% 1.57/0.60  fof(f264,plain,(
% 1.57/0.60    ~v1_relat_1(sK1) | spl3_20),
% 1.57/0.60    inference(avatar_component_clause,[],[f262])).
% 1.57/0.60  fof(f226,plain,(
% 1.57/0.60    spl3_12),
% 1.57/0.60    inference(avatar_contradiction_clause,[],[f225])).
% 1.57/0.60  fof(f225,plain,(
% 1.57/0.60    $false | spl3_12),
% 1.57/0.60    inference(subsumption_resolution,[],[f50,f195])).
% 1.57/0.60  fof(f195,plain,(
% 1.57/0.60    ~v3_funct_2(sK2,sK0,sK0) | spl3_12),
% 1.57/0.60    inference(avatar_component_clause,[],[f193])).
% 1.57/0.60  fof(f193,plain,(
% 1.57/0.60    spl3_12 <=> v3_funct_2(sK2,sK0,sK0)),
% 1.57/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 1.57/0.60  fof(f50,plain,(
% 1.57/0.60    v3_funct_2(sK2,sK0,sK0)),
% 1.57/0.60    inference(cnf_transformation,[],[f22])).
% 1.57/0.60  fof(f224,plain,(
% 1.57/0.60    spl3_10),
% 1.57/0.60    inference(avatar_contradiction_clause,[],[f223])).
% 1.57/0.60  fof(f223,plain,(
% 1.57/0.60    $false | spl3_10),
% 1.57/0.60    inference(subsumption_resolution,[],[f54,f186])).
% 1.57/0.60  fof(f186,plain,(
% 1.57/0.60    ~v1_funct_1(sK1) | spl3_10),
% 1.57/0.60    inference(avatar_component_clause,[],[f184])).
% 1.57/0.60  fof(f222,plain,(
% 1.57/0.60    spl3_9),
% 1.57/0.60    inference(avatar_contradiction_clause,[],[f221])).
% 1.57/0.60  fof(f221,plain,(
% 1.57/0.60    $false | spl3_9),
% 1.57/0.60    inference(subsumption_resolution,[],[f56,f182])).
% 1.57/0.60  fof(f182,plain,(
% 1.57/0.60    ~v3_funct_2(sK1,sK0,sK0) | spl3_9),
% 1.57/0.60    inference(avatar_component_clause,[],[f180])).
% 1.57/0.60  fof(f56,plain,(
% 1.57/0.60    v3_funct_2(sK1,sK0,sK0)),
% 1.57/0.60    inference(cnf_transformation,[],[f22])).
% 1.57/0.60  fof(f220,plain,(
% 1.57/0.60    spl3_16 | ~spl3_12 | ~spl3_13),
% 1.57/0.60    inference(avatar_split_clause,[],[f206,f197,f193,f217])).
% 1.57/0.60  fof(f206,plain,(
% 1.57/0.60    ~v1_funct_1(sK2) | ~v3_funct_2(sK2,sK0,sK0) | v2_funct_2(sK2,sK0)),
% 1.57/0.60    inference(resolution,[],[f83,f51])).
% 1.57/0.60  fof(f83,plain,(
% 1.57/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | v2_funct_2(X2,X1)) )),
% 1.57/0.60    inference(cnf_transformation,[],[f39])).
% 1.57/0.60  fof(f39,plain,(
% 1.57/0.60    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.57/0.60    inference(flattening,[],[f38])).
% 1.57/0.60  fof(f38,plain,(
% 1.57/0.60    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.57/0.60    inference(ennf_transformation,[],[f11])).
% 1.57/0.60  fof(f11,axiom,(
% 1.57/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 1.57/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).
% 1.57/0.60  fof(f215,plain,(
% 1.57/0.60    spl3_15 | ~spl3_9 | ~spl3_10),
% 1.57/0.60    inference(avatar_split_clause,[],[f205,f184,f180,f212])).
% 1.57/0.60  fof(f205,plain,(
% 1.57/0.60    ~v1_funct_1(sK1) | ~v3_funct_2(sK1,sK0,sK0) | v2_funct_2(sK1,sK0)),
% 1.57/0.60    inference(resolution,[],[f83,f57])).
% 1.57/0.60  fof(f202,plain,(
% 1.57/0.60    spl3_13),
% 1.57/0.60    inference(avatar_contradiction_clause,[],[f201])).
% 1.57/0.60  fof(f201,plain,(
% 1.57/0.60    $false | spl3_13),
% 1.57/0.60    inference(subsumption_resolution,[],[f48,f199])).
% 1.57/0.60  fof(f199,plain,(
% 1.57/0.60    ~v1_funct_1(sK2) | spl3_13),
% 1.57/0.60    inference(avatar_component_clause,[],[f197])).
% 1.57/0.60  fof(f200,plain,(
% 1.57/0.60    spl3_11 | ~spl3_12 | ~spl3_13),
% 1.57/0.60    inference(avatar_split_clause,[],[f162,f197,f193,f189])).
% 1.57/0.60  fof(f162,plain,(
% 1.57/0.60    ~v1_funct_1(sK2) | ~v3_funct_2(sK2,sK0,sK0) | v2_funct_1(sK2)),
% 1.57/0.60    inference(resolution,[],[f82,f51])).
% 1.57/0.60  fof(f82,plain,(
% 1.57/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | v2_funct_1(X2)) )),
% 1.57/0.60    inference(cnf_transformation,[],[f39])).
% 1.57/0.60  fof(f187,plain,(
% 1.57/0.60    spl3_8 | ~spl3_9 | ~spl3_10),
% 1.57/0.60    inference(avatar_split_clause,[],[f161,f184,f180,f176])).
% 1.57/0.60  fof(f161,plain,(
% 1.57/0.60    ~v1_funct_1(sK1) | ~v3_funct_2(sK1,sK0,sK0) | v2_funct_1(sK1)),
% 1.57/0.60    inference(resolution,[],[f82,f57])).
% 1.57/0.60  % SZS output end Proof for theBenchmark
% 1.57/0.60  % (20180)------------------------------
% 1.57/0.60  % (20180)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.60  % (20180)Termination reason: Refutation
% 1.57/0.60  
% 1.57/0.60  % (20180)Memory used [KB]: 6780
% 1.57/0.60  % (20180)Time elapsed: 0.149 s
% 1.57/0.60  % (20180)------------------------------
% 1.57/0.60  % (20180)------------------------------
% 1.57/0.60  % (20157)Success in time 0.238 s
%------------------------------------------------------------------------------
