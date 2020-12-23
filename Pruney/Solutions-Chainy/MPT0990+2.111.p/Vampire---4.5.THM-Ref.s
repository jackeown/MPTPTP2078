%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:47 EST 2020

% Result     : Theorem 1.53s
% Output     : Refutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :  211 ( 404 expanded)
%              Number of leaves         :   48 ( 148 expanded)
%              Depth                    :   12
%              Number of atoms          :  656 (1680 expanded)
%              Number of equality atoms :  118 ( 436 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2181,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f117,f126,f130,f134,f227,f229,f241,f311,f313,f319,f438,f444,f633,f635,f863,f876,f883,f912,f931,f948,f1198,f1732,f1745,f1781,f2112,f2164])).

fof(f2164,plain,(
    ~ spl4_141 ),
    inference(avatar_contradiction_clause,[],[f2125])).

fof(f2125,plain,
    ( $false
    | ~ spl4_141 ),
    inference(subsumption_resolution,[],[f59,f2111])).

fof(f2111,plain,
    ( sK3 = k2_funct_1(sK2)
    | ~ spl4_141 ),
    inference(avatar_component_clause,[],[f2109])).

fof(f2109,plain,
    ( spl4_141
  <=> sK3 = k2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_141])])).

fof(f59,plain,(
    sK3 != k2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
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
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
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

fof(f2112,plain,
    ( ~ spl4_19
    | ~ spl4_9
    | ~ spl4_20
    | ~ spl4_1
    | ~ spl4_3
    | spl4_141
    | ~ spl4_6
    | ~ spl4_54
    | ~ spl4_80
    | ~ spl4_118 ),
    inference(avatar_split_clause,[],[f2107,f1778,f1195,f869,f223,f2109,f119,f110,f429,f300,f425])).

fof(f425,plain,
    ( spl4_19
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f300,plain,
    ( spl4_9
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f429,plain,
    ( spl4_20
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f110,plain,
    ( spl4_1
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f119,plain,
    ( spl4_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f223,plain,
    ( spl4_6
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f869,plain,
    ( spl4_54
  <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).

fof(f1195,plain,
    ( spl4_80
  <=> k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_80])])).

fof(f1778,plain,
    ( spl4_118
  <=> sK3 = k5_relat_1(k6_partfun1(sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_118])])).

fof(f2107,plain,
    ( sK3 = k2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ spl4_6
    | ~ spl4_54
    | ~ spl4_80
    | ~ spl4_118 ),
    inference(forward_demodulation,[],[f2106,f1197])).

fof(f1197,plain,
    ( k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0))
    | ~ spl4_80 ),
    inference(avatar_component_clause,[],[f1195])).

fof(f2106,plain,
    ( sK3 = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0))
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ spl4_6
    | ~ spl4_54
    | ~ spl4_118 ),
    inference(forward_demodulation,[],[f2105,f1780])).

fof(f1780,plain,
    ( sK3 = k5_relat_1(k6_partfun1(sK1),sK3)
    | ~ spl4_118 ),
    inference(avatar_component_clause,[],[f1778])).

fof(f2105,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k6_partfun1(sK1),sK3)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ spl4_6
    | ~ spl4_54 ),
    inference(forward_demodulation,[],[f2027,f225])).

fof(f225,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f223])).

fof(f2027,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k6_partfun1(k2_relat_1(sK2)),sK3)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ spl4_54 ),
    inference(superposition,[],[f374,f871])).

fof(f871,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl4_54 ),
    inference(avatar_component_clause,[],[f869])).

fof(f374,plain,(
    ! [X8,X9] :
      ( k5_relat_1(k2_funct_1(X8),k5_relat_1(X8,X9)) = k5_relat_1(k6_partfun1(k2_relat_1(X8)),X9)
      | ~ v1_relat_1(X8)
      | ~ v1_relat_1(X9)
      | ~ v1_relat_1(k2_funct_1(X8))
      | ~ v1_funct_1(X8)
      | ~ v2_funct_1(X8) ) ),
    inference(duplicate_literal_removal,[],[f360])).

fof(f360,plain,(
    ! [X8,X9] :
      ( k5_relat_1(k2_funct_1(X8),k5_relat_1(X8,X9)) = k5_relat_1(k6_partfun1(k2_relat_1(X8)),X9)
      | ~ v1_relat_1(X8)
      | ~ v1_relat_1(X9)
      | ~ v1_relat_1(k2_funct_1(X8))
      | ~ v1_funct_1(X8)
      | ~ v2_funct_1(X8)
      | ~ v1_relat_1(X8) ) ),
    inference(superposition,[],[f72,f100])).

fof(f100,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f79,f63])).

fof(f63,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f79,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
          & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

fof(f1781,plain,
    ( ~ spl4_1
    | spl4_118
    | ~ spl4_112 ),
    inference(avatar_split_clause,[],[f1750,f1725,f1778,f110])).

fof(f1725,plain,
    ( spl4_112
  <=> sK1 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_112])])).

fof(f1750,plain,
    ( sK3 = k5_relat_1(k6_partfun1(sK1),sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_112 ),
    inference(superposition,[],[f99,f1727])).

fof(f1727,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl4_112 ),
    inference(avatar_component_clause,[],[f1725])).

fof(f99,plain,(
    ! [X0] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f70,f63])).

fof(f70,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).

fof(f1745,plain,
    ( ~ spl4_1
    | spl4_113 ),
    inference(avatar_contradiction_clause,[],[f1743])).

fof(f1743,plain,
    ( $false
    | ~ spl4_1
    | spl4_113 ),
    inference(unit_resulting_resolution,[],[f112,f150,f1731,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f1731,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),sK1)
    | spl4_113 ),
    inference(avatar_component_clause,[],[f1729])).

fof(f1729,plain,
    ( spl4_113
  <=> r1_tarski(k1_relat_1(sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_113])])).

fof(f150,plain,(
    v4_relat_1(sK3,sK1) ),
    inference(resolution,[],[f89,f53])).

fof(f53,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f112,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f110])).

fof(f1732,plain,
    ( ~ spl4_1
    | ~ spl4_3
    | ~ spl4_9
    | spl4_112
    | ~ spl4_113
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_54
    | ~ spl4_61 ),
    inference(avatar_split_clause,[],[f1723,f928,f869,f304,f223,f1729,f1725,f300,f119,f110])).

fof(f304,plain,
    ( spl4_10
  <=> sK1 = k9_relat_1(sK2,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f928,plain,
    ( spl4_61
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_61])])).

fof(f1723,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),sK1)
    | sK1 = k1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_54
    | ~ spl4_61 ),
    inference(forward_demodulation,[],[f1722,f225])).

fof(f1722,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ r1_tarski(k1_relat_1(sK3),k2_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ spl4_10
    | ~ spl4_54
    | ~ spl4_61 ),
    inference(forward_demodulation,[],[f1721,f950])).

fof(f950,plain,
    ( sK1 = k9_relat_1(sK2,sK0)
    | ~ spl4_10
    | ~ spl4_61 ),
    inference(superposition,[],[f306,f930])).

fof(f930,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl4_61 ),
    inference(avatar_component_clause,[],[f928])).

fof(f306,plain,
    ( sK1 = k9_relat_1(sK2,k1_relat_1(sK2))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f304])).

fof(f1721,plain,
    ( k1_relat_1(sK3) = k9_relat_1(sK2,sK0)
    | ~ v1_funct_1(sK2)
    | ~ r1_tarski(k1_relat_1(sK3),k2_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ spl4_54 ),
    inference(forward_demodulation,[],[f1641,f97])).

fof(f97,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f66,f63])).

fof(f66,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f1641,plain,
    ( k1_relat_1(sK3) = k9_relat_1(sK2,k1_relat_1(k6_partfun1(sK0)))
    | ~ v1_funct_1(sK2)
    | ~ r1_tarski(k1_relat_1(sK3),k2_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ spl4_54 ),
    inference(superposition,[],[f295,f871])).

fof(f295,plain,(
    ! [X2,X1] :
      ( k1_relat_1(X2) = k9_relat_1(X1,k1_relat_1(k5_relat_1(X1,X2)))
      | ~ v1_funct_1(X1)
      | ~ r1_tarski(k1_relat_1(X2),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2) ) ),
    inference(duplicate_literal_removal,[],[f289])).

fof(f289,plain,(
    ! [X2,X1] :
      ( k1_relat_1(X2) = k9_relat_1(X1,k1_relat_1(k5_relat_1(X1,X2)))
      | ~ v1_funct_1(X1)
      | ~ r1_tarski(k1_relat_1(X2),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f84,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

fof(f84,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ v1_funct_1(X1)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

fof(f1198,plain,
    ( ~ spl4_3
    | ~ spl4_19
    | ~ spl4_9
    | ~ spl4_20
    | spl4_80
    | ~ spl4_61 ),
    inference(avatar_split_clause,[],[f1181,f928,f1195,f429,f300,f425,f119])).

fof(f1181,plain,
    ( k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_61 ),
    inference(superposition,[],[f183,f930])).

fof(f183,plain,(
    ! [X0] :
      ( k2_funct_1(X0) = k5_relat_1(k2_funct_1(X0),k6_partfun1(k1_relat_1(X0)))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f98,f77])).

fof(f77,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f98,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f69,f63])).

fof(f69,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

fof(f948,plain,(
    spl4_60 ),
    inference(avatar_contradiction_clause,[],[f945])).

fof(f945,plain,
    ( $false
    | spl4_60 ),
    inference(subsumption_resolution,[],[f151,f926])).

fof(f926,plain,
    ( ~ v4_relat_1(sK2,sK0)
    | spl4_60 ),
    inference(avatar_component_clause,[],[f924])).

fof(f924,plain,
    ( spl4_60
  <=> v4_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_60])])).

fof(f151,plain,(
    v4_relat_1(sK2,sK0) ),
    inference(resolution,[],[f89,f62])).

fof(f62,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f26])).

fof(f931,plain,
    ( ~ spl4_60
    | ~ spl4_3
    | spl4_61
    | ~ spl4_59 ),
    inference(avatar_split_clause,[],[f921,f909,f928,f119,f924])).

fof(f909,plain,
    ( spl4_59
  <=> r1_tarski(sK0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_59])])).

fof(f921,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v4_relat_1(sK2,sK0)
    | ~ spl4_59 ),
    inference(resolution,[],[f911,f149])).

fof(f149,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(X3,k1_relat_1(X4))
      | k1_relat_1(X4) = X3
      | ~ v1_relat_1(X4)
      | ~ v4_relat_1(X4,X3) ) ),
    inference(resolution,[],[f87,f83])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f911,plain,
    ( r1_tarski(sK0,k1_relat_1(sK2))
    | ~ spl4_59 ),
    inference(avatar_component_clause,[],[f909])).

fof(f912,plain,
    ( ~ spl4_1
    | ~ spl4_3
    | spl4_59
    | ~ spl4_54 ),
    inference(avatar_split_clause,[],[f907,f869,f909,f119,f110])).

fof(f907,plain,
    ( r1_tarski(sK0,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ spl4_54 ),
    inference(forward_demodulation,[],[f893,f97])).

fof(f893,plain,
    ( r1_tarski(k1_relat_1(k6_partfun1(sK0)),k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ spl4_54 ),
    inference(superposition,[],[f193,f871])).

fof(f193,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1) ) ),
    inference(duplicate_literal_removal,[],[f188])).

fof(f188,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f81,f71])).

fof(f81,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

fof(f883,plain,
    ( ~ spl4_9
    | ~ spl4_35
    | ~ spl4_36
    | ~ spl4_5
    | spl4_54
    | ~ spl4_52 ),
    inference(avatar_split_clause,[],[f880,f860,f869,f219,f624,f620,f300])).

fof(f620,plain,
    ( spl4_35
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f624,plain,
    ( spl4_36
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f219,plain,
    ( spl4_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f860,plain,
    ( spl4_52
  <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).

fof(f880,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_52 ),
    inference(superposition,[],[f93,f862])).

fof(f862,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | ~ spl4_52 ),
    inference(avatar_component_clause,[],[f860])).

fof(f93,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f876,plain,(
    spl4_51 ),
    inference(avatar_contradiction_clause,[],[f873])).

fof(f873,plain,
    ( $false
    | spl4_51 ),
    inference(unit_resulting_resolution,[],[f60,f51,f53,f62,f858,f95])).

fof(f95,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f858,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl4_51 ),
    inference(avatar_component_clause,[],[f856])).

fof(f856,plain,
    ( spl4_51
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_51])])).

fof(f51,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f60,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f863,plain,
    ( ~ spl4_51
    | spl4_52 ),
    inference(avatar_split_clause,[],[f852,f860,f856])).

fof(f852,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f440,f55])).

fof(f55,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f26])).

fof(f440,plain,(
    ! [X2,X1] :
      ( ~ r2_relset_1(X2,X2,X1,k6_partfun1(X2))
      | k6_partfun1(X2) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ) ),
    inference(resolution,[],[f92,f65])).

fof(f65,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f92,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f635,plain,(
    spl4_36 ),
    inference(avatar_contradiction_clause,[],[f634])).

fof(f634,plain,
    ( $false
    | spl4_36 ),
    inference(subsumption_resolution,[],[f51,f626])).

fof(f626,plain,
    ( ~ v1_funct_1(sK3)
    | spl4_36 ),
    inference(avatar_component_clause,[],[f624])).

fof(f633,plain,(
    spl4_35 ),
    inference(avatar_contradiction_clause,[],[f632])).

fof(f632,plain,
    ( $false
    | spl4_35 ),
    inference(subsumption_resolution,[],[f53,f622])).

fof(f622,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl4_35 ),
    inference(avatar_component_clause,[],[f620])).

fof(f444,plain,
    ( ~ spl4_3
    | spl4_20 ),
    inference(avatar_contradiction_clause,[],[f442])).

fof(f442,plain,
    ( $false
    | ~ spl4_3
    | spl4_20 ),
    inference(unit_resulting_resolution,[],[f121,f60,f431,f74])).

fof(f74,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f431,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | spl4_20 ),
    inference(avatar_component_clause,[],[f429])).

fof(f121,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f119])).

fof(f438,plain,(
    spl4_19 ),
    inference(avatar_contradiction_clause,[],[f437])).

fof(f437,plain,
    ( $false
    | spl4_19 ),
    inference(subsumption_resolution,[],[f56,f427])).

fof(f427,plain,
    ( ~ v2_funct_1(sK2)
    | spl4_19 ),
    inference(avatar_component_clause,[],[f425])).

fof(f56,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f319,plain,(
    spl4_11 ),
    inference(avatar_contradiction_clause,[],[f315])).

fof(f315,plain,
    ( $false
    | spl4_11 ),
    inference(unit_resulting_resolution,[],[f136,f152,f310,f145])).

fof(f145,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(k6_partfun1(X0),X1)
      | ~ v1_relat_1(k6_partfun1(X0))
      | r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f83,f97])).

fof(f310,plain,
    ( ~ r1_tarski(sK1,sK1)
    | spl4_11 ),
    inference(avatar_component_clause,[],[f308])).

fof(f308,plain,
    ( spl4_11
  <=> r1_tarski(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f152,plain,(
    ! [X0] : v4_relat_1(k6_partfun1(X0),X0) ),
    inference(resolution,[],[f89,f65])).

fof(f136,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(resolution,[],[f108,f80])).

fof(f80,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f108,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k2_zfmisc_1(X0,X0))
      | v1_relat_1(k6_partfun1(X0)) ) ),
    inference(resolution,[],[f73,f65])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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

fof(f313,plain,(
    spl4_9 ),
    inference(avatar_contradiction_clause,[],[f312])).

fof(f312,plain,
    ( $false
    | spl4_9 ),
    inference(subsumption_resolution,[],[f60,f302])).

fof(f302,plain,
    ( ~ v1_funct_1(sK2)
    | spl4_9 ),
    inference(avatar_component_clause,[],[f300])).

fof(f311,plain,
    ( ~ spl4_3
    | ~ spl4_9
    | spl4_10
    | ~ spl4_11
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f298,f238,f223,f308,f304,f300,f119])).

fof(f238,plain,
    ( spl4_8
  <=> k1_relat_1(sK2) = k10_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f298,plain,
    ( ~ r1_tarski(sK1,sK1)
    | sK1 = k9_relat_1(sK2,k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(forward_demodulation,[],[f292,f225])).

fof(f292,plain,
    ( sK1 = k9_relat_1(sK2,k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ r1_tarski(sK1,k2_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl4_8 ),
    inference(superposition,[],[f84,f240])).

fof(f240,plain,
    ( k1_relat_1(sK2) = k10_relat_1(sK2,sK1)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f238])).

fof(f241,plain,
    ( ~ spl4_3
    | spl4_8
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f231,f223,f238,f119])).

fof(f231,plain,
    ( k1_relat_1(sK2) = k10_relat_1(sK2,sK1)
    | ~ v1_relat_1(sK2)
    | ~ spl4_6 ),
    inference(superposition,[],[f68,f225])).

fof(f68,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(f229,plain,(
    spl4_5 ),
    inference(avatar_contradiction_clause,[],[f228])).

fof(f228,plain,
    ( $false
    | spl4_5 ),
    inference(subsumption_resolution,[],[f62,f221])).

fof(f221,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl4_5 ),
    inference(avatar_component_clause,[],[f219])).

fof(f227,plain,
    ( ~ spl4_5
    | spl4_6 ),
    inference(avatar_split_clause,[],[f217,f223,f219])).

fof(f217,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f54,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f54,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f134,plain,(
    spl4_4 ),
    inference(avatar_contradiction_clause,[],[f131])).

fof(f131,plain,
    ( $false
    | spl4_4 ),
    inference(unit_resulting_resolution,[],[f80,f125])).

fof(f125,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl4_4 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl4_4
  <=> v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f130,plain,(
    spl4_2 ),
    inference(avatar_contradiction_clause,[],[f127])).

fof(f127,plain,
    ( $false
    | spl4_2 ),
    inference(unit_resulting_resolution,[],[f80,f116])).

fof(f116,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl4_2
  <=> v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f126,plain,
    ( spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f107,f123,f119])).

fof(f107,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK2) ),
    inference(resolution,[],[f73,f62])).

fof(f117,plain,
    ( spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f106,f114,f110])).

fof(f106,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK3) ),
    inference(resolution,[],[f73,f53])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:16:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (18545)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.51  % (18546)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.51  % (18547)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.51  % (18542)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.52  % (18549)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (18555)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.52  % (18559)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.52  % (18559)Refutation not found, incomplete strategy% (18559)------------------------------
% 0.22/0.52  % (18559)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (18559)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (18559)Memory used [KB]: 10746
% 0.22/0.52  % (18559)Time elapsed: 0.106 s
% 0.22/0.52  % (18559)------------------------------
% 0.22/0.52  % (18559)------------------------------
% 0.22/0.52  % (18562)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.53  % (18544)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.53  % (18566)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.53  % (18551)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.53  % (18553)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.53  % (18568)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.53  % (18558)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.53  % (18570)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.53  % (18548)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.53  % (18567)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.53  % (18573)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.54  % (18556)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.54  % (18572)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.54  % (18557)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.54  % (18565)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.54  % (18550)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.40/0.54  % (18569)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.40/0.55  % (18563)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.40/0.55  % (18554)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.40/0.55  % (18564)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.40/0.55  % (18560)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.40/0.55  % (18552)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.40/0.56  % (18571)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.53/0.61  % (18556)Refutation found. Thanks to Tanya!
% 1.53/0.61  % SZS status Theorem for theBenchmark
% 2.06/0.63  % SZS output start Proof for theBenchmark
% 2.06/0.63  fof(f2181,plain,(
% 2.06/0.63    $false),
% 2.06/0.63    inference(avatar_sat_refutation,[],[f117,f126,f130,f134,f227,f229,f241,f311,f313,f319,f438,f444,f633,f635,f863,f876,f883,f912,f931,f948,f1198,f1732,f1745,f1781,f2112,f2164])).
% 2.06/0.63  fof(f2164,plain,(
% 2.06/0.63    ~spl4_141),
% 2.06/0.63    inference(avatar_contradiction_clause,[],[f2125])).
% 2.06/0.63  fof(f2125,plain,(
% 2.06/0.63    $false | ~spl4_141),
% 2.06/0.63    inference(subsumption_resolution,[],[f59,f2111])).
% 2.06/0.63  fof(f2111,plain,(
% 2.06/0.63    sK3 = k2_funct_1(sK2) | ~spl4_141),
% 2.06/0.63    inference(avatar_component_clause,[],[f2109])).
% 2.06/0.63  fof(f2109,plain,(
% 2.06/0.63    spl4_141 <=> sK3 = k2_funct_1(sK2)),
% 2.06/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_141])])).
% 2.06/0.63  fof(f59,plain,(
% 2.06/0.63    sK3 != k2_funct_1(sK2)),
% 2.06/0.63    inference(cnf_transformation,[],[f26])).
% 2.06/0.63  fof(f26,plain,(
% 2.06/0.63    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.06/0.63    inference(flattening,[],[f25])).
% 2.06/0.63  fof(f25,plain,(
% 2.06/0.63    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.06/0.63    inference(ennf_transformation,[],[f24])).
% 2.06/0.63  fof(f24,negated_conjecture,(
% 2.06/0.63    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.06/0.63    inference(negated_conjecture,[],[f23])).
% 2.06/0.63  fof(f23,conjecture,(
% 2.06/0.63    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.06/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).
% 2.06/0.63  fof(f2112,plain,(
% 2.06/0.63    ~spl4_19 | ~spl4_9 | ~spl4_20 | ~spl4_1 | ~spl4_3 | spl4_141 | ~spl4_6 | ~spl4_54 | ~spl4_80 | ~spl4_118),
% 2.06/0.63    inference(avatar_split_clause,[],[f2107,f1778,f1195,f869,f223,f2109,f119,f110,f429,f300,f425])).
% 2.06/0.63  fof(f425,plain,(
% 2.06/0.63    spl4_19 <=> v2_funct_1(sK2)),
% 2.06/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 2.06/0.63  fof(f300,plain,(
% 2.06/0.63    spl4_9 <=> v1_funct_1(sK2)),
% 2.06/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 2.06/0.63  fof(f429,plain,(
% 2.06/0.63    spl4_20 <=> v1_relat_1(k2_funct_1(sK2))),
% 2.06/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 2.06/0.63  fof(f110,plain,(
% 2.06/0.63    spl4_1 <=> v1_relat_1(sK3)),
% 2.06/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 2.06/0.63  fof(f119,plain,(
% 2.06/0.63    spl4_3 <=> v1_relat_1(sK2)),
% 2.06/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 2.06/0.63  fof(f223,plain,(
% 2.06/0.63    spl4_6 <=> sK1 = k2_relat_1(sK2)),
% 2.06/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 2.06/0.63  fof(f869,plain,(
% 2.06/0.63    spl4_54 <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 2.06/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).
% 2.06/0.63  fof(f1195,plain,(
% 2.06/0.63    spl4_80 <=> k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0))),
% 2.06/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_80])])).
% 2.06/0.63  fof(f1778,plain,(
% 2.06/0.63    spl4_118 <=> sK3 = k5_relat_1(k6_partfun1(sK1),sK3)),
% 2.06/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_118])])).
% 2.06/0.63  fof(f2107,plain,(
% 2.06/0.63    sK3 = k2_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_relat_1(sK3) | ~v1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | (~spl4_6 | ~spl4_54 | ~spl4_80 | ~spl4_118)),
% 2.06/0.63    inference(forward_demodulation,[],[f2106,f1197])).
% 2.06/0.63  fof(f1197,plain,(
% 2.06/0.63    k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) | ~spl4_80),
% 2.06/0.63    inference(avatar_component_clause,[],[f1195])).
% 2.06/0.63  fof(f2106,plain,(
% 2.06/0.63    sK3 = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) | ~v1_relat_1(sK2) | ~v1_relat_1(sK3) | ~v1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | (~spl4_6 | ~spl4_54 | ~spl4_118)),
% 2.06/0.63    inference(forward_demodulation,[],[f2105,f1780])).
% 2.06/0.63  fof(f1780,plain,(
% 2.06/0.63    sK3 = k5_relat_1(k6_partfun1(sK1),sK3) | ~spl4_118),
% 2.06/0.63    inference(avatar_component_clause,[],[f1778])).
% 2.06/0.63  fof(f2105,plain,(
% 2.06/0.63    k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k6_partfun1(sK1),sK3) | ~v1_relat_1(sK2) | ~v1_relat_1(sK3) | ~v1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | (~spl4_6 | ~spl4_54)),
% 2.06/0.63    inference(forward_demodulation,[],[f2027,f225])).
% 2.06/0.63  fof(f225,plain,(
% 2.06/0.63    sK1 = k2_relat_1(sK2) | ~spl4_6),
% 2.06/0.63    inference(avatar_component_clause,[],[f223])).
% 2.06/0.63  fof(f2027,plain,(
% 2.06/0.63    k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k6_partfun1(k2_relat_1(sK2)),sK3) | ~v1_relat_1(sK2) | ~v1_relat_1(sK3) | ~v1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~spl4_54),
% 2.06/0.63    inference(superposition,[],[f374,f871])).
% 2.06/0.63  fof(f871,plain,(
% 2.06/0.63    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~spl4_54),
% 2.06/0.63    inference(avatar_component_clause,[],[f869])).
% 2.06/0.63  fof(f374,plain,(
% 2.06/0.63    ( ! [X8,X9] : (k5_relat_1(k2_funct_1(X8),k5_relat_1(X8,X9)) = k5_relat_1(k6_partfun1(k2_relat_1(X8)),X9) | ~v1_relat_1(X8) | ~v1_relat_1(X9) | ~v1_relat_1(k2_funct_1(X8)) | ~v1_funct_1(X8) | ~v2_funct_1(X8)) )),
% 2.06/0.63    inference(duplicate_literal_removal,[],[f360])).
% 2.06/0.63  fof(f360,plain,(
% 2.06/0.63    ( ! [X8,X9] : (k5_relat_1(k2_funct_1(X8),k5_relat_1(X8,X9)) = k5_relat_1(k6_partfun1(k2_relat_1(X8)),X9) | ~v1_relat_1(X8) | ~v1_relat_1(X9) | ~v1_relat_1(k2_funct_1(X8)) | ~v1_funct_1(X8) | ~v2_funct_1(X8) | ~v1_relat_1(X8)) )),
% 2.06/0.63    inference(superposition,[],[f72,f100])).
% 2.06/0.63  fof(f100,plain,(
% 2.06/0.63    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.06/0.63    inference(definition_unfolding,[],[f79,f63])).
% 2.06/0.63  fof(f63,plain,(
% 2.06/0.63    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.06/0.63    inference(cnf_transformation,[],[f22])).
% 2.06/0.63  fof(f22,axiom,(
% 2.06/0.63    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.06/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 2.06/0.63  fof(f79,plain,(
% 2.06/0.63    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)) )),
% 2.06/0.63    inference(cnf_transformation,[],[f38])).
% 2.06/0.63  fof(f38,plain,(
% 2.06/0.63    ! [X0] : ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.06/0.63    inference(flattening,[],[f37])).
% 2.06/0.63  fof(f37,plain,(
% 2.06/0.63    ! [X0] : (((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.06/0.63    inference(ennf_transformation,[],[f15])).
% 2.06/0.63  fof(f15,axiom,(
% 2.06/0.63    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)))))),
% 2.06/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).
% 2.06/0.63  fof(f72,plain,(
% 2.06/0.63    ( ! [X2,X0,X1] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | ~v1_relat_1(X0)) )),
% 2.06/0.63    inference(cnf_transformation,[],[f31])).
% 2.06/0.63  fof(f31,plain,(
% 2.06/0.63    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.06/0.63    inference(ennf_transformation,[],[f8])).
% 2.06/0.63  fof(f8,axiom,(
% 2.06/0.63    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 2.06/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).
% 2.06/0.63  fof(f1781,plain,(
% 2.06/0.63    ~spl4_1 | spl4_118 | ~spl4_112),
% 2.06/0.63    inference(avatar_split_clause,[],[f1750,f1725,f1778,f110])).
% 2.06/0.63  fof(f1725,plain,(
% 2.06/0.63    spl4_112 <=> sK1 = k1_relat_1(sK3)),
% 2.06/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_112])])).
% 2.06/0.63  fof(f1750,plain,(
% 2.06/0.63    sK3 = k5_relat_1(k6_partfun1(sK1),sK3) | ~v1_relat_1(sK3) | ~spl4_112),
% 2.06/0.63    inference(superposition,[],[f99,f1727])).
% 2.06/0.63  fof(f1727,plain,(
% 2.06/0.63    sK1 = k1_relat_1(sK3) | ~spl4_112),
% 2.06/0.63    inference(avatar_component_clause,[],[f1725])).
% 2.06/0.63  fof(f99,plain,(
% 2.06/0.63    ( ! [X0] : (k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) )),
% 2.06/0.63    inference(definition_unfolding,[],[f70,f63])).
% 2.06/0.63  fof(f70,plain,(
% 2.06/0.63    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0) )),
% 2.06/0.63    inference(cnf_transformation,[],[f29])).
% 2.06/0.63  fof(f29,plain,(
% 2.06/0.63    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 2.06/0.63    inference(ennf_transformation,[],[f10])).
% 2.06/0.63  fof(f10,axiom,(
% 2.06/0.63    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 2.06/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).
% 2.06/0.63  fof(f1745,plain,(
% 2.06/0.63    ~spl4_1 | spl4_113),
% 2.06/0.63    inference(avatar_contradiction_clause,[],[f1743])).
% 2.06/0.63  fof(f1743,plain,(
% 2.06/0.63    $false | (~spl4_1 | spl4_113)),
% 2.06/0.63    inference(unit_resulting_resolution,[],[f112,f150,f1731,f83])).
% 2.06/0.63  fof(f83,plain,(
% 2.06/0.63    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1) | ~v4_relat_1(X1,X0)) )),
% 2.06/0.63    inference(cnf_transformation,[],[f40])).
% 2.06/0.63  fof(f40,plain,(
% 2.06/0.63    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.06/0.63    inference(ennf_transformation,[],[f3])).
% 2.06/0.63  fof(f3,axiom,(
% 2.06/0.63    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 2.06/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 2.06/0.63  fof(f1731,plain,(
% 2.06/0.63    ~r1_tarski(k1_relat_1(sK3),sK1) | spl4_113),
% 2.06/0.63    inference(avatar_component_clause,[],[f1729])).
% 2.06/0.63  fof(f1729,plain,(
% 2.06/0.63    spl4_113 <=> r1_tarski(k1_relat_1(sK3),sK1)),
% 2.06/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_113])])).
% 2.06/0.63  fof(f150,plain,(
% 2.06/0.63    v4_relat_1(sK3,sK1)),
% 2.06/0.63    inference(resolution,[],[f89,f53])).
% 2.06/0.63  fof(f53,plain,(
% 2.06/0.63    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.06/0.63    inference(cnf_transformation,[],[f26])).
% 2.06/0.63  fof(f89,plain,(
% 2.06/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 2.06/0.63    inference(cnf_transformation,[],[f44])).
% 2.06/0.63  fof(f44,plain,(
% 2.06/0.63    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.06/0.63    inference(ennf_transformation,[],[f16])).
% 2.06/0.63  fof(f16,axiom,(
% 2.06/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.06/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 2.06/0.63  fof(f112,plain,(
% 2.06/0.63    v1_relat_1(sK3) | ~spl4_1),
% 2.06/0.63    inference(avatar_component_clause,[],[f110])).
% 2.06/0.63  fof(f1732,plain,(
% 2.06/0.63    ~spl4_1 | ~spl4_3 | ~spl4_9 | spl4_112 | ~spl4_113 | ~spl4_6 | ~spl4_10 | ~spl4_54 | ~spl4_61),
% 2.06/0.63    inference(avatar_split_clause,[],[f1723,f928,f869,f304,f223,f1729,f1725,f300,f119,f110])).
% 2.06/0.63  fof(f304,plain,(
% 2.06/0.63    spl4_10 <=> sK1 = k9_relat_1(sK2,k1_relat_1(sK2))),
% 2.06/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 2.06/0.63  fof(f928,plain,(
% 2.06/0.63    spl4_61 <=> sK0 = k1_relat_1(sK2)),
% 2.06/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_61])])).
% 2.06/0.63  fof(f1723,plain,(
% 2.06/0.63    ~r1_tarski(k1_relat_1(sK3),sK1) | sK1 = k1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_relat_1(sK3) | (~spl4_6 | ~spl4_10 | ~spl4_54 | ~spl4_61)),
% 2.06/0.63    inference(forward_demodulation,[],[f1722,f225])).
% 2.06/0.63  fof(f1722,plain,(
% 2.06/0.63    sK1 = k1_relat_1(sK3) | ~v1_funct_1(sK2) | ~r1_tarski(k1_relat_1(sK3),k2_relat_1(sK2)) | ~v1_relat_1(sK2) | ~v1_relat_1(sK3) | (~spl4_10 | ~spl4_54 | ~spl4_61)),
% 2.06/0.63    inference(forward_demodulation,[],[f1721,f950])).
% 2.06/0.63  fof(f950,plain,(
% 2.06/0.63    sK1 = k9_relat_1(sK2,sK0) | (~spl4_10 | ~spl4_61)),
% 2.06/0.63    inference(superposition,[],[f306,f930])).
% 2.06/0.63  fof(f930,plain,(
% 2.06/0.63    sK0 = k1_relat_1(sK2) | ~spl4_61),
% 2.06/0.63    inference(avatar_component_clause,[],[f928])).
% 2.06/0.63  fof(f306,plain,(
% 2.06/0.63    sK1 = k9_relat_1(sK2,k1_relat_1(sK2)) | ~spl4_10),
% 2.06/0.63    inference(avatar_component_clause,[],[f304])).
% 2.06/0.63  fof(f1721,plain,(
% 2.06/0.63    k1_relat_1(sK3) = k9_relat_1(sK2,sK0) | ~v1_funct_1(sK2) | ~r1_tarski(k1_relat_1(sK3),k2_relat_1(sK2)) | ~v1_relat_1(sK2) | ~v1_relat_1(sK3) | ~spl4_54),
% 2.06/0.63    inference(forward_demodulation,[],[f1641,f97])).
% 2.06/0.63  fof(f97,plain,(
% 2.06/0.63    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 2.06/0.63    inference(definition_unfolding,[],[f66,f63])).
% 2.06/0.63  fof(f66,plain,(
% 2.06/0.63    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 2.06/0.63    inference(cnf_transformation,[],[f9])).
% 2.06/0.63  fof(f9,axiom,(
% 2.06/0.63    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 2.06/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 2.06/0.63  fof(f1641,plain,(
% 2.06/0.63    k1_relat_1(sK3) = k9_relat_1(sK2,k1_relat_1(k6_partfun1(sK0))) | ~v1_funct_1(sK2) | ~r1_tarski(k1_relat_1(sK3),k2_relat_1(sK2)) | ~v1_relat_1(sK2) | ~v1_relat_1(sK3) | ~spl4_54),
% 2.06/0.63    inference(superposition,[],[f295,f871])).
% 2.06/0.63  fof(f295,plain,(
% 2.06/0.63    ( ! [X2,X1] : (k1_relat_1(X2) = k9_relat_1(X1,k1_relat_1(k5_relat_1(X1,X2))) | ~v1_funct_1(X1) | ~r1_tarski(k1_relat_1(X2),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X2)) )),
% 2.06/0.63    inference(duplicate_literal_removal,[],[f289])).
% 2.06/0.63  fof(f289,plain,(
% 2.06/0.63    ( ! [X2,X1] : (k1_relat_1(X2) = k9_relat_1(X1,k1_relat_1(k5_relat_1(X1,X2))) | ~v1_funct_1(X1) | ~r1_tarski(k1_relat_1(X2),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 2.06/0.63    inference(superposition,[],[f84,f71])).
% 2.06/0.63  fof(f71,plain,(
% 2.06/0.63    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.06/0.63    inference(cnf_transformation,[],[f30])).
% 2.06/0.63  fof(f30,plain,(
% 2.06/0.63    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.06/0.63    inference(ennf_transformation,[],[f7])).
% 2.06/0.63  fof(f7,axiom,(
% 2.06/0.63    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 2.06/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).
% 2.06/0.63  fof(f84,plain,(
% 2.06/0.63    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~v1_funct_1(X1) | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.06/0.63    inference(cnf_transformation,[],[f42])).
% 2.06/0.63  fof(f42,plain,(
% 2.06/0.63    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.06/0.63    inference(flattening,[],[f41])).
% 2.06/0.63  fof(f41,plain,(
% 2.06/0.63    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.06/0.63    inference(ennf_transformation,[],[f13])).
% 2.06/0.63  fof(f13,axiom,(
% 2.06/0.63    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 2.06/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).
% 2.06/0.63  fof(f1198,plain,(
% 2.06/0.63    ~spl4_3 | ~spl4_19 | ~spl4_9 | ~spl4_20 | spl4_80 | ~spl4_61),
% 2.06/0.63    inference(avatar_split_clause,[],[f1181,f928,f1195,f429,f300,f425,f119])).
% 2.06/0.63  fof(f1181,plain,(
% 2.06/0.63    k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) | ~v1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl4_61),
% 2.06/0.63    inference(superposition,[],[f183,f930])).
% 2.06/0.63  fof(f183,plain,(
% 2.06/0.63    ( ! [X0] : (k2_funct_1(X0) = k5_relat_1(k2_funct_1(X0),k6_partfun1(k1_relat_1(X0))) | ~v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.06/0.63    inference(superposition,[],[f98,f77])).
% 2.06/0.63  fof(f77,plain,(
% 2.06/0.63    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.06/0.63    inference(cnf_transformation,[],[f36])).
% 2.06/0.63  fof(f36,plain,(
% 2.06/0.63    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.06/0.63    inference(flattening,[],[f35])).
% 2.06/0.63  fof(f35,plain,(
% 2.06/0.63    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.06/0.63    inference(ennf_transformation,[],[f14])).
% 2.06/0.63  fof(f14,axiom,(
% 2.06/0.63    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 2.06/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 2.06/0.63  fof(f98,plain,(
% 2.06/0.63    ( ! [X0] : (k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 2.06/0.63    inference(definition_unfolding,[],[f69,f63])).
% 2.06/0.63  fof(f69,plain,(
% 2.06/0.63    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0) )),
% 2.06/0.63    inference(cnf_transformation,[],[f28])).
% 2.06/0.63  fof(f28,plain,(
% 2.06/0.63    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 2.06/0.63    inference(ennf_transformation,[],[f11])).
% 2.06/0.63  fof(f11,axiom,(
% 2.06/0.63    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 2.06/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).
% 2.06/0.63  fof(f948,plain,(
% 2.06/0.63    spl4_60),
% 2.06/0.63    inference(avatar_contradiction_clause,[],[f945])).
% 2.06/0.63  fof(f945,plain,(
% 2.06/0.63    $false | spl4_60),
% 2.06/0.63    inference(subsumption_resolution,[],[f151,f926])).
% 2.06/0.63  fof(f926,plain,(
% 2.06/0.63    ~v4_relat_1(sK2,sK0) | spl4_60),
% 2.06/0.63    inference(avatar_component_clause,[],[f924])).
% 2.06/0.63  fof(f924,plain,(
% 2.06/0.63    spl4_60 <=> v4_relat_1(sK2,sK0)),
% 2.06/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_60])])).
% 2.06/0.63  fof(f151,plain,(
% 2.06/0.63    v4_relat_1(sK2,sK0)),
% 2.06/0.63    inference(resolution,[],[f89,f62])).
% 2.06/0.63  fof(f62,plain,(
% 2.06/0.63    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.06/0.63    inference(cnf_transformation,[],[f26])).
% 2.06/0.63  fof(f931,plain,(
% 2.06/0.63    ~spl4_60 | ~spl4_3 | spl4_61 | ~spl4_59),
% 2.06/0.63    inference(avatar_split_clause,[],[f921,f909,f928,f119,f924])).
% 2.06/0.63  fof(f909,plain,(
% 2.06/0.63    spl4_59 <=> r1_tarski(sK0,k1_relat_1(sK2))),
% 2.06/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_59])])).
% 2.06/0.63  fof(f921,plain,(
% 2.06/0.63    sK0 = k1_relat_1(sK2) | ~v1_relat_1(sK2) | ~v4_relat_1(sK2,sK0) | ~spl4_59),
% 2.06/0.63    inference(resolution,[],[f911,f149])).
% 2.06/0.63  fof(f149,plain,(
% 2.06/0.63    ( ! [X4,X3] : (~r1_tarski(X3,k1_relat_1(X4)) | k1_relat_1(X4) = X3 | ~v1_relat_1(X4) | ~v4_relat_1(X4,X3)) )),
% 2.06/0.63    inference(resolution,[],[f87,f83])).
% 2.06/0.63  fof(f87,plain,(
% 2.06/0.63    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 2.06/0.63    inference(cnf_transformation,[],[f1])).
% 2.06/0.63  fof(f1,axiom,(
% 2.06/0.63    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.06/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.06/0.63  fof(f911,plain,(
% 2.06/0.63    r1_tarski(sK0,k1_relat_1(sK2)) | ~spl4_59),
% 2.06/0.63    inference(avatar_component_clause,[],[f909])).
% 2.06/0.63  fof(f912,plain,(
% 2.06/0.63    ~spl4_1 | ~spl4_3 | spl4_59 | ~spl4_54),
% 2.06/0.63    inference(avatar_split_clause,[],[f907,f869,f909,f119,f110])).
% 2.06/0.63  fof(f907,plain,(
% 2.06/0.63    r1_tarski(sK0,k1_relat_1(sK2)) | ~v1_relat_1(sK2) | ~v1_relat_1(sK3) | ~spl4_54),
% 2.06/0.63    inference(forward_demodulation,[],[f893,f97])).
% 2.06/0.63  fof(f893,plain,(
% 2.06/0.63    r1_tarski(k1_relat_1(k6_partfun1(sK0)),k1_relat_1(sK2)) | ~v1_relat_1(sK2) | ~v1_relat_1(sK3) | ~spl4_54),
% 2.06/0.63    inference(superposition,[],[f193,f871])).
% 2.06/0.63  fof(f193,plain,(
% 2.06/0.63    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X0) | ~v1_relat_1(X1)) )),
% 2.06/0.63    inference(duplicate_literal_removal,[],[f188])).
% 2.06/0.63  fof(f188,plain,(
% 2.06/0.63    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.06/0.63    inference(superposition,[],[f81,f71])).
% 2.06/0.63  fof(f81,plain,(
% 2.06/0.63    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.06/0.63    inference(cnf_transformation,[],[f39])).
% 2.06/0.63  fof(f39,plain,(
% 2.06/0.63    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.06/0.63    inference(ennf_transformation,[],[f5])).
% 2.06/0.63  fof(f5,axiom,(
% 2.06/0.63    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 2.06/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).
% 2.06/0.63  fof(f883,plain,(
% 2.06/0.63    ~spl4_9 | ~spl4_35 | ~spl4_36 | ~spl4_5 | spl4_54 | ~spl4_52),
% 2.06/0.63    inference(avatar_split_clause,[],[f880,f860,f869,f219,f624,f620,f300])).
% 2.06/0.63  fof(f620,plain,(
% 2.06/0.63    spl4_35 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.06/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).
% 2.06/0.63  fof(f624,plain,(
% 2.06/0.63    spl4_36 <=> v1_funct_1(sK3)),
% 2.06/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 2.06/0.63  fof(f219,plain,(
% 2.06/0.63    spl4_5 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.06/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 2.06/0.63  fof(f860,plain,(
% 2.06/0.63    spl4_52 <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)),
% 2.06/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).
% 2.06/0.63  fof(f880,plain,(
% 2.06/0.63    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | ~spl4_52),
% 2.06/0.63    inference(superposition,[],[f93,f862])).
% 2.06/0.63  fof(f862,plain,(
% 2.06/0.63    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) | ~spl4_52),
% 2.06/0.63    inference(avatar_component_clause,[],[f860])).
% 2.06/0.63  fof(f93,plain,(
% 2.06/0.63    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 2.06/0.63    inference(cnf_transformation,[],[f48])).
% 2.06/0.63  fof(f48,plain,(
% 2.06/0.63    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.06/0.63    inference(flattening,[],[f47])).
% 2.06/0.63  fof(f47,plain,(
% 2.06/0.63    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.06/0.63    inference(ennf_transformation,[],[f21])).
% 2.06/0.63  fof(f21,axiom,(
% 2.06/0.63    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 2.06/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 2.06/0.63  fof(f876,plain,(
% 2.06/0.63    spl4_51),
% 2.06/0.63    inference(avatar_contradiction_clause,[],[f873])).
% 2.06/0.63  fof(f873,plain,(
% 2.06/0.63    $false | spl4_51),
% 2.06/0.63    inference(unit_resulting_resolution,[],[f60,f51,f53,f62,f858,f95])).
% 2.06/0.63  fof(f95,plain,(
% 2.06/0.63    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 2.06/0.63    inference(cnf_transformation,[],[f50])).
% 2.06/0.63  fof(f50,plain,(
% 2.06/0.63    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.06/0.63    inference(flattening,[],[f49])).
% 2.06/0.63  fof(f49,plain,(
% 2.06/0.63    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.06/0.63    inference(ennf_transformation,[],[f19])).
% 2.06/0.63  fof(f19,axiom,(
% 2.06/0.63    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 2.06/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 2.06/0.63  fof(f858,plain,(
% 2.06/0.63    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl4_51),
% 2.06/0.63    inference(avatar_component_clause,[],[f856])).
% 2.06/0.63  fof(f856,plain,(
% 2.06/0.63    spl4_51 <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.06/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_51])])).
% 2.06/0.63  fof(f51,plain,(
% 2.06/0.63    v1_funct_1(sK3)),
% 2.06/0.63    inference(cnf_transformation,[],[f26])).
% 2.06/0.63  fof(f60,plain,(
% 2.06/0.63    v1_funct_1(sK2)),
% 2.06/0.63    inference(cnf_transformation,[],[f26])).
% 2.06/0.63  fof(f863,plain,(
% 2.06/0.63    ~spl4_51 | spl4_52),
% 2.06/0.63    inference(avatar_split_clause,[],[f852,f860,f856])).
% 2.06/0.63  fof(f852,plain,(
% 2.06/0.63    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.06/0.63    inference(resolution,[],[f440,f55])).
% 2.06/0.63  fof(f55,plain,(
% 2.06/0.63    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 2.06/0.63    inference(cnf_transformation,[],[f26])).
% 2.06/0.63  fof(f440,plain,(
% 2.06/0.63    ( ! [X2,X1] : (~r2_relset_1(X2,X2,X1,k6_partfun1(X2)) | k6_partfun1(X2) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))) )),
% 2.06/0.63    inference(resolution,[],[f92,f65])).
% 2.06/0.63  fof(f65,plain,(
% 2.06/0.63    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.06/0.63    inference(cnf_transformation,[],[f20])).
% 2.06/0.63  fof(f20,axiom,(
% 2.06/0.63    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 2.06/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 2.06/0.63  fof(f92,plain,(
% 2.06/0.63    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 = X3 | ~r2_relset_1(X0,X1,X2,X3)) )),
% 2.06/0.63    inference(cnf_transformation,[],[f46])).
% 2.06/0.63  fof(f46,plain,(
% 2.06/0.63    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.06/0.63    inference(flattening,[],[f45])).
% 2.06/0.63  fof(f45,plain,(
% 2.06/0.63    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.06/0.63    inference(ennf_transformation,[],[f18])).
% 2.06/0.63  fof(f18,axiom,(
% 2.06/0.63    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.06/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 2.06/0.63  fof(f635,plain,(
% 2.06/0.63    spl4_36),
% 2.06/0.63    inference(avatar_contradiction_clause,[],[f634])).
% 2.06/0.63  fof(f634,plain,(
% 2.06/0.63    $false | spl4_36),
% 2.06/0.63    inference(subsumption_resolution,[],[f51,f626])).
% 2.06/0.63  fof(f626,plain,(
% 2.06/0.63    ~v1_funct_1(sK3) | spl4_36),
% 2.06/0.63    inference(avatar_component_clause,[],[f624])).
% 2.06/0.63  fof(f633,plain,(
% 2.06/0.63    spl4_35),
% 2.06/0.63    inference(avatar_contradiction_clause,[],[f632])).
% 2.06/0.63  fof(f632,plain,(
% 2.06/0.63    $false | spl4_35),
% 2.06/0.63    inference(subsumption_resolution,[],[f53,f622])).
% 2.06/0.63  fof(f622,plain,(
% 2.06/0.63    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl4_35),
% 2.06/0.63    inference(avatar_component_clause,[],[f620])).
% 2.06/0.63  fof(f444,plain,(
% 2.06/0.63    ~spl4_3 | spl4_20),
% 2.06/0.63    inference(avatar_contradiction_clause,[],[f442])).
% 2.06/0.63  fof(f442,plain,(
% 2.06/0.63    $false | (~spl4_3 | spl4_20)),
% 2.06/0.63    inference(unit_resulting_resolution,[],[f121,f60,f431,f74])).
% 2.06/0.63  fof(f74,plain,(
% 2.06/0.63    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.06/0.63    inference(cnf_transformation,[],[f34])).
% 2.06/0.63  fof(f34,plain,(
% 2.06/0.63    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.06/0.63    inference(flattening,[],[f33])).
% 2.06/0.63  fof(f33,plain,(
% 2.06/0.63    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.06/0.63    inference(ennf_transformation,[],[f12])).
% 2.06/0.63  fof(f12,axiom,(
% 2.06/0.63    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.06/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 2.06/0.63  fof(f431,plain,(
% 2.06/0.63    ~v1_relat_1(k2_funct_1(sK2)) | spl4_20),
% 2.06/0.63    inference(avatar_component_clause,[],[f429])).
% 2.06/0.63  fof(f121,plain,(
% 2.06/0.63    v1_relat_1(sK2) | ~spl4_3),
% 2.06/0.63    inference(avatar_component_clause,[],[f119])).
% 2.06/0.63  fof(f438,plain,(
% 2.06/0.63    spl4_19),
% 2.06/0.63    inference(avatar_contradiction_clause,[],[f437])).
% 2.06/0.63  fof(f437,plain,(
% 2.06/0.63    $false | spl4_19),
% 2.06/0.63    inference(subsumption_resolution,[],[f56,f427])).
% 2.06/0.63  fof(f427,plain,(
% 2.06/0.63    ~v2_funct_1(sK2) | spl4_19),
% 2.06/0.63    inference(avatar_component_clause,[],[f425])).
% 2.06/0.63  fof(f56,plain,(
% 2.06/0.63    v2_funct_1(sK2)),
% 2.06/0.63    inference(cnf_transformation,[],[f26])).
% 2.06/0.63  fof(f319,plain,(
% 2.06/0.63    spl4_11),
% 2.06/0.63    inference(avatar_contradiction_clause,[],[f315])).
% 2.06/0.63  fof(f315,plain,(
% 2.06/0.63    $false | spl4_11),
% 2.06/0.63    inference(unit_resulting_resolution,[],[f136,f152,f310,f145])).
% 2.06/0.63  fof(f145,plain,(
% 2.06/0.63    ( ! [X0,X1] : (~v4_relat_1(k6_partfun1(X0),X1) | ~v1_relat_1(k6_partfun1(X0)) | r1_tarski(X0,X1)) )),
% 2.06/0.63    inference(superposition,[],[f83,f97])).
% 2.06/0.63  fof(f310,plain,(
% 2.06/0.63    ~r1_tarski(sK1,sK1) | spl4_11),
% 2.06/0.63    inference(avatar_component_clause,[],[f308])).
% 2.06/0.63  fof(f308,plain,(
% 2.06/0.63    spl4_11 <=> r1_tarski(sK1,sK1)),
% 2.06/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 2.06/0.63  fof(f152,plain,(
% 2.06/0.63    ( ! [X0] : (v4_relat_1(k6_partfun1(X0),X0)) )),
% 2.06/0.63    inference(resolution,[],[f89,f65])).
% 2.06/0.63  fof(f136,plain,(
% 2.06/0.63    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) )),
% 2.06/0.63    inference(resolution,[],[f108,f80])).
% 2.06/0.63  fof(f80,plain,(
% 2.06/0.63    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.06/0.63    inference(cnf_transformation,[],[f4])).
% 2.06/0.63  fof(f4,axiom,(
% 2.06/0.63    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.06/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 2.06/0.63  fof(f108,plain,(
% 2.06/0.63    ( ! [X0] : (~v1_relat_1(k2_zfmisc_1(X0,X0)) | v1_relat_1(k6_partfun1(X0))) )),
% 2.06/0.63    inference(resolution,[],[f73,f65])).
% 2.06/0.63  fof(f73,plain,(
% 2.06/0.63    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 2.06/0.63    inference(cnf_transformation,[],[f32])).
% 2.06/0.63  fof(f32,plain,(
% 2.06/0.63    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.06/0.63    inference(ennf_transformation,[],[f2])).
% 2.06/0.63  fof(f2,axiom,(
% 2.06/0.63    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.06/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 2.06/0.63  fof(f313,plain,(
% 2.06/0.63    spl4_9),
% 2.06/0.63    inference(avatar_contradiction_clause,[],[f312])).
% 2.06/0.63  fof(f312,plain,(
% 2.06/0.63    $false | spl4_9),
% 2.06/0.63    inference(subsumption_resolution,[],[f60,f302])).
% 2.06/0.63  fof(f302,plain,(
% 2.06/0.63    ~v1_funct_1(sK2) | spl4_9),
% 2.06/0.63    inference(avatar_component_clause,[],[f300])).
% 2.06/0.63  fof(f311,plain,(
% 2.06/0.63    ~spl4_3 | ~spl4_9 | spl4_10 | ~spl4_11 | ~spl4_6 | ~spl4_8),
% 2.06/0.63    inference(avatar_split_clause,[],[f298,f238,f223,f308,f304,f300,f119])).
% 2.06/0.63  fof(f238,plain,(
% 2.06/0.63    spl4_8 <=> k1_relat_1(sK2) = k10_relat_1(sK2,sK1)),
% 2.06/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 2.06/0.63  fof(f298,plain,(
% 2.06/0.63    ~r1_tarski(sK1,sK1) | sK1 = k9_relat_1(sK2,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl4_6 | ~spl4_8)),
% 2.06/0.63    inference(forward_demodulation,[],[f292,f225])).
% 2.06/0.63  fof(f292,plain,(
% 2.06/0.63    sK1 = k9_relat_1(sK2,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~r1_tarski(sK1,k2_relat_1(sK2)) | ~v1_relat_1(sK2) | ~spl4_8),
% 2.06/0.63    inference(superposition,[],[f84,f240])).
% 2.06/0.63  fof(f240,plain,(
% 2.06/0.63    k1_relat_1(sK2) = k10_relat_1(sK2,sK1) | ~spl4_8),
% 2.06/0.63    inference(avatar_component_clause,[],[f238])).
% 2.06/0.63  fof(f241,plain,(
% 2.06/0.63    ~spl4_3 | spl4_8 | ~spl4_6),
% 2.06/0.63    inference(avatar_split_clause,[],[f231,f223,f238,f119])).
% 2.06/0.63  fof(f231,plain,(
% 2.06/0.63    k1_relat_1(sK2) = k10_relat_1(sK2,sK1) | ~v1_relat_1(sK2) | ~spl4_6),
% 2.06/0.63    inference(superposition,[],[f68,f225])).
% 2.06/0.63  fof(f68,plain,(
% 2.06/0.63    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.06/0.63    inference(cnf_transformation,[],[f27])).
% 2.06/0.63  fof(f27,plain,(
% 2.06/0.63    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 2.06/0.63    inference(ennf_transformation,[],[f6])).
% 2.06/0.63  fof(f6,axiom,(
% 2.06/0.63    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 2.06/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).
% 2.06/0.63  fof(f229,plain,(
% 2.06/0.63    spl4_5),
% 2.06/0.63    inference(avatar_contradiction_clause,[],[f228])).
% 2.06/0.63  fof(f228,plain,(
% 2.06/0.63    $false | spl4_5),
% 2.06/0.63    inference(subsumption_resolution,[],[f62,f221])).
% 2.06/0.63  fof(f221,plain,(
% 2.06/0.63    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl4_5),
% 2.06/0.63    inference(avatar_component_clause,[],[f219])).
% 2.06/0.63  fof(f227,plain,(
% 2.06/0.63    ~spl4_5 | spl4_6),
% 2.06/0.63    inference(avatar_split_clause,[],[f217,f223,f219])).
% 2.06/0.63  fof(f217,plain,(
% 2.06/0.63    sK1 = k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.06/0.63    inference(superposition,[],[f54,f88])).
% 2.06/0.63  fof(f88,plain,(
% 2.06/0.63    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.06/0.63    inference(cnf_transformation,[],[f43])).
% 2.06/0.63  fof(f43,plain,(
% 2.06/0.63    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.06/0.63    inference(ennf_transformation,[],[f17])).
% 2.06/0.63  fof(f17,axiom,(
% 2.06/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 2.06/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 2.06/0.63  fof(f54,plain,(
% 2.06/0.63    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 2.06/0.63    inference(cnf_transformation,[],[f26])).
% 2.06/0.63  fof(f134,plain,(
% 2.06/0.63    spl4_4),
% 2.06/0.63    inference(avatar_contradiction_clause,[],[f131])).
% 2.06/0.63  fof(f131,plain,(
% 2.06/0.63    $false | spl4_4),
% 2.06/0.63    inference(unit_resulting_resolution,[],[f80,f125])).
% 2.06/0.63  fof(f125,plain,(
% 2.06/0.63    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl4_4),
% 2.06/0.63    inference(avatar_component_clause,[],[f123])).
% 2.06/0.63  fof(f123,plain,(
% 2.06/0.63    spl4_4 <=> v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 2.06/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 2.06/0.63  fof(f130,plain,(
% 2.06/0.63    spl4_2),
% 2.06/0.63    inference(avatar_contradiction_clause,[],[f127])).
% 2.06/0.63  fof(f127,plain,(
% 2.06/0.63    $false | spl4_2),
% 2.06/0.63    inference(unit_resulting_resolution,[],[f80,f116])).
% 2.06/0.63  fof(f116,plain,(
% 2.06/0.63    ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | spl4_2),
% 2.06/0.63    inference(avatar_component_clause,[],[f114])).
% 2.06/0.63  fof(f114,plain,(
% 2.06/0.63    spl4_2 <=> v1_relat_1(k2_zfmisc_1(sK1,sK0))),
% 2.06/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 2.06/0.63  fof(f126,plain,(
% 2.06/0.63    spl4_3 | ~spl4_4),
% 2.06/0.63    inference(avatar_split_clause,[],[f107,f123,f119])).
% 2.06/0.63  fof(f107,plain,(
% 2.06/0.63    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | v1_relat_1(sK2)),
% 2.06/0.63    inference(resolution,[],[f73,f62])).
% 2.06/0.63  fof(f117,plain,(
% 2.06/0.63    spl4_1 | ~spl4_2),
% 2.06/0.63    inference(avatar_split_clause,[],[f106,f114,f110])).
% 2.06/0.63  fof(f106,plain,(
% 2.06/0.63    ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | v1_relat_1(sK3)),
% 2.06/0.63    inference(resolution,[],[f73,f53])).
% 2.06/0.63  % SZS output end Proof for theBenchmark
% 2.06/0.63  % (18556)------------------------------
% 2.06/0.63  % (18556)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.06/0.63  % (18556)Termination reason: Refutation
% 2.06/0.63  
% 2.06/0.63  % (18556)Memory used [KB]: 7803
% 2.06/0.63  % (18556)Time elapsed: 0.211 s
% 2.06/0.63  % (18556)------------------------------
% 2.06/0.63  % (18556)------------------------------
% 2.06/0.63  % (18539)Success in time 0.272 s
%------------------------------------------------------------------------------
