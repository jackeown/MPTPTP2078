%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:48 EST 2020

% Result     : Theorem 2.14s
% Output     : Refutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :  177 ( 310 expanded)
%              Number of leaves         :   42 ( 107 expanded)
%              Depth                    :   11
%              Number of atoms          :  531 (1428 expanded)
%              Number of equality atoms :   95 ( 373 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1754,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f111,f120,f124,f128,f204,f206,f409,f414,f417,f537,f539,f711,f724,f731,f760,f779,f796,f948,f1633,f1677,f1692,f1739])).

fof(f1739,plain,(
    ~ spl4_119 ),
    inference(avatar_contradiction_clause,[],[f1704])).

fof(f1704,plain,
    ( $false
    | ~ spl4_119 ),
    inference(subsumption_resolution,[],[f55,f1672])).

fof(f1672,plain,
    ( sK3 = k2_funct_1(sK2)
    | ~ spl4_119 ),
    inference(avatar_component_clause,[],[f1670])).

fof(f1670,plain,
    ( spl4_119
  <=> sK3 = k2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_119])])).

fof(f55,plain,(
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

fof(f1692,plain,
    ( ~ spl4_1
    | spl4_118 ),
    inference(avatar_contradiction_clause,[],[f1690])).

fof(f1690,plain,
    ( $false
    | ~ spl4_1
    | spl4_118 ),
    inference(unit_resulting_resolution,[],[f106,f140,f1668,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f1668,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),sK1)
    | spl4_118 ),
    inference(avatar_component_clause,[],[f1666])).

fof(f1666,plain,
    ( spl4_118
  <=> r1_tarski(k1_relat_1(sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_118])])).

fof(f140,plain,(
    v4_relat_1(sK3,sK1) ),
    inference(resolution,[],[f83,f49])).

fof(f49,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f24])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f106,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl4_1
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f1677,plain,
    ( ~ spl4_1
    | ~ spl4_118
    | spl4_119
    | ~ spl4_115 ),
    inference(avatar_split_clause,[],[f1659,f1630,f1670,f1666,f104])).

fof(f1630,plain,
    ( spl4_115
  <=> k2_funct_1(sK2) = k5_relat_1(k6_partfun1(sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_115])])).

fof(f1659,plain,
    ( sK3 = k2_funct_1(sK2)
    | ~ r1_tarski(k1_relat_1(sK3),sK1)
    | ~ v1_relat_1(sK3)
    | ~ spl4_115 ),
    inference(superposition,[],[f95,f1632])).

fof(f1632,plain,
    ( k2_funct_1(sK2) = k5_relat_1(k6_partfun1(sK1),sK3)
    | ~ spl4_115 ),
    inference(avatar_component_clause,[],[f1630])).

fof(f95,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_partfun1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f76,f59])).

fof(f59,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | k5_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

fof(f1633,plain,
    ( ~ spl4_16
    | ~ spl4_17
    | ~ spl4_18
    | ~ spl4_1
    | ~ spl4_3
    | spl4_115
    | ~ spl4_6
    | ~ spl4_44
    | ~ spl4_64 ),
    inference(avatar_split_clause,[],[f1628,f945,f717,f200,f1630,f113,f104,f400,f396,f392])).

fof(f392,plain,
    ( spl4_16
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f396,plain,
    ( spl4_17
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f400,plain,
    ( spl4_18
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f113,plain,
    ( spl4_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f200,plain,
    ( spl4_6
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f717,plain,
    ( spl4_44
  <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).

fof(f945,plain,
    ( spl4_64
  <=> k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_64])])).

fof(f1628,plain,
    ( k2_funct_1(sK2) = k5_relat_1(k6_partfun1(sK1),sK3)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ spl4_6
    | ~ spl4_44
    | ~ spl4_64 ),
    inference(forward_demodulation,[],[f1627,f947])).

fof(f947,plain,
    ( k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0))
    | ~ spl4_64 ),
    inference(avatar_component_clause,[],[f945])).

fof(f1627,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k6_partfun1(sK1),sK3)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ spl4_6
    | ~ spl4_44 ),
    inference(forward_demodulation,[],[f1555,f202])).

fof(f202,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f200])).

fof(f1555,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k6_partfun1(k2_relat_1(sK2)),sK3)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ spl4_44 ),
    inference(superposition,[],[f330,f719])).

fof(f719,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl4_44 ),
    inference(avatar_component_clause,[],[f717])).

fof(f330,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k2_funct_1(X0),k5_relat_1(X0,X1)) = k5_relat_1(k6_partfun1(k2_relat_1(X0)),X1)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f310])).

fof(f310,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k2_funct_1(X0),k5_relat_1(X0,X1)) = k5_relat_1(k6_partfun1(k2_relat_1(X0)),X1)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f66,f93])).

fof(f93,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f73,f59])).

fof(f73,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

fof(f948,plain,
    ( ~ spl4_3
    | ~ spl4_16
    | ~ spl4_17
    | ~ spl4_18
    | spl4_64
    | ~ spl4_51 ),
    inference(avatar_split_clause,[],[f932,f776,f945,f400,f396,f392,f113])).

fof(f776,plain,
    ( spl4_51
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_51])])).

fof(f932,plain,
    ( k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_51 ),
    inference(superposition,[],[f163,f778])).

fof(f778,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl4_51 ),
    inference(avatar_component_clause,[],[f776])).

fof(f163,plain,(
    ! [X0] :
      ( k2_funct_1(X0) = k5_relat_1(k2_funct_1(X0),k6_partfun1(k1_relat_1(X0)))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f92,f71])).

fof(f71,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f92,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f64,f59])).

fof(f64,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

fof(f796,plain,(
    spl4_50 ),
    inference(avatar_contradiction_clause,[],[f793])).

fof(f793,plain,
    ( $false
    | spl4_50 ),
    inference(subsumption_resolution,[],[f141,f774])).

fof(f774,plain,
    ( ~ v4_relat_1(sK2,sK0)
    | spl4_50 ),
    inference(avatar_component_clause,[],[f772])).

fof(f772,plain,
    ( spl4_50
  <=> v4_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).

fof(f141,plain,(
    v4_relat_1(sK2,sK0) ),
    inference(resolution,[],[f83,f58])).

fof(f58,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f24])).

fof(f779,plain,
    ( ~ spl4_50
    | ~ spl4_3
    | spl4_51
    | ~ spl4_49 ),
    inference(avatar_split_clause,[],[f769,f757,f776,f113,f772])).

fof(f757,plain,
    ( spl4_49
  <=> r1_tarski(sK0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).

fof(f769,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v4_relat_1(sK2,sK0)
    | ~ spl4_49 ),
    inference(resolution,[],[f759,f139])).

fof(f139,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(X3,k1_relat_1(X4))
      | k1_relat_1(X4) = X3
      | ~ v1_relat_1(X4)
      | ~ v4_relat_1(X4,X3) ) ),
    inference(resolution,[],[f81,f78])).

fof(f81,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f759,plain,
    ( r1_tarski(sK0,k1_relat_1(sK2))
    | ~ spl4_49 ),
    inference(avatar_component_clause,[],[f757])).

fof(f760,plain,
    ( ~ spl4_1
    | ~ spl4_3
    | spl4_49
    | ~ spl4_44 ),
    inference(avatar_split_clause,[],[f755,f717,f757,f113,f104])).

fof(f755,plain,
    ( r1_tarski(sK0,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ spl4_44 ),
    inference(forward_demodulation,[],[f741,f91])).

fof(f91,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f62,f59])).

fof(f62,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f741,plain,
    ( r1_tarski(k1_relat_1(k6_partfun1(sK0)),k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ spl4_44 ),
    inference(superposition,[],[f171,f719])).

fof(f171,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1) ) ),
    inference(duplicate_literal_removal,[],[f168])).

fof(f168,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f75,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

fof(f731,plain,
    ( ~ spl4_17
    | ~ spl4_31
    | ~ spl4_32
    | ~ spl4_5
    | spl4_44
    | ~ spl4_42 ),
    inference(avatar_split_clause,[],[f728,f708,f717,f196,f528,f524,f396])).

fof(f524,plain,
    ( spl4_31
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f528,plain,
    ( spl4_32
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f196,plain,
    ( spl4_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f708,plain,
    ( spl4_42
  <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).

fof(f728,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_42 ),
    inference(superposition,[],[f87,f710])).

fof(f710,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | ~ spl4_42 ),
    inference(avatar_component_clause,[],[f708])).

fof(f87,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
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
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f724,plain,(
    spl4_41 ),
    inference(avatar_contradiction_clause,[],[f721])).

fof(f721,plain,
    ( $false
    | spl4_41 ),
    inference(unit_resulting_resolution,[],[f56,f47,f49,f58,f706,f89])).

fof(f89,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f706,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl4_41 ),
    inference(avatar_component_clause,[],[f704])).

fof(f704,plain,
    ( spl4_41
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).

fof(f47,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f56,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f711,plain,
    ( ~ spl4_41
    | spl4_42 ),
    inference(avatar_split_clause,[],[f700,f708,f704])).

fof(f700,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f411,f51])).

fof(f51,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f411,plain,(
    ! [X2,X1] :
      ( ~ r2_relset_1(X2,X2,X1,k6_partfun1(X2))
      | k6_partfun1(X2) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ) ),
    inference(resolution,[],[f86,f61])).

fof(f61,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
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
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f539,plain,(
    spl4_32 ),
    inference(avatar_contradiction_clause,[],[f538])).

fof(f538,plain,
    ( $false
    | spl4_32 ),
    inference(subsumption_resolution,[],[f47,f530])).

fof(f530,plain,
    ( ~ v1_funct_1(sK3)
    | spl4_32 ),
    inference(avatar_component_clause,[],[f528])).

fof(f537,plain,(
    spl4_31 ),
    inference(avatar_contradiction_clause,[],[f536])).

fof(f536,plain,
    ( $false
    | spl4_31 ),
    inference(subsumption_resolution,[],[f49,f526])).

fof(f526,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl4_31 ),
    inference(avatar_component_clause,[],[f524])).

fof(f417,plain,
    ( ~ spl4_3
    | spl4_18 ),
    inference(avatar_contradiction_clause,[],[f415])).

fof(f415,plain,
    ( $false
    | ~ spl4_3
    | spl4_18 ),
    inference(unit_resulting_resolution,[],[f115,f56,f402,f68])).

fof(f68,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f402,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | spl4_18 ),
    inference(avatar_component_clause,[],[f400])).

fof(f115,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f113])).

fof(f414,plain,(
    spl4_17 ),
    inference(avatar_contradiction_clause,[],[f413])).

fof(f413,plain,
    ( $false
    | spl4_17 ),
    inference(subsumption_resolution,[],[f56,f398])).

fof(f398,plain,
    ( ~ v1_funct_1(sK2)
    | spl4_17 ),
    inference(avatar_component_clause,[],[f396])).

fof(f409,plain,(
    spl4_16 ),
    inference(avatar_contradiction_clause,[],[f408])).

fof(f408,plain,
    ( $false
    | spl4_16 ),
    inference(subsumption_resolution,[],[f52,f394])).

fof(f394,plain,
    ( ~ v2_funct_1(sK2)
    | spl4_16 ),
    inference(avatar_component_clause,[],[f392])).

fof(f52,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f206,plain,(
    spl4_5 ),
    inference(avatar_contradiction_clause,[],[f205])).

fof(f205,plain,
    ( $false
    | spl4_5 ),
    inference(subsumption_resolution,[],[f58,f198])).

fof(f198,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl4_5 ),
    inference(avatar_component_clause,[],[f196])).

fof(f204,plain,
    ( ~ spl4_5
    | spl4_6 ),
    inference(avatar_split_clause,[],[f194,f200,f196])).

fof(f194,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f50,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f50,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f128,plain,(
    spl4_4 ),
    inference(avatar_contradiction_clause,[],[f125])).

fof(f125,plain,
    ( $false
    | spl4_4 ),
    inference(unit_resulting_resolution,[],[f74,f119])).

fof(f119,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl4_4 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl4_4
  <=> v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f74,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f124,plain,(
    spl4_2 ),
    inference(avatar_contradiction_clause,[],[f121])).

fof(f121,plain,
    ( $false
    | spl4_2 ),
    inference(unit_resulting_resolution,[],[f74,f110])).

fof(f110,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl4_2
  <=> v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f120,plain,
    ( spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f101,f117,f113])).

fof(f101,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK2) ),
    inference(resolution,[],[f67,f58])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f111,plain,
    ( spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f100,f108,f104])).

fof(f100,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK3) ),
    inference(resolution,[],[f67,f49])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 11:54:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.50  % (32493)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.51  % (32501)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.51  % (32511)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.52  % (32498)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (32494)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.53  % (32508)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.53  % (32508)Refutation not found, incomplete strategy% (32508)------------------------------
% 0.22/0.53  % (32508)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (32508)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (32508)Memory used [KB]: 10746
% 0.22/0.53  % (32508)Time elapsed: 0.120 s
% 0.22/0.53  % (32508)------------------------------
% 0.22/0.53  % (32508)------------------------------
% 0.22/0.53  % (32515)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.54  % (32492)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.54  % (32496)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.54  % (32507)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.54  % (32517)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.54  % (32512)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.54  % (32495)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.54  % (32518)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.54  % (32499)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.55  % (32521)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.55  % (32516)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.55  % (32520)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.55  % (32509)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.55  % (32500)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.55  % (32502)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.55  % (32513)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.55  % (32505)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.55  % (32519)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.55  % (32510)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.56  % (32503)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.56  % (32504)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.56  % (32497)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.56  % (32506)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.79/0.60  % (32514)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 2.14/0.66  % (32505)Refutation found. Thanks to Tanya!
% 2.14/0.66  % SZS status Theorem for theBenchmark
% 2.14/0.68  % SZS output start Proof for theBenchmark
% 2.14/0.68  fof(f1754,plain,(
% 2.14/0.68    $false),
% 2.14/0.68    inference(avatar_sat_refutation,[],[f111,f120,f124,f128,f204,f206,f409,f414,f417,f537,f539,f711,f724,f731,f760,f779,f796,f948,f1633,f1677,f1692,f1739])).
% 2.14/0.68  fof(f1739,plain,(
% 2.14/0.68    ~spl4_119),
% 2.14/0.68    inference(avatar_contradiction_clause,[],[f1704])).
% 2.14/0.68  fof(f1704,plain,(
% 2.14/0.68    $false | ~spl4_119),
% 2.14/0.68    inference(subsumption_resolution,[],[f55,f1672])).
% 2.14/0.68  fof(f1672,plain,(
% 2.14/0.68    sK3 = k2_funct_1(sK2) | ~spl4_119),
% 2.14/0.68    inference(avatar_component_clause,[],[f1670])).
% 2.14/0.68  fof(f1670,plain,(
% 2.14/0.68    spl4_119 <=> sK3 = k2_funct_1(sK2)),
% 2.14/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_119])])).
% 2.14/0.68  fof(f55,plain,(
% 2.14/0.68    sK3 != k2_funct_1(sK2)),
% 2.14/0.68    inference(cnf_transformation,[],[f24])).
% 2.14/0.68  fof(f24,plain,(
% 2.14/0.68    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.14/0.68    inference(flattening,[],[f23])).
% 2.14/0.68  fof(f23,plain,(
% 2.14/0.68    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.14/0.68    inference(ennf_transformation,[],[f22])).
% 2.14/0.68  fof(f22,negated_conjecture,(
% 2.14/0.68    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.14/0.68    inference(negated_conjecture,[],[f21])).
% 2.14/0.68  fof(f21,conjecture,(
% 2.14/0.68    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.14/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).
% 2.14/0.68  fof(f1692,plain,(
% 2.14/0.68    ~spl4_1 | spl4_118),
% 2.14/0.68    inference(avatar_contradiction_clause,[],[f1690])).
% 2.14/0.68  fof(f1690,plain,(
% 2.14/0.68    $false | (~spl4_1 | spl4_118)),
% 2.14/0.68    inference(unit_resulting_resolution,[],[f106,f140,f1668,f78])).
% 2.14/0.68  fof(f78,plain,(
% 2.14/0.68    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1) | ~v4_relat_1(X1,X0)) )),
% 2.14/0.68    inference(cnf_transformation,[],[f38])).
% 2.14/0.68  fof(f38,plain,(
% 2.14/0.68    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.14/0.68    inference(ennf_transformation,[],[f3])).
% 2.14/0.68  fof(f3,axiom,(
% 2.14/0.68    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 2.14/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 2.14/0.68  fof(f1668,plain,(
% 2.14/0.68    ~r1_tarski(k1_relat_1(sK3),sK1) | spl4_118),
% 2.14/0.68    inference(avatar_component_clause,[],[f1666])).
% 2.14/0.68  fof(f1666,plain,(
% 2.14/0.68    spl4_118 <=> r1_tarski(k1_relat_1(sK3),sK1)),
% 2.14/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_118])])).
% 2.14/0.68  fof(f140,plain,(
% 2.14/0.68    v4_relat_1(sK3,sK1)),
% 2.14/0.68    inference(resolution,[],[f83,f49])).
% 2.14/0.68  fof(f49,plain,(
% 2.14/0.68    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.14/0.68    inference(cnf_transformation,[],[f24])).
% 2.14/0.68  fof(f83,plain,(
% 2.14/0.68    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 2.14/0.68    inference(cnf_transformation,[],[f40])).
% 2.14/0.68  fof(f40,plain,(
% 2.14/0.68    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.14/0.68    inference(ennf_transformation,[],[f14])).
% 2.14/0.68  fof(f14,axiom,(
% 2.14/0.68    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.14/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 2.14/0.68  fof(f106,plain,(
% 2.14/0.68    v1_relat_1(sK3) | ~spl4_1),
% 2.14/0.68    inference(avatar_component_clause,[],[f104])).
% 2.14/0.68  fof(f104,plain,(
% 2.14/0.68    spl4_1 <=> v1_relat_1(sK3)),
% 2.14/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 2.14/0.68  fof(f1677,plain,(
% 2.14/0.68    ~spl4_1 | ~spl4_118 | spl4_119 | ~spl4_115),
% 2.14/0.68    inference(avatar_split_clause,[],[f1659,f1630,f1670,f1666,f104])).
% 2.14/0.68  fof(f1630,plain,(
% 2.14/0.68    spl4_115 <=> k2_funct_1(sK2) = k5_relat_1(k6_partfun1(sK1),sK3)),
% 2.14/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_115])])).
% 2.14/0.68  fof(f1659,plain,(
% 2.14/0.68    sK3 = k2_funct_1(sK2) | ~r1_tarski(k1_relat_1(sK3),sK1) | ~v1_relat_1(sK3) | ~spl4_115),
% 2.14/0.68    inference(superposition,[],[f95,f1632])).
% 2.14/0.68  fof(f1632,plain,(
% 2.14/0.68    k2_funct_1(sK2) = k5_relat_1(k6_partfun1(sK1),sK3) | ~spl4_115),
% 2.14/0.68    inference(avatar_component_clause,[],[f1630])).
% 2.14/0.68  fof(f95,plain,(
% 2.14/0.68    ( ! [X0,X1] : (k5_relat_1(k6_partfun1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 2.14/0.68    inference(definition_unfolding,[],[f76,f59])).
% 2.14/0.68  fof(f59,plain,(
% 2.14/0.68    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.14/0.68    inference(cnf_transformation,[],[f20])).
% 2.14/0.68  fof(f20,axiom,(
% 2.14/0.68    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.14/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 2.14/0.68  fof(f76,plain,(
% 2.14/0.68    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k1_relat_1(X1),X0) | k5_relat_1(k6_relat_1(X0),X1) = X1) )),
% 2.14/0.68    inference(cnf_transformation,[],[f37])).
% 2.14/0.68  fof(f37,plain,(
% 2.14/0.68    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 2.14/0.68    inference(flattening,[],[f36])).
% 2.14/0.68  fof(f36,plain,(
% 2.14/0.68    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.14/0.68    inference(ennf_transformation,[],[f9])).
% 2.14/0.68  fof(f9,axiom,(
% 2.14/0.68    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 2.14/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).
% 2.14/0.68  fof(f1633,plain,(
% 2.14/0.68    ~spl4_16 | ~spl4_17 | ~spl4_18 | ~spl4_1 | ~spl4_3 | spl4_115 | ~spl4_6 | ~spl4_44 | ~spl4_64),
% 2.14/0.68    inference(avatar_split_clause,[],[f1628,f945,f717,f200,f1630,f113,f104,f400,f396,f392])).
% 2.14/0.68  fof(f392,plain,(
% 2.14/0.68    spl4_16 <=> v2_funct_1(sK2)),
% 2.14/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 2.14/0.68  fof(f396,plain,(
% 2.14/0.68    spl4_17 <=> v1_funct_1(sK2)),
% 2.14/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 2.14/0.68  fof(f400,plain,(
% 2.14/0.68    spl4_18 <=> v1_relat_1(k2_funct_1(sK2))),
% 2.14/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 2.14/0.68  fof(f113,plain,(
% 2.14/0.68    spl4_3 <=> v1_relat_1(sK2)),
% 2.14/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 2.14/0.68  fof(f200,plain,(
% 2.14/0.68    spl4_6 <=> sK1 = k2_relat_1(sK2)),
% 2.14/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 2.14/0.68  fof(f717,plain,(
% 2.14/0.68    spl4_44 <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 2.14/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).
% 2.14/0.68  fof(f945,plain,(
% 2.14/0.68    spl4_64 <=> k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0))),
% 2.14/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_64])])).
% 2.14/0.68  fof(f1628,plain,(
% 2.14/0.68    k2_funct_1(sK2) = k5_relat_1(k6_partfun1(sK1),sK3) | ~v1_relat_1(sK2) | ~v1_relat_1(sK3) | ~v1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | (~spl4_6 | ~spl4_44 | ~spl4_64)),
% 2.14/0.68    inference(forward_demodulation,[],[f1627,f947])).
% 2.14/0.68  fof(f947,plain,(
% 2.14/0.68    k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) | ~spl4_64),
% 2.14/0.68    inference(avatar_component_clause,[],[f945])).
% 2.14/0.68  fof(f1627,plain,(
% 2.14/0.68    k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k6_partfun1(sK1),sK3) | ~v1_relat_1(sK2) | ~v1_relat_1(sK3) | ~v1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | (~spl4_6 | ~spl4_44)),
% 2.14/0.68    inference(forward_demodulation,[],[f1555,f202])).
% 2.14/0.68  fof(f202,plain,(
% 2.14/0.68    sK1 = k2_relat_1(sK2) | ~spl4_6),
% 2.14/0.68    inference(avatar_component_clause,[],[f200])).
% 2.14/0.68  fof(f1555,plain,(
% 2.14/0.68    k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k6_partfun1(k2_relat_1(sK2)),sK3) | ~v1_relat_1(sK2) | ~v1_relat_1(sK3) | ~v1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~spl4_44),
% 2.14/0.68    inference(superposition,[],[f330,f719])).
% 2.14/0.68  fof(f719,plain,(
% 2.14/0.68    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~spl4_44),
% 2.14/0.68    inference(avatar_component_clause,[],[f717])).
% 2.14/0.68  fof(f330,plain,(
% 2.14/0.68    ( ! [X0,X1] : (k5_relat_1(k2_funct_1(X0),k5_relat_1(X0,X1)) = k5_relat_1(k6_partfun1(k2_relat_1(X0)),X1) | ~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0)) )),
% 2.14/0.68    inference(duplicate_literal_removal,[],[f310])).
% 2.14/0.68  fof(f310,plain,(
% 2.14/0.68    ( ! [X0,X1] : (k5_relat_1(k2_funct_1(X0),k5_relat_1(X0,X1)) = k5_relat_1(k6_partfun1(k2_relat_1(X0)),X1) | ~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.14/0.68    inference(superposition,[],[f66,f93])).
% 2.14/0.68  fof(f93,plain,(
% 2.14/0.68    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.14/0.68    inference(definition_unfolding,[],[f73,f59])).
% 2.14/0.68  fof(f73,plain,(
% 2.14/0.68    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)) )),
% 2.14/0.68    inference(cnf_transformation,[],[f34])).
% 2.14/0.68  fof(f34,plain,(
% 2.14/0.68    ! [X0] : ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.14/0.68    inference(flattening,[],[f33])).
% 2.14/0.68  fof(f33,plain,(
% 2.14/0.68    ! [X0] : (((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.14/0.68    inference(ennf_transformation,[],[f13])).
% 2.14/0.68  fof(f13,axiom,(
% 2.14/0.68    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 2.14/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).
% 2.14/0.68  fof(f66,plain,(
% 2.14/0.68    ( ! [X2,X0,X1] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | ~v1_relat_1(X0)) )),
% 2.14/0.68    inference(cnf_transformation,[],[f27])).
% 2.14/0.68  fof(f27,plain,(
% 2.14/0.68    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.14/0.68    inference(ennf_transformation,[],[f7])).
% 2.14/0.68  fof(f7,axiom,(
% 2.14/0.68    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 2.14/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).
% 2.14/0.68  fof(f948,plain,(
% 2.14/0.68    ~spl4_3 | ~spl4_16 | ~spl4_17 | ~spl4_18 | spl4_64 | ~spl4_51),
% 2.14/0.68    inference(avatar_split_clause,[],[f932,f776,f945,f400,f396,f392,f113])).
% 2.14/0.68  fof(f776,plain,(
% 2.14/0.68    spl4_51 <=> sK0 = k1_relat_1(sK2)),
% 2.14/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_51])])).
% 2.14/0.68  fof(f932,plain,(
% 2.14/0.68    k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) | ~v1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl4_51),
% 2.14/0.68    inference(superposition,[],[f163,f778])).
% 2.14/0.68  fof(f778,plain,(
% 2.14/0.68    sK0 = k1_relat_1(sK2) | ~spl4_51),
% 2.14/0.68    inference(avatar_component_clause,[],[f776])).
% 2.14/0.68  fof(f163,plain,(
% 2.14/0.68    ( ! [X0] : (k2_funct_1(X0) = k5_relat_1(k2_funct_1(X0),k6_partfun1(k1_relat_1(X0))) | ~v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.14/0.68    inference(superposition,[],[f92,f71])).
% 2.14/0.68  fof(f71,plain,(
% 2.14/0.68    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.14/0.68    inference(cnf_transformation,[],[f32])).
% 2.14/0.68  fof(f32,plain,(
% 2.14/0.68    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.14/0.68    inference(flattening,[],[f31])).
% 2.14/0.68  fof(f31,plain,(
% 2.14/0.68    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.14/0.68    inference(ennf_transformation,[],[f12])).
% 2.14/0.68  fof(f12,axiom,(
% 2.14/0.68    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 2.14/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 2.14/0.68  fof(f92,plain,(
% 2.14/0.68    ( ! [X0] : (k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 2.14/0.68    inference(definition_unfolding,[],[f64,f59])).
% 2.14/0.68  fof(f64,plain,(
% 2.14/0.68    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0) )),
% 2.14/0.68    inference(cnf_transformation,[],[f25])).
% 2.14/0.68  fof(f25,plain,(
% 2.14/0.68    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 2.14/0.68    inference(ennf_transformation,[],[f10])).
% 2.14/0.69  fof(f10,axiom,(
% 2.14/0.69    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 2.14/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).
% 2.14/0.69  fof(f796,plain,(
% 2.14/0.69    spl4_50),
% 2.14/0.69    inference(avatar_contradiction_clause,[],[f793])).
% 2.14/0.69  fof(f793,plain,(
% 2.14/0.69    $false | spl4_50),
% 2.14/0.69    inference(subsumption_resolution,[],[f141,f774])).
% 2.14/0.69  fof(f774,plain,(
% 2.14/0.69    ~v4_relat_1(sK2,sK0) | spl4_50),
% 2.14/0.69    inference(avatar_component_clause,[],[f772])).
% 2.14/0.69  fof(f772,plain,(
% 2.14/0.69    spl4_50 <=> v4_relat_1(sK2,sK0)),
% 2.14/0.69    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).
% 2.14/0.69  fof(f141,plain,(
% 2.14/0.69    v4_relat_1(sK2,sK0)),
% 2.14/0.69    inference(resolution,[],[f83,f58])).
% 2.14/0.69  fof(f58,plain,(
% 2.14/0.69    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.14/0.69    inference(cnf_transformation,[],[f24])).
% 2.14/0.69  fof(f779,plain,(
% 2.14/0.69    ~spl4_50 | ~spl4_3 | spl4_51 | ~spl4_49),
% 2.14/0.69    inference(avatar_split_clause,[],[f769,f757,f776,f113,f772])).
% 2.14/0.69  fof(f757,plain,(
% 2.14/0.69    spl4_49 <=> r1_tarski(sK0,k1_relat_1(sK2))),
% 2.14/0.69    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).
% 2.14/0.69  fof(f769,plain,(
% 2.14/0.69    sK0 = k1_relat_1(sK2) | ~v1_relat_1(sK2) | ~v4_relat_1(sK2,sK0) | ~spl4_49),
% 2.14/0.69    inference(resolution,[],[f759,f139])).
% 2.14/0.69  fof(f139,plain,(
% 2.14/0.69    ( ! [X4,X3] : (~r1_tarski(X3,k1_relat_1(X4)) | k1_relat_1(X4) = X3 | ~v1_relat_1(X4) | ~v4_relat_1(X4,X3)) )),
% 2.14/0.69    inference(resolution,[],[f81,f78])).
% 2.14/0.69  fof(f81,plain,(
% 2.14/0.69    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 2.14/0.69    inference(cnf_transformation,[],[f1])).
% 2.14/0.69  fof(f1,axiom,(
% 2.14/0.69    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.14/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.14/0.69  fof(f759,plain,(
% 2.14/0.69    r1_tarski(sK0,k1_relat_1(sK2)) | ~spl4_49),
% 2.14/0.69    inference(avatar_component_clause,[],[f757])).
% 2.14/0.69  fof(f760,plain,(
% 2.14/0.69    ~spl4_1 | ~spl4_3 | spl4_49 | ~spl4_44),
% 2.14/0.69    inference(avatar_split_clause,[],[f755,f717,f757,f113,f104])).
% 2.14/0.69  fof(f755,plain,(
% 2.14/0.69    r1_tarski(sK0,k1_relat_1(sK2)) | ~v1_relat_1(sK2) | ~v1_relat_1(sK3) | ~spl4_44),
% 2.14/0.69    inference(forward_demodulation,[],[f741,f91])).
% 2.14/0.69  fof(f91,plain,(
% 2.14/0.69    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 2.14/0.69    inference(definition_unfolding,[],[f62,f59])).
% 2.14/0.69  fof(f62,plain,(
% 2.14/0.69    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 2.14/0.69    inference(cnf_transformation,[],[f8])).
% 2.14/0.69  fof(f8,axiom,(
% 2.14/0.69    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 2.14/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 2.14/0.69  fof(f741,plain,(
% 2.14/0.69    r1_tarski(k1_relat_1(k6_partfun1(sK0)),k1_relat_1(sK2)) | ~v1_relat_1(sK2) | ~v1_relat_1(sK3) | ~spl4_44),
% 2.14/0.69    inference(superposition,[],[f171,f719])).
% 2.14/0.69  fof(f171,plain,(
% 2.14/0.69    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X0) | ~v1_relat_1(X1)) )),
% 2.14/0.69    inference(duplicate_literal_removal,[],[f168])).
% 2.14/0.69  fof(f168,plain,(
% 2.14/0.69    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.14/0.69    inference(superposition,[],[f75,f65])).
% 2.14/0.69  fof(f65,plain,(
% 2.14/0.69    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.14/0.69    inference(cnf_transformation,[],[f26])).
% 2.14/0.69  fof(f26,plain,(
% 2.14/0.69    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.14/0.69    inference(ennf_transformation,[],[f6])).
% 2.14/0.69  fof(f6,axiom,(
% 2.14/0.69    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 2.14/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).
% 2.14/0.69  fof(f75,plain,(
% 2.14/0.69    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.14/0.69    inference(cnf_transformation,[],[f35])).
% 2.14/0.69  fof(f35,plain,(
% 2.14/0.69    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.14/0.69    inference(ennf_transformation,[],[f5])).
% 2.14/0.69  fof(f5,axiom,(
% 2.14/0.69    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 2.14/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).
% 2.14/0.69  fof(f731,plain,(
% 2.14/0.69    ~spl4_17 | ~spl4_31 | ~spl4_32 | ~spl4_5 | spl4_44 | ~spl4_42),
% 2.14/0.69    inference(avatar_split_clause,[],[f728,f708,f717,f196,f528,f524,f396])).
% 2.14/0.69  fof(f524,plain,(
% 2.14/0.69    spl4_31 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.14/0.69    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).
% 2.14/0.69  fof(f528,plain,(
% 2.14/0.69    spl4_32 <=> v1_funct_1(sK3)),
% 2.14/0.69    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 2.14/0.69  fof(f196,plain,(
% 2.14/0.69    spl4_5 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.14/0.69    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 2.14/0.69  fof(f708,plain,(
% 2.14/0.69    spl4_42 <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)),
% 2.14/0.69    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).
% 2.14/0.69  fof(f728,plain,(
% 2.14/0.69    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | ~spl4_42),
% 2.14/0.69    inference(superposition,[],[f87,f710])).
% 2.14/0.69  fof(f710,plain,(
% 2.14/0.69    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) | ~spl4_42),
% 2.14/0.69    inference(avatar_component_clause,[],[f708])).
% 2.14/0.69  fof(f87,plain,(
% 2.14/0.69    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 2.14/0.69    inference(cnf_transformation,[],[f44])).
% 2.14/0.69  fof(f44,plain,(
% 2.14/0.69    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.14/0.69    inference(flattening,[],[f43])).
% 2.14/0.69  fof(f43,plain,(
% 2.14/0.69    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.14/0.69    inference(ennf_transformation,[],[f19])).
% 2.14/0.69  fof(f19,axiom,(
% 2.14/0.69    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 2.14/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 2.14/0.69  fof(f724,plain,(
% 2.14/0.69    spl4_41),
% 2.14/0.69    inference(avatar_contradiction_clause,[],[f721])).
% 2.14/0.69  fof(f721,plain,(
% 2.14/0.69    $false | spl4_41),
% 2.14/0.69    inference(unit_resulting_resolution,[],[f56,f47,f49,f58,f706,f89])).
% 2.14/0.69  fof(f89,plain,(
% 2.14/0.69    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 2.14/0.69    inference(cnf_transformation,[],[f46])).
% 2.14/0.69  fof(f46,plain,(
% 2.14/0.69    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.14/0.69    inference(flattening,[],[f45])).
% 2.14/0.69  fof(f45,plain,(
% 2.14/0.69    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.14/0.69    inference(ennf_transformation,[],[f17])).
% 2.14/0.69  fof(f17,axiom,(
% 2.14/0.69    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 2.14/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 2.14/0.69  fof(f706,plain,(
% 2.14/0.69    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl4_41),
% 2.14/0.69    inference(avatar_component_clause,[],[f704])).
% 2.14/0.69  fof(f704,plain,(
% 2.14/0.69    spl4_41 <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.14/0.69    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).
% 2.14/0.69  fof(f47,plain,(
% 2.14/0.69    v1_funct_1(sK3)),
% 2.14/0.69    inference(cnf_transformation,[],[f24])).
% 2.14/0.69  fof(f56,plain,(
% 2.14/0.69    v1_funct_1(sK2)),
% 2.14/0.69    inference(cnf_transformation,[],[f24])).
% 2.14/0.69  fof(f711,plain,(
% 2.14/0.69    ~spl4_41 | spl4_42),
% 2.14/0.69    inference(avatar_split_clause,[],[f700,f708,f704])).
% 2.14/0.69  fof(f700,plain,(
% 2.14/0.69    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.14/0.69    inference(resolution,[],[f411,f51])).
% 2.14/0.69  fof(f51,plain,(
% 2.14/0.69    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 2.14/0.69    inference(cnf_transformation,[],[f24])).
% 2.14/0.69  fof(f411,plain,(
% 2.14/0.69    ( ! [X2,X1] : (~r2_relset_1(X2,X2,X1,k6_partfun1(X2)) | k6_partfun1(X2) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))) )),
% 2.14/0.69    inference(resolution,[],[f86,f61])).
% 2.14/0.69  fof(f61,plain,(
% 2.14/0.69    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.14/0.69    inference(cnf_transformation,[],[f18])).
% 2.14/0.69  fof(f18,axiom,(
% 2.14/0.69    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 2.14/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 2.14/0.69  fof(f86,plain,(
% 2.14/0.69    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 = X3 | ~r2_relset_1(X0,X1,X2,X3)) )),
% 2.14/0.69    inference(cnf_transformation,[],[f42])).
% 2.14/0.69  fof(f42,plain,(
% 2.14/0.69    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.14/0.69    inference(flattening,[],[f41])).
% 2.14/0.69  fof(f41,plain,(
% 2.14/0.69    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.14/0.69    inference(ennf_transformation,[],[f16])).
% 2.14/0.69  fof(f16,axiom,(
% 2.14/0.69    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.14/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 2.14/0.69  fof(f539,plain,(
% 2.14/0.69    spl4_32),
% 2.14/0.69    inference(avatar_contradiction_clause,[],[f538])).
% 2.14/0.69  fof(f538,plain,(
% 2.14/0.69    $false | spl4_32),
% 2.14/0.69    inference(subsumption_resolution,[],[f47,f530])).
% 2.14/0.69  fof(f530,plain,(
% 2.14/0.69    ~v1_funct_1(sK3) | spl4_32),
% 2.14/0.69    inference(avatar_component_clause,[],[f528])).
% 2.14/0.69  fof(f537,plain,(
% 2.14/0.69    spl4_31),
% 2.14/0.69    inference(avatar_contradiction_clause,[],[f536])).
% 2.14/0.69  fof(f536,plain,(
% 2.14/0.69    $false | spl4_31),
% 2.14/0.69    inference(subsumption_resolution,[],[f49,f526])).
% 2.14/0.69  fof(f526,plain,(
% 2.14/0.69    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl4_31),
% 2.14/0.69    inference(avatar_component_clause,[],[f524])).
% 2.14/0.69  fof(f417,plain,(
% 2.14/0.69    ~spl4_3 | spl4_18),
% 2.14/0.69    inference(avatar_contradiction_clause,[],[f415])).
% 2.14/0.69  fof(f415,plain,(
% 2.14/0.69    $false | (~spl4_3 | spl4_18)),
% 2.14/0.69    inference(unit_resulting_resolution,[],[f115,f56,f402,f68])).
% 2.14/0.69  fof(f68,plain,(
% 2.14/0.69    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.14/0.69    inference(cnf_transformation,[],[f30])).
% 2.14/0.69  fof(f30,plain,(
% 2.14/0.69    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.14/0.69    inference(flattening,[],[f29])).
% 2.14/0.69  fof(f29,plain,(
% 2.14/0.69    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.14/0.69    inference(ennf_transformation,[],[f11])).
% 2.14/0.69  fof(f11,axiom,(
% 2.14/0.69    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.14/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 2.14/0.69  fof(f402,plain,(
% 2.14/0.69    ~v1_relat_1(k2_funct_1(sK2)) | spl4_18),
% 2.14/0.69    inference(avatar_component_clause,[],[f400])).
% 2.14/0.69  fof(f115,plain,(
% 2.14/0.69    v1_relat_1(sK2) | ~spl4_3),
% 2.14/0.69    inference(avatar_component_clause,[],[f113])).
% 2.14/0.69  fof(f414,plain,(
% 2.14/0.69    spl4_17),
% 2.14/0.69    inference(avatar_contradiction_clause,[],[f413])).
% 2.14/0.69  fof(f413,plain,(
% 2.14/0.69    $false | spl4_17),
% 2.14/0.69    inference(subsumption_resolution,[],[f56,f398])).
% 2.14/0.69  fof(f398,plain,(
% 2.14/0.69    ~v1_funct_1(sK2) | spl4_17),
% 2.14/0.69    inference(avatar_component_clause,[],[f396])).
% 2.14/0.69  fof(f409,plain,(
% 2.14/0.69    spl4_16),
% 2.14/0.69    inference(avatar_contradiction_clause,[],[f408])).
% 2.14/0.69  fof(f408,plain,(
% 2.14/0.69    $false | spl4_16),
% 2.14/0.69    inference(subsumption_resolution,[],[f52,f394])).
% 2.14/0.69  fof(f394,plain,(
% 2.14/0.69    ~v2_funct_1(sK2) | spl4_16),
% 2.14/0.69    inference(avatar_component_clause,[],[f392])).
% 2.14/0.69  fof(f52,plain,(
% 2.14/0.69    v2_funct_1(sK2)),
% 2.14/0.69    inference(cnf_transformation,[],[f24])).
% 2.14/0.69  fof(f206,plain,(
% 2.14/0.69    spl4_5),
% 2.14/0.69    inference(avatar_contradiction_clause,[],[f205])).
% 2.14/0.69  fof(f205,plain,(
% 2.14/0.69    $false | spl4_5),
% 2.14/0.69    inference(subsumption_resolution,[],[f58,f198])).
% 2.14/0.69  fof(f198,plain,(
% 2.14/0.69    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl4_5),
% 2.14/0.69    inference(avatar_component_clause,[],[f196])).
% 2.14/0.69  fof(f204,plain,(
% 2.14/0.69    ~spl4_5 | spl4_6),
% 2.14/0.69    inference(avatar_split_clause,[],[f194,f200,f196])).
% 2.14/0.69  fof(f194,plain,(
% 2.14/0.69    sK1 = k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.14/0.69    inference(superposition,[],[f50,f82])).
% 2.14/0.69  fof(f82,plain,(
% 2.14/0.69    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.14/0.69    inference(cnf_transformation,[],[f39])).
% 2.14/0.69  fof(f39,plain,(
% 2.14/0.69    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.14/0.69    inference(ennf_transformation,[],[f15])).
% 2.14/0.69  fof(f15,axiom,(
% 2.14/0.69    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 2.14/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 2.14/0.69  fof(f50,plain,(
% 2.14/0.69    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 2.14/0.69    inference(cnf_transformation,[],[f24])).
% 2.14/0.69  fof(f128,plain,(
% 2.14/0.69    spl4_4),
% 2.14/0.69    inference(avatar_contradiction_clause,[],[f125])).
% 2.14/0.69  fof(f125,plain,(
% 2.14/0.69    $false | spl4_4),
% 2.14/0.69    inference(unit_resulting_resolution,[],[f74,f119])).
% 2.14/0.69  fof(f119,plain,(
% 2.14/0.69    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl4_4),
% 2.14/0.69    inference(avatar_component_clause,[],[f117])).
% 2.14/0.69  fof(f117,plain,(
% 2.14/0.69    spl4_4 <=> v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 2.14/0.69    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 2.14/0.69  fof(f74,plain,(
% 2.14/0.69    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.14/0.69    inference(cnf_transformation,[],[f4])).
% 2.14/0.69  fof(f4,axiom,(
% 2.14/0.69    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.14/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 2.14/0.69  fof(f124,plain,(
% 2.14/0.69    spl4_2),
% 2.14/0.69    inference(avatar_contradiction_clause,[],[f121])).
% 2.14/0.69  fof(f121,plain,(
% 2.14/0.69    $false | spl4_2),
% 2.14/0.69    inference(unit_resulting_resolution,[],[f74,f110])).
% 2.14/0.69  fof(f110,plain,(
% 2.14/0.69    ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | spl4_2),
% 2.14/0.69    inference(avatar_component_clause,[],[f108])).
% 2.14/0.69  fof(f108,plain,(
% 2.14/0.69    spl4_2 <=> v1_relat_1(k2_zfmisc_1(sK1,sK0))),
% 2.14/0.69    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 2.14/0.69  fof(f120,plain,(
% 2.14/0.69    spl4_3 | ~spl4_4),
% 2.14/0.69    inference(avatar_split_clause,[],[f101,f117,f113])).
% 2.14/0.69  fof(f101,plain,(
% 2.14/0.69    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | v1_relat_1(sK2)),
% 2.14/0.69    inference(resolution,[],[f67,f58])).
% 2.14/0.69  fof(f67,plain,(
% 2.14/0.69    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 2.14/0.69    inference(cnf_transformation,[],[f28])).
% 2.14/0.69  fof(f28,plain,(
% 2.14/0.69    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.14/0.69    inference(ennf_transformation,[],[f2])).
% 2.14/0.69  fof(f2,axiom,(
% 2.14/0.69    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.14/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 2.14/0.69  fof(f111,plain,(
% 2.14/0.69    spl4_1 | ~spl4_2),
% 2.14/0.69    inference(avatar_split_clause,[],[f100,f108,f104])).
% 2.14/0.69  fof(f100,plain,(
% 2.14/0.69    ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | v1_relat_1(sK3)),
% 2.14/0.69    inference(resolution,[],[f67,f49])).
% 2.14/0.69  % SZS output end Proof for theBenchmark
% 2.14/0.69  % (32505)------------------------------
% 2.14/0.69  % (32505)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.14/0.69  % (32505)Termination reason: Refutation
% 2.14/0.69  
% 2.14/0.69  % (32505)Memory used [KB]: 7419
% 2.14/0.69  % (32505)Time elapsed: 0.219 s
% 2.14/0.69  % (32505)------------------------------
% 2.14/0.69  % (32505)------------------------------
% 2.14/0.69  % (32491)Success in time 0.326 s
%------------------------------------------------------------------------------
