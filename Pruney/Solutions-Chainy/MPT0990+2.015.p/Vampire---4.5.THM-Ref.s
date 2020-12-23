%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:30 EST 2020

% Result     : Theorem 2.03s
% Output     : Refutation 2.03s
% Verified   : 
% Statistics : Number of formulae       :  216 ( 435 expanded)
%              Number of leaves         :   49 ( 149 expanded)
%              Depth                    :   11
%              Number of atoms          :  642 (1860 expanded)
%              Number of equality atoms :  127 ( 516 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1971,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f238,f243,f322,f324,f326,f329,f561,f651,f653,f673,f687,f710,f912,f924,f952,f968,f1199,f1222,f1237,f1245,f1288,f1421,f1761,f1856,f1925,f1954])).

fof(f1954,plain,(
    ~ spl4_146 ),
    inference(avatar_contradiction_clause,[],[f1926])).

fof(f1926,plain,
    ( $false
    | ~ spl4_146 ),
    inference(subsumption_resolution,[],[f72,f1848])).

fof(f1848,plain,
    ( sK3 = k2_funct_1(sK2)
    | ~ spl4_146 ),
    inference(avatar_component_clause,[],[f1846])).

fof(f1846,plain,
    ( spl4_146
  <=> sK3 = k2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_146])])).

fof(f72,plain,(
    sK3 != k2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f29])).

fof(f29,negated_conjecture,(
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
    inference(negated_conjecture,[],[f28])).

fof(f28,conjecture,(
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

fof(f1925,plain,
    ( ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_107
    | ~ spl4_60
    | spl4_145 ),
    inference(avatar_split_clause,[],[f1924,f1842,f933,f1362,f305,f301,f297])).

fof(f297,plain,
    ( spl4_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f301,plain,
    ( spl4_4
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f305,plain,
    ( spl4_5
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f1362,plain,
    ( spl4_107
  <=> r1_tarski(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_107])])).

fof(f933,plain,
    ( spl4_60
  <=> k6_partfun1(sK0) = k6_partfun1(k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_60])])).

fof(f1842,plain,
    ( spl4_145
  <=> r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_145])])).

fof(f1924,plain,
    ( ~ r1_tarski(sK0,sK0)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_60
    | spl4_145 ),
    inference(forward_demodulation,[],[f1923,f1012])).

fof(f1012,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl4_60 ),
    inference(forward_demodulation,[],[f979,f117])).

fof(f117,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f84,f77])).

fof(f77,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f84,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f979,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k6_partfun1(sK0))
    | ~ spl4_60 ),
    inference(superposition,[],[f117,f935])).

fof(f935,plain,
    ( k6_partfun1(sK0) = k6_partfun1(k1_relat_1(sK2))
    | ~ spl4_60 ),
    inference(avatar_component_clause,[],[f933])).

fof(f1923,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK0)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl4_145 ),
    inference(superposition,[],[f1844,f92])).

fof(f92,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f1844,plain,
    ( ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0)
    | spl4_145 ),
    inference(avatar_component_clause,[],[f1842])).

fof(f1856,plain,
    ( ~ spl4_6
    | ~ spl4_145
    | spl4_146
    | ~ spl4_135 ),
    inference(avatar_split_clause,[],[f1836,f1758,f1846,f1842,f309])).

fof(f309,plain,
    ( spl4_6
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f1758,plain,
    ( spl4_135
  <=> sK3 = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_135])])).

fof(f1836,plain,
    ( sK3 = k2_funct_1(sK2)
    | ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl4_135 ),
    inference(superposition,[],[f122,f1760])).

fof(f1760,plain,
    ( sK3 = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0))
    | ~ spl4_135 ),
    inference(avatar_component_clause,[],[f1758])).

fof(f122,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_partfun1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f98,f77])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

fof(f1761,plain,
    ( ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_35
    | ~ spl4_3
    | spl4_135
    | ~ spl4_2
    | ~ spl4_33
    | ~ spl4_99 ),
    inference(avatar_split_clause,[],[f1756,f1285,f676,f234,f1758,f297,f698,f309,f305,f301])).

fof(f698,plain,
    ( spl4_35
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f234,plain,
    ( spl4_2
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f676,plain,
    ( spl4_33
  <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).

fof(f1285,plain,
    ( spl4_99
  <=> sK3 = k5_relat_1(k6_partfun1(sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_99])])).

fof(f1756,plain,
    ( sK3 = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0))
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ spl4_2
    | ~ spl4_33
    | ~ spl4_99 ),
    inference(forward_demodulation,[],[f1755,f1287])).

fof(f1287,plain,
    ( sK3 = k5_relat_1(k6_partfun1(sK1),sK3)
    | ~ spl4_99 ),
    inference(avatar_component_clause,[],[f1285])).

fof(f1755,plain,
    ( k5_relat_1(k6_partfun1(sK1),sK3) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0))
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ spl4_2
    | ~ spl4_33 ),
    inference(forward_demodulation,[],[f1694,f236])).

fof(f236,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f234])).

fof(f1694,plain,
    ( k5_relat_1(k6_partfun1(k2_relat_1(sK2)),sK3) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0))
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ spl4_33 ),
    inference(superposition,[],[f344,f678])).

fof(f678,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl4_33 ),
    inference(avatar_component_clause,[],[f676])).

fof(f344,plain,(
    ! [X10,X9] :
      ( k5_relat_1(k2_funct_1(X9),k5_relat_1(X9,X10)) = k5_relat_1(k6_partfun1(k2_relat_1(X9)),X10)
      | ~ v1_relat_1(X9)
      | ~ v1_relat_1(X10)
      | ~ v1_relat_1(k2_funct_1(X9))
      | ~ v1_funct_1(X9)
      | ~ v2_funct_1(X9) ) ),
    inference(duplicate_literal_removal,[],[f333])).

fof(f333,plain,(
    ! [X10,X9] :
      ( k5_relat_1(k2_funct_1(X9),k5_relat_1(X9,X10)) = k5_relat_1(k6_partfun1(k2_relat_1(X9)),X10)
      | ~ v1_relat_1(X9)
      | ~ v1_relat_1(X10)
      | ~ v1_relat_1(k2_funct_1(X9))
      | ~ v1_funct_1(X9)
      | ~ v2_funct_1(X9)
      | ~ v1_relat_1(X9) ) ),
    inference(superposition,[],[f87,f120])).

fof(f120,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f94,f77])).

fof(f94,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
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

fof(f1421,plain,(
    spl4_107 ),
    inference(avatar_contradiction_clause,[],[f1416])).

fof(f1416,plain,
    ( $false
    | spl4_107 ),
    inference(unit_resulting_resolution,[],[f125,f1364,f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f1364,plain,
    ( ~ r1_tarski(sK0,sK0)
    | spl4_107 ),
    inference(avatar_component_clause,[],[f1362])).

fof(f125,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f78,f76])).

fof(f76,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f78,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f1288,plain,
    ( ~ spl4_35
    | spl4_99
    | ~ spl4_93 ),
    inference(avatar_split_clause,[],[f1264,f1232,f1285,f698])).

fof(f1232,plain,
    ( spl4_93
  <=> sK1 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_93])])).

fof(f1264,plain,
    ( sK3 = k5_relat_1(k6_partfun1(sK1),sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_93 ),
    inference(superposition,[],[f119,f1234])).

fof(f1234,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl4_93 ),
    inference(avatar_component_clause,[],[f1232])).

fof(f119,plain,(
    ! [X0] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f85,f77])).

fof(f85,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).

fof(f1245,plain,(
    spl4_92 ),
    inference(avatar_contradiction_clause,[],[f1238])).

fof(f1238,plain,
    ( $false
    | spl4_92 ),
    inference(subsumption_resolution,[],[f150,f1230])).

fof(f1230,plain,
    ( ~ v4_relat_1(sK2,sK0)
    | spl4_92 ),
    inference(avatar_component_clause,[],[f1228])).

fof(f1228,plain,
    ( spl4_92
  <=> v4_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_92])])).

fof(f150,plain,(
    v4_relat_1(sK2,sK0) ),
    inference(resolution,[],[f107,f75])).

fof(f75,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f31])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f1237,plain,
    ( ~ spl4_92
    | ~ spl4_3
    | spl4_93
    | ~ spl4_2
    | ~ spl4_89 ),
    inference(avatar_split_clause,[],[f1236,f1192,f234,f1232,f297,f1228])).

fof(f1192,plain,
    ( spl4_89
  <=> k1_relat_1(sK3) = k9_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_89])])).

fof(f1236,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ v4_relat_1(sK2,sK0)
    | ~ spl4_2
    | ~ spl4_89 ),
    inference(forward_demodulation,[],[f1225,f236])).

fof(f1225,plain,
    ( k1_relat_1(sK3) = k2_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v4_relat_1(sK2,sK0)
    | ~ spl4_89 ),
    inference(superposition,[],[f169,f1194])).

fof(f1194,plain,
    ( k1_relat_1(sK3) = k9_relat_1(sK2,sK0)
    | ~ spl4_89 ),
    inference(avatar_component_clause,[],[f1192])).

fof(f169,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = k9_relat_1(X0,X1)
      | ~ v1_relat_1(X0)
      | ~ v4_relat_1(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f168])).

fof(f168,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = k9_relat_1(X0,X1)
      | ~ v1_relat_1(X0)
      | ~ v4_relat_1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f97,f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f97,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f1222,plain,(
    spl4_90 ),
    inference(avatar_contradiction_clause,[],[f1220])).

fof(f1220,plain,
    ( $false
    | spl4_90 ),
    inference(unit_resulting_resolution,[],[f135,f151,f1198,f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f1198,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),sK1)
    | spl4_90 ),
    inference(avatar_component_clause,[],[f1196])).

fof(f1196,plain,
    ( spl4_90
  <=> r1_tarski(k1_relat_1(sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_90])])).

fof(f151,plain,(
    v4_relat_1(sK3,sK1) ),
    inference(resolution,[],[f107,f66])).

fof(f66,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f31])).

fof(f135,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f105,f66])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f1199,plain,
    ( ~ spl4_35
    | ~ spl4_3
    | ~ spl4_5
    | spl4_89
    | ~ spl4_90
    | ~ spl4_2
    | ~ spl4_33 ),
    inference(avatar_split_clause,[],[f1190,f676,f234,f1196,f1192,f305,f297,f698])).

fof(f1190,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),sK1)
    | k1_relat_1(sK3) = k9_relat_1(sK2,sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ spl4_2
    | ~ spl4_33 ),
    inference(forward_demodulation,[],[f1189,f236])).

fof(f1189,plain,
    ( k1_relat_1(sK3) = k9_relat_1(sK2,sK0)
    | ~ v1_funct_1(sK2)
    | ~ r1_tarski(k1_relat_1(sK3),k2_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ spl4_33 ),
    inference(forward_demodulation,[],[f1128,f118])).

fof(f118,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f83,f77])).

fof(f83,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f1128,plain,
    ( k1_relat_1(sK3) = k9_relat_1(sK2,k1_relat_1(k6_partfun1(sK0)))
    | ~ v1_funct_1(sK2)
    | ~ r1_tarski(k1_relat_1(sK3),k2_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ spl4_33 ),
    inference(superposition,[],[f285,f678])).

fof(f285,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = k9_relat_1(X0,k1_relat_1(k5_relat_1(X0,X1)))
      | ~ v1_funct_1(X0)
      | ~ r1_tarski(k1_relat_1(X1),k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1) ) ),
    inference(duplicate_literal_removal,[],[f278])).

fof(f278,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = k9_relat_1(X0,k1_relat_1(k5_relat_1(X0,X1)))
      | ~ v1_funct_1(X0)
      | ~ r1_tarski(k1_relat_1(X1),k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f101,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

fof(f101,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ v1_funct_1(X1)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

fof(f968,plain,(
    spl4_61 ),
    inference(avatar_contradiction_clause,[],[f966])).

fof(f966,plain,
    ( $false
    | spl4_61 ),
    inference(unit_resulting_resolution,[],[f134,f150,f939,f100])).

fof(f939,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK0)
    | spl4_61 ),
    inference(avatar_component_clause,[],[f937])).

fof(f937,plain,
    ( spl4_61
  <=> r1_tarski(k1_relat_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_61])])).

fof(f134,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f105,f75])).

fof(f952,plain,
    ( ~ spl4_57
    | spl4_60
    | ~ spl4_61
    | ~ spl4_58 ),
    inference(avatar_split_clause,[],[f951,f909,f937,f933,f905])).

fof(f905,plain,
    ( spl4_57
  <=> v1_relat_1(k6_partfun1(k1_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_57])])).

fof(f909,plain,
    ( spl4_58
  <=> k6_partfun1(sK0) = k5_relat_1(k6_partfun1(k1_relat_1(sK2)),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_58])])).

fof(f951,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK0)
    | k6_partfun1(sK0) = k6_partfun1(k1_relat_1(sK2))
    | ~ v1_relat_1(k6_partfun1(k1_relat_1(sK2)))
    | ~ spl4_58 ),
    inference(forward_demodulation,[],[f928,f117])).

fof(f928,plain,
    ( k6_partfun1(sK0) = k6_partfun1(k1_relat_1(sK2))
    | ~ r1_tarski(k2_relat_1(k6_partfun1(k1_relat_1(sK2))),sK0)
    | ~ v1_relat_1(k6_partfun1(k1_relat_1(sK2)))
    | ~ spl4_58 ),
    inference(superposition,[],[f122,f911])).

fof(f911,plain,
    ( k6_partfun1(sK0) = k5_relat_1(k6_partfun1(k1_relat_1(sK2)),k6_partfun1(sK0))
    | ~ spl4_58 ),
    inference(avatar_component_clause,[],[f909])).

fof(f924,plain,(
    spl4_57 ),
    inference(avatar_contradiction_clause,[],[f919])).

fof(f919,plain,
    ( $false
    | spl4_57 ),
    inference(unit_resulting_resolution,[],[f82,f907,f105])).

fof(f907,plain,
    ( ~ v1_relat_1(k6_partfun1(k1_relat_1(sK2)))
    | spl4_57 ),
    inference(avatar_component_clause,[],[f905])).

fof(f82,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f912,plain,
    ( ~ spl4_57
    | ~ spl4_35
    | ~ spl4_3
    | spl4_58
    | ~ spl4_33 ),
    inference(avatar_split_clause,[],[f880,f676,f909,f297,f698,f905])).

fof(f880,plain,
    ( k6_partfun1(sK0) = k5_relat_1(k6_partfun1(k1_relat_1(sK2)),k6_partfun1(sK0))
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(k6_partfun1(k1_relat_1(sK2)))
    | ~ spl4_33 ),
    inference(superposition,[],[f343,f678])).

fof(f343,plain,(
    ! [X12,X11] :
      ( k5_relat_1(X11,X12) = k5_relat_1(k6_partfun1(k1_relat_1(X11)),k5_relat_1(X11,X12))
      | ~ v1_relat_1(X11)
      | ~ v1_relat_1(X12)
      | ~ v1_relat_1(k6_partfun1(k1_relat_1(X11))) ) ),
    inference(duplicate_literal_removal,[],[f334])).

fof(f334,plain,(
    ! [X12,X11] :
      ( k5_relat_1(X11,X12) = k5_relat_1(k6_partfun1(k1_relat_1(X11)),k5_relat_1(X11,X12))
      | ~ v1_relat_1(X11)
      | ~ v1_relat_1(X12)
      | ~ v1_relat_1(k6_partfun1(k1_relat_1(X11)))
      | ~ v1_relat_1(X11) ) ),
    inference(superposition,[],[f87,f119])).

fof(f710,plain,(
    spl4_35 ),
    inference(avatar_contradiction_clause,[],[f705])).

fof(f705,plain,
    ( $false
    | spl4_35 ),
    inference(subsumption_resolution,[],[f135,f700])).

fof(f700,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_35 ),
    inference(avatar_component_clause,[],[f698])).

fof(f687,plain,
    ( ~ spl4_5
    | ~ spl4_28
    | ~ spl4_29
    | ~ spl4_1
    | spl4_33
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f684,f558,f676,f230,f621,f617,f305])).

fof(f617,plain,
    ( spl4_28
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f621,plain,
    ( spl4_29
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f230,plain,
    ( spl4_1
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f558,plain,
    ( spl4_22
  <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f684,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_22 ),
    inference(superposition,[],[f112,f560])).

fof(f560,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f558])).

fof(f112,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f673,plain,(
    spl4_21 ),
    inference(avatar_contradiction_clause,[],[f661])).

fof(f661,plain,
    ( $false
    | spl4_21 ),
    inference(unit_resulting_resolution,[],[f73,f64,f66,f75,f556,f114])).

fof(f114,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f556,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl4_21 ),
    inference(avatar_component_clause,[],[f554])).

fof(f554,plain,
    ( spl4_21
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f64,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f73,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f653,plain,(
    spl4_29 ),
    inference(avatar_contradiction_clause,[],[f652])).

fof(f652,plain,
    ( $false
    | spl4_29 ),
    inference(subsumption_resolution,[],[f64,f623])).

fof(f623,plain,
    ( ~ v1_funct_1(sK3)
    | spl4_29 ),
    inference(avatar_component_clause,[],[f621])).

fof(f651,plain,(
    spl4_28 ),
    inference(avatar_contradiction_clause,[],[f647])).

fof(f647,plain,
    ( $false
    | spl4_28 ),
    inference(subsumption_resolution,[],[f66,f619])).

fof(f619,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl4_28 ),
    inference(avatar_component_clause,[],[f617])).

fof(f561,plain,
    ( ~ spl4_21
    | spl4_22 ),
    inference(avatar_split_clause,[],[f551,f558,f554])).

fof(f551,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f522,f68])).

fof(f68,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f31])).

fof(f522,plain,(
    ! [X8,X7] :
      ( ~ r2_relset_1(X8,X8,X7,k6_partfun1(X8))
      | k6_partfun1(X8) = X7
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X8,X8))) ) ),
    inference(resolution,[],[f111,f82])).

fof(f111,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f329,plain,(
    spl4_6 ),
    inference(avatar_contradiction_clause,[],[f327])).

fof(f327,plain,
    ( $false
    | spl4_6 ),
    inference(unit_resulting_resolution,[],[f134,f73,f311,f88])).

fof(f88,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
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

fof(f311,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | spl4_6 ),
    inference(avatar_component_clause,[],[f309])).

fof(f326,plain,(
    spl4_5 ),
    inference(avatar_contradiction_clause,[],[f325])).

fof(f325,plain,
    ( $false
    | spl4_5 ),
    inference(subsumption_resolution,[],[f73,f307])).

fof(f307,plain,
    ( ~ v1_funct_1(sK2)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f305])).

fof(f324,plain,(
    spl4_4 ),
    inference(avatar_contradiction_clause,[],[f323])).

fof(f323,plain,
    ( $false
    | spl4_4 ),
    inference(subsumption_resolution,[],[f69,f303])).

fof(f303,plain,
    ( ~ v2_funct_1(sK2)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f301])).

fof(f69,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f322,plain,(
    spl4_3 ),
    inference(avatar_contradiction_clause,[],[f317])).

fof(f317,plain,
    ( $false
    | spl4_3 ),
    inference(subsumption_resolution,[],[f134,f299])).

fof(f299,plain,
    ( ~ v1_relat_1(sK2)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f297])).

fof(f243,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f239])).

fof(f239,plain,
    ( $false
    | spl4_1 ),
    inference(subsumption_resolution,[],[f75,f232])).

fof(f232,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f230])).

fof(f238,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f228,f234,f230])).

fof(f228,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f67,f106])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f67,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:51:54 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.51  % (23722)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.52  % (23719)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.52  % (23711)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.52  % (23732)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.52  % (23724)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.53  % (23718)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.53  % (23714)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.53  % (23712)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.53  % (23713)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.53  % (23716)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (23730)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.53  % (23710)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.54  % (23736)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.54  % (23717)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.54  % (23728)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.54  % (23734)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.54  % (23735)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.54  % (23729)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.54  % (23715)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.54  % (23731)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.55  % (23726)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.55  % (23738)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.55  % (23726)Refutation not found, incomplete strategy% (23726)------------------------------
% 0.20/0.55  % (23726)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (23726)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (23726)Memory used [KB]: 10746
% 0.20/0.55  % (23726)Time elapsed: 0.138 s
% 0.20/0.55  % (23726)------------------------------
% 0.20/0.55  % (23726)------------------------------
% 0.20/0.55  % (23725)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.55  % (23737)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.55  % (23727)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.55  % (23723)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.55  % (23733)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.55  % (23739)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.56  % (23721)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.56  % (23720)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 2.03/0.64  % (23723)Refutation found. Thanks to Tanya!
% 2.03/0.64  % SZS status Theorem for theBenchmark
% 2.03/0.65  % SZS output start Proof for theBenchmark
% 2.03/0.65  fof(f1971,plain,(
% 2.03/0.65    $false),
% 2.03/0.65    inference(avatar_sat_refutation,[],[f238,f243,f322,f324,f326,f329,f561,f651,f653,f673,f687,f710,f912,f924,f952,f968,f1199,f1222,f1237,f1245,f1288,f1421,f1761,f1856,f1925,f1954])).
% 2.03/0.65  fof(f1954,plain,(
% 2.03/0.65    ~spl4_146),
% 2.03/0.65    inference(avatar_contradiction_clause,[],[f1926])).
% 2.03/0.65  fof(f1926,plain,(
% 2.03/0.65    $false | ~spl4_146),
% 2.03/0.65    inference(subsumption_resolution,[],[f72,f1848])).
% 2.03/0.65  fof(f1848,plain,(
% 2.03/0.65    sK3 = k2_funct_1(sK2) | ~spl4_146),
% 2.03/0.65    inference(avatar_component_clause,[],[f1846])).
% 2.03/0.65  fof(f1846,plain,(
% 2.03/0.65    spl4_146 <=> sK3 = k2_funct_1(sK2)),
% 2.03/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_146])])).
% 2.03/0.65  fof(f72,plain,(
% 2.03/0.65    sK3 != k2_funct_1(sK2)),
% 2.03/0.65    inference(cnf_transformation,[],[f31])).
% 2.03/0.65  fof(f31,plain,(
% 2.03/0.65    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.03/0.65    inference(flattening,[],[f30])).
% 2.03/0.65  fof(f30,plain,(
% 2.03/0.65    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.03/0.65    inference(ennf_transformation,[],[f29])).
% 2.03/0.66  fof(f29,negated_conjecture,(
% 2.03/0.66    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.03/0.66    inference(negated_conjecture,[],[f28])).
% 2.03/0.66  fof(f28,conjecture,(
% 2.03/0.66    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.03/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).
% 2.03/0.66  fof(f1925,plain,(
% 2.03/0.66    ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_107 | ~spl4_60 | spl4_145),
% 2.03/0.66    inference(avatar_split_clause,[],[f1924,f1842,f933,f1362,f305,f301,f297])).
% 2.03/0.66  fof(f297,plain,(
% 2.03/0.66    spl4_3 <=> v1_relat_1(sK2)),
% 2.03/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 2.03/0.66  fof(f301,plain,(
% 2.03/0.66    spl4_4 <=> v2_funct_1(sK2)),
% 2.03/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 2.03/0.66  fof(f305,plain,(
% 2.03/0.66    spl4_5 <=> v1_funct_1(sK2)),
% 2.03/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 2.03/0.66  fof(f1362,plain,(
% 2.03/0.66    spl4_107 <=> r1_tarski(sK0,sK0)),
% 2.03/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_107])])).
% 2.03/0.66  fof(f933,plain,(
% 2.03/0.66    spl4_60 <=> k6_partfun1(sK0) = k6_partfun1(k1_relat_1(sK2))),
% 2.03/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_60])])).
% 2.03/0.66  fof(f1842,plain,(
% 2.03/0.66    spl4_145 <=> r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0)),
% 2.03/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_145])])).
% 2.03/0.66  fof(f1924,plain,(
% 2.03/0.66    ~r1_tarski(sK0,sK0) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl4_60 | spl4_145)),
% 2.03/0.66    inference(forward_demodulation,[],[f1923,f1012])).
% 2.03/0.66  fof(f1012,plain,(
% 2.03/0.66    sK0 = k1_relat_1(sK2) | ~spl4_60),
% 2.03/0.66    inference(forward_demodulation,[],[f979,f117])).
% 2.03/0.66  fof(f117,plain,(
% 2.03/0.66    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 2.03/0.66    inference(definition_unfolding,[],[f84,f77])).
% 2.03/0.66  fof(f77,plain,(
% 2.03/0.66    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.03/0.66    inference(cnf_transformation,[],[f26])).
% 2.03/0.66  fof(f26,axiom,(
% 2.03/0.66    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.03/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 2.03/0.66  fof(f84,plain,(
% 2.03/0.66    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 2.03/0.66    inference(cnf_transformation,[],[f9])).
% 2.03/0.66  fof(f9,axiom,(
% 2.03/0.66    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 2.03/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 2.03/0.66  fof(f979,plain,(
% 2.03/0.66    k1_relat_1(sK2) = k2_relat_1(k6_partfun1(sK0)) | ~spl4_60),
% 2.03/0.66    inference(superposition,[],[f117,f935])).
% 2.03/0.66  fof(f935,plain,(
% 2.03/0.66    k6_partfun1(sK0) = k6_partfun1(k1_relat_1(sK2)) | ~spl4_60),
% 2.03/0.66    inference(avatar_component_clause,[],[f933])).
% 2.03/0.66  fof(f1923,plain,(
% 2.03/0.66    ~r1_tarski(k1_relat_1(sK2),sK0) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | spl4_145),
% 2.03/0.66    inference(superposition,[],[f1844,f92])).
% 2.03/0.66  fof(f92,plain,(
% 2.03/0.66    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.03/0.66    inference(cnf_transformation,[],[f40])).
% 2.03/0.66  fof(f40,plain,(
% 2.03/0.66    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.03/0.66    inference(flattening,[],[f39])).
% 2.03/0.66  fof(f39,plain,(
% 2.03/0.66    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.03/0.66    inference(ennf_transformation,[],[f16])).
% 2.03/0.66  fof(f16,axiom,(
% 2.03/0.66    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 2.03/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 2.03/0.66  fof(f1844,plain,(
% 2.03/0.66    ~r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) | spl4_145),
% 2.03/0.66    inference(avatar_component_clause,[],[f1842])).
% 2.03/0.66  fof(f1856,plain,(
% 2.03/0.66    ~spl4_6 | ~spl4_145 | spl4_146 | ~spl4_135),
% 2.03/0.66    inference(avatar_split_clause,[],[f1836,f1758,f1846,f1842,f309])).
% 2.03/0.66  fof(f309,plain,(
% 2.03/0.66    spl4_6 <=> v1_relat_1(k2_funct_1(sK2))),
% 2.03/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 2.03/0.66  fof(f1758,plain,(
% 2.03/0.66    spl4_135 <=> sK3 = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0))),
% 2.03/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_135])])).
% 2.03/0.66  fof(f1836,plain,(
% 2.03/0.66    sK3 = k2_funct_1(sK2) | ~r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) | ~v1_relat_1(k2_funct_1(sK2)) | ~spl4_135),
% 2.03/0.66    inference(superposition,[],[f122,f1760])).
% 2.03/0.66  fof(f1760,plain,(
% 2.03/0.66    sK3 = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) | ~spl4_135),
% 2.03/0.66    inference(avatar_component_clause,[],[f1758])).
% 2.03/0.66  fof(f122,plain,(
% 2.03/0.66    ( ! [X0,X1] : (k5_relat_1(X1,k6_partfun1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 2.03/0.66    inference(definition_unfolding,[],[f98,f77])).
% 2.03/0.66  fof(f98,plain,(
% 2.03/0.66    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | k5_relat_1(X1,k6_relat_1(X0)) = X1) )),
% 2.03/0.66    inference(cnf_transformation,[],[f47])).
% 2.03/0.66  fof(f47,plain,(
% 2.03/0.66    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 2.03/0.66    inference(flattening,[],[f46])).
% 2.03/0.66  fof(f46,plain,(
% 2.03/0.66    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.03/0.66    inference(ennf_transformation,[],[f11])).
% 2.03/0.66  fof(f11,axiom,(
% 2.03/0.66    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 2.03/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).
% 2.03/0.66  fof(f1761,plain,(
% 2.03/0.66    ~spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_35 | ~spl4_3 | spl4_135 | ~spl4_2 | ~spl4_33 | ~spl4_99),
% 2.03/0.66    inference(avatar_split_clause,[],[f1756,f1285,f676,f234,f1758,f297,f698,f309,f305,f301])).
% 2.03/0.66  fof(f698,plain,(
% 2.03/0.66    spl4_35 <=> v1_relat_1(sK3)),
% 2.03/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).
% 2.03/0.66  fof(f234,plain,(
% 2.03/0.66    spl4_2 <=> sK1 = k2_relat_1(sK2)),
% 2.03/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 2.03/0.66  fof(f676,plain,(
% 2.03/0.66    spl4_33 <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 2.03/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).
% 2.03/0.66  fof(f1285,plain,(
% 2.03/0.66    spl4_99 <=> sK3 = k5_relat_1(k6_partfun1(sK1),sK3)),
% 2.03/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_99])])).
% 2.03/0.66  fof(f1756,plain,(
% 2.03/0.66    sK3 = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) | ~v1_relat_1(sK2) | ~v1_relat_1(sK3) | ~v1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | (~spl4_2 | ~spl4_33 | ~spl4_99)),
% 2.03/0.66    inference(forward_demodulation,[],[f1755,f1287])).
% 2.03/0.66  fof(f1287,plain,(
% 2.03/0.66    sK3 = k5_relat_1(k6_partfun1(sK1),sK3) | ~spl4_99),
% 2.03/0.66    inference(avatar_component_clause,[],[f1285])).
% 2.03/0.66  fof(f1755,plain,(
% 2.03/0.66    k5_relat_1(k6_partfun1(sK1),sK3) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) | ~v1_relat_1(sK2) | ~v1_relat_1(sK3) | ~v1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | (~spl4_2 | ~spl4_33)),
% 2.03/0.66    inference(forward_demodulation,[],[f1694,f236])).
% 2.03/0.66  fof(f236,plain,(
% 2.03/0.66    sK1 = k2_relat_1(sK2) | ~spl4_2),
% 2.03/0.66    inference(avatar_component_clause,[],[f234])).
% 2.03/0.66  fof(f1694,plain,(
% 2.03/0.66    k5_relat_1(k6_partfun1(k2_relat_1(sK2)),sK3) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) | ~v1_relat_1(sK2) | ~v1_relat_1(sK3) | ~v1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~spl4_33),
% 2.03/0.66    inference(superposition,[],[f344,f678])).
% 2.03/0.66  fof(f678,plain,(
% 2.03/0.66    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~spl4_33),
% 2.03/0.66    inference(avatar_component_clause,[],[f676])).
% 2.03/0.66  fof(f344,plain,(
% 2.03/0.66    ( ! [X10,X9] : (k5_relat_1(k2_funct_1(X9),k5_relat_1(X9,X10)) = k5_relat_1(k6_partfun1(k2_relat_1(X9)),X10) | ~v1_relat_1(X9) | ~v1_relat_1(X10) | ~v1_relat_1(k2_funct_1(X9)) | ~v1_funct_1(X9) | ~v2_funct_1(X9)) )),
% 2.03/0.66    inference(duplicate_literal_removal,[],[f333])).
% 2.03/0.66  fof(f333,plain,(
% 2.03/0.66    ( ! [X10,X9] : (k5_relat_1(k2_funct_1(X9),k5_relat_1(X9,X10)) = k5_relat_1(k6_partfun1(k2_relat_1(X9)),X10) | ~v1_relat_1(X9) | ~v1_relat_1(X10) | ~v1_relat_1(k2_funct_1(X9)) | ~v1_funct_1(X9) | ~v2_funct_1(X9) | ~v1_relat_1(X9)) )),
% 2.03/0.66    inference(superposition,[],[f87,f120])).
% 2.03/0.66  fof(f120,plain,(
% 2.03/0.66    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.03/0.66    inference(definition_unfolding,[],[f94,f77])).
% 2.03/0.66  fof(f94,plain,(
% 2.03/0.66    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))) )),
% 2.03/0.66    inference(cnf_transformation,[],[f42])).
% 2.03/0.66  fof(f42,plain,(
% 2.03/0.66    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.03/0.66    inference(flattening,[],[f41])).
% 2.03/0.66  fof(f41,plain,(
% 2.03/0.66    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.03/0.66    inference(ennf_transformation,[],[f17])).
% 2.03/0.66  fof(f17,axiom,(
% 2.03/0.66    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)))))),
% 2.03/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).
% 2.03/0.66  fof(f87,plain,(
% 2.03/0.66    ( ! [X2,X0,X1] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | ~v1_relat_1(X0)) )),
% 2.03/0.66    inference(cnf_transformation,[],[f34])).
% 2.03/0.66  fof(f34,plain,(
% 2.03/0.66    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.03/0.66    inference(ennf_transformation,[],[f8])).
% 2.03/0.66  fof(f8,axiom,(
% 2.03/0.66    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 2.03/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).
% 2.03/0.66  fof(f1421,plain,(
% 2.03/0.66    spl4_107),
% 2.03/0.66    inference(avatar_contradiction_clause,[],[f1416])).
% 2.03/0.66  fof(f1416,plain,(
% 2.03/0.66    $false | spl4_107),
% 2.03/0.66    inference(unit_resulting_resolution,[],[f125,f1364,f104])).
% 2.03/0.66  fof(f104,plain,(
% 2.03/0.66    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 2.03/0.66    inference(cnf_transformation,[],[f3])).
% 2.03/0.66  fof(f3,axiom,(
% 2.03/0.66    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.03/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 2.03/0.66  fof(f1364,plain,(
% 2.03/0.66    ~r1_tarski(sK0,sK0) | spl4_107),
% 2.03/0.66    inference(avatar_component_clause,[],[f1362])).
% 2.03/0.66  fof(f125,plain,(
% 2.03/0.66    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 2.03/0.66    inference(forward_demodulation,[],[f78,f76])).
% 2.03/0.66  fof(f76,plain,(
% 2.03/0.66    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 2.03/0.66    inference(cnf_transformation,[],[f1])).
% 2.03/0.66  fof(f1,axiom,(
% 2.03/0.66    ! [X0] : k2_subset_1(X0) = X0),
% 2.03/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 2.03/0.66  fof(f78,plain,(
% 2.03/0.66    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 2.03/0.66    inference(cnf_transformation,[],[f2])).
% 2.03/0.66  fof(f2,axiom,(
% 2.03/0.66    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 2.03/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 2.03/0.66  fof(f1288,plain,(
% 2.03/0.66    ~spl4_35 | spl4_99 | ~spl4_93),
% 2.03/0.66    inference(avatar_split_clause,[],[f1264,f1232,f1285,f698])).
% 2.03/0.66  fof(f1232,plain,(
% 2.03/0.66    spl4_93 <=> sK1 = k1_relat_1(sK3)),
% 2.03/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_93])])).
% 2.03/0.66  fof(f1264,plain,(
% 2.03/0.66    sK3 = k5_relat_1(k6_partfun1(sK1),sK3) | ~v1_relat_1(sK3) | ~spl4_93),
% 2.03/0.66    inference(superposition,[],[f119,f1234])).
% 2.03/0.66  fof(f1234,plain,(
% 2.03/0.66    sK1 = k1_relat_1(sK3) | ~spl4_93),
% 2.03/0.66    inference(avatar_component_clause,[],[f1232])).
% 2.03/0.66  fof(f119,plain,(
% 2.03/0.66    ( ! [X0] : (k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) )),
% 2.03/0.66    inference(definition_unfolding,[],[f85,f77])).
% 2.03/0.66  fof(f85,plain,(
% 2.03/0.66    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0) )),
% 2.03/0.66    inference(cnf_transformation,[],[f32])).
% 2.03/0.66  fof(f32,plain,(
% 2.03/0.66    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 2.03/0.66    inference(ennf_transformation,[],[f10])).
% 2.03/0.66  fof(f10,axiom,(
% 2.03/0.66    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 2.03/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).
% 2.03/0.66  fof(f1245,plain,(
% 2.03/0.66    spl4_92),
% 2.03/0.66    inference(avatar_contradiction_clause,[],[f1238])).
% 2.03/0.66  fof(f1238,plain,(
% 2.03/0.66    $false | spl4_92),
% 2.03/0.66    inference(subsumption_resolution,[],[f150,f1230])).
% 2.03/0.66  fof(f1230,plain,(
% 2.03/0.66    ~v4_relat_1(sK2,sK0) | spl4_92),
% 2.03/0.66    inference(avatar_component_clause,[],[f1228])).
% 2.03/0.66  fof(f1228,plain,(
% 2.03/0.66    spl4_92 <=> v4_relat_1(sK2,sK0)),
% 2.03/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_92])])).
% 2.03/0.66  fof(f150,plain,(
% 2.03/0.66    v4_relat_1(sK2,sK0)),
% 2.03/0.66    inference(resolution,[],[f107,f75])).
% 2.03/0.66  fof(f75,plain,(
% 2.03/0.66    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.03/0.66    inference(cnf_transformation,[],[f31])).
% 2.03/0.66  fof(f107,plain,(
% 2.03/0.66    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 2.03/0.66    inference(cnf_transformation,[],[f55])).
% 2.03/0.66  fof(f55,plain,(
% 2.03/0.66    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.03/0.66    inference(ennf_transformation,[],[f20])).
% 2.03/0.66  fof(f20,axiom,(
% 2.03/0.66    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.03/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 2.03/0.66  fof(f1237,plain,(
% 2.03/0.66    ~spl4_92 | ~spl4_3 | spl4_93 | ~spl4_2 | ~spl4_89),
% 2.03/0.66    inference(avatar_split_clause,[],[f1236,f1192,f234,f1232,f297,f1228])).
% 2.03/0.66  fof(f1192,plain,(
% 2.03/0.66    spl4_89 <=> k1_relat_1(sK3) = k9_relat_1(sK2,sK0)),
% 2.03/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_89])])).
% 2.03/0.66  fof(f1236,plain,(
% 2.03/0.66    sK1 = k1_relat_1(sK3) | ~v1_relat_1(sK2) | ~v4_relat_1(sK2,sK0) | (~spl4_2 | ~spl4_89)),
% 2.03/0.66    inference(forward_demodulation,[],[f1225,f236])).
% 2.03/0.66  fof(f1225,plain,(
% 2.03/0.66    k1_relat_1(sK3) = k2_relat_1(sK2) | ~v1_relat_1(sK2) | ~v4_relat_1(sK2,sK0) | ~spl4_89),
% 2.03/0.66    inference(superposition,[],[f169,f1194])).
% 2.03/0.66  fof(f1194,plain,(
% 2.03/0.66    k1_relat_1(sK3) = k9_relat_1(sK2,sK0) | ~spl4_89),
% 2.03/0.66    inference(avatar_component_clause,[],[f1192])).
% 2.03/0.66  fof(f169,plain,(
% 2.03/0.66    ( ! [X0,X1] : (k2_relat_1(X0) = k9_relat_1(X0,X1) | ~v1_relat_1(X0) | ~v4_relat_1(X0,X1)) )),
% 2.03/0.66    inference(duplicate_literal_removal,[],[f168])).
% 2.03/0.66  fof(f168,plain,(
% 2.03/0.66    ( ! [X0,X1] : (k2_relat_1(X0) = k9_relat_1(X0,X1) | ~v1_relat_1(X0) | ~v4_relat_1(X0,X1) | ~v1_relat_1(X0)) )),
% 2.03/0.66    inference(superposition,[],[f97,f102])).
% 2.03/0.66  fof(f102,plain,(
% 2.03/0.66    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.03/0.66    inference(cnf_transformation,[],[f52])).
% 2.03/0.66  fof(f52,plain,(
% 2.03/0.66    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.03/0.66    inference(flattening,[],[f51])).
% 2.03/0.66  fof(f51,plain,(
% 2.03/0.66    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.03/0.66    inference(ennf_transformation,[],[f7])).
% 2.03/0.66  fof(f7,axiom,(
% 2.03/0.66    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 2.03/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 2.03/0.66  fof(f97,plain,(
% 2.03/0.66    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.03/0.66    inference(cnf_transformation,[],[f45])).
% 2.03/0.66  fof(f45,plain,(
% 2.03/0.66    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.03/0.66    inference(ennf_transformation,[],[f5])).
% 2.03/0.66  fof(f5,axiom,(
% 2.03/0.66    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 2.03/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 2.03/0.66  fof(f1222,plain,(
% 2.03/0.66    spl4_90),
% 2.03/0.66    inference(avatar_contradiction_clause,[],[f1220])).
% 2.03/0.66  fof(f1220,plain,(
% 2.03/0.66    $false | spl4_90),
% 2.03/0.66    inference(unit_resulting_resolution,[],[f135,f151,f1198,f100])).
% 2.03/0.66  fof(f100,plain,(
% 2.03/0.66    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1) | ~v4_relat_1(X1,X0)) )),
% 2.03/0.66    inference(cnf_transformation,[],[f48])).
% 2.03/0.66  fof(f48,plain,(
% 2.03/0.66    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.03/0.66    inference(ennf_transformation,[],[f4])).
% 2.03/0.66  fof(f4,axiom,(
% 2.03/0.66    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 2.03/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 2.03/0.66  fof(f1198,plain,(
% 2.03/0.66    ~r1_tarski(k1_relat_1(sK3),sK1) | spl4_90),
% 2.03/0.66    inference(avatar_component_clause,[],[f1196])).
% 2.03/0.66  fof(f1196,plain,(
% 2.03/0.66    spl4_90 <=> r1_tarski(k1_relat_1(sK3),sK1)),
% 2.03/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_90])])).
% 2.03/0.66  fof(f151,plain,(
% 2.03/0.66    v4_relat_1(sK3,sK1)),
% 2.03/0.66    inference(resolution,[],[f107,f66])).
% 2.03/0.66  fof(f66,plain,(
% 2.03/0.66    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.03/0.66    inference(cnf_transformation,[],[f31])).
% 2.03/0.66  fof(f135,plain,(
% 2.03/0.66    v1_relat_1(sK3)),
% 2.03/0.66    inference(resolution,[],[f105,f66])).
% 2.03/0.66  fof(f105,plain,(
% 2.03/0.66    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 2.03/0.66    inference(cnf_transformation,[],[f53])).
% 2.03/0.66  fof(f53,plain,(
% 2.03/0.66    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.03/0.66    inference(ennf_transformation,[],[f19])).
% 2.03/0.66  fof(f19,axiom,(
% 2.03/0.66    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.03/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 2.03/0.66  fof(f1199,plain,(
% 2.03/0.66    ~spl4_35 | ~spl4_3 | ~spl4_5 | spl4_89 | ~spl4_90 | ~spl4_2 | ~spl4_33),
% 2.03/0.66    inference(avatar_split_clause,[],[f1190,f676,f234,f1196,f1192,f305,f297,f698])).
% 2.03/0.66  fof(f1190,plain,(
% 2.03/0.66    ~r1_tarski(k1_relat_1(sK3),sK1) | k1_relat_1(sK3) = k9_relat_1(sK2,sK0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_relat_1(sK3) | (~spl4_2 | ~spl4_33)),
% 2.03/0.66    inference(forward_demodulation,[],[f1189,f236])).
% 2.03/0.66  fof(f1189,plain,(
% 2.03/0.66    k1_relat_1(sK3) = k9_relat_1(sK2,sK0) | ~v1_funct_1(sK2) | ~r1_tarski(k1_relat_1(sK3),k2_relat_1(sK2)) | ~v1_relat_1(sK2) | ~v1_relat_1(sK3) | ~spl4_33),
% 2.03/0.66    inference(forward_demodulation,[],[f1128,f118])).
% 2.03/0.66  fof(f118,plain,(
% 2.03/0.66    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 2.03/0.66    inference(definition_unfolding,[],[f83,f77])).
% 2.03/0.66  fof(f83,plain,(
% 2.03/0.66    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 2.03/0.66    inference(cnf_transformation,[],[f9])).
% 2.03/0.66  fof(f1128,plain,(
% 2.03/0.66    k1_relat_1(sK3) = k9_relat_1(sK2,k1_relat_1(k6_partfun1(sK0))) | ~v1_funct_1(sK2) | ~r1_tarski(k1_relat_1(sK3),k2_relat_1(sK2)) | ~v1_relat_1(sK2) | ~v1_relat_1(sK3) | ~spl4_33),
% 2.03/0.66    inference(superposition,[],[f285,f678])).
% 2.03/0.66  fof(f285,plain,(
% 2.03/0.66    ( ! [X0,X1] : (k1_relat_1(X1) = k9_relat_1(X0,k1_relat_1(k5_relat_1(X0,X1))) | ~v1_funct_1(X0) | ~r1_tarski(k1_relat_1(X1),k2_relat_1(X0)) | ~v1_relat_1(X0) | ~v1_relat_1(X1)) )),
% 2.03/0.66    inference(duplicate_literal_removal,[],[f278])).
% 2.03/0.66  fof(f278,plain,(
% 2.03/0.66    ( ! [X0,X1] : (k1_relat_1(X1) = k9_relat_1(X0,k1_relat_1(k5_relat_1(X0,X1))) | ~v1_funct_1(X0) | ~r1_tarski(k1_relat_1(X1),k2_relat_1(X0)) | ~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.03/0.66    inference(superposition,[],[f101,f86])).
% 2.03/0.66  fof(f86,plain,(
% 2.03/0.66    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.03/0.66    inference(cnf_transformation,[],[f33])).
% 2.03/0.66  fof(f33,plain,(
% 2.03/0.66    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.03/0.66    inference(ennf_transformation,[],[f6])).
% 2.03/0.66  fof(f6,axiom,(
% 2.03/0.66    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 2.03/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).
% 2.03/0.66  fof(f101,plain,(
% 2.03/0.66    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~v1_funct_1(X1) | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.03/0.66    inference(cnf_transformation,[],[f50])).
% 2.03/0.66  fof(f50,plain,(
% 2.03/0.66    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.03/0.66    inference(flattening,[],[f49])).
% 2.03/0.66  fof(f49,plain,(
% 2.03/0.66    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.03/0.66    inference(ennf_transformation,[],[f14])).
% 2.03/0.66  fof(f14,axiom,(
% 2.03/0.66    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 2.03/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).
% 2.03/0.66  fof(f968,plain,(
% 2.03/0.66    spl4_61),
% 2.03/0.66    inference(avatar_contradiction_clause,[],[f966])).
% 2.03/0.66  fof(f966,plain,(
% 2.03/0.66    $false | spl4_61),
% 2.03/0.66    inference(unit_resulting_resolution,[],[f134,f150,f939,f100])).
% 2.03/0.66  fof(f939,plain,(
% 2.03/0.66    ~r1_tarski(k1_relat_1(sK2),sK0) | spl4_61),
% 2.03/0.66    inference(avatar_component_clause,[],[f937])).
% 2.03/0.66  fof(f937,plain,(
% 2.03/0.66    spl4_61 <=> r1_tarski(k1_relat_1(sK2),sK0)),
% 2.03/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_61])])).
% 2.03/0.66  fof(f134,plain,(
% 2.03/0.66    v1_relat_1(sK2)),
% 2.03/0.66    inference(resolution,[],[f105,f75])).
% 2.03/0.66  fof(f952,plain,(
% 2.03/0.66    ~spl4_57 | spl4_60 | ~spl4_61 | ~spl4_58),
% 2.03/0.66    inference(avatar_split_clause,[],[f951,f909,f937,f933,f905])).
% 2.03/0.66  fof(f905,plain,(
% 2.03/0.66    spl4_57 <=> v1_relat_1(k6_partfun1(k1_relat_1(sK2)))),
% 2.03/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_57])])).
% 2.03/0.66  fof(f909,plain,(
% 2.03/0.66    spl4_58 <=> k6_partfun1(sK0) = k5_relat_1(k6_partfun1(k1_relat_1(sK2)),k6_partfun1(sK0))),
% 2.03/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_58])])).
% 2.03/0.66  fof(f951,plain,(
% 2.03/0.66    ~r1_tarski(k1_relat_1(sK2),sK0) | k6_partfun1(sK0) = k6_partfun1(k1_relat_1(sK2)) | ~v1_relat_1(k6_partfun1(k1_relat_1(sK2))) | ~spl4_58),
% 2.03/0.66    inference(forward_demodulation,[],[f928,f117])).
% 2.03/0.66  fof(f928,plain,(
% 2.03/0.66    k6_partfun1(sK0) = k6_partfun1(k1_relat_1(sK2)) | ~r1_tarski(k2_relat_1(k6_partfun1(k1_relat_1(sK2))),sK0) | ~v1_relat_1(k6_partfun1(k1_relat_1(sK2))) | ~spl4_58),
% 2.03/0.66    inference(superposition,[],[f122,f911])).
% 2.03/0.66  fof(f911,plain,(
% 2.03/0.66    k6_partfun1(sK0) = k5_relat_1(k6_partfun1(k1_relat_1(sK2)),k6_partfun1(sK0)) | ~spl4_58),
% 2.03/0.66    inference(avatar_component_clause,[],[f909])).
% 2.03/0.66  fof(f924,plain,(
% 2.03/0.66    spl4_57),
% 2.03/0.66    inference(avatar_contradiction_clause,[],[f919])).
% 2.03/0.66  fof(f919,plain,(
% 2.03/0.66    $false | spl4_57),
% 2.03/0.66    inference(unit_resulting_resolution,[],[f82,f907,f105])).
% 2.03/0.66  fof(f907,plain,(
% 2.03/0.66    ~v1_relat_1(k6_partfun1(k1_relat_1(sK2))) | spl4_57),
% 2.03/0.66    inference(avatar_component_clause,[],[f905])).
% 2.03/0.66  fof(f82,plain,(
% 2.03/0.66    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.03/0.66    inference(cnf_transformation,[],[f24])).
% 2.03/0.66  fof(f24,axiom,(
% 2.03/0.66    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 2.03/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 2.03/0.66  fof(f912,plain,(
% 2.03/0.66    ~spl4_57 | ~spl4_35 | ~spl4_3 | spl4_58 | ~spl4_33),
% 2.03/0.66    inference(avatar_split_clause,[],[f880,f676,f909,f297,f698,f905])).
% 2.03/0.66  fof(f880,plain,(
% 2.03/0.66    k6_partfun1(sK0) = k5_relat_1(k6_partfun1(k1_relat_1(sK2)),k6_partfun1(sK0)) | ~v1_relat_1(sK2) | ~v1_relat_1(sK3) | ~v1_relat_1(k6_partfun1(k1_relat_1(sK2))) | ~spl4_33),
% 2.03/0.66    inference(superposition,[],[f343,f678])).
% 2.03/0.66  fof(f343,plain,(
% 2.03/0.66    ( ! [X12,X11] : (k5_relat_1(X11,X12) = k5_relat_1(k6_partfun1(k1_relat_1(X11)),k5_relat_1(X11,X12)) | ~v1_relat_1(X11) | ~v1_relat_1(X12) | ~v1_relat_1(k6_partfun1(k1_relat_1(X11)))) )),
% 2.03/0.66    inference(duplicate_literal_removal,[],[f334])).
% 2.03/0.66  fof(f334,plain,(
% 2.03/0.66    ( ! [X12,X11] : (k5_relat_1(X11,X12) = k5_relat_1(k6_partfun1(k1_relat_1(X11)),k5_relat_1(X11,X12)) | ~v1_relat_1(X11) | ~v1_relat_1(X12) | ~v1_relat_1(k6_partfun1(k1_relat_1(X11))) | ~v1_relat_1(X11)) )),
% 2.03/0.66    inference(superposition,[],[f87,f119])).
% 2.03/0.66  fof(f710,plain,(
% 2.03/0.66    spl4_35),
% 2.03/0.66    inference(avatar_contradiction_clause,[],[f705])).
% 2.03/0.66  fof(f705,plain,(
% 2.03/0.66    $false | spl4_35),
% 2.03/0.66    inference(subsumption_resolution,[],[f135,f700])).
% 2.03/0.66  fof(f700,plain,(
% 2.03/0.66    ~v1_relat_1(sK3) | spl4_35),
% 2.03/0.66    inference(avatar_component_clause,[],[f698])).
% 2.03/0.66  fof(f687,plain,(
% 2.03/0.66    ~spl4_5 | ~spl4_28 | ~spl4_29 | ~spl4_1 | spl4_33 | ~spl4_22),
% 2.03/0.66    inference(avatar_split_clause,[],[f684,f558,f676,f230,f621,f617,f305])).
% 2.03/0.66  fof(f617,plain,(
% 2.03/0.66    spl4_28 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.03/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 2.03/0.66  fof(f621,plain,(
% 2.03/0.66    spl4_29 <=> v1_funct_1(sK3)),
% 2.03/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 2.03/0.66  fof(f230,plain,(
% 2.03/0.66    spl4_1 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.03/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 2.03/0.66  fof(f558,plain,(
% 2.03/0.66    spl4_22 <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)),
% 2.03/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 2.03/0.66  fof(f684,plain,(
% 2.03/0.66    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | ~spl4_22),
% 2.03/0.66    inference(superposition,[],[f112,f560])).
% 2.03/0.66  fof(f560,plain,(
% 2.03/0.66    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) | ~spl4_22),
% 2.03/0.66    inference(avatar_component_clause,[],[f558])).
% 2.03/0.66  fof(f112,plain,(
% 2.03/0.66    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 2.03/0.66    inference(cnf_transformation,[],[f61])).
% 2.03/0.66  fof(f61,plain,(
% 2.03/0.66    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.03/0.66    inference(flattening,[],[f60])).
% 2.03/0.66  fof(f60,plain,(
% 2.03/0.66    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.03/0.66    inference(ennf_transformation,[],[f25])).
% 2.03/0.66  fof(f25,axiom,(
% 2.03/0.66    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 2.03/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 2.03/0.66  fof(f673,plain,(
% 2.03/0.66    spl4_21),
% 2.03/0.66    inference(avatar_contradiction_clause,[],[f661])).
% 2.03/0.66  fof(f661,plain,(
% 2.03/0.66    $false | spl4_21),
% 2.03/0.66    inference(unit_resulting_resolution,[],[f73,f64,f66,f75,f556,f114])).
% 2.03/0.66  fof(f114,plain,(
% 2.03/0.66    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 2.03/0.66    inference(cnf_transformation,[],[f63])).
% 2.03/0.66  fof(f63,plain,(
% 2.03/0.66    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.03/0.66    inference(flattening,[],[f62])).
% 2.03/0.66  fof(f62,plain,(
% 2.03/0.66    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.03/0.66    inference(ennf_transformation,[],[f23])).
% 2.03/0.66  fof(f23,axiom,(
% 2.03/0.66    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 2.03/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 2.03/0.66  fof(f556,plain,(
% 2.03/0.66    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl4_21),
% 2.03/0.66    inference(avatar_component_clause,[],[f554])).
% 2.03/0.66  fof(f554,plain,(
% 2.03/0.66    spl4_21 <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.03/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 2.03/0.66  fof(f64,plain,(
% 2.03/0.66    v1_funct_1(sK3)),
% 2.03/0.66    inference(cnf_transformation,[],[f31])).
% 2.03/0.66  fof(f73,plain,(
% 2.03/0.66    v1_funct_1(sK2)),
% 2.03/0.66    inference(cnf_transformation,[],[f31])).
% 2.03/0.66  fof(f653,plain,(
% 2.03/0.66    spl4_29),
% 2.03/0.66    inference(avatar_contradiction_clause,[],[f652])).
% 2.03/0.66  fof(f652,plain,(
% 2.03/0.66    $false | spl4_29),
% 2.03/0.66    inference(subsumption_resolution,[],[f64,f623])).
% 2.03/0.66  fof(f623,plain,(
% 2.03/0.66    ~v1_funct_1(sK3) | spl4_29),
% 2.03/0.66    inference(avatar_component_clause,[],[f621])).
% 2.03/0.66  fof(f651,plain,(
% 2.03/0.66    spl4_28),
% 2.03/0.66    inference(avatar_contradiction_clause,[],[f647])).
% 2.03/0.66  fof(f647,plain,(
% 2.03/0.66    $false | spl4_28),
% 2.03/0.66    inference(subsumption_resolution,[],[f66,f619])).
% 2.03/0.66  fof(f619,plain,(
% 2.03/0.66    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl4_28),
% 2.03/0.66    inference(avatar_component_clause,[],[f617])).
% 2.03/0.66  fof(f561,plain,(
% 2.03/0.66    ~spl4_21 | spl4_22),
% 2.03/0.66    inference(avatar_split_clause,[],[f551,f558,f554])).
% 2.03/0.66  fof(f551,plain,(
% 2.03/0.66    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.03/0.66    inference(resolution,[],[f522,f68])).
% 2.03/0.66  fof(f68,plain,(
% 2.03/0.66    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 2.03/0.66    inference(cnf_transformation,[],[f31])).
% 2.03/0.66  fof(f522,plain,(
% 2.03/0.66    ( ! [X8,X7] : (~r2_relset_1(X8,X8,X7,k6_partfun1(X8)) | k6_partfun1(X8) = X7 | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X8,X8)))) )),
% 2.03/0.66    inference(resolution,[],[f111,f82])).
% 2.03/0.66  fof(f111,plain,(
% 2.03/0.66    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 = X3 | ~r2_relset_1(X0,X1,X2,X3)) )),
% 2.03/0.66    inference(cnf_transformation,[],[f59])).
% 2.03/0.66  fof(f59,plain,(
% 2.03/0.66    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.03/0.66    inference(flattening,[],[f58])).
% 2.03/0.66  fof(f58,plain,(
% 2.03/0.66    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.03/0.66    inference(ennf_transformation,[],[f22])).
% 2.03/0.66  fof(f22,axiom,(
% 2.03/0.66    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.03/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 2.03/0.66  fof(f329,plain,(
% 2.03/0.66    spl4_6),
% 2.03/0.66    inference(avatar_contradiction_clause,[],[f327])).
% 2.03/0.66  fof(f327,plain,(
% 2.03/0.66    $false | spl4_6),
% 2.03/0.66    inference(unit_resulting_resolution,[],[f134,f73,f311,f88])).
% 2.03/0.66  fof(f88,plain,(
% 2.03/0.66    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.03/0.66    inference(cnf_transformation,[],[f36])).
% 2.03/0.66  fof(f36,plain,(
% 2.03/0.66    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.03/0.66    inference(flattening,[],[f35])).
% 2.03/0.66  fof(f35,plain,(
% 2.03/0.66    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.03/0.66    inference(ennf_transformation,[],[f12])).
% 2.03/0.66  fof(f12,axiom,(
% 2.03/0.66    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.03/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 2.03/0.66  fof(f311,plain,(
% 2.03/0.66    ~v1_relat_1(k2_funct_1(sK2)) | spl4_6),
% 2.03/0.66    inference(avatar_component_clause,[],[f309])).
% 2.03/0.66  fof(f326,plain,(
% 2.03/0.66    spl4_5),
% 2.03/0.66    inference(avatar_contradiction_clause,[],[f325])).
% 2.03/0.66  fof(f325,plain,(
% 2.03/0.66    $false | spl4_5),
% 2.03/0.66    inference(subsumption_resolution,[],[f73,f307])).
% 2.03/0.66  fof(f307,plain,(
% 2.03/0.66    ~v1_funct_1(sK2) | spl4_5),
% 2.03/0.66    inference(avatar_component_clause,[],[f305])).
% 2.03/0.66  fof(f324,plain,(
% 2.03/0.66    spl4_4),
% 2.03/0.66    inference(avatar_contradiction_clause,[],[f323])).
% 2.03/0.66  fof(f323,plain,(
% 2.03/0.66    $false | spl4_4),
% 2.03/0.66    inference(subsumption_resolution,[],[f69,f303])).
% 2.03/0.66  fof(f303,plain,(
% 2.03/0.66    ~v2_funct_1(sK2) | spl4_4),
% 2.03/0.66    inference(avatar_component_clause,[],[f301])).
% 2.03/0.66  fof(f69,plain,(
% 2.03/0.66    v2_funct_1(sK2)),
% 2.03/0.66    inference(cnf_transformation,[],[f31])).
% 2.03/0.66  fof(f322,plain,(
% 2.03/0.66    spl4_3),
% 2.03/0.66    inference(avatar_contradiction_clause,[],[f317])).
% 2.03/0.66  fof(f317,plain,(
% 2.03/0.66    $false | spl4_3),
% 2.03/0.66    inference(subsumption_resolution,[],[f134,f299])).
% 2.03/0.66  fof(f299,plain,(
% 2.03/0.66    ~v1_relat_1(sK2) | spl4_3),
% 2.03/0.66    inference(avatar_component_clause,[],[f297])).
% 2.03/0.66  fof(f243,plain,(
% 2.03/0.66    spl4_1),
% 2.03/0.66    inference(avatar_contradiction_clause,[],[f239])).
% 2.03/0.66  fof(f239,plain,(
% 2.03/0.66    $false | spl4_1),
% 2.03/0.66    inference(subsumption_resolution,[],[f75,f232])).
% 2.03/0.66  fof(f232,plain,(
% 2.03/0.66    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl4_1),
% 2.03/0.66    inference(avatar_component_clause,[],[f230])).
% 2.03/0.66  fof(f238,plain,(
% 2.03/0.66    ~spl4_1 | spl4_2),
% 2.03/0.66    inference(avatar_split_clause,[],[f228,f234,f230])).
% 2.03/0.66  fof(f228,plain,(
% 2.03/0.66    sK1 = k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.03/0.66    inference(superposition,[],[f67,f106])).
% 2.03/0.66  fof(f106,plain,(
% 2.03/0.66    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.03/0.66    inference(cnf_transformation,[],[f54])).
% 2.03/0.66  fof(f54,plain,(
% 2.03/0.66    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.03/0.66    inference(ennf_transformation,[],[f21])).
% 2.03/0.66  fof(f21,axiom,(
% 2.03/0.66    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 2.03/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 2.03/0.66  fof(f67,plain,(
% 2.03/0.66    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 2.03/0.66    inference(cnf_transformation,[],[f31])).
% 2.03/0.66  % SZS output end Proof for theBenchmark
% 2.03/0.66  % (23723)------------------------------
% 2.03/0.66  % (23723)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.03/0.66  % (23723)Termination reason: Refutation
% 2.03/0.66  
% 2.03/0.66  % (23723)Memory used [KB]: 7675
% 2.03/0.66  % (23723)Time elapsed: 0.234 s
% 2.03/0.66  % (23723)------------------------------
% 2.03/0.66  % (23723)------------------------------
% 2.03/0.66  % (23709)Success in time 0.303 s
%------------------------------------------------------------------------------
