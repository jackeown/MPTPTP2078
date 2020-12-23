%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:33 EST 2020

% Result     : Theorem 1.38s
% Output     : Refutation 1.38s
% Verified   : 
% Statistics : Number of formulae       :  152 ( 327 expanded)
%              Number of leaves         :   34 ( 127 expanded)
%              Depth                    :   13
%              Number of atoms          :  614 (1979 expanded)
%              Number of equality atoms :  146 ( 586 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f821,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f105,f110,f115,f120,f125,f130,f135,f140,f145,f150,f155,f160,f171,f187,f254,f276,f644,f794])).

fof(f794,plain,
    ( ~ spl4_1
    | ~ spl4_3
    | spl4_4
    | spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_13
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_16
    | ~ spl4_39 ),
    inference(avatar_contradiction_clause,[],[f793])).

fof(f793,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_3
    | spl4_4
    | spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_13
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_16
    | ~ spl4_39 ),
    inference(subsumption_resolution,[],[f792,f139])).

fof(f139,plain,
    ( k2_funct_1(sK2) != sK3
    | spl4_8 ),
    inference(avatar_component_clause,[],[f137])).

fof(f137,plain,
    ( spl4_8
  <=> k2_funct_1(sK2) = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f792,plain,
    ( k2_funct_1(sK2) = sK3
    | ~ spl4_1
    | ~ spl4_3
    | spl4_4
    | spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_13
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_16
    | ~ spl4_39 ),
    inference(backward_demodulation,[],[f383,f761])).

fof(f761,plain,
    ( sK3 = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0))
    | ~ spl4_1
    | ~ spl4_3
    | spl4_4
    | spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_13
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_16
    | ~ spl4_39 ),
    inference(backward_demodulation,[],[f402,f705])).

fof(f705,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl4_16
    | ~ spl4_39 ),
    inference(unit_resulting_resolution,[],[f61,f275,f643,f83])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f643,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_39 ),
    inference(avatar_component_clause,[],[f641])).

fof(f641,plain,
    ( spl4_39
  <=> m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f275,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0))
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f273])).

fof(f273,plain,
    ( spl4_16
  <=> r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f61,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f402,plain,
    ( sK3 = k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,sK3))
    | ~ spl4_1
    | ~ spl4_3
    | spl4_4
    | spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_13
    | ~ spl4_14
    | ~ spl4_15 ),
    inference(forward_demodulation,[],[f401,f238])).

fof(f238,plain,
    ( sK3 = k5_relat_1(k6_partfun1(sK1),sK3)
    | spl4_4
    | ~ spl4_7
    | ~ spl4_10
    | ~ spl4_14 ),
    inference(backward_demodulation,[],[f218,f237])).

fof(f237,plain,
    ( sK1 = k1_relat_1(sK3)
    | spl4_4
    | ~ spl4_7
    | ~ spl4_10 ),
    inference(backward_demodulation,[],[f192,f233])).

fof(f233,plain,
    ( sK1 = k1_relset_1(sK1,sK0,sK3)
    | spl4_4
    | ~ spl4_7
    | ~ spl4_10 ),
    inference(unit_resulting_resolution,[],[f119,f134,f149,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
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
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f149,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl4_10
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f134,plain,
    ( v1_funct_2(sK3,sK1,sK0)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl4_7
  <=> v1_funct_2(sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f119,plain,
    ( k1_xboole_0 != sK0
    | spl4_4 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl4_4
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f192,plain,
    ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3)
    | ~ spl4_10 ),
    inference(unit_resulting_resolution,[],[f149,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f218,plain,
    ( sK3 = k5_relat_1(k6_partfun1(k1_relat_1(sK3)),sK3)
    | ~ spl4_14 ),
    inference(unit_resulting_resolution,[],[f186,f91])).

fof(f91,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0 ) ),
    inference(definition_unfolding,[],[f65,f59])).

fof(f59,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f65,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).

fof(f186,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f184])).

fof(f184,plain,
    ( spl4_14
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f401,plain,
    ( k5_relat_1(k6_partfun1(sK1),sK3) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,sK3))
    | ~ spl4_1
    | ~ spl4_3
    | spl4_5
    | ~ spl4_6
    | ~ spl4_9
    | ~ spl4_11
    | ~ spl4_13
    | ~ spl4_14
    | ~ spl4_15 ),
    inference(forward_demodulation,[],[f350,f302])).

fof(f302,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | ~ spl4_1
    | ~ spl4_3
    | spl4_5
    | ~ spl4_6
    | ~ spl4_9
    | ~ spl4_11 ),
    inference(unit_resulting_resolution,[],[f104,f114,f124,f129,f144,f154,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | k1_xboole_0 = X1
      | k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
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
       => ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
            & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).

fof(f154,plain,
    ( sK1 = k2_relset_1(sK0,sK1,sK2)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f152])).

fof(f152,plain,
    ( spl4_11
  <=> sK1 = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f144,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl4_9
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f129,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl4_6
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f124,plain,
    ( k1_xboole_0 != sK1
    | spl4_5 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl4_5
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f114,plain,
    ( v2_funct_1(sK2)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl4_3
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f104,plain,
    ( v1_funct_1(sK2)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl4_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f350,plain,
    ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),sK3) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,sK3))
    | ~ spl4_13
    | ~ spl4_14
    | ~ spl4_15 ),
    inference(unit_resulting_resolution,[],[f186,f170,f253,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

fof(f253,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f251])).

fof(f251,plain,
    ( spl4_15
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f170,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f168])).

fof(f168,plain,
    ( spl4_13
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f383,plain,
    ( k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0))
    | ~ spl4_1
    | ~ spl4_3
    | spl4_5
    | ~ spl4_6
    | ~ spl4_9
    | ~ spl4_13
    | ~ spl4_15 ),
    inference(forward_demodulation,[],[f376,f242])).

fof(f242,plain,
    ( sK0 = k2_relat_1(k2_funct_1(sK2))
    | ~ spl4_1
    | ~ spl4_3
    | spl4_5
    | ~ spl4_6
    | ~ spl4_9
    | ~ spl4_13 ),
    inference(backward_demodulation,[],[f190,f239])).

fof(f239,plain,
    ( sK0 = k1_relat_1(sK2)
    | spl4_5
    | ~ spl4_6
    | ~ spl4_9 ),
    inference(backward_demodulation,[],[f191,f232])).

fof(f232,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | spl4_5
    | ~ spl4_6
    | ~ spl4_9 ),
    inference(unit_resulting_resolution,[],[f124,f129,f144,f75])).

fof(f191,plain,
    ( k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)
    | ~ spl4_9 ),
    inference(unit_resulting_resolution,[],[f144,f74])).

fof(f190,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f189,f170])).

fof(f189,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl4_1
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f188,f104])).

fof(f188,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_3 ),
    inference(resolution,[],[f70,f114])).

fof(f70,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f376,plain,
    ( k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(k2_relat_1(k2_funct_1(sK2))))
    | ~ spl4_15 ),
    inference(unit_resulting_resolution,[],[f253,f90])).

fof(f90,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 ) ),
    inference(definition_unfolding,[],[f64,f59])).

fof(f64,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

fof(f644,plain,
    ( spl4_39
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_9
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f295,f147,f142,f107,f102,f641])).

fof(f107,plain,
    ( spl4_2
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f295,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_9
    | ~ spl4_10 ),
    inference(forward_demodulation,[],[f284,f261])).

fof(f261,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_9
    | ~ spl4_10 ),
    inference(unit_resulting_resolution,[],[f104,f109,f144,f149,f85])).

fof(f85,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
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
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f109,plain,
    ( v1_funct_1(sK3)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f107])).

fof(f284,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_9
    | ~ spl4_10 ),
    inference(unit_resulting_resolution,[],[f104,f109,f144,f149,f87])).

fof(f87,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
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
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f276,plain,
    ( spl4_16
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f269,f157,f147,f142,f107,f102,f273])).

fof(f157,plain,
    ( spl4_12
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f269,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12 ),
    inference(backward_demodulation,[],[f159,f261])).

fof(f159,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f157])).

fof(f254,plain,
    ( spl4_15
    | ~ spl4_1
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f202,f168,f102,f251])).

fof(f202,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ spl4_1
    | ~ spl4_13 ),
    inference(unit_resulting_resolution,[],[f104,f170,f67])).

fof(f67,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f187,plain,
    ( spl4_14
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f162,f147,f184])).

fof(f162,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_10 ),
    inference(unit_resulting_resolution,[],[f149,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f171,plain,
    ( spl4_13
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f161,f142,f168])).

fof(f161,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_9 ),
    inference(unit_resulting_resolution,[],[f144,f73])).

fof(f160,plain,(
    spl4_12 ),
    inference(avatar_split_clause,[],[f54,f157])).

fof(f54,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,
    ( k2_funct_1(sK2) != sK3
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & v2_funct_1(sK2)
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & sK1 = k2_relset_1(sK0,sK1,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f43,f42])).

fof(f42,plain,
    ( ? [X0,X1,X2] :
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
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( k2_funct_1(sK2) != X3
          & k1_xboole_0 != sK1
          & k1_xboole_0 != sK0
          & v2_funct_1(sK2)
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
          & sK1 = k2_relset_1(sK0,sK1,sK2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
          & v1_funct_2(X3,sK1,sK0)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X3] :
        ( k2_funct_1(sK2) != X3
        & k1_xboole_0 != sK1
        & k1_xboole_0 != sK0
        & v2_funct_1(sK2)
        & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
        & sK1 = k2_relset_1(sK0,sK1,sK2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        & v1_funct_2(X3,sK1,sK0)
        & v1_funct_1(X3) )
   => ( k2_funct_1(sK2) != sK3
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & v2_funct_1(sK2)
      & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
      & sK1 = k2_relset_1(sK0,sK1,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      & v1_funct_2(sK3,sK1,sK0)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

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
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
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
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
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

fof(f155,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f53,f152])).

fof(f53,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f150,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f52,f147])).

fof(f52,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f44])).

fof(f145,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f49,f142])).

fof(f49,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f44])).

fof(f140,plain,(
    ~ spl4_8 ),
    inference(avatar_split_clause,[],[f58,f137])).

fof(f58,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f44])).

fof(f135,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f51,f132])).

fof(f51,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f130,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f48,f127])).

fof(f48,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f125,plain,(
    ~ spl4_5 ),
    inference(avatar_split_clause,[],[f57,f122])).

fof(f57,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f44])).

fof(f120,plain,(
    ~ spl4_4 ),
    inference(avatar_split_clause,[],[f56,f117])).

fof(f56,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f44])).

fof(f115,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f55,f112])).

fof(f55,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f110,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f50,f107])).

fof(f50,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f105,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f47,f102])).

fof(f47,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f44])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n006.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 11:11:52 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.22/0.52  % (16517)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.52  % (16540)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.12/0.53  % (16532)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.12/0.53  % (16516)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.12/0.54  % (16535)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.12/0.54  % (16514)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.12/0.55  % (16513)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.38/0.55  % (16527)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.38/0.55  % (16526)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.38/0.55  % (16539)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.38/0.55  % (16541)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.38/0.55  % (16512)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.38/0.55  % (16515)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.38/0.55  % (16519)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.38/0.55  % (16518)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.38/0.56  % (16533)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.38/0.56  % (16522)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.38/0.56  % (16528)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.38/0.56  % (16523)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.38/0.56  % (16534)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.38/0.56  % (16528)Refutation not found, incomplete strategy% (16528)------------------------------
% 1.38/0.56  % (16528)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.56  % (16528)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.56  
% 1.38/0.56  % (16528)Memory used [KB]: 10746
% 1.38/0.56  % (16528)Time elapsed: 0.147 s
% 1.38/0.56  % (16528)------------------------------
% 1.38/0.56  % (16528)------------------------------
% 1.38/0.56  % (16538)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.38/0.56  % (16525)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.38/0.57  % (16520)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.38/0.57  % (16524)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.38/0.57  % (16529)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.38/0.57  % (16521)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.38/0.57  % (16537)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.38/0.57  % (16536)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.38/0.57  % (16531)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.38/0.57  % (16530)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.38/0.60  % (16532)Refutation found. Thanks to Tanya!
% 1.38/0.60  % SZS status Theorem for theBenchmark
% 1.38/0.60  % SZS output start Proof for theBenchmark
% 1.38/0.60  fof(f821,plain,(
% 1.38/0.60    $false),
% 1.38/0.60    inference(avatar_sat_refutation,[],[f105,f110,f115,f120,f125,f130,f135,f140,f145,f150,f155,f160,f171,f187,f254,f276,f644,f794])).
% 1.38/0.60  fof(f794,plain,(
% 1.38/0.60    ~spl4_1 | ~spl4_3 | spl4_4 | spl4_5 | ~spl4_6 | ~spl4_7 | spl4_8 | ~spl4_9 | ~spl4_10 | ~spl4_11 | ~spl4_13 | ~spl4_14 | ~spl4_15 | ~spl4_16 | ~spl4_39),
% 1.38/0.60    inference(avatar_contradiction_clause,[],[f793])).
% 1.38/0.60  fof(f793,plain,(
% 1.38/0.60    $false | (~spl4_1 | ~spl4_3 | spl4_4 | spl4_5 | ~spl4_6 | ~spl4_7 | spl4_8 | ~spl4_9 | ~spl4_10 | ~spl4_11 | ~spl4_13 | ~spl4_14 | ~spl4_15 | ~spl4_16 | ~spl4_39)),
% 1.38/0.60    inference(subsumption_resolution,[],[f792,f139])).
% 1.38/0.60  fof(f139,plain,(
% 1.38/0.60    k2_funct_1(sK2) != sK3 | spl4_8),
% 1.38/0.60    inference(avatar_component_clause,[],[f137])).
% 1.38/0.60  fof(f137,plain,(
% 1.38/0.60    spl4_8 <=> k2_funct_1(sK2) = sK3),
% 1.38/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.38/0.60  fof(f792,plain,(
% 1.38/0.60    k2_funct_1(sK2) = sK3 | (~spl4_1 | ~spl4_3 | spl4_4 | spl4_5 | ~spl4_6 | ~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_11 | ~spl4_13 | ~spl4_14 | ~spl4_15 | ~spl4_16 | ~spl4_39)),
% 1.38/0.60    inference(backward_demodulation,[],[f383,f761])).
% 1.38/0.60  fof(f761,plain,(
% 1.38/0.60    sK3 = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) | (~spl4_1 | ~spl4_3 | spl4_4 | spl4_5 | ~spl4_6 | ~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_11 | ~spl4_13 | ~spl4_14 | ~spl4_15 | ~spl4_16 | ~spl4_39)),
% 1.38/0.60    inference(backward_demodulation,[],[f402,f705])).
% 1.38/0.60  fof(f705,plain,(
% 1.38/0.60    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | (~spl4_16 | ~spl4_39)),
% 1.38/0.60    inference(unit_resulting_resolution,[],[f61,f275,f643,f83])).
% 1.38/0.60  fof(f83,plain,(
% 1.38/0.60    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.38/0.60    inference(cnf_transformation,[],[f46])).
% 1.38/0.60  fof(f46,plain,(
% 1.38/0.60    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.38/0.60    inference(nnf_transformation,[],[f37])).
% 1.38/0.60  fof(f37,plain,(
% 1.38/0.60    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.38/0.60    inference(flattening,[],[f36])).
% 1.38/0.60  fof(f36,plain,(
% 1.38/0.60    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.38/0.60    inference(ennf_transformation,[],[f10])).
% 1.38/0.60  fof(f10,axiom,(
% 1.38/0.60    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.38/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.38/0.60  fof(f643,plain,(
% 1.38/0.60    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl4_39),
% 1.38/0.60    inference(avatar_component_clause,[],[f641])).
% 1.38/0.60  fof(f641,plain,(
% 1.38/0.60    spl4_39 <=> m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.38/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).
% 1.38/0.60  fof(f275,plain,(
% 1.38/0.60    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0)) | ~spl4_16),
% 1.38/0.60    inference(avatar_component_clause,[],[f273])).
% 1.38/0.60  fof(f273,plain,(
% 1.38/0.60    spl4_16 <=> r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0))),
% 1.38/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 1.38/0.60  fof(f61,plain,(
% 1.38/0.60    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.38/0.60    inference(cnf_transformation,[],[f13])).
% 1.38/0.60  fof(f13,axiom,(
% 1.38/0.60    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 1.38/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 1.38/0.60  fof(f402,plain,(
% 1.38/0.60    sK3 = k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,sK3)) | (~spl4_1 | ~spl4_3 | spl4_4 | spl4_5 | ~spl4_6 | ~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_11 | ~spl4_13 | ~spl4_14 | ~spl4_15)),
% 1.38/0.60    inference(forward_demodulation,[],[f401,f238])).
% 1.38/0.60  fof(f238,plain,(
% 1.38/0.60    sK3 = k5_relat_1(k6_partfun1(sK1),sK3) | (spl4_4 | ~spl4_7 | ~spl4_10 | ~spl4_14)),
% 1.38/0.60    inference(backward_demodulation,[],[f218,f237])).
% 1.38/0.60  fof(f237,plain,(
% 1.38/0.60    sK1 = k1_relat_1(sK3) | (spl4_4 | ~spl4_7 | ~spl4_10)),
% 1.38/0.60    inference(backward_demodulation,[],[f192,f233])).
% 1.38/0.60  fof(f233,plain,(
% 1.38/0.60    sK1 = k1_relset_1(sK1,sK0,sK3) | (spl4_4 | ~spl4_7 | ~spl4_10)),
% 1.38/0.60    inference(unit_resulting_resolution,[],[f119,f134,f149,f75])).
% 1.38/0.60  fof(f75,plain,(
% 1.38/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 1.38/0.60    inference(cnf_transformation,[],[f45])).
% 1.38/0.60  fof(f45,plain,(
% 1.38/0.60    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.38/0.60    inference(nnf_transformation,[],[f33])).
% 1.38/0.60  fof(f33,plain,(
% 1.38/0.60    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.38/0.60    inference(flattening,[],[f32])).
% 1.38/0.60  fof(f32,plain,(
% 1.38/0.60    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.38/0.60    inference(ennf_transformation,[],[f11])).
% 1.38/0.60  fof(f11,axiom,(
% 1.38/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.38/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.38/0.60  fof(f149,plain,(
% 1.38/0.60    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_10),
% 1.38/0.60    inference(avatar_component_clause,[],[f147])).
% 1.38/0.60  fof(f147,plain,(
% 1.38/0.60    spl4_10 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.38/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 1.38/0.60  fof(f134,plain,(
% 1.38/0.60    v1_funct_2(sK3,sK1,sK0) | ~spl4_7),
% 1.38/0.60    inference(avatar_component_clause,[],[f132])).
% 1.38/0.60  fof(f132,plain,(
% 1.38/0.60    spl4_7 <=> v1_funct_2(sK3,sK1,sK0)),
% 1.38/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.38/0.60  fof(f119,plain,(
% 1.38/0.60    k1_xboole_0 != sK0 | spl4_4),
% 1.38/0.60    inference(avatar_component_clause,[],[f117])).
% 1.38/0.60  fof(f117,plain,(
% 1.38/0.60    spl4_4 <=> k1_xboole_0 = sK0),
% 1.38/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.38/0.60  fof(f192,plain,(
% 1.38/0.60    k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) | ~spl4_10),
% 1.38/0.60    inference(unit_resulting_resolution,[],[f149,f74])).
% 1.38/0.60  fof(f74,plain,(
% 1.38/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.38/0.60    inference(cnf_transformation,[],[f31])).
% 1.38/0.60  fof(f31,plain,(
% 1.38/0.60    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.38/0.60    inference(ennf_transformation,[],[f9])).
% 1.38/0.60  fof(f9,axiom,(
% 1.38/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.38/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.38/0.60  fof(f218,plain,(
% 1.38/0.60    sK3 = k5_relat_1(k6_partfun1(k1_relat_1(sK3)),sK3) | ~spl4_14),
% 1.38/0.60    inference(unit_resulting_resolution,[],[f186,f91])).
% 1.38/0.60  fof(f91,plain,(
% 1.38/0.60    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0) )),
% 1.38/0.60    inference(definition_unfolding,[],[f65,f59])).
% 1.38/0.60  fof(f59,plain,(
% 1.38/0.60    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.38/0.60    inference(cnf_transformation,[],[f15])).
% 1.38/0.60  fof(f15,axiom,(
% 1.38/0.60    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.38/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.38/0.60  fof(f65,plain,(
% 1.38/0.60    ( ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) )),
% 1.38/0.60    inference(cnf_transformation,[],[f22])).
% 1.38/0.60  fof(f22,plain,(
% 1.38/0.60    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 1.38/0.60    inference(ennf_transformation,[],[f3])).
% 1.38/0.60  fof(f3,axiom,(
% 1.38/0.60    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 1.38/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).
% 1.38/0.60  fof(f186,plain,(
% 1.38/0.60    v1_relat_1(sK3) | ~spl4_14),
% 1.38/0.60    inference(avatar_component_clause,[],[f184])).
% 1.38/0.60  fof(f184,plain,(
% 1.38/0.60    spl4_14 <=> v1_relat_1(sK3)),
% 1.38/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 1.38/0.60  fof(f401,plain,(
% 1.38/0.60    k5_relat_1(k6_partfun1(sK1),sK3) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,sK3)) | (~spl4_1 | ~spl4_3 | spl4_5 | ~spl4_6 | ~spl4_9 | ~spl4_11 | ~spl4_13 | ~spl4_14 | ~spl4_15)),
% 1.38/0.60    inference(forward_demodulation,[],[f350,f302])).
% 1.38/0.60  fof(f302,plain,(
% 1.38/0.60    k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) | (~spl4_1 | ~spl4_3 | spl4_5 | ~spl4_6 | ~spl4_9 | ~spl4_11)),
% 1.38/0.60    inference(unit_resulting_resolution,[],[f104,f114,f124,f129,f144,f154,f82])).
% 1.38/0.60  fof(f82,plain,(
% 1.38/0.60    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | k1_xboole_0 = X1 | k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.38/0.60    inference(cnf_transformation,[],[f35])).
% 1.38/0.60  fof(f35,plain,(
% 1.38/0.60    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.38/0.60    inference(flattening,[],[f34])).
% 1.38/0.60  fof(f34,plain,(
% 1.38/0.60    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.38/0.60    inference(ennf_transformation,[],[f16])).
% 1.38/0.60  fof(f16,axiom,(
% 1.38/0.60    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 1.38/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).
% 1.38/0.60  fof(f154,plain,(
% 1.38/0.60    sK1 = k2_relset_1(sK0,sK1,sK2) | ~spl4_11),
% 1.38/0.60    inference(avatar_component_clause,[],[f152])).
% 1.38/0.60  fof(f152,plain,(
% 1.38/0.60    spl4_11 <=> sK1 = k2_relset_1(sK0,sK1,sK2)),
% 1.38/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 1.38/0.60  fof(f144,plain,(
% 1.38/0.60    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_9),
% 1.38/0.60    inference(avatar_component_clause,[],[f142])).
% 1.38/0.60  fof(f142,plain,(
% 1.38/0.60    spl4_9 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.38/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 1.38/0.60  fof(f129,plain,(
% 1.38/0.60    v1_funct_2(sK2,sK0,sK1) | ~spl4_6),
% 1.38/0.60    inference(avatar_component_clause,[],[f127])).
% 1.38/0.60  fof(f127,plain,(
% 1.38/0.60    spl4_6 <=> v1_funct_2(sK2,sK0,sK1)),
% 1.38/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.38/0.60  fof(f124,plain,(
% 1.38/0.60    k1_xboole_0 != sK1 | spl4_5),
% 1.38/0.60    inference(avatar_component_clause,[],[f122])).
% 1.38/0.60  fof(f122,plain,(
% 1.38/0.60    spl4_5 <=> k1_xboole_0 = sK1),
% 1.38/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.38/0.60  fof(f114,plain,(
% 1.38/0.60    v2_funct_1(sK2) | ~spl4_3),
% 1.38/0.60    inference(avatar_component_clause,[],[f112])).
% 1.38/0.60  fof(f112,plain,(
% 1.38/0.60    spl4_3 <=> v2_funct_1(sK2)),
% 1.38/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.38/0.60  fof(f104,plain,(
% 1.38/0.60    v1_funct_1(sK2) | ~spl4_1),
% 1.38/0.60    inference(avatar_component_clause,[],[f102])).
% 1.38/0.60  fof(f102,plain,(
% 1.38/0.60    spl4_1 <=> v1_funct_1(sK2)),
% 1.38/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.38/0.60  fof(f350,plain,(
% 1.38/0.60    k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),sK3) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,sK3)) | (~spl4_13 | ~spl4_14 | ~spl4_15)),
% 1.38/0.60    inference(unit_resulting_resolution,[],[f186,f170,f253,f66])).
% 1.38/0.60  fof(f66,plain,(
% 1.38/0.60    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.38/0.60    inference(cnf_transformation,[],[f23])).
% 1.38/0.60  fof(f23,plain,(
% 1.38/0.60    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.38/0.60    inference(ennf_transformation,[],[f1])).
% 1.38/0.60  fof(f1,axiom,(
% 1.38/0.60    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 1.38/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).
% 1.38/0.60  fof(f253,plain,(
% 1.38/0.60    v1_relat_1(k2_funct_1(sK2)) | ~spl4_15),
% 1.38/0.60    inference(avatar_component_clause,[],[f251])).
% 1.38/0.60  fof(f251,plain,(
% 1.38/0.60    spl4_15 <=> v1_relat_1(k2_funct_1(sK2))),
% 1.38/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 1.38/0.60  fof(f170,plain,(
% 1.38/0.60    v1_relat_1(sK2) | ~spl4_13),
% 1.38/0.60    inference(avatar_component_clause,[],[f168])).
% 1.38/0.60  fof(f168,plain,(
% 1.38/0.60    spl4_13 <=> v1_relat_1(sK2)),
% 1.38/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 1.38/0.60  fof(f383,plain,(
% 1.38/0.60    k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) | (~spl4_1 | ~spl4_3 | spl4_5 | ~spl4_6 | ~spl4_9 | ~spl4_13 | ~spl4_15)),
% 1.38/0.60    inference(forward_demodulation,[],[f376,f242])).
% 1.38/0.60  fof(f242,plain,(
% 1.38/0.60    sK0 = k2_relat_1(k2_funct_1(sK2)) | (~spl4_1 | ~spl4_3 | spl4_5 | ~spl4_6 | ~spl4_9 | ~spl4_13)),
% 1.38/0.60    inference(backward_demodulation,[],[f190,f239])).
% 1.38/0.60  fof(f239,plain,(
% 1.38/0.60    sK0 = k1_relat_1(sK2) | (spl4_5 | ~spl4_6 | ~spl4_9)),
% 1.38/0.60    inference(backward_demodulation,[],[f191,f232])).
% 1.38/0.60  fof(f232,plain,(
% 1.38/0.60    sK0 = k1_relset_1(sK0,sK1,sK2) | (spl4_5 | ~spl4_6 | ~spl4_9)),
% 1.38/0.60    inference(unit_resulting_resolution,[],[f124,f129,f144,f75])).
% 1.38/0.60  fof(f191,plain,(
% 1.38/0.60    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) | ~spl4_9),
% 1.38/0.60    inference(unit_resulting_resolution,[],[f144,f74])).
% 1.38/0.60  fof(f190,plain,(
% 1.38/0.60    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | (~spl4_1 | ~spl4_3 | ~spl4_13)),
% 1.38/0.60    inference(subsumption_resolution,[],[f189,f170])).
% 1.38/0.60  fof(f189,plain,(
% 1.38/0.60    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2) | (~spl4_1 | ~spl4_3)),
% 1.38/0.60    inference(subsumption_resolution,[],[f188,f104])).
% 1.38/0.60  fof(f188,plain,(
% 1.38/0.60    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl4_3),
% 1.38/0.60    inference(resolution,[],[f70,f114])).
% 1.38/0.60  fof(f70,plain,(
% 1.38/0.60    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.38/0.60    inference(cnf_transformation,[],[f27])).
% 1.38/0.60  fof(f27,plain,(
% 1.38/0.60    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.38/0.60    inference(flattening,[],[f26])).
% 1.38/0.60  fof(f26,plain,(
% 1.38/0.60    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.38/0.60    inference(ennf_transformation,[],[f6])).
% 1.38/0.60  fof(f6,axiom,(
% 1.38/0.60    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 1.38/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 1.38/0.60  fof(f376,plain,(
% 1.38/0.60    k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(k2_relat_1(k2_funct_1(sK2)))) | ~spl4_15),
% 1.38/0.60    inference(unit_resulting_resolution,[],[f253,f90])).
% 1.38/0.60  fof(f90,plain,(
% 1.38/0.60    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0) )),
% 1.38/0.60    inference(definition_unfolding,[],[f64,f59])).
% 1.38/0.60  fof(f64,plain,(
% 1.38/0.60    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 1.38/0.60    inference(cnf_transformation,[],[f21])).
% 1.38/0.60  fof(f21,plain,(
% 1.38/0.60    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 1.38/0.60    inference(ennf_transformation,[],[f4])).
% 1.38/0.60  fof(f4,axiom,(
% 1.38/0.60    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 1.38/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).
% 1.38/0.60  fof(f644,plain,(
% 1.38/0.60    spl4_39 | ~spl4_1 | ~spl4_2 | ~spl4_9 | ~spl4_10),
% 1.38/0.60    inference(avatar_split_clause,[],[f295,f147,f142,f107,f102,f641])).
% 1.38/0.60  fof(f107,plain,(
% 1.38/0.60    spl4_2 <=> v1_funct_1(sK3)),
% 1.38/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.38/0.60  fof(f295,plain,(
% 1.38/0.60    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | (~spl4_1 | ~spl4_2 | ~spl4_9 | ~spl4_10)),
% 1.38/0.60    inference(forward_demodulation,[],[f284,f261])).
% 1.38/0.60  fof(f261,plain,(
% 1.38/0.60    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) | (~spl4_1 | ~spl4_2 | ~spl4_9 | ~spl4_10)),
% 1.38/0.60    inference(unit_resulting_resolution,[],[f104,f109,f144,f149,f85])).
% 1.38/0.60  fof(f85,plain,(
% 1.38/0.60    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.38/0.60    inference(cnf_transformation,[],[f39])).
% 1.38/0.60  fof(f39,plain,(
% 1.38/0.60    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.38/0.60    inference(flattening,[],[f38])).
% 1.38/0.60  fof(f38,plain,(
% 1.38/0.60    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.38/0.60    inference(ennf_transformation,[],[f14])).
% 1.38/0.60  fof(f14,axiom,(
% 1.38/0.60    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.38/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.38/0.60  fof(f109,plain,(
% 1.38/0.60    v1_funct_1(sK3) | ~spl4_2),
% 1.38/0.60    inference(avatar_component_clause,[],[f107])).
% 1.38/0.60  fof(f284,plain,(
% 1.38/0.60    m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | (~spl4_1 | ~spl4_2 | ~spl4_9 | ~spl4_10)),
% 1.38/0.60    inference(unit_resulting_resolution,[],[f104,f109,f144,f149,f87])).
% 1.38/0.60  fof(f87,plain,(
% 1.38/0.60    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.38/0.60    inference(cnf_transformation,[],[f41])).
% 1.38/0.60  fof(f41,plain,(
% 1.38/0.60    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.38/0.60    inference(flattening,[],[f40])).
% 1.38/0.60  fof(f40,plain,(
% 1.38/0.60    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.38/0.60    inference(ennf_transformation,[],[f12])).
% 1.38/0.60  fof(f12,axiom,(
% 1.38/0.60    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.38/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.38/0.60  fof(f276,plain,(
% 1.38/0.60    spl4_16 | ~spl4_1 | ~spl4_2 | ~spl4_9 | ~spl4_10 | ~spl4_12),
% 1.38/0.60    inference(avatar_split_clause,[],[f269,f157,f147,f142,f107,f102,f273])).
% 1.38/0.60  fof(f157,plain,(
% 1.38/0.60    spl4_12 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.38/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 1.38/0.60  fof(f269,plain,(
% 1.38/0.60    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0)) | (~spl4_1 | ~spl4_2 | ~spl4_9 | ~spl4_10 | ~spl4_12)),
% 1.38/0.60    inference(backward_demodulation,[],[f159,f261])).
% 1.38/0.60  fof(f159,plain,(
% 1.38/0.60    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) | ~spl4_12),
% 1.38/0.60    inference(avatar_component_clause,[],[f157])).
% 1.38/0.60  fof(f254,plain,(
% 1.38/0.60    spl4_15 | ~spl4_1 | ~spl4_13),
% 1.38/0.60    inference(avatar_split_clause,[],[f202,f168,f102,f251])).
% 1.38/0.60  fof(f202,plain,(
% 1.38/0.60    v1_relat_1(k2_funct_1(sK2)) | (~spl4_1 | ~spl4_13)),
% 1.38/0.60    inference(unit_resulting_resolution,[],[f104,f170,f67])).
% 1.38/0.60  fof(f67,plain,(
% 1.38/0.60    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.38/0.60    inference(cnf_transformation,[],[f25])).
% 1.38/0.60  fof(f25,plain,(
% 1.38/0.60    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.38/0.60    inference(flattening,[],[f24])).
% 1.38/0.60  fof(f24,plain,(
% 1.38/0.60    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.38/0.60    inference(ennf_transformation,[],[f5])).
% 1.38/0.60  fof(f5,axiom,(
% 1.38/0.60    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.38/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 1.38/0.60  fof(f187,plain,(
% 1.38/0.60    spl4_14 | ~spl4_10),
% 1.38/0.60    inference(avatar_split_clause,[],[f162,f147,f184])).
% 1.38/0.60  fof(f162,plain,(
% 1.38/0.60    v1_relat_1(sK3) | ~spl4_10),
% 1.38/0.60    inference(unit_resulting_resolution,[],[f149,f73])).
% 1.38/0.60  fof(f73,plain,(
% 1.38/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.38/0.60    inference(cnf_transformation,[],[f30])).
% 1.38/0.60  fof(f30,plain,(
% 1.38/0.60    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.38/0.60    inference(ennf_transformation,[],[f8])).
% 1.38/0.60  fof(f8,axiom,(
% 1.38/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.38/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.38/0.60  fof(f171,plain,(
% 1.38/0.60    spl4_13 | ~spl4_9),
% 1.38/0.60    inference(avatar_split_clause,[],[f161,f142,f168])).
% 1.38/0.60  fof(f161,plain,(
% 1.38/0.60    v1_relat_1(sK2) | ~spl4_9),
% 1.38/0.60    inference(unit_resulting_resolution,[],[f144,f73])).
% 1.38/0.60  fof(f160,plain,(
% 1.38/0.60    spl4_12),
% 1.38/0.60    inference(avatar_split_clause,[],[f54,f157])).
% 1.38/0.60  fof(f54,plain,(
% 1.38/0.60    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.38/0.60    inference(cnf_transformation,[],[f44])).
% 1.38/0.60  fof(f44,plain,(
% 1.38/0.60    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 1.38/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f43,f42])).
% 1.38/0.60  fof(f42,plain,(
% 1.38/0.60    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 1.38/0.60    introduced(choice_axiom,[])).
% 1.38/0.60  fof(f43,plain,(
% 1.38/0.60    ? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 1.38/0.60    introduced(choice_axiom,[])).
% 1.38/0.60  fof(f20,plain,(
% 1.38/0.60    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.38/0.60    inference(flattening,[],[f19])).
% 1.38/0.60  fof(f19,plain,(
% 1.38/0.60    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.38/0.60    inference(ennf_transformation,[],[f18])).
% 1.38/0.60  fof(f18,negated_conjecture,(
% 1.38/0.60    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.38/0.60    inference(negated_conjecture,[],[f17])).
% 1.38/0.60  fof(f17,conjecture,(
% 1.38/0.60    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.38/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).
% 1.38/0.60  fof(f155,plain,(
% 1.38/0.60    spl4_11),
% 1.38/0.60    inference(avatar_split_clause,[],[f53,f152])).
% 1.38/0.60  fof(f53,plain,(
% 1.38/0.60    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 1.38/0.60    inference(cnf_transformation,[],[f44])).
% 1.38/0.60  fof(f150,plain,(
% 1.38/0.60    spl4_10),
% 1.38/0.60    inference(avatar_split_clause,[],[f52,f147])).
% 1.38/0.60  fof(f52,plain,(
% 1.38/0.60    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.38/0.60    inference(cnf_transformation,[],[f44])).
% 1.38/0.60  fof(f145,plain,(
% 1.38/0.60    spl4_9),
% 1.38/0.60    inference(avatar_split_clause,[],[f49,f142])).
% 1.38/0.60  fof(f49,plain,(
% 1.38/0.60    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.38/0.60    inference(cnf_transformation,[],[f44])).
% 1.38/0.60  fof(f140,plain,(
% 1.38/0.60    ~spl4_8),
% 1.38/0.60    inference(avatar_split_clause,[],[f58,f137])).
% 1.38/0.60  fof(f58,plain,(
% 1.38/0.60    k2_funct_1(sK2) != sK3),
% 1.38/0.60    inference(cnf_transformation,[],[f44])).
% 1.38/0.60  fof(f135,plain,(
% 1.38/0.60    spl4_7),
% 1.38/0.60    inference(avatar_split_clause,[],[f51,f132])).
% 1.38/0.60  fof(f51,plain,(
% 1.38/0.60    v1_funct_2(sK3,sK1,sK0)),
% 1.38/0.60    inference(cnf_transformation,[],[f44])).
% 1.38/0.60  fof(f130,plain,(
% 1.38/0.60    spl4_6),
% 1.38/0.60    inference(avatar_split_clause,[],[f48,f127])).
% 1.38/0.60  fof(f48,plain,(
% 1.38/0.60    v1_funct_2(sK2,sK0,sK1)),
% 1.38/0.60    inference(cnf_transformation,[],[f44])).
% 1.38/0.60  fof(f125,plain,(
% 1.38/0.60    ~spl4_5),
% 1.38/0.60    inference(avatar_split_clause,[],[f57,f122])).
% 1.38/0.60  fof(f57,plain,(
% 1.38/0.60    k1_xboole_0 != sK1),
% 1.38/0.60    inference(cnf_transformation,[],[f44])).
% 1.38/0.60  fof(f120,plain,(
% 1.38/0.60    ~spl4_4),
% 1.38/0.60    inference(avatar_split_clause,[],[f56,f117])).
% 1.38/0.60  fof(f56,plain,(
% 1.38/0.60    k1_xboole_0 != sK0),
% 1.38/0.60    inference(cnf_transformation,[],[f44])).
% 1.38/0.60  fof(f115,plain,(
% 1.38/0.60    spl4_3),
% 1.38/0.60    inference(avatar_split_clause,[],[f55,f112])).
% 1.38/0.60  fof(f55,plain,(
% 1.38/0.60    v2_funct_1(sK2)),
% 1.38/0.60    inference(cnf_transformation,[],[f44])).
% 1.38/0.60  fof(f110,plain,(
% 1.38/0.60    spl4_2),
% 1.38/0.60    inference(avatar_split_clause,[],[f50,f107])).
% 1.38/0.60  fof(f50,plain,(
% 1.38/0.60    v1_funct_1(sK3)),
% 1.38/0.60    inference(cnf_transformation,[],[f44])).
% 1.38/0.60  fof(f105,plain,(
% 1.38/0.60    spl4_1),
% 1.38/0.60    inference(avatar_split_clause,[],[f47,f102])).
% 1.38/0.60  fof(f47,plain,(
% 1.38/0.60    v1_funct_1(sK2)),
% 1.38/0.60    inference(cnf_transformation,[],[f44])).
% 1.38/0.60  % SZS output end Proof for theBenchmark
% 1.38/0.60  % (16532)------------------------------
% 1.38/0.60  % (16532)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.60  % (16532)Termination reason: Refutation
% 1.38/0.60  
% 1.38/0.60  % (16532)Memory used [KB]: 11641
% 1.38/0.60  % (16532)Time elapsed: 0.154 s
% 1.38/0.60  % (16532)------------------------------
% 1.38/0.60  % (16532)------------------------------
% 1.38/0.60  % (16511)Success in time 0.23 s
%------------------------------------------------------------------------------
