%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:32 EST 2020

% Result     : Theorem 1.63s
% Output     : Refutation 1.63s
% Verified   : 
% Statistics : Number of formulae       :  159 ( 339 expanded)
%              Number of leaves         :   36 ( 140 expanded)
%              Depth                    :   12
%              Number of atoms          :  633 (1814 expanded)
%              Number of equality atoms :  131 ( 487 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f862,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f90,f95,f100,f110,f115,f125,f130,f135,f140,f145,f168,f182,f253,f287,f309,f428,f433,f687,f837])).

fof(f837,plain,
    ( ~ spl4_1
    | ~ spl4_3
    | spl4_5
    | ~ spl4_6
    | spl4_8
    | ~ spl4_9
    | ~ spl4_11
    | ~ spl4_13
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_17
    | ~ spl4_21
    | ~ spl4_31
    | ~ spl4_32
    | ~ spl4_37 ),
    inference(avatar_contradiction_clause,[],[f836])).

fof(f836,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_3
    | spl4_5
    | ~ spl4_6
    | spl4_8
    | ~ spl4_9
    | ~ spl4_11
    | ~ spl4_13
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_17
    | ~ spl4_21
    | ~ spl4_31
    | ~ spl4_32
    | ~ spl4_37 ),
    inference(subsumption_resolution,[],[f835,f124])).

fof(f124,plain,
    ( k2_funct_1(sK2) != sK3
    | spl4_8 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl4_8
  <=> k2_funct_1(sK2) = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f835,plain,
    ( k2_funct_1(sK2) = sK3
    | ~ spl4_1
    | ~ spl4_3
    | spl4_5
    | ~ spl4_6
    | ~ spl4_9
    | ~ spl4_11
    | ~ spl4_13
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_17
    | ~ spl4_21
    | ~ spl4_31
    | ~ spl4_32
    | ~ spl4_37 ),
    inference(backward_demodulation,[],[f494,f801])).

fof(f801,plain,
    ( sK3 = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0))
    | ~ spl4_1
    | ~ spl4_3
    | spl4_5
    | ~ spl4_6
    | ~ spl4_9
    | ~ spl4_11
    | ~ spl4_13
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_17
    | ~ spl4_21
    | ~ spl4_37 ),
    inference(backward_demodulation,[],[f532,f743])).

fof(f743,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl4_15
    | ~ spl4_37 ),
    inference(unit_resulting_resolution,[],[f59,f252,f686,f75])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
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

fof(f686,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_37 ),
    inference(avatar_component_clause,[],[f684])).

fof(f684,plain,
    ( spl4_37
  <=> m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f252,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0))
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f250])).

fof(f250,plain,
    ( spl4_15
  <=> r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f59,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f532,plain,
    ( sK3 = k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,sK3))
    | ~ spl4_1
    | ~ spl4_3
    | spl4_5
    | ~ spl4_6
    | ~ spl4_9
    | ~ spl4_11
    | ~ spl4_13
    | ~ spl4_14
    | ~ spl4_17
    | ~ spl4_21 ),
    inference(forward_demodulation,[],[f531,f299])).

fof(f299,plain,
    ( sK3 = k7_relat_1(sK3,sK1)
    | ~ spl4_14
    | ~ spl4_17 ),
    inference(unit_resulting_resolution,[],[f181,f286,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f286,plain,
    ( v4_relat_1(sK3,sK1)
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f284])).

fof(f284,plain,
    ( spl4_17
  <=> v4_relat_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f181,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f179])).

fof(f179,plain,
    ( spl4_14
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f531,plain,
    ( k7_relat_1(sK3,sK1) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,sK3))
    | ~ spl4_1
    | ~ spl4_3
    | spl4_5
    | ~ spl4_6
    | ~ spl4_9
    | ~ spl4_11
    | ~ spl4_13
    | ~ spl4_14
    | ~ spl4_21 ),
    inference(forward_demodulation,[],[f530,f244])).

fof(f244,plain,
    ( ! [X0] : k5_relat_1(k6_partfun1(X0),sK3) = k7_relat_1(sK3,X0)
    | ~ spl4_14 ),
    inference(unit_resulting_resolution,[],[f181,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_partfun1(X0),X1) ) ),
    inference(definition_unfolding,[],[f68,f57])).

fof(f57,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f68,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f530,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,sK3)) = k5_relat_1(k6_partfun1(sK1),sK3)
    | ~ spl4_1
    | ~ spl4_3
    | spl4_5
    | ~ spl4_6
    | ~ spl4_9
    | ~ spl4_11
    | ~ spl4_13
    | ~ spl4_14
    | ~ spl4_21 ),
    inference(forward_demodulation,[],[f450,f277])).

fof(f277,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | ~ spl4_1
    | ~ spl4_3
    | spl4_5
    | ~ spl4_6
    | ~ spl4_9
    | ~ spl4_11 ),
    inference(unit_resulting_resolution,[],[f89,f99,f109,f114,f129,f139,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | k1_xboole_0 = X1
      | k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

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
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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

fof(f139,plain,
    ( sK1 = k2_relset_1(sK0,sK1,sK2)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f137])).

fof(f137,plain,
    ( spl4_11
  <=> sK1 = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f129,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl4_9
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f114,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl4_6
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f109,plain,
    ( k1_xboole_0 != sK1
    | spl4_5 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl4_5
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f99,plain,
    ( v2_funct_1(sK2)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl4_3
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f89,plain,
    ( v1_funct_1(sK2)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl4_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f450,plain,
    ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),sK3) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,sK3))
    | ~ spl4_13
    | ~ spl4_14
    | ~ spl4_21 ),
    inference(unit_resulting_resolution,[],[f181,f167,f308,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

fof(f308,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f306])).

fof(f306,plain,
    ( spl4_21
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f167,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f165])).

fof(f165,plain,
    ( spl4_13
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f494,plain,
    ( k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0))
    | ~ spl4_21
    | ~ spl4_31
    | ~ spl4_32 ),
    inference(forward_demodulation,[],[f493,f432])).

fof(f432,plain,
    ( k6_partfun1(sK0) = k6_partfun1(k1_relat_1(sK2))
    | ~ spl4_32 ),
    inference(avatar_component_clause,[],[f430])).

fof(f430,plain,
    ( spl4_32
  <=> k6_partfun1(sK0) = k6_partfun1(k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f493,plain,
    ( k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(k1_relat_1(sK2)))
    | ~ spl4_21
    | ~ spl4_31 ),
    inference(forward_demodulation,[],[f487,f427])).

fof(f427,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl4_31 ),
    inference(avatar_component_clause,[],[f425])).

fof(f425,plain,
    ( spl4_31
  <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f487,plain,
    ( k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(k2_relat_1(k2_funct_1(sK2))))
    | ~ spl4_21 ),
    inference(unit_resulting_resolution,[],[f308,f80])).

fof(f80,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 ) ),
    inference(definition_unfolding,[],[f60,f57])).

fof(f60,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

fof(f687,plain,
    ( spl4_37
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_9
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f264,f132,f127,f92,f87,f684])).

fof(f92,plain,
    ( spl4_2
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f132,plain,
    ( spl4_10
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f264,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_9
    | ~ spl4_10 ),
    inference(forward_demodulation,[],[f256,f218])).

fof(f218,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_9
    | ~ spl4_10 ),
    inference(unit_resulting_resolution,[],[f89,f94,f129,f134,f77])).

fof(f77,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f134,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f132])).

fof(f94,plain,
    ( v1_funct_1(sK3)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f92])).

fof(f256,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_9
    | ~ spl4_10 ),
    inference(unit_resulting_resolution,[],[f89,f94,f129,f134,f79])).

fof(f79,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f433,plain,
    ( spl4_32
    | ~ spl4_1
    | ~ spl4_3
    | spl4_5
    | ~ spl4_6
    | ~ spl4_9
    | ~ spl4_11
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f269,f165,f137,f127,f112,f107,f97,f87,f430])).

fof(f269,plain,
    ( k6_partfun1(sK0) = k6_partfun1(k1_relat_1(sK2))
    | ~ spl4_1
    | ~ spl4_3
    | spl4_5
    | ~ spl4_6
    | ~ spl4_9
    | ~ spl4_11
    | ~ spl4_13 ),
    inference(backward_demodulation,[],[f194,f267])).

fof(f267,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ spl4_1
    | ~ spl4_3
    | spl4_5
    | ~ spl4_6
    | ~ spl4_9
    | ~ spl4_11 ),
    inference(unit_resulting_resolution,[],[f89,f99,f109,f114,f129,f139,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | k1_xboole_0 = X1
      | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f194,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2))
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f193,f167])).

fof(f193,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl4_1
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f192,f89])).

fof(f192,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_3 ),
    inference(resolution,[],[f82,f99])).

fof(f82,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f66,f57])).

fof(f66,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

% (10643)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% (10652)Refutation not found, incomplete strategy% (10652)------------------------------
% (10652)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (10652)Termination reason: Refutation not found, incomplete strategy

% (10652)Memory used [KB]: 10746
% (10652)Time elapsed: 0.177 s
% (10652)------------------------------
% (10652)------------------------------
% (10642)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% (10655)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% (10644)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% (10663)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% (10665)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
fof(f26,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(f428,plain,
    ( spl4_31
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f188,f165,f97,f87,f425])).

fof(f188,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f187,f167])).

fof(f187,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl4_1
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f186,f89])).

fof(f186,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_3 ),
    inference(resolution,[],[f65,f99])).

fof(f65,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
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

fof(f309,plain,
    ( spl4_21
    | ~ spl4_1
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f195,f165,f87,f306])).

fof(f195,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ spl4_1
    | ~ spl4_13 ),
    inference(unit_resulting_resolution,[],[f89,f167,f62])).

fof(f62,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f287,plain,
    ( spl4_17
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f153,f132,f284])).

fof(f153,plain,
    ( v4_relat_1(sK3,sK1)
    | ~ spl4_10 ),
    inference(unit_resulting_resolution,[],[f134,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f253,plain,
    ( spl4_15
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f226,f142,f132,f127,f92,f87,f250])).

fof(f142,plain,
    ( spl4_12
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f226,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12 ),
    inference(backward_demodulation,[],[f144,f218])).

fof(f144,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f142])).

fof(f182,plain,
    ( spl4_14
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f147,f132,f179])).

fof(f147,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_10 ),
    inference(unit_resulting_resolution,[],[f134,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f168,plain,
    ( spl4_13
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f146,f127,f165])).

fof(f146,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_9 ),
    inference(unit_resulting_resolution,[],[f129,f70])).

fof(f145,plain,(
    spl4_12 ),
    inference(avatar_split_clause,[],[f52,f142])).

fof(f52,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f42,f41])).

fof(f41,plain,
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

fof(f42,plain,
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

fof(f140,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f51,f137])).

fof(f51,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f135,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f50,f132])).

fof(f50,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f43])).

fof(f130,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f47,f127])).

fof(f47,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f43])).

fof(f125,plain,(
    ~ spl4_8 ),
    inference(avatar_split_clause,[],[f56,f122])).

fof(f56,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f43])).

fof(f115,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f46,f112])).

fof(f46,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f110,plain,(
    ~ spl4_5 ),
    inference(avatar_split_clause,[],[f55,f107])).

fof(f55,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f43])).

fof(f100,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f53,f97])).

fof(f53,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f95,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f48,f92])).

fof(f48,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f90,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f45,f87])).

fof(f45,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f43])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:15:24 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.53  % (10649)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.53  % (10656)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.54  % (10647)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.42/0.55  % (10664)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.42/0.56  % (10646)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.42/0.56  % (10640)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.42/0.57  % (10638)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.63/0.57  % (10641)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.63/0.57  % (10639)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.63/0.57  % (10650)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.63/0.57  % (10652)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.63/0.57  % (10654)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.63/0.57  % (10636)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.63/0.58  % (10645)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.63/0.58  % (10637)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.63/0.58  % (10661)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.63/0.58  % (10658)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.63/0.59  % (10653)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.63/0.59  % (10662)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.63/0.59  % (10660)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.63/0.59  % (10659)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.63/0.59  % (10651)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.63/0.59  % (10656)Refutation found. Thanks to Tanya!
% 1.63/0.59  % SZS status Theorem for theBenchmark
% 1.63/0.59  % SZS output start Proof for theBenchmark
% 1.63/0.59  fof(f862,plain,(
% 1.63/0.59    $false),
% 1.63/0.59    inference(avatar_sat_refutation,[],[f90,f95,f100,f110,f115,f125,f130,f135,f140,f145,f168,f182,f253,f287,f309,f428,f433,f687,f837])).
% 1.63/0.59  fof(f837,plain,(
% 1.63/0.59    ~spl4_1 | ~spl4_3 | spl4_5 | ~spl4_6 | spl4_8 | ~spl4_9 | ~spl4_11 | ~spl4_13 | ~spl4_14 | ~spl4_15 | ~spl4_17 | ~spl4_21 | ~spl4_31 | ~spl4_32 | ~spl4_37),
% 1.63/0.59    inference(avatar_contradiction_clause,[],[f836])).
% 1.63/0.59  fof(f836,plain,(
% 1.63/0.59    $false | (~spl4_1 | ~spl4_3 | spl4_5 | ~spl4_6 | spl4_8 | ~spl4_9 | ~spl4_11 | ~spl4_13 | ~spl4_14 | ~spl4_15 | ~spl4_17 | ~spl4_21 | ~spl4_31 | ~spl4_32 | ~spl4_37)),
% 1.63/0.59    inference(subsumption_resolution,[],[f835,f124])).
% 1.63/0.59  fof(f124,plain,(
% 1.63/0.59    k2_funct_1(sK2) != sK3 | spl4_8),
% 1.63/0.59    inference(avatar_component_clause,[],[f122])).
% 1.63/0.59  fof(f122,plain,(
% 1.63/0.59    spl4_8 <=> k2_funct_1(sK2) = sK3),
% 1.63/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.63/0.59  fof(f835,plain,(
% 1.63/0.59    k2_funct_1(sK2) = sK3 | (~spl4_1 | ~spl4_3 | spl4_5 | ~spl4_6 | ~spl4_9 | ~spl4_11 | ~spl4_13 | ~spl4_14 | ~spl4_15 | ~spl4_17 | ~spl4_21 | ~spl4_31 | ~spl4_32 | ~spl4_37)),
% 1.63/0.59    inference(backward_demodulation,[],[f494,f801])).
% 1.63/0.59  fof(f801,plain,(
% 1.63/0.59    sK3 = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) | (~spl4_1 | ~spl4_3 | spl4_5 | ~spl4_6 | ~spl4_9 | ~spl4_11 | ~spl4_13 | ~spl4_14 | ~spl4_15 | ~spl4_17 | ~spl4_21 | ~spl4_37)),
% 1.63/0.59    inference(backward_demodulation,[],[f532,f743])).
% 1.63/0.59  fof(f743,plain,(
% 1.63/0.59    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | (~spl4_15 | ~spl4_37)),
% 1.63/0.59    inference(unit_resulting_resolution,[],[f59,f252,f686,f75])).
% 1.63/0.59  fof(f75,plain,(
% 1.63/0.59    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.63/0.59    inference(cnf_transformation,[],[f44])).
% 1.63/0.59  fof(f44,plain,(
% 1.63/0.59    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.63/0.59    inference(nnf_transformation,[],[f36])).
% 1.63/0.59  fof(f36,plain,(
% 1.63/0.59    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.63/0.59    inference(flattening,[],[f35])).
% 1.63/0.59  fof(f35,plain,(
% 1.63/0.59    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.63/0.59    inference(ennf_transformation,[],[f10])).
% 1.63/0.59  fof(f10,axiom,(
% 1.63/0.59    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.63/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.63/0.59  fof(f686,plain,(
% 1.63/0.59    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl4_37),
% 1.63/0.59    inference(avatar_component_clause,[],[f684])).
% 1.63/0.59  fof(f684,plain,(
% 1.63/0.59    spl4_37 <=> m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.63/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).
% 1.63/0.59  fof(f252,plain,(
% 1.63/0.59    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0)) | ~spl4_15),
% 1.63/0.59    inference(avatar_component_clause,[],[f250])).
% 1.63/0.59  fof(f250,plain,(
% 1.63/0.59    spl4_15 <=> r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0))),
% 1.63/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 1.63/0.59  fof(f59,plain,(
% 1.63/0.59    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.63/0.59    inference(cnf_transformation,[],[f12])).
% 1.63/0.59  fof(f12,axiom,(
% 1.63/0.59    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 1.63/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 1.63/0.59  fof(f532,plain,(
% 1.63/0.59    sK3 = k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,sK3)) | (~spl4_1 | ~spl4_3 | spl4_5 | ~spl4_6 | ~spl4_9 | ~spl4_11 | ~spl4_13 | ~spl4_14 | ~spl4_17 | ~spl4_21)),
% 1.63/0.59    inference(forward_demodulation,[],[f531,f299])).
% 1.63/0.59  fof(f299,plain,(
% 1.63/0.59    sK3 = k7_relat_1(sK3,sK1) | (~spl4_14 | ~spl4_17)),
% 1.63/0.59    inference(unit_resulting_resolution,[],[f181,f286,f69])).
% 1.63/0.59  fof(f69,plain,(
% 1.63/0.59    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1) )),
% 1.63/0.59    inference(cnf_transformation,[],[f30])).
% 1.63/0.59  fof(f30,plain,(
% 1.63/0.59    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.63/0.59    inference(flattening,[],[f29])).
% 1.63/0.59  fof(f29,plain,(
% 1.63/0.59    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.63/0.59    inference(ennf_transformation,[],[f1])).
% 1.63/0.59  fof(f1,axiom,(
% 1.63/0.59    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 1.63/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 1.63/0.59  fof(f286,plain,(
% 1.63/0.59    v4_relat_1(sK3,sK1) | ~spl4_17),
% 1.63/0.59    inference(avatar_component_clause,[],[f284])).
% 1.63/0.59  fof(f284,plain,(
% 1.63/0.59    spl4_17 <=> v4_relat_1(sK3,sK1)),
% 1.63/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 1.63/0.59  fof(f181,plain,(
% 1.63/0.59    v1_relat_1(sK3) | ~spl4_14),
% 1.63/0.59    inference(avatar_component_clause,[],[f179])).
% 1.63/0.59  fof(f179,plain,(
% 1.63/0.59    spl4_14 <=> v1_relat_1(sK3)),
% 1.63/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 1.63/0.59  fof(f531,plain,(
% 1.63/0.59    k7_relat_1(sK3,sK1) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,sK3)) | (~spl4_1 | ~spl4_3 | spl4_5 | ~spl4_6 | ~spl4_9 | ~spl4_11 | ~spl4_13 | ~spl4_14 | ~spl4_21)),
% 1.63/0.59    inference(forward_demodulation,[],[f530,f244])).
% 1.63/0.59  fof(f244,plain,(
% 1.63/0.59    ( ! [X0] : (k5_relat_1(k6_partfun1(X0),sK3) = k7_relat_1(sK3,X0)) ) | ~spl4_14),
% 1.63/0.59    inference(unit_resulting_resolution,[],[f181,f83])).
% 1.63/0.59  fof(f83,plain,(
% 1.63/0.59    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_partfun1(X0),X1)) )),
% 1.63/0.59    inference(definition_unfolding,[],[f68,f57])).
% 1.63/0.59  fof(f57,plain,(
% 1.63/0.59    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.63/0.59    inference(cnf_transformation,[],[f14])).
% 1.63/0.59  fof(f14,axiom,(
% 1.63/0.59    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.63/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.63/0.59  fof(f68,plain,(
% 1.63/0.59    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 1.63/0.59    inference(cnf_transformation,[],[f28])).
% 1.63/0.59  fof(f28,plain,(
% 1.63/0.59    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 1.63/0.59    inference(ennf_transformation,[],[f4])).
% 1.63/0.59  fof(f4,axiom,(
% 1.63/0.59    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 1.63/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 1.63/0.59  fof(f530,plain,(
% 1.63/0.59    k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,sK3)) = k5_relat_1(k6_partfun1(sK1),sK3) | (~spl4_1 | ~spl4_3 | spl4_5 | ~spl4_6 | ~spl4_9 | ~spl4_11 | ~spl4_13 | ~spl4_14 | ~spl4_21)),
% 1.63/0.59    inference(forward_demodulation,[],[f450,f277])).
% 1.63/0.59  fof(f277,plain,(
% 1.63/0.59    k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) | (~spl4_1 | ~spl4_3 | spl4_5 | ~spl4_6 | ~spl4_9 | ~spl4_11)),
% 1.63/0.59    inference(unit_resulting_resolution,[],[f89,f99,f109,f114,f129,f139,f74])).
% 1.63/0.59  fof(f74,plain,(
% 1.63/0.59    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | k1_xboole_0 = X1 | k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.63/0.59    inference(cnf_transformation,[],[f34])).
% 1.63/0.59  fof(f34,plain,(
% 1.63/0.59    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.63/0.59    inference(flattening,[],[f33])).
% 1.63/0.59  fof(f33,plain,(
% 1.63/0.59    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.63/0.59    inference(ennf_transformation,[],[f15])).
% 1.63/0.59  fof(f15,axiom,(
% 1.63/0.59    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 1.63/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).
% 1.63/0.59  fof(f139,plain,(
% 1.63/0.59    sK1 = k2_relset_1(sK0,sK1,sK2) | ~spl4_11),
% 1.63/0.59    inference(avatar_component_clause,[],[f137])).
% 1.63/0.59  fof(f137,plain,(
% 1.63/0.59    spl4_11 <=> sK1 = k2_relset_1(sK0,sK1,sK2)),
% 1.63/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 1.63/0.59  fof(f129,plain,(
% 1.63/0.59    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_9),
% 1.63/0.59    inference(avatar_component_clause,[],[f127])).
% 1.63/0.59  fof(f127,plain,(
% 1.63/0.59    spl4_9 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.63/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 1.63/0.59  fof(f114,plain,(
% 1.63/0.59    v1_funct_2(sK2,sK0,sK1) | ~spl4_6),
% 1.63/0.59    inference(avatar_component_clause,[],[f112])).
% 1.63/0.59  fof(f112,plain,(
% 1.63/0.59    spl4_6 <=> v1_funct_2(sK2,sK0,sK1)),
% 1.63/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.63/0.59  fof(f109,plain,(
% 1.63/0.59    k1_xboole_0 != sK1 | spl4_5),
% 1.63/0.59    inference(avatar_component_clause,[],[f107])).
% 1.63/0.59  fof(f107,plain,(
% 1.63/0.59    spl4_5 <=> k1_xboole_0 = sK1),
% 1.63/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.63/0.59  fof(f99,plain,(
% 1.63/0.59    v2_funct_1(sK2) | ~spl4_3),
% 1.63/0.59    inference(avatar_component_clause,[],[f97])).
% 1.63/0.59  fof(f97,plain,(
% 1.63/0.59    spl4_3 <=> v2_funct_1(sK2)),
% 1.63/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.63/0.59  fof(f89,plain,(
% 1.63/0.59    v1_funct_1(sK2) | ~spl4_1),
% 1.63/0.59    inference(avatar_component_clause,[],[f87])).
% 1.63/0.59  fof(f87,plain,(
% 1.63/0.59    spl4_1 <=> v1_funct_1(sK2)),
% 1.63/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.63/0.59  fof(f450,plain,(
% 1.63/0.59    k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),sK3) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,sK3)) | (~spl4_13 | ~spl4_14 | ~spl4_21)),
% 1.63/0.59    inference(unit_resulting_resolution,[],[f181,f167,f308,f61])).
% 1.63/0.59  fof(f61,plain,(
% 1.63/0.59    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.63/0.59    inference(cnf_transformation,[],[f21])).
% 1.63/0.59  fof(f21,plain,(
% 1.63/0.59    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.63/0.59    inference(ennf_transformation,[],[f2])).
% 1.63/0.59  fof(f2,axiom,(
% 1.63/0.59    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 1.63/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).
% 1.63/0.59  fof(f308,plain,(
% 1.63/0.59    v1_relat_1(k2_funct_1(sK2)) | ~spl4_21),
% 1.63/0.59    inference(avatar_component_clause,[],[f306])).
% 1.63/0.59  fof(f306,plain,(
% 1.63/0.59    spl4_21 <=> v1_relat_1(k2_funct_1(sK2))),
% 1.63/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 1.63/0.59  fof(f167,plain,(
% 1.63/0.59    v1_relat_1(sK2) | ~spl4_13),
% 1.63/0.59    inference(avatar_component_clause,[],[f165])).
% 1.63/0.59  fof(f165,plain,(
% 1.63/0.59    spl4_13 <=> v1_relat_1(sK2)),
% 1.63/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 1.63/0.59  fof(f494,plain,(
% 1.63/0.59    k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) | (~spl4_21 | ~spl4_31 | ~spl4_32)),
% 1.63/0.59    inference(forward_demodulation,[],[f493,f432])).
% 1.63/0.59  fof(f432,plain,(
% 1.63/0.59    k6_partfun1(sK0) = k6_partfun1(k1_relat_1(sK2)) | ~spl4_32),
% 1.63/0.59    inference(avatar_component_clause,[],[f430])).
% 1.63/0.59  fof(f430,plain,(
% 1.63/0.59    spl4_32 <=> k6_partfun1(sK0) = k6_partfun1(k1_relat_1(sK2))),
% 1.63/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 1.63/0.59  fof(f493,plain,(
% 1.63/0.59    k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(k1_relat_1(sK2))) | (~spl4_21 | ~spl4_31)),
% 1.63/0.59    inference(forward_demodulation,[],[f487,f427])).
% 1.63/0.59  fof(f427,plain,(
% 1.63/0.59    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~spl4_31),
% 1.63/0.59    inference(avatar_component_clause,[],[f425])).
% 1.63/0.59  fof(f425,plain,(
% 1.63/0.59    spl4_31 <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 1.63/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).
% 1.63/0.59  fof(f487,plain,(
% 1.63/0.59    k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(k2_relat_1(k2_funct_1(sK2)))) | ~spl4_21),
% 1.63/0.59    inference(unit_resulting_resolution,[],[f308,f80])).
% 1.63/0.59  fof(f80,plain,(
% 1.63/0.59    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0) )),
% 1.63/0.59    inference(definition_unfolding,[],[f60,f57])).
% 1.63/0.59  fof(f60,plain,(
% 1.63/0.59    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 1.63/0.59    inference(cnf_transformation,[],[f20])).
% 1.63/0.59  fof(f20,plain,(
% 1.63/0.59    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 1.63/0.59    inference(ennf_transformation,[],[f3])).
% 1.63/0.59  fof(f3,axiom,(
% 1.63/0.59    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 1.63/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).
% 1.63/0.59  fof(f687,plain,(
% 1.63/0.59    spl4_37 | ~spl4_1 | ~spl4_2 | ~spl4_9 | ~spl4_10),
% 1.63/0.59    inference(avatar_split_clause,[],[f264,f132,f127,f92,f87,f684])).
% 1.63/0.59  fof(f92,plain,(
% 1.63/0.59    spl4_2 <=> v1_funct_1(sK3)),
% 1.63/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.63/0.59  fof(f132,plain,(
% 1.63/0.59    spl4_10 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.63/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 1.63/0.59  fof(f264,plain,(
% 1.63/0.59    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | (~spl4_1 | ~spl4_2 | ~spl4_9 | ~spl4_10)),
% 1.63/0.59    inference(forward_demodulation,[],[f256,f218])).
% 1.63/0.59  fof(f218,plain,(
% 1.63/0.59    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) | (~spl4_1 | ~spl4_2 | ~spl4_9 | ~spl4_10)),
% 1.63/0.59    inference(unit_resulting_resolution,[],[f89,f94,f129,f134,f77])).
% 1.63/0.59  fof(f77,plain,(
% 1.63/0.59    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.63/0.59    inference(cnf_transformation,[],[f38])).
% 1.63/0.59  fof(f38,plain,(
% 1.63/0.59    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.63/0.59    inference(flattening,[],[f37])).
% 1.63/0.59  fof(f37,plain,(
% 1.63/0.59    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.63/0.59    inference(ennf_transformation,[],[f13])).
% 1.63/0.59  fof(f13,axiom,(
% 1.63/0.59    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.63/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.63/0.59  fof(f134,plain,(
% 1.63/0.59    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_10),
% 1.63/0.59    inference(avatar_component_clause,[],[f132])).
% 1.63/0.59  fof(f94,plain,(
% 1.63/0.59    v1_funct_1(sK3) | ~spl4_2),
% 1.63/0.59    inference(avatar_component_clause,[],[f92])).
% 1.63/0.59  fof(f256,plain,(
% 1.63/0.59    m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | (~spl4_1 | ~spl4_2 | ~spl4_9 | ~spl4_10)),
% 1.63/0.59    inference(unit_resulting_resolution,[],[f89,f94,f129,f134,f79])).
% 1.63/0.59  fof(f79,plain,(
% 1.63/0.59    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.63/0.59    inference(cnf_transformation,[],[f40])).
% 1.63/0.59  fof(f40,plain,(
% 1.63/0.59    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.63/0.59    inference(flattening,[],[f39])).
% 1.63/0.59  fof(f39,plain,(
% 1.63/0.59    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.63/0.59    inference(ennf_transformation,[],[f11])).
% 1.63/0.59  fof(f11,axiom,(
% 1.63/0.59    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.63/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.63/0.59  fof(f433,plain,(
% 1.63/0.59    spl4_32 | ~spl4_1 | ~spl4_3 | spl4_5 | ~spl4_6 | ~spl4_9 | ~spl4_11 | ~spl4_13),
% 1.63/0.59    inference(avatar_split_clause,[],[f269,f165,f137,f127,f112,f107,f97,f87,f430])).
% 1.63/0.59  fof(f269,plain,(
% 1.63/0.59    k6_partfun1(sK0) = k6_partfun1(k1_relat_1(sK2)) | (~spl4_1 | ~spl4_3 | spl4_5 | ~spl4_6 | ~spl4_9 | ~spl4_11 | ~spl4_13)),
% 1.63/0.59    inference(backward_demodulation,[],[f194,f267])).
% 1.63/0.59  fof(f267,plain,(
% 1.63/0.59    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | (~spl4_1 | ~spl4_3 | spl4_5 | ~spl4_6 | ~spl4_9 | ~spl4_11)),
% 1.63/0.59    inference(unit_resulting_resolution,[],[f89,f99,f109,f114,f129,f139,f73])).
% 1.63/0.59  fof(f73,plain,(
% 1.63/0.59    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | k1_xboole_0 = X1 | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.63/0.59    inference(cnf_transformation,[],[f34])).
% 1.63/0.59  fof(f194,plain,(
% 1.63/0.59    k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) | (~spl4_1 | ~spl4_3 | ~spl4_13)),
% 1.63/0.59    inference(subsumption_resolution,[],[f193,f167])).
% 1.63/0.59  fof(f193,plain,(
% 1.63/0.59    k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) | ~v1_relat_1(sK2) | (~spl4_1 | ~spl4_3)),
% 1.63/0.59    inference(subsumption_resolution,[],[f192,f89])).
% 1.63/0.59  fof(f192,plain,(
% 1.63/0.59    k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl4_3),
% 1.63/0.59    inference(resolution,[],[f82,f99])).
% 1.63/0.59  fof(f82,plain,(
% 1.63/0.59    ( ! [X0] : (~v2_funct_1(X0) | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.63/0.59    inference(definition_unfolding,[],[f66,f57])).
% 1.63/0.59  fof(f66,plain,(
% 1.63/0.59    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.63/0.59    inference(cnf_transformation,[],[f27])).
% 1.63/0.59  fof(f27,plain,(
% 1.63/0.59    ! [X0] : ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.63/0.59    inference(flattening,[],[f26])).
% 1.63/0.60  % (10643)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.63/0.60  % (10652)Refutation not found, incomplete strategy% (10652)------------------------------
% 1.63/0.60  % (10652)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.60  % (10652)Termination reason: Refutation not found, incomplete strategy
% 1.63/0.60  
% 1.63/0.60  % (10652)Memory used [KB]: 10746
% 1.63/0.60  % (10652)Time elapsed: 0.177 s
% 1.63/0.60  % (10652)------------------------------
% 1.63/0.60  % (10652)------------------------------
% 1.63/0.60  % (10642)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.63/0.60  % (10655)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.63/0.60  % (10644)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.63/0.60  % (10663)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.63/0.60  % (10665)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.63/0.61  fof(f26,plain,(
% 1.63/0.61    ! [X0] : (((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.63/0.61    inference(ennf_transformation,[],[f7])).
% 1.63/0.61  fof(f7,axiom,(
% 1.63/0.61    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 1.63/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).
% 1.63/0.61  fof(f428,plain,(
% 1.63/0.61    spl4_31 | ~spl4_1 | ~spl4_3 | ~spl4_13),
% 1.63/0.61    inference(avatar_split_clause,[],[f188,f165,f97,f87,f425])).
% 1.63/0.61  fof(f188,plain,(
% 1.63/0.61    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | (~spl4_1 | ~spl4_3 | ~spl4_13)),
% 1.63/0.61    inference(subsumption_resolution,[],[f187,f167])).
% 1.63/0.61  fof(f187,plain,(
% 1.63/0.61    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2) | (~spl4_1 | ~spl4_3)),
% 1.63/0.61    inference(subsumption_resolution,[],[f186,f89])).
% 1.63/0.61  fof(f186,plain,(
% 1.63/0.61    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl4_3),
% 1.63/0.61    inference(resolution,[],[f65,f99])).
% 1.63/0.61  fof(f65,plain,(
% 1.63/0.61    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.63/0.61    inference(cnf_transformation,[],[f25])).
% 1.63/0.61  fof(f25,plain,(
% 1.63/0.61    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.63/0.61    inference(flattening,[],[f24])).
% 1.63/0.61  fof(f24,plain,(
% 1.63/0.61    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.63/0.61    inference(ennf_transformation,[],[f6])).
% 1.63/0.61  fof(f6,axiom,(
% 1.63/0.61    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 1.63/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 1.63/0.61  fof(f309,plain,(
% 1.63/0.61    spl4_21 | ~spl4_1 | ~spl4_13),
% 1.63/0.61    inference(avatar_split_clause,[],[f195,f165,f87,f306])).
% 1.63/0.61  fof(f195,plain,(
% 1.63/0.61    v1_relat_1(k2_funct_1(sK2)) | (~spl4_1 | ~spl4_13)),
% 1.63/0.61    inference(unit_resulting_resolution,[],[f89,f167,f62])).
% 1.63/0.61  fof(f62,plain,(
% 1.63/0.61    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.63/0.61    inference(cnf_transformation,[],[f23])).
% 1.63/0.61  fof(f23,plain,(
% 1.63/0.61    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.63/0.61    inference(flattening,[],[f22])).
% 1.63/0.61  fof(f22,plain,(
% 1.63/0.61    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.63/0.61    inference(ennf_transformation,[],[f5])).
% 1.63/0.61  fof(f5,axiom,(
% 1.63/0.61    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.63/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 1.63/0.61  fof(f287,plain,(
% 1.63/0.61    spl4_17 | ~spl4_10),
% 1.63/0.61    inference(avatar_split_clause,[],[f153,f132,f284])).
% 1.63/0.61  fof(f153,plain,(
% 1.63/0.61    v4_relat_1(sK3,sK1) | ~spl4_10),
% 1.63/0.61    inference(unit_resulting_resolution,[],[f134,f71])).
% 1.63/0.61  fof(f71,plain,(
% 1.63/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.63/0.61    inference(cnf_transformation,[],[f32])).
% 1.63/0.61  fof(f32,plain,(
% 1.63/0.61    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.63/0.61    inference(ennf_transformation,[],[f9])).
% 1.63/0.61  fof(f9,axiom,(
% 1.63/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.63/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.63/0.61  fof(f253,plain,(
% 1.63/0.61    spl4_15 | ~spl4_1 | ~spl4_2 | ~spl4_9 | ~spl4_10 | ~spl4_12),
% 1.63/0.61    inference(avatar_split_clause,[],[f226,f142,f132,f127,f92,f87,f250])).
% 1.63/0.61  fof(f142,plain,(
% 1.63/0.61    spl4_12 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.63/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 1.63/0.61  fof(f226,plain,(
% 1.63/0.61    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0)) | (~spl4_1 | ~spl4_2 | ~spl4_9 | ~spl4_10 | ~spl4_12)),
% 1.63/0.61    inference(backward_demodulation,[],[f144,f218])).
% 1.63/0.61  fof(f144,plain,(
% 1.63/0.61    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) | ~spl4_12),
% 1.63/0.61    inference(avatar_component_clause,[],[f142])).
% 1.63/0.61  fof(f182,plain,(
% 1.63/0.61    spl4_14 | ~spl4_10),
% 1.63/0.61    inference(avatar_split_clause,[],[f147,f132,f179])).
% 1.63/0.61  fof(f147,plain,(
% 1.63/0.61    v1_relat_1(sK3) | ~spl4_10),
% 1.63/0.61    inference(unit_resulting_resolution,[],[f134,f70])).
% 1.63/0.61  fof(f70,plain,(
% 1.63/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.63/0.61    inference(cnf_transformation,[],[f31])).
% 1.63/0.61  fof(f31,plain,(
% 1.63/0.61    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.63/0.61    inference(ennf_transformation,[],[f8])).
% 1.63/0.61  fof(f8,axiom,(
% 1.63/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.63/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.63/0.61  fof(f168,plain,(
% 1.63/0.61    spl4_13 | ~spl4_9),
% 1.63/0.61    inference(avatar_split_clause,[],[f146,f127,f165])).
% 1.63/0.61  fof(f146,plain,(
% 1.63/0.61    v1_relat_1(sK2) | ~spl4_9),
% 1.63/0.61    inference(unit_resulting_resolution,[],[f129,f70])).
% 1.63/0.61  fof(f145,plain,(
% 1.63/0.61    spl4_12),
% 1.63/0.61    inference(avatar_split_clause,[],[f52,f142])).
% 1.63/0.61  fof(f52,plain,(
% 1.63/0.61    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.63/0.61    inference(cnf_transformation,[],[f43])).
% 1.63/0.61  fof(f43,plain,(
% 1.63/0.61    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 1.63/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f42,f41])).
% 1.63/0.61  fof(f41,plain,(
% 1.63/0.61    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 1.63/0.61    introduced(choice_axiom,[])).
% 1.63/0.61  fof(f42,plain,(
% 1.63/0.61    ? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 1.63/0.61    introduced(choice_axiom,[])).
% 1.63/0.61  fof(f19,plain,(
% 1.63/0.61    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.63/0.61    inference(flattening,[],[f18])).
% 1.63/0.61  fof(f18,plain,(
% 1.63/0.61    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.63/0.61    inference(ennf_transformation,[],[f17])).
% 1.63/0.61  fof(f17,negated_conjecture,(
% 1.63/0.61    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.63/0.61    inference(negated_conjecture,[],[f16])).
% 1.63/0.61  fof(f16,conjecture,(
% 1.63/0.61    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.63/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).
% 1.63/0.61  fof(f140,plain,(
% 1.63/0.61    spl4_11),
% 1.63/0.61    inference(avatar_split_clause,[],[f51,f137])).
% 1.63/0.61  fof(f51,plain,(
% 1.63/0.61    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 1.63/0.61    inference(cnf_transformation,[],[f43])).
% 1.63/0.61  fof(f135,plain,(
% 1.63/0.61    spl4_10),
% 1.63/0.61    inference(avatar_split_clause,[],[f50,f132])).
% 1.63/0.61  fof(f50,plain,(
% 1.63/0.61    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.63/0.61    inference(cnf_transformation,[],[f43])).
% 1.63/0.61  fof(f130,plain,(
% 1.63/0.61    spl4_9),
% 1.63/0.61    inference(avatar_split_clause,[],[f47,f127])).
% 1.63/0.61  fof(f47,plain,(
% 1.63/0.61    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.63/0.61    inference(cnf_transformation,[],[f43])).
% 1.63/0.61  fof(f125,plain,(
% 1.63/0.61    ~spl4_8),
% 1.63/0.61    inference(avatar_split_clause,[],[f56,f122])).
% 1.63/0.61  fof(f56,plain,(
% 1.63/0.61    k2_funct_1(sK2) != sK3),
% 1.63/0.61    inference(cnf_transformation,[],[f43])).
% 1.63/0.61  fof(f115,plain,(
% 1.63/0.61    spl4_6),
% 1.63/0.61    inference(avatar_split_clause,[],[f46,f112])).
% 1.63/0.61  fof(f46,plain,(
% 1.63/0.61    v1_funct_2(sK2,sK0,sK1)),
% 1.63/0.61    inference(cnf_transformation,[],[f43])).
% 1.63/0.61  fof(f110,plain,(
% 1.63/0.61    ~spl4_5),
% 1.63/0.61    inference(avatar_split_clause,[],[f55,f107])).
% 1.63/0.61  fof(f55,plain,(
% 1.63/0.61    k1_xboole_0 != sK1),
% 1.63/0.61    inference(cnf_transformation,[],[f43])).
% 1.63/0.61  fof(f100,plain,(
% 1.63/0.61    spl4_3),
% 1.63/0.61    inference(avatar_split_clause,[],[f53,f97])).
% 1.63/0.61  fof(f53,plain,(
% 1.63/0.61    v2_funct_1(sK2)),
% 1.63/0.61    inference(cnf_transformation,[],[f43])).
% 1.63/0.61  fof(f95,plain,(
% 1.63/0.61    spl4_2),
% 1.63/0.61    inference(avatar_split_clause,[],[f48,f92])).
% 1.63/0.61  fof(f48,plain,(
% 1.63/0.61    v1_funct_1(sK3)),
% 1.63/0.61    inference(cnf_transformation,[],[f43])).
% 1.63/0.61  fof(f90,plain,(
% 1.63/0.61    spl4_1),
% 1.63/0.61    inference(avatar_split_clause,[],[f45,f87])).
% 1.63/0.61  fof(f45,plain,(
% 1.63/0.61    v1_funct_1(sK2)),
% 1.63/0.61    inference(cnf_transformation,[],[f43])).
% 1.63/0.61  % SZS output end Proof for theBenchmark
% 1.63/0.61  % (10656)------------------------------
% 1.63/0.61  % (10656)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.61  % (10656)Termination reason: Refutation
% 1.63/0.61  
% 1.63/0.61  % (10656)Memory used [KB]: 11513
% 1.63/0.61  % (10656)Time elapsed: 0.180 s
% 1.63/0.61  % (10656)------------------------------
% 1.63/0.61  % (10656)------------------------------
% 1.63/0.61  % (10648)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.63/0.62  % (10635)Success in time 0.256 s
%------------------------------------------------------------------------------
