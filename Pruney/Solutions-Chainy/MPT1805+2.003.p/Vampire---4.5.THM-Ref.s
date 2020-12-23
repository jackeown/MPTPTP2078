%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:39 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 1.54s
% Verified   : 
% Statistics : Number of formulae       :  264 ( 646 expanded)
%              Number of leaves         :   47 ( 269 expanded)
%              Depth                    :   21
%              Number of atoms          : 1579 (3072 expanded)
%              Number of equality atoms :  159 ( 303 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f805,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f98,f103,f108,f113,f118,f133,f149,f168,f226,f243,f297,f303,f387,f408,f413,f425,f435,f467,f524,f535,f702,f715,f716,f791,f801,f802,f803,f804])).

fof(f804,plain,
    ( k9_tmap_1(sK0,sK1) != k6_partfun1(u1_struct_0(sK0))
    | k8_tmap_1(sK0,sK1) != k6_tmap_1(sK0,u1_struct_0(sK1))
    | u1_struct_0(sK0) != u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))
    | m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | ~ m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f803,plain,
    ( k8_tmap_1(sK0,sK1) != k6_tmap_1(sK0,u1_struct_0(sK1))
    | k9_tmap_1(sK0,sK1) != k6_partfun1(u1_struct_0(sK0))
    | v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK1),sK1,k8_tmap_1(sK0,sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK1),sK1,k8_tmap_1(sK0,sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f802,plain,
    ( k9_tmap_1(sK0,sK1) != k6_partfun1(u1_struct_0(sK0))
    | k8_tmap_1(sK0,sK1) != k6_tmap_1(sK0,u1_struct_0(sK1))
    | u1_struct_0(sK0) != u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))
    | v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK1),u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK1),u1_struct_0(sK1),u1_struct_0(sK0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f801,plain,
    ( ~ spl4_7
    | spl4_11
    | ~ spl4_30
    | ~ spl4_31
    | spl4_62 ),
    inference(avatar_contradiction_clause,[],[f800])).

fof(f800,plain,
    ( $false
    | ~ spl4_7
    | spl4_11
    | ~ spl4_30
    | ~ spl4_31
    | spl4_62 ),
    inference(subsumption_resolution,[],[f799,f201])).

fof(f201,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | spl4_11 ),
    inference(avatar_component_clause,[],[f199])).

fof(f199,plain,
    ( spl4_11
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f799,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl4_7
    | ~ spl4_30
    | ~ spl4_31
    | spl4_62 ),
    inference(subsumption_resolution,[],[f798,f148])).

fof(f148,plain,
    ( v1_funct_1(k6_partfun1(u1_struct_0(sK0)))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl4_7
  <=> v1_funct_1(k6_partfun1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f798,plain,
    ( ~ v1_funct_1(k6_partfun1(u1_struct_0(sK0)))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl4_30
    | ~ spl4_31
    | spl4_62 ),
    inference(subsumption_resolution,[],[f797,f424])).

fof(f424,plain,
    ( v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f422])).

fof(f422,plain,
    ( spl4_30
  <=> v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f797,plain,
    ( ~ v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k6_partfun1(u1_struct_0(sK0)))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl4_31
    | spl4_62 ),
    inference(subsumption_resolution,[],[f795,f466])).

fof(f466,plain,
    ( m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl4_31 ),
    inference(avatar_component_clause,[],[f464])).

fof(f464,plain,
    ( spl4_31
  <=> m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f795,plain,
    ( ~ m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k6_partfun1(u1_struct_0(sK0)))
    | v1_xboole_0(u1_struct_0(sK0))
    | spl4_62 ),
    inference(duplicate_literal_removal,[],[f794])).

fof(f794,plain,
    ( ~ m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k6_partfun1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | spl4_62 ),
    inference(resolution,[],[f790,f93])).

fof(f93,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r1_funct_2(X0,X1,X2,X3,X5,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X5,X0,X1)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(duplicate_literal_removal,[],[f92])).

fof(f92,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r1_funct_2(X0,X1,X2,X3,X5,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X5,X0,X1)
      | ~ v1_funct_1(X5)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      | X4 != X5
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
          | X4 != X5 )
        & ( X4 = X5
          | ~ r1_funct_2(X0,X1,X2,X3,X4,X5) ) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_2(X5,X2,X3)
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X4,X0,X1)
        & v1_funct_1(X4)
        & ~ v1_xboole_0(X3)
        & ~ v1_xboole_0(X1) )
     => ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_funct_2)).

fof(f790,plain,
    ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k6_partfun1(u1_struct_0(sK0)),k6_partfun1(u1_struct_0(sK0)))
    | spl4_62 ),
    inference(avatar_component_clause,[],[f788])).

fof(f788,plain,
    ( spl4_62
  <=> r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k6_partfun1(u1_struct_0(sK0)),k6_partfun1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_62])])).

fof(f791,plain,
    ( spl4_51
    | ~ spl4_62
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_14
    | ~ spl4_21
    | ~ spl4_30
    | ~ spl4_31
    | ~ spl4_52 ),
    inference(avatar_split_clause,[],[f733,f712,f464,f422,f300,f240,f146,f130,f115,f105,f100,f95,f788,f708])).

fof(f708,plain,
    ( spl4_51
  <=> k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_51])])).

fof(f95,plain,
    ( spl4_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f100,plain,
    ( spl4_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f105,plain,
    ( spl4_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f115,plain,
    ( spl4_5
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f130,plain,
    ( spl4_6
  <=> k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(sK0,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f240,plain,
    ( spl4_14
  <=> k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f300,plain,
    ( spl4_21
  <=> u1_struct_0(k8_tmap_1(sK0,sK1)) = u1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f712,plain,
    ( spl4_52
  <=> u1_struct_0(sK1) = sK3(sK0,sK1,k6_partfun1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).

fof(f733,plain,
    ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k6_partfun1(u1_struct_0(sK0)),k6_partfun1(u1_struct_0(sK0)))
    | k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0))
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_14
    | ~ spl4_21
    | ~ spl4_30
    | ~ spl4_31
    | ~ spl4_52 ),
    inference(subsumption_resolution,[],[f732,f424])).

fof(f732,plain,
    ( ~ v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k6_partfun1(u1_struct_0(sK0)),k6_partfun1(u1_struct_0(sK0)))
    | k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0))
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_14
    | ~ spl4_21
    | ~ spl4_31
    | ~ spl4_52 ),
    inference(forward_demodulation,[],[f731,f302])).

fof(f302,plain,
    ( u1_struct_0(k8_tmap_1(sK0,sK1)) = u1_struct_0(sK0)
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f300])).

fof(f731,plain,
    ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k6_partfun1(u1_struct_0(sK0)),k6_partfun1(u1_struct_0(sK0)))
    | k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0))
    | ~ v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_14
    | ~ spl4_21
    | ~ spl4_31
    | ~ spl4_52 ),
    inference(subsumption_resolution,[],[f730,f466])).

fof(f730,plain,
    ( ~ m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k6_partfun1(u1_struct_0(sK0)),k6_partfun1(u1_struct_0(sK0)))
    | k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0))
    | ~ v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_14
    | ~ spl4_21
    | ~ spl4_52 ),
    inference(forward_demodulation,[],[f729,f302])).

fof(f729,plain,
    ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k6_partfun1(u1_struct_0(sK0)),k6_partfun1(u1_struct_0(sK0)))
    | k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0))
    | ~ m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | ~ v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_14
    | ~ spl4_21
    | ~ spl4_52 ),
    inference(forward_demodulation,[],[f728,f302])).

fof(f728,plain,
    ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),k6_partfun1(u1_struct_0(sK0)),k6_partfun1(u1_struct_0(sK0)))
    | k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0))
    | ~ m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | ~ v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_14
    | ~ spl4_52 ),
    inference(forward_demodulation,[],[f727,f242])).

fof(f242,plain,
    ( k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f240])).

fof(f727,plain,
    ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))),k6_partfun1(u1_struct_0(sK0)),k6_partfun1(u1_struct_0(sK0)))
    | k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0))
    | ~ m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | ~ v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_52 ),
    inference(forward_demodulation,[],[f726,f132])).

fof(f132,plain,
    ( k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f130])).

fof(f726,plain,
    ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))),k6_partfun1(u1_struct_0(sK0)),k7_tmap_1(sK0,u1_struct_0(sK1)))
    | k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0))
    | ~ m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | ~ v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_52 ),
    inference(subsumption_resolution,[],[f725,f97])).

fof(f97,plain,
    ( ~ v2_struct_0(sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f95])).

fof(f725,plain,
    ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))),k6_partfun1(u1_struct_0(sK0)),k7_tmap_1(sK0,u1_struct_0(sK1)))
    | k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0))
    | ~ m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | ~ v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | v2_struct_0(sK0)
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_52 ),
    inference(subsumption_resolution,[],[f724,f102])).

fof(f102,plain,
    ( v2_pre_topc(sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f100])).

fof(f724,plain,
    ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))),k6_partfun1(u1_struct_0(sK0)),k7_tmap_1(sK0,u1_struct_0(sK1)))
    | k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0))
    | ~ m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | ~ v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_52 ),
    inference(subsumption_resolution,[],[f723,f107])).

fof(f107,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f105])).

fof(f723,plain,
    ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))),k6_partfun1(u1_struct_0(sK0)),k7_tmap_1(sK0,u1_struct_0(sK1)))
    | k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0))
    | ~ m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | ~ v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_52 ),
    inference(subsumption_resolution,[],[f722,f117])).

fof(f117,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f115])).

fof(f722,plain,
    ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))),k6_partfun1(u1_struct_0(sK0)),k7_tmap_1(sK0,u1_struct_0(sK1)))
    | k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0))
    | ~ m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | ~ v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_7
    | ~ spl4_52 ),
    inference(subsumption_resolution,[],[f721,f148])).

fof(f721,plain,
    ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))),k6_partfun1(u1_struct_0(sK0)),k7_tmap_1(sK0,u1_struct_0(sK1)))
    | k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0))
    | ~ m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | ~ v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ v1_funct_1(k6_partfun1(u1_struct_0(sK0)))
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_52 ),
    inference(superposition,[],[f67,f714])).

fof(f714,plain,
    ( u1_struct_0(sK1) = sK3(sK0,sK1,k6_partfun1(u1_struct_0(sK0)))
    | ~ spl4_52 ),
    inference(avatar_component_clause,[],[f712])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK3(X0,X1,X2))),X2,k7_tmap_1(X0,sK3(X0,X1,X2)))
      | k9_tmap_1(X0,X1) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k9_tmap_1(X0,X1) = X2
                  | ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK3(X0,X1,X2))),X2,k7_tmap_1(X0,sK3(X0,X1,X2)))
                    & u1_struct_0(X1) = sK3(X0,X1,X2)
                    & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4))
                      | u1_struct_0(X1) != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k9_tmap_1(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              | ~ v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f47,f48])).

fof(f48,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
          & u1_struct_0(X1) = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK3(X0,X1,X2))),X2,k7_tmap_1(X0,sK3(X0,X1,X2)))
        & u1_struct_0(X1) = sK3(X0,X1,X2)
        & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k9_tmap_1(X0,X1) = X2
                  | ? [X3] :
                      ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
                      & u1_struct_0(X1) = X3
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4))
                      | u1_struct_0(X1) != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k9_tmap_1(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              | ~ v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k9_tmap_1(X0,X1) = X2
                  | ? [X3] :
                      ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
                      & u1_struct_0(X1) = X3
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X3] :
                      ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
                      | u1_struct_0(X1) != X3
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k9_tmap_1(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              | ~ v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k9_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
                    | u1_struct_0(X1) != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              | ~ v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k9_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))
                    | u1_struct_0(X1) != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
              | ~ v1_funct_1(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
                & v1_funct_1(X2) )
             => ( k9_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( u1_struct_0(X1) = X3
                     => r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_tmap_1)).

fof(f716,plain,
    ( k8_tmap_1(sK0,sK1) != k6_tmap_1(sK0,u1_struct_0(sK1))
    | k9_tmap_1(sK0,sK1) != k6_partfun1(u1_struct_0(sK0))
    | v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,u1_struct_0(sK1)),k6_partfun1(u1_struct_0(sK0)),sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f715,plain,
    ( spl4_51
    | spl4_52
    | ~ spl4_7
    | ~ spl4_30
    | ~ spl4_31
    | ~ spl4_50 ),
    inference(avatar_split_clause,[],[f706,f700,f464,f422,f146,f712,f708])).

fof(f700,plain,
    ( spl4_50
  <=> ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | u1_struct_0(sK1) = sK3(sK0,sK1,X2)
        | k9_tmap_1(sK0,sK1) = X2
        | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ v1_funct_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).

fof(f706,plain,
    ( u1_struct_0(sK1) = sK3(sK0,sK1,k6_partfun1(u1_struct_0(sK0)))
    | k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0))
    | ~ spl4_7
    | ~ spl4_30
    | ~ spl4_31
    | ~ spl4_50 ),
    inference(subsumption_resolution,[],[f705,f148])).

fof(f705,plain,
    ( u1_struct_0(sK1) = sK3(sK0,sK1,k6_partfun1(u1_struct_0(sK0)))
    | k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0))
    | ~ v1_funct_1(k6_partfun1(u1_struct_0(sK0)))
    | ~ spl4_30
    | ~ spl4_31
    | ~ spl4_50 ),
    inference(subsumption_resolution,[],[f704,f424])).

fof(f704,plain,
    ( u1_struct_0(sK1) = sK3(sK0,sK1,k6_partfun1(u1_struct_0(sK0)))
    | k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0))
    | ~ v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ v1_funct_1(k6_partfun1(u1_struct_0(sK0)))
    | ~ spl4_31
    | ~ spl4_50 ),
    inference(resolution,[],[f701,f466])).

fof(f701,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | u1_struct_0(sK1) = sK3(sK0,sK1,X2)
        | k9_tmap_1(sK0,sK1) = X2
        | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ v1_funct_1(X2) )
    | ~ spl4_50 ),
    inference(avatar_component_clause,[],[f700])).

fof(f702,plain,
    ( spl4_50
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_21 ),
    inference(avatar_split_clause,[],[f339,f300,f115,f105,f100,f95,f700])).

fof(f339,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | u1_struct_0(sK1) = sK3(sK0,sK1,X2)
        | k9_tmap_1(sK0,sK1) = X2
        | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ v1_funct_1(X2) )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f338,f97])).

fof(f338,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | u1_struct_0(sK1) = sK3(sK0,sK1,X2)
        | k9_tmap_1(sK0,sK1) = X2
        | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ v1_funct_1(X2)
        | v2_struct_0(sK0) )
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f337,f102])).

fof(f337,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | u1_struct_0(sK1) = sK3(sK0,sK1,X2)
        | k9_tmap_1(sK0,sK1) = X2
        | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ v1_funct_1(X2)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f336,f107])).

fof(f336,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | u1_struct_0(sK1) = sK3(sK0,sK1,X2)
        | k9_tmap_1(sK0,sK1) = X2
        | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ v1_funct_1(X2)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_5
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f307,f117])).

fof(f307,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        | u1_struct_0(sK1) = sK3(sK0,sK1,X2)
        | k9_tmap_1(sK0,sK1) = X2
        | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK0))
        | ~ v1_funct_1(X2)
        | ~ m1_pre_topc(sK1,sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_21 ),
    inference(superposition,[],[f66,f302])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))))
      | u1_struct_0(X1) = sK3(X0,X1,X2)
      | k9_tmap_1(X0,X1) = X2
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f535,plain,
    ( ~ spl4_3
    | spl4_37 ),
    inference(avatar_contradiction_clause,[],[f534])).

fof(f534,plain,
    ( $false
    | ~ spl4_3
    | spl4_37 ),
    inference(subsumption_resolution,[],[f532,f107])).

fof(f532,plain,
    ( ~ l1_pre_topc(sK0)
    | spl4_37 ),
    inference(resolution,[],[f523,f57])).

fof(f57,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f523,plain,
    ( ~ l1_struct_0(sK0)
    | spl4_37 ),
    inference(avatar_component_clause,[],[f521])).

fof(f521,plain,
    ( spl4_37
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f524,plain,
    ( ~ spl4_37
    | spl4_1
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f519,f199,f95,f521])).

fof(f519,plain,
    ( ~ l1_struct_0(sK0)
    | spl4_1
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f518,f97])).

fof(f518,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_11 ),
    inference(resolution,[],[f200,f59])).

fof(f59,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f200,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f199])).

fof(f467,plain,
    ( spl4_31
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_6
    | ~ spl4_14
    | ~ spl4_21
    | ~ spl4_29 ),
    inference(avatar_split_clause,[],[f462,f418,f300,f240,f130,f105,f100,f95,f464])).

fof(f418,plain,
    ( spl4_29
  <=> m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f462,plain,
    ( m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_6
    | ~ spl4_14
    | ~ spl4_21
    | ~ spl4_29 ),
    inference(subsumption_resolution,[],[f367,f419])).

fof(f419,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_29 ),
    inference(avatar_component_clause,[],[f418])).

fof(f367,plain,
    ( m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_6
    | ~ spl4_14
    | ~ spl4_21 ),
    inference(forward_demodulation,[],[f366,f132])).

fof(f366,plain,
    ( m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_14
    | ~ spl4_21 ),
    inference(forward_demodulation,[],[f365,f302])).

fof(f365,plain,
    ( m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f364,f97])).

fof(f364,plain,
    ( m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f363,f102])).

fof(f363,plain,
    ( m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_3
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f354,f107])).

fof(f354,plain,
    ( m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_14 ),
    inference(superposition,[],[f81,f242])).

fof(f81,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_tmap_1)).

fof(f435,plain,
    ( ~ spl4_3
    | ~ spl4_5
    | spl4_29 ),
    inference(avatar_contradiction_clause,[],[f434])).

fof(f434,plain,
    ( $false
    | ~ spl4_3
    | ~ spl4_5
    | spl4_29 ),
    inference(subsumption_resolution,[],[f433,f107])).

fof(f433,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl4_5
    | spl4_29 ),
    inference(subsumption_resolution,[],[f431,f117])).

fof(f431,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | spl4_29 ),
    inference(resolution,[],[f420,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f420,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_29 ),
    inference(avatar_component_clause,[],[f418])).

fof(f425,plain,
    ( ~ spl4_29
    | spl4_30
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_6
    | ~ spl4_14
    | ~ spl4_21 ),
    inference(avatar_split_clause,[],[f372,f300,f240,f130,f105,f100,f95,f422,f418])).

fof(f372,plain,
    ( v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_6
    | ~ spl4_14
    | ~ spl4_21 ),
    inference(forward_demodulation,[],[f371,f132])).

fof(f371,plain,
    ( v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_14
    | ~ spl4_21 ),
    inference(forward_demodulation,[],[f370,f302])).

fof(f370,plain,
    ( v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f369,f97])).

fof(f369,plain,
    ( v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f368,f102])).

fof(f368,plain,
    ( v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_3
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f355,f107])).

fof(f355,plain,
    ( v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_14 ),
    inference(superposition,[],[f80,f242])).

fof(f80,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f413,plain,
    ( spl4_28
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_14
    | ~ spl4_21 ),
    inference(avatar_split_clause,[],[f362,f300,f240,f130,f115,f110,f105,f100,f95,f410])).

fof(f410,plain,
    ( spl4_28
  <=> v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK1),u1_struct_0(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f110,plain,
    ( spl4_4
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f362,plain,
    ( v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_14
    | ~ spl4_21 ),
    inference(forward_demodulation,[],[f361,f132])).

fof(f361,plain,
    ( v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | spl4_4
    | ~ spl4_5
    | ~ spl4_14
    | ~ spl4_21 ),
    inference(forward_demodulation,[],[f360,f302])).

fof(f360,plain,
    ( v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),sK1),u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | spl4_4
    | ~ spl4_5
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f359,f97])).

fof(f359,plain,
    ( v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),sK1),u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | v2_struct_0(sK0)
    | ~ spl4_2
    | ~ spl4_3
    | spl4_4
    | ~ spl4_5
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f358,f102])).

fof(f358,plain,
    ( v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),sK1),u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_3
    | spl4_4
    | ~ spl4_5
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f357,f107])).

fof(f357,plain,
    ( v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),sK1),u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_4
    | ~ spl4_5
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f356,f112])).

fof(f112,plain,
    ( ~ v2_struct_0(sK1)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f110])).

fof(f356,plain,
    ( v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),sK1),u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_5
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f353,f117])).

fof(f353,plain,
    ( v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),sK1),u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_14 ),
    inference(superposition,[],[f244,f242])).

fof(f244,plain,(
    ! [X2,X0] :
      ( v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X2)),k7_tmap_1(X0,u1_struct_0(X2)),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X2))))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f90,f58])).

fof(f90,plain,(
    ! [X2,X0] :
      ( v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X2)),k7_tmap_1(X0,u1_struct_0(X2)),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X2))))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))
      | u1_struct_0(X2) != X1
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))))
                & v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
                & v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))
                & v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)) )
              | u1_struct_0(X2) != X1
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))))
                & v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
                & v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))
                & v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)) )
              | u1_struct_0(X2) != X1
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( u1_struct_0(X2) = X1
               => ( m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))))
                  & v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
                  & v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))
                  & v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_tmap_1)).

fof(f408,plain,
    ( spl4_27
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_14
    | ~ spl4_21 ),
    inference(avatar_split_clause,[],[f403,f300,f240,f130,f115,f110,f105,f100,f95,f405])).

fof(f405,plain,
    ( spl4_27
  <=> m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f403,plain,
    ( m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_14
    | ~ spl4_21 ),
    inference(forward_demodulation,[],[f402,f302])).

fof(f402,plain,
    ( m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_14 ),
    inference(forward_demodulation,[],[f272,f242])).

fof(f272,plain,
    ( m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,u1_struct_0(sK1)),k6_partfun1(u1_struct_0(sK0)),sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))))))
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | spl4_4
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(forward_demodulation,[],[f271,f132])).

fof(f271,plain,
    ( m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,u1_struct_0(sK1)),k7_tmap_1(sK0,u1_struct_0(sK1)),sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))))))
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f270,f97])).

fof(f270,plain,
    ( m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,u1_struct_0(sK1)),k7_tmap_1(sK0,u1_struct_0(sK1)),sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))))))
    | v2_struct_0(sK0)
    | ~ spl4_2
    | ~ spl4_3
    | spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f269,f102])).

fof(f269,plain,
    ( m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,u1_struct_0(sK1)),k7_tmap_1(sK0,u1_struct_0(sK1)),sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))))))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_3
    | spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f268,f107])).

fof(f268,plain,
    ( m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,u1_struct_0(sK1)),k7_tmap_1(sK0,u1_struct_0(sK1)),sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f267,f112])).

fof(f267,plain,
    ( m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,u1_struct_0(sK1)),k7_tmap_1(sK0,u1_struct_0(sK1)),sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))))))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_5 ),
    inference(resolution,[],[f265,f117])).

fof(f265,plain,(
    ! [X2,X0] :
      ( ~ m1_pre_topc(X2,X0)
      | m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X2)),k7_tmap_1(X0,u1_struct_0(X2)),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X2))))))
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f88,f58])).

fof(f88,plain,(
    ! [X2,X0] :
      ( m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X2)),k7_tmap_1(X0,u1_struct_0(X2)),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X2))))))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1)))))
      | u1_struct_0(X2) != X1
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f387,plain,
    ( spl4_24
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f382,f240,f130,f115,f110,f105,f100,f95,f384])).

fof(f384,plain,
    ( spl4_24
  <=> v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK1),sK1,k8_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f382,plain,
    ( v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK1),sK1,k8_tmap_1(sK0,sK1))
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_14 ),
    inference(forward_demodulation,[],[f221,f242])).

fof(f221,plain,
    ( v5_pre_topc(k2_tmap_1(sK0,k6_tmap_1(sK0,u1_struct_0(sK1)),k6_partfun1(u1_struct_0(sK0)),sK1),sK1,k6_tmap_1(sK0,u1_struct_0(sK1)))
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | spl4_4
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(forward_demodulation,[],[f220,f132])).

fof(f220,plain,
    ( v5_pre_topc(k2_tmap_1(sK0,k6_tmap_1(sK0,u1_struct_0(sK1)),k7_tmap_1(sK0,u1_struct_0(sK1)),sK1),sK1,k6_tmap_1(sK0,u1_struct_0(sK1)))
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f219,f97])).

fof(f219,plain,
    ( v5_pre_topc(k2_tmap_1(sK0,k6_tmap_1(sK0,u1_struct_0(sK1)),k7_tmap_1(sK0,u1_struct_0(sK1)),sK1),sK1,k6_tmap_1(sK0,u1_struct_0(sK1)))
    | v2_struct_0(sK0)
    | ~ spl4_2
    | ~ spl4_3
    | spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f218,f102])).

fof(f218,plain,
    ( v5_pre_topc(k2_tmap_1(sK0,k6_tmap_1(sK0,u1_struct_0(sK1)),k7_tmap_1(sK0,u1_struct_0(sK1)),sK1),sK1,k6_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_3
    | spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f217,f107])).

fof(f217,plain,
    ( v5_pre_topc(k2_tmap_1(sK0,k6_tmap_1(sK0,u1_struct_0(sK1)),k7_tmap_1(sK0,u1_struct_0(sK1)),sK1),sK1,k6_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f216,f112])).

fof(f216,plain,
    ( v5_pre_topc(k2_tmap_1(sK0,k6_tmap_1(sK0,u1_struct_0(sK1)),k7_tmap_1(sK0,u1_struct_0(sK1)),sK1),sK1,k6_tmap_1(sK0,u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_5 ),
    inference(resolution,[],[f215,f117])).

fof(f215,plain,(
    ! [X2,X0] :
      ( ~ m1_pre_topc(X2,X0)
      | v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X2)),k7_tmap_1(X0,u1_struct_0(X2)),X2),X2,k6_tmap_1(X0,u1_struct_0(X2)))
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f89,f58])).

fof(f89,plain,(
    ! [X2,X0] :
      ( v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X2)),k7_tmap_1(X0,u1_struct_0(X2)),X2),X2,k6_tmap_1(X0,u1_struct_0(X2)))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1))
      | u1_struct_0(X2) != X1
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f303,plain,
    ( spl4_21
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f238,f165,f115,f105,f100,f95,f300])).

fof(f165,plain,
    ( spl4_8
  <=> u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f238,plain,
    ( u1_struct_0(k8_tmap_1(sK0,sK1)) = u1_struct_0(sK0)
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_8 ),
    inference(backward_demodulation,[],[f167,f234])).

fof(f234,plain,
    ( k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f233,f97])).

fof(f233,plain,
    ( k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f232,f102])).

fof(f232,plain,
    ( k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f231,f107])).

fof(f231,plain,
    ( k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_5 ),
    inference(resolution,[],[f230,f117])).

fof(f230,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f229,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_tmap_1)).

fof(f229,plain,(
    ! [X0,X1] :
      ( k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1))
      | ~ v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f228,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f228,plain,(
    ! [X0,X1] :
      ( k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1))
      | ~ v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f227,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f227,plain,(
    ! [X0,X1] :
      ( k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1))
      | ~ l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f85,f58])).

fof(f85,plain,(
    ! [X0,X1] :
      ( k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(k8_tmap_1(X0,X1))
      | ~ v2_pre_topc(k8_tmap_1(X0,X1))
      | ~ v1_pre_topc(k8_tmap_1(X0,X1))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( k6_tmap_1(X0,u1_struct_0(X1)) = X2
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | k8_tmap_1(X0,X1) != X2
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ v1_pre_topc(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X4,X2,X0,X1] :
      ( k6_tmap_1(X0,X4) = X2
      | u1_struct_0(X1) != X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | k8_tmap_1(X0,X1) != X2
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ v1_pre_topc(X2)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k8_tmap_1(X0,X1) = X2
                  | ( k6_tmap_1(X0,sK2(X0,X1,X2)) != X2
                    & u1_struct_0(X1) = sK2(X0,X1,X2)
                    & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( k6_tmap_1(X0,X4) = X2
                      | u1_struct_0(X1) != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k8_tmap_1(X0,X1) != X2 ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f43,f44])).

fof(f44,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k6_tmap_1(X0,X3) != X2
          & u1_struct_0(X1) = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k6_tmap_1(X0,sK2(X0,X1,X2)) != X2
        & u1_struct_0(X1) = sK2(X0,X1,X2)
        & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k8_tmap_1(X0,X1) = X2
                  | ? [X3] :
                      ( k6_tmap_1(X0,X3) != X2
                      & u1_struct_0(X1) = X3
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( k6_tmap_1(X0,X4) = X2
                      | u1_struct_0(X1) != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k8_tmap_1(X0,X1) != X2 ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k8_tmap_1(X0,X1) = X2
                  | ? [X3] :
                      ( k6_tmap_1(X0,X3) != X2
                      & u1_struct_0(X1) = X3
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X3] :
                      ( k6_tmap_1(X0,X3) = X2
                      | u1_struct_0(X1) != X3
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | k8_tmap_1(X0,X1) != X2 ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k8_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( k6_tmap_1(X0,X3) = X2
                    | u1_struct_0(X1) != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k8_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( k6_tmap_1(X0,X3) = X2
                    | u1_struct_0(X1) != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | ~ v1_pre_topc(X2) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2)
                & v1_pre_topc(X2) )
             => ( k8_tmap_1(X0,X1) = X2
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( u1_struct_0(X1) = X3
                     => k6_tmap_1(X0,X3) = X2 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_tmap_1)).

fof(f167,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f165])).

fof(f297,plain,
    ( ~ spl4_17
    | ~ spl4_18
    | ~ spl4_19
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f56,f294,f290,f286,f282])).

fof(f282,plain,
    ( spl4_17
  <=> v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f286,plain,
    ( spl4_18
  <=> v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK1),u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f290,plain,
    ( spl4_19
  <=> v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK1),sK1,k8_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f294,plain,
    ( spl4_20
  <=> m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK0,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f56,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK0,sK1)))))
    | ~ v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK1),sK1,k8_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK1),u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK0,sK1)))
    | ~ v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK1)) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
    ( ( ~ m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK0,sK1)))))
      | ~ v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK1),sK1,k8_tmap_1(sK0,sK1))
      | ~ v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK1),u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK0,sK1)))
      | ~ v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK1)) )
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f40,f39])).

% (7044)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
fof(f39,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X0,X1)))))
              | ~ v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X1,k8_tmap_1(X0,X1))
              | ~ v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X0,X1)))
              | ~ v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1)) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,X1),k9_tmap_1(sK0,X1),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(sK0,X1)))))
            | ~ v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,X1),k9_tmap_1(sK0,X1),X1),X1,k8_tmap_1(sK0,X1))
            | ~ v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,X1),k9_tmap_1(sK0,X1),X1),u1_struct_0(X1),u1_struct_0(k8_tmap_1(sK0,X1)))
            | ~ v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,X1),k9_tmap_1(sK0,X1),X1)) )
          & m1_pre_topc(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X1] :
        ( ( ~ m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,X1),k9_tmap_1(sK0,X1),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(sK0,X1)))))
          | ~ v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,X1),k9_tmap_1(sK0,X1),X1),X1,k8_tmap_1(sK0,X1))
          | ~ v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,X1),k9_tmap_1(sK0,X1),X1),u1_struct_0(X1),u1_struct_0(k8_tmap_1(sK0,X1)))
          | ~ v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,X1),k9_tmap_1(sK0,X1),X1)) )
        & m1_pre_topc(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ( ~ m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK0,sK1)))))
        | ~ v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK1),sK1,k8_tmap_1(sK0,sK1))
        | ~ v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK1),u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK0,sK1)))
        | ~ v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK1)) )
      & m1_pre_topc(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X0,X1)))))
            | ~ v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X1,k8_tmap_1(X0,X1))
            | ~ v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X0,X1)))
            | ~ v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1)) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X0,X1)))))
            | ~ v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X1,k8_tmap_1(X0,X1))
            | ~ v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X0,X1)))
            | ~ v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1)) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ( m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X0,X1)))))
              & v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X1,k8_tmap_1(X0,X1))
              & v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X0,X1)))
              & v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1)) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ( m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X0,X1)))))
            & v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X1,k8_tmap_1(X0,X1))
            & v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X0,X1)))
            & v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_tmap_1)).

fof(f243,plain,
    ( spl4_14
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f234,f115,f105,f100,f95,f240])).

fof(f226,plain,
    ( spl4_13
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | spl4_4
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f208,f130,f115,f110,f105,f100,f95,f223])).

fof(f223,plain,
    ( spl4_13
  <=> v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,u1_struct_0(sK1)),k6_partfun1(u1_struct_0(sK0)),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f208,plain,
    ( v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,u1_struct_0(sK1)),k6_partfun1(u1_struct_0(sK0)),sK1))
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | spl4_4
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(forward_demodulation,[],[f207,f132])).

fof(f207,plain,
    ( v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,u1_struct_0(sK1)),k7_tmap_1(sK0,u1_struct_0(sK1)),sK1))
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f206,f97])).

fof(f206,plain,
    ( v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,u1_struct_0(sK1)),k7_tmap_1(sK0,u1_struct_0(sK1)),sK1))
    | v2_struct_0(sK0)
    | ~ spl4_2
    | ~ spl4_3
    | spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f205,f102])).

fof(f205,plain,
    ( v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,u1_struct_0(sK1)),k7_tmap_1(sK0,u1_struct_0(sK1)),sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_3
    | spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f204,f107])).

fof(f204,plain,
    ( v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,u1_struct_0(sK1)),k7_tmap_1(sK0,u1_struct_0(sK1)),sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f203,f112])).

fof(f203,plain,
    ( v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,u1_struct_0(sK1)),k7_tmap_1(sK0,u1_struct_0(sK1)),sK1))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_5 ),
    inference(resolution,[],[f189,f117])).

fof(f189,plain,(
    ! [X2,X0] :
      ( ~ m1_pre_topc(X2,X0)
      | v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X2)),k7_tmap_1(X0,u1_struct_0(X2)),X2))
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f91,f58])).

fof(f91,plain,(
    ! [X2,X0] :
      ( v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X2)),k7_tmap_1(X0,u1_struct_0(X2)),X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2))
      | u1_struct_0(X2) != X1
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f168,plain,
    ( spl4_8
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f160,f115,f105,f100,f95,f165])).

fof(f160,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f159,f97])).

fof(f159,plain,
    ( v2_struct_0(sK0)
    | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f158,f102])).

fof(f158,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f157,f107])).

fof(f157,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))
    | ~ spl4_5 ),
    inference(resolution,[],[f128,f117])).

fof(f128,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))) ) ),
    inference(duplicate_literal_removal,[],[f127])).

fof(f127,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f69,f58])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_tmap_1)).

fof(f149,plain,
    ( spl4_7
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f140,f130,f115,f105,f100,f95,f146])).

fof(f140,plain,
    ( v1_funct_1(k6_partfun1(u1_struct_0(sK0)))
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f139,f117])).

fof(f139,plain,
    ( v1_funct_1(k6_partfun1(u1_struct_0(sK0)))
    | ~ m1_pre_topc(sK1,sK0)
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f138,f97])).

fof(f138,plain,
    ( v1_funct_1(k6_partfun1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f137,f102])).

fof(f137,plain,
    ( v1_funct_1(k6_partfun1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ spl4_3
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f136,f107])).

fof(f136,plain,
    ( v1_funct_1(k6_partfun1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ spl4_6 ),
    inference(superposition,[],[f120,f132])).

fof(f120,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_tmap_1(X0,u1_struct_0(X1)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,X0) ) ),
    inference(duplicate_literal_removal,[],[f119])).

fof(f119,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_tmap_1(X0,u1_struct_0(X1)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f79,f58])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_funct_1(k7_tmap_1(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f133,plain,
    ( spl4_6
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f126,f115,f105,f100,f95,f130])).

fof(f126,plain,
    ( k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f125,f97])).

fof(f125,plain,
    ( v2_struct_0(sK0)
    | k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f124,f102])).

fof(f124,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f123,f107])).

fof(f123,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(sK0,u1_struct_0(sK1))
    | ~ spl4_5 ),
    inference(resolution,[],[f122,f117])).

fof(f122,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | k6_partfun1(u1_struct_0(X0)) = k7_tmap_1(X0,u1_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f121])).

fof(f121,plain,(
    ! [X0,X1] :
      ( k6_partfun1(u1_struct_0(X0)) = k7_tmap_1(X0,u1_struct_0(X1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f68,f58])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_tmap_1)).

fof(f118,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f55,f115])).

fof(f55,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f113,plain,(
    ~ spl4_4 ),
    inference(avatar_split_clause,[],[f54,f110])).

fof(f54,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f108,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f53,f105])).

fof(f53,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f103,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f52,f100])).

fof(f52,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f98,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f51,f95])).

fof(f51,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f41])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.36  % Computer   : n023.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 18:36:20 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.23/0.52  % (7037)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.23/0.53  % (7031)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.23/0.54  % (7056)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.23/0.54  % (7033)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.23/0.54  % (7037)Refutation not found, incomplete strategy% (7037)------------------------------
% 0.23/0.54  % (7037)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.54  % (7037)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.54  
% 0.23/0.54  % (7037)Memory used [KB]: 10618
% 0.23/0.54  % (7037)Time elapsed: 0.107 s
% 0.23/0.54  % (7037)------------------------------
% 0.23/0.54  % (7037)------------------------------
% 0.23/0.54  % (7032)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.23/0.55  % (7031)Refutation not found, incomplete strategy% (7031)------------------------------
% 0.23/0.55  % (7031)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.55  % (7031)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.55  
% 0.23/0.55  % (7031)Memory used [KB]: 10746
% 0.23/0.55  % (7031)Time elapsed: 0.107 s
% 0.23/0.55  % (7031)------------------------------
% 0.23/0.55  % (7031)------------------------------
% 0.23/0.55  % (7038)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.23/0.55  % (7053)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.23/0.55  % (7036)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.23/0.55  % (7045)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.23/0.55  % (7035)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.23/0.55  % (7054)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.23/0.56  % (7042)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.23/0.56  % (7051)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.23/0.56  % (7039)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.23/0.56  % (7049)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.23/0.56  % (7046)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.23/0.57  % (7038)Refutation not found, incomplete strategy% (7038)------------------------------
% 0.23/0.57  % (7038)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.57  % (7038)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.57  
% 0.23/0.57  % (7038)Memory used [KB]: 1791
% 0.23/0.57  % (7038)Time elapsed: 0.074 s
% 0.23/0.57  % (7038)------------------------------
% 0.23/0.57  % (7038)------------------------------
% 0.23/0.58  % (7036)Refutation not found, incomplete strategy% (7036)------------------------------
% 0.23/0.58  % (7036)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.58  % (7036)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.58  
% 0.23/0.58  % (7036)Memory used [KB]: 6140
% 0.23/0.58  % (7036)Time elapsed: 0.119 s
% 0.23/0.58  % (7036)------------------------------
% 0.23/0.58  % (7036)------------------------------
% 0.23/0.58  % (7034)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.23/0.58  % (7033)Refutation found. Thanks to Tanya!
% 0.23/0.58  % SZS status Theorem for theBenchmark
% 1.54/0.59  % (7041)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.54/0.59  % SZS output start Proof for theBenchmark
% 1.54/0.59  fof(f805,plain,(
% 1.54/0.59    $false),
% 1.54/0.59    inference(avatar_sat_refutation,[],[f98,f103,f108,f113,f118,f133,f149,f168,f226,f243,f297,f303,f387,f408,f413,f425,f435,f467,f524,f535,f702,f715,f716,f791,f801,f802,f803,f804])).
% 1.54/0.59  fof(f804,plain,(
% 1.54/0.59    k9_tmap_1(sK0,sK1) != k6_partfun1(u1_struct_0(sK0)) | k8_tmap_1(sK0,sK1) != k6_tmap_1(sK0,u1_struct_0(sK1)) | u1_struct_0(sK0) != u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))) | m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK0,sK1))))) | ~m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 1.54/0.59    introduced(theory_tautology_sat_conflict,[])).
% 1.54/0.59  fof(f803,plain,(
% 1.54/0.59    k8_tmap_1(sK0,sK1) != k6_tmap_1(sK0,u1_struct_0(sK1)) | k9_tmap_1(sK0,sK1) != k6_partfun1(u1_struct_0(sK0)) | v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK1),sK1,k8_tmap_1(sK0,sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK1),sK1,k8_tmap_1(sK0,sK1))),
% 1.54/0.59    introduced(theory_tautology_sat_conflict,[])).
% 1.54/0.59  fof(f802,plain,(
% 1.54/0.59    k9_tmap_1(sK0,sK1) != k6_partfun1(u1_struct_0(sK0)) | k8_tmap_1(sK0,sK1) != k6_tmap_1(sK0,u1_struct_0(sK1)) | u1_struct_0(sK0) != u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))) | v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK1),u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK1),u1_struct_0(sK1),u1_struct_0(sK0))),
% 1.54/0.59    introduced(theory_tautology_sat_conflict,[])).
% 1.54/0.59  fof(f801,plain,(
% 1.54/0.59    ~spl4_7 | spl4_11 | ~spl4_30 | ~spl4_31 | spl4_62),
% 1.54/0.59    inference(avatar_contradiction_clause,[],[f800])).
% 1.54/0.59  fof(f800,plain,(
% 1.54/0.59    $false | (~spl4_7 | spl4_11 | ~spl4_30 | ~spl4_31 | spl4_62)),
% 1.54/0.59    inference(subsumption_resolution,[],[f799,f201])).
% 1.54/0.59  fof(f201,plain,(
% 1.54/0.59    ~v1_xboole_0(u1_struct_0(sK0)) | spl4_11),
% 1.54/0.59    inference(avatar_component_clause,[],[f199])).
% 1.54/0.59  fof(f199,plain,(
% 1.54/0.59    spl4_11 <=> v1_xboole_0(u1_struct_0(sK0))),
% 1.54/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 1.54/0.59  fof(f799,plain,(
% 1.54/0.59    v1_xboole_0(u1_struct_0(sK0)) | (~spl4_7 | ~spl4_30 | ~spl4_31 | spl4_62)),
% 1.54/0.59    inference(subsumption_resolution,[],[f798,f148])).
% 1.54/0.59  fof(f148,plain,(
% 1.54/0.59    v1_funct_1(k6_partfun1(u1_struct_0(sK0))) | ~spl4_7),
% 1.54/0.59    inference(avatar_component_clause,[],[f146])).
% 1.54/0.59  fof(f146,plain,(
% 1.54/0.59    spl4_7 <=> v1_funct_1(k6_partfun1(u1_struct_0(sK0)))),
% 1.54/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.54/0.59  fof(f798,plain,(
% 1.54/0.59    ~v1_funct_1(k6_partfun1(u1_struct_0(sK0))) | v1_xboole_0(u1_struct_0(sK0)) | (~spl4_30 | ~spl4_31 | spl4_62)),
% 1.54/0.59    inference(subsumption_resolution,[],[f797,f424])).
% 1.54/0.59  fof(f424,plain,(
% 1.54/0.59    v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)) | ~spl4_30),
% 1.54/0.59    inference(avatar_component_clause,[],[f422])).
% 1.54/0.59  fof(f422,plain,(
% 1.54/0.59    spl4_30 <=> v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0))),
% 1.54/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 1.54/0.59  fof(f797,plain,(
% 1.54/0.59    ~v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(k6_partfun1(u1_struct_0(sK0))) | v1_xboole_0(u1_struct_0(sK0)) | (~spl4_31 | spl4_62)),
% 1.54/0.59    inference(subsumption_resolution,[],[f795,f466])).
% 1.54/0.59  fof(f466,plain,(
% 1.54/0.59    m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~spl4_31),
% 1.54/0.59    inference(avatar_component_clause,[],[f464])).
% 1.54/0.59  fof(f464,plain,(
% 1.54/0.59    spl4_31 <=> m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))),
% 1.54/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).
% 1.54/0.59  fof(f795,plain,(
% 1.54/0.59    ~m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(k6_partfun1(u1_struct_0(sK0))) | v1_xboole_0(u1_struct_0(sK0)) | spl4_62),
% 1.54/0.59    inference(duplicate_literal_removal,[],[f794])).
% 1.54/0.59  fof(f794,plain,(
% 1.54/0.59    ~m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(k6_partfun1(u1_struct_0(sK0))) | ~m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | spl4_62),
% 1.54/0.59    inference(resolution,[],[f790,f93])).
% 1.54/0.59  fof(f93,plain,(
% 1.54/0.59    ( ! [X2,X0,X5,X3,X1] : (r1_funct_2(X0,X1,X2,X3,X5,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X5,X0,X1) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 1.54/0.59    inference(duplicate_literal_removal,[],[f92])).
% 1.54/0.59  fof(f92,plain,(
% 1.54/0.59    ( ! [X2,X0,X5,X3,X1] : (r1_funct_2(X0,X1,X2,X3,X5,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X5,X0,X1) | ~v1_funct_1(X5) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 1.54/0.59    inference(equality_resolution,[],[f83])).
% 1.54/0.59  fof(f83,plain,(
% 1.54/0.59    ( ! [X4,X2,X0,X5,X3,X1] : (r1_funct_2(X0,X1,X2,X3,X4,X5) | X4 != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 1.54/0.59    inference(cnf_transformation,[],[f50])).
% 1.54/0.59  fof(f50,plain,(
% 1.54/0.59    ! [X0,X1,X2,X3,X4,X5] : (((r1_funct_2(X0,X1,X2,X3,X4,X5) | X4 != X5) & (X4 = X5 | ~r1_funct_2(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 1.54/0.59    inference(nnf_transformation,[],[f38])).
% 1.54/0.59  fof(f38,plain,(
% 1.54/0.59    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 1.54/0.59    inference(flattening,[],[f37])).
% 1.54/0.59  fof(f37,plain,(
% 1.54/0.59    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)))),
% 1.54/0.59    inference(ennf_transformation,[],[f4])).
% 1.54/0.59  fof(f4,axiom,(
% 1.54/0.59    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_2(X5,X2,X3) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4) & ~v1_xboole_0(X3) & ~v1_xboole_0(X1)) => (r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5))),
% 1.54/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_funct_2)).
% 1.54/0.59  fof(f790,plain,(
% 1.54/0.59    ~r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k6_partfun1(u1_struct_0(sK0)),k6_partfun1(u1_struct_0(sK0))) | spl4_62),
% 1.54/0.59    inference(avatar_component_clause,[],[f788])).
% 1.54/0.59  fof(f788,plain,(
% 1.54/0.59    spl4_62 <=> r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k6_partfun1(u1_struct_0(sK0)),k6_partfun1(u1_struct_0(sK0)))),
% 1.54/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_62])])).
% 1.54/0.59  fof(f791,plain,(
% 1.54/0.59    spl4_51 | ~spl4_62 | spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_5 | ~spl4_6 | ~spl4_7 | ~spl4_14 | ~spl4_21 | ~spl4_30 | ~spl4_31 | ~spl4_52),
% 1.54/0.59    inference(avatar_split_clause,[],[f733,f712,f464,f422,f300,f240,f146,f130,f115,f105,f100,f95,f788,f708])).
% 1.54/0.59  fof(f708,plain,(
% 1.54/0.59    spl4_51 <=> k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0))),
% 1.54/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_51])])).
% 1.54/0.59  fof(f95,plain,(
% 1.54/0.59    spl4_1 <=> v2_struct_0(sK0)),
% 1.54/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.54/0.59  fof(f100,plain,(
% 1.54/0.59    spl4_2 <=> v2_pre_topc(sK0)),
% 1.54/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.54/0.59  fof(f105,plain,(
% 1.54/0.59    spl4_3 <=> l1_pre_topc(sK0)),
% 1.54/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.54/0.59  fof(f115,plain,(
% 1.54/0.59    spl4_5 <=> m1_pre_topc(sK1,sK0)),
% 1.54/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.54/0.59  fof(f130,plain,(
% 1.54/0.59    spl4_6 <=> k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(sK0,u1_struct_0(sK1))),
% 1.54/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.54/0.59  fof(f240,plain,(
% 1.54/0.59    spl4_14 <=> k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1))),
% 1.54/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 1.54/0.59  fof(f300,plain,(
% 1.54/0.59    spl4_21 <=> u1_struct_0(k8_tmap_1(sK0,sK1)) = u1_struct_0(sK0)),
% 1.54/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 1.54/0.59  fof(f712,plain,(
% 1.54/0.59    spl4_52 <=> u1_struct_0(sK1) = sK3(sK0,sK1,k6_partfun1(u1_struct_0(sK0)))),
% 1.54/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).
% 1.54/0.59  fof(f733,plain,(
% 1.54/0.59    ~r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k6_partfun1(u1_struct_0(sK0)),k6_partfun1(u1_struct_0(sK0))) | k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0)) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_5 | ~spl4_6 | ~spl4_7 | ~spl4_14 | ~spl4_21 | ~spl4_30 | ~spl4_31 | ~spl4_52)),
% 1.54/0.59    inference(subsumption_resolution,[],[f732,f424])).
% 1.54/0.59  fof(f732,plain,(
% 1.54/0.59    ~v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)) | ~r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k6_partfun1(u1_struct_0(sK0)),k6_partfun1(u1_struct_0(sK0))) | k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0)) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_5 | ~spl4_6 | ~spl4_7 | ~spl4_14 | ~spl4_21 | ~spl4_31 | ~spl4_52)),
% 1.54/0.59    inference(forward_demodulation,[],[f731,f302])).
% 1.54/0.59  fof(f302,plain,(
% 1.54/0.59    u1_struct_0(k8_tmap_1(sK0,sK1)) = u1_struct_0(sK0) | ~spl4_21),
% 1.54/0.59    inference(avatar_component_clause,[],[f300])).
% 1.54/0.59  fof(f731,plain,(
% 1.54/0.59    ~r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k6_partfun1(u1_struct_0(sK0)),k6_partfun1(u1_struct_0(sK0))) | k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0)) | ~v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_5 | ~spl4_6 | ~spl4_7 | ~spl4_14 | ~spl4_21 | ~spl4_31 | ~spl4_52)),
% 1.54/0.59    inference(subsumption_resolution,[],[f730,f466])).
% 1.54/0.59  fof(f730,plain,(
% 1.54/0.59    ~m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k6_partfun1(u1_struct_0(sK0)),k6_partfun1(u1_struct_0(sK0))) | k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0)) | ~v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_5 | ~spl4_6 | ~spl4_7 | ~spl4_14 | ~spl4_21 | ~spl4_52)),
% 1.54/0.59    inference(forward_demodulation,[],[f729,f302])).
% 1.54/0.59  fof(f729,plain,(
% 1.54/0.59    ~r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k6_partfun1(u1_struct_0(sK0)),k6_partfun1(u1_struct_0(sK0))) | k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0)) | ~m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | ~v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_5 | ~spl4_6 | ~spl4_7 | ~spl4_14 | ~spl4_21 | ~spl4_52)),
% 1.54/0.59    inference(forward_demodulation,[],[f728,f302])).
% 1.54/0.59  fof(f728,plain,(
% 1.54/0.59    ~r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),k6_partfun1(u1_struct_0(sK0)),k6_partfun1(u1_struct_0(sK0))) | k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0)) | ~m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | ~v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_5 | ~spl4_6 | ~spl4_7 | ~spl4_14 | ~spl4_52)),
% 1.54/0.59    inference(forward_demodulation,[],[f727,f242])).
% 1.54/0.59  fof(f242,plain,(
% 1.54/0.59    k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) | ~spl4_14),
% 1.54/0.59    inference(avatar_component_clause,[],[f240])).
% 1.54/0.59  fof(f727,plain,(
% 1.54/0.59    ~r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))),k6_partfun1(u1_struct_0(sK0)),k6_partfun1(u1_struct_0(sK0))) | k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0)) | ~m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | ~v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_5 | ~spl4_6 | ~spl4_7 | ~spl4_52)),
% 1.54/0.59    inference(forward_demodulation,[],[f726,f132])).
% 1.54/0.59  fof(f132,plain,(
% 1.54/0.59    k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(sK0,u1_struct_0(sK1)) | ~spl4_6),
% 1.54/0.59    inference(avatar_component_clause,[],[f130])).
% 1.54/0.59  fof(f726,plain,(
% 1.54/0.59    ~r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))),k6_partfun1(u1_struct_0(sK0)),k7_tmap_1(sK0,u1_struct_0(sK1))) | k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0)) | ~m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | ~v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_5 | ~spl4_7 | ~spl4_52)),
% 1.54/0.59    inference(subsumption_resolution,[],[f725,f97])).
% 1.54/0.59  fof(f97,plain,(
% 1.54/0.59    ~v2_struct_0(sK0) | spl4_1),
% 1.54/0.59    inference(avatar_component_clause,[],[f95])).
% 1.54/0.59  fof(f725,plain,(
% 1.54/0.59    ~r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))),k6_partfun1(u1_struct_0(sK0)),k7_tmap_1(sK0,u1_struct_0(sK1))) | k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0)) | ~m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | ~v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | v2_struct_0(sK0) | (~spl4_2 | ~spl4_3 | ~spl4_5 | ~spl4_7 | ~spl4_52)),
% 1.54/0.59    inference(subsumption_resolution,[],[f724,f102])).
% 1.54/0.59  fof(f102,plain,(
% 1.54/0.59    v2_pre_topc(sK0) | ~spl4_2),
% 1.54/0.59    inference(avatar_component_clause,[],[f100])).
% 1.54/0.59  fof(f724,plain,(
% 1.54/0.59    ~r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))),k6_partfun1(u1_struct_0(sK0)),k7_tmap_1(sK0,u1_struct_0(sK1))) | k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0)) | ~m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | ~v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl4_3 | ~spl4_5 | ~spl4_7 | ~spl4_52)),
% 1.54/0.59    inference(subsumption_resolution,[],[f723,f107])).
% 1.54/0.59  fof(f107,plain,(
% 1.54/0.59    l1_pre_topc(sK0) | ~spl4_3),
% 1.54/0.59    inference(avatar_component_clause,[],[f105])).
% 1.54/0.59  fof(f723,plain,(
% 1.54/0.59    ~r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))),k6_partfun1(u1_struct_0(sK0)),k7_tmap_1(sK0,u1_struct_0(sK1))) | k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0)) | ~m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | ~v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl4_5 | ~spl4_7 | ~spl4_52)),
% 1.54/0.59    inference(subsumption_resolution,[],[f722,f117])).
% 1.54/0.59  fof(f117,plain,(
% 1.54/0.59    m1_pre_topc(sK1,sK0) | ~spl4_5),
% 1.54/0.59    inference(avatar_component_clause,[],[f115])).
% 1.54/0.59  fof(f722,plain,(
% 1.54/0.59    ~r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))),k6_partfun1(u1_struct_0(sK0)),k7_tmap_1(sK0,u1_struct_0(sK1))) | k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0)) | ~m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | ~v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl4_7 | ~spl4_52)),
% 1.54/0.59    inference(subsumption_resolution,[],[f721,f148])).
% 1.54/0.59  fof(f721,plain,(
% 1.54/0.59    ~r1_funct_2(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))),k6_partfun1(u1_struct_0(sK0)),k7_tmap_1(sK0,u1_struct_0(sK1))) | k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0)) | ~m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | ~v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~v1_funct_1(k6_partfun1(u1_struct_0(sK0))) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl4_52),
% 1.54/0.59    inference(superposition,[],[f67,f714])).
% 1.54/0.59  fof(f714,plain,(
% 1.54/0.59    u1_struct_0(sK1) = sK3(sK0,sK1,k6_partfun1(u1_struct_0(sK0))) | ~spl4_52),
% 1.54/0.59    inference(avatar_component_clause,[],[f712])).
% 1.54/0.59  fof(f67,plain,(
% 1.54/0.59    ( ! [X2,X0,X1] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK3(X0,X1,X2))),X2,k7_tmap_1(X0,sK3(X0,X1,X2))) | k9_tmap_1(X0,X1) = X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.54/0.59    inference(cnf_transformation,[],[f49])).
% 1.54/0.59  fof(f49,plain,(
% 1.54/0.59    ! [X0] : (! [X1] : (! [X2] : (((k9_tmap_1(X0,X1) = X2 | (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK3(X0,X1,X2))),X2,k7_tmap_1(X0,sK3(X0,X1,X2))) & u1_struct_0(X1) = sK3(X0,X1,X2) & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4)) | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k9_tmap_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.54/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f47,f48])).
% 1.54/0.59  fof(f48,plain,(
% 1.54/0.59    ! [X2,X1,X0] : (? [X3] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,sK3(X0,X1,X2))),X2,k7_tmap_1(X0,sK3(X0,X1,X2))) & u1_struct_0(X1) = sK3(X0,X1,X2) & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.54/0.59    introduced(choice_axiom,[])).
% 1.54/0.59  fof(f47,plain,(
% 1.54/0.59    ! [X0] : (! [X1] : (! [X2] : (((k9_tmap_1(X0,X1) = X2 | ? [X3] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X4)),X2,k7_tmap_1(X0,X4)) | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k9_tmap_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.54/0.59    inference(rectify,[],[f46])).
% 1.54/0.59  fof(f46,plain,(
% 1.54/0.59    ! [X0] : (! [X1] : (! [X2] : (((k9_tmap_1(X0,X1) = X2 | ? [X3] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | k9_tmap_1(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.54/0.59    inference(nnf_transformation,[],[f24])).
% 1.54/0.59  fof(f24,plain,(
% 1.54/0.59    ! [X0] : (! [X1] : (! [X2] : ((k9_tmap_1(X0,X1) = X2 <=> ! [X3] : (r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.54/0.59    inference(flattening,[],[f23])).
% 1.54/0.59  fof(f23,plain,(
% 1.54/0.59    ! [X0] : (! [X1] : (! [X2] : ((k9_tmap_1(X0,X1) = X2 <=> ! [X3] : ((r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3)) | u1_struct_0(X1) != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.54/0.59    inference(ennf_transformation,[],[f7])).
% 1.54/0.59  fof(f7,axiom,(
% 1.54/0.59    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(X2)) => (k9_tmap_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X3 => r1_funct_2(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1)),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X3)),X2,k7_tmap_1(X0,X3))))))))),
% 1.54/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_tmap_1)).
% 1.54/0.59  fof(f716,plain,(
% 1.54/0.59    k8_tmap_1(sK0,sK1) != k6_tmap_1(sK0,u1_struct_0(sK1)) | k9_tmap_1(sK0,sK1) != k6_partfun1(u1_struct_0(sK0)) | v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK1)) | ~v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,u1_struct_0(sK1)),k6_partfun1(u1_struct_0(sK0)),sK1))),
% 1.54/0.59    introduced(theory_tautology_sat_conflict,[])).
% 1.54/0.59  fof(f715,plain,(
% 1.54/0.59    spl4_51 | spl4_52 | ~spl4_7 | ~spl4_30 | ~spl4_31 | ~spl4_50),
% 1.54/0.59    inference(avatar_split_clause,[],[f706,f700,f464,f422,f146,f712,f708])).
% 1.54/0.59  fof(f700,plain,(
% 1.54/0.59    spl4_50 <=> ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | u1_struct_0(sK1) = sK3(sK0,sK1,X2) | k9_tmap_1(sK0,sK1) = X2 | ~v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(X2))),
% 1.54/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).
% 1.54/0.59  fof(f706,plain,(
% 1.54/0.59    u1_struct_0(sK1) = sK3(sK0,sK1,k6_partfun1(u1_struct_0(sK0))) | k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0)) | (~spl4_7 | ~spl4_30 | ~spl4_31 | ~spl4_50)),
% 1.54/0.59    inference(subsumption_resolution,[],[f705,f148])).
% 1.54/0.59  fof(f705,plain,(
% 1.54/0.59    u1_struct_0(sK1) = sK3(sK0,sK1,k6_partfun1(u1_struct_0(sK0))) | k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0)) | ~v1_funct_1(k6_partfun1(u1_struct_0(sK0))) | (~spl4_30 | ~spl4_31 | ~spl4_50)),
% 1.54/0.59    inference(subsumption_resolution,[],[f704,f424])).
% 1.54/0.59  fof(f704,plain,(
% 1.54/0.59    u1_struct_0(sK1) = sK3(sK0,sK1,k6_partfun1(u1_struct_0(sK0))) | k9_tmap_1(sK0,sK1) = k6_partfun1(u1_struct_0(sK0)) | ~v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(k6_partfun1(u1_struct_0(sK0))) | (~spl4_31 | ~spl4_50)),
% 1.54/0.59    inference(resolution,[],[f701,f466])).
% 1.54/0.59  fof(f701,plain,(
% 1.54/0.59    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | u1_struct_0(sK1) = sK3(sK0,sK1,X2) | k9_tmap_1(sK0,sK1) = X2 | ~v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(X2)) ) | ~spl4_50),
% 1.54/0.59    inference(avatar_component_clause,[],[f700])).
% 1.54/0.59  fof(f702,plain,(
% 1.54/0.59    spl4_50 | spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_5 | ~spl4_21),
% 1.54/0.59    inference(avatar_split_clause,[],[f339,f300,f115,f105,f100,f95,f700])).
% 1.54/0.59  fof(f339,plain,(
% 1.54/0.59    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | u1_struct_0(sK1) = sK3(sK0,sK1,X2) | k9_tmap_1(sK0,sK1) = X2 | ~v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(X2)) ) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_5 | ~spl4_21)),
% 1.54/0.59    inference(subsumption_resolution,[],[f338,f97])).
% 1.54/0.59  fof(f338,plain,(
% 1.54/0.59    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | u1_struct_0(sK1) = sK3(sK0,sK1,X2) | k9_tmap_1(sK0,sK1) = X2 | ~v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(X2) | v2_struct_0(sK0)) ) | (~spl4_2 | ~spl4_3 | ~spl4_5 | ~spl4_21)),
% 1.54/0.59    inference(subsumption_resolution,[],[f337,f102])).
% 1.54/0.59  fof(f337,plain,(
% 1.54/0.59    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | u1_struct_0(sK1) = sK3(sK0,sK1,X2) | k9_tmap_1(sK0,sK1) = X2 | ~v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(X2) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl4_3 | ~spl4_5 | ~spl4_21)),
% 1.54/0.59    inference(subsumption_resolution,[],[f336,f107])).
% 1.54/0.59  fof(f336,plain,(
% 1.54/0.59    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | u1_struct_0(sK1) = sK3(sK0,sK1,X2) | k9_tmap_1(sK0,sK1) = X2 | ~v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(X2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl4_5 | ~spl4_21)),
% 1.54/0.59    inference(subsumption_resolution,[],[f307,f117])).
% 1.54/0.59  fof(f307,plain,(
% 1.54/0.59    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | u1_struct_0(sK1) = sK3(sK0,sK1,X2) | k9_tmap_1(sK0,sK1) = X2 | ~v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK0)) | ~v1_funct_1(X2) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl4_21),
% 1.54/0.59    inference(superposition,[],[f66,f302])).
% 1.54/0.59  fof(f66,plain,(
% 1.54/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))))) | u1_struct_0(X1) = sK3(X0,X1,X2) | k9_tmap_1(X0,X1) = X2 | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.54/0.59    inference(cnf_transformation,[],[f49])).
% 1.54/0.59  fof(f535,plain,(
% 1.54/0.59    ~spl4_3 | spl4_37),
% 1.54/0.59    inference(avatar_contradiction_clause,[],[f534])).
% 1.54/0.59  fof(f534,plain,(
% 1.54/0.59    $false | (~spl4_3 | spl4_37)),
% 1.54/0.59    inference(subsumption_resolution,[],[f532,f107])).
% 1.54/0.59  fof(f532,plain,(
% 1.54/0.59    ~l1_pre_topc(sK0) | spl4_37),
% 1.54/0.59    inference(resolution,[],[f523,f57])).
% 1.54/0.59  fof(f57,plain,(
% 1.54/0.59    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.54/0.59    inference(cnf_transformation,[],[f17])).
% 1.54/0.59  fof(f17,plain,(
% 1.54/0.59    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.54/0.59    inference(ennf_transformation,[],[f1])).
% 1.54/0.59  fof(f1,axiom,(
% 1.54/0.59    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.54/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.54/0.59  fof(f523,plain,(
% 1.54/0.59    ~l1_struct_0(sK0) | spl4_37),
% 1.54/0.59    inference(avatar_component_clause,[],[f521])).
% 1.54/0.59  fof(f521,plain,(
% 1.54/0.59    spl4_37 <=> l1_struct_0(sK0)),
% 1.54/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).
% 1.54/0.59  fof(f524,plain,(
% 1.54/0.59    ~spl4_37 | spl4_1 | ~spl4_11),
% 1.54/0.59    inference(avatar_split_clause,[],[f519,f199,f95,f521])).
% 1.54/0.59  fof(f519,plain,(
% 1.54/0.59    ~l1_struct_0(sK0) | (spl4_1 | ~spl4_11)),
% 1.54/0.59    inference(subsumption_resolution,[],[f518,f97])).
% 1.54/0.59  fof(f518,plain,(
% 1.54/0.59    ~l1_struct_0(sK0) | v2_struct_0(sK0) | ~spl4_11),
% 1.54/0.59    inference(resolution,[],[f200,f59])).
% 1.54/0.59  fof(f59,plain,(
% 1.54/0.59    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.54/0.59    inference(cnf_transformation,[],[f20])).
% 1.54/0.59  fof(f20,plain,(
% 1.54/0.59    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.54/0.59    inference(flattening,[],[f19])).
% 1.54/0.59  fof(f19,plain,(
% 1.54/0.59    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.54/0.59    inference(ennf_transformation,[],[f3])).
% 1.54/0.59  fof(f3,axiom,(
% 1.54/0.59    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.54/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 1.54/0.59  fof(f200,plain,(
% 1.54/0.59    v1_xboole_0(u1_struct_0(sK0)) | ~spl4_11),
% 1.54/0.59    inference(avatar_component_clause,[],[f199])).
% 1.54/0.59  fof(f467,plain,(
% 1.54/0.59    spl4_31 | spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_6 | ~spl4_14 | ~spl4_21 | ~spl4_29),
% 1.54/0.59    inference(avatar_split_clause,[],[f462,f418,f300,f240,f130,f105,f100,f95,f464])).
% 1.54/0.59  fof(f418,plain,(
% 1.54/0.59    spl4_29 <=> m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.54/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 1.54/0.59  fof(f462,plain,(
% 1.54/0.59    m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_6 | ~spl4_14 | ~spl4_21 | ~spl4_29)),
% 1.54/0.59    inference(subsumption_resolution,[],[f367,f419])).
% 1.54/0.59  fof(f419,plain,(
% 1.54/0.59    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_29),
% 1.54/0.59    inference(avatar_component_clause,[],[f418])).
% 1.54/0.59  fof(f367,plain,(
% 1.54/0.59    m1_subset_1(k6_partfun1(u1_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_6 | ~spl4_14 | ~spl4_21)),
% 1.54/0.59    inference(forward_demodulation,[],[f366,f132])).
% 1.54/0.59  fof(f366,plain,(
% 1.54/0.59    m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_14 | ~spl4_21)),
% 1.54/0.59    inference(forward_demodulation,[],[f365,f302])).
% 1.54/0.59  fof(f365,plain,(
% 1.54/0.59    m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_14)),
% 1.54/0.59    inference(subsumption_resolution,[],[f364,f97])).
% 1.54/0.59  fof(f364,plain,(
% 1.54/0.59    m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (~spl4_2 | ~spl4_3 | ~spl4_14)),
% 1.54/0.59    inference(subsumption_resolution,[],[f363,f102])).
% 1.54/0.59  fof(f363,plain,(
% 1.54/0.59    m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl4_3 | ~spl4_14)),
% 1.54/0.59    inference(subsumption_resolution,[],[f354,f107])).
% 1.54/0.59  fof(f354,plain,(
% 1.54/0.59    m1_subset_1(k7_tmap_1(sK0,u1_struct_0(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))))) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl4_14),
% 1.54/0.59    inference(superposition,[],[f81,f242])).
% 1.54/0.59  fof(f81,plain,(
% 1.54/0.59    ( ! [X0,X1] : (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.54/0.59    inference(cnf_transformation,[],[f36])).
% 1.54/0.59  fof(f36,plain,(
% 1.54/0.59    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.54/0.59    inference(flattening,[],[f35])).
% 1.54/0.59  fof(f35,plain,(
% 1.54/0.59    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.54/0.59    inference(ennf_transformation,[],[f8])).
% 1.54/0.59  fof(f8,axiom,(
% 1.54/0.59    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))))),
% 1.54/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_tmap_1)).
% 1.54/0.59  fof(f435,plain,(
% 1.54/0.59    ~spl4_3 | ~spl4_5 | spl4_29),
% 1.54/0.59    inference(avatar_contradiction_clause,[],[f434])).
% 1.54/0.59  fof(f434,plain,(
% 1.54/0.59    $false | (~spl4_3 | ~spl4_5 | spl4_29)),
% 1.54/0.59    inference(subsumption_resolution,[],[f433,f107])).
% 1.54/0.59  fof(f433,plain,(
% 1.54/0.59    ~l1_pre_topc(sK0) | (~spl4_5 | spl4_29)),
% 1.54/0.59    inference(subsumption_resolution,[],[f431,f117])).
% 1.54/0.59  fof(f431,plain,(
% 1.54/0.59    ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | spl4_29),
% 1.54/0.59    inference(resolution,[],[f420,f58])).
% 1.54/0.59  fof(f58,plain,(
% 1.54/0.59    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.54/0.59    inference(cnf_transformation,[],[f18])).
% 1.54/0.59  fof(f18,plain,(
% 1.54/0.59    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.54/0.59    inference(ennf_transformation,[],[f12])).
% 1.54/0.59  fof(f12,axiom,(
% 1.54/0.59    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.54/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).
% 1.54/0.59  fof(f420,plain,(
% 1.54/0.59    ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl4_29),
% 1.54/0.59    inference(avatar_component_clause,[],[f418])).
% 1.54/0.59  fof(f425,plain,(
% 1.54/0.59    ~spl4_29 | spl4_30 | spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_6 | ~spl4_14 | ~spl4_21),
% 1.54/0.59    inference(avatar_split_clause,[],[f372,f300,f240,f130,f105,f100,f95,f422,f418])).
% 1.54/0.59  fof(f372,plain,(
% 1.54/0.59    v1_funct_2(k6_partfun1(u1_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_6 | ~spl4_14 | ~spl4_21)),
% 1.54/0.59    inference(forward_demodulation,[],[f371,f132])).
% 1.54/0.59  fof(f371,plain,(
% 1.54/0.59    v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_14 | ~spl4_21)),
% 1.54/0.59    inference(forward_demodulation,[],[f370,f302])).
% 1.54/0.59  fof(f370,plain,(
% 1.54/0.59    v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_14)),
% 1.54/0.59    inference(subsumption_resolution,[],[f369,f97])).
% 1.54/0.59  fof(f369,plain,(
% 1.54/0.59    v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | (~spl4_2 | ~spl4_3 | ~spl4_14)),
% 1.54/0.59    inference(subsumption_resolution,[],[f368,f102])).
% 1.54/0.59  fof(f368,plain,(
% 1.54/0.59    v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl4_3 | ~spl4_14)),
% 1.54/0.59    inference(subsumption_resolution,[],[f355,f107])).
% 1.54/0.59  fof(f355,plain,(
% 1.54/0.59    v1_funct_2(k7_tmap_1(sK0,u1_struct_0(sK1)),u1_struct_0(sK0),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl4_14),
% 1.54/0.59    inference(superposition,[],[f80,f242])).
% 1.54/0.59  fof(f80,plain,(
% 1.54/0.59    ( ! [X0,X1] : (v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.54/0.59    inference(cnf_transformation,[],[f36])).
% 1.54/0.59  fof(f413,plain,(
% 1.54/0.59    spl4_28 | spl4_1 | ~spl4_2 | ~spl4_3 | spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_14 | ~spl4_21),
% 1.54/0.59    inference(avatar_split_clause,[],[f362,f300,f240,f130,f115,f110,f105,f100,f95,f410])).
% 1.54/0.59  fof(f410,plain,(
% 1.54/0.59    spl4_28 <=> v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK1),u1_struct_0(sK1),u1_struct_0(sK0))),
% 1.54/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 1.54/0.59  fof(f110,plain,(
% 1.54/0.59    spl4_4 <=> v2_struct_0(sK1)),
% 1.54/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.54/0.59  fof(f362,plain,(
% 1.54/0.59    v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | (spl4_1 | ~spl4_2 | ~spl4_3 | spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_14 | ~spl4_21)),
% 1.54/0.59    inference(forward_demodulation,[],[f361,f132])).
% 1.54/0.59  fof(f361,plain,(
% 1.54/0.59    v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | (spl4_1 | ~spl4_2 | ~spl4_3 | spl4_4 | ~spl4_5 | ~spl4_14 | ~spl4_21)),
% 1.54/0.59    inference(forward_demodulation,[],[f360,f302])).
% 1.54/0.59  fof(f360,plain,(
% 1.54/0.59    v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),sK1),u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK0,sK1))) | (spl4_1 | ~spl4_2 | ~spl4_3 | spl4_4 | ~spl4_5 | ~spl4_14)),
% 1.54/0.59    inference(subsumption_resolution,[],[f359,f97])).
% 1.54/0.59  fof(f359,plain,(
% 1.54/0.59    v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),sK1),u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK0,sK1))) | v2_struct_0(sK0) | (~spl4_2 | ~spl4_3 | spl4_4 | ~spl4_5 | ~spl4_14)),
% 1.54/0.59    inference(subsumption_resolution,[],[f358,f102])).
% 1.54/0.59  fof(f358,plain,(
% 1.54/0.59    v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),sK1),u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl4_3 | spl4_4 | ~spl4_5 | ~spl4_14)),
% 1.54/0.59    inference(subsumption_resolution,[],[f357,f107])).
% 1.54/0.59  fof(f357,plain,(
% 1.54/0.59    v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),sK1),u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl4_4 | ~spl4_5 | ~spl4_14)),
% 1.54/0.59    inference(subsumption_resolution,[],[f356,f112])).
% 1.54/0.59  fof(f112,plain,(
% 1.54/0.59    ~v2_struct_0(sK1) | spl4_4),
% 1.54/0.59    inference(avatar_component_clause,[],[f110])).
% 1.54/0.59  fof(f356,plain,(
% 1.54/0.59    v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),sK1),u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK0,sK1))) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl4_5 | ~spl4_14)),
% 1.54/0.59    inference(subsumption_resolution,[],[f353,f117])).
% 1.54/0.59  fof(f353,plain,(
% 1.54/0.59    v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k7_tmap_1(sK0,u1_struct_0(sK1)),sK1),u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl4_14),
% 1.54/0.59    inference(superposition,[],[f244,f242])).
% 1.54/0.59  fof(f244,plain,(
% 1.54/0.59    ( ! [X2,X0] : (v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X2)),k7_tmap_1(X0,u1_struct_0(X2)),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X2)))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.54/0.59    inference(subsumption_resolution,[],[f90,f58])).
% 1.54/0.59  fof(f90,plain,(
% 1.54/0.59    ( ! [X2,X0] : (v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X2)),k7_tmap_1(X0,u1_struct_0(X2)),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X2)))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.54/0.59    inference(equality_resolution,[],[f72])).
% 1.54/0.59  fof(f72,plain,(
% 1.54/0.59    ( ! [X2,X0,X1] : (v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1))) | u1_struct_0(X2) != X1 | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.54/0.59    inference(cnf_transformation,[],[f30])).
% 1.54/0.59  fof(f30,plain,(
% 1.54/0.59    ! [X0] : (! [X1] : (! [X2] : ((m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1)) & v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2))) | u1_struct_0(X2) != X1 | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.54/0.59    inference(flattening,[],[f29])).
% 1.54/0.59  fof(f29,plain,(
% 1.54/0.59    ! [X0] : (! [X1] : (! [X2] : (((m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1)) & v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2))) | u1_struct_0(X2) != X1) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.54/0.59    inference(ennf_transformation,[],[f11])).
% 1.54/0.59  fof(f11,axiom,(
% 1.54/0.59    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (u1_struct_0(X2) = X1 => (m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1)) & v1_funct_2(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)))))))),
% 1.54/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_tmap_1)).
% 1.54/0.59  fof(f408,plain,(
% 1.54/0.59    spl4_27 | spl4_1 | ~spl4_2 | ~spl4_3 | spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_14 | ~spl4_21),
% 1.54/0.59    inference(avatar_split_clause,[],[f403,f300,f240,f130,f115,f110,f105,f100,f95,f405])).
% 1.54/0.59  fof(f405,plain,(
% 1.54/0.59    spl4_27 <=> m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 1.54/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 1.54/0.59  fof(f403,plain,(
% 1.54/0.59    m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | (spl4_1 | ~spl4_2 | ~spl4_3 | spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_14 | ~spl4_21)),
% 1.54/0.59    inference(forward_demodulation,[],[f402,f302])).
% 1.54/0.59  fof(f402,plain,(
% 1.54/0.59    m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK0,sK1))))) | (spl4_1 | ~spl4_2 | ~spl4_3 | spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_14)),
% 1.54/0.59    inference(forward_demodulation,[],[f272,f242])).
% 1.54/0.59  fof(f272,plain,(
% 1.54/0.59    m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,u1_struct_0(sK1)),k6_partfun1(u1_struct_0(sK0)),sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))))) | (spl4_1 | ~spl4_2 | ~spl4_3 | spl4_4 | ~spl4_5 | ~spl4_6)),
% 1.54/0.59    inference(forward_demodulation,[],[f271,f132])).
% 1.54/0.59  fof(f271,plain,(
% 1.54/0.59    m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,u1_struct_0(sK1)),k7_tmap_1(sK0,u1_struct_0(sK1)),sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))))) | (spl4_1 | ~spl4_2 | ~spl4_3 | spl4_4 | ~spl4_5)),
% 1.54/0.59    inference(subsumption_resolution,[],[f270,f97])).
% 1.54/0.59  fof(f270,plain,(
% 1.54/0.59    m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,u1_struct_0(sK1)),k7_tmap_1(sK0,u1_struct_0(sK1)),sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))))) | v2_struct_0(sK0) | (~spl4_2 | ~spl4_3 | spl4_4 | ~spl4_5)),
% 1.54/0.59    inference(subsumption_resolution,[],[f269,f102])).
% 1.54/0.59  fof(f269,plain,(
% 1.54/0.59    m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,u1_struct_0(sK1)),k7_tmap_1(sK0,u1_struct_0(sK1)),sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl4_3 | spl4_4 | ~spl4_5)),
% 1.54/0.59    inference(subsumption_resolution,[],[f268,f107])).
% 1.54/0.59  fof(f268,plain,(
% 1.54/0.59    m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,u1_struct_0(sK1)),k7_tmap_1(sK0,u1_struct_0(sK1)),sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl4_4 | ~spl4_5)),
% 1.54/0.59    inference(subsumption_resolution,[],[f267,f112])).
% 1.54/0.59  fof(f267,plain,(
% 1.54/0.59    m1_subset_1(k2_tmap_1(sK0,k6_tmap_1(sK0,u1_struct_0(sK1)),k7_tmap_1(sK0,u1_struct_0(sK1)),sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))))) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl4_5),
% 1.54/0.59    inference(resolution,[],[f265,f117])).
% 1.54/0.59  fof(f265,plain,(
% 1.54/0.59    ( ! [X2,X0] : (~m1_pre_topc(X2,X0) | m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X2)),k7_tmap_1(X0,u1_struct_0(X2)),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X2)))))) | v2_struct_0(X2) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.54/0.59    inference(subsumption_resolution,[],[f88,f58])).
% 1.54/0.59  fof(f88,plain,(
% 1.54/0.59    ( ! [X2,X0] : (m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X2)),k7_tmap_1(X0,u1_struct_0(X2)),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,u1_struct_0(X2)))))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.54/0.59    inference(equality_resolution,[],[f74])).
% 1.54/0.59  fof(f74,plain,(
% 1.54/0.59    ( ! [X2,X0,X1] : (m1_subset_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k6_tmap_1(X0,X1))))) | u1_struct_0(X2) != X1 | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.54/0.59    inference(cnf_transformation,[],[f30])).
% 1.54/0.59  fof(f387,plain,(
% 1.54/0.59    spl4_24 | spl4_1 | ~spl4_2 | ~spl4_3 | spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_14),
% 1.54/0.59    inference(avatar_split_clause,[],[f382,f240,f130,f115,f110,f105,f100,f95,f384])).
% 1.54/0.59  fof(f384,plain,(
% 1.54/0.59    spl4_24 <=> v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK1),sK1,k8_tmap_1(sK0,sK1))),
% 1.54/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 1.54/0.59  fof(f382,plain,(
% 1.54/0.59    v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k6_partfun1(u1_struct_0(sK0)),sK1),sK1,k8_tmap_1(sK0,sK1)) | (spl4_1 | ~spl4_2 | ~spl4_3 | spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_14)),
% 1.54/0.59    inference(forward_demodulation,[],[f221,f242])).
% 1.54/0.59  fof(f221,plain,(
% 1.54/0.59    v5_pre_topc(k2_tmap_1(sK0,k6_tmap_1(sK0,u1_struct_0(sK1)),k6_partfun1(u1_struct_0(sK0)),sK1),sK1,k6_tmap_1(sK0,u1_struct_0(sK1))) | (spl4_1 | ~spl4_2 | ~spl4_3 | spl4_4 | ~spl4_5 | ~spl4_6)),
% 1.54/0.59    inference(forward_demodulation,[],[f220,f132])).
% 1.54/0.59  fof(f220,plain,(
% 1.54/0.59    v5_pre_topc(k2_tmap_1(sK0,k6_tmap_1(sK0,u1_struct_0(sK1)),k7_tmap_1(sK0,u1_struct_0(sK1)),sK1),sK1,k6_tmap_1(sK0,u1_struct_0(sK1))) | (spl4_1 | ~spl4_2 | ~spl4_3 | spl4_4 | ~spl4_5)),
% 1.54/0.59    inference(subsumption_resolution,[],[f219,f97])).
% 1.54/0.59  fof(f219,plain,(
% 1.54/0.59    v5_pre_topc(k2_tmap_1(sK0,k6_tmap_1(sK0,u1_struct_0(sK1)),k7_tmap_1(sK0,u1_struct_0(sK1)),sK1),sK1,k6_tmap_1(sK0,u1_struct_0(sK1))) | v2_struct_0(sK0) | (~spl4_2 | ~spl4_3 | spl4_4 | ~spl4_5)),
% 1.54/0.59    inference(subsumption_resolution,[],[f218,f102])).
% 1.54/0.59  fof(f218,plain,(
% 1.54/0.59    v5_pre_topc(k2_tmap_1(sK0,k6_tmap_1(sK0,u1_struct_0(sK1)),k7_tmap_1(sK0,u1_struct_0(sK1)),sK1),sK1,k6_tmap_1(sK0,u1_struct_0(sK1))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl4_3 | spl4_4 | ~spl4_5)),
% 1.54/0.59    inference(subsumption_resolution,[],[f217,f107])).
% 1.54/0.59  fof(f217,plain,(
% 1.54/0.59    v5_pre_topc(k2_tmap_1(sK0,k6_tmap_1(sK0,u1_struct_0(sK1)),k7_tmap_1(sK0,u1_struct_0(sK1)),sK1),sK1,k6_tmap_1(sK0,u1_struct_0(sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl4_4 | ~spl4_5)),
% 1.54/0.59    inference(subsumption_resolution,[],[f216,f112])).
% 1.54/0.59  fof(f216,plain,(
% 1.54/0.59    v5_pre_topc(k2_tmap_1(sK0,k6_tmap_1(sK0,u1_struct_0(sK1)),k7_tmap_1(sK0,u1_struct_0(sK1)),sK1),sK1,k6_tmap_1(sK0,u1_struct_0(sK1))) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl4_5),
% 1.54/0.59    inference(resolution,[],[f215,f117])).
% 1.54/0.59  fof(f215,plain,(
% 1.54/0.59    ( ! [X2,X0] : (~m1_pre_topc(X2,X0) | v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X2)),k7_tmap_1(X0,u1_struct_0(X2)),X2),X2,k6_tmap_1(X0,u1_struct_0(X2))) | v2_struct_0(X2) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.54/0.59    inference(subsumption_resolution,[],[f89,f58])).
% 1.54/0.59  fof(f89,plain,(
% 1.54/0.59    ( ! [X2,X0] : (v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X2)),k7_tmap_1(X0,u1_struct_0(X2)),X2),X2,k6_tmap_1(X0,u1_struct_0(X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.54/0.59    inference(equality_resolution,[],[f73])).
% 1.54/0.59  fof(f73,plain,(
% 1.54/0.59    ( ! [X2,X0,X1] : (v5_pre_topc(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X2,k6_tmap_1(X0,X1)) | u1_struct_0(X2) != X1 | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.54/0.59    inference(cnf_transformation,[],[f30])).
% 1.54/0.59  fof(f303,plain,(
% 1.54/0.59    spl4_21 | spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_5 | ~spl4_8),
% 1.54/0.59    inference(avatar_split_clause,[],[f238,f165,f115,f105,f100,f95,f300])).
% 1.54/0.59  fof(f165,plain,(
% 1.54/0.59    spl4_8 <=> u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1)))),
% 1.54/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.54/0.59  fof(f238,plain,(
% 1.54/0.59    u1_struct_0(k8_tmap_1(sK0,sK1)) = u1_struct_0(sK0) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_5 | ~spl4_8)),
% 1.54/0.59    inference(backward_demodulation,[],[f167,f234])).
% 1.54/0.59  fof(f234,plain,(
% 1.54/0.59    k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_5)),
% 1.54/0.59    inference(subsumption_resolution,[],[f233,f97])).
% 1.54/0.59  fof(f233,plain,(
% 1.54/0.59    k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) | v2_struct_0(sK0) | (~spl4_2 | ~spl4_3 | ~spl4_5)),
% 1.54/0.59    inference(subsumption_resolution,[],[f232,f102])).
% 1.54/0.59  fof(f232,plain,(
% 1.54/0.59    k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl4_3 | ~spl4_5)),
% 1.54/0.59    inference(subsumption_resolution,[],[f231,f107])).
% 1.54/0.59  fof(f231,plain,(
% 1.54/0.59    k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl4_5),
% 1.54/0.59    inference(resolution,[],[f230,f117])).
% 1.54/0.59  fof(f230,plain,(
% 1.54/0.59    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.54/0.59    inference(subsumption_resolution,[],[f229,f76])).
% 1.54/0.59  fof(f76,plain,(
% 1.54/0.59    ( ! [X0,X1] : (v1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.54/0.59    inference(cnf_transformation,[],[f34])).
% 1.54/0.59  fof(f34,plain,(
% 1.54/0.59    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.54/0.59    inference(flattening,[],[f33])).
% 1.54/0.59  fof(f33,plain,(
% 1.54/0.59    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.54/0.59    inference(ennf_transformation,[],[f9])).
% 1.54/0.59  fof(f9,axiom,(
% 1.54/0.59    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))))),
% 1.54/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_tmap_1)).
% 1.54/0.59  fof(f229,plain,(
% 1.54/0.59    ( ! [X0,X1] : (k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1)) | ~v1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.54/0.59    inference(subsumption_resolution,[],[f228,f77])).
% 1.54/0.59  fof(f77,plain,(
% 1.54/0.59    ( ! [X0,X1] : (v2_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.54/0.59    inference(cnf_transformation,[],[f34])).
% 1.54/0.59  fof(f228,plain,(
% 1.54/0.59    ( ! [X0,X1] : (k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1)) | ~v2_pre_topc(k8_tmap_1(X0,X1)) | ~v1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.54/0.59    inference(subsumption_resolution,[],[f227,f78])).
% 1.54/0.59  fof(f78,plain,(
% 1.54/0.59    ( ! [X0,X1] : (l1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.54/0.59    inference(cnf_transformation,[],[f34])).
% 1.54/0.59  fof(f227,plain,(
% 1.54/0.59    ( ! [X0,X1] : (k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1)) | ~l1_pre_topc(k8_tmap_1(X0,X1)) | ~v2_pre_topc(k8_tmap_1(X0,X1)) | ~v1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.54/0.59    inference(subsumption_resolution,[],[f85,f58])).
% 1.54/0.59  fof(f85,plain,(
% 1.54/0.59    ( ! [X0,X1] : (k8_tmap_1(X0,X1) = k6_tmap_1(X0,u1_struct_0(X1)) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(k8_tmap_1(X0,X1)) | ~v2_pre_topc(k8_tmap_1(X0,X1)) | ~v1_pre_topc(k8_tmap_1(X0,X1)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.54/0.59    inference(equality_resolution,[],[f84])).
% 1.54/0.59  fof(f84,plain,(
% 1.54/0.59    ( ! [X2,X0,X1] : (k6_tmap_1(X0,u1_struct_0(X1)) = X2 | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | k8_tmap_1(X0,X1) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.54/0.59    inference(equality_resolution,[],[f60])).
% 1.54/0.59  fof(f60,plain,(
% 1.54/0.59    ( ! [X4,X2,X0,X1] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | k8_tmap_1(X0,X1) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.54/0.59    inference(cnf_transformation,[],[f45])).
% 1.54/0.59  fof(f45,plain,(
% 1.54/0.59    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | (k6_tmap_1(X0,sK2(X0,X1,X2)) != X2 & u1_struct_0(X1) = sK2(X0,X1,X2) & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.54/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f43,f44])).
% 1.54/0.59  fof(f44,plain,(
% 1.54/0.59    ! [X2,X1,X0] : (? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (k6_tmap_1(X0,sK2(X0,X1,X2)) != X2 & u1_struct_0(X1) = sK2(X0,X1,X2) & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.54/0.59    introduced(choice_axiom,[])).
% 1.54/0.59  fof(f43,plain,(
% 1.54/0.59    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | ? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (k6_tmap_1(X0,X4) = X2 | u1_struct_0(X1) != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.54/0.59    inference(rectify,[],[f42])).
% 1.54/0.59  fof(f42,plain,(
% 1.54/0.59    ! [X0] : (! [X1] : (! [X2] : (((k8_tmap_1(X0,X1) = X2 | ? [X3] : (k6_tmap_1(X0,X3) != X2 & u1_struct_0(X1) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | k8_tmap_1(X0,X1) != X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.54/0.59    inference(nnf_transformation,[],[f22])).
% 1.54/0.59  fof(f22,plain,(
% 1.54/0.59    ! [X0] : (! [X1] : (! [X2] : ((k8_tmap_1(X0,X1) = X2 <=> ! [X3] : (k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.54/0.59    inference(flattening,[],[f21])).
% 1.54/0.59  fof(f21,plain,(
% 1.54/0.59    ! [X0] : (! [X1] : (! [X2] : ((k8_tmap_1(X0,X1) = X2 <=> ! [X3] : ((k6_tmap_1(X0,X3) = X2 | u1_struct_0(X1) != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v1_pre_topc(X2))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.54/0.59    inference(ennf_transformation,[],[f6])).
% 1.54/0.59  fof(f6,axiom,(
% 1.54/0.59    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2) & v1_pre_topc(X2)) => (k8_tmap_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X3 => k6_tmap_1(X0,X3) = X2))))))),
% 1.54/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_tmap_1)).
% 1.54/0.59  fof(f167,plain,(
% 1.54/0.59    u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))) | ~spl4_8),
% 1.54/0.59    inference(avatar_component_clause,[],[f165])).
% 1.54/0.59  fof(f297,plain,(
% 1.54/0.59    ~spl4_17 | ~spl4_18 | ~spl4_19 | ~spl4_20),
% 1.54/0.59    inference(avatar_split_clause,[],[f56,f294,f290,f286,f282])).
% 1.54/0.59  fof(f282,plain,(
% 1.54/0.59    spl4_17 <=> v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK1))),
% 1.54/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 1.54/0.59  fof(f286,plain,(
% 1.54/0.59    spl4_18 <=> v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK1),u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK0,sK1)))),
% 1.54/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 1.54/0.59  fof(f290,plain,(
% 1.54/0.59    spl4_19 <=> v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK1),sK1,k8_tmap_1(sK0,sK1))),
% 1.54/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 1.54/0.59  fof(f294,plain,(
% 1.54/0.59    spl4_20 <=> m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK0,sK1)))))),
% 1.54/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 1.54/0.59  fof(f56,plain,(
% 1.54/0.59    ~m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK0,sK1))))) | ~v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK1),sK1,k8_tmap_1(sK0,sK1)) | ~v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK1),u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK1))),
% 1.54/0.59    inference(cnf_transformation,[],[f41])).
% 1.54/0.59  fof(f41,plain,(
% 1.54/0.59    ((~m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK0,sK1))))) | ~v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK1),sK1,k8_tmap_1(sK0,sK1)) | ~v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK1),u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK1))) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.54/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f40,f39])).
% 1.54/0.59  % (7044)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.54/0.59  fof(f39,plain,(
% 1.54/0.59    ? [X0] : (? [X1] : ((~m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X1,k8_tmap_1(X0,X1)) | ~v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1))) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,X1),k9_tmap_1(sK0,X1),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(sK0,X1))))) | ~v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,X1),k9_tmap_1(sK0,X1),X1),X1,k8_tmap_1(sK0,X1)) | ~v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,X1),k9_tmap_1(sK0,X1),X1),u1_struct_0(X1),u1_struct_0(k8_tmap_1(sK0,X1))) | ~v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,X1),k9_tmap_1(sK0,X1),X1))) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.54/0.59    introduced(choice_axiom,[])).
% 1.54/0.59  fof(f40,plain,(
% 1.54/0.59    ? [X1] : ((~m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,X1),k9_tmap_1(sK0,X1),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(sK0,X1))))) | ~v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,X1),k9_tmap_1(sK0,X1),X1),X1,k8_tmap_1(sK0,X1)) | ~v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,X1),k9_tmap_1(sK0,X1),X1),u1_struct_0(X1),u1_struct_0(k8_tmap_1(sK0,X1))) | ~v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,X1),k9_tmap_1(sK0,X1),X1))) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) => ((~m1_subset_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK0,sK1))))) | ~v5_pre_topc(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK1),sK1,k8_tmap_1(sK0,sK1)) | ~v1_funct_2(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK1),u1_struct_0(sK1),u1_struct_0(k8_tmap_1(sK0,sK1))) | ~v1_funct_1(k2_tmap_1(sK0,k8_tmap_1(sK0,sK1),k9_tmap_1(sK0,sK1),sK1))) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1))),
% 1.54/0.59    introduced(choice_axiom,[])).
% 1.54/0.59  fof(f16,plain,(
% 1.54/0.59    ? [X0] : (? [X1] : ((~m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X1,k8_tmap_1(X0,X1)) | ~v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1))) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.54/0.59    inference(flattening,[],[f15])).
% 1.54/0.59  fof(f15,plain,(
% 1.54/0.59    ? [X0] : (? [X1] : ((~m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X0,X1))))) | ~v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X1,k8_tmap_1(X0,X1)) | ~v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X0,X1))) | ~v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.54/0.59    inference(ennf_transformation,[],[f14])).
% 1.54/0.59  fof(f14,negated_conjecture,(
% 1.54/0.59    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X0,X1))))) & v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X1,k8_tmap_1(X0,X1)) & v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1)))))),
% 1.54/0.59    inference(negated_conjecture,[],[f13])).
% 1.54/0.59  fof(f13,conjecture,(
% 1.54/0.59    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (m1_subset_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X0,X1))))) & v5_pre_topc(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),X1,k8_tmap_1(X0,X1)) & v1_funct_2(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X0,X1))) & v1_funct_1(k2_tmap_1(X0,k8_tmap_1(X0,X1),k9_tmap_1(X0,X1),X1)))))),
% 1.54/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_tmap_1)).
% 1.54/0.59  fof(f243,plain,(
% 1.54/0.59    spl4_14 | spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_5),
% 1.54/0.59    inference(avatar_split_clause,[],[f234,f115,f105,f100,f95,f240])).
% 1.54/0.59  fof(f226,plain,(
% 1.54/0.59    spl4_13 | spl4_1 | ~spl4_2 | ~spl4_3 | spl4_4 | ~spl4_5 | ~spl4_6),
% 1.54/0.59    inference(avatar_split_clause,[],[f208,f130,f115,f110,f105,f100,f95,f223])).
% 1.54/0.59  fof(f223,plain,(
% 1.54/0.59    spl4_13 <=> v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,u1_struct_0(sK1)),k6_partfun1(u1_struct_0(sK0)),sK1))),
% 1.54/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 1.54/0.59  fof(f208,plain,(
% 1.54/0.59    v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,u1_struct_0(sK1)),k6_partfun1(u1_struct_0(sK0)),sK1)) | (spl4_1 | ~spl4_2 | ~spl4_3 | spl4_4 | ~spl4_5 | ~spl4_6)),
% 1.54/0.59    inference(forward_demodulation,[],[f207,f132])).
% 1.54/0.59  fof(f207,plain,(
% 1.54/0.59    v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,u1_struct_0(sK1)),k7_tmap_1(sK0,u1_struct_0(sK1)),sK1)) | (spl4_1 | ~spl4_2 | ~spl4_3 | spl4_4 | ~spl4_5)),
% 1.54/0.59    inference(subsumption_resolution,[],[f206,f97])).
% 1.54/0.59  fof(f206,plain,(
% 1.54/0.59    v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,u1_struct_0(sK1)),k7_tmap_1(sK0,u1_struct_0(sK1)),sK1)) | v2_struct_0(sK0) | (~spl4_2 | ~spl4_3 | spl4_4 | ~spl4_5)),
% 1.54/0.59    inference(subsumption_resolution,[],[f205,f102])).
% 1.54/0.59  fof(f205,plain,(
% 1.54/0.59    v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,u1_struct_0(sK1)),k7_tmap_1(sK0,u1_struct_0(sK1)),sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl4_3 | spl4_4 | ~spl4_5)),
% 1.54/0.59    inference(subsumption_resolution,[],[f204,f107])).
% 1.54/0.59  fof(f204,plain,(
% 1.54/0.59    v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,u1_struct_0(sK1)),k7_tmap_1(sK0,u1_struct_0(sK1)),sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl4_4 | ~spl4_5)),
% 1.54/0.59    inference(subsumption_resolution,[],[f203,f112])).
% 1.54/0.59  fof(f203,plain,(
% 1.54/0.59    v1_funct_1(k2_tmap_1(sK0,k6_tmap_1(sK0,u1_struct_0(sK1)),k7_tmap_1(sK0,u1_struct_0(sK1)),sK1)) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl4_5),
% 1.54/0.59    inference(resolution,[],[f189,f117])).
% 1.54/0.59  fof(f189,plain,(
% 1.54/0.59    ( ! [X2,X0] : (~m1_pre_topc(X2,X0) | v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X2)),k7_tmap_1(X0,u1_struct_0(X2)),X2)) | v2_struct_0(X2) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.54/0.59    inference(subsumption_resolution,[],[f91,f58])).
% 1.54/0.59  fof(f91,plain,(
% 1.54/0.59    ( ! [X2,X0] : (v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,u1_struct_0(X2)),k7_tmap_1(X0,u1_struct_0(X2)),X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.54/0.59    inference(equality_resolution,[],[f71])).
% 1.54/0.59  fof(f71,plain,(
% 1.54/0.59    ( ! [X2,X0,X1] : (v1_funct_1(k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)) | u1_struct_0(X2) != X1 | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.54/0.59    inference(cnf_transformation,[],[f30])).
% 1.54/0.59  fof(f168,plain,(
% 1.54/0.59    spl4_8 | spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_5),
% 1.54/0.59    inference(avatar_split_clause,[],[f160,f115,f105,f100,f95,f165])).
% 1.54/0.59  fof(f160,plain,(
% 1.54/0.59    u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_5)),
% 1.54/0.59    inference(subsumption_resolution,[],[f159,f97])).
% 1.54/0.59  fof(f159,plain,(
% 1.54/0.59    v2_struct_0(sK0) | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))) | (~spl4_2 | ~spl4_3 | ~spl4_5)),
% 1.54/0.59    inference(subsumption_resolution,[],[f158,f102])).
% 1.54/0.59  fof(f158,plain,(
% 1.54/0.59    ~v2_pre_topc(sK0) | v2_struct_0(sK0) | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))) | (~spl4_3 | ~spl4_5)),
% 1.54/0.59    inference(subsumption_resolution,[],[f157,f107])).
% 1.54/0.59  fof(f157,plain,(
% 1.54/0.59    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK1))) | ~spl4_5),
% 1.54/0.59    inference(resolution,[],[f128,f117])).
% 1.54/0.59  fof(f128,plain,(
% 1.54/0.59    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1)))) )),
% 1.54/0.59    inference(duplicate_literal_removal,[],[f127])).
% 1.54/0.59  fof(f127,plain,(
% 1.54/0.59    ( ! [X0,X1] : (u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,u1_struct_0(X1))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.54/0.59    inference(resolution,[],[f69,f58])).
% 1.54/0.59  fof(f69,plain,(
% 1.54/0.59    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.54/0.59    inference(cnf_transformation,[],[f28])).
% 1.54/0.59  fof(f28,plain,(
% 1.54/0.59    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.54/0.59    inference(flattening,[],[f27])).
% 1.54/0.59  fof(f27,plain,(
% 1.54/0.59    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.54/0.59    inference(ennf_transformation,[],[f10])).
% 1.54/0.59  fof(f10,axiom,(
% 1.54/0.59    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)))))),
% 1.54/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_tmap_1)).
% 1.54/0.59  fof(f149,plain,(
% 1.54/0.59    spl4_7 | spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_5 | ~spl4_6),
% 1.54/0.59    inference(avatar_split_clause,[],[f140,f130,f115,f105,f100,f95,f146])).
% 1.54/0.59  fof(f140,plain,(
% 1.54/0.59    v1_funct_1(k6_partfun1(u1_struct_0(sK0))) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_5 | ~spl4_6)),
% 1.54/0.59    inference(subsumption_resolution,[],[f139,f117])).
% 1.54/0.59  fof(f139,plain,(
% 1.54/0.59    v1_funct_1(k6_partfun1(u1_struct_0(sK0))) | ~m1_pre_topc(sK1,sK0) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_6)),
% 1.54/0.59    inference(subsumption_resolution,[],[f138,f97])).
% 1.54/0.59  fof(f138,plain,(
% 1.54/0.59    v1_funct_1(k6_partfun1(u1_struct_0(sK0))) | v2_struct_0(sK0) | ~m1_pre_topc(sK1,sK0) | (~spl4_2 | ~spl4_3 | ~spl4_6)),
% 1.54/0.59    inference(subsumption_resolution,[],[f137,f102])).
% 1.54/0.59  fof(f137,plain,(
% 1.54/0.59    v1_funct_1(k6_partfun1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_pre_topc(sK1,sK0) | (~spl4_3 | ~spl4_6)),
% 1.54/0.59    inference(subsumption_resolution,[],[f136,f107])).
% 1.54/0.59  fof(f136,plain,(
% 1.54/0.59    v1_funct_1(k6_partfun1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_pre_topc(sK1,sK0) | ~spl4_6),
% 1.54/0.59    inference(superposition,[],[f120,f132])).
% 1.54/0.59  fof(f120,plain,(
% 1.54/0.59    ( ! [X0,X1] : (v1_funct_1(k7_tmap_1(X0,u1_struct_0(X1))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(X1,X0)) )),
% 1.54/0.59    inference(duplicate_literal_removal,[],[f119])).
% 1.54/0.59  fof(f119,plain,(
% 1.54/0.59    ( ! [X0,X1] : (v1_funct_1(k7_tmap_1(X0,u1_struct_0(X1))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.54/0.59    inference(resolution,[],[f79,f58])).
% 1.54/0.59  fof(f79,plain,(
% 1.54/0.59    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_funct_1(k7_tmap_1(X0,X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.54/0.59    inference(cnf_transformation,[],[f36])).
% 1.54/0.59  fof(f133,plain,(
% 1.54/0.59    spl4_6 | spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_5),
% 1.54/0.59    inference(avatar_split_clause,[],[f126,f115,f105,f100,f95,f130])).
% 1.54/0.59  fof(f126,plain,(
% 1.54/0.59    k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(sK0,u1_struct_0(sK1)) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_5)),
% 1.54/0.59    inference(subsumption_resolution,[],[f125,f97])).
% 1.54/0.59  fof(f125,plain,(
% 1.54/0.59    v2_struct_0(sK0) | k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(sK0,u1_struct_0(sK1)) | (~spl4_2 | ~spl4_3 | ~spl4_5)),
% 1.54/0.59    inference(subsumption_resolution,[],[f124,f102])).
% 1.54/0.59  fof(f124,plain,(
% 1.54/0.59    ~v2_pre_topc(sK0) | v2_struct_0(sK0) | k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(sK0,u1_struct_0(sK1)) | (~spl4_3 | ~spl4_5)),
% 1.54/0.59    inference(subsumption_resolution,[],[f123,f107])).
% 1.54/0.59  fof(f123,plain,(
% 1.54/0.59    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | k6_partfun1(u1_struct_0(sK0)) = k7_tmap_1(sK0,u1_struct_0(sK1)) | ~spl4_5),
% 1.54/0.59    inference(resolution,[],[f122,f117])).
% 1.54/0.59  fof(f122,plain,(
% 1.54/0.59    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | k6_partfun1(u1_struct_0(X0)) = k7_tmap_1(X0,u1_struct_0(X1))) )),
% 1.54/0.59    inference(duplicate_literal_removal,[],[f121])).
% 1.54/0.59  fof(f121,plain,(
% 1.54/0.59    ( ! [X0,X1] : (k6_partfun1(u1_struct_0(X0)) = k7_tmap_1(X0,u1_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.54/0.59    inference(resolution,[],[f68,f58])).
% 1.54/0.59  fof(f68,plain,(
% 1.54/0.59    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.54/0.59    inference(cnf_transformation,[],[f26])).
% 1.54/0.59  fof(f26,plain,(
% 1.54/0.59    ! [X0] : (! [X1] : (k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.54/0.59    inference(flattening,[],[f25])).
% 1.54/0.59  fof(f25,plain,(
% 1.54/0.59    ! [X0] : (! [X1] : (k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.54/0.59    inference(ennf_transformation,[],[f5])).
% 1.54/0.59  fof(f5,axiom,(
% 1.54/0.59    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))))),
% 1.54/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_tmap_1)).
% 1.54/0.59  fof(f118,plain,(
% 1.54/0.59    spl4_5),
% 1.54/0.59    inference(avatar_split_clause,[],[f55,f115])).
% 1.54/0.59  fof(f55,plain,(
% 1.54/0.59    m1_pre_topc(sK1,sK0)),
% 1.54/0.59    inference(cnf_transformation,[],[f41])).
% 1.54/0.59  fof(f113,plain,(
% 1.54/0.59    ~spl4_4),
% 1.54/0.59    inference(avatar_split_clause,[],[f54,f110])).
% 1.54/0.59  fof(f54,plain,(
% 1.54/0.59    ~v2_struct_0(sK1)),
% 1.54/0.59    inference(cnf_transformation,[],[f41])).
% 1.54/0.59  fof(f108,plain,(
% 1.54/0.59    spl4_3),
% 1.54/0.59    inference(avatar_split_clause,[],[f53,f105])).
% 1.54/0.59  fof(f53,plain,(
% 1.54/0.59    l1_pre_topc(sK0)),
% 1.54/0.59    inference(cnf_transformation,[],[f41])).
% 1.54/0.59  fof(f103,plain,(
% 1.54/0.59    spl4_2),
% 1.54/0.59    inference(avatar_split_clause,[],[f52,f100])).
% 1.54/0.59  fof(f52,plain,(
% 1.54/0.59    v2_pre_topc(sK0)),
% 1.54/0.59    inference(cnf_transformation,[],[f41])).
% 1.54/0.59  fof(f98,plain,(
% 1.54/0.59    ~spl4_1),
% 1.54/0.59    inference(avatar_split_clause,[],[f51,f95])).
% 1.54/0.59  fof(f51,plain,(
% 1.54/0.59    ~v2_struct_0(sK0)),
% 1.54/0.59    inference(cnf_transformation,[],[f41])).
% 1.54/0.59  % SZS output end Proof for theBenchmark
% 1.54/0.59  % (7033)------------------------------
% 1.54/0.59  % (7033)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.59  % (7033)Termination reason: Refutation
% 1.54/0.59  
% 1.54/0.59  % (7033)Memory used [KB]: 6908
% 1.54/0.59  % (7033)Time elapsed: 0.128 s
% 1.54/0.59  % (7033)------------------------------
% 1.54/0.59  % (7033)------------------------------
% 1.54/0.60  % (7030)Success in time 0.225 s
%------------------------------------------------------------------------------
