%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:25 EST 2020

% Result     : Theorem 1.67s
% Output     : Refutation 1.67s
% Verified   : 
% Statistics : Number of formulae       :  207 ( 715 expanded)
%              Number of leaves         :   54 ( 327 expanded)
%              Depth                    :   11
%              Number of atoms          :  716 (3710 expanded)
%              Number of equality atoms :   47 ( 297 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f723,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f76,f81,f86,f91,f96,f101,f106,f111,f116,f121,f126,f133,f139,f145,f151,f170,f186,f196,f202,f231,f237,f246,f256,f266,f307,f316,f341,f351,f368,f493,f585,f608,f625,f650,f720,f722])).

fof(f722,plain,
    ( ~ spl5_14
    | ~ spl5_15
    | spl5_35 ),
    inference(avatar_contradiction_clause,[],[f721])).

fof(f721,plain,
    ( $false
    | ~ spl5_14
    | ~ spl5_15
    | spl5_35 ),
    inference(subsumption_resolution,[],[f719,f686])).

fof(f686,plain,
    ( ! [X0] : m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK1))))
    | ~ spl5_14
    | ~ spl5_15 ),
    inference(unit_resulting_resolution,[],[f154,f158,f685,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

fof(f685,plain,
    ( ! [X0] : r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),u1_struct_0(sK1))
    | ~ spl5_14
    | ~ spl5_15 ),
    inference(unit_resulting_resolution,[],[f154,f682,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f682,plain,
    ( ! [X0] : v5_relat_1(k7_relat_1(sK3,X0),u1_struct_0(sK1))
    | ~ spl5_14
    | ~ spl5_15 ),
    inference(unit_resulting_resolution,[],[f346,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f346,plain,
    ( ! [X0] : m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl5_14
    | ~ spl5_15 ),
    inference(unit_resulting_resolution,[],[f215,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f215,plain,
    ( ! [X0] : r1_tarski(k7_relat_1(sK3,X0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | ~ spl5_14
    | ~ spl5_15 ),
    inference(unit_resulting_resolution,[],[f152,f144,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f144,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl5_14
  <=> r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f152,plain,
    ( ! [X0] : r1_tarski(k7_relat_1(sK3,X0),sK3)
    | ~ spl5_15 ),
    inference(unit_resulting_resolution,[],[f150,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

fof(f150,plain,
    ( v1_relat_1(sK3)
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl5_15
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f158,plain,
    ( ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),X0)
    | ~ spl5_15 ),
    inference(unit_resulting_resolution,[],[f150,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

fof(f154,plain,
    ( ! [X0] : v1_relat_1(k7_relat_1(sK3,X0))
    | ~ spl5_15 ),
    inference(unit_resulting_resolution,[],[f150,f153,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f153,plain,
    ( ! [X0] : m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(sK3))
    | ~ spl5_15 ),
    inference(unit_resulting_resolution,[],[f152,f66])).

fof(f719,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | spl5_35 ),
    inference(avatar_component_clause,[],[f717])).

fof(f717,plain,
    ( spl5_35
  <=> m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).

fof(f720,plain,
    ( ~ spl5_35
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_11
    | ~ spl5_13
    | spl5_27
    | ~ spl5_30 ),
    inference(avatar_split_clause,[],[f510,f490,f338,f136,f123,f113,f108,f98,f93,f88,f83,f78,f73,f717])).

fof(f73,plain,
    ( spl5_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f78,plain,
    ( spl5_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f83,plain,
    ( spl5_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f88,plain,
    ( spl5_4
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f93,plain,
    ( spl5_5
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f98,plain,
    ( spl5_6
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f108,plain,
    ( spl5_8
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f113,plain,
    ( spl5_9
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f123,plain,
    ( spl5_11
  <=> v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f136,plain,
    ( spl5_13
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f338,plain,
    ( spl5_27
  <=> k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),sK4) = k10_relat_1(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f490,plain,
    ( spl5_30
  <=> k10_relat_1(sK3,sK4) = k10_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f510,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_11
    | ~ spl5_13
    | spl5_27
    | ~ spl5_30 ),
    inference(subsumption_resolution,[],[f509,f492])).

fof(f492,plain,
    ( k10_relat_1(sK3,sK4) = k10_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK4)
    | ~ spl5_30 ),
    inference(avatar_component_clause,[],[f490])).

fof(f509,plain,
    ( k10_relat_1(sK3,sK4) != k10_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK4)
    | ~ m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_11
    | ~ spl5_13
    | spl5_27 ),
    inference(forward_demodulation,[],[f507,f506])).

fof(f506,plain,
    ( k2_tmap_1(sK0,sK1,sK3,sK2) = k7_relat_1(sK3,u1_struct_0(sK2))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_11
    | ~ spl5_13 ),
    inference(forward_demodulation,[],[f504,f460])).

fof(f460,plain,
    ( ! [X0] : k7_relat_1(sK3,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,X0)
    | ~ spl5_8
    | ~ spl5_13 ),
    inference(unit_resulting_resolution,[],[f110,f138,f71])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f138,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f136])).

fof(f110,plain,
    ( v1_funct_1(sK3)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f108])).

fof(f504,plain,
    ( k2_tmap_1(sK0,sK1,sK3,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,u1_struct_0(sK2))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_11
    | ~ spl5_13 ),
    inference(unit_resulting_resolution,[],[f75,f80,f85,f90,f95,f100,f110,f115,f125,f138,f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).

fof(f125,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f123])).

fof(f115,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f113])).

fof(f100,plain,
    ( l1_pre_topc(sK1)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f98])).

fof(f95,plain,
    ( v2_pre_topc(sK1)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f93])).

fof(f90,plain,
    ( ~ v2_struct_0(sK1)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f88])).

fof(f85,plain,
    ( l1_pre_topc(sK0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f83])).

fof(f80,plain,
    ( v2_pre_topc(sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f78])).

fof(f75,plain,
    ( ~ v2_struct_0(sK0)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f73])).

fof(f507,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | k10_relat_1(sK3,sK4) != k10_relat_1(k2_tmap_1(sK0,sK1,sK3,sK2),sK4)
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_11
    | ~ spl5_13
    | spl5_27 ),
    inference(backward_demodulation,[],[f363,f506])).

fof(f363,plain,
    ( k10_relat_1(sK3,sK4) != k10_relat_1(k2_tmap_1(sK0,sK1,sK3,sK2),sK4)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | spl5_27 ),
    inference(superposition,[],[f340,f70])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f340,plain,
    ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),sK4) != k10_relat_1(sK3,sK4)
    | spl5_27 ),
    inference(avatar_component_clause,[],[f338])).

fof(f650,plain,
    ( spl5_34
    | ~ spl5_15
    | ~ spl5_21 ),
    inference(avatar_split_clause,[],[f238,f234,f148,f647])).

fof(f647,plain,
    ( spl5_34
  <=> r1_tarski(k1_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,sK4)))),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).

fof(f234,plain,
    ( spl5_21
  <=> r1_tarski(k1_relat_1(k7_relat_1(sK3,sK4)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f238,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,sK4)))),u1_struct_0(sK1))
    | ~ spl5_15
    | ~ spl5_21 ),
    inference(unit_resulting_resolution,[],[f158,f236,f69])).

fof(f236,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK3,sK4)),u1_struct_0(sK1))
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f234])).

fof(f625,plain,
    ( spl5_33
    | ~ spl5_14
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f216,f148,f142,f622])).

fof(f622,plain,
    ( spl5_33
  <=> r1_tarski(k1_relat_1(k7_relat_1(sK3,sK3)),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).

fof(f216,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK3,sK3)),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | ~ spl5_14
    | ~ spl5_15 ),
    inference(unit_resulting_resolution,[],[f158,f144,f69])).

fof(f608,plain,
    ( spl5_32
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_11
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f506,f136,f123,f113,f108,f98,f93,f88,f83,f78,f73,f605])).

fof(f605,plain,
    ( spl5_32
  <=> k2_tmap_1(sK0,sK1,sK3,sK2) = k7_relat_1(sK3,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f585,plain,
    ( ~ spl5_31
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_11
    | ~ spl5_13
    | spl5_27 ),
    inference(avatar_split_clause,[],[f508,f338,f136,f123,f113,f108,f98,f93,f88,f83,f78,f73,f582])).

fof(f582,plain,
    ( spl5_31
  <=> k10_relat_1(sK3,sK4) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK3,u1_struct_0(sK2)),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).

fof(f508,plain,
    ( k10_relat_1(sK3,sK4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_11
    | ~ spl5_13
    | spl5_27 ),
    inference(backward_demodulation,[],[f340,f506])).

fof(f493,plain,
    ( spl5_30
    | ~ spl5_8
    | ~ spl5_15
    | ~ spl5_25 ),
    inference(avatar_split_clause,[],[f488,f304,f148,f108,f490])).

fof(f304,plain,
    ( spl5_25
  <=> r1_tarski(k10_relat_1(sK3,sK4),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f488,plain,
    ( k10_relat_1(sK3,sK4) = k10_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK4)
    | ~ spl5_8
    | ~ spl5_15
    | ~ spl5_25 ),
    inference(unit_resulting_resolution,[],[f150,f110,f306,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)
      | ~ r1_tarski(k10_relat_1(X0,X2),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)
          | ~ r1_tarski(k10_relat_1(X0,X2),X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)
          | ~ r1_tarski(k10_relat_1(X0,X2),X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( r1_tarski(k10_relat_1(X0,X2),X1)
         => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_funct_2)).

fof(f306,plain,
    ( r1_tarski(k10_relat_1(sK3,sK4),u1_struct_0(sK2))
    | ~ spl5_25 ),
    inference(avatar_component_clause,[],[f304])).

fof(f368,plain,
    ( spl5_29
    | ~ spl5_23 ),
    inference(avatar_split_clause,[],[f260,f253,f365])).

fof(f365,plain,
    ( spl5_29
  <=> m1_subset_1(k1_relat_1(k7_relat_1(sK3,k2_relat_1(sK3))),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).

fof(f253,plain,
    ( spl5_23
  <=> r1_tarski(k1_relat_1(k7_relat_1(sK3,k2_relat_1(sK3))),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f260,plain,
    ( m1_subset_1(k1_relat_1(k7_relat_1(sK3,k2_relat_1(sK3))),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl5_23 ),
    inference(unit_resulting_resolution,[],[f255,f66])).

fof(f255,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK3,k2_relat_1(sK3))),u1_struct_0(sK1))
    | ~ spl5_23 ),
    inference(avatar_component_clause,[],[f253])).

fof(f351,plain,
    ( spl5_28
    | ~ spl5_13
    | ~ spl5_15
    | ~ spl5_22 ),
    inference(avatar_split_clause,[],[f297,f243,f148,f136,f348])).

fof(f348,plain,
    ( spl5_28
  <=> r1_tarski(k1_relat_1(k7_relat_1(sK3,k10_relat_1(sK3,sK4))),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f243,plain,
    ( spl5_22
  <=> r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f297,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK3,k10_relat_1(sK3,sK4))),u1_struct_0(sK2))
    | ~ spl5_13
    | ~ spl5_15
    | ~ spl5_22 ),
    inference(backward_demodulation,[],[f267,f295])).

fof(f295,plain,
    ( ! [X0] : k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,X0) = k10_relat_1(sK3,X0)
    | ~ spl5_13 ),
    inference(unit_resulting_resolution,[],[f138,f70])).

fof(f267,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK3,k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4))),u1_struct_0(sK2))
    | ~ spl5_15
    | ~ spl5_22 ),
    inference(unit_resulting_resolution,[],[f158,f245,f69])).

fof(f245,plain,
    ( r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),u1_struct_0(sK2))
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f243])).

fof(f341,plain,
    ( ~ spl5_27
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f302,f136,f338])).

fof(f302,plain,
    ( k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),sK4) != k10_relat_1(sK3,sK4)
    | ~ spl5_13 ),
    inference(backward_demodulation,[],[f56,f295])).

fof(f56,plain,(
    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),sK4)
    & r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),u1_struct_0(sK2))
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK3)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f18,f39,f38,f37,f36,f35])).

fof(f35,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4)
                        & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2))
                        & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                    & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                    & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
                    & v1_funct_1(X3) )
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(sK0,X1,X3,X2),X4)
                      & r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X3,X4),u1_struct_0(X2))
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
                  & v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(X1))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(sK0,X1,X3,X2),X4)
                    & r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X3,X4),u1_struct_0(X2))
                    & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
                & v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(X1))
                & v1_funct_1(X3) )
            & m1_pre_topc(X2,sK0)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,X3,X2),X4)
                  & r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X3,X4),u1_struct_0(X2))
                  & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1))) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
              & v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(sK1))
              & v1_funct_1(X3) )
          & m1_pre_topc(X2,sK0)
          & ~ v2_struct_0(X2) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,X3,X2),X4)
                & r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X3,X4),u1_struct_0(X2))
                & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1))) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
            & v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(sK1))
            & v1_funct_1(X3) )
        & m1_pre_topc(X2,sK0)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X3,X4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,X3,sK2),X4)
              & r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X3,X4),u1_struct_0(sK2))
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1))) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(X3) )
      & m1_pre_topc(sK2,sK0)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X3,X4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,X3,sK2),X4)
            & r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X3,X4),u1_struct_0(sK2))
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1))) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,X4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),X4)
          & r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,X4),u1_struct_0(sK2))
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1))) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      & v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X4] :
        ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,X4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),X4)
        & r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,X4),u1_struct_0(sK2))
        & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1))) )
   => ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),sK4)
      & r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),u1_struct_0(sK2))
      & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4)
                      & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2))
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4)
                      & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2))
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
                      & v1_funct_1(X3) )
                   => ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                       => ( r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2))
                         => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) = k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                    & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
                    & v1_funct_1(X3) )
                 => ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                     => ( r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2))
                       => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) = k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tmap_1)).

fof(f316,plain,
    ( spl5_26
    | ~ spl5_13
    | ~ spl5_22 ),
    inference(avatar_split_clause,[],[f300,f243,f136,f313])).

fof(f313,plain,
    ( spl5_26
  <=> m1_subset_1(k10_relat_1(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f300,plain,
    ( m1_subset_1(k10_relat_1(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl5_13
    | ~ spl5_22 ),
    inference(backward_demodulation,[],[f270,f295])).

fof(f270,plain,
    ( m1_subset_1(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl5_22 ),
    inference(unit_resulting_resolution,[],[f245,f66])).

fof(f307,plain,
    ( spl5_25
    | ~ spl5_13
    | ~ spl5_22 ),
    inference(avatar_split_clause,[],[f301,f243,f136,f304])).

fof(f301,plain,
    ( r1_tarski(k10_relat_1(sK3,sK4),u1_struct_0(sK2))
    | ~ spl5_13
    | ~ spl5_22 ),
    inference(backward_demodulation,[],[f245,f295])).

fof(f266,plain,
    ( spl5_24
    | ~ spl5_21 ),
    inference(avatar_split_clause,[],[f241,f234,f263])).

fof(f263,plain,
    ( spl5_24
  <=> m1_subset_1(k1_relat_1(k7_relat_1(sK3,sK4)),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f241,plain,
    ( m1_subset_1(k1_relat_1(k7_relat_1(sK3,sK4)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl5_21 ),
    inference(unit_resulting_resolution,[],[f236,f66])).

fof(f256,plain,
    ( spl5_23
    | ~ spl5_15
    | ~ spl5_19 ),
    inference(avatar_split_clause,[],[f223,f199,f148,f253])).

fof(f199,plain,
    ( spl5_19
  <=> r1_tarski(k2_relat_1(sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f223,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK3,k2_relat_1(sK3))),u1_struct_0(sK1))
    | ~ spl5_15
    | ~ spl5_19 ),
    inference(unit_resulting_resolution,[],[f158,f201,f69])).

fof(f201,plain,
    ( r1_tarski(k2_relat_1(sK3),u1_struct_0(sK1))
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f199])).

fof(f246,plain,(
    spl5_22 ),
    inference(avatar_split_clause,[],[f55,f243])).

fof(f55,plain,(
    r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f40])).

fof(f237,plain,
    ( spl5_21
    | ~ spl5_12
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f219,f148,f130,f234])).

fof(f130,plain,
    ( spl5_12
  <=> r1_tarski(sK4,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f219,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK3,sK4)),u1_struct_0(sK1))
    | ~ spl5_12
    | ~ spl5_15 ),
    inference(unit_resulting_resolution,[],[f158,f132,f69])).

fof(f132,plain,
    ( r1_tarski(sK4,u1_struct_0(sK1))
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f130])).

fof(f231,plain,
    ( spl5_20
    | ~ spl5_19 ),
    inference(avatar_split_clause,[],[f226,f199,f228])).

fof(f228,plain,
    ( spl5_20
  <=> m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f226,plain,
    ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl5_19 ),
    inference(unit_resulting_resolution,[],[f201,f66])).

fof(f202,plain,
    ( spl5_19
    | ~ spl5_15
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f197,f193,f148,f199])).

fof(f193,plain,
    ( spl5_18
  <=> v5_relat_1(sK3,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f197,plain,
    ( r1_tarski(k2_relat_1(sK3),u1_struct_0(sK1))
    | ~ spl5_15
    | ~ spl5_18 ),
    inference(unit_resulting_resolution,[],[f150,f195,f63])).

fof(f195,plain,
    ( v5_relat_1(sK3,u1_struct_0(sK1))
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f193])).

fof(f196,plain,
    ( spl5_18
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f191,f136,f193])).

fof(f191,plain,
    ( v5_relat_1(sK3,u1_struct_0(sK1))
    | ~ spl5_13 ),
    inference(unit_resulting_resolution,[],[f138,f68])).

fof(f186,plain,
    ( spl5_17
    | ~ spl5_15
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f172,f167,f148,f183])).

fof(f183,plain,
    ( spl5_17
  <=> v1_relat_1(k1_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,sK3))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f167,plain,
    ( spl5_16
  <=> v1_relat_1(k1_relat_1(k7_relat_1(sK3,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f172,plain,
    ( v1_relat_1(k1_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,sK3)))))
    | ~ spl5_15
    | ~ spl5_16 ),
    inference(unit_resulting_resolution,[],[f160,f169,f57])).

fof(f169,plain,
    ( v1_relat_1(k1_relat_1(k7_relat_1(sK3,sK3)))
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f167])).

fof(f160,plain,
    ( ! [X0] : m1_subset_1(k1_relat_1(k7_relat_1(sK3,X0)),k1_zfmisc_1(X0))
    | ~ spl5_15 ),
    inference(unit_resulting_resolution,[],[f158,f66])).

fof(f170,plain,
    ( spl5_16
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f163,f148,f167])).

fof(f163,plain,
    ( v1_relat_1(k1_relat_1(k7_relat_1(sK3,sK3)))
    | ~ spl5_15 ),
    inference(unit_resulting_resolution,[],[f150,f160,f57])).

fof(f151,plain,
    ( spl5_15
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f146,f136,f148])).

fof(f146,plain,
    ( v1_relat_1(sK3)
    | ~ spl5_13 ),
    inference(unit_resulting_resolution,[],[f60,f138,f57])).

fof(f60,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f145,plain,
    ( spl5_14
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f140,f136,f142])).

fof(f140,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | ~ spl5_13 ),
    inference(unit_resulting_resolution,[],[f138,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f139,plain,(
    spl5_13 ),
    inference(avatar_split_clause,[],[f53,f136])).

fof(f53,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f40])).

fof(f133,plain,
    ( spl5_12
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f128,f118,f130])).

fof(f118,plain,
    ( spl5_10
  <=> m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f128,plain,
    ( r1_tarski(sK4,u1_struct_0(sK1))
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f120,f65])).

fof(f120,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f118])).

fof(f126,plain,(
    spl5_11 ),
    inference(avatar_split_clause,[],[f52,f123])).

fof(f52,plain,(
    v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f40])).

fof(f121,plain,(
    spl5_10 ),
    inference(avatar_split_clause,[],[f54,f118])).

fof(f54,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f40])).

fof(f116,plain,(
    spl5_9 ),
    inference(avatar_split_clause,[],[f50,f113])).

fof(f50,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f111,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f51,f108])).

fof(f51,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f106,plain,(
    ~ spl5_7 ),
    inference(avatar_split_clause,[],[f49,f103])).

fof(f103,plain,
    ( spl5_7
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f49,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f101,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f48,f98])).

fof(f48,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f96,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f47,f93])).

fof(f47,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f91,plain,(
    ~ spl5_4 ),
    inference(avatar_split_clause,[],[f46,f88])).

fof(f46,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f86,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f45,f83])).

fof(f45,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f81,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f44,f78])).

fof(f44,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f76,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f43,f73])).

fof(f43,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:54:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.45  % (31506)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.21/0.46  % (31490)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.47  % (31506)Refutation not found, incomplete strategy% (31506)------------------------------
% 0.21/0.47  % (31506)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (31506)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (31506)Memory used [KB]: 10618
% 0.21/0.47  % (31506)Time elapsed: 0.066 s
% 0.21/0.47  % (31506)------------------------------
% 0.21/0.47  % (31506)------------------------------
% 0.21/0.48  % (31491)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.21/0.50  % (31488)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.50  % (31491)Refutation not found, incomplete strategy% (31491)------------------------------
% 0.21/0.50  % (31491)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (31491)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (31491)Memory used [KB]: 10618
% 0.21/0.50  % (31491)Time elapsed: 0.079 s
% 0.21/0.50  % (31491)------------------------------
% 0.21/0.50  % (31491)------------------------------
% 0.21/0.50  % (31483)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.21/0.50  % (31487)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.50  % (31486)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.50  % (31497)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.21/0.51  % (31502)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.21/0.51  % (31505)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.21/0.51  % (31495)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.51  % (31494)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.21/0.51  % (31503)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.21/0.51  % (31496)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.21/0.51  % (31484)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.21/0.52  % (31498)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.21/0.52  % (31485)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.52  % (31499)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.21/0.52  % (31501)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.21/0.53  % (31504)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.21/0.53  % (31489)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.53  % (31500)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.21/0.54  % (31493)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.21/0.54  % (31492)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 1.67/0.57  % (31483)Refutation found. Thanks to Tanya!
% 1.67/0.57  % SZS status Theorem for theBenchmark
% 1.67/0.57  % SZS output start Proof for theBenchmark
% 1.67/0.57  fof(f723,plain,(
% 1.67/0.57    $false),
% 1.67/0.57    inference(avatar_sat_refutation,[],[f76,f81,f86,f91,f96,f101,f106,f111,f116,f121,f126,f133,f139,f145,f151,f170,f186,f196,f202,f231,f237,f246,f256,f266,f307,f316,f341,f351,f368,f493,f585,f608,f625,f650,f720,f722])).
% 1.67/0.57  fof(f722,plain,(
% 1.67/0.57    ~spl5_14 | ~spl5_15 | spl5_35),
% 1.67/0.57    inference(avatar_contradiction_clause,[],[f721])).
% 1.67/0.57  fof(f721,plain,(
% 1.67/0.57    $false | (~spl5_14 | ~spl5_15 | spl5_35)),
% 1.67/0.57    inference(subsumption_resolution,[],[f719,f686])).
% 1.67/0.57  fof(f686,plain,(
% 1.67/0.57    ( ! [X0] : (m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK1))))) ) | (~spl5_14 | ~spl5_15)),
% 1.67/0.57    inference(unit_resulting_resolution,[],[f154,f158,f685,f67])).
% 1.67/0.57  fof(f67,plain,(
% 1.67/0.57    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 1.67/0.57    inference(cnf_transformation,[],[f28])).
% 1.67/0.57  fof(f28,plain,(
% 1.67/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 1.67/0.57    inference(flattening,[],[f27])).
% 1.67/0.57  fof(f27,plain,(
% 1.67/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 1.67/0.57    inference(ennf_transformation,[],[f10])).
% 1.67/0.57  fof(f10,axiom,(
% 1.67/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.67/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).
% 1.67/0.57  fof(f685,plain,(
% 1.67/0.57    ( ! [X0] : (r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),u1_struct_0(sK1))) ) | (~spl5_14 | ~spl5_15)),
% 1.67/0.57    inference(unit_resulting_resolution,[],[f154,f682,f63])).
% 1.67/0.57  fof(f63,plain,(
% 1.67/0.57    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.67/0.57    inference(cnf_transformation,[],[f41])).
% 1.67/0.57  fof(f41,plain,(
% 1.67/0.57    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.67/0.57    inference(nnf_transformation,[],[f26])).
% 1.67/0.57  fof(f26,plain,(
% 1.67/0.57    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.67/0.57    inference(ennf_transformation,[],[f4])).
% 1.67/0.57  fof(f4,axiom,(
% 1.67/0.57    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.67/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 1.67/0.57  fof(f682,plain,(
% 1.67/0.57    ( ! [X0] : (v5_relat_1(k7_relat_1(sK3,X0),u1_struct_0(sK1))) ) | (~spl5_14 | ~spl5_15)),
% 1.67/0.57    inference(unit_resulting_resolution,[],[f346,f68])).
% 1.67/0.57  fof(f68,plain,(
% 1.67/0.57    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.67/0.57    inference(cnf_transformation,[],[f29])).
% 1.67/0.57  fof(f29,plain,(
% 1.67/0.57    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.67/0.57    inference(ennf_transformation,[],[f16])).
% 1.67/0.57  fof(f16,plain,(
% 1.67/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 1.67/0.57    inference(pure_predicate_removal,[],[f8])).
% 1.67/0.57  fof(f8,axiom,(
% 1.67/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.67/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.67/0.57  fof(f346,plain,(
% 1.67/0.57    ( ! [X0] : (m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))) ) | (~spl5_14 | ~spl5_15)),
% 1.67/0.57    inference(unit_resulting_resolution,[],[f215,f66])).
% 1.67/0.57  fof(f66,plain,(
% 1.67/0.57    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.67/0.57    inference(cnf_transformation,[],[f42])).
% 1.67/0.57  fof(f42,plain,(
% 1.67/0.57    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.67/0.57    inference(nnf_transformation,[],[f2])).
% 1.67/0.57  fof(f2,axiom,(
% 1.67/0.57    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.67/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.67/0.57  fof(f215,plain,(
% 1.67/0.57    ( ! [X0] : (r1_tarski(k7_relat_1(sK3,X0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ) | (~spl5_14 | ~spl5_15)),
% 1.67/0.57    inference(unit_resulting_resolution,[],[f152,f144,f69])).
% 1.67/0.57  fof(f69,plain,(
% 1.67/0.57    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 1.67/0.57    inference(cnf_transformation,[],[f31])).
% 1.67/0.57  fof(f31,plain,(
% 1.67/0.57    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.67/0.57    inference(flattening,[],[f30])).
% 1.67/0.57  fof(f30,plain,(
% 1.67/0.57    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.67/0.57    inference(ennf_transformation,[],[f1])).
% 1.67/0.57  fof(f1,axiom,(
% 1.67/0.57    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.67/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.67/0.57  fof(f144,plain,(
% 1.67/0.57    r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) | ~spl5_14),
% 1.67/0.57    inference(avatar_component_clause,[],[f142])).
% 1.67/0.57  fof(f142,plain,(
% 1.67/0.57    spl5_14 <=> r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))),
% 1.67/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 1.67/0.57  fof(f152,plain,(
% 1.67/0.57    ( ! [X0] : (r1_tarski(k7_relat_1(sK3,X0),sK3)) ) | ~spl5_15),
% 1.67/0.57    inference(unit_resulting_resolution,[],[f150,f61])).
% 1.67/0.57  fof(f61,plain,(
% 1.67/0.57    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 1.67/0.57    inference(cnf_transformation,[],[f24])).
% 1.67/0.57  fof(f24,plain,(
% 1.67/0.57    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 1.67/0.57    inference(ennf_transformation,[],[f7])).
% 1.67/0.57  fof(f7,axiom,(
% 1.67/0.57    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 1.67/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).
% 1.67/0.57  fof(f150,plain,(
% 1.67/0.57    v1_relat_1(sK3) | ~spl5_15),
% 1.67/0.57    inference(avatar_component_clause,[],[f148])).
% 1.67/0.57  fof(f148,plain,(
% 1.67/0.57    spl5_15 <=> v1_relat_1(sK3)),
% 1.67/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 1.67/0.57  fof(f158,plain,(
% 1.67/0.57    ( ! [X0] : (r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),X0)) ) | ~spl5_15),
% 1.67/0.57    inference(unit_resulting_resolution,[],[f150,f62])).
% 1.67/0.57  fof(f62,plain,(
% 1.67/0.57    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 1.67/0.57    inference(cnf_transformation,[],[f25])).
% 1.67/0.57  fof(f25,plain,(
% 1.67/0.57    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 1.67/0.57    inference(ennf_transformation,[],[f6])).
% 1.67/0.57  fof(f6,axiom,(
% 1.67/0.57    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 1.67/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).
% 1.67/0.57  fof(f154,plain,(
% 1.67/0.57    ( ! [X0] : (v1_relat_1(k7_relat_1(sK3,X0))) ) | ~spl5_15),
% 1.67/0.57    inference(unit_resulting_resolution,[],[f150,f153,f57])).
% 1.67/0.57  fof(f57,plain,(
% 1.67/0.57    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.67/0.57    inference(cnf_transformation,[],[f19])).
% 1.67/0.57  fof(f19,plain,(
% 1.67/0.57    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.67/0.57    inference(ennf_transformation,[],[f3])).
% 1.67/0.57  fof(f3,axiom,(
% 1.67/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.67/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.67/0.57  fof(f153,plain,(
% 1.67/0.57    ( ! [X0] : (m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(sK3))) ) | ~spl5_15),
% 1.67/0.57    inference(unit_resulting_resolution,[],[f152,f66])).
% 1.67/0.57  fof(f719,plain,(
% 1.67/0.57    ~m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | spl5_35),
% 1.67/0.57    inference(avatar_component_clause,[],[f717])).
% 1.67/0.57  fof(f717,plain,(
% 1.67/0.57    spl5_35 <=> m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 1.67/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).
% 1.67/0.57  fof(f720,plain,(
% 1.67/0.57    ~spl5_35 | spl5_1 | ~spl5_2 | ~spl5_3 | spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_8 | ~spl5_9 | ~spl5_11 | ~spl5_13 | spl5_27 | ~spl5_30),
% 1.67/0.57    inference(avatar_split_clause,[],[f510,f490,f338,f136,f123,f113,f108,f98,f93,f88,f83,f78,f73,f717])).
% 1.67/0.57  fof(f73,plain,(
% 1.67/0.57    spl5_1 <=> v2_struct_0(sK0)),
% 1.67/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.67/0.57  fof(f78,plain,(
% 1.67/0.57    spl5_2 <=> v2_pre_topc(sK0)),
% 1.67/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.67/0.57  fof(f83,plain,(
% 1.67/0.57    spl5_3 <=> l1_pre_topc(sK0)),
% 1.67/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.67/0.57  fof(f88,plain,(
% 1.67/0.57    spl5_4 <=> v2_struct_0(sK1)),
% 1.67/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.67/0.57  fof(f93,plain,(
% 1.67/0.57    spl5_5 <=> v2_pre_topc(sK1)),
% 1.67/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.67/0.57  fof(f98,plain,(
% 1.67/0.57    spl5_6 <=> l1_pre_topc(sK1)),
% 1.67/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 1.67/0.57  fof(f108,plain,(
% 1.67/0.57    spl5_8 <=> v1_funct_1(sK3)),
% 1.67/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 1.67/0.57  fof(f113,plain,(
% 1.67/0.57    spl5_9 <=> m1_pre_topc(sK2,sK0)),
% 1.67/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 1.67/0.57  fof(f123,plain,(
% 1.67/0.57    spl5_11 <=> v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))),
% 1.67/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 1.67/0.57  fof(f136,plain,(
% 1.67/0.57    spl5_13 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 1.67/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 1.67/0.57  fof(f338,plain,(
% 1.67/0.57    spl5_27 <=> k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),sK4) = k10_relat_1(sK3,sK4)),
% 1.67/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).
% 1.67/0.57  fof(f490,plain,(
% 1.67/0.57    spl5_30 <=> k10_relat_1(sK3,sK4) = k10_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK4)),
% 1.67/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).
% 1.67/0.57  fof(f510,plain,(
% 1.67/0.57    ~m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | (spl5_1 | ~spl5_2 | ~spl5_3 | spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_8 | ~spl5_9 | ~spl5_11 | ~spl5_13 | spl5_27 | ~spl5_30)),
% 1.67/0.57    inference(subsumption_resolution,[],[f509,f492])).
% 1.67/0.57  fof(f492,plain,(
% 1.67/0.57    k10_relat_1(sK3,sK4) = k10_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK4) | ~spl5_30),
% 1.67/0.57    inference(avatar_component_clause,[],[f490])).
% 1.67/0.57  fof(f509,plain,(
% 1.67/0.57    k10_relat_1(sK3,sK4) != k10_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK4) | ~m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | (spl5_1 | ~spl5_2 | ~spl5_3 | spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_8 | ~spl5_9 | ~spl5_11 | ~spl5_13 | spl5_27)),
% 1.67/0.57    inference(forward_demodulation,[],[f507,f506])).
% 1.67/0.57  fof(f506,plain,(
% 1.67/0.57    k2_tmap_1(sK0,sK1,sK3,sK2) = k7_relat_1(sK3,u1_struct_0(sK2)) | (spl5_1 | ~spl5_2 | ~spl5_3 | spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_8 | ~spl5_9 | ~spl5_11 | ~spl5_13)),
% 1.67/0.57    inference(forward_demodulation,[],[f504,f460])).
% 1.67/0.57  fof(f460,plain,(
% 1.67/0.57    ( ! [X0] : (k7_relat_1(sK3,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,X0)) ) | (~spl5_8 | ~spl5_13)),
% 1.67/0.57    inference(unit_resulting_resolution,[],[f110,f138,f71])).
% 1.67/0.57  fof(f71,plain,(
% 1.67/0.57    ( ! [X2,X0,X3,X1] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.67/0.57    inference(cnf_transformation,[],[f34])).
% 1.67/0.57  fof(f34,plain,(
% 1.67/0.57    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.67/0.57    inference(flattening,[],[f33])).
% 1.67/0.57  fof(f33,plain,(
% 1.67/0.57    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.67/0.57    inference(ennf_transformation,[],[f11])).
% 1.67/0.57  fof(f11,axiom,(
% 1.67/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 1.67/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 1.67/0.57  fof(f138,plain,(
% 1.67/0.57    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl5_13),
% 1.67/0.57    inference(avatar_component_clause,[],[f136])).
% 1.67/0.57  fof(f110,plain,(
% 1.67/0.57    v1_funct_1(sK3) | ~spl5_8),
% 1.67/0.57    inference(avatar_component_clause,[],[f108])).
% 1.67/0.57  fof(f504,plain,(
% 1.67/0.57    k2_tmap_1(sK0,sK1,sK3,sK2) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,u1_struct_0(sK2)) | (spl5_1 | ~spl5_2 | ~spl5_3 | spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_8 | ~spl5_9 | ~spl5_11 | ~spl5_13)),
% 1.67/0.57    inference(unit_resulting_resolution,[],[f75,f80,f85,f90,f95,f100,f110,f115,f125,f138,f58])).
% 1.67/0.57  fof(f58,plain,(
% 1.67/0.57    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.67/0.57    inference(cnf_transformation,[],[f21])).
% 1.67/0.57  fof(f21,plain,(
% 1.67/0.57    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.67/0.57    inference(flattening,[],[f20])).
% 1.67/0.57  fof(f20,plain,(
% 1.67/0.57    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.67/0.57    inference(ennf_transformation,[],[f13])).
% 1.67/0.57  fof(f13,axiom,(
% 1.67/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 1.67/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).
% 1.67/0.57  fof(f125,plain,(
% 1.67/0.57    v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl5_11),
% 1.67/0.57    inference(avatar_component_clause,[],[f123])).
% 1.67/0.57  fof(f115,plain,(
% 1.67/0.57    m1_pre_topc(sK2,sK0) | ~spl5_9),
% 1.67/0.57    inference(avatar_component_clause,[],[f113])).
% 1.67/0.57  fof(f100,plain,(
% 1.67/0.57    l1_pre_topc(sK1) | ~spl5_6),
% 1.67/0.57    inference(avatar_component_clause,[],[f98])).
% 1.67/0.57  fof(f95,plain,(
% 1.67/0.57    v2_pre_topc(sK1) | ~spl5_5),
% 1.67/0.57    inference(avatar_component_clause,[],[f93])).
% 1.67/0.57  fof(f90,plain,(
% 1.67/0.57    ~v2_struct_0(sK1) | spl5_4),
% 1.67/0.57    inference(avatar_component_clause,[],[f88])).
% 1.67/0.57  fof(f85,plain,(
% 1.67/0.57    l1_pre_topc(sK0) | ~spl5_3),
% 1.67/0.57    inference(avatar_component_clause,[],[f83])).
% 1.67/0.57  fof(f80,plain,(
% 1.67/0.57    v2_pre_topc(sK0) | ~spl5_2),
% 1.67/0.57    inference(avatar_component_clause,[],[f78])).
% 1.67/0.57  fof(f75,plain,(
% 1.67/0.57    ~v2_struct_0(sK0) | spl5_1),
% 1.67/0.57    inference(avatar_component_clause,[],[f73])).
% 1.67/0.57  fof(f507,plain,(
% 1.67/0.57    ~m1_subset_1(k7_relat_1(sK3,u1_struct_0(sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | k10_relat_1(sK3,sK4) != k10_relat_1(k2_tmap_1(sK0,sK1,sK3,sK2),sK4) | (spl5_1 | ~spl5_2 | ~spl5_3 | spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_8 | ~spl5_9 | ~spl5_11 | ~spl5_13 | spl5_27)),
% 1.67/0.57    inference(backward_demodulation,[],[f363,f506])).
% 1.67/0.57  fof(f363,plain,(
% 1.67/0.57    k10_relat_1(sK3,sK4) != k10_relat_1(k2_tmap_1(sK0,sK1,sK3,sK2),sK4) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | spl5_27),
% 1.67/0.57    inference(superposition,[],[f340,f70])).
% 1.67/0.57  fof(f70,plain,(
% 1.67/0.57    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.67/0.57    inference(cnf_transformation,[],[f32])).
% 1.67/0.57  fof(f32,plain,(
% 1.67/0.57    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.67/0.57    inference(ennf_transformation,[],[f9])).
% 1.67/0.57  fof(f9,axiom,(
% 1.67/0.57    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 1.67/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 1.67/0.57  fof(f340,plain,(
% 1.67/0.57    k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),sK4) != k10_relat_1(sK3,sK4) | spl5_27),
% 1.67/0.57    inference(avatar_component_clause,[],[f338])).
% 1.67/0.57  fof(f650,plain,(
% 1.67/0.57    spl5_34 | ~spl5_15 | ~spl5_21),
% 1.67/0.57    inference(avatar_split_clause,[],[f238,f234,f148,f647])).
% 1.67/0.57  fof(f647,plain,(
% 1.67/0.57    spl5_34 <=> r1_tarski(k1_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,sK4)))),u1_struct_0(sK1))),
% 1.67/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).
% 1.67/0.57  fof(f234,plain,(
% 1.67/0.57    spl5_21 <=> r1_tarski(k1_relat_1(k7_relat_1(sK3,sK4)),u1_struct_0(sK1))),
% 1.67/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 1.67/0.57  fof(f238,plain,(
% 1.67/0.57    r1_tarski(k1_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,sK4)))),u1_struct_0(sK1)) | (~spl5_15 | ~spl5_21)),
% 1.67/0.57    inference(unit_resulting_resolution,[],[f158,f236,f69])).
% 1.67/0.57  fof(f236,plain,(
% 1.67/0.57    r1_tarski(k1_relat_1(k7_relat_1(sK3,sK4)),u1_struct_0(sK1)) | ~spl5_21),
% 1.67/0.57    inference(avatar_component_clause,[],[f234])).
% 1.67/0.57  fof(f625,plain,(
% 1.67/0.57    spl5_33 | ~spl5_14 | ~spl5_15),
% 1.67/0.57    inference(avatar_split_clause,[],[f216,f148,f142,f622])).
% 1.67/0.57  fof(f622,plain,(
% 1.67/0.57    spl5_33 <=> r1_tarski(k1_relat_1(k7_relat_1(sK3,sK3)),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))),
% 1.67/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).
% 1.67/0.57  fof(f216,plain,(
% 1.67/0.57    r1_tarski(k1_relat_1(k7_relat_1(sK3,sK3)),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) | (~spl5_14 | ~spl5_15)),
% 1.67/0.57    inference(unit_resulting_resolution,[],[f158,f144,f69])).
% 1.67/0.57  fof(f608,plain,(
% 1.67/0.57    spl5_32 | spl5_1 | ~spl5_2 | ~spl5_3 | spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_8 | ~spl5_9 | ~spl5_11 | ~spl5_13),
% 1.67/0.57    inference(avatar_split_clause,[],[f506,f136,f123,f113,f108,f98,f93,f88,f83,f78,f73,f605])).
% 1.67/0.57  fof(f605,plain,(
% 1.67/0.57    spl5_32 <=> k2_tmap_1(sK0,sK1,sK3,sK2) = k7_relat_1(sK3,u1_struct_0(sK2))),
% 1.67/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).
% 1.67/0.57  fof(f585,plain,(
% 1.67/0.57    ~spl5_31 | spl5_1 | ~spl5_2 | ~spl5_3 | spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_8 | ~spl5_9 | ~spl5_11 | ~spl5_13 | spl5_27),
% 1.67/0.57    inference(avatar_split_clause,[],[f508,f338,f136,f123,f113,f108,f98,f93,f88,f83,f78,f73,f582])).
% 1.67/0.57  fof(f582,plain,(
% 1.67/0.57    spl5_31 <=> k10_relat_1(sK3,sK4) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)),
% 1.67/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).
% 1.67/0.57  fof(f508,plain,(
% 1.67/0.57    k10_relat_1(sK3,sK4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k7_relat_1(sK3,u1_struct_0(sK2)),sK4) | (spl5_1 | ~spl5_2 | ~spl5_3 | spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_8 | ~spl5_9 | ~spl5_11 | ~spl5_13 | spl5_27)),
% 1.67/0.57    inference(backward_demodulation,[],[f340,f506])).
% 1.67/0.57  fof(f493,plain,(
% 1.67/0.57    spl5_30 | ~spl5_8 | ~spl5_15 | ~spl5_25),
% 1.67/0.57    inference(avatar_split_clause,[],[f488,f304,f148,f108,f490])).
% 1.67/0.57  fof(f304,plain,(
% 1.67/0.57    spl5_25 <=> r1_tarski(k10_relat_1(sK3,sK4),u1_struct_0(sK2))),
% 1.67/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 1.67/0.57  fof(f488,plain,(
% 1.67/0.57    k10_relat_1(sK3,sK4) = k10_relat_1(k7_relat_1(sK3,u1_struct_0(sK2)),sK4) | (~spl5_8 | ~spl5_15 | ~spl5_25)),
% 1.67/0.57    inference(unit_resulting_resolution,[],[f150,f110,f306,f59])).
% 1.67/0.57  fof(f59,plain,(
% 1.67/0.57    ( ! [X2,X0,X1] : (k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) | ~r1_tarski(k10_relat_1(X0,X2),X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.67/0.57    inference(cnf_transformation,[],[f23])).
% 1.67/0.57  fof(f23,plain,(
% 1.67/0.57    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) | ~r1_tarski(k10_relat_1(X0,X2),X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.67/0.57    inference(flattening,[],[f22])).
% 1.67/0.57  fof(f22,plain,(
% 1.67/0.57    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) | ~r1_tarski(k10_relat_1(X0,X2),X1)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.67/0.57    inference(ennf_transformation,[],[f12])).
% 1.67/0.57  fof(f12,axiom,(
% 1.67/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 1.67/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_funct_2)).
% 1.67/0.57  fof(f306,plain,(
% 1.67/0.57    r1_tarski(k10_relat_1(sK3,sK4),u1_struct_0(sK2)) | ~spl5_25),
% 1.67/0.57    inference(avatar_component_clause,[],[f304])).
% 1.67/0.57  fof(f368,plain,(
% 1.67/0.57    spl5_29 | ~spl5_23),
% 1.67/0.57    inference(avatar_split_clause,[],[f260,f253,f365])).
% 1.67/0.57  fof(f365,plain,(
% 1.67/0.57    spl5_29 <=> m1_subset_1(k1_relat_1(k7_relat_1(sK3,k2_relat_1(sK3))),k1_zfmisc_1(u1_struct_0(sK1)))),
% 1.67/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).
% 1.67/0.57  fof(f253,plain,(
% 1.67/0.57    spl5_23 <=> r1_tarski(k1_relat_1(k7_relat_1(sK3,k2_relat_1(sK3))),u1_struct_0(sK1))),
% 1.67/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 1.67/0.57  fof(f260,plain,(
% 1.67/0.57    m1_subset_1(k1_relat_1(k7_relat_1(sK3,k2_relat_1(sK3))),k1_zfmisc_1(u1_struct_0(sK1))) | ~spl5_23),
% 1.67/0.57    inference(unit_resulting_resolution,[],[f255,f66])).
% 1.67/0.57  fof(f255,plain,(
% 1.67/0.57    r1_tarski(k1_relat_1(k7_relat_1(sK3,k2_relat_1(sK3))),u1_struct_0(sK1)) | ~spl5_23),
% 1.67/0.57    inference(avatar_component_clause,[],[f253])).
% 1.67/0.57  fof(f351,plain,(
% 1.67/0.57    spl5_28 | ~spl5_13 | ~spl5_15 | ~spl5_22),
% 1.67/0.57    inference(avatar_split_clause,[],[f297,f243,f148,f136,f348])).
% 1.67/0.57  fof(f348,plain,(
% 1.67/0.57    spl5_28 <=> r1_tarski(k1_relat_1(k7_relat_1(sK3,k10_relat_1(sK3,sK4))),u1_struct_0(sK2))),
% 1.67/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).
% 1.67/0.57  fof(f243,plain,(
% 1.67/0.57    spl5_22 <=> r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),u1_struct_0(sK2))),
% 1.67/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 1.67/0.57  fof(f297,plain,(
% 1.67/0.57    r1_tarski(k1_relat_1(k7_relat_1(sK3,k10_relat_1(sK3,sK4))),u1_struct_0(sK2)) | (~spl5_13 | ~spl5_15 | ~spl5_22)),
% 1.67/0.57    inference(backward_demodulation,[],[f267,f295])).
% 1.67/0.57  fof(f295,plain,(
% 1.67/0.57    ( ! [X0] : (k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,X0) = k10_relat_1(sK3,X0)) ) | ~spl5_13),
% 1.67/0.57    inference(unit_resulting_resolution,[],[f138,f70])).
% 1.67/0.57  fof(f267,plain,(
% 1.67/0.57    r1_tarski(k1_relat_1(k7_relat_1(sK3,k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4))),u1_struct_0(sK2)) | (~spl5_15 | ~spl5_22)),
% 1.67/0.57    inference(unit_resulting_resolution,[],[f158,f245,f69])).
% 1.67/0.57  fof(f245,plain,(
% 1.67/0.57    r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),u1_struct_0(sK2)) | ~spl5_22),
% 1.67/0.57    inference(avatar_component_clause,[],[f243])).
% 1.67/0.57  fof(f341,plain,(
% 1.67/0.57    ~spl5_27 | ~spl5_13),
% 1.67/0.57    inference(avatar_split_clause,[],[f302,f136,f338])).
% 1.67/0.57  fof(f302,plain,(
% 1.67/0.57    k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),sK4) != k10_relat_1(sK3,sK4) | ~spl5_13),
% 1.67/0.57    inference(backward_demodulation,[],[f56,f295])).
% 1.67/0.57  fof(f56,plain,(
% 1.67/0.57    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),sK4)),
% 1.67/0.57    inference(cnf_transformation,[],[f40])).
% 1.67/0.57  fof(f40,plain,(
% 1.67/0.57    ((((k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),sK4) & r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),u1_struct_0(sK2)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.67/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f18,f39,f38,f37,f36,f35])).
% 1.67/0.57  fof(f35,plain,(
% 1.67/0.57    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4) & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(sK0,X1,X3,X2),X4) & r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X3,X4),u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.67/0.57    introduced(choice_axiom,[])).
% 1.67/0.57  fof(f36,plain,(
% 1.67/0.57    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(sK0,X1,X3,X2),X4) & r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X3,X4),u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,X3,X2),X4) & r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X3,X4),u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 1.67/0.57    introduced(choice_axiom,[])).
% 1.67/0.57  fof(f37,plain,(
% 1.67/0.57    ? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,X3,X2),X4) & r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X3,X4),u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X3,X4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,X3,sK2),X4) & r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X3,X4),u1_struct_0(sK2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2))),
% 1.67/0.57    introduced(choice_axiom,[])).
% 1.67/0.57  fof(f38,plain,(
% 1.67/0.57    ? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X3,X4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,X3,sK2),X4) & r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X3,X4),u1_struct_0(sK2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X3)) => (? [X4] : (k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,X4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),X4) & r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,X4),u1_struct_0(sK2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK3))),
% 1.67/0.57    introduced(choice_axiom,[])).
% 1.67/0.57  fof(f39,plain,(
% 1.67/0.57    ? [X4] : (k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,X4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),X4) & r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,X4),u1_struct_0(sK2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK1)))) => (k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tmap_1(sK0,sK1,sK3,sK2),sK4) & r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),u1_struct_0(sK2)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))))),
% 1.67/0.57    introduced(choice_axiom,[])).
% 1.67/0.57  fof(f18,plain,(
% 1.67/0.57    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4) & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.67/0.57    inference(flattening,[],[f17])).
% 1.67/0.57  fof(f17,plain,(
% 1.67/0.57    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) != k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4) & r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.67/0.57    inference(ennf_transformation,[],[f15])).
% 1.67/0.57  fof(f15,negated_conjecture,(
% 1.67/0.57    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => (r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2)) => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) = k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4)))))))),
% 1.67/0.57    inference(negated_conjecture,[],[f14])).
% 1.67/0.57  fof(f14,conjecture,(
% 1.67/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => (r1_tarski(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4),u1_struct_0(X2)) => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X3,X4) = k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tmap_1(X0,X1,X3,X2),X4)))))))),
% 1.67/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tmap_1)).
% 1.67/0.57  fof(f316,plain,(
% 1.67/0.57    spl5_26 | ~spl5_13 | ~spl5_22),
% 1.67/0.57    inference(avatar_split_clause,[],[f300,f243,f136,f313])).
% 1.67/0.57  fof(f313,plain,(
% 1.67/0.57    spl5_26 <=> m1_subset_1(k10_relat_1(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2)))),
% 1.67/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 1.67/0.57  fof(f300,plain,(
% 1.67/0.57    m1_subset_1(k10_relat_1(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2))) | (~spl5_13 | ~spl5_22)),
% 1.67/0.57    inference(backward_demodulation,[],[f270,f295])).
% 1.67/0.57  fof(f270,plain,(
% 1.67/0.57    m1_subset_1(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2))) | ~spl5_22),
% 1.67/0.57    inference(unit_resulting_resolution,[],[f245,f66])).
% 1.67/0.57  fof(f307,plain,(
% 1.67/0.57    spl5_25 | ~spl5_13 | ~spl5_22),
% 1.67/0.57    inference(avatar_split_clause,[],[f301,f243,f136,f304])).
% 1.67/0.57  fof(f301,plain,(
% 1.67/0.57    r1_tarski(k10_relat_1(sK3,sK4),u1_struct_0(sK2)) | (~spl5_13 | ~spl5_22)),
% 1.67/0.57    inference(backward_demodulation,[],[f245,f295])).
% 1.67/0.57  fof(f266,plain,(
% 1.67/0.57    spl5_24 | ~spl5_21),
% 1.67/0.57    inference(avatar_split_clause,[],[f241,f234,f263])).
% 1.67/0.57  fof(f263,plain,(
% 1.67/0.57    spl5_24 <=> m1_subset_1(k1_relat_1(k7_relat_1(sK3,sK4)),k1_zfmisc_1(u1_struct_0(sK1)))),
% 1.67/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 1.67/0.57  fof(f241,plain,(
% 1.67/0.57    m1_subset_1(k1_relat_1(k7_relat_1(sK3,sK4)),k1_zfmisc_1(u1_struct_0(sK1))) | ~spl5_21),
% 1.67/0.57    inference(unit_resulting_resolution,[],[f236,f66])).
% 1.67/0.57  fof(f256,plain,(
% 1.67/0.57    spl5_23 | ~spl5_15 | ~spl5_19),
% 1.67/0.57    inference(avatar_split_clause,[],[f223,f199,f148,f253])).
% 1.67/0.57  fof(f199,plain,(
% 1.67/0.57    spl5_19 <=> r1_tarski(k2_relat_1(sK3),u1_struct_0(sK1))),
% 1.67/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 1.67/0.57  fof(f223,plain,(
% 1.67/0.57    r1_tarski(k1_relat_1(k7_relat_1(sK3,k2_relat_1(sK3))),u1_struct_0(sK1)) | (~spl5_15 | ~spl5_19)),
% 1.67/0.57    inference(unit_resulting_resolution,[],[f158,f201,f69])).
% 1.67/0.57  fof(f201,plain,(
% 1.67/0.57    r1_tarski(k2_relat_1(sK3),u1_struct_0(sK1)) | ~spl5_19),
% 1.67/0.57    inference(avatar_component_clause,[],[f199])).
% 1.67/0.57  fof(f246,plain,(
% 1.67/0.57    spl5_22),
% 1.67/0.57    inference(avatar_split_clause,[],[f55,f243])).
% 1.67/0.57  fof(f55,plain,(
% 1.67/0.57    r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK3,sK4),u1_struct_0(sK2))),
% 1.67/0.57    inference(cnf_transformation,[],[f40])).
% 1.67/0.57  fof(f237,plain,(
% 1.67/0.57    spl5_21 | ~spl5_12 | ~spl5_15),
% 1.67/0.57    inference(avatar_split_clause,[],[f219,f148,f130,f234])).
% 1.67/0.57  fof(f130,plain,(
% 1.67/0.57    spl5_12 <=> r1_tarski(sK4,u1_struct_0(sK1))),
% 1.67/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 1.67/0.57  fof(f219,plain,(
% 1.67/0.57    r1_tarski(k1_relat_1(k7_relat_1(sK3,sK4)),u1_struct_0(sK1)) | (~spl5_12 | ~spl5_15)),
% 1.67/0.57    inference(unit_resulting_resolution,[],[f158,f132,f69])).
% 1.67/0.57  fof(f132,plain,(
% 1.67/0.57    r1_tarski(sK4,u1_struct_0(sK1)) | ~spl5_12),
% 1.67/0.57    inference(avatar_component_clause,[],[f130])).
% 1.67/0.57  fof(f231,plain,(
% 1.67/0.57    spl5_20 | ~spl5_19),
% 1.67/0.57    inference(avatar_split_clause,[],[f226,f199,f228])).
% 1.67/0.57  fof(f228,plain,(
% 1.67/0.57    spl5_20 <=> m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(u1_struct_0(sK1)))),
% 1.67/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 1.67/0.57  fof(f226,plain,(
% 1.67/0.57    m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(u1_struct_0(sK1))) | ~spl5_19),
% 1.67/0.57    inference(unit_resulting_resolution,[],[f201,f66])).
% 1.67/0.57  fof(f202,plain,(
% 1.67/0.57    spl5_19 | ~spl5_15 | ~spl5_18),
% 1.67/0.57    inference(avatar_split_clause,[],[f197,f193,f148,f199])).
% 1.67/0.57  fof(f193,plain,(
% 1.67/0.57    spl5_18 <=> v5_relat_1(sK3,u1_struct_0(sK1))),
% 1.67/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 1.67/0.57  fof(f197,plain,(
% 1.67/0.57    r1_tarski(k2_relat_1(sK3),u1_struct_0(sK1)) | (~spl5_15 | ~spl5_18)),
% 1.67/0.57    inference(unit_resulting_resolution,[],[f150,f195,f63])).
% 1.67/0.57  fof(f195,plain,(
% 1.67/0.57    v5_relat_1(sK3,u1_struct_0(sK1)) | ~spl5_18),
% 1.67/0.57    inference(avatar_component_clause,[],[f193])).
% 1.67/0.57  fof(f196,plain,(
% 1.67/0.57    spl5_18 | ~spl5_13),
% 1.67/0.57    inference(avatar_split_clause,[],[f191,f136,f193])).
% 1.67/0.57  fof(f191,plain,(
% 1.67/0.57    v5_relat_1(sK3,u1_struct_0(sK1)) | ~spl5_13),
% 1.67/0.57    inference(unit_resulting_resolution,[],[f138,f68])).
% 1.67/0.58  fof(f186,plain,(
% 1.67/0.58    spl5_17 | ~spl5_15 | ~spl5_16),
% 1.67/0.58    inference(avatar_split_clause,[],[f172,f167,f148,f183])).
% 1.67/0.58  fof(f183,plain,(
% 1.67/0.58    spl5_17 <=> v1_relat_1(k1_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,sK3)))))),
% 1.67/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 1.67/0.58  fof(f167,plain,(
% 1.67/0.58    spl5_16 <=> v1_relat_1(k1_relat_1(k7_relat_1(sK3,sK3)))),
% 1.67/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 1.67/0.58  fof(f172,plain,(
% 1.67/0.58    v1_relat_1(k1_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,sK3))))) | (~spl5_15 | ~spl5_16)),
% 1.67/0.58    inference(unit_resulting_resolution,[],[f160,f169,f57])).
% 1.67/0.58  fof(f169,plain,(
% 1.67/0.58    v1_relat_1(k1_relat_1(k7_relat_1(sK3,sK3))) | ~spl5_16),
% 1.67/0.58    inference(avatar_component_clause,[],[f167])).
% 1.67/0.58  fof(f160,plain,(
% 1.67/0.58    ( ! [X0] : (m1_subset_1(k1_relat_1(k7_relat_1(sK3,X0)),k1_zfmisc_1(X0))) ) | ~spl5_15),
% 1.67/0.58    inference(unit_resulting_resolution,[],[f158,f66])).
% 1.67/0.58  fof(f170,plain,(
% 1.67/0.58    spl5_16 | ~spl5_15),
% 1.67/0.58    inference(avatar_split_clause,[],[f163,f148,f167])).
% 1.67/0.58  fof(f163,plain,(
% 1.67/0.58    v1_relat_1(k1_relat_1(k7_relat_1(sK3,sK3))) | ~spl5_15),
% 1.67/0.58    inference(unit_resulting_resolution,[],[f150,f160,f57])).
% 1.67/0.58  fof(f151,plain,(
% 1.67/0.58    spl5_15 | ~spl5_13),
% 1.67/0.58    inference(avatar_split_clause,[],[f146,f136,f148])).
% 1.67/0.58  fof(f146,plain,(
% 1.67/0.58    v1_relat_1(sK3) | ~spl5_13),
% 1.67/0.58    inference(unit_resulting_resolution,[],[f60,f138,f57])).
% 1.67/0.58  fof(f60,plain,(
% 1.67/0.58    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.67/0.58    inference(cnf_transformation,[],[f5])).
% 1.67/0.58  fof(f5,axiom,(
% 1.67/0.58    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.67/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.67/0.58  fof(f145,plain,(
% 1.67/0.58    spl5_14 | ~spl5_13),
% 1.67/0.58    inference(avatar_split_clause,[],[f140,f136,f142])).
% 1.67/0.58  fof(f140,plain,(
% 1.67/0.58    r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) | ~spl5_13),
% 1.67/0.58    inference(unit_resulting_resolution,[],[f138,f65])).
% 1.67/0.58  fof(f65,plain,(
% 1.67/0.58    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.67/0.58    inference(cnf_transformation,[],[f42])).
% 1.67/0.58  fof(f139,plain,(
% 1.67/0.58    spl5_13),
% 1.67/0.58    inference(avatar_split_clause,[],[f53,f136])).
% 1.67/0.58  fof(f53,plain,(
% 1.67/0.58    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 1.67/0.58    inference(cnf_transformation,[],[f40])).
% 1.67/0.58  fof(f133,plain,(
% 1.67/0.58    spl5_12 | ~spl5_10),
% 1.67/0.58    inference(avatar_split_clause,[],[f128,f118,f130])).
% 1.67/0.58  fof(f118,plain,(
% 1.67/0.58    spl5_10 <=> m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))),
% 1.67/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 1.67/0.58  fof(f128,plain,(
% 1.67/0.58    r1_tarski(sK4,u1_struct_0(sK1)) | ~spl5_10),
% 1.67/0.58    inference(unit_resulting_resolution,[],[f120,f65])).
% 1.67/0.58  fof(f120,plain,(
% 1.67/0.58    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) | ~spl5_10),
% 1.67/0.58    inference(avatar_component_clause,[],[f118])).
% 1.67/0.58  fof(f126,plain,(
% 1.67/0.58    spl5_11),
% 1.67/0.58    inference(avatar_split_clause,[],[f52,f123])).
% 1.67/0.58  fof(f52,plain,(
% 1.67/0.58    v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(sK1))),
% 1.67/0.58    inference(cnf_transformation,[],[f40])).
% 1.67/0.58  fof(f121,plain,(
% 1.67/0.58    spl5_10),
% 1.67/0.58    inference(avatar_split_clause,[],[f54,f118])).
% 1.67/0.58  fof(f54,plain,(
% 1.67/0.58    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))),
% 1.67/0.58    inference(cnf_transformation,[],[f40])).
% 1.67/0.58  fof(f116,plain,(
% 1.67/0.58    spl5_9),
% 1.67/0.58    inference(avatar_split_clause,[],[f50,f113])).
% 1.67/0.58  fof(f50,plain,(
% 1.67/0.58    m1_pre_topc(sK2,sK0)),
% 1.67/0.58    inference(cnf_transformation,[],[f40])).
% 1.67/0.58  fof(f111,plain,(
% 1.67/0.58    spl5_8),
% 1.67/0.58    inference(avatar_split_clause,[],[f51,f108])).
% 1.67/0.58  fof(f51,plain,(
% 1.67/0.58    v1_funct_1(sK3)),
% 1.67/0.58    inference(cnf_transformation,[],[f40])).
% 1.67/0.58  fof(f106,plain,(
% 1.67/0.58    ~spl5_7),
% 1.67/0.58    inference(avatar_split_clause,[],[f49,f103])).
% 1.67/0.58  fof(f103,plain,(
% 1.67/0.58    spl5_7 <=> v2_struct_0(sK2)),
% 1.67/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 1.67/0.58  fof(f49,plain,(
% 1.67/0.58    ~v2_struct_0(sK2)),
% 1.67/0.58    inference(cnf_transformation,[],[f40])).
% 1.67/0.58  fof(f101,plain,(
% 1.67/0.58    spl5_6),
% 1.67/0.58    inference(avatar_split_clause,[],[f48,f98])).
% 1.67/0.58  fof(f48,plain,(
% 1.67/0.58    l1_pre_topc(sK1)),
% 1.67/0.58    inference(cnf_transformation,[],[f40])).
% 1.67/0.58  fof(f96,plain,(
% 1.67/0.58    spl5_5),
% 1.67/0.58    inference(avatar_split_clause,[],[f47,f93])).
% 1.67/0.58  fof(f47,plain,(
% 1.67/0.58    v2_pre_topc(sK1)),
% 1.67/0.58    inference(cnf_transformation,[],[f40])).
% 1.67/0.58  fof(f91,plain,(
% 1.67/0.58    ~spl5_4),
% 1.67/0.58    inference(avatar_split_clause,[],[f46,f88])).
% 1.67/0.58  fof(f46,plain,(
% 1.67/0.58    ~v2_struct_0(sK1)),
% 1.67/0.58    inference(cnf_transformation,[],[f40])).
% 1.67/0.58  fof(f86,plain,(
% 1.67/0.58    spl5_3),
% 1.67/0.58    inference(avatar_split_clause,[],[f45,f83])).
% 1.67/0.58  fof(f45,plain,(
% 1.67/0.58    l1_pre_topc(sK0)),
% 1.67/0.58    inference(cnf_transformation,[],[f40])).
% 1.67/0.58  fof(f81,plain,(
% 1.67/0.58    spl5_2),
% 1.67/0.58    inference(avatar_split_clause,[],[f44,f78])).
% 1.67/0.58  fof(f44,plain,(
% 1.67/0.58    v2_pre_topc(sK0)),
% 1.67/0.58    inference(cnf_transformation,[],[f40])).
% 1.67/0.58  fof(f76,plain,(
% 1.67/0.58    ~spl5_1),
% 1.67/0.58    inference(avatar_split_clause,[],[f43,f73])).
% 1.67/0.58  fof(f43,plain,(
% 1.67/0.58    ~v2_struct_0(sK0)),
% 1.67/0.58    inference(cnf_transformation,[],[f40])).
% 1.67/0.58  % SZS output end Proof for theBenchmark
% 1.67/0.58  % (31483)------------------------------
% 1.67/0.58  % (31483)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.67/0.58  % (31483)Termination reason: Refutation
% 1.67/0.58  
% 1.67/0.58  % (31483)Memory used [KB]: 2558
% 1.67/0.58  % (31483)Time elapsed: 0.145 s
% 1.67/0.58  % (31483)------------------------------
% 1.67/0.58  % (31483)------------------------------
% 1.67/0.58  % (31482)Success in time 0.223 s
%------------------------------------------------------------------------------
