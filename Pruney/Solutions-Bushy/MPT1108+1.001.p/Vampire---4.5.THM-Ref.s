%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1108+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:16 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 272 expanded)
%              Number of leaves         :   35 ( 132 expanded)
%              Depth                    :    8
%              Number of atoms          :  444 (1403 expanded)
%              Number of equality atoms :   33 (  63 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f381,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f67,f71,f75,f79,f83,f87,f91,f95,f99,f105,f130,f136,f142,f144,f150,f257,f329,f332,f338,f362,f364,f380])).

fof(f380,plain,
    ( spl4_30
    | ~ spl4_4
    | ~ spl4_31 ),
    inference(avatar_split_clause,[],[f378,f360,f69,f336])).

fof(f336,plain,
    ( spl4_30
  <=> m1_subset_1(k7_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f69,plain,
    ( spl4_4
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f360,plain,
    ( spl4_31
  <=> ! [X0] :
        ( m1_subset_1(k7_relat_1(sK2,X0),k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK1))))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f378,plain,
    ( m1_subset_1(k7_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,u1_struct_0(sK1))))
    | ~ spl4_4
    | ~ spl4_31 ),
    inference(resolution,[],[f361,f70])).

fof(f70,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f69])).

fof(f361,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_subset_1(k7_relat_1(sK2,X0),k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK1)))) )
    | ~ spl4_31 ),
    inference(avatar_component_clause,[],[f360])).

fof(f364,plain,
    ( ~ spl4_8
    | spl4_29 ),
    inference(avatar_split_clause,[],[f363,f326,f85])).

fof(f85,plain,
    ( spl4_8
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f326,plain,
    ( spl4_29
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f363,plain,
    ( ~ l1_pre_topc(sK1)
    | spl4_29 ),
    inference(resolution,[],[f327,f41])).

fof(f41,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f327,plain,
    ( ~ l1_struct_0(sK1)
    | spl4_29 ),
    inference(avatar_component_clause,[],[f326])).

fof(f362,plain,
    ( ~ spl4_7
    | spl4_23
    | ~ spl4_5
    | spl4_31
    | ~ spl4_6
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f358,f134,f77,f360,f73,f252,f81])).

fof(f81,plain,
    ( spl4_7
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f252,plain,
    ( spl4_23
  <=> k1_xboole_0 = u1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f73,plain,
    ( spl4_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f77,plain,
    ( spl4_6
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f134,plain,
    ( spl4_19
  <=> ! [X0] : k7_relat_1(sK2,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f358,plain,
    ( ! [X0] :
        ( m1_subset_1(k7_relat_1(sK2,X0),k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK1))))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | k1_xboole_0 = u1_struct_0(sK1)
        | ~ v1_funct_1(sK2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_6
    | ~ spl4_19 ),
    inference(forward_demodulation,[],[f356,f135])).

fof(f135,plain,
    ( ! [X0] : k7_relat_1(sK2,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f134])).

fof(f356,plain,
    ( ! [X0] :
        ( m1_subset_1(k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK1))))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | k1_xboole_0 = u1_struct_0(sK1)
        | ~ v1_funct_1(sK2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_6 ),
    inference(resolution,[],[f238,f78])).

fof(f78,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f77])).

fof(f238,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(X2,X1,X0)
      | m1_subset_1(k2_partfun1(X1,X0,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X3,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k1_xboole_0 = X0
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X1)) ) ),
    inference(resolution,[],[f50,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X2,X0)
      | k1_xboole_0 = X1
      | m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X2,X0)
       => ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
            & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
            & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_funct_2)).

fof(f338,plain,
    ( ~ spl4_30
    | spl4_3
    | ~ spl4_5
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f334,f103,f73,f65,f336])).

fof(f65,plain,
    ( spl4_3
  <=> m1_subset_1(k5_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK3)),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f103,plain,
    ( spl4_12
  <=> sK3 = u1_struct_0(k1_pre_topc(sK0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f334,plain,
    ( ~ m1_subset_1(k7_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,u1_struct_0(sK1))))
    | spl4_3
    | ~ spl4_5
    | ~ spl4_12 ),
    inference(forward_demodulation,[],[f333,f125])).

fof(f125,plain,
    ( ! [X0] : k7_relat_1(sK2,X0) = k5_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)
    | ~ spl4_5 ),
    inference(resolution,[],[f45,f74])).

fof(f74,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f73])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

fof(f333,plain,
    ( ~ m1_subset_1(k5_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,u1_struct_0(sK1))))
    | spl4_3
    | ~ spl4_12 ),
    inference(forward_demodulation,[],[f66,f104])).

fof(f104,plain,
    ( sK3 = u1_struct_0(k1_pre_topc(sK0,sK3))
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f103])).

fof(f66,plain,
    ( ~ m1_subset_1(k5_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK3)),u1_struct_0(sK1))))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f65])).

fof(f332,plain,
    ( spl4_21
    | ~ spl4_4
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f330,f255,f69,f148])).

fof(f148,plain,
    ( spl4_21
  <=> v1_funct_2(k7_relat_1(sK2,sK3),sK3,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f255,plain,
    ( spl4_24
  <=> ! [X0] :
        ( v1_funct_2(k7_relat_1(sK2,X0),X0,u1_struct_0(sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f330,plain,
    ( v1_funct_2(k7_relat_1(sK2,sK3),sK3,u1_struct_0(sK1))
    | ~ spl4_4
    | ~ spl4_24 ),
    inference(resolution,[],[f256,f70])).

fof(f256,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_funct_2(k7_relat_1(sK2,X0),X0,u1_struct_0(sK1)) )
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f255])).

fof(f329,plain,
    ( spl4_9
    | ~ spl4_29
    | ~ spl4_11
    | ~ spl4_23 ),
    inference(avatar_split_clause,[],[f306,f252,f97,f326,f89])).

fof(f89,plain,
    ( spl4_9
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f97,plain,
    ( spl4_11
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f306,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl4_23 ),
    inference(superposition,[],[f43,f253])).

fof(f253,plain,
    ( k1_xboole_0 = u1_struct_0(sK1)
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f252])).

fof(f43,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f257,plain,
    ( ~ spl4_7
    | spl4_23
    | ~ spl4_5
    | spl4_24
    | ~ spl4_6
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f250,f134,f77,f255,f73,f252,f81])).

fof(f250,plain,
    ( ! [X0] :
        ( v1_funct_2(k7_relat_1(sK2,X0),X0,u1_struct_0(sK1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | k1_xboole_0 = u1_struct_0(sK1)
        | ~ v1_funct_1(sK2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_6
    | ~ spl4_19 ),
    inference(forward_demodulation,[],[f249,f135])).

fof(f249,plain,
    ( ! [X0] :
        ( v1_funct_2(k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),X0,u1_struct_0(sK1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | k1_xboole_0 = u1_struct_0(sK1)
        | ~ v1_funct_1(sK2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_6 ),
    inference(resolution,[],[f221,f78])).

fof(f221,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(X2,X1,X0)
      | v1_funct_2(k2_partfun1(X1,X0,X2,X3),X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k1_xboole_0 = X0
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X1)) ) ),
    inference(resolution,[],[f48,f44])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X2,X0)
      | k1_xboole_0 = X1
      | v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f150,plain,
    ( ~ spl4_21
    | spl4_2
    | ~ spl4_5
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f146,f103,f73,f62,f148])).

fof(f62,plain,
    ( spl4_2
  <=> v1_funct_2(k5_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),u1_struct_0(k1_pre_topc(sK0,sK3)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f146,plain,
    ( ~ v1_funct_2(k7_relat_1(sK2,sK3),sK3,u1_struct_0(sK1))
    | spl4_2
    | ~ spl4_5
    | ~ spl4_12 ),
    inference(forward_demodulation,[],[f145,f125])).

fof(f145,plain,
    ( ~ v1_funct_2(k5_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),sK3,u1_struct_0(sK1))
    | spl4_2
    | ~ spl4_12 ),
    inference(forward_demodulation,[],[f63,f104])).

fof(f63,plain,
    ( ~ v1_funct_2(k5_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),u1_struct_0(k1_pre_topc(sK0,sK3)),u1_struct_0(sK1))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f144,plain,
    ( spl4_18
    | ~ spl4_20 ),
    inference(avatar_contradiction_clause,[],[f143])).

fof(f143,plain,
    ( $false
    | spl4_18
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f129,f141])).

fof(f141,plain,
    ( ! [X0] : v1_funct_1(k7_relat_1(sK2,X0))
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl4_20
  <=> ! [X0] : v1_funct_1(k7_relat_1(sK2,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f129,plain,
    ( ~ v1_funct_1(k7_relat_1(sK2,sK3))
    | spl4_18 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl4_18
  <=> v1_funct_1(k7_relat_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f142,plain,
    ( ~ spl4_7
    | ~ spl4_5
    | spl4_20
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f137,f134,f140,f73,f81])).

fof(f137,plain,
    ( ! [X0] :
        ( v1_funct_1(k7_relat_1(sK2,X0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ v1_funct_1(sK2) )
    | ~ spl4_19 ),
    inference(superposition,[],[f53,f135])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).

fof(f136,plain,
    ( ~ spl4_7
    | spl4_19
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f131,f73,f134,f81])).

fof(f131,plain,
    ( ! [X0] :
        ( k7_relat_1(sK2,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0)
        | ~ v1_funct_1(sK2) )
    | ~ spl4_5 ),
    inference(resolution,[],[f52,f74])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f130,plain,
    ( ~ spl4_18
    | spl4_1
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f126,f73,f59,f128])).

fof(f59,plain,
    ( spl4_1
  <=> v1_funct_1(k5_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f126,plain,
    ( ~ v1_funct_1(k7_relat_1(sK2,sK3))
    | spl4_1
    | ~ spl4_5 ),
    inference(superposition,[],[f60,f125])).

fof(f60,plain,
    ( ~ v1_funct_1(k5_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f59])).

fof(f105,plain,
    ( ~ spl4_10
    | spl4_12
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f100,f69,f103,f93])).

fof(f93,plain,
    ( spl4_10
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f100,plain,
    ( sK3 = u1_struct_0(k1_pre_topc(sK0,sK3))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_4 ),
    inference(resolution,[],[f42,f70])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => u1_struct_0(k1_pre_topc(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_pre_topc)).

fof(f99,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f40,f97])).

fof(f40,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f95,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f32,f93])).

fof(f32,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ( ~ m1_subset_1(k5_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK3)),u1_struct_0(sK1))))
      | ~ v1_funct_2(k5_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),u1_struct_0(k1_pre_topc(sK0,sK3)),u1_struct_0(sK1))
      | ~ v1_funct_1(k5_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3)) )
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f30,f29,f28,f27])).

fof(f27,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ~ m1_subset_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X3)),u1_struct_0(X1))))
                      | ~ v1_funct_2(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),u1_struct_0(k1_pre_topc(X0,X3)),u1_struct_0(X1))
                      | ~ v1_funct_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) )
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_pre_topc(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_subset_1(k5_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,X3)),u1_struct_0(X1))))
                    | ~ v1_funct_2(k5_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,X3),u1_struct_0(k1_pre_topc(sK0,X3)),u1_struct_0(X1))
                    | ~ v1_funct_1(k5_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,X3)) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ~ m1_subset_1(k5_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,X3)),u1_struct_0(X1))))
                  | ~ v1_funct_2(k5_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,X3),u1_struct_0(k1_pre_topc(sK0,X3)),u1_struct_0(X1))
                  | ~ v1_funct_1(k5_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,X3)) )
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ~ m1_subset_1(k5_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,X3)),u1_struct_0(sK1))))
                | ~ v1_funct_2(k5_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,X3),u1_struct_0(k1_pre_topc(sK0,X3)),u1_struct_0(sK1))
                | ~ v1_funct_1(k5_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,X3)) )
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(X2) )
      & l1_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ~ m1_subset_1(k5_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,X3)),u1_struct_0(sK1))))
              | ~ v1_funct_2(k5_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,X3),u1_struct_0(k1_pre_topc(sK0,X3)),u1_struct_0(sK1))
              | ~ v1_funct_1(k5_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,X3)) )
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ( ~ m1_subset_1(k5_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,X3)),u1_struct_0(sK1))))
            | ~ v1_funct_2(k5_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X3),u1_struct_0(k1_pre_topc(sK0,X3)),u1_struct_0(sK1))
            | ~ v1_funct_1(k5_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X3)) )
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X3] :
        ( ( ~ m1_subset_1(k5_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,X3)),u1_struct_0(sK1))))
          | ~ v1_funct_2(k5_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X3),u1_struct_0(k1_pre_topc(sK0,X3)),u1_struct_0(sK1))
          | ~ v1_funct_1(k5_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X3)) )
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( ~ m1_subset_1(k5_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK3)),u1_struct_0(sK1))))
        | ~ v1_funct_2(k5_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),u1_struct_0(k1_pre_topc(sK0,sK3)),u1_struct_0(sK1))
        | ~ v1_funct_1(k5_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3)) )
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_subset_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X3)),u1_struct_0(X1))))
                    | ~ v1_funct_2(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),u1_struct_0(k1_pre_topc(X0,X3)),u1_struct_0(X1))
                    | ~ v1_funct_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_subset_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X3)),u1_struct_0(X1))))
                    | ~ v1_funct_2(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),u1_struct_0(k1_pre_topc(X0,X3)),u1_struct_0(X1))
                    | ~ v1_funct_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( m1_subset_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X3)),u1_struct_0(X1))))
                      & v1_funct_2(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),u1_struct_0(k1_pre_topc(X0,X3)),u1_struct_0(X1))
                      & v1_funct_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( m1_subset_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X3)),u1_struct_0(X1))))
                    & v1_funct_2(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),u1_struct_0(k1_pre_topc(X0,X3)),u1_struct_0(X1))
                    & v1_funct_1(k5_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_pre_topc)).

fof(f91,plain,(
    ~ spl4_9 ),
    inference(avatar_split_clause,[],[f33,f89])).

fof(f33,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f87,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f34,f85])).

fof(f34,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f83,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f35,f81])).

fof(f35,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f79,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f36,f77])).

fof(f36,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f31])).

fof(f75,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f37,f73])).

fof(f37,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f31])).

fof(f71,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f38,f69])).

fof(f38,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f31])).

fof(f67,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f39,f65,f62,f59])).

fof(f39,plain,
    ( ~ m1_subset_1(k5_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK3)),u1_struct_0(sK1))))
    | ~ v1_funct_2(k5_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),u1_struct_0(k1_pre_topc(sK0,sK3)),u1_struct_0(sK1))
    | ~ v1_funct_1(k5_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3)) ),
    inference(cnf_transformation,[],[f31])).

%------------------------------------------------------------------------------
