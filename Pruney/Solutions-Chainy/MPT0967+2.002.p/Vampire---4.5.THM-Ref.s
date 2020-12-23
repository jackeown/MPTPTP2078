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
% DateTime   : Thu Dec  3 13:00:42 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  154 ( 269 expanded)
%              Number of leaves         :   34 (  91 expanded)
%              Depth                    :    9
%              Number of atoms          :  437 ( 990 expanded)
%              Number of equality atoms :   79 ( 221 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1500,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f119,f142,f151,f161,f169,f188,f234,f248,f291,f620,f627,f846,f850,f983,f1053,f1081,f1219,f1290,f1499])).

fof(f1499,plain,
    ( ~ spl8_1
    | spl8_6
    | ~ spl8_9
    | ~ spl8_18
    | ~ spl8_30 ),
    inference(avatar_contradiction_clause,[],[f1497])).

fof(f1497,plain,
    ( $false
    | ~ spl8_1
    | spl8_6
    | ~ spl8_9
    | ~ spl8_18
    | ~ spl8_30 ),
    inference(subsumption_resolution,[],[f646,f1281])).

fof(f1281,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl8_1
    | spl8_6
    | ~ spl8_9
    | ~ spl8_30 ),
    inference(forward_demodulation,[],[f436,f982])).

fof(f982,plain,
    ( k1_xboole_0 = sK2
    | ~ spl8_30 ),
    inference(avatar_component_clause,[],[f980])).

fof(f980,plain,
    ( spl8_30
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).

fof(f436,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK2)
    | ~ spl8_1
    | spl8_6
    | ~ spl8_9 ),
    inference(forward_demodulation,[],[f254,f345])).

fof(f345,plain,
    ( k1_xboole_0 = sK3
    | ~ spl8_9 ),
    inference(resolution,[],[f183,f56])).

fof(f56,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

fof(f183,plain,
    ( v1_xboole_0(sK3)
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f181])).

fof(f181,plain,
    ( spl8_9
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f254,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,sK2)
    | ~ spl8_1
    | spl8_6 ),
    inference(backward_demodulation,[],[f150,f114])).

fof(f114,plain,
    ( k1_xboole_0 = sK0
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl8_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f150,plain,
    ( ~ v1_funct_2(sK3,sK0,sK2)
    | spl8_6 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl8_6
  <=> v1_funct_2(sK3,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f646,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f644])).

fof(f644,plain,
    ( spl8_18
  <=> v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f1290,plain,
    ( spl8_18
    | ~ spl8_9
    | ~ spl8_13 ),
    inference(avatar_split_clause,[],[f379,f231,f181,f644])).

fof(f231,plain,
    ( spl8_13
  <=> v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f379,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl8_9
    | ~ spl8_13 ),
    inference(forward_demodulation,[],[f378,f52])).

fof(f52,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f378,plain,
    ( v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ spl8_9
    | ~ spl8_13 ),
    inference(forward_demodulation,[],[f375,f53])).

fof(f53,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f13])).

fof(f375,plain,
    ( v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0))
    | ~ spl8_9
    | ~ spl8_13 ),
    inference(backward_demodulation,[],[f233,f345])).

fof(f233,plain,
    ( v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3))
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f231])).

fof(f1219,plain,
    ( ~ spl8_1
    | ~ spl8_9
    | spl8_14 ),
    inference(avatar_contradiction_clause,[],[f1217])).

fof(f1217,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_9
    | spl8_14 ),
    inference(subsumption_resolution,[],[f114,f1085])).

fof(f1085,plain,
    ( k1_xboole_0 != sK0
    | ~ spl8_9
    | spl8_14 ),
    inference(forward_demodulation,[],[f439,f52])).

fof(f439,plain,
    ( k1_relat_1(k1_xboole_0) != sK0
    | ~ spl8_9
    | spl8_14 ),
    inference(forward_demodulation,[],[f246,f345])).

fof(f246,plain,
    ( sK0 != k1_relat_1(sK3)
    | spl8_14 ),
    inference(avatar_component_clause,[],[f245])).

fof(f245,plain,
    ( spl8_14
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f1081,plain,
    ( spl8_2
    | ~ spl8_3
    | ~ spl8_30 ),
    inference(avatar_contradiction_clause,[],[f1065])).

fof(f1065,plain,
    ( $false
    | spl8_2
    | ~ spl8_3
    | ~ spl8_30 ),
    inference(subsumption_resolution,[],[f118,f1064])).

fof(f1064,plain,
    ( k1_xboole_0 = sK1
    | ~ spl8_3
    | ~ spl8_30 ),
    inference(forward_demodulation,[],[f137,f982])).

fof(f137,plain,
    ( sK1 = sK2
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl8_3
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f118,plain,
    ( k1_xboole_0 != sK1
    | spl8_2 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl8_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f1053,plain,
    ( spl8_4
    | ~ spl8_30 ),
    inference(avatar_contradiction_clause,[],[f1044])).

fof(f1044,plain,
    ( $false
    | spl8_4
    | ~ spl8_30 ),
    inference(resolution,[],[f988,f54])).

fof(f54,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f988,plain,
    ( ~ r1_tarski(k1_xboole_0,sK1)
    | spl8_4
    | ~ spl8_30 ),
    inference(backward_demodulation,[],[f141,f982])).

fof(f141,plain,
    ( ~ r1_tarski(sK2,sK1)
    | spl8_4 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl8_4
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f983,plain,
    ( spl8_6
    | spl8_30
    | ~ spl8_5
    | ~ spl8_14 ),
    inference(avatar_split_clause,[],[f978,f245,f144,f980,f148])).

fof(f144,plain,
    ( spl8_5
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f978,plain,
    ( k1_xboole_0 = sK2
    | v1_funct_2(sK3,sK0,sK2)
    | ~ spl8_5
    | ~ spl8_14 ),
    inference(trivial_inequality_removal,[],[f977])).

fof(f977,plain,
    ( sK0 != sK0
    | k1_xboole_0 = sK2
    | v1_funct_2(sK3,sK0,sK2)
    | ~ spl8_5
    | ~ spl8_14 ),
    inference(forward_demodulation,[],[f855,f862])).

fof(f862,plain,
    ( sK0 = k1_relset_1(sK0,sK2,sK3)
    | ~ spl8_5
    | ~ spl8_14 ),
    inference(forward_demodulation,[],[f852,f247])).

fof(f247,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f245])).

fof(f852,plain,
    ( k1_relat_1(sK3) = k1_relset_1(sK0,sK2,sK3)
    | ~ spl8_5 ),
    inference(resolution,[],[f145,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f145,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f144])).

fof(f855,plain,
    ( k1_xboole_0 = sK2
    | sK0 != k1_relset_1(sK0,sK2,sK3)
    | v1_funct_2(sK3,sK0,sK2)
    | ~ spl8_5 ),
    inference(resolution,[],[f145,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

fof(f42,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
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

fof(f850,plain,(
    spl8_27 ),
    inference(avatar_contradiction_clause,[],[f847])).

fof(f847,plain,
    ( $false
    | spl8_27 ),
    inference(resolution,[],[f845,f90])).

fof(f90,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f845,plain,
    ( ~ r1_tarski(sK0,sK0)
    | spl8_27 ),
    inference(avatar_component_clause,[],[f843])).

fof(f843,plain,
    ( spl8_27
  <=> r1_tarski(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).

fof(f846,plain,
    ( ~ spl8_16
    | ~ spl8_7
    | ~ spl8_27
    | spl8_5
    | ~ spl8_14 ),
    inference(avatar_split_clause,[],[f566,f245,f144,f843,f154,f624])).

fof(f624,plain,
    ( spl8_16
  <=> r1_tarski(k2_relat_1(sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f154,plain,
    ( spl8_7
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f566,plain,
    ( ~ r1_tarski(sK0,sK0)
    | ~ v1_relat_1(sK3)
    | ~ r1_tarski(k2_relat_1(sK3),sK2)
    | spl8_5
    | ~ spl8_14 ),
    inference(forward_demodulation,[],[f565,f247])).

fof(f565,plain,
    ( ~ v1_relat_1(sK3)
    | ~ r1_tarski(k1_relat_1(sK3),sK0)
    | ~ r1_tarski(k2_relat_1(sK3),sK2)
    | spl8_5 ),
    inference(resolution,[],[f146,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(f146,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | spl8_5 ),
    inference(avatar_component_clause,[],[f144])).

fof(f627,plain,
    ( spl8_16
    | ~ spl8_7
    | ~ spl8_15 ),
    inference(avatar_split_clause,[],[f622,f617,f154,f624])).

fof(f617,plain,
    ( spl8_15
  <=> v5_relat_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f622,plain,
    ( ~ v1_relat_1(sK3)
    | r1_tarski(k2_relat_1(sK3),sK2)
    | ~ spl8_15 ),
    inference(resolution,[],[f619,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f619,plain,
    ( v5_relat_1(sK3,sK2)
    | ~ spl8_15 ),
    inference(avatar_component_clause,[],[f617])).

fof(f620,plain,
    ( spl8_15
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f613,f154,f617])).

fof(f613,plain,
    ( ~ v1_relat_1(sK3)
    | v5_relat_1(sK3,sK2) ),
    inference(resolution,[],[f108,f122])).

fof(f122,plain,(
    v5_relat_1(sK3,sK1) ),
    inference(resolution,[],[f49,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f49,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(X1,X2)
         => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
              & v1_funct_2(X3,X0,X2)
              & v1_funct_1(X3) )
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X1,X2)
       => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
            & v1_funct_2(X3,X0,X2)
            & v1_funct_1(X3) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_2)).

fof(f108,plain,(
    ! [X0] :
      ( ~ v5_relat_1(X0,sK1)
      | ~ v1_relat_1(X0)
      | v5_relat_1(X0,sK2) ) ),
    inference(resolution,[],[f50,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2)
      | ~ v5_relat_1(X2,X0)
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v5_relat_1(X2,X1)
          | ~ v5_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v5_relat_1(X2,X1)
          | ~ v5_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( ( v5_relat_1(X2,X0)
            & v1_relat_1(X2) )
         => v5_relat_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t218_relat_1)).

fof(f50,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f291,plain,
    ( ~ spl8_1
    | spl8_10 ),
    inference(avatar_contradiction_clause,[],[f280])).

fof(f280,plain,
    ( $false
    | ~ spl8_1
    | spl8_10 ),
    inference(subsumption_resolution,[],[f51,f260])).

fof(f260,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl8_1
    | spl8_10 ),
    inference(forward_demodulation,[],[f255,f92])).

fof(f92,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f255,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(k1_xboole_0,sK1))
    | ~ spl8_1
    | spl8_10 ),
    inference(backward_demodulation,[],[f187,f114])).

fof(f187,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | spl8_10 ),
    inference(avatar_component_clause,[],[f185])).

fof(f185,plain,
    ( spl8_10
  <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f51,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f248,plain,
    ( spl8_14
    | spl8_2 ),
    inference(avatar_split_clause,[],[f200,f116,f245])).

fof(f200,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relat_1(sK3) ),
    inference(global_subsumption,[],[f48,f49,f192])).

fof(f192,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_xboole_0 = sK1
    | ~ v1_funct_2(sK3,sK0,sK1) ),
    inference(superposition,[],[f120,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f120,plain,(
    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) ),
    inference(resolution,[],[f49,f77])).

fof(f48,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f234,plain,
    ( spl8_13
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f103,f154,f231])).

fof(f103,plain,
    ( ~ v1_relat_1(sK3)
    | v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3)) ),
    inference(resolution,[],[f47,f61])).

fof(f61,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(f47,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f188,plain,
    ( spl8_9
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f129,f185,f181])).

fof(f129,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | v1_xboole_0(sK3) ),
    inference(resolution,[],[f49,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f169,plain,(
    spl8_8 ),
    inference(avatar_contradiction_clause,[],[f166])).

fof(f166,plain,
    ( $false
    | spl8_8 ),
    inference(resolution,[],[f160,f63])).

fof(f63,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f160,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl8_8 ),
    inference(avatar_component_clause,[],[f158])).

fof(f158,plain,
    ( spl8_8
  <=> v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f161,plain,
    ( spl8_7
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f128,f158,f154])).

fof(f128,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK3) ),
    inference(resolution,[],[f49,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f151,plain,
    ( ~ spl8_5
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f102,f148,f144])).

fof(f102,plain,
    ( ~ v1_funct_2(sK3,sK0,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(global_subsumption,[],[f47,f45])).

fof(f45,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK0,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f25])).

fof(f142,plain,
    ( spl8_3
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f106,f139,f135])).

fof(f106,plain,
    ( ~ r1_tarski(sK2,sK1)
    | sK1 = sK2 ),
    inference(resolution,[],[f50,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f119,plain,
    ( spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f46,f116,f112])).

fof(f46,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:27:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.22/0.43  % (21267)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.46  % (21267)Refutation found. Thanks to Tanya!
% 0.22/0.46  % SZS status Theorem for theBenchmark
% 0.22/0.46  % SZS output start Proof for theBenchmark
% 0.22/0.46  fof(f1500,plain,(
% 0.22/0.46    $false),
% 0.22/0.46    inference(avatar_sat_refutation,[],[f119,f142,f151,f161,f169,f188,f234,f248,f291,f620,f627,f846,f850,f983,f1053,f1081,f1219,f1290,f1499])).
% 0.22/0.46  fof(f1499,plain,(
% 0.22/0.46    ~spl8_1 | spl8_6 | ~spl8_9 | ~spl8_18 | ~spl8_30),
% 0.22/0.46    inference(avatar_contradiction_clause,[],[f1497])).
% 0.22/0.46  fof(f1497,plain,(
% 0.22/0.46    $false | (~spl8_1 | spl8_6 | ~spl8_9 | ~spl8_18 | ~spl8_30)),
% 0.22/0.46    inference(subsumption_resolution,[],[f646,f1281])).
% 0.22/0.46  fof(f1281,plain,(
% 0.22/0.46    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl8_1 | spl8_6 | ~spl8_9 | ~spl8_30)),
% 0.22/0.46    inference(forward_demodulation,[],[f436,f982])).
% 0.22/0.46  fof(f982,plain,(
% 0.22/0.46    k1_xboole_0 = sK2 | ~spl8_30),
% 0.22/0.46    inference(avatar_component_clause,[],[f980])).
% 0.22/0.46  fof(f980,plain,(
% 0.22/0.46    spl8_30 <=> k1_xboole_0 = sK2),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).
% 0.22/0.46  fof(f436,plain,(
% 0.22/0.46    ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK2) | (~spl8_1 | spl8_6 | ~spl8_9)),
% 0.22/0.46    inference(forward_demodulation,[],[f254,f345])).
% 0.22/0.46  fof(f345,plain,(
% 0.22/0.46    k1_xboole_0 = sK3 | ~spl8_9),
% 0.22/0.46    inference(resolution,[],[f183,f56])).
% 0.22/0.46  fof(f56,plain,(
% 0.22/0.46    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.22/0.46    inference(cnf_transformation,[],[f27])).
% 0.22/0.46  fof(f27,plain,(
% 0.22/0.46    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.46    inference(ennf_transformation,[],[f4])).
% 0.22/0.46  fof(f4,axiom,(
% 0.22/0.46    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).
% 0.22/0.46  fof(f183,plain,(
% 0.22/0.46    v1_xboole_0(sK3) | ~spl8_9),
% 0.22/0.46    inference(avatar_component_clause,[],[f181])).
% 0.22/0.46  fof(f181,plain,(
% 0.22/0.46    spl8_9 <=> v1_xboole_0(sK3)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.22/0.46  fof(f254,plain,(
% 0.22/0.46    ~v1_funct_2(sK3,k1_xboole_0,sK2) | (~spl8_1 | spl8_6)),
% 0.22/0.46    inference(backward_demodulation,[],[f150,f114])).
% 0.22/0.46  fof(f114,plain,(
% 0.22/0.46    k1_xboole_0 = sK0 | ~spl8_1),
% 0.22/0.46    inference(avatar_component_clause,[],[f112])).
% 0.22/0.46  fof(f112,plain,(
% 0.22/0.46    spl8_1 <=> k1_xboole_0 = sK0),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.22/0.46  fof(f150,plain,(
% 0.22/0.46    ~v1_funct_2(sK3,sK0,sK2) | spl8_6),
% 0.22/0.46    inference(avatar_component_clause,[],[f148])).
% 0.22/0.46  fof(f148,plain,(
% 0.22/0.46    spl8_6 <=> v1_funct_2(sK3,sK0,sK2)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.22/0.46  fof(f646,plain,(
% 0.22/0.46    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~spl8_18),
% 0.22/0.46    inference(avatar_component_clause,[],[f644])).
% 0.22/0.46  fof(f644,plain,(
% 0.22/0.46    spl8_18 <=> v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).
% 0.22/0.46  fof(f1290,plain,(
% 0.22/0.46    spl8_18 | ~spl8_9 | ~spl8_13),
% 0.22/0.46    inference(avatar_split_clause,[],[f379,f231,f181,f644])).
% 0.22/0.46  fof(f231,plain,(
% 0.22/0.46    spl8_13 <=> v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 0.22/0.46  fof(f379,plain,(
% 0.22/0.46    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl8_9 | ~spl8_13)),
% 0.22/0.46    inference(forward_demodulation,[],[f378,f52])).
% 0.22/0.46  fof(f52,plain,(
% 0.22/0.46    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.46    inference(cnf_transformation,[],[f13])).
% 0.22/0.46  fof(f13,axiom,(
% 0.22/0.46    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.22/0.46  fof(f378,plain,(
% 0.22/0.46    v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) | (~spl8_9 | ~spl8_13)),
% 0.22/0.46    inference(forward_demodulation,[],[f375,f53])).
% 0.22/0.46  fof(f53,plain,(
% 0.22/0.46    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.22/0.46    inference(cnf_transformation,[],[f13])).
% 0.22/0.46  fof(f375,plain,(
% 0.22/0.46    v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0)) | (~spl8_9 | ~spl8_13)),
% 0.22/0.46    inference(backward_demodulation,[],[f233,f345])).
% 0.22/0.46  fof(f233,plain,(
% 0.22/0.46    v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3)) | ~spl8_13),
% 0.22/0.46    inference(avatar_component_clause,[],[f231])).
% 0.22/0.46  fof(f1219,plain,(
% 0.22/0.46    ~spl8_1 | ~spl8_9 | spl8_14),
% 0.22/0.46    inference(avatar_contradiction_clause,[],[f1217])).
% 0.22/0.46  fof(f1217,plain,(
% 0.22/0.46    $false | (~spl8_1 | ~spl8_9 | spl8_14)),
% 0.22/0.46    inference(subsumption_resolution,[],[f114,f1085])).
% 0.22/0.46  fof(f1085,plain,(
% 0.22/0.46    k1_xboole_0 != sK0 | (~spl8_9 | spl8_14)),
% 0.22/0.46    inference(forward_demodulation,[],[f439,f52])).
% 0.22/0.46  fof(f439,plain,(
% 0.22/0.46    k1_relat_1(k1_xboole_0) != sK0 | (~spl8_9 | spl8_14)),
% 0.22/0.46    inference(forward_demodulation,[],[f246,f345])).
% 0.22/0.46  fof(f246,plain,(
% 0.22/0.46    sK0 != k1_relat_1(sK3) | spl8_14),
% 0.22/0.46    inference(avatar_component_clause,[],[f245])).
% 0.22/0.46  fof(f245,plain,(
% 0.22/0.46    spl8_14 <=> sK0 = k1_relat_1(sK3)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 0.22/0.46  fof(f1081,plain,(
% 0.22/0.46    spl8_2 | ~spl8_3 | ~spl8_30),
% 0.22/0.46    inference(avatar_contradiction_clause,[],[f1065])).
% 0.22/0.46  fof(f1065,plain,(
% 0.22/0.46    $false | (spl8_2 | ~spl8_3 | ~spl8_30)),
% 0.22/0.46    inference(subsumption_resolution,[],[f118,f1064])).
% 0.22/0.46  fof(f1064,plain,(
% 0.22/0.46    k1_xboole_0 = sK1 | (~spl8_3 | ~spl8_30)),
% 0.22/0.46    inference(forward_demodulation,[],[f137,f982])).
% 0.22/0.46  fof(f137,plain,(
% 0.22/0.46    sK1 = sK2 | ~spl8_3),
% 0.22/0.46    inference(avatar_component_clause,[],[f135])).
% 0.22/0.46  fof(f135,plain,(
% 0.22/0.46    spl8_3 <=> sK1 = sK2),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.22/0.46  fof(f118,plain,(
% 0.22/0.46    k1_xboole_0 != sK1 | spl8_2),
% 0.22/0.46    inference(avatar_component_clause,[],[f116])).
% 0.22/0.46  fof(f116,plain,(
% 0.22/0.46    spl8_2 <=> k1_xboole_0 = sK1),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.22/0.46  fof(f1053,plain,(
% 0.22/0.46    spl8_4 | ~spl8_30),
% 0.22/0.46    inference(avatar_contradiction_clause,[],[f1044])).
% 0.22/0.46  fof(f1044,plain,(
% 0.22/0.46    $false | (spl8_4 | ~spl8_30)),
% 0.22/0.46    inference(resolution,[],[f988,f54])).
% 0.22/0.46  fof(f54,plain,(
% 0.22/0.46    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f3])).
% 0.22/0.46  fof(f3,axiom,(
% 0.22/0.46    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.46  fof(f988,plain,(
% 0.22/0.46    ~r1_tarski(k1_xboole_0,sK1) | (spl8_4 | ~spl8_30)),
% 0.22/0.46    inference(backward_demodulation,[],[f141,f982])).
% 0.22/0.46  fof(f141,plain,(
% 0.22/0.46    ~r1_tarski(sK2,sK1) | spl8_4),
% 0.22/0.46    inference(avatar_component_clause,[],[f139])).
% 0.22/0.46  fof(f139,plain,(
% 0.22/0.46    spl8_4 <=> r1_tarski(sK2,sK1)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.22/0.46  fof(f983,plain,(
% 0.22/0.46    spl8_6 | spl8_30 | ~spl8_5 | ~spl8_14),
% 0.22/0.46    inference(avatar_split_clause,[],[f978,f245,f144,f980,f148])).
% 0.22/0.46  fof(f144,plain,(
% 0.22/0.46    spl8_5 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.22/0.46  fof(f978,plain,(
% 0.22/0.46    k1_xboole_0 = sK2 | v1_funct_2(sK3,sK0,sK2) | (~spl8_5 | ~spl8_14)),
% 0.22/0.46    inference(trivial_inequality_removal,[],[f977])).
% 0.22/0.46  fof(f977,plain,(
% 0.22/0.46    sK0 != sK0 | k1_xboole_0 = sK2 | v1_funct_2(sK3,sK0,sK2) | (~spl8_5 | ~spl8_14)),
% 0.22/0.46    inference(forward_demodulation,[],[f855,f862])).
% 0.22/0.46  fof(f862,plain,(
% 0.22/0.46    sK0 = k1_relset_1(sK0,sK2,sK3) | (~spl8_5 | ~spl8_14)),
% 0.22/0.46    inference(forward_demodulation,[],[f852,f247])).
% 0.22/0.46  fof(f247,plain,(
% 0.22/0.46    sK0 = k1_relat_1(sK3) | ~spl8_14),
% 0.22/0.46    inference(avatar_component_clause,[],[f245])).
% 0.22/0.46  fof(f852,plain,(
% 0.22/0.46    k1_relat_1(sK3) = k1_relset_1(sK0,sK2,sK3) | ~spl8_5),
% 0.22/0.46    inference(resolution,[],[f145,f77])).
% 0.22/0.46  fof(f77,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f40])).
% 0.22/0.46  fof(f40,plain,(
% 0.22/0.46    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.46    inference(ennf_transformation,[],[f17])).
% 0.22/0.46  fof(f17,axiom,(
% 0.22/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.46  fof(f145,plain,(
% 0.22/0.46    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~spl8_5),
% 0.22/0.46    inference(avatar_component_clause,[],[f144])).
% 0.22/0.46  fof(f855,plain,(
% 0.22/0.46    k1_xboole_0 = sK2 | sK0 != k1_relset_1(sK0,sK2,sK3) | v1_funct_2(sK3,sK0,sK2) | ~spl8_5),
% 0.22/0.46    inference(resolution,[],[f145,f84])).
% 0.22/0.46  fof(f84,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f43])).
% 0.22/0.46  fof(f43,plain,(
% 0.22/0.46    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.46    inference(flattening,[],[f42])).
% 0.22/0.46  fof(f42,plain,(
% 0.22/0.46    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.46    inference(ennf_transformation,[],[f20])).
% 0.22/0.46  fof(f20,axiom,(
% 0.22/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.46  fof(f850,plain,(
% 0.22/0.46    spl8_27),
% 0.22/0.46    inference(avatar_contradiction_clause,[],[f847])).
% 0.22/0.46  fof(f847,plain,(
% 0.22/0.46    $false | spl8_27),
% 0.22/0.46    inference(resolution,[],[f845,f90])).
% 0.22/0.46  fof(f90,plain,(
% 0.22/0.46    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.46    inference(equality_resolution,[],[f69])).
% 0.22/0.46  fof(f69,plain,(
% 0.22/0.46    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.22/0.46    inference(cnf_transformation,[],[f2])).
% 0.22/0.46  fof(f2,axiom,(
% 0.22/0.46    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.46  fof(f845,plain,(
% 0.22/0.46    ~r1_tarski(sK0,sK0) | spl8_27),
% 0.22/0.46    inference(avatar_component_clause,[],[f843])).
% 0.22/0.46  fof(f843,plain,(
% 0.22/0.46    spl8_27 <=> r1_tarski(sK0,sK0)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).
% 0.22/0.46  fof(f846,plain,(
% 0.22/0.46    ~spl8_16 | ~spl8_7 | ~spl8_27 | spl8_5 | ~spl8_14),
% 0.22/0.46    inference(avatar_split_clause,[],[f566,f245,f144,f843,f154,f624])).
% 0.22/0.46  fof(f624,plain,(
% 0.22/0.46    spl8_16 <=> r1_tarski(k2_relat_1(sK3),sK2)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).
% 0.22/0.46  fof(f154,plain,(
% 0.22/0.46    spl8_7 <=> v1_relat_1(sK3)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.22/0.46  fof(f566,plain,(
% 0.22/0.46    ~r1_tarski(sK0,sK0) | ~v1_relat_1(sK3) | ~r1_tarski(k2_relat_1(sK3),sK2) | (spl8_5 | ~spl8_14)),
% 0.22/0.46    inference(forward_demodulation,[],[f565,f247])).
% 0.22/0.46  fof(f565,plain,(
% 0.22/0.46    ~v1_relat_1(sK3) | ~r1_tarski(k1_relat_1(sK3),sK0) | ~r1_tarski(k2_relat_1(sK3),sK2) | spl8_5),
% 0.22/0.46    inference(resolution,[],[f146,f76])).
% 0.22/0.46  fof(f76,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(k1_relat_1(X2),X0) | ~r1_tarski(k2_relat_1(X2),X1) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.46    inference(cnf_transformation,[],[f39])).
% 0.22/0.46  fof(f39,plain,(
% 0.22/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 0.22/0.46    inference(flattening,[],[f38])).
% 0.22/0.46  fof(f38,plain,(
% 0.22/0.46    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 0.22/0.46    inference(ennf_transformation,[],[f18])).
% 0.22/0.46  fof(f18,axiom,(
% 0.22/0.46    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).
% 0.22/0.46  fof(f146,plain,(
% 0.22/0.46    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | spl8_5),
% 0.22/0.46    inference(avatar_component_clause,[],[f144])).
% 0.22/0.46  fof(f627,plain,(
% 0.22/0.46    spl8_16 | ~spl8_7 | ~spl8_15),
% 0.22/0.46    inference(avatar_split_clause,[],[f622,f617,f154,f624])).
% 0.22/0.46  fof(f617,plain,(
% 0.22/0.46    spl8_15 <=> v5_relat_1(sK3,sK2)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).
% 0.22/0.46  fof(f622,plain,(
% 0.22/0.46    ~v1_relat_1(sK3) | r1_tarski(k2_relat_1(sK3),sK2) | ~spl8_15),
% 0.22/0.46    inference(resolution,[],[f619,f67])).
% 0.22/0.46  fof(f67,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f34])).
% 0.22/0.46  fof(f34,plain,(
% 0.22/0.46    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.46    inference(ennf_transformation,[],[f10])).
% 0.22/0.46  fof(f10,axiom,(
% 0.22/0.46    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.22/0.46  fof(f619,plain,(
% 0.22/0.46    v5_relat_1(sK3,sK2) | ~spl8_15),
% 0.22/0.46    inference(avatar_component_clause,[],[f617])).
% 0.22/0.46  fof(f620,plain,(
% 0.22/0.46    spl8_15 | ~spl8_7),
% 0.22/0.46    inference(avatar_split_clause,[],[f613,f154,f617])).
% 0.22/0.46  fof(f613,plain,(
% 0.22/0.46    ~v1_relat_1(sK3) | v5_relat_1(sK3,sK2)),
% 0.22/0.46    inference(resolution,[],[f108,f122])).
% 0.22/0.46  fof(f122,plain,(
% 0.22/0.46    v5_relat_1(sK3,sK1)),
% 0.22/0.46    inference(resolution,[],[f49,f79])).
% 0.22/0.46  fof(f79,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f41])).
% 0.22/0.46  fof(f41,plain,(
% 0.22/0.46    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.46    inference(ennf_transformation,[],[f16])).
% 0.22/0.46  fof(f16,axiom,(
% 0.22/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.46  fof(f49,plain,(
% 0.22/0.46    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.46    inference(cnf_transformation,[],[f25])).
% 0.22/0.46  fof(f25,plain,(
% 0.22/0.46    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.22/0.46    inference(flattening,[],[f24])).
% 0.22/0.46  fof(f24,plain,(
% 0.22/0.46    ? [X0,X1,X2,X3] : ((((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X1,X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.22/0.46    inference(ennf_transformation,[],[f23])).
% 0.22/0.46  fof(f23,negated_conjecture,(
% 0.22/0.46    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X1,X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.22/0.46    inference(negated_conjecture,[],[f22])).
% 0.22/0.46  fof(f22,conjecture,(
% 0.22/0.46    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X1,X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_2)).
% 0.22/0.46  fof(f108,plain,(
% 0.22/0.46    ( ! [X0] : (~v5_relat_1(X0,sK1) | ~v1_relat_1(X0) | v5_relat_1(X0,sK2)) )),
% 0.22/0.46    inference(resolution,[],[f50,f68])).
% 0.22/0.46  fof(f68,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~v1_relat_1(X2) | ~v5_relat_1(X2,X0) | v5_relat_1(X2,X1)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f36])).
% 0.22/0.46  fof(f36,plain,(
% 0.22/0.46    ! [X0,X1] : (! [X2] : (v5_relat_1(X2,X1) | ~v5_relat_1(X2,X0) | ~v1_relat_1(X2)) | ~r1_tarski(X0,X1))),
% 0.22/0.46    inference(flattening,[],[f35])).
% 0.22/0.46  fof(f35,plain,(
% 0.22/0.46    ! [X0,X1] : (! [X2] : (v5_relat_1(X2,X1) | (~v5_relat_1(X2,X0) | ~v1_relat_1(X2))) | ~r1_tarski(X0,X1))),
% 0.22/0.46    inference(ennf_transformation,[],[f12])).
% 0.22/0.46  fof(f12,axiom,(
% 0.22/0.46    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : ((v5_relat_1(X2,X0) & v1_relat_1(X2)) => v5_relat_1(X2,X1)))),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t218_relat_1)).
% 0.22/0.46  fof(f50,plain,(
% 0.22/0.46    r1_tarski(sK1,sK2)),
% 0.22/0.46    inference(cnf_transformation,[],[f25])).
% 0.22/0.46  fof(f291,plain,(
% 0.22/0.46    ~spl8_1 | spl8_10),
% 0.22/0.46    inference(avatar_contradiction_clause,[],[f280])).
% 0.22/0.46  fof(f280,plain,(
% 0.22/0.46    $false | (~spl8_1 | spl8_10)),
% 0.22/0.46    inference(subsumption_resolution,[],[f51,f260])).
% 0.22/0.46  fof(f260,plain,(
% 0.22/0.46    ~v1_xboole_0(k1_xboole_0) | (~spl8_1 | spl8_10)),
% 0.22/0.46    inference(forward_demodulation,[],[f255,f92])).
% 0.22/0.46  fof(f92,plain,(
% 0.22/0.46    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.22/0.46    inference(equality_resolution,[],[f73])).
% 0.22/0.46  fof(f73,plain,(
% 0.22/0.46    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f5])).
% 0.22/0.46  fof(f5,axiom,(
% 0.22/0.46    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.46  fof(f255,plain,(
% 0.22/0.46    ~v1_xboole_0(k2_zfmisc_1(k1_xboole_0,sK1)) | (~spl8_1 | spl8_10)),
% 0.22/0.46    inference(backward_demodulation,[],[f187,f114])).
% 0.22/0.46  fof(f187,plain,(
% 0.22/0.46    ~v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | spl8_10),
% 0.22/0.46    inference(avatar_component_clause,[],[f185])).
% 0.22/0.46  fof(f185,plain,(
% 0.22/0.46    spl8_10 <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 0.22/0.46  fof(f51,plain,(
% 0.22/0.46    v1_xboole_0(k1_xboole_0)),
% 0.22/0.46    inference(cnf_transformation,[],[f1])).
% 0.22/0.46  fof(f1,axiom,(
% 0.22/0.46    v1_xboole_0(k1_xboole_0)),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.46  fof(f248,plain,(
% 0.22/0.46    spl8_14 | spl8_2),
% 0.22/0.46    inference(avatar_split_clause,[],[f200,f116,f245])).
% 0.22/0.46  fof(f200,plain,(
% 0.22/0.46    k1_xboole_0 = sK1 | sK0 = k1_relat_1(sK3)),
% 0.22/0.46    inference(global_subsumption,[],[f48,f49,f192])).
% 0.22/0.46  fof(f192,plain,(
% 0.22/0.46    sK0 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | k1_xboole_0 = sK1 | ~v1_funct_2(sK3,sK0,sK1)),
% 0.22/0.46    inference(superposition,[],[f120,f85])).
% 0.22/0.46  fof(f85,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f43])).
% 0.22/0.46  fof(f120,plain,(
% 0.22/0.46    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)),
% 0.22/0.46    inference(resolution,[],[f49,f77])).
% 0.22/0.46  fof(f48,plain,(
% 0.22/0.46    v1_funct_2(sK3,sK0,sK1)),
% 0.22/0.46    inference(cnf_transformation,[],[f25])).
% 0.22/0.46  fof(f234,plain,(
% 0.22/0.46    spl8_13 | ~spl8_7),
% 0.22/0.46    inference(avatar_split_clause,[],[f103,f154,f231])).
% 0.22/0.46  fof(f103,plain,(
% 0.22/0.46    ~v1_relat_1(sK3) | v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3))),
% 0.22/0.46    inference(resolution,[],[f47,f61])).
% 0.22/0.46  fof(f61,plain,(
% 0.22/0.46    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))) )),
% 0.22/0.46    inference(cnf_transformation,[],[f32])).
% 0.22/0.46  fof(f32,plain,(
% 0.22/0.46    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.46    inference(flattening,[],[f31])).
% 0.22/0.46  fof(f31,plain,(
% 0.22/0.46    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.46    inference(ennf_transformation,[],[f21])).
% 0.22/0.46  fof(f21,axiom,(
% 0.22/0.46    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).
% 0.22/0.46  fof(f47,plain,(
% 0.22/0.46    v1_funct_1(sK3)),
% 0.22/0.46    inference(cnf_transformation,[],[f25])).
% 0.22/0.46  fof(f188,plain,(
% 0.22/0.46    spl8_9 | ~spl8_10),
% 0.22/0.46    inference(avatar_split_clause,[],[f129,f185,f181])).
% 0.22/0.46  fof(f129,plain,(
% 0.22/0.46    ~v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | v1_xboole_0(sK3)),
% 0.22/0.46    inference(resolution,[],[f49,f57])).
% 0.22/0.46  fof(f57,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f28])).
% 0.22/0.46  fof(f28,plain,(
% 0.22/0.46    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.22/0.46    inference(ennf_transformation,[],[f6])).
% 0.22/0.46  fof(f6,axiom,(
% 0.22/0.46    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.22/0.46  fof(f169,plain,(
% 0.22/0.46    spl8_8),
% 0.22/0.46    inference(avatar_contradiction_clause,[],[f166])).
% 0.22/0.46  fof(f166,plain,(
% 0.22/0.46    $false | spl8_8),
% 0.22/0.46    inference(resolution,[],[f160,f63])).
% 0.22/0.46  fof(f63,plain,(
% 0.22/0.46    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.46    inference(cnf_transformation,[],[f11])).
% 0.22/0.46  fof(f11,axiom,(
% 0.22/0.46    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.46  fof(f160,plain,(
% 0.22/0.46    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl8_8),
% 0.22/0.46    inference(avatar_component_clause,[],[f158])).
% 0.22/0.46  fof(f158,plain,(
% 0.22/0.46    spl8_8 <=> v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.22/0.46  fof(f161,plain,(
% 0.22/0.46    spl8_7 | ~spl8_8),
% 0.22/0.46    inference(avatar_split_clause,[],[f128,f158,f154])).
% 0.22/0.46  fof(f128,plain,(
% 0.22/0.46    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | v1_relat_1(sK3)),
% 0.22/0.46    inference(resolution,[],[f49,f60])).
% 0.22/0.46  fof(f60,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f30])).
% 0.22/0.46  fof(f30,plain,(
% 0.22/0.46    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.46    inference(ennf_transformation,[],[f8])).
% 0.22/0.46  fof(f8,axiom,(
% 0.22/0.46    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.46  fof(f151,plain,(
% 0.22/0.46    ~spl8_5 | ~spl8_6),
% 0.22/0.46    inference(avatar_split_clause,[],[f102,f148,f144])).
% 0.22/0.46  fof(f102,plain,(
% 0.22/0.46    ~v1_funct_2(sK3,sK0,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.22/0.46    inference(global_subsumption,[],[f47,f45])).
% 0.22/0.46  fof(f45,plain,(
% 0.22/0.46    ~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK0,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.22/0.46    inference(cnf_transformation,[],[f25])).
% 0.22/0.46  fof(f142,plain,(
% 0.22/0.46    spl8_3 | ~spl8_4),
% 0.22/0.46    inference(avatar_split_clause,[],[f106,f139,f135])).
% 0.22/0.46  fof(f106,plain,(
% 0.22/0.46    ~r1_tarski(sK2,sK1) | sK1 = sK2),
% 0.22/0.46    inference(resolution,[],[f50,f71])).
% 0.22/0.46  fof(f71,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.22/0.46    inference(cnf_transformation,[],[f2])).
% 0.22/0.46  fof(f119,plain,(
% 0.22/0.46    spl8_1 | ~spl8_2),
% 0.22/0.46    inference(avatar_split_clause,[],[f46,f116,f112])).
% 0.22/0.46  fof(f46,plain,(
% 0.22/0.46    k1_xboole_0 != sK1 | k1_xboole_0 = sK0),
% 0.22/0.46    inference(cnf_transformation,[],[f25])).
% 0.22/0.46  % SZS output end Proof for theBenchmark
% 0.22/0.46  % (21267)------------------------------
% 0.22/0.46  % (21267)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.46  % (21267)Termination reason: Refutation
% 0.22/0.46  
% 0.22/0.46  % (21267)Memory used [KB]: 11129
% 0.22/0.46  % (21267)Time elapsed: 0.036 s
% 0.22/0.46  % (21267)------------------------------
% 0.22/0.46  % (21267)------------------------------
% 0.22/0.47  % (21252)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.47  % (21243)Success in time 0.107 s
%------------------------------------------------------------------------------
