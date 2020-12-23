%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:36 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 208 expanded)
%              Number of leaves         :   31 (  82 expanded)
%              Depth                    :    9
%              Number of atoms          :  366 ( 612 expanded)
%              Number of equality atoms :   56 (  91 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f392,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f70,f75,f80,f89,f94,f99,f113,f118,f123,f132,f137,f146,f155,f159,f199,f246,f324,f330,f344,f391])).

fof(f391,plain,
    ( ~ spl8_13
    | ~ spl8_27
    | ~ spl8_32 ),
    inference(avatar_contradiction_clause,[],[f390])).

fof(f390,plain,
    ( $false
    | ~ spl8_13
    | ~ spl8_27
    | ~ spl8_32 ),
    inference(subsumption_resolution,[],[f328,f382])).

fof(f382,plain,
    ( ! [X0] : ~ sP5(X0,sK3)
    | ~ spl8_13
    | ~ spl8_27 ),
    inference(resolution,[],[f381,f150])).

fof(f150,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k2_relat_1(sK3))
        | ~ sP5(X0,sK3) )
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f149])).

fof(f149,plain,
    ( spl8_13
  <=> ! [X0] :
        ( ~ sP5(X0,sK3)
        | r2_hidden(X0,k2_relat_1(sK3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f381,plain,
    ( ! [X2] : ~ r2_hidden(X2,k2_relat_1(sK3))
    | ~ spl8_27 ),
    inference(resolution,[],[f245,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

% (24473)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f245,plain,
    ( v1_xboole_0(k2_relat_1(sK3))
    | ~ spl8_27 ),
    inference(avatar_component_clause,[],[f243])).

fof(f243,plain,
    ( spl8_27
  <=> v1_xboole_0(k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).

fof(f328,plain,
    ( sP5(k1_funct_1(sK3,sK2),sK3)
    | ~ spl8_32 ),
    inference(avatar_component_clause,[],[f327])).

fof(f327,plain,
    ( spl8_32
  <=> sP5(k1_funct_1(sK3,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).

fof(f344,plain,
    ( ~ spl8_2
    | ~ spl8_12
    | spl8_32 ),
    inference(avatar_contradiction_clause,[],[f343])).

fof(f343,plain,
    ( $false
    | ~ spl8_2
    | ~ spl8_12
    | spl8_32 ),
    inference(subsumption_resolution,[],[f342,f74])).

fof(f74,plain,
    ( r2_hidden(sK2,sK0)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl8_2
  <=> r2_hidden(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f342,plain,
    ( ~ r2_hidden(sK2,sK0)
    | ~ spl8_12
    | spl8_32 ),
    inference(forward_demodulation,[],[f340,f141])).

fof(f141,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl8_12
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f340,plain,
    ( ~ r2_hidden(sK2,k1_relat_1(sK3))
    | spl8_32 ),
    inference(resolution,[],[f329,f60])).

fof(f60,plain,(
    ! [X0,X3] :
      ( sP5(k1_funct_1(X0,X3),X0)
      | ~ r2_hidden(X3,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(X3,k1_relat_1(X0))
      | k1_funct_1(X0,X3) != X2
      | sP5(X2,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

fof(f329,plain,
    ( ~ sP5(k1_funct_1(sK3,sK2),sK3)
    | spl8_32 ),
    inference(avatar_component_clause,[],[f327])).

fof(f330,plain,
    ( ~ spl8_32
    | ~ spl8_13
    | spl8_31 ),
    inference(avatar_split_clause,[],[f325,f321,f149,f327])).

fof(f321,plain,
    ( spl8_31
  <=> r2_hidden(k1_funct_1(sK3,sK2),k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_31])])).

fof(f325,plain,
    ( ~ sP5(k1_funct_1(sK3,sK2),sK3)
    | ~ spl8_13
    | spl8_31 ),
    inference(resolution,[],[f323,f150])).

fof(f323,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK2),k2_relat_1(sK3))
    | spl8_31 ),
    inference(avatar_component_clause,[],[f321])).

fof(f324,plain,
    ( ~ spl8_31
    | spl8_5
    | ~ spl8_20 ),
    inference(avatar_split_clause,[],[f299,f197,f91,f321])).

fof(f91,plain,
    ( spl8_5
  <=> r2_hidden(k1_funct_1(sK3,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f197,plain,
    ( spl8_20
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK3))
        | r2_hidden(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f299,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK2),k2_relat_1(sK3))
    | spl8_5
    | ~ spl8_20 ),
    inference(resolution,[],[f198,f93])).

fof(f93,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK2),sK1)
    | spl8_5 ),
    inference(avatar_component_clause,[],[f91])).

fof(f198,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,k2_relat_1(sK3)) )
    | ~ spl8_20 ),
    inference(avatar_component_clause,[],[f197])).

fof(f246,plain,
    ( spl8_27
    | ~ spl8_10
    | ~ spl8_19 ),
    inference(avatar_split_clause,[],[f228,f193,f129,f243])).

fof(f129,plain,
    ( spl8_10
  <=> m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f193,plain,
    ( spl8_19
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f228,plain,
    ( v1_xboole_0(k2_relat_1(sK3))
    | ~ spl8_10
    | ~ spl8_19 ),
    inference(resolution,[],[f217,f43])).

fof(f43,plain,(
    ! [X0] :
      ( r2_hidden(sK7(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f217,plain,
    ( ! [X1] : ~ r2_hidden(X1,k2_relat_1(sK3))
    | ~ spl8_10
    | ~ spl8_19 ),
    inference(resolution,[],[f200,f131])).

fof(f131,plain,
    ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1))
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f129])).

fof(f200,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1))
        | ~ r2_hidden(X1,X0) )
    | ~ spl8_19 ),
    inference(resolution,[],[f195,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f195,plain,
    ( v1_xboole_0(sK1)
    | ~ spl8_19 ),
    inference(avatar_component_clause,[],[f193])).

fof(f199,plain,
    ( spl8_19
    | spl8_20
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f161,f129,f197,f193])).

fof(f161,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK3))
        | v1_xboole_0(sK1)
        | r2_hidden(X0,sK1) )
    | ~ spl8_10 ),
    inference(resolution,[],[f142,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

% (24462)Refutation not found, incomplete strategy% (24462)------------------------------
% (24462)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (24462)Termination reason: Refutation not found, incomplete strategy

% (24462)Memory used [KB]: 10618
% (24462)Time elapsed: 0.083 s
% (24462)------------------------------
% (24462)------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f142,plain,
    ( ! [X0] :
        ( m1_subset_1(X0,sK1)
        | ~ r2_hidden(X0,k2_relat_1(sK3)) )
    | ~ spl8_10 ),
    inference(resolution,[],[f131,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f159,plain,
    ( ~ spl8_6
    | spl8_14 ),
    inference(avatar_contradiction_clause,[],[f158])).

fof(f158,plain,
    ( $false
    | ~ spl8_6
    | spl8_14 ),
    inference(subsumption_resolution,[],[f157,f45])).

fof(f45,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f157,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | ~ spl8_6
    | spl8_14 ),
    inference(resolution,[],[f156,f98])).

fof(f98,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl8_6
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f156,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl8_14 ),
    inference(resolution,[],[f154,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f154,plain,
    ( ~ v1_relat_1(sK3)
    | spl8_14 ),
    inference(avatar_component_clause,[],[f152])).

fof(f152,plain,
    ( spl8_14
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f155,plain,
    ( spl8_13
    | ~ spl8_14
    | ~ spl8_1 ),
    inference(avatar_split_clause,[],[f81,f67,f152,f149])).

fof(f67,plain,
    ( spl8_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f81,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK3)
        | ~ sP5(X0,sK3)
        | r2_hidden(X0,k2_relat_1(sK3)) )
    | ~ spl8_1 ),
    inference(resolution,[],[f69,f59])).

fof(f59,plain,(
    ! [X2,X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ sP5(X2,X0)
      | r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ sP5(X2,X0)
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f69,plain,
    ( v1_funct_1(sK3)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f67])).

fof(f146,plain,
    ( spl8_12
    | ~ spl8_9
    | ~ spl8_11 ),
    inference(avatar_split_clause,[],[f144,f134,f120,f139])).

fof(f120,plain,
    ( spl8_9
  <=> k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f134,plain,
    ( spl8_11
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f144,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl8_9
    | ~ spl8_11 ),
    inference(superposition,[],[f136,f122])).

fof(f122,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f120])).

fof(f136,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f134])).

fof(f137,plain,
    ( spl8_11
    | spl8_3
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f108,f96,f86,f77,f134])).

fof(f77,plain,
    ( spl8_3
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f86,plain,
    ( spl8_4
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f108,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | spl8_3
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f107,f88])).

fof(f88,plain,
    ( v1_funct_2(sK3,sK0,sK1)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f86])).

fof(f107,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ v1_funct_2(sK3,sK0,sK1)
    | spl8_3
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f101,f79])).

fof(f79,plain,
    ( k1_xboole_0 != sK1
    | spl8_3 ),
    inference(avatar_component_clause,[],[f77])).

fof(f101,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ spl8_6 ),
    inference(resolution,[],[f98,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f132,plain,
    ( spl8_10
    | ~ spl8_7
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f126,f115,f110,f129])).

fof(f110,plain,
    ( spl8_7
  <=> m1_subset_1(k2_relset_1(sK0,sK1,sK3),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f115,plain,
    ( spl8_8
  <=> k2_relat_1(sK3) = k2_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f126,plain,
    ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1))
    | ~ spl8_7
    | ~ spl8_8 ),
    inference(superposition,[],[f112,f117])).

fof(f117,plain,
    ( k2_relat_1(sK3) = k2_relset_1(sK0,sK1,sK3)
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f115])).

fof(f112,plain,
    ( m1_subset_1(k2_relset_1(sK0,sK1,sK3),k1_zfmisc_1(sK1))
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f110])).

fof(f123,plain,
    ( spl8_9
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f104,f96,f120])).

fof(f104,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)
    | ~ spl8_6 ),
    inference(resolution,[],[f98,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f118,plain,
    ( spl8_8
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f103,f96,f115])).

fof(f103,plain,
    ( k2_relat_1(sK3) = k2_relset_1(sK0,sK1,sK3)
    | ~ spl8_6 ),
    inference(resolution,[],[f98,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f113,plain,
    ( spl8_7
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f102,f96,f110])).

fof(f102,plain,
    ( m1_subset_1(k2_relset_1(sK0,sK1,sK3),k1_zfmisc_1(sK1))
    | ~ spl8_6 ),
    inference(resolution,[],[f98,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(f99,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f31,f96])).

fof(f31,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_hidden(k1_funct_1(X3,X2),X1)
      & k1_xboole_0 != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_hidden(k1_funct_1(X3,X2),X1)
      & k1_xboole_0 != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f13])).

% (24475)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r2_hidden(X2,X0)
         => ( r2_hidden(k1_funct_1(X3,X2),X1)
            | k1_xboole_0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

fof(f94,plain,(
    ~ spl8_5 ),
    inference(avatar_split_clause,[],[f34,f91])).

fof(f34,plain,(
    ~ r2_hidden(k1_funct_1(sK3,sK2),sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f89,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f30,f86])).

fof(f30,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f80,plain,(
    ~ spl8_3 ),
    inference(avatar_split_clause,[],[f33,f77])).

fof(f33,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f15])).

fof(f75,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f32,f72])).

fof(f32,plain,(
    r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f70,plain,(
    spl8_1 ),
    inference(avatar_split_clause,[],[f29,f67])).

fof(f29,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:29:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.48  % (24464)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.49  % (24465)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.49  % (24466)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (24464)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % (24461)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.49  % (24472)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.49  % (24467)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.50  % (24472)Refutation not found, incomplete strategy% (24472)------------------------------
% 0.21/0.50  % (24472)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (24472)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (24472)Memory used [KB]: 10618
% 0.21/0.50  % (24472)Time elapsed: 0.084 s
% 0.21/0.50  % (24472)------------------------------
% 0.21/0.50  % (24472)------------------------------
% 0.21/0.50  % (24470)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.50  % (24469)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.50  % (24462)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f392,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f70,f75,f80,f89,f94,f99,f113,f118,f123,f132,f137,f146,f155,f159,f199,f246,f324,f330,f344,f391])).
% 0.21/0.50  fof(f391,plain,(
% 0.21/0.50    ~spl8_13 | ~spl8_27 | ~spl8_32),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f390])).
% 0.21/0.50  fof(f390,plain,(
% 0.21/0.50    $false | (~spl8_13 | ~spl8_27 | ~spl8_32)),
% 0.21/0.50    inference(subsumption_resolution,[],[f328,f382])).
% 0.21/0.50  fof(f382,plain,(
% 0.21/0.50    ( ! [X0] : (~sP5(X0,sK3)) ) | (~spl8_13 | ~spl8_27)),
% 0.21/0.50    inference(resolution,[],[f381,f150])).
% 0.21/0.50  fof(f150,plain,(
% 0.21/0.50    ( ! [X0] : (r2_hidden(X0,k2_relat_1(sK3)) | ~sP5(X0,sK3)) ) | ~spl8_13),
% 0.21/0.50    inference(avatar_component_clause,[],[f149])).
% 0.21/0.50  fof(f149,plain,(
% 0.21/0.50    spl8_13 <=> ! [X0] : (~sP5(X0,sK3) | r2_hidden(X0,k2_relat_1(sK3)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 0.21/0.50  fof(f381,plain,(
% 0.21/0.50    ( ! [X2] : (~r2_hidden(X2,k2_relat_1(sK3))) ) | ~spl8_27),
% 0.21/0.50    inference(resolution,[],[f245,f44])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~r2_hidden(X1,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.50  % (24473)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  fof(f245,plain,(
% 0.21/0.50    v1_xboole_0(k2_relat_1(sK3)) | ~spl8_27),
% 0.21/0.50    inference(avatar_component_clause,[],[f243])).
% 0.21/0.50  fof(f243,plain,(
% 0.21/0.50    spl8_27 <=> v1_xboole_0(k2_relat_1(sK3))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).
% 0.21/0.50  fof(f328,plain,(
% 0.21/0.50    sP5(k1_funct_1(sK3,sK2),sK3) | ~spl8_32),
% 0.21/0.50    inference(avatar_component_clause,[],[f327])).
% 0.21/0.50  fof(f327,plain,(
% 0.21/0.50    spl8_32 <=> sP5(k1_funct_1(sK3,sK2),sK3)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).
% 0.21/0.50  fof(f344,plain,(
% 0.21/0.50    ~spl8_2 | ~spl8_12 | spl8_32),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f343])).
% 0.21/0.50  fof(f343,plain,(
% 0.21/0.50    $false | (~spl8_2 | ~spl8_12 | spl8_32)),
% 0.21/0.50    inference(subsumption_resolution,[],[f342,f74])).
% 0.21/0.50  fof(f74,plain,(
% 0.21/0.50    r2_hidden(sK2,sK0) | ~spl8_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f72])).
% 0.21/0.50  fof(f72,plain,(
% 0.21/0.50    spl8_2 <=> r2_hidden(sK2,sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.21/0.50  fof(f342,plain,(
% 0.21/0.50    ~r2_hidden(sK2,sK0) | (~spl8_12 | spl8_32)),
% 0.21/0.50    inference(forward_demodulation,[],[f340,f141])).
% 0.21/0.50  fof(f141,plain,(
% 0.21/0.50    sK0 = k1_relat_1(sK3) | ~spl8_12),
% 0.21/0.50    inference(avatar_component_clause,[],[f139])).
% 0.21/0.50  fof(f139,plain,(
% 0.21/0.50    spl8_12 <=> sK0 = k1_relat_1(sK3)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 0.21/0.50  fof(f340,plain,(
% 0.21/0.50    ~r2_hidden(sK2,k1_relat_1(sK3)) | spl8_32),
% 0.21/0.50    inference(resolution,[],[f329,f60])).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    ( ! [X0,X3] : (sP5(k1_funct_1(X0,X3),X0) | ~r2_hidden(X3,k1_relat_1(X0))) )),
% 0.21/0.50    inference(equality_resolution,[],[f36])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    ( ! [X2,X0,X3] : (~r2_hidden(X3,k1_relat_1(X0)) | k1_funct_1(X0,X3) != X2 | sP5(X2,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(flattening,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).
% 0.21/0.50  fof(f329,plain,(
% 0.21/0.50    ~sP5(k1_funct_1(sK3,sK2),sK3) | spl8_32),
% 0.21/0.50    inference(avatar_component_clause,[],[f327])).
% 0.21/0.50  fof(f330,plain,(
% 0.21/0.50    ~spl8_32 | ~spl8_13 | spl8_31),
% 0.21/0.50    inference(avatar_split_clause,[],[f325,f321,f149,f327])).
% 0.21/0.50  fof(f321,plain,(
% 0.21/0.50    spl8_31 <=> r2_hidden(k1_funct_1(sK3,sK2),k2_relat_1(sK3))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_31])])).
% 0.21/0.50  fof(f325,plain,(
% 0.21/0.50    ~sP5(k1_funct_1(sK3,sK2),sK3) | (~spl8_13 | spl8_31)),
% 0.21/0.50    inference(resolution,[],[f323,f150])).
% 0.21/0.50  fof(f323,plain,(
% 0.21/0.50    ~r2_hidden(k1_funct_1(sK3,sK2),k2_relat_1(sK3)) | spl8_31),
% 0.21/0.50    inference(avatar_component_clause,[],[f321])).
% 0.21/0.50  fof(f324,plain,(
% 0.21/0.50    ~spl8_31 | spl8_5 | ~spl8_20),
% 0.21/0.50    inference(avatar_split_clause,[],[f299,f197,f91,f321])).
% 0.21/0.50  fof(f91,plain,(
% 0.21/0.50    spl8_5 <=> r2_hidden(k1_funct_1(sK3,sK2),sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.21/0.50  fof(f197,plain,(
% 0.21/0.50    spl8_20 <=> ! [X0] : (~r2_hidden(X0,k2_relat_1(sK3)) | r2_hidden(X0,sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).
% 0.21/0.50  fof(f299,plain,(
% 0.21/0.50    ~r2_hidden(k1_funct_1(sK3,sK2),k2_relat_1(sK3)) | (spl8_5 | ~spl8_20)),
% 0.21/0.50    inference(resolution,[],[f198,f93])).
% 0.21/0.50  fof(f93,plain,(
% 0.21/0.50    ~r2_hidden(k1_funct_1(sK3,sK2),sK1) | spl8_5),
% 0.21/0.50    inference(avatar_component_clause,[],[f91])).
% 0.21/0.50  fof(f198,plain,(
% 0.21/0.50    ( ! [X0] : (r2_hidden(X0,sK1) | ~r2_hidden(X0,k2_relat_1(sK3))) ) | ~spl8_20),
% 0.21/0.50    inference(avatar_component_clause,[],[f197])).
% 0.21/0.50  fof(f246,plain,(
% 0.21/0.50    spl8_27 | ~spl8_10 | ~spl8_19),
% 0.21/0.50    inference(avatar_split_clause,[],[f228,f193,f129,f243])).
% 0.21/0.50  fof(f129,plain,(
% 0.21/0.50    spl8_10 <=> m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 0.21/0.50  fof(f193,plain,(
% 0.21/0.50    spl8_19 <=> v1_xboole_0(sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).
% 0.21/0.50  fof(f228,plain,(
% 0.21/0.50    v1_xboole_0(k2_relat_1(sK3)) | (~spl8_10 | ~spl8_19)),
% 0.21/0.50    inference(resolution,[],[f217,f43])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    ( ! [X0] : (r2_hidden(sK7(X0),X0) | v1_xboole_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f1])).
% 0.21/0.50  fof(f217,plain,(
% 0.21/0.50    ( ! [X1] : (~r2_hidden(X1,k2_relat_1(sK3))) ) | (~spl8_10 | ~spl8_19)),
% 0.21/0.50    inference(resolution,[],[f200,f131])).
% 0.21/0.50  fof(f131,plain,(
% 0.21/0.50    m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1)) | ~spl8_10),
% 0.21/0.50    inference(avatar_component_clause,[],[f129])).
% 0.21/0.50  fof(f200,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(sK1)) | ~r2_hidden(X1,X0)) ) | ~spl8_19),
% 0.21/0.50    inference(resolution,[],[f195,f57])).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 0.21/0.50  fof(f195,plain,(
% 0.21/0.50    v1_xboole_0(sK1) | ~spl8_19),
% 0.21/0.50    inference(avatar_component_clause,[],[f193])).
% 0.21/0.50  fof(f199,plain,(
% 0.21/0.50    spl8_19 | spl8_20 | ~spl8_10),
% 0.21/0.50    inference(avatar_split_clause,[],[f161,f129,f197,f193])).
% 0.21/0.50  fof(f161,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK3)) | v1_xboole_0(sK1) | r2_hidden(X0,sK1)) ) | ~spl8_10),
% 0.21/0.50    inference(resolution,[],[f142,f46])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.50    inference(flattening,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f2])).
% 0.21/0.50  % (24462)Refutation not found, incomplete strategy% (24462)------------------------------
% 0.21/0.50  % (24462)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (24462)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (24462)Memory used [KB]: 10618
% 0.21/0.50  % (24462)Time elapsed: 0.083 s
% 0.21/0.50  % (24462)------------------------------
% 0.21/0.50  % (24462)------------------------------
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.50  fof(f142,plain,(
% 0.21/0.50    ( ! [X0] : (m1_subset_1(X0,sK1) | ~r2_hidden(X0,k2_relat_1(sK3))) ) | ~spl8_10),
% 0.21/0.50    inference(resolution,[],[f131,f56])).
% 0.21/0.50  fof(f56,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1) | m1_subset_1(X0,X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.50    inference(flattening,[],[f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.21/0.50    inference(ennf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 0.21/0.50  fof(f159,plain,(
% 0.21/0.50    ~spl8_6 | spl8_14),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f158])).
% 0.21/0.50  fof(f158,plain,(
% 0.21/0.50    $false | (~spl8_6 | spl8_14)),
% 0.21/0.50    inference(subsumption_resolution,[],[f157,f45])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.50  fof(f157,plain,(
% 0.21/0.50    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | (~spl8_6 | spl8_14)),
% 0.21/0.50    inference(resolution,[],[f156,f98])).
% 0.21/0.50  fof(f98,plain,(
% 0.21/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl8_6),
% 0.21/0.50    inference(avatar_component_clause,[],[f96])).
% 0.21/0.50  fof(f96,plain,(
% 0.21/0.50    spl8_6 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.21/0.50  fof(f156,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl8_14),
% 0.21/0.50    inference(resolution,[],[f154,f35])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.50  fof(f154,plain,(
% 0.21/0.50    ~v1_relat_1(sK3) | spl8_14),
% 0.21/0.50    inference(avatar_component_clause,[],[f152])).
% 0.21/0.50  fof(f152,plain,(
% 0.21/0.50    spl8_14 <=> v1_relat_1(sK3)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 0.21/0.50  fof(f155,plain,(
% 0.21/0.50    spl8_13 | ~spl8_14 | ~spl8_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f81,f67,f152,f149])).
% 0.21/0.50  fof(f67,plain,(
% 0.21/0.50    spl8_1 <=> v1_funct_1(sK3)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.21/0.50  fof(f81,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_relat_1(sK3) | ~sP5(X0,sK3) | r2_hidden(X0,k2_relat_1(sK3))) ) | ~spl8_1),
% 0.21/0.50    inference(resolution,[],[f69,f59])).
% 0.21/0.50  fof(f59,plain,(
% 0.21/0.50    ( ! [X2,X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | ~sP5(X2,X0) | r2_hidden(X2,k2_relat_1(X0))) )),
% 0.21/0.50    inference(equality_resolution,[],[f39])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~sP5(X2,X0) | r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f69,plain,(
% 0.21/0.50    v1_funct_1(sK3) | ~spl8_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f67])).
% 0.21/0.50  fof(f146,plain,(
% 0.21/0.50    spl8_12 | ~spl8_9 | ~spl8_11),
% 0.21/0.50    inference(avatar_split_clause,[],[f144,f134,f120,f139])).
% 0.21/0.50  fof(f120,plain,(
% 0.21/0.50    spl8_9 <=> k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.21/0.50  fof(f134,plain,(
% 0.21/0.50    spl8_11 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 0.21/0.50  fof(f144,plain,(
% 0.21/0.50    sK0 = k1_relat_1(sK3) | (~spl8_9 | ~spl8_11)),
% 0.21/0.50    inference(superposition,[],[f136,f122])).
% 0.21/0.50  fof(f122,plain,(
% 0.21/0.50    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) | ~spl8_9),
% 0.21/0.50    inference(avatar_component_clause,[],[f120])).
% 0.21/0.50  fof(f136,plain,(
% 0.21/0.50    sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl8_11),
% 0.21/0.50    inference(avatar_component_clause,[],[f134])).
% 0.21/0.50  fof(f137,plain,(
% 0.21/0.50    spl8_11 | spl8_3 | ~spl8_4 | ~spl8_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f108,f96,f86,f77,f134])).
% 0.21/0.50  fof(f77,plain,(
% 0.21/0.50    spl8_3 <=> k1_xboole_0 = sK1),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.21/0.50  fof(f86,plain,(
% 0.21/0.50    spl8_4 <=> v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.21/0.50  fof(f108,plain,(
% 0.21/0.50    sK0 = k1_relset_1(sK0,sK1,sK3) | (spl8_3 | ~spl8_4 | ~spl8_6)),
% 0.21/0.50    inference(subsumption_resolution,[],[f107,f88])).
% 0.21/0.50  fof(f88,plain,(
% 0.21/0.50    v1_funct_2(sK3,sK0,sK1) | ~spl8_4),
% 0.21/0.50    inference(avatar_component_clause,[],[f86])).
% 0.21/0.50  fof(f107,plain,(
% 0.21/0.50    sK0 = k1_relset_1(sK0,sK1,sK3) | ~v1_funct_2(sK3,sK0,sK1) | (spl8_3 | ~spl8_6)),
% 0.21/0.50    inference(subsumption_resolution,[],[f101,f79])).
% 0.21/0.50  fof(f79,plain,(
% 0.21/0.50    k1_xboole_0 != sK1 | spl8_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f77])).
% 0.21/0.50  fof(f101,plain,(
% 0.21/0.50    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~v1_funct_2(sK3,sK0,sK1) | ~spl8_6),
% 0.21/0.50    inference(resolution,[],[f98,f55])).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(flattening,[],[f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.50  fof(f132,plain,(
% 0.21/0.50    spl8_10 | ~spl8_7 | ~spl8_8),
% 0.21/0.50    inference(avatar_split_clause,[],[f126,f115,f110,f129])).
% 0.21/0.50  fof(f110,plain,(
% 0.21/0.50    spl8_7 <=> m1_subset_1(k2_relset_1(sK0,sK1,sK3),k1_zfmisc_1(sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.21/0.50  fof(f115,plain,(
% 0.21/0.50    spl8_8 <=> k2_relat_1(sK3) = k2_relset_1(sK0,sK1,sK3)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.21/0.50  fof(f126,plain,(
% 0.21/0.50    m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1)) | (~spl8_7 | ~spl8_8)),
% 0.21/0.50    inference(superposition,[],[f112,f117])).
% 0.21/0.50  fof(f117,plain,(
% 0.21/0.50    k2_relat_1(sK3) = k2_relset_1(sK0,sK1,sK3) | ~spl8_8),
% 0.21/0.50    inference(avatar_component_clause,[],[f115])).
% 0.21/0.50  fof(f112,plain,(
% 0.21/0.50    m1_subset_1(k2_relset_1(sK0,sK1,sK3),k1_zfmisc_1(sK1)) | ~spl8_7),
% 0.21/0.50    inference(avatar_component_clause,[],[f110])).
% 0.21/0.50  fof(f123,plain,(
% 0.21/0.50    spl8_9 | ~spl8_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f104,f96,f120])).
% 0.21/0.50  fof(f104,plain,(
% 0.21/0.50    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) | ~spl8_6),
% 0.21/0.50    inference(resolution,[],[f98,f47])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.50  fof(f118,plain,(
% 0.21/0.50    spl8_8 | ~spl8_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f103,f96,f115])).
% 0.21/0.50  fof(f103,plain,(
% 0.21/0.50    k2_relat_1(sK3) = k2_relset_1(sK0,sK1,sK3) | ~spl8_6),
% 0.21/0.50    inference(resolution,[],[f98,f48])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.50  fof(f113,plain,(
% 0.21/0.50    spl8_7 | ~spl8_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f102,f96,f110])).
% 0.21/0.50  fof(f102,plain,(
% 0.21/0.50    m1_subset_1(k2_relset_1(sK0,sK1,sK3),k1_zfmisc_1(sK1)) | ~spl8_6),
% 0.21/0.50    inference(resolution,[],[f98,f49])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).
% 0.21/0.50  fof(f99,plain,(
% 0.21/0.50    spl8_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f31,f96])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ? [X0,X1,X2,X3] : (~r2_hidden(k1_funct_1(X3,X2),X1) & k1_xboole_0 != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.21/0.50    inference(flattening,[],[f14])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ? [X0,X1,X2,X3] : (((~r2_hidden(k1_funct_1(X3,X2),X1) & k1_xboole_0 != X1) & r2_hidden(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.21/0.50    inference(ennf_transformation,[],[f13])).
% 0.21/0.50  % (24475)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.50  fof(f13,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 0.21/0.50    inference(negated_conjecture,[],[f12])).
% 0.21/0.50  fof(f12,conjecture,(
% 0.21/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).
% 0.21/0.50  fof(f94,plain,(
% 0.21/0.50    ~spl8_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f34,f91])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ~r2_hidden(k1_funct_1(sK3,sK2),sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f89,plain,(
% 0.21/0.50    spl8_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f30,f86])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f80,plain,(
% 0.21/0.50    ~spl8_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f33,f77])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    k1_xboole_0 != sK1),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f75,plain,(
% 0.21/0.50    spl8_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f32,f72])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    r2_hidden(sK2,sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f70,plain,(
% 0.21/0.50    spl8_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f29,f67])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    v1_funct_1(sK3)),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (24464)------------------------------
% 0.21/0.50  % (24464)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (24464)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (24464)Memory used [KB]: 10746
% 0.21/0.50  % (24464)Time elapsed: 0.081 s
% 0.21/0.50  % (24464)------------------------------
% 0.21/0.50  % (24464)------------------------------
% 0.21/0.50  % (24460)Success in time 0.139 s
%------------------------------------------------------------------------------
