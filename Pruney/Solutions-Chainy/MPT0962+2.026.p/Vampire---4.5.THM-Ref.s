%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:24 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 216 expanded)
%              Number of leaves         :   26 (  85 expanded)
%              Depth                    :    9
%              Number of atoms          :  318 ( 624 expanded)
%              Number of equality atoms :   57 ( 105 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f241,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f82,f87,f92,f111,f114,f125,f129,f138,f145,f151,f160,f169,f173,f214,f226,f236,f240])).

fof(f240,plain,
    ( spl7_17
    | ~ spl7_18
    | ~ spl7_19 ),
    inference(avatar_contradiction_clause,[],[f237])).

% (21346)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
fof(f237,plain,
    ( $false
    | spl7_17
    | ~ spl7_18
    | ~ spl7_19 ),
    inference(unit_resulting_resolution,[],[f213,f225,f235,f73])).

fof(f73,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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

fof(f235,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK1)
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f233])).

fof(f233,plain,
    ( spl7_19
  <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f225,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f223])).

fof(f223,plain,
    ( spl7_18
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f213,plain,
    ( ~ v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)
    | spl7_17 ),
    inference(avatar_component_clause,[],[f211])).

fof(f211,plain,
    ( spl7_17
  <=> v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f236,plain,
    ( spl7_19
    | ~ spl7_14
    | ~ spl7_15 ),
    inference(avatar_split_clause,[],[f194,f171,f166,f233])).

fof(f166,plain,
    ( spl7_14
  <=> k1_relat_1(sK1) = k1_relset_1(k1_relat_1(sK1),k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f171,plain,
    ( spl7_15
  <=> ! [X0] :
        ( r2_hidden(k1_funct_1(sK1,X0),k1_xboole_0)
        | ~ r2_hidden(X0,k1_relat_1(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f194,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK1)
    | ~ spl7_14
    | ~ spl7_15 ),
    inference(backward_demodulation,[],[f168,f190])).

fof(f190,plain,
    ( k1_xboole_0 = k1_relat_1(sK1)
    | ~ spl7_15 ),
    inference(resolution,[],[f187,f32])).

fof(f32,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f187,plain,
    ( ! [X4] : r1_tarski(k1_relat_1(sK1),X4)
    | ~ spl7_15 ),
    inference(resolution,[],[f179,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f179,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_relat_1(sK1))
    | ~ spl7_15 ),
    inference(resolution,[],[f174,f31])).

fof(f31,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f174,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,k1_funct_1(sK1,X0))
        | ~ r2_hidden(X0,k1_relat_1(sK1)) )
    | ~ spl7_15 ),
    inference(resolution,[],[f172,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f172,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(sK1,X0),k1_xboole_0)
        | ~ r2_hidden(X0,k1_relat_1(sK1)) )
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f171])).

fof(f168,plain,
    ( k1_relat_1(sK1) = k1_relset_1(k1_relat_1(sK1),k1_xboole_0,sK1)
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f166])).

fof(f226,plain,
    ( spl7_18
    | ~ spl7_13
    | ~ spl7_15 ),
    inference(avatar_split_clause,[],[f193,f171,f157,f223])).

fof(f157,plain,
    ( spl7_13
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f193,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl7_13
    | ~ spl7_15 ),
    inference(backward_demodulation,[],[f159,f190])).

fof(f159,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0)))
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f157])).

fof(f214,plain,
    ( ~ spl7_17
    | spl7_11
    | ~ spl7_15 ),
    inference(avatar_split_clause,[],[f192,f171,f142,f211])).

fof(f142,plain,
    ( spl7_11
  <=> v1_funct_2(sK1,k1_relat_1(sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f192,plain,
    ( ~ v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)
    | spl7_11
    | ~ spl7_15 ),
    inference(backward_demodulation,[],[f144,f190])).

fof(f144,plain,
    ( ~ v1_funct_2(sK1,k1_relat_1(sK1),k1_xboole_0)
    | spl7_11 ),
    inference(avatar_component_clause,[],[f142])).

fof(f173,plain,
    ( ~ spl7_1
    | ~ spl7_2
    | spl7_15
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f155,f148,f171,f84,f79])).

fof(f79,plain,
    ( spl7_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f84,plain,
    ( spl7_2
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f148,plain,
    ( spl7_12
  <=> k1_xboole_0 = k2_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f155,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(sK1,X0),k1_xboole_0)
        | ~ v1_funct_1(sK1)
        | ~ r2_hidden(X0,k1_relat_1(sK1))
        | ~ v1_relat_1(sK1) )
    | ~ spl7_12 ),
    inference(superposition,[],[f63,f150])).

fof(f150,plain,
    ( k1_xboole_0 = k2_relat_1(sK1)
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f148])).

fof(f63,plain,(
    ! [X0,X3] :
      ( r2_hidden(k1_funct_1(X0,X3),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | r2_hidden(k1_funct_1(X0,X3),X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | k1_funct_1(X0,X3) != X2
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f17])).

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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f5])).

% (21345)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f5,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

fof(f169,plain,
    ( spl7_14
    | ~ spl7_8
    | ~ spl7_9 ),
    inference(avatar_split_clause,[],[f164,f122,f118,f166])).

fof(f118,plain,
    ( spl7_8
  <=> k1_relat_1(sK1) = k1_relset_1(k1_relat_1(sK1),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f122,plain,
    ( spl7_9
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f164,plain,
    ( k1_relat_1(sK1) = k1_relset_1(k1_relat_1(sK1),k1_xboole_0,sK1)
    | ~ spl7_8
    | ~ spl7_9 ),
    inference(forward_demodulation,[],[f119,f124])).

fof(f124,plain,
    ( k1_xboole_0 = sK0
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f122])).

fof(f119,plain,
    ( k1_relat_1(sK1) = k1_relset_1(k1_relat_1(sK1),sK0,sK1)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f118])).

fof(f160,plain,
    ( spl7_13
    | ~ spl7_6
    | ~ spl7_9 ),
    inference(avatar_split_clause,[],[f130,f122,f104,f157])).

fof(f104,plain,
    ( spl7_6
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f130,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0)))
    | ~ spl7_6
    | ~ spl7_9 ),
    inference(backward_demodulation,[],[f105,f124])).

fof(f105,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f104])).

fof(f151,plain,
    ( spl7_12
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f139,f135,f148])).

fof(f135,plain,
    ( spl7_10
  <=> r1_tarski(k2_relat_1(sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f139,plain,
    ( k1_xboole_0 = k2_relat_1(sK1)
    | ~ spl7_10 ),
    inference(resolution,[],[f137,f32])).

fof(f137,plain,
    ( r1_tarski(k2_relat_1(sK1),k1_xboole_0)
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f135])).

fof(f145,plain,
    ( ~ spl7_11
    | spl7_7
    | ~ spl7_9 ),
    inference(avatar_split_clause,[],[f131,f122,f108,f142])).

fof(f108,plain,
    ( spl7_7
  <=> v1_funct_2(sK1,k1_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f131,plain,
    ( ~ v1_funct_2(sK1,k1_relat_1(sK1),k1_xboole_0)
    | spl7_7
    | ~ spl7_9 ),
    inference(backward_demodulation,[],[f110,f124])).

fof(f110,plain,
    ( ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
    | spl7_7 ),
    inference(avatar_component_clause,[],[f108])).

fof(f138,plain,
    ( spl7_10
    | ~ spl7_3
    | ~ spl7_9 ),
    inference(avatar_split_clause,[],[f133,f122,f89,f135])).

fof(f89,plain,
    ( spl7_3
  <=> r1_tarski(k2_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f133,plain,
    ( r1_tarski(k2_relat_1(sK1),k1_xboole_0)
    | ~ spl7_3
    | ~ spl7_9 ),
    inference(backward_demodulation,[],[f91,f124])).

fof(f91,plain,
    ( r1_tarski(k2_relat_1(sK1),sK0)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f89])).

fof(f129,plain,
    ( ~ spl7_6
    | spl7_8 ),
    inference(avatar_contradiction_clause,[],[f126])).

fof(f126,plain,
    ( $false
    | ~ spl7_6
    | spl7_8 ),
    inference(unit_resulting_resolution,[],[f105,f120,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f120,plain,
    ( k1_relat_1(sK1) != k1_relset_1(k1_relat_1(sK1),sK0,sK1)
    | spl7_8 ),
    inference(avatar_component_clause,[],[f118])).

fof(f125,plain,
    ( spl7_7
    | ~ spl7_8
    | spl7_9
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f115,f104,f122,f118,f108])).

fof(f115,plain,
    ( k1_xboole_0 = sK0
    | k1_relat_1(sK1) != k1_relset_1(k1_relat_1(sK1),sK0,sK1)
    | v1_funct_2(sK1,k1_relat_1(sK1),sK0)
    | ~ spl7_6 ),
    inference(resolution,[],[f105,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f114,plain,
    ( ~ spl7_1
    | ~ spl7_3
    | spl7_6 ),
    inference(avatar_contradiction_clause,[],[f112])).

fof(f112,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_3
    | spl7_6 ),
    inference(unit_resulting_resolution,[],[f81,f91,f67,f106,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

fof(f106,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | spl7_6 ),
    inference(avatar_component_clause,[],[f104])).

fof(f67,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f81,plain,
    ( v1_relat_1(sK1)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f79])).

fof(f111,plain,
    ( ~ spl7_6
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f77,f108,f104])).

fof(f77,plain,
    ( ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) ),
    inference(global_subsumption,[],[f29,f27])).

fof(f27,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
        | ~ v1_funct_1(X1) )
      & r1_tarski(k2_relat_1(X1),X0)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
        | ~ v1_funct_1(X1) )
      & r1_tarski(k2_relat_1(X1),X0)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( r1_tarski(k2_relat_1(X1),X0)
         => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
            & v1_funct_2(X1,k1_relat_1(X1),X0)
            & v1_funct_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

fof(f29,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f92,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f30,f89])).

fof(f30,plain,(
    r1_tarski(k2_relat_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f87,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f29,f84])).

fof(f82,plain,(
    spl7_1 ),
    inference(avatar_split_clause,[],[f28,f79])).

fof(f28,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:27:47 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.47  % (21333)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.47  % (21351)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.47  % (21337)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.48  % (21341)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.49  % (21338)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.50  % (21355)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.51  % (21347)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.51  % (21362)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.51  % (21335)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.51  % (21336)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (21342)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.51  % (21336)Refutation not found, incomplete strategy% (21336)------------------------------
% 0.20/0.51  % (21336)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (21336)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (21336)Memory used [KB]: 6268
% 0.20/0.51  % (21336)Time elapsed: 0.107 s
% 0.20/0.51  % (21336)------------------------------
% 0.20/0.51  % (21336)------------------------------
% 0.20/0.52  % (21354)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.52  % (21332)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.52  % (21355)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % (21352)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f241,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(avatar_sat_refutation,[],[f82,f87,f92,f111,f114,f125,f129,f138,f145,f151,f160,f169,f173,f214,f226,f236,f240])).
% 0.20/0.52  fof(f240,plain,(
% 0.20/0.52    spl7_17 | ~spl7_18 | ~spl7_19),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f237])).
% 0.20/0.52  % (21346)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.52  fof(f237,plain,(
% 0.20/0.52    $false | (spl7_17 | ~spl7_18 | ~spl7_19)),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f213,f225,f235,f73])).
% 0.20/0.52  fof(f73,plain,(
% 0.20/0.52    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | v1_funct_2(X2,k1_xboole_0,X1)) )),
% 0.20/0.52    inference(equality_resolution,[],[f58])).
% 0.20/0.52  fof(f58,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f26])).
% 0.20/0.52  fof(f26,plain,(
% 0.20/0.52    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.52    inference(flattening,[],[f25])).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.52    inference(ennf_transformation,[],[f10])).
% 0.20/0.52  fof(f10,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.52  fof(f235,plain,(
% 0.20/0.52    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) | ~spl7_19),
% 0.20/0.52    inference(avatar_component_clause,[],[f233])).
% 0.20/0.52  fof(f233,plain,(
% 0.20/0.52    spl7_19 <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK1)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).
% 0.20/0.52  fof(f225,plain,(
% 0.20/0.52    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl7_18),
% 0.20/0.52    inference(avatar_component_clause,[],[f223])).
% 0.20/0.52  fof(f223,plain,(
% 0.20/0.52    spl7_18 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 0.20/0.52  fof(f213,plain,(
% 0.20/0.52    ~v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) | spl7_17),
% 0.20/0.52    inference(avatar_component_clause,[],[f211])).
% 0.20/0.52  fof(f211,plain,(
% 0.20/0.52    spl7_17 <=> v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).
% 0.20/0.52  fof(f236,plain,(
% 0.20/0.52    spl7_19 | ~spl7_14 | ~spl7_15),
% 0.20/0.52    inference(avatar_split_clause,[],[f194,f171,f166,f233])).
% 0.20/0.52  fof(f166,plain,(
% 0.20/0.52    spl7_14 <=> k1_relat_1(sK1) = k1_relset_1(k1_relat_1(sK1),k1_xboole_0,sK1)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 0.20/0.52  fof(f171,plain,(
% 0.20/0.52    spl7_15 <=> ! [X0] : (r2_hidden(k1_funct_1(sK1,X0),k1_xboole_0) | ~r2_hidden(X0,k1_relat_1(sK1)))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 0.20/0.52  fof(f194,plain,(
% 0.20/0.52    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK1) | (~spl7_14 | ~spl7_15)),
% 0.20/0.52    inference(backward_demodulation,[],[f168,f190])).
% 0.20/0.52  fof(f190,plain,(
% 0.20/0.52    k1_xboole_0 = k1_relat_1(sK1) | ~spl7_15),
% 0.20/0.52    inference(resolution,[],[f187,f32])).
% 0.20/0.52  fof(f32,plain,(
% 0.20/0.52    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f15])).
% 0.20/0.52  fof(f15,plain,(
% 0.20/0.52    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.20/0.52    inference(ennf_transformation,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.20/0.52  fof(f187,plain,(
% 0.20/0.52    ( ! [X4] : (r1_tarski(k1_relat_1(sK1),X4)) ) | ~spl7_15),
% 0.20/0.52    inference(resolution,[],[f179,f43])).
% 0.20/0.52  fof(f43,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f18])).
% 0.20/0.52  fof(f18,plain,(
% 0.20/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.52  fof(f179,plain,(
% 0.20/0.52    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1))) ) | ~spl7_15),
% 0.20/0.52    inference(resolution,[],[f174,f31])).
% 0.20/0.52  fof(f31,plain,(
% 0.20/0.52    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.52  fof(f174,plain,(
% 0.20/0.52    ( ! [X0] : (~r1_tarski(k1_xboole_0,k1_funct_1(sK1,X0)) | ~r2_hidden(X0,k1_relat_1(sK1))) ) | ~spl7_15),
% 0.20/0.52    inference(resolution,[],[f172,f45])).
% 0.20/0.52  fof(f45,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f19])).
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f7])).
% 0.20/0.52  fof(f7,axiom,(
% 0.20/0.52    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.20/0.52  fof(f172,plain,(
% 0.20/0.52    ( ! [X0] : (r2_hidden(k1_funct_1(sK1,X0),k1_xboole_0) | ~r2_hidden(X0,k1_relat_1(sK1))) ) | ~spl7_15),
% 0.20/0.52    inference(avatar_component_clause,[],[f171])).
% 0.20/0.52  fof(f168,plain,(
% 0.20/0.52    k1_relat_1(sK1) = k1_relset_1(k1_relat_1(sK1),k1_xboole_0,sK1) | ~spl7_14),
% 0.20/0.52    inference(avatar_component_clause,[],[f166])).
% 0.20/0.52  fof(f226,plain,(
% 0.20/0.52    spl7_18 | ~spl7_13 | ~spl7_15),
% 0.20/0.52    inference(avatar_split_clause,[],[f193,f171,f157,f223])).
% 0.20/0.52  fof(f157,plain,(
% 0.20/0.52    spl7_13 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0)))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 0.20/0.52  fof(f193,plain,(
% 0.20/0.52    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl7_13 | ~spl7_15)),
% 0.20/0.52    inference(backward_demodulation,[],[f159,f190])).
% 0.20/0.52  fof(f159,plain,(
% 0.20/0.52    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0))) | ~spl7_13),
% 0.20/0.52    inference(avatar_component_clause,[],[f157])).
% 0.20/0.52  fof(f214,plain,(
% 0.20/0.52    ~spl7_17 | spl7_11 | ~spl7_15),
% 0.20/0.52    inference(avatar_split_clause,[],[f192,f171,f142,f211])).
% 0.20/0.52  fof(f142,plain,(
% 0.20/0.52    spl7_11 <=> v1_funct_2(sK1,k1_relat_1(sK1),k1_xboole_0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.20/0.52  fof(f192,plain,(
% 0.20/0.52    ~v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) | (spl7_11 | ~spl7_15)),
% 0.20/0.52    inference(backward_demodulation,[],[f144,f190])).
% 0.20/0.52  fof(f144,plain,(
% 0.20/0.52    ~v1_funct_2(sK1,k1_relat_1(sK1),k1_xboole_0) | spl7_11),
% 0.20/0.52    inference(avatar_component_clause,[],[f142])).
% 0.20/0.52  fof(f173,plain,(
% 0.20/0.52    ~spl7_1 | ~spl7_2 | spl7_15 | ~spl7_12),
% 0.20/0.52    inference(avatar_split_clause,[],[f155,f148,f171,f84,f79])).
% 0.20/0.52  fof(f79,plain,(
% 0.20/0.52    spl7_1 <=> v1_relat_1(sK1)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.20/0.52  fof(f84,plain,(
% 0.20/0.52    spl7_2 <=> v1_funct_1(sK1)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.20/0.52  fof(f148,plain,(
% 0.20/0.52    spl7_12 <=> k1_xboole_0 = k2_relat_1(sK1)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.20/0.52  fof(f155,plain,(
% 0.20/0.52    ( ! [X0] : (r2_hidden(k1_funct_1(sK1,X0),k1_xboole_0) | ~v1_funct_1(sK1) | ~r2_hidden(X0,k1_relat_1(sK1)) | ~v1_relat_1(sK1)) ) | ~spl7_12),
% 0.20/0.52    inference(superposition,[],[f63,f150])).
% 0.20/0.52  fof(f150,plain,(
% 0.20/0.52    k1_xboole_0 = k2_relat_1(sK1) | ~spl7_12),
% 0.20/0.52    inference(avatar_component_clause,[],[f148])).
% 0.20/0.52  fof(f63,plain,(
% 0.20/0.52    ( ! [X0,X3] : (r2_hidden(k1_funct_1(X0,X3),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~r2_hidden(X3,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.52    inference(equality_resolution,[],[f62])).
% 0.20/0.53  fof(f62,plain,(
% 0.20/0.53    ( ! [X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r2_hidden(X3,k1_relat_1(X0)) | r2_hidden(k1_funct_1(X0,X3),X1) | k2_relat_1(X0) != X1) )),
% 0.20/0.53    inference(equality_resolution,[],[f38])).
% 0.20/0.53  fof(f38,plain,(
% 0.20/0.53    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r2_hidden(X3,k1_relat_1(X0)) | k1_funct_1(X0,X3) != X2 | r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.20/0.53    inference(cnf_transformation,[],[f17])).
% 0.20/0.53  fof(f17,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.53    inference(flattening,[],[f16])).
% 0.20/0.53  fof(f16,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f5])).
% 0.20/0.53  % (21345)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  fof(f5,axiom,(
% 0.20/0.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).
% 0.20/0.53  fof(f169,plain,(
% 0.20/0.53    spl7_14 | ~spl7_8 | ~spl7_9),
% 0.20/0.53    inference(avatar_split_clause,[],[f164,f122,f118,f166])).
% 0.20/0.53  fof(f118,plain,(
% 0.20/0.53    spl7_8 <=> k1_relat_1(sK1) = k1_relset_1(k1_relat_1(sK1),sK0,sK1)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.20/0.53  fof(f122,plain,(
% 0.20/0.53    spl7_9 <=> k1_xboole_0 = sK0),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.20/0.53  fof(f164,plain,(
% 0.20/0.53    k1_relat_1(sK1) = k1_relset_1(k1_relat_1(sK1),k1_xboole_0,sK1) | (~spl7_8 | ~spl7_9)),
% 0.20/0.53    inference(forward_demodulation,[],[f119,f124])).
% 0.20/0.53  fof(f124,plain,(
% 0.20/0.53    k1_xboole_0 = sK0 | ~spl7_9),
% 0.20/0.53    inference(avatar_component_clause,[],[f122])).
% 0.20/0.53  fof(f119,plain,(
% 0.20/0.53    k1_relat_1(sK1) = k1_relset_1(k1_relat_1(sK1),sK0,sK1) | ~spl7_8),
% 0.20/0.53    inference(avatar_component_clause,[],[f118])).
% 0.20/0.53  fof(f160,plain,(
% 0.20/0.53    spl7_13 | ~spl7_6 | ~spl7_9),
% 0.20/0.53    inference(avatar_split_clause,[],[f130,f122,f104,f157])).
% 0.20/0.53  fof(f104,plain,(
% 0.20/0.53    spl7_6 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.20/0.53  fof(f130,plain,(
% 0.20/0.53    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0))) | (~spl7_6 | ~spl7_9)),
% 0.20/0.53    inference(backward_demodulation,[],[f105,f124])).
% 0.20/0.53  fof(f105,plain,(
% 0.20/0.53    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | ~spl7_6),
% 0.20/0.53    inference(avatar_component_clause,[],[f104])).
% 0.20/0.53  fof(f151,plain,(
% 0.20/0.53    spl7_12 | ~spl7_10),
% 0.20/0.53    inference(avatar_split_clause,[],[f139,f135,f148])).
% 0.20/0.53  fof(f135,plain,(
% 0.20/0.53    spl7_10 <=> r1_tarski(k2_relat_1(sK1),k1_xboole_0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.20/0.53  fof(f139,plain,(
% 0.20/0.53    k1_xboole_0 = k2_relat_1(sK1) | ~spl7_10),
% 0.20/0.53    inference(resolution,[],[f137,f32])).
% 0.20/0.53  fof(f137,plain,(
% 0.20/0.53    r1_tarski(k2_relat_1(sK1),k1_xboole_0) | ~spl7_10),
% 0.20/0.53    inference(avatar_component_clause,[],[f135])).
% 0.20/0.53  fof(f145,plain,(
% 0.20/0.53    ~spl7_11 | spl7_7 | ~spl7_9),
% 0.20/0.53    inference(avatar_split_clause,[],[f131,f122,f108,f142])).
% 0.20/0.53  fof(f108,plain,(
% 0.20/0.53    spl7_7 <=> v1_funct_2(sK1,k1_relat_1(sK1),sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.20/0.53  fof(f131,plain,(
% 0.20/0.53    ~v1_funct_2(sK1,k1_relat_1(sK1),k1_xboole_0) | (spl7_7 | ~spl7_9)),
% 0.20/0.53    inference(backward_demodulation,[],[f110,f124])).
% 0.20/0.53  fof(f110,plain,(
% 0.20/0.53    ~v1_funct_2(sK1,k1_relat_1(sK1),sK0) | spl7_7),
% 0.20/0.53    inference(avatar_component_clause,[],[f108])).
% 0.20/0.53  fof(f138,plain,(
% 0.20/0.53    spl7_10 | ~spl7_3 | ~spl7_9),
% 0.20/0.53    inference(avatar_split_clause,[],[f133,f122,f89,f135])).
% 0.20/0.53  fof(f89,plain,(
% 0.20/0.53    spl7_3 <=> r1_tarski(k2_relat_1(sK1),sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.20/0.53  fof(f133,plain,(
% 0.20/0.53    r1_tarski(k2_relat_1(sK1),k1_xboole_0) | (~spl7_3 | ~spl7_9)),
% 0.20/0.53    inference(backward_demodulation,[],[f91,f124])).
% 0.20/0.53  fof(f91,plain,(
% 0.20/0.53    r1_tarski(k2_relat_1(sK1),sK0) | ~spl7_3),
% 0.20/0.53    inference(avatar_component_clause,[],[f89])).
% 0.20/0.53  fof(f129,plain,(
% 0.20/0.53    ~spl7_6 | spl7_8),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f126])).
% 0.20/0.53  fof(f126,plain,(
% 0.20/0.53    $false | (~spl7_6 | spl7_8)),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f105,f120,f55])).
% 0.20/0.53  fof(f55,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f24])).
% 0.20/0.53  fof(f24,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(ennf_transformation,[],[f8])).
% 0.20/0.53  fof(f8,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.53  fof(f120,plain,(
% 0.20/0.53    k1_relat_1(sK1) != k1_relset_1(k1_relat_1(sK1),sK0,sK1) | spl7_8),
% 0.20/0.53    inference(avatar_component_clause,[],[f118])).
% 0.20/0.53  fof(f125,plain,(
% 0.20/0.53    spl7_7 | ~spl7_8 | spl7_9 | ~spl7_6),
% 0.20/0.53    inference(avatar_split_clause,[],[f115,f104,f122,f118,f108])).
% 0.20/0.53  fof(f115,plain,(
% 0.20/0.53    k1_xboole_0 = sK0 | k1_relat_1(sK1) != k1_relset_1(k1_relat_1(sK1),sK0,sK1) | v1_funct_2(sK1,k1_relat_1(sK1),sK0) | ~spl7_6),
% 0.20/0.53    inference(resolution,[],[f105,f60])).
% 0.20/0.53  fof(f60,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f26])).
% 0.20/0.53  fof(f114,plain,(
% 0.20/0.53    ~spl7_1 | ~spl7_3 | spl7_6),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f112])).
% 0.20/0.53  fof(f112,plain,(
% 0.20/0.53    $false | (~spl7_1 | ~spl7_3 | spl7_6)),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f81,f91,f67,f106,f54])).
% 0.20/0.53  fof(f54,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k1_relat_1(X2),X0) | ~r1_tarski(k2_relat_1(X2),X1) | ~v1_relat_1(X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f23])).
% 0.20/0.53  fof(f23,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 0.20/0.53    inference(flattening,[],[f22])).
% 0.20/0.53  fof(f22,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 0.20/0.53    inference(ennf_transformation,[],[f9])).
% 0.20/0.53  fof(f9,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).
% 0.20/0.53  fof(f106,plain,(
% 0.20/0.53    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | spl7_6),
% 0.20/0.53    inference(avatar_component_clause,[],[f104])).
% 0.20/0.53  fof(f67,plain,(
% 0.20/0.53    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.53    inference(equality_resolution,[],[f39])).
% 0.20/0.53  fof(f39,plain,(
% 0.20/0.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.20/0.53    inference(cnf_transformation,[],[f2])).
% 0.20/0.53  fof(f2,axiom,(
% 0.20/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.53  fof(f81,plain,(
% 0.20/0.53    v1_relat_1(sK1) | ~spl7_1),
% 0.20/0.53    inference(avatar_component_clause,[],[f79])).
% 0.20/0.53  fof(f111,plain,(
% 0.20/0.53    ~spl7_6 | ~spl7_7),
% 0.20/0.53    inference(avatar_split_clause,[],[f77,f108,f104])).
% 0.20/0.53  fof(f77,plain,(
% 0.20/0.53    ~v1_funct_2(sK1,k1_relat_1(sK1),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))),
% 0.20/0.53    inference(global_subsumption,[],[f29,f27])).
% 0.20/0.53  fof(f27,plain,(
% 0.20/0.53    ~v1_funct_1(sK1) | ~v1_funct_2(sK1,k1_relat_1(sK1),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))),
% 0.20/0.53    inference(cnf_transformation,[],[f14])).
% 0.20/0.53  fof(f14,plain,(
% 0.20/0.53    ? [X0,X1] : ((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.20/0.53    inference(flattening,[],[f13])).
% 0.20/0.53  fof(f13,plain,(
% 0.20/0.53    ? [X0,X1] : (((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.20/0.53    inference(ennf_transformation,[],[f12])).
% 0.20/0.53  fof(f12,negated_conjecture,(
% 0.20/0.53    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 0.20/0.53    inference(negated_conjecture,[],[f11])).
% 0.20/0.53  fof(f11,conjecture,(
% 0.20/0.53    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).
% 0.20/0.53  fof(f29,plain,(
% 0.20/0.53    v1_funct_1(sK1)),
% 0.20/0.53    inference(cnf_transformation,[],[f14])).
% 0.20/0.53  fof(f92,plain,(
% 0.20/0.53    spl7_3),
% 0.20/0.53    inference(avatar_split_clause,[],[f30,f89])).
% 0.20/0.53  fof(f30,plain,(
% 0.20/0.53    r1_tarski(k2_relat_1(sK1),sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f14])).
% 0.20/0.53  fof(f87,plain,(
% 0.20/0.53    spl7_2),
% 0.20/0.53    inference(avatar_split_clause,[],[f29,f84])).
% 0.20/0.53  fof(f82,plain,(
% 0.20/0.53    spl7_1),
% 0.20/0.53    inference(avatar_split_clause,[],[f28,f79])).
% 0.20/0.53  fof(f28,plain,(
% 0.20/0.53    v1_relat_1(sK1)),
% 0.20/0.53    inference(cnf_transformation,[],[f14])).
% 0.20/0.53  % SZS output end Proof for theBenchmark
% 0.20/0.53  % (21355)------------------------------
% 0.20/0.53  % (21355)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (21355)Termination reason: Refutation
% 0.20/0.53  
% 0.20/0.53  % (21355)Memory used [KB]: 10874
% 0.20/0.53  % (21355)Time elapsed: 0.112 s
% 0.20/0.53  % (21355)------------------------------
% 0.20/0.53  % (21355)------------------------------
% 0.20/0.53  % (21343)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.53  % (21360)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.53  % (21361)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.53  % (21334)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (21349)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.53  % (21334)Refutation not found, incomplete strategy% (21334)------------------------------
% 0.20/0.53  % (21334)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (21334)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (21334)Memory used [KB]: 10746
% 0.20/0.53  % (21334)Time elapsed: 0.127 s
% 0.20/0.53  % (21334)------------------------------
% 0.20/0.53  % (21334)------------------------------
% 0.20/0.53  % (21328)Success in time 0.177 s
%------------------------------------------------------------------------------
