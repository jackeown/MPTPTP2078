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
% DateTime   : Thu Dec  3 13:00:27 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 192 expanded)
%              Number of leaves         :   26 (  81 expanded)
%              Depth                    :    9
%              Number of atoms          :  335 ( 627 expanded)
%              Number of equality atoms :   84 ( 143 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f308,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f68,f73,f74,f79,f103,f113,f119,f136,f142,f155,f170,f185,f235,f246,f276,f297,f307])).

fof(f307,plain,
    ( spl2_31
    | ~ spl2_34 ),
    inference(avatar_contradiction_clause,[],[f306])).

fof(f306,plain,
    ( $false
    | spl2_31
    | ~ spl2_34 ),
    inference(subsumption_resolution,[],[f305,f293])).

fof(f293,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl2_34 ),
    inference(avatar_component_clause,[],[f291])).

fof(f291,plain,
    ( spl2_34
  <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).

fof(f305,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | spl2_31 ),
    inference(unit_resulting_resolution,[],[f48,f275,f52])).

fof(f52,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f9])).

% (4191)Refutation not found, incomplete strategy% (4191)------------------------------
% (4191)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (4191)Termination reason: Refutation not found, incomplete strategy

% (4191)Memory used [KB]: 10618
% (4191)Time elapsed: 0.101 s
% (4191)------------------------------
% (4191)------------------------------
% (4193)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% (4190)Refutation not found, incomplete strategy% (4190)------------------------------
% (4190)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (4190)Termination reason: Refutation not found, incomplete strategy

% (4190)Memory used [KB]: 6140
% (4190)Time elapsed: 0.068 s
% (4190)------------------------------
% (4190)------------------------------
fof(f9,axiom,(
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

fof(f275,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | spl2_31 ),
    inference(avatar_component_clause,[],[f273])).

fof(f273,plain,
    ( spl2_31
  <=> v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).

fof(f48,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f297,plain,
    ( spl2_34
    | ~ spl2_14
    | ~ spl2_25 ),
    inference(avatar_split_clause,[],[f296,f230,f145,f291])).

fof(f145,plain,
    ( spl2_14
  <=> k1_relat_1(sK1) = k1_relset_1(k1_relat_1(sK1),k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f230,plain,
    ( spl2_25
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).

fof(f296,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl2_14
    | ~ spl2_25 ),
    inference(forward_demodulation,[],[f295,f42])).

fof(f42,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f295,plain,
    ( k1_relat_1(k1_xboole_0) = k1_relset_1(k1_relat_1(k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | ~ spl2_14
    | ~ spl2_25 ),
    inference(forward_demodulation,[],[f147,f232])).

fof(f232,plain,
    ( k1_xboole_0 = sK1
    | ~ spl2_25 ),
    inference(avatar_component_clause,[],[f230])).

fof(f147,plain,
    ( k1_relat_1(sK1) = k1_relset_1(k1_relat_1(sK1),k1_xboole_0,sK1)
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f145])).

fof(f276,plain,
    ( ~ spl2_31
    | spl2_19
    | ~ spl2_25 ),
    inference(avatar_split_clause,[],[f271,f230,f182,f273])).

fof(f182,plain,
    ( spl2_19
  <=> v1_funct_2(sK1,k1_relat_1(sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f271,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | spl2_19
    | ~ spl2_25 ),
    inference(forward_demodulation,[],[f251,f42])).

fof(f251,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | spl2_19
    | ~ spl2_25 ),
    inference(backward_demodulation,[],[f184,f232])).

fof(f184,plain,
    ( ~ v1_funct_2(sK1,k1_relat_1(sK1),k1_xboole_0)
    | spl2_19 ),
    inference(avatar_component_clause,[],[f182])).

fof(f246,plain,
    ( spl2_14
    | ~ spl2_12
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f156,f139,f132,f145])).

fof(f132,plain,
    ( spl2_12
  <=> k1_relat_1(sK1) = k1_relset_1(k1_relat_1(sK1),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f139,plain,
    ( spl2_13
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f156,plain,
    ( k1_relat_1(sK1) = k1_relset_1(k1_relat_1(sK1),k1_xboole_0,sK1)
    | ~ spl2_12
    | ~ spl2_13 ),
    inference(forward_demodulation,[],[f134,f141])).

fof(f141,plain,
    ( k1_xboole_0 = sK0
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f139])).

fof(f134,plain,
    ( k1_relat_1(sK1) = k1_relset_1(k1_relat_1(sK1),sK0,sK1)
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f132])).

fof(f235,plain,
    ( spl2_25
    | ~ spl2_5
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f234,f159,f76,f230])).

fof(f76,plain,
    ( spl2_5
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f159,plain,
    ( spl2_15
  <=> k1_xboole_0 = k2_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f234,plain,
    ( k1_xboole_0 = sK1
    | ~ spl2_5
    | ~ spl2_15 ),
    inference(subsumption_resolution,[],[f228,f78])).

fof(f78,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f76])).

fof(f228,plain,
    ( k1_xboole_0 = sK1
    | ~ v1_relat_1(sK1)
    | ~ spl2_15 ),
    inference(trivial_inequality_removal,[],[f227])).

fof(f227,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK1
    | ~ v1_relat_1(sK1)
    | ~ spl2_15 ),
    inference(superposition,[],[f46,f161])).

fof(f161,plain,
    ( k1_xboole_0 = k2_relat_1(sK1)
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f159])).

fof(f46,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_relat_1(X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f185,plain,
    ( ~ spl2_19
    | spl2_2
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f152,f139,f61,f182])).

fof(f61,plain,
    ( spl2_2
  <=> v1_funct_2(sK1,k1_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f152,plain,
    ( ~ v1_funct_2(sK1,k1_relat_1(sK1),k1_xboole_0)
    | spl2_2
    | ~ spl2_13 ),
    inference(backward_demodulation,[],[f63,f141])).

fof(f63,plain,
    ( ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f61])).

fof(f170,plain,
    ( spl2_15
    | ~ spl2_8
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f169,f139,f105,f159])).

fof(f105,plain,
    ( spl2_8
  <=> sK0 = k2_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f169,plain,
    ( k1_xboole_0 = k2_relat_1(sK1)
    | ~ spl2_8
    | ~ spl2_13 ),
    inference(forward_demodulation,[],[f107,f141])).

fof(f107,plain,
    ( sK0 = k2_relat_1(sK1)
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f105])).

fof(f155,plain,
    ( spl2_10
    | ~ spl2_13 ),
    inference(avatar_contradiction_clause,[],[f154])).

fof(f154,plain,
    ( $false
    | spl2_10
    | ~ spl2_13 ),
    inference(subsumption_resolution,[],[f148,f48])).

fof(f148,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_relat_1(sK1)))
    | spl2_10
    | ~ spl2_13 ),
    inference(backward_demodulation,[],[f118,f141])).

fof(f118,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_relat_1(sK1)))
    | spl2_10 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl2_10
  <=> m1_subset_1(sK0,k1_zfmisc_1(k2_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f142,plain,
    ( spl2_13
    | ~ spl2_12
    | spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f137,f65,f61,f132,f139])).

fof(f65,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f137,plain,
    ( k1_relat_1(sK1) != k1_relset_1(k1_relat_1(sK1),sK0,sK1)
    | k1_xboole_0 = sK0
    | spl2_2
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f124,f63])).

fof(f124,plain,
    ( k1_relat_1(sK1) != k1_relset_1(k1_relat_1(sK1),sK0,sK1)
    | k1_xboole_0 = sK0
    | v1_funct_2(sK1,k1_relat_1(sK1),sK0)
    | ~ spl2_3 ),
    inference(resolution,[],[f66,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f66,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f65])).

fof(f136,plain,
    ( spl2_12
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f122,f65,f132])).

fof(f122,plain,
    ( k1_relat_1(sK1) = k1_relset_1(k1_relat_1(sK1),sK0,sK1)
    | ~ spl2_3 ),
    inference(resolution,[],[f66,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f119,plain,
    ( ~ spl2_10
    | spl2_9 ),
    inference(avatar_split_clause,[],[f114,f109,f116])).

fof(f109,plain,
    ( spl2_9
  <=> r1_tarski(sK0,k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f114,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_relat_1(sK1)))
    | spl2_9 ),
    inference(unit_resulting_resolution,[],[f111,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f111,plain,
    ( ~ r1_tarski(sK0,k2_relat_1(sK1))
    | spl2_9 ),
    inference(avatar_component_clause,[],[f109])).

fof(f113,plain,
    ( spl2_8
    | ~ spl2_9
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f96,f70,f109,f105])).

fof(f70,plain,
    ( spl2_4
  <=> r1_tarski(k2_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f96,plain,
    ( ~ r1_tarski(sK0,k2_relat_1(sK1))
    | sK0 = k2_relat_1(sK1)
    | ~ spl2_4 ),
    inference(resolution,[],[f72,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f72,plain,
    ( r1_tarski(k2_relat_1(sK1),sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f70])).

fof(f103,plain,
    ( spl2_3
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f92,f76,f70,f65])).

fof(f92,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(unit_resulting_resolution,[],[f78,f55,f72,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(f55,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f79,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f27,f76])).

fof(f27,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
      | ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
      | ~ v1_funct_1(sK1) )
    & r1_tarski(k2_relat_1(sK1),sK0)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f21])).

fof(f21,plain,
    ( ? [X0,X1] :
        ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
          | ~ v1_funct_1(X1) )
        & r1_tarski(k2_relat_1(X1),X0)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
        | ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
        | ~ v1_funct_1(sK1) )
      & r1_tarski(k2_relat_1(sK1),sK0)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
        | ~ v1_funct_1(X1) )
      & r1_tarski(k2_relat_1(X1),X0)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
        | ~ v1_funct_1(X1) )
      & r1_tarski(k2_relat_1(X1),X0)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( r1_tarski(k2_relat_1(X1),X0)
         => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
            & v1_funct_2(X1,k1_relat_1(X1),X0)
            & v1_funct_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

fof(f74,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f28,f57])).

fof(f57,plain,
    ( spl2_1
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f28,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f73,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f29,f70])).

fof(f29,plain,(
    r1_tarski(k2_relat_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f68,plain,
    ( ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f30,f65,f61,f57])).

fof(f30,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
    | ~ v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:23:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (4194)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.47  % (4209)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.49  % (4206)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.50  % (4199)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.50  % (4198)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.50  % (4185)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.50  % (4186)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.50  % (4190)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.50  % (4191)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.50  % (4192)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.50  % (4189)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.50  % (4198)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f308,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(avatar_sat_refutation,[],[f68,f73,f74,f79,f103,f113,f119,f136,f142,f155,f170,f185,f235,f246,f276,f297,f307])).
% 0.20/0.50  fof(f307,plain,(
% 0.20/0.50    spl2_31 | ~spl2_34),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f306])).
% 0.20/0.50  fof(f306,plain,(
% 0.20/0.50    $false | (spl2_31 | ~spl2_34)),
% 0.20/0.50    inference(subsumption_resolution,[],[f305,f293])).
% 0.20/0.50  fof(f293,plain,(
% 0.20/0.50    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~spl2_34),
% 0.20/0.50    inference(avatar_component_clause,[],[f291])).
% 0.20/0.50  fof(f291,plain,(
% 0.20/0.50    spl2_34 <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).
% 0.20/0.50  fof(f305,plain,(
% 0.20/0.50    k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | spl2_31),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f48,f275,f52])).
% 0.20/0.50  fof(f52,plain,(
% 0.20/0.50    ( ! [X2,X1] : (k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 0.20/0.50    inference(equality_resolution,[],[f34])).
% 0.20/0.50  fof(f34,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f23])).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(nnf_transformation,[],[f15])).
% 0.20/0.50  fof(f15,plain,(
% 0.20/0.50    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(flattening,[],[f14])).
% 0.20/0.50  fof(f14,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(ennf_transformation,[],[f9])).
% 0.20/0.50  % (4191)Refutation not found, incomplete strategy% (4191)------------------------------
% 0.20/0.50  % (4191)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (4191)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (4191)Memory used [KB]: 10618
% 0.20/0.50  % (4191)Time elapsed: 0.101 s
% 0.20/0.50  % (4191)------------------------------
% 0.20/0.50  % (4191)------------------------------
% 0.20/0.50  % (4193)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.50  % (4190)Refutation not found, incomplete strategy% (4190)------------------------------
% 0.20/0.50  % (4190)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (4190)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (4190)Memory used [KB]: 6140
% 0.20/0.50  % (4190)Time elapsed: 0.068 s
% 0.20/0.50  % (4190)------------------------------
% 0.20/0.50  % (4190)------------------------------
% 0.20/0.50  fof(f9,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.50  fof(f275,plain,(
% 0.20/0.50    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | spl2_31),
% 0.20/0.50    inference(avatar_component_clause,[],[f273])).
% 0.20/0.50  fof(f273,plain,(
% 0.20/0.50    spl2_31 <=> v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).
% 0.20/0.50  fof(f48,plain,(
% 0.20/0.50    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.20/0.50  fof(f297,plain,(
% 0.20/0.50    spl2_34 | ~spl2_14 | ~spl2_25),
% 0.20/0.50    inference(avatar_split_clause,[],[f296,f230,f145,f291])).
% 0.20/0.50  fof(f145,plain,(
% 0.20/0.50    spl2_14 <=> k1_relat_1(sK1) = k1_relset_1(k1_relat_1(sK1),k1_xboole_0,sK1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.20/0.50  fof(f230,plain,(
% 0.20/0.50    spl2_25 <=> k1_xboole_0 = sK1),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).
% 0.20/0.50  fof(f296,plain,(
% 0.20/0.50    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl2_14 | ~spl2_25)),
% 0.20/0.50    inference(forward_demodulation,[],[f295,f42])).
% 0.20/0.50  fof(f42,plain,(
% 0.20/0.50    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.50    inference(cnf_transformation,[],[f5])).
% 0.20/0.50  fof(f5,axiom,(
% 0.20/0.50    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.20/0.50  fof(f295,plain,(
% 0.20/0.50    k1_relat_1(k1_xboole_0) = k1_relset_1(k1_relat_1(k1_xboole_0),k1_xboole_0,k1_xboole_0) | (~spl2_14 | ~spl2_25)),
% 0.20/0.50    inference(forward_demodulation,[],[f147,f232])).
% 0.20/0.50  fof(f232,plain,(
% 0.20/0.50    k1_xboole_0 = sK1 | ~spl2_25),
% 0.20/0.50    inference(avatar_component_clause,[],[f230])).
% 0.20/0.50  fof(f147,plain,(
% 0.20/0.50    k1_relat_1(sK1) = k1_relset_1(k1_relat_1(sK1),k1_xboole_0,sK1) | ~spl2_14),
% 0.20/0.50    inference(avatar_component_clause,[],[f145])).
% 0.20/0.50  fof(f276,plain,(
% 0.20/0.50    ~spl2_31 | spl2_19 | ~spl2_25),
% 0.20/0.50    inference(avatar_split_clause,[],[f271,f230,f182,f273])).
% 0.20/0.50  fof(f182,plain,(
% 0.20/0.50    spl2_19 <=> v1_funct_2(sK1,k1_relat_1(sK1),k1_xboole_0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 0.20/0.50  fof(f271,plain,(
% 0.20/0.50    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (spl2_19 | ~spl2_25)),
% 0.20/0.50    inference(forward_demodulation,[],[f251,f42])).
% 0.20/0.50  fof(f251,plain,(
% 0.20/0.50    ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) | (spl2_19 | ~spl2_25)),
% 0.20/0.50    inference(backward_demodulation,[],[f184,f232])).
% 0.20/0.50  fof(f184,plain,(
% 0.20/0.50    ~v1_funct_2(sK1,k1_relat_1(sK1),k1_xboole_0) | spl2_19),
% 0.20/0.50    inference(avatar_component_clause,[],[f182])).
% 0.20/0.50  fof(f246,plain,(
% 0.20/0.50    spl2_14 | ~spl2_12 | ~spl2_13),
% 0.20/0.50    inference(avatar_split_clause,[],[f156,f139,f132,f145])).
% 0.20/0.50  fof(f132,plain,(
% 0.20/0.50    spl2_12 <=> k1_relat_1(sK1) = k1_relset_1(k1_relat_1(sK1),sK0,sK1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.20/0.50  fof(f139,plain,(
% 0.20/0.50    spl2_13 <=> k1_xboole_0 = sK0),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.20/0.50  fof(f156,plain,(
% 0.20/0.50    k1_relat_1(sK1) = k1_relset_1(k1_relat_1(sK1),k1_xboole_0,sK1) | (~spl2_12 | ~spl2_13)),
% 0.20/0.50    inference(forward_demodulation,[],[f134,f141])).
% 0.20/0.50  fof(f141,plain,(
% 0.20/0.50    k1_xboole_0 = sK0 | ~spl2_13),
% 0.20/0.50    inference(avatar_component_clause,[],[f139])).
% 0.20/0.50  fof(f134,plain,(
% 0.20/0.50    k1_relat_1(sK1) = k1_relset_1(k1_relat_1(sK1),sK0,sK1) | ~spl2_12),
% 0.20/0.50    inference(avatar_component_clause,[],[f132])).
% 0.20/0.50  fof(f235,plain,(
% 0.20/0.50    spl2_25 | ~spl2_5 | ~spl2_15),
% 0.20/0.50    inference(avatar_split_clause,[],[f234,f159,f76,f230])).
% 0.20/0.50  fof(f76,plain,(
% 0.20/0.50    spl2_5 <=> v1_relat_1(sK1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.20/0.50  fof(f159,plain,(
% 0.20/0.50    spl2_15 <=> k1_xboole_0 = k2_relat_1(sK1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.20/0.50  fof(f234,plain,(
% 0.20/0.50    k1_xboole_0 = sK1 | (~spl2_5 | ~spl2_15)),
% 0.20/0.50    inference(subsumption_resolution,[],[f228,f78])).
% 0.20/0.50  fof(f78,plain,(
% 0.20/0.50    v1_relat_1(sK1) | ~spl2_5),
% 0.20/0.50    inference(avatar_component_clause,[],[f76])).
% 0.20/0.50  fof(f228,plain,(
% 0.20/0.50    k1_xboole_0 = sK1 | ~v1_relat_1(sK1) | ~spl2_15),
% 0.20/0.50    inference(trivial_inequality_removal,[],[f227])).
% 0.20/0.50  fof(f227,plain,(
% 0.20/0.50    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK1 | ~v1_relat_1(sK1) | ~spl2_15),
% 0.20/0.50    inference(superposition,[],[f46,f161])).
% 0.20/0.50  fof(f161,plain,(
% 0.20/0.50    k1_xboole_0 = k2_relat_1(sK1) | ~spl2_15),
% 0.20/0.50    inference(avatar_component_clause,[],[f159])).
% 0.20/0.50  fof(f46,plain,(
% 0.20/0.50    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f19])).
% 0.20/0.50  fof(f19,plain,(
% 0.20/0.50    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(flattening,[],[f18])).
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f6])).
% 0.20/0.50  fof(f6,axiom,(
% 0.20/0.50    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 0.20/0.50  fof(f185,plain,(
% 0.20/0.50    ~spl2_19 | spl2_2 | ~spl2_13),
% 0.20/0.50    inference(avatar_split_clause,[],[f152,f139,f61,f182])).
% 0.20/0.50  fof(f61,plain,(
% 0.20/0.50    spl2_2 <=> v1_funct_2(sK1,k1_relat_1(sK1),sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.50  fof(f152,plain,(
% 0.20/0.50    ~v1_funct_2(sK1,k1_relat_1(sK1),k1_xboole_0) | (spl2_2 | ~spl2_13)),
% 0.20/0.50    inference(backward_demodulation,[],[f63,f141])).
% 0.20/0.50  fof(f63,plain,(
% 0.20/0.50    ~v1_funct_2(sK1,k1_relat_1(sK1),sK0) | spl2_2),
% 0.20/0.50    inference(avatar_component_clause,[],[f61])).
% 0.20/0.50  fof(f170,plain,(
% 0.20/0.50    spl2_15 | ~spl2_8 | ~spl2_13),
% 0.20/0.50    inference(avatar_split_clause,[],[f169,f139,f105,f159])).
% 0.20/0.50  fof(f105,plain,(
% 0.20/0.50    spl2_8 <=> sK0 = k2_relat_1(sK1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.20/0.50  fof(f169,plain,(
% 0.20/0.50    k1_xboole_0 = k2_relat_1(sK1) | (~spl2_8 | ~spl2_13)),
% 0.20/0.50    inference(forward_demodulation,[],[f107,f141])).
% 0.20/0.50  fof(f107,plain,(
% 0.20/0.50    sK0 = k2_relat_1(sK1) | ~spl2_8),
% 0.20/0.50    inference(avatar_component_clause,[],[f105])).
% 0.20/0.50  fof(f155,plain,(
% 0.20/0.50    spl2_10 | ~spl2_13),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f154])).
% 0.20/0.50  fof(f154,plain,(
% 0.20/0.50    $false | (spl2_10 | ~spl2_13)),
% 0.20/0.50    inference(subsumption_resolution,[],[f148,f48])).
% 0.20/0.50  fof(f148,plain,(
% 0.20/0.50    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_relat_1(sK1))) | (spl2_10 | ~spl2_13)),
% 0.20/0.50    inference(backward_demodulation,[],[f118,f141])).
% 0.20/0.50  fof(f118,plain,(
% 0.20/0.50    ~m1_subset_1(sK0,k1_zfmisc_1(k2_relat_1(sK1))) | spl2_10),
% 0.20/0.50    inference(avatar_component_clause,[],[f116])).
% 0.20/0.50  fof(f116,plain,(
% 0.20/0.50    spl2_10 <=> m1_subset_1(sK0,k1_zfmisc_1(k2_relat_1(sK1)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.20/0.50  fof(f142,plain,(
% 0.20/0.50    spl2_13 | ~spl2_12 | spl2_2 | ~spl2_3),
% 0.20/0.50    inference(avatar_split_clause,[],[f137,f65,f61,f132,f139])).
% 0.20/0.50  fof(f65,plain,(
% 0.20/0.50    spl2_3 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.20/0.51  fof(f137,plain,(
% 0.20/0.51    k1_relat_1(sK1) != k1_relset_1(k1_relat_1(sK1),sK0,sK1) | k1_xboole_0 = sK0 | (spl2_2 | ~spl2_3)),
% 0.20/0.51    inference(subsumption_resolution,[],[f124,f63])).
% 0.20/0.51  fof(f124,plain,(
% 0.20/0.51    k1_relat_1(sK1) != k1_relset_1(k1_relat_1(sK1),sK0,sK1) | k1_xboole_0 = sK0 | v1_funct_2(sK1,k1_relat_1(sK1),sK0) | ~spl2_3),
% 0.20/0.51    inference(resolution,[],[f66,f33])).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | v1_funct_2(X2,X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f23])).
% 0.20/0.51  fof(f66,plain,(
% 0.20/0.51    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | ~spl2_3),
% 0.20/0.51    inference(avatar_component_clause,[],[f65])).
% 0.20/0.51  fof(f136,plain,(
% 0.20/0.51    spl2_12 | ~spl2_3),
% 0.20/0.51    inference(avatar_split_clause,[],[f122,f65,f132])).
% 0.20/0.51  fof(f122,plain,(
% 0.20/0.51    k1_relat_1(sK1) = k1_relset_1(k1_relat_1(sK1),sK0,sK1) | ~spl2_3),
% 0.20/0.51    inference(resolution,[],[f66,f47])).
% 0.20/0.51  fof(f47,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f20])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.51    inference(ennf_transformation,[],[f7])).
% 0.20/0.51  fof(f7,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.51  fof(f119,plain,(
% 0.20/0.51    ~spl2_10 | spl2_9),
% 0.20/0.51    inference(avatar_split_clause,[],[f114,f109,f116])).
% 0.20/0.51  fof(f109,plain,(
% 0.20/0.51    spl2_9 <=> r1_tarski(sK0,k2_relat_1(sK1))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.20/0.51  fof(f114,plain,(
% 0.20/0.51    ~m1_subset_1(sK0,k1_zfmisc_1(k2_relat_1(sK1))) | spl2_9),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f111,f37])).
% 0.20/0.51  fof(f37,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f24])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.20/0.51    inference(nnf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.51  fof(f111,plain,(
% 0.20/0.51    ~r1_tarski(sK0,k2_relat_1(sK1)) | spl2_9),
% 0.20/0.51    inference(avatar_component_clause,[],[f109])).
% 0.20/0.51  fof(f113,plain,(
% 0.20/0.51    spl2_8 | ~spl2_9 | ~spl2_4),
% 0.20/0.51    inference(avatar_split_clause,[],[f96,f70,f109,f105])).
% 0.20/0.51  fof(f70,plain,(
% 0.20/0.51    spl2_4 <=> r1_tarski(k2_relat_1(sK1),sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.20/0.51  fof(f96,plain,(
% 0.20/0.51    ~r1_tarski(sK0,k2_relat_1(sK1)) | sK0 = k2_relat_1(sK1) | ~spl2_4),
% 0.20/0.51    inference(resolution,[],[f72,f41])).
% 0.20/0.51  fof(f41,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.20/0.51    inference(cnf_transformation,[],[f26])).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.51    inference(flattening,[],[f25])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.51    inference(nnf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.51  fof(f72,plain,(
% 0.20/0.51    r1_tarski(k2_relat_1(sK1),sK0) | ~spl2_4),
% 0.20/0.51    inference(avatar_component_clause,[],[f70])).
% 0.20/0.51  fof(f103,plain,(
% 0.20/0.51    spl2_3 | ~spl2_4 | ~spl2_5),
% 0.20/0.51    inference(avatar_split_clause,[],[f92,f76,f70,f65])).
% 0.20/0.51  fof(f92,plain,(
% 0.20/0.51    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | (~spl2_4 | ~spl2_5)),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f78,f55,f72,f44])).
% 0.20/0.51  fof(f44,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f17])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 0.20/0.51    inference(flattening,[],[f16])).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 0.20/0.51    inference(ennf_transformation,[],[f8])).
% 0.20/0.51  fof(f8,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).
% 0.20/0.51  fof(f55,plain,(
% 0.20/0.51    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.51    inference(equality_resolution,[],[f39])).
% 0.20/0.51  fof(f39,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.20/0.51    inference(cnf_transformation,[],[f26])).
% 0.20/0.51  fof(f79,plain,(
% 0.20/0.51    spl2_5),
% 0.20/0.51    inference(avatar_split_clause,[],[f27,f76])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    v1_relat_1(sK1)),
% 0.20/0.51    inference(cnf_transformation,[],[f22])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | ~v1_funct_2(sK1,k1_relat_1(sK1),sK0) | ~v1_funct_1(sK1)) & r1_tarski(k2_relat_1(sK1),sK0) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f21])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    ? [X0,X1] : ((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0) & v1_funct_1(X1) & v1_relat_1(X1)) => ((~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | ~v1_funct_2(sK1,k1_relat_1(sK1),sK0) | ~v1_funct_1(sK1)) & r1_tarski(k2_relat_1(sK1),sK0) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f13,plain,(
% 0.20/0.51    ? [X0,X1] : ((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.20/0.51    inference(flattening,[],[f12])).
% 0.20/0.51  fof(f12,plain,(
% 0.20/0.51    ? [X0,X1] : (((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.20/0.51    inference(ennf_transformation,[],[f11])).
% 0.20/0.51  fof(f11,negated_conjecture,(
% 0.20/0.51    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 0.20/0.51    inference(negated_conjecture,[],[f10])).
% 0.20/0.51  fof(f10,conjecture,(
% 0.20/0.51    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).
% 0.20/0.51  fof(f74,plain,(
% 0.20/0.51    spl2_1),
% 0.20/0.51    inference(avatar_split_clause,[],[f28,f57])).
% 0.20/0.51  fof(f57,plain,(
% 0.20/0.51    spl2_1 <=> v1_funct_1(sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    v1_funct_1(sK1)),
% 0.20/0.51    inference(cnf_transformation,[],[f22])).
% 0.20/0.51  fof(f73,plain,(
% 0.20/0.51    spl2_4),
% 0.20/0.51    inference(avatar_split_clause,[],[f29,f70])).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    r1_tarski(k2_relat_1(sK1),sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f22])).
% 0.20/0.51  fof(f68,plain,(
% 0.20/0.51    ~spl2_1 | ~spl2_2 | ~spl2_3),
% 0.20/0.51    inference(avatar_split_clause,[],[f30,f65,f61,f57])).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | ~v1_funct_2(sK1,k1_relat_1(sK1),sK0) | ~v1_funct_1(sK1)),
% 0.20/0.51    inference(cnf_transformation,[],[f22])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (4198)------------------------------
% 0.20/0.51  % (4198)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (4198)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (4198)Memory used [KB]: 6268
% 0.20/0.51  % (4198)Time elapsed: 0.060 s
% 0.20/0.51  % (4198)------------------------------
% 0.20/0.51  % (4198)------------------------------
% 0.20/0.51  % (4184)Success in time 0.156 s
%------------------------------------------------------------------------------
