%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:45 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  184 ( 347 expanded)
%              Number of leaves         :   38 ( 138 expanded)
%              Depth                    :   12
%              Number of atoms          :  548 (1076 expanded)
%              Number of equality atoms :  102 ( 266 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f633,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f79,f84,f96,f101,f113,f122,f134,f145,f177,f204,f215,f264,f283,f293,f382,f404,f419,f431,f465,f471,f476,f564,f569,f585,f600,f628,f632])).

% (22693)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
fof(f632,plain,
    ( ~ spl4_2
    | ~ spl4_22
    | spl4_38 ),
    inference(avatar_contradiction_clause,[],[f631])).

fof(f631,plain,
    ( $false
    | ~ spl4_2
    | ~ spl4_22
    | spl4_38 ),
    inference(subsumption_resolution,[],[f605,f531])).

fof(f531,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK2)
    | spl4_38 ),
    inference(avatar_component_clause,[],[f530])).

fof(f530,plain,
    ( spl4_38
  <=> r1_tarski(k2_relat_1(sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f605,plain,
    ( r1_tarski(k2_relat_1(sK3),sK2)
    | ~ spl4_2
    | ~ spl4_22 ),
    inference(resolution,[],[f287,f78])).

fof(f78,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl4_2
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f287,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK1,X0)
        | r1_tarski(k2_relat_1(sK3),X0) )
    | ~ spl4_22 ),
    inference(resolution,[],[f282,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
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

fof(f282,plain,
    ( r1_tarski(k2_relat_1(sK3),sK1)
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f280])).

fof(f280,plain,
    ( spl4_22
  <=> r1_tarski(k2_relat_1(sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f628,plain,
    ( ~ spl4_8
    | spl4_9
    | ~ spl4_18
    | ~ spl4_23
    | ~ spl4_38 ),
    inference(avatar_contradiction_clause,[],[f627])).

fof(f627,plain,
    ( $false
    | ~ spl4_8
    | spl4_9
    | ~ spl4_18
    | ~ spl4_23
    | ~ spl4_38 ),
    inference(subsumption_resolution,[],[f626,f117])).

fof(f117,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | spl4_9 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl4_9
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f626,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl4_8
    | ~ spl4_18
    | ~ spl4_23
    | ~ spl4_38 ),
    inference(resolution,[],[f609,f532])).

fof(f532,plain,
    ( r1_tarski(k2_relat_1(sK3),sK2)
    | ~ spl4_38 ),
    inference(avatar_component_clause,[],[f530])).

fof(f609,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(sK3),X0)
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) )
    | ~ spl4_8
    | ~ spl4_18
    | ~ spl4_23 ),
    inference(resolution,[],[f607,f292])).

fof(f292,plain,
    ( r1_tarski(sK0,sK0)
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f290])).

fof(f290,plain,
    ( spl4_23
  <=> r1_tarski(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f607,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(sK0,X0)
        | ~ r1_tarski(k2_relat_1(sK3),X1)
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl4_8
    | ~ spl4_18 ),
    inference(forward_demodulation,[],[f123,f214])).

fof(f214,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f212])).

fof(f212,plain,
    ( spl4_18
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f123,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k1_relat_1(sK3),X0)
        | ~ r1_tarski(k2_relat_1(sK3),X1)
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl4_8 ),
    inference(resolution,[],[f112,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

fof(f112,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl4_8
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f600,plain,
    ( spl4_31
    | ~ spl4_33 ),
    inference(avatar_contradiction_clause,[],[f599])).

fof(f599,plain,
    ( $false
    | spl4_31
    | ~ spl4_33 ),
    inference(subsumption_resolution,[],[f598,f38])).

fof(f38,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f598,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | spl4_31
    | ~ spl4_33 ),
    inference(subsumption_resolution,[],[f593,f418])).

fof(f418,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | spl4_31 ),
    inference(avatar_component_clause,[],[f416])).

fof(f416,plain,
    ( spl4_31
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f593,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl4_33 ),
    inference(superposition,[],[f51,f435])).

fof(f435,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,k1_xboole_0)
    | ~ spl4_33 ),
    inference(avatar_component_clause,[],[f433])).

fof(f433,plain,
    ( spl4_33
  <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f585,plain,
    ( spl4_33
    | ~ spl4_35 ),
    inference(avatar_split_clause,[],[f484,f468,f433])).

fof(f468,plain,
    ( spl4_35
  <=> v1_funct_2(k1_xboole_0,k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f484,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,k1_xboole_0)
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f482,f38])).

fof(f482,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl4_35 ),
    inference(resolution,[],[f470,f64])).

fof(f64,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

% (22682)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
fof(f27,plain,(
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
    inference(flattening,[],[f26])).

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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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

fof(f470,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,sK1)
    | ~ spl4_35 ),
    inference(avatar_component_clause,[],[f468])).

fof(f569,plain,
    ( ~ spl4_9
    | ~ spl4_18
    | spl4_41 ),
    inference(avatar_contradiction_clause,[],[f568])).

fof(f568,plain,
    ( $false
    | ~ spl4_9
    | ~ spl4_18
    | spl4_41 ),
    inference(subsumption_resolution,[],[f567,f116])).

fof(f116,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f115])).

fof(f567,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl4_18
    | spl4_41 ),
    inference(subsumption_resolution,[],[f566,f214])).

fof(f566,plain,
    ( sK0 != k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | spl4_41 ),
    inference(superposition,[],[f563,f51])).

fof(f563,plain,
    ( sK0 != k1_relset_1(sK0,sK2,sK3)
    | spl4_41 ),
    inference(avatar_component_clause,[],[f561])).

fof(f561,plain,
    ( spl4_41
  <=> sK0 = k1_relset_1(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).

fof(f564,plain,
    ( ~ spl4_41
    | ~ spl4_9
    | spl4_10
    | spl4_28 ),
    inference(avatar_split_clause,[],[f554,f397,f119,f115,f561])).

fof(f119,plain,
    ( spl4_10
  <=> v1_funct_2(sK3,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f397,plain,
    ( spl4_28
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f554,plain,
    ( sK0 != k1_relset_1(sK0,sK2,sK3)
    | ~ spl4_9
    | spl4_10
    | spl4_28 ),
    inference(subsumption_resolution,[],[f513,f116])).

fof(f513,plain,
    ( sK0 != k1_relset_1(sK0,sK2,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | spl4_10
    | spl4_28 ),
    inference(subsumption_resolution,[],[f128,f398])).

fof(f398,plain,
    ( k1_xboole_0 != sK2
    | spl4_28 ),
    inference(avatar_component_clause,[],[f397])).

fof(f128,plain,
    ( k1_xboole_0 = sK2
    | sK0 != k1_relset_1(sK0,sK2,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | spl4_10 ),
    inference(resolution,[],[f121,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f121,plain,
    ( ~ v1_funct_2(sK3,sK0,sK2)
    | spl4_10 ),
    inference(avatar_component_clause,[],[f119])).

fof(f476,plain,
    ( spl4_5
    | ~ spl4_34 ),
    inference(avatar_contradiction_clause,[],[f475])).

fof(f475,plain,
    ( $false
    | spl4_5
    | ~ spl4_34 ),
    inference(subsumption_resolution,[],[f472,f95])).

fof(f95,plain,
    ( k1_xboole_0 != sK1
    | spl4_5 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl4_5
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f472,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_34 ),
    inference(resolution,[],[f464,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f464,plain,
    ( r1_tarski(sK1,k1_xboole_0)
    | ~ spl4_34 ),
    inference(avatar_component_clause,[],[f462])).

fof(f462,plain,
    ( spl4_34
  <=> r1_tarski(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f471,plain,
    ( spl4_35
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_17 ),
    inference(avatar_split_clause,[],[f438,f201,f89,f81,f468])).

fof(f81,plain,
    ( spl4_3
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f89,plain,
    ( spl4_4
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f201,plain,
    ( spl4_17
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f438,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,sK1)
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_17 ),
    inference(forward_demodulation,[],[f303,f203])).

fof(f203,plain,
    ( k1_xboole_0 = sK3
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f201])).

fof(f303,plain,
    ( v1_funct_2(sK3,k1_xboole_0,sK1)
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(superposition,[],[f83,f91])).

fof(f91,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f89])).

fof(f83,plain,
    ( v1_funct_2(sK3,sK0,sK1)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f81])).

fof(f465,plain,
    ( spl4_34
    | ~ spl4_2
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f449,f397,f76,f462])).

fof(f449,plain,
    ( r1_tarski(sK1,k1_xboole_0)
    | ~ spl4_2
    | ~ spl4_28 ),
    inference(superposition,[],[f78,f399])).

fof(f399,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f397])).

fof(f431,plain,
    ( k1_xboole_0 != sK3
    | k1_xboole_0 != sK0
    | k1_xboole_0 != sK2
    | v1_funct_2(sK3,sK0,sK2)
    | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f419,plain,
    ( ~ spl4_31
    | spl4_29 ),
    inference(avatar_split_clause,[],[f411,f401,f416])).

fof(f401,plain,
    ( spl4_29
  <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f411,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | spl4_29 ),
    inference(subsumption_resolution,[],[f410,f38])).

fof(f410,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
    | spl4_29 ),
    inference(superposition,[],[f403,f51])).

fof(f403,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,sK2,k1_xboole_0)
    | spl4_29 ),
    inference(avatar_component_clause,[],[f401])).

fof(f404,plain,
    ( spl4_28
    | ~ spl4_29
    | ~ spl4_4
    | spl4_10
    | ~ spl4_17 ),
    inference(avatar_split_clause,[],[f394,f201,f119,f89,f401,f397])).

fof(f394,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,sK2,k1_xboole_0)
    | k1_xboole_0 = sK2
    | ~ spl4_4
    | spl4_10
    | ~ spl4_17 ),
    inference(subsumption_resolution,[],[f393,f38])).

fof(f393,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 != k1_relset_1(k1_xboole_0,sK2,k1_xboole_0)
    | k1_xboole_0 = sK2
    | ~ spl4_4
    | spl4_10
    | ~ spl4_17 ),
    inference(forward_demodulation,[],[f392,f203])).

fof(f392,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 != k1_relset_1(k1_xboole_0,sK2,k1_xboole_0)
    | k1_xboole_0 = sK2
    | ~ spl4_4
    | spl4_10
    | ~ spl4_17 ),
    inference(forward_demodulation,[],[f391,f63])).

fof(f63,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f391,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
    | k1_xboole_0 != k1_relset_1(k1_xboole_0,sK2,k1_xboole_0)
    | k1_xboole_0 = sK2
    | ~ spl4_4
    | spl4_10
    | ~ spl4_17 ),
    inference(forward_demodulation,[],[f390,f91])).

fof(f390,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,sK2,k1_xboole_0)
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl4_4
    | spl4_10
    | ~ spl4_17 ),
    inference(forward_demodulation,[],[f389,f91])).

fof(f389,plain,
    ( sK0 != k1_relset_1(sK0,sK2,k1_xboole_0)
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | spl4_10
    | ~ spl4_17 ),
    inference(forward_demodulation,[],[f128,f203])).

fof(f382,plain,
    ( spl4_27
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_17 ),
    inference(avatar_split_clause,[],[f358,f201,f93,f89,f81,f379])).

fof(f379,plain,
    ( spl4_27
  <=> v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f358,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_17 ),
    inference(forward_demodulation,[],[f357,f203])).

fof(f357,plain,
    ( v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f303,f94])).

fof(f94,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f93])).

fof(f293,plain,
    ( spl4_23
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f284,f212,f110,f98,f290])).

fof(f98,plain,
    ( spl4_6
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f284,plain,
    ( r1_tarski(sK0,sK0)
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_18 ),
    inference(resolution,[],[f274,f100])).

fof(f100,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f98])).

fof(f274,plain,
    ( ! [X2,X1] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | r1_tarski(sK0,X1) )
    | ~ spl4_8
    | ~ spl4_18 ),
    inference(forward_demodulation,[],[f140,f214])).

fof(f140,plain,
    ( ! [X2,X1] :
        ( r1_tarski(k1_relat_1(sK3),X1)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
    | ~ spl4_8 ),
    inference(resolution,[],[f125,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f125,plain,
    ( ! [X3] :
        ( ~ v4_relat_1(sK3,X3)
        | r1_tarski(k1_relat_1(sK3),X3) )
    | ~ spl4_8 ),
    inference(resolution,[],[f112,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f283,plain,
    ( spl4_22
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f276,f110,f98,f280])).

fof(f276,plain,
    ( r1_tarski(k2_relat_1(sK3),sK1)
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(resolution,[],[f273,f100])).

fof(f273,plain,
    ( ! [X2,X1] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | r1_tarski(k2_relat_1(sK3),X1) )
    | ~ spl4_8 ),
    inference(resolution,[],[f127,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f127,plain,
    ( ! [X5] :
        ( ~ v5_relat_1(sK3,X5)
        | r1_tarski(k2_relat_1(sK3),X5) )
    | ~ spl4_8 ),
    inference(resolution,[],[f112,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f264,plain,
    ( spl4_9
    | ~ spl4_17 ),
    inference(avatar_contradiction_clause,[],[f263])).

fof(f263,plain,
    ( $false
    | spl4_9
    | ~ spl4_17 ),
    inference(subsumption_resolution,[],[f254,f38])).

fof(f254,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | spl4_9
    | ~ spl4_17 ),
    inference(superposition,[],[f117,f203])).

fof(f215,plain,
    ( spl4_18
    | ~ spl4_6
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f207,f142,f98,f212])).

fof(f142,plain,
    ( spl4_12
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f207,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl4_6
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f205,f100])).

fof(f205,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_12 ),
    inference(superposition,[],[f144,f51])).

fof(f144,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f142])).

fof(f204,plain,
    ( spl4_17
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f190,f174,f201])).

fof(f174,plain,
    ( spl4_15
  <=> r1_tarski(sK3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f190,plain,
    ( k1_xboole_0 = sK3
    | ~ spl4_15 ),
    inference(resolution,[],[f176,f39])).

fof(f176,plain,
    ( r1_tarski(sK3,k1_xboole_0)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f174])).

fof(f177,plain,
    ( spl4_15
    | ~ spl4_4
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f152,f131,f89,f174])).

fof(f131,plain,
    ( spl4_11
  <=> r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f152,plain,
    ( r1_tarski(sK3,k1_xboole_0)
    | ~ spl4_4
    | ~ spl4_11 ),
    inference(forward_demodulation,[],[f147,f63])).

fof(f147,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,sK1))
    | ~ spl4_4
    | ~ spl4_11 ),
    inference(superposition,[],[f133,f91])).

fof(f133,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f131])).

fof(f145,plain,
    ( spl4_12
    | ~ spl4_3
    | spl4_5
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f138,f98,f93,f81,f142])).

fof(f138,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl4_3
    | spl4_5
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f137,f100])).

fof(f137,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_3
    | spl4_5 ),
    inference(subsumption_resolution,[],[f87,f95])).

fof(f87,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_3 ),
    inference(resolution,[],[f83,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f134,plain,
    ( spl4_11
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f108,f98,f131])).

fof(f108,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))
    | ~ spl4_6 ),
    inference(resolution,[],[f100,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f122,plain,
    ( ~ spl4_9
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f69,f119,f115])).

fof(f69,plain,
    ( ~ v1_funct_2(sK3,sK0,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(global_subsumption,[],[f34,f32])).

fof(f32,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK0,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_2)).

fof(f34,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f17])).

fof(f113,plain,
    ( spl4_8
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f107,f98,f110])).

fof(f107,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_6 ),
    inference(resolution,[],[f100,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f101,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f36,f98])).

fof(f36,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f17])).

fof(f96,plain,
    ( spl4_4
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f33,f93,f89])).

fof(f33,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f17])).

fof(f84,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f35,f81])).

fof(f35,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f79,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f37,f76])).

fof(f37,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:43:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (22687)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.47  % (22690)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.47  % (22695)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.48  % (22680)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.48  % (22691)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.49  % (22689)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (22683)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.49  % (22681)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.49  % (22680)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % (22688)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.50  % (22692)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f633,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f79,f84,f96,f101,f113,f122,f134,f145,f177,f204,f215,f264,f283,f293,f382,f404,f419,f431,f465,f471,f476,f564,f569,f585,f600,f628,f632])).
% 0.21/0.50  % (22693)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.50  fof(f632,plain,(
% 0.21/0.50    ~spl4_2 | ~spl4_22 | spl4_38),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f631])).
% 0.21/0.50  fof(f631,plain,(
% 0.21/0.50    $false | (~spl4_2 | ~spl4_22 | spl4_38)),
% 0.21/0.50    inference(subsumption_resolution,[],[f605,f531])).
% 0.21/0.50  fof(f531,plain,(
% 0.21/0.50    ~r1_tarski(k2_relat_1(sK3),sK2) | spl4_38),
% 0.21/0.50    inference(avatar_component_clause,[],[f530])).
% 0.21/0.50  fof(f530,plain,(
% 0.21/0.50    spl4_38 <=> r1_tarski(k2_relat_1(sK3),sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).
% 0.21/0.50  fof(f605,plain,(
% 0.21/0.50    r1_tarski(k2_relat_1(sK3),sK2) | (~spl4_2 | ~spl4_22)),
% 0.21/0.50    inference(resolution,[],[f287,f78])).
% 0.21/0.50  fof(f78,plain,(
% 0.21/0.50    r1_tarski(sK1,sK2) | ~spl4_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f76])).
% 0.21/0.50  fof(f76,plain,(
% 0.21/0.50    spl4_2 <=> r1_tarski(sK1,sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.50  fof(f287,plain,(
% 0.21/0.50    ( ! [X0] : (~r1_tarski(sK1,X0) | r1_tarski(k2_relat_1(sK3),X0)) ) | ~spl4_22),
% 0.21/0.50    inference(resolution,[],[f282,f61])).
% 0.21/0.50  fof(f61,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.50    inference(flattening,[],[f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.50    inference(ennf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.21/0.50  fof(f282,plain,(
% 0.21/0.50    r1_tarski(k2_relat_1(sK3),sK1) | ~spl4_22),
% 0.21/0.50    inference(avatar_component_clause,[],[f280])).
% 0.21/0.50  fof(f280,plain,(
% 0.21/0.50    spl4_22 <=> r1_tarski(k2_relat_1(sK3),sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.21/0.50  fof(f628,plain,(
% 0.21/0.50    ~spl4_8 | spl4_9 | ~spl4_18 | ~spl4_23 | ~spl4_38),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f627])).
% 0.21/0.50  fof(f627,plain,(
% 0.21/0.50    $false | (~spl4_8 | spl4_9 | ~spl4_18 | ~spl4_23 | ~spl4_38)),
% 0.21/0.50    inference(subsumption_resolution,[],[f626,f117])).
% 0.21/0.50  fof(f117,plain,(
% 0.21/0.50    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | spl4_9),
% 0.21/0.50    inference(avatar_component_clause,[],[f115])).
% 0.21/0.50  fof(f115,plain,(
% 0.21/0.50    spl4_9 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.50  fof(f626,plain,(
% 0.21/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | (~spl4_8 | ~spl4_18 | ~spl4_23 | ~spl4_38)),
% 0.21/0.50    inference(resolution,[],[f609,f532])).
% 0.21/0.50  fof(f532,plain,(
% 0.21/0.50    r1_tarski(k2_relat_1(sK3),sK2) | ~spl4_38),
% 0.21/0.50    inference(avatar_component_clause,[],[f530])).
% 0.21/0.50  fof(f609,plain,(
% 0.21/0.50    ( ! [X0] : (~r1_tarski(k2_relat_1(sK3),X0) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))) ) | (~spl4_8 | ~spl4_18 | ~spl4_23)),
% 0.21/0.50    inference(resolution,[],[f607,f292])).
% 0.21/0.50  fof(f292,plain,(
% 0.21/0.50    r1_tarski(sK0,sK0) | ~spl4_23),
% 0.21/0.50    inference(avatar_component_clause,[],[f290])).
% 0.21/0.50  fof(f290,plain,(
% 0.21/0.50    spl4_23 <=> r1_tarski(sK0,sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 0.21/0.50  fof(f607,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_tarski(sK0,X0) | ~r1_tarski(k2_relat_1(sK3),X1) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | (~spl4_8 | ~spl4_18)),
% 0.21/0.50    inference(forward_demodulation,[],[f123,f214])).
% 0.21/0.50  fof(f214,plain,(
% 0.21/0.50    sK0 = k1_relat_1(sK3) | ~spl4_18),
% 0.21/0.50    inference(avatar_component_clause,[],[f212])).
% 0.21/0.50  fof(f212,plain,(
% 0.21/0.50    spl4_18 <=> sK0 = k1_relat_1(sK3)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.21/0.50  fof(f123,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(sK3),X0) | ~r1_tarski(k2_relat_1(sK3),X1) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl4_8),
% 0.21/0.50    inference(resolution,[],[f112,f49])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(k1_relat_1(X2),X0) | ~r1_tarski(k2_relat_1(X2),X1) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 0.21/0.50    inference(flattening,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 0.21/0.50    inference(ennf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).
% 0.21/0.50  fof(f112,plain,(
% 0.21/0.50    v1_relat_1(sK3) | ~spl4_8),
% 0.21/0.50    inference(avatar_component_clause,[],[f110])).
% 0.21/0.50  fof(f110,plain,(
% 0.21/0.50    spl4_8 <=> v1_relat_1(sK3)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.50  fof(f600,plain,(
% 0.21/0.50    spl4_31 | ~spl4_33),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f599])).
% 0.21/0.50  fof(f599,plain,(
% 0.21/0.50    $false | (spl4_31 | ~spl4_33)),
% 0.21/0.50    inference(subsumption_resolution,[],[f598,f38])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.50  fof(f598,plain,(
% 0.21/0.50    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | (spl4_31 | ~spl4_33)),
% 0.21/0.50    inference(subsumption_resolution,[],[f593,f418])).
% 0.21/0.50  fof(f418,plain,(
% 0.21/0.50    k1_xboole_0 != k1_relat_1(k1_xboole_0) | spl4_31),
% 0.21/0.50    inference(avatar_component_clause,[],[f416])).
% 0.21/0.50  fof(f416,plain,(
% 0.21/0.50    spl4_31 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).
% 0.21/0.50  fof(f593,plain,(
% 0.21/0.50    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | ~spl4_33),
% 0.21/0.50    inference(superposition,[],[f51,f435])).
% 0.21/0.50  fof(f435,plain,(
% 0.21/0.50    k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,k1_xboole_0) | ~spl4_33),
% 0.21/0.50    inference(avatar_component_clause,[],[f433])).
% 0.21/0.50  fof(f433,plain,(
% 0.21/0.50    spl4_33 <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,k1_xboole_0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.50  fof(f585,plain,(
% 0.21/0.50    spl4_33 | ~spl4_35),
% 0.21/0.50    inference(avatar_split_clause,[],[f484,f468,f433])).
% 0.21/0.50  fof(f468,plain,(
% 0.21/0.50    spl4_35 <=> v1_funct_2(k1_xboole_0,k1_xboole_0,sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).
% 0.21/0.50  fof(f484,plain,(
% 0.21/0.50    k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,k1_xboole_0) | ~spl4_35),
% 0.21/0.50    inference(subsumption_resolution,[],[f482,f38])).
% 0.21/0.50  fof(f482,plain,(
% 0.21/0.50    k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | ~spl4_35),
% 0.21/0.50    inference(resolution,[],[f470,f64])).
% 0.21/0.50  fof(f64,plain,(
% 0.21/0.50    ( ! [X2,X1] : (~v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 0.21/0.50    inference(equality_resolution,[],[f57])).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f27])).
% 0.21/0.50  % (22682)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(flattening,[],[f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.50  fof(f470,plain,(
% 0.21/0.50    v1_funct_2(k1_xboole_0,k1_xboole_0,sK1) | ~spl4_35),
% 0.21/0.50    inference(avatar_component_clause,[],[f468])).
% 0.21/0.50  fof(f569,plain,(
% 0.21/0.50    ~spl4_9 | ~spl4_18 | spl4_41),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f568])).
% 0.21/0.50  fof(f568,plain,(
% 0.21/0.50    $false | (~spl4_9 | ~spl4_18 | spl4_41)),
% 0.21/0.50    inference(subsumption_resolution,[],[f567,f116])).
% 0.21/0.50  fof(f116,plain,(
% 0.21/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~spl4_9),
% 0.21/0.50    inference(avatar_component_clause,[],[f115])).
% 0.21/0.50  fof(f567,plain,(
% 0.21/0.50    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | (~spl4_18 | spl4_41)),
% 0.21/0.50    inference(subsumption_resolution,[],[f566,f214])).
% 0.21/0.50  fof(f566,plain,(
% 0.21/0.50    sK0 != k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | spl4_41),
% 0.21/0.50    inference(superposition,[],[f563,f51])).
% 0.21/0.50  fof(f563,plain,(
% 0.21/0.50    sK0 != k1_relset_1(sK0,sK2,sK3) | spl4_41),
% 0.21/0.50    inference(avatar_component_clause,[],[f561])).
% 0.21/0.50  fof(f561,plain,(
% 0.21/0.50    spl4_41 <=> sK0 = k1_relset_1(sK0,sK2,sK3)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).
% 0.21/0.50  fof(f564,plain,(
% 0.21/0.50    ~spl4_41 | ~spl4_9 | spl4_10 | spl4_28),
% 0.21/0.50    inference(avatar_split_clause,[],[f554,f397,f119,f115,f561])).
% 0.21/0.50  fof(f119,plain,(
% 0.21/0.50    spl4_10 <=> v1_funct_2(sK3,sK0,sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.50  fof(f397,plain,(
% 0.21/0.50    spl4_28 <=> k1_xboole_0 = sK2),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 0.21/0.50  fof(f554,plain,(
% 0.21/0.50    sK0 != k1_relset_1(sK0,sK2,sK3) | (~spl4_9 | spl4_10 | spl4_28)),
% 0.21/0.50    inference(subsumption_resolution,[],[f513,f116])).
% 0.21/0.50  fof(f513,plain,(
% 0.21/0.50    sK0 != k1_relset_1(sK0,sK2,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | (spl4_10 | spl4_28)),
% 0.21/0.50    inference(subsumption_resolution,[],[f128,f398])).
% 0.21/0.50  fof(f398,plain,(
% 0.21/0.50    k1_xboole_0 != sK2 | spl4_28),
% 0.21/0.50    inference(avatar_component_clause,[],[f397])).
% 0.21/0.50  fof(f128,plain,(
% 0.21/0.50    k1_xboole_0 = sK2 | sK0 != k1_relset_1(sK0,sK2,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | spl4_10),
% 0.21/0.50    inference(resolution,[],[f121,f58])).
% 0.21/0.50  fof(f58,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f27])).
% 0.21/0.50  fof(f121,plain,(
% 0.21/0.50    ~v1_funct_2(sK3,sK0,sK2) | spl4_10),
% 0.21/0.50    inference(avatar_component_clause,[],[f119])).
% 0.21/0.50  fof(f476,plain,(
% 0.21/0.50    spl4_5 | ~spl4_34),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f475])).
% 0.21/0.50  fof(f475,plain,(
% 0.21/0.50    $false | (spl4_5 | ~spl4_34)),
% 0.21/0.50    inference(subsumption_resolution,[],[f472,f95])).
% 0.21/0.50  fof(f95,plain,(
% 0.21/0.50    k1_xboole_0 != sK1 | spl4_5),
% 0.21/0.50    inference(avatar_component_clause,[],[f93])).
% 0.21/0.50  fof(f93,plain,(
% 0.21/0.50    spl4_5 <=> k1_xboole_0 = sK1),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.50  fof(f472,plain,(
% 0.21/0.50    k1_xboole_0 = sK1 | ~spl4_34),
% 0.21/0.50    inference(resolution,[],[f464,f39])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.21/0.50    inference(ennf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.21/0.50  fof(f464,plain,(
% 0.21/0.50    r1_tarski(sK1,k1_xboole_0) | ~spl4_34),
% 0.21/0.50    inference(avatar_component_clause,[],[f462])).
% 0.21/0.50  fof(f462,plain,(
% 0.21/0.50    spl4_34 <=> r1_tarski(sK1,k1_xboole_0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).
% 0.21/0.50  fof(f471,plain,(
% 0.21/0.50    spl4_35 | ~spl4_3 | ~spl4_4 | ~spl4_17),
% 0.21/0.50    inference(avatar_split_clause,[],[f438,f201,f89,f81,f468])).
% 0.21/0.50  fof(f81,plain,(
% 0.21/0.50    spl4_3 <=> v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.50  fof(f89,plain,(
% 0.21/0.50    spl4_4 <=> k1_xboole_0 = sK0),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.50  fof(f201,plain,(
% 0.21/0.50    spl4_17 <=> k1_xboole_0 = sK3),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.21/0.50  fof(f438,plain,(
% 0.21/0.50    v1_funct_2(k1_xboole_0,k1_xboole_0,sK1) | (~spl4_3 | ~spl4_4 | ~spl4_17)),
% 0.21/0.50    inference(forward_demodulation,[],[f303,f203])).
% 0.21/0.50  fof(f203,plain,(
% 0.21/0.50    k1_xboole_0 = sK3 | ~spl4_17),
% 0.21/0.50    inference(avatar_component_clause,[],[f201])).
% 0.21/0.50  fof(f303,plain,(
% 0.21/0.50    v1_funct_2(sK3,k1_xboole_0,sK1) | (~spl4_3 | ~spl4_4)),
% 0.21/0.50    inference(superposition,[],[f83,f91])).
% 0.21/0.50  fof(f91,plain,(
% 0.21/0.50    k1_xboole_0 = sK0 | ~spl4_4),
% 0.21/0.50    inference(avatar_component_clause,[],[f89])).
% 0.21/0.50  fof(f83,plain,(
% 0.21/0.50    v1_funct_2(sK3,sK0,sK1) | ~spl4_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f81])).
% 0.21/0.50  fof(f465,plain,(
% 0.21/0.50    spl4_34 | ~spl4_2 | ~spl4_28),
% 0.21/0.50    inference(avatar_split_clause,[],[f449,f397,f76,f462])).
% 0.21/0.50  fof(f449,plain,(
% 0.21/0.50    r1_tarski(sK1,k1_xboole_0) | (~spl4_2 | ~spl4_28)),
% 0.21/0.50    inference(superposition,[],[f78,f399])).
% 0.21/0.50  fof(f399,plain,(
% 0.21/0.50    k1_xboole_0 = sK2 | ~spl4_28),
% 0.21/0.50    inference(avatar_component_clause,[],[f397])).
% 0.21/0.50  fof(f431,plain,(
% 0.21/0.50    k1_xboole_0 != sK3 | k1_xboole_0 != sK0 | k1_xboole_0 != sK2 | v1_funct_2(sK3,sK0,sK2) | ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.21/0.50    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.50  fof(f419,plain,(
% 0.21/0.50    ~spl4_31 | spl4_29),
% 0.21/0.50    inference(avatar_split_clause,[],[f411,f401,f416])).
% 0.21/0.50  fof(f401,plain,(
% 0.21/0.50    spl4_29 <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,sK2,k1_xboole_0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 0.21/0.50  fof(f411,plain,(
% 0.21/0.50    k1_xboole_0 != k1_relat_1(k1_xboole_0) | spl4_29),
% 0.21/0.50    inference(subsumption_resolution,[],[f410,f38])).
% 0.21/0.50  fof(f410,plain,(
% 0.21/0.50    k1_xboole_0 != k1_relat_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) | spl4_29),
% 0.21/0.50    inference(superposition,[],[f403,f51])).
% 0.21/0.50  fof(f403,plain,(
% 0.21/0.50    k1_xboole_0 != k1_relset_1(k1_xboole_0,sK2,k1_xboole_0) | spl4_29),
% 0.21/0.50    inference(avatar_component_clause,[],[f401])).
% 0.21/0.50  fof(f404,plain,(
% 0.21/0.50    spl4_28 | ~spl4_29 | ~spl4_4 | spl4_10 | ~spl4_17),
% 0.21/0.50    inference(avatar_split_clause,[],[f394,f201,f119,f89,f401,f397])).
% 0.21/0.50  fof(f394,plain,(
% 0.21/0.50    k1_xboole_0 != k1_relset_1(k1_xboole_0,sK2,k1_xboole_0) | k1_xboole_0 = sK2 | (~spl4_4 | spl4_10 | ~spl4_17)),
% 0.21/0.50    inference(subsumption_resolution,[],[f393,f38])).
% 0.21/0.50  fof(f393,plain,(
% 0.21/0.50    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 != k1_relset_1(k1_xboole_0,sK2,k1_xboole_0) | k1_xboole_0 = sK2 | (~spl4_4 | spl4_10 | ~spl4_17)),
% 0.21/0.50    inference(forward_demodulation,[],[f392,f203])).
% 0.21/0.50  fof(f392,plain,(
% 0.21/0.50    ~m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 != k1_relset_1(k1_xboole_0,sK2,k1_xboole_0) | k1_xboole_0 = sK2 | (~spl4_4 | spl4_10 | ~spl4_17)),
% 0.21/0.50    inference(forward_demodulation,[],[f391,f63])).
% 0.21/0.50  fof(f63,plain,(
% 0.21/0.50    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.21/0.50    inference(equality_resolution,[],[f47])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.50  fof(f391,plain,(
% 0.21/0.50    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) | k1_xboole_0 != k1_relset_1(k1_xboole_0,sK2,k1_xboole_0) | k1_xboole_0 = sK2 | (~spl4_4 | spl4_10 | ~spl4_17)),
% 0.21/0.50    inference(forward_demodulation,[],[f390,f91])).
% 0.21/0.50  fof(f390,plain,(
% 0.21/0.50    k1_xboole_0 != k1_relset_1(k1_xboole_0,sK2,k1_xboole_0) | k1_xboole_0 = sK2 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | (~spl4_4 | spl4_10 | ~spl4_17)),
% 0.21/0.50    inference(forward_demodulation,[],[f389,f91])).
% 0.21/0.50  fof(f389,plain,(
% 0.21/0.50    sK0 != k1_relset_1(sK0,sK2,k1_xboole_0) | k1_xboole_0 = sK2 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | (spl4_10 | ~spl4_17)),
% 0.21/0.50    inference(forward_demodulation,[],[f128,f203])).
% 0.21/0.50  fof(f382,plain,(
% 0.21/0.50    spl4_27 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_17),
% 0.21/0.50    inference(avatar_split_clause,[],[f358,f201,f93,f89,f81,f379])).
% 0.21/0.50  fof(f379,plain,(
% 0.21/0.50    spl4_27 <=> v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 0.21/0.50  fof(f358,plain,(
% 0.21/0.50    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_17)),
% 0.21/0.50    inference(forward_demodulation,[],[f357,f203])).
% 0.21/0.50  fof(f357,plain,(
% 0.21/0.50    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | (~spl4_3 | ~spl4_4 | ~spl4_5)),
% 0.21/0.50    inference(forward_demodulation,[],[f303,f94])).
% 0.21/0.50  fof(f94,plain,(
% 0.21/0.50    k1_xboole_0 = sK1 | ~spl4_5),
% 0.21/0.50    inference(avatar_component_clause,[],[f93])).
% 0.21/0.50  fof(f293,plain,(
% 0.21/0.50    spl4_23 | ~spl4_6 | ~spl4_8 | ~spl4_18),
% 0.21/0.50    inference(avatar_split_clause,[],[f284,f212,f110,f98,f290])).
% 0.21/0.50  fof(f98,plain,(
% 0.21/0.50    spl4_6 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.50  fof(f284,plain,(
% 0.21/0.50    r1_tarski(sK0,sK0) | (~spl4_6 | ~spl4_8 | ~spl4_18)),
% 0.21/0.50    inference(resolution,[],[f274,f100])).
% 0.21/0.50  fof(f100,plain,(
% 0.21/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_6),
% 0.21/0.50    inference(avatar_component_clause,[],[f98])).
% 0.21/0.50  fof(f274,plain,(
% 0.21/0.50    ( ! [X2,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | r1_tarski(sK0,X1)) ) | (~spl4_8 | ~spl4_18)),
% 0.21/0.50    inference(forward_demodulation,[],[f140,f214])).
% 0.21/0.50  fof(f140,plain,(
% 0.21/0.50    ( ! [X2,X1] : (r1_tarski(k1_relat_1(sK3),X1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ) | ~spl4_8),
% 0.21/0.50    inference(resolution,[],[f125,f52])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.50  fof(f125,plain,(
% 0.21/0.50    ( ! [X3] : (~v4_relat_1(sK3,X3) | r1_tarski(k1_relat_1(sK3),X3)) ) | ~spl4_8),
% 0.21/0.50    inference(resolution,[],[f112,f43])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 0.21/0.50  fof(f283,plain,(
% 0.21/0.50    spl4_22 | ~spl4_6 | ~spl4_8),
% 0.21/0.50    inference(avatar_split_clause,[],[f276,f110,f98,f280])).
% 0.21/0.50  fof(f276,plain,(
% 0.21/0.50    r1_tarski(k2_relat_1(sK3),sK1) | (~spl4_6 | ~spl4_8)),
% 0.21/0.50    inference(resolution,[],[f273,f100])).
% 0.21/0.50  fof(f273,plain,(
% 0.21/0.50    ( ! [X2,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | r1_tarski(k2_relat_1(sK3),X1)) ) | ~spl4_8),
% 0.21/0.50    inference(resolution,[],[f127,f53])).
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f25])).
% 0.21/0.50  fof(f127,plain,(
% 0.21/0.50    ( ! [X5] : (~v5_relat_1(sK3,X5) | r1_tarski(k2_relat_1(sK3),X5)) ) | ~spl4_8),
% 0.21/0.50    inference(resolution,[],[f112,f41])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 0.21/0.50  fof(f264,plain,(
% 0.21/0.50    spl4_9 | ~spl4_17),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f263])).
% 0.21/0.50  fof(f263,plain,(
% 0.21/0.50    $false | (spl4_9 | ~spl4_17)),
% 0.21/0.50    inference(subsumption_resolution,[],[f254,f38])).
% 0.21/0.50  fof(f254,plain,(
% 0.21/0.50    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | (spl4_9 | ~spl4_17)),
% 0.21/0.50    inference(superposition,[],[f117,f203])).
% 0.21/0.50  fof(f215,plain,(
% 0.21/0.50    spl4_18 | ~spl4_6 | ~spl4_12),
% 0.21/0.50    inference(avatar_split_clause,[],[f207,f142,f98,f212])).
% 0.21/0.50  fof(f142,plain,(
% 0.21/0.50    spl4_12 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.21/0.50  fof(f207,plain,(
% 0.21/0.50    sK0 = k1_relat_1(sK3) | (~spl4_6 | ~spl4_12)),
% 0.21/0.50    inference(subsumption_resolution,[],[f205,f100])).
% 0.21/0.50  fof(f205,plain,(
% 0.21/0.50    sK0 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_12),
% 0.21/0.50    inference(superposition,[],[f144,f51])).
% 0.21/0.50  fof(f144,plain,(
% 0.21/0.50    sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl4_12),
% 0.21/0.50    inference(avatar_component_clause,[],[f142])).
% 0.21/0.50  fof(f204,plain,(
% 0.21/0.50    spl4_17 | ~spl4_15),
% 0.21/0.50    inference(avatar_split_clause,[],[f190,f174,f201])).
% 0.21/0.50  fof(f174,plain,(
% 0.21/0.50    spl4_15 <=> r1_tarski(sK3,k1_xboole_0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.21/0.50  fof(f190,plain,(
% 0.21/0.50    k1_xboole_0 = sK3 | ~spl4_15),
% 0.21/0.50    inference(resolution,[],[f176,f39])).
% 0.21/0.50  fof(f176,plain,(
% 0.21/0.50    r1_tarski(sK3,k1_xboole_0) | ~spl4_15),
% 0.21/0.50    inference(avatar_component_clause,[],[f174])).
% 0.21/0.50  fof(f177,plain,(
% 0.21/0.50    spl4_15 | ~spl4_4 | ~spl4_11),
% 0.21/0.50    inference(avatar_split_clause,[],[f152,f131,f89,f174])).
% 0.21/0.50  fof(f131,plain,(
% 0.21/0.50    spl4_11 <=> r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.50  fof(f152,plain,(
% 0.21/0.50    r1_tarski(sK3,k1_xboole_0) | (~spl4_4 | ~spl4_11)),
% 0.21/0.50    inference(forward_demodulation,[],[f147,f63])).
% 0.21/0.50  fof(f147,plain,(
% 0.21/0.50    r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,sK1)) | (~spl4_4 | ~spl4_11)),
% 0.21/0.50    inference(superposition,[],[f133,f91])).
% 0.21/0.50  fof(f133,plain,(
% 0.21/0.50    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) | ~spl4_11),
% 0.21/0.50    inference(avatar_component_clause,[],[f131])).
% 0.21/0.50  fof(f145,plain,(
% 0.21/0.50    spl4_12 | ~spl4_3 | spl4_5 | ~spl4_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f138,f98,f93,f81,f142])).
% 0.21/0.50  fof(f138,plain,(
% 0.21/0.50    sK0 = k1_relset_1(sK0,sK1,sK3) | (~spl4_3 | spl4_5 | ~spl4_6)),
% 0.21/0.50    inference(subsumption_resolution,[],[f137,f100])).
% 0.21/0.50  fof(f137,plain,(
% 0.21/0.50    sK0 = k1_relset_1(sK0,sK1,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (~spl4_3 | spl4_5)),
% 0.21/0.50    inference(subsumption_resolution,[],[f87,f95])).
% 0.21/0.50  fof(f87,plain,(
% 0.21/0.50    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_3),
% 0.21/0.50    inference(resolution,[],[f83,f59])).
% 0.21/0.50  fof(f59,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f27])).
% 0.21/0.50  fof(f134,plain,(
% 0.21/0.50    spl4_11 | ~spl4_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f108,f98,f131])).
% 0.21/0.50  fof(f108,plain,(
% 0.21/0.50    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) | ~spl4_6),
% 0.21/0.50    inference(resolution,[],[f100,f45])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.50  fof(f122,plain,(
% 0.21/0.50    ~spl4_9 | ~spl4_10),
% 0.21/0.50    inference(avatar_split_clause,[],[f69,f119,f115])).
% 0.21/0.50  fof(f69,plain,(
% 0.21/0.50    ~v1_funct_2(sK3,sK0,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.21/0.50    inference(global_subsumption,[],[f34,f32])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK0,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.21/0.50    inference(cnf_transformation,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.21/0.50    inference(flattening,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ? [X0,X1,X2,X3] : ((((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X1,X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.21/0.50    inference(ennf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X1,X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.21/0.50    inference(negated_conjecture,[],[f14])).
% 0.21/0.50  fof(f14,conjecture,(
% 0.21/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X1,X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_2)).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    v1_funct_1(sK3)),
% 0.21/0.50    inference(cnf_transformation,[],[f17])).
% 0.21/0.50  fof(f113,plain,(
% 0.21/0.50    spl4_8 | ~spl4_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f107,f98,f110])).
% 0.21/0.50  fof(f107,plain,(
% 0.21/0.50    v1_relat_1(sK3) | ~spl4_6),
% 0.21/0.50    inference(resolution,[],[f100,f50])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.50  fof(f101,plain,(
% 0.21/0.50    spl4_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f36,f98])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.50    inference(cnf_transformation,[],[f17])).
% 0.21/0.50  fof(f96,plain,(
% 0.21/0.50    spl4_4 | ~spl4_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f33,f93,f89])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    k1_xboole_0 != sK1 | k1_xboole_0 = sK0),
% 0.21/0.50    inference(cnf_transformation,[],[f17])).
% 0.21/0.50  fof(f84,plain,(
% 0.21/0.50    spl4_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f35,f81])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f17])).
% 0.21/0.50  fof(f79,plain,(
% 0.21/0.50    spl4_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f37,f76])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    r1_tarski(sK1,sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f17])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (22680)------------------------------
% 0.21/0.50  % (22680)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (22680)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (22680)Memory used [KB]: 10874
% 0.21/0.50  % (22680)Time elapsed: 0.074 s
% 0.21/0.50  % (22680)------------------------------
% 0.21/0.50  % (22680)------------------------------
% 0.21/0.50  % (22678)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (22679)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.51  % (22676)Success in time 0.147 s
%------------------------------------------------------------------------------
