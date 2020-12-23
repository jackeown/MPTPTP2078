%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:11 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  255 ( 550 expanded)
%              Number of leaves         :   49 ( 234 expanded)
%              Depth                    :   15
%              Number of atoms          : 1135 (2137 expanded)
%              Number of equality atoms :  116 ( 191 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f646,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f74,f79,f84,f89,f94,f99,f120,f125,f130,f145,f150,f155,f166,f181,f186,f201,f231,f245,f277,f296,f312,f332,f347,f364,f440,f461,f464,f491,f530,f569,f595,f633,f644,f645])).

fof(f645,plain,
    ( k3_funct_2(sK1,sK0,sK3,sK5) != k7_partfun1(sK0,sK3,sK5)
    | k7_partfun1(sK0,sK3,sK5) != k1_funct_1(sK3,sK5)
    | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f644,plain,
    ( spl6_64
    | spl6_3
    | ~ spl6_5
    | ~ spl6_26
    | ~ spl6_43
    | ~ spl6_49
    | ~ spl6_63 ),
    inference(avatar_split_clause,[],[f638,f623,f488,f437,f293,f91,f81,f641])).

fof(f641,plain,
    ( spl6_64
  <=> k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_64])])).

fof(f81,plain,
    ( spl6_3
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f91,plain,
    ( spl6_5
  <=> m1_subset_1(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f293,plain,
    ( spl6_26
  <=> v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f437,plain,
    ( spl6_43
  <=> m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).

fof(f488,plain,
    ( spl6_49
  <=> k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_49])])).

fof(f623,plain,
    ( spl6_63
  <=> v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_63])])).

fof(f638,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | spl6_3
    | ~ spl6_5
    | ~ spl6_26
    | ~ spl6_43
    | ~ spl6_49
    | ~ spl6_63 ),
    inference(forward_demodulation,[],[f637,f490])).

fof(f490,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | ~ spl6_49 ),
    inference(avatar_component_clause,[],[f488])).

fof(f637,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5)
    | spl6_3
    | ~ spl6_5
    | ~ spl6_26
    | ~ spl6_43
    | ~ spl6_63 ),
    inference(resolution,[],[f636,f93])).

fof(f93,plain,
    ( m1_subset_1(sK5,sK1)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f91])).

fof(f636,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) )
    | spl6_3
    | ~ spl6_26
    | ~ spl6_43
    | ~ spl6_63 ),
    inference(subsumption_resolution,[],[f601,f624])).

fof(f624,plain,
    ( v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2)
    | ~ spl6_63 ),
    inference(avatar_component_clause,[],[f623])).

% (11438)Refutation not found, incomplete strategy% (11438)------------------------------
% (11438)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (11438)Termination reason: Refutation not found, incomplete strategy

% (11438)Memory used [KB]: 10618
% (11438)Time elapsed: 0.090 s
% (11438)------------------------------
% (11438)------------------------------
% (11434)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% (11424)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% (11431)Termination reason: Refutation not found, incomplete strategy

% (11431)Memory used [KB]: 1791
% (11431)Time elapsed: 0.091 s
% (11431)------------------------------
% (11431)------------------------------
fof(f601,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2)
        | ~ m1_subset_1(X0,sK1)
        | k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) )
    | spl6_3
    | ~ spl6_26
    | ~ spl6_43 ),
    inference(subsumption_resolution,[],[f600,f83])).

fof(f83,plain,
    ( ~ v1_xboole_0(sK1)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f81])).

fof(f600,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2)
        | v1_xboole_0(sK1)
        | ~ m1_subset_1(X0,sK1)
        | k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) )
    | ~ spl6_26
    | ~ spl6_43 ),
    inference(resolution,[],[f301,f439])).

fof(f439,plain,
    ( m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl6_43 ),
    inference(avatar_component_clause,[],[f437])).

fof(f301,plain,
    ( ! [X10,X8,X9] :
        ( ~ m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
        | ~ v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X8,X9)
        | v1_xboole_0(X8)
        | ~ m1_subset_1(X10,X8)
        | k3_funct_2(X8,X9,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X10) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X10) )
    | ~ spl6_26 ),
    inference(resolution,[],[f295,f65])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | v1_xboole_0(X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,X0)
      | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(f295,plain,
    ( v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4))
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f293])).

fof(f633,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | spl6_63 ),
    inference(avatar_contradiction_clause,[],[f632])).

fof(f632,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | spl6_63 ),
    inference(subsumption_resolution,[],[f631,f119])).

fof(f119,plain,
    ( v1_funct_2(sK3,sK1,sK0)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl6_7
  <=> v1_funct_2(sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f631,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_8
    | ~ spl6_9
    | spl6_63 ),
    inference(subsumption_resolution,[],[f630,f124])).

fof(f124,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl6_8
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f630,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_9
    | spl6_63 ),
    inference(subsumption_resolution,[],[f629,f73])).

fof(f73,plain,
    ( v1_funct_1(sK4)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl6_1
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f629,plain,
    ( ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ spl6_2
    | ~ spl6_9
    | spl6_63 ),
    inference(subsumption_resolution,[],[f627,f129])).

fof(f129,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl6_9
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f627,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ spl6_2
    | spl6_63 ),
    inference(resolution,[],[f625,f112])).

fof(f112,plain,
    ( ! [X17,X15,X18,X16] :
        ( v1_funct_2(k8_funct_2(X15,X16,X18,sK3,X17),X15,X18)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X15,X16)))
        | ~ v1_funct_1(X17)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X16,X18)))
        | ~ v1_funct_2(sK3,X15,X16) )
    | ~ spl6_2 ),
    inference(resolution,[],[f78,f67])).

fof(f67,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2)
        & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2)
        & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X4)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2)
        & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_funct_2)).

fof(f78,plain,
    ( v1_funct_1(sK3)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl6_2
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f625,plain,
    ( ~ v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2)
    | spl6_63 ),
    inference(avatar_component_clause,[],[f623])).

fof(f595,plain,
    ( spl6_59
    | ~ spl6_1
    | spl6_4
    | ~ spl6_8
    | ~ spl6_25
    | ~ spl6_33
    | ~ spl6_57 ),
    inference(avatar_split_clause,[],[f576,f566,f361,f269,f122,f86,f71,f592])).

fof(f592,plain,
    ( spl6_59
  <=> k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_59])])).

fof(f86,plain,
    ( spl6_4
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f269,plain,
    ( spl6_25
  <=> v1_funct_2(sK4,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f361,plain,
    ( spl6_33
  <=> m1_subset_1(k1_funct_1(sK3,sK5),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).

fof(f566,plain,
    ( spl6_57
  <=> k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,sK5)) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_57])])).

fof(f576,plain,
    ( k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | ~ spl6_1
    | spl6_4
    | ~ spl6_8
    | ~ spl6_25
    | ~ spl6_33
    | ~ spl6_57 ),
    inference(subsumption_resolution,[],[f575,f88])).

fof(f88,plain,
    ( ~ v1_xboole_0(sK0)
    | spl6_4 ),
    inference(avatar_component_clause,[],[f86])).

fof(f575,plain,
    ( k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | v1_xboole_0(sK0)
    | ~ spl6_1
    | ~ spl6_8
    | ~ spl6_25
    | ~ spl6_33
    | ~ spl6_57 ),
    inference(subsumption_resolution,[],[f574,f363])).

fof(f363,plain,
    ( m1_subset_1(k1_funct_1(sK3,sK5),sK0)
    | ~ spl6_33 ),
    inference(avatar_component_clause,[],[f361])).

fof(f574,plain,
    ( k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | ~ m1_subset_1(k1_funct_1(sK3,sK5),sK0)
    | v1_xboole_0(sK0)
    | ~ spl6_1
    | ~ spl6_8
    | ~ spl6_25
    | ~ spl6_57 ),
    inference(subsumption_resolution,[],[f573,f124])).

fof(f573,plain,
    ( k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ m1_subset_1(k1_funct_1(sK3,sK5),sK0)
    | v1_xboole_0(sK0)
    | ~ spl6_1
    | ~ spl6_25
    | ~ spl6_57 ),
    inference(subsumption_resolution,[],[f570,f270])).

fof(f270,plain,
    ( v1_funct_2(sK4,sK0,sK2)
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f269])).

fof(f570,plain,
    ( k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | ~ v1_funct_2(sK4,sK0,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ m1_subset_1(k1_funct_1(sK3,sK5),sK0)
    | v1_xboole_0(sK0)
    | ~ spl6_1
    | ~ spl6_57 ),
    inference(superposition,[],[f568,f103])).

fof(f103,plain,
    ( ! [X10,X8,X9] :
        ( k3_funct_2(X8,X9,sK4,X10) = k1_funct_1(sK4,X10)
        | ~ v1_funct_2(sK4,X8,X9)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
        | ~ m1_subset_1(X10,X8)
        | v1_xboole_0(X8) )
    | ~ spl6_1 ),
    inference(resolution,[],[f73,f65])).

fof(f568,plain,
    ( k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,sK5)) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5))
    | ~ spl6_57 ),
    inference(avatar_component_clause,[],[f566])).

fof(f569,plain,
    ( spl6_57
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | spl6_21
    | ~ spl6_25
    | ~ spl6_27
    | ~ spl6_31 ),
    inference(avatar_split_clause,[],[f448,f344,f309,f269,f228,f127,f122,f117,f91,f86,f81,f76,f71,f566])).

fof(f228,plain,
    ( spl6_21
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f309,plain,
    ( spl6_27
  <=> k3_funct_2(sK1,sK0,sK3,sK5) = k7_partfun1(sK0,sK3,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f344,plain,
    ( spl6_31
  <=> k7_partfun1(sK0,sK3,sK5) = k1_funct_1(sK3,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).

fof(f448,plain,
    ( k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,sK5)) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5))
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | spl6_21
    | ~ spl6_25
    | ~ spl6_27
    | ~ spl6_31 ),
    inference(forward_demodulation,[],[f447,f346])).

fof(f346,plain,
    ( k7_partfun1(sK0,sK3,sK5) = k1_funct_1(sK3,sK5)
    | ~ spl6_31 ),
    inference(avatar_component_clause,[],[f344])).

fof(f447,plain,
    ( k3_funct_2(sK0,sK2,sK4,k7_partfun1(sK0,sK3,sK5)) = k7_partfun1(sK2,sK4,k7_partfun1(sK0,sK3,sK5))
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | spl6_21
    | ~ spl6_25
    | ~ spl6_27 ),
    inference(forward_demodulation,[],[f446,f311])).

fof(f311,plain,
    ( k3_funct_2(sK1,sK0,sK3,sK5) = k7_partfun1(sK0,sK3,sK5)
    | ~ spl6_27 ),
    inference(avatar_component_clause,[],[f309])).

fof(f446,plain,
    ( k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) = k3_funct_2(sK0,sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5))
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | spl6_21
    | ~ spl6_25 ),
    inference(resolution,[],[f306,f93])).

fof(f306,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | k3_funct_2(sK0,sK2,sK4,k3_funct_2(sK1,sK0,sK3,X0)) = k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,X0)) )
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | spl6_21
    | ~ spl6_25 ),
    inference(resolution,[],[f305,f225])).

fof(f225,plain,
    ( ! [X0] :
        ( m1_subset_1(k3_funct_2(sK1,sK0,sK3,X0),sK0)
        | ~ m1_subset_1(X0,sK1) )
    | ~ spl6_2
    | spl6_3
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f224,f83])).

fof(f224,plain,
    ( ! [X0] :
        ( v1_xboole_0(sK1)
        | ~ m1_subset_1(X0,sK1)
        | m1_subset_1(k3_funct_2(sK1,sK0,sK3,X0),sK0) )
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f223,f119])).

fof(f223,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK3,sK1,sK0)
        | v1_xboole_0(sK1)
        | ~ m1_subset_1(X0,sK1)
        | m1_subset_1(k3_funct_2(sK1,sK0,sK3,X0),sK0) )
    | ~ spl6_2
    | ~ spl6_9 ),
    inference(resolution,[],[f109,f129])).

fof(f109,plain,
    ( ! [X6,X7,X5] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
        | ~ v1_funct_2(sK3,X5,X6)
        | v1_xboole_0(X5)
        | ~ m1_subset_1(X7,X5)
        | m1_subset_1(k3_funct_2(X5,X6,sK3,X7),X6) )
    | ~ spl6_2 ),
    inference(resolution,[],[f78,f64])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | v1_xboole_0(X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,X0)
      | m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_funct_2)).

fof(f305,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK0)
        | k3_funct_2(sK0,sK2,sK4,X0) = k7_partfun1(sK2,sK4,X0) )
    | ~ spl6_1
    | spl6_4
    | ~ spl6_8
    | spl6_21
    | ~ spl6_25 ),
    inference(subsumption_resolution,[],[f240,f270])).

fof(f240,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK4,sK0,sK2)
        | ~ m1_subset_1(X0,sK0)
        | k3_funct_2(sK0,sK2,sK4,X0) = k7_partfun1(sK2,sK4,X0) )
    | ~ spl6_1
    | spl6_4
    | ~ spl6_8
    | spl6_21 ),
    inference(subsumption_resolution,[],[f239,f230])).

fof(f230,plain,
    ( ~ v1_xboole_0(sK2)
    | spl6_21 ),
    inference(avatar_component_clause,[],[f228])).

fof(f239,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK4,sK0,sK2)
        | v1_xboole_0(sK2)
        | ~ m1_subset_1(X0,sK0)
        | k3_funct_2(sK0,sK2,sK4,X0) = k7_partfun1(sK2,sK4,X0) )
    | ~ spl6_1
    | spl6_4
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f238,f88])).

fof(f238,plain,
    ( ! [X0] :
        ( v1_xboole_0(sK0)
        | ~ v1_funct_2(sK4,sK0,sK2)
        | v1_xboole_0(sK2)
        | ~ m1_subset_1(X0,sK0)
        | k3_funct_2(sK0,sK2,sK4,X0) = k7_partfun1(sK2,sK4,X0) )
    | ~ spl6_1
    | ~ spl6_8 ),
    inference(resolution,[],[f100,f124])).

fof(f100,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | v1_xboole_0(X1)
        | ~ v1_funct_2(sK4,X1,X0)
        | v1_xboole_0(X0)
        | ~ m1_subset_1(X2,X1)
        | k3_funct_2(X1,X0,sK4,X2) = k7_partfun1(X0,sK4,X2) )
    | ~ spl6_1 ),
    inference(resolution,[],[f73,f51])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,X0)
      | k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3)
                  | ~ m1_subset_1(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X2,X0,X1)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3)
                  | ~ m1_subset_1(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X2,X0,X1)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X2,X0,X1)
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,X0)
                 => k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t176_funct_2)).

fof(f530,plain,
    ( spl6_3
    | ~ spl6_29 ),
    inference(avatar_contradiction_clause,[],[f529])).

fof(f529,plain,
    ( $false
    | spl6_3
    | ~ spl6_29 ),
    inference(subsumption_resolution,[],[f505,f50])).

fof(f50,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f505,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl6_3
    | ~ spl6_29 ),
    inference(superposition,[],[f83,f336])).

fof(f336,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_29 ),
    inference(avatar_component_clause,[],[f334])).

fof(f334,plain,
    ( spl6_29
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f491,plain,
    ( spl6_49
    | ~ spl6_5
    | ~ spl6_45 ),
    inference(avatar_split_clause,[],[f469,f455,f91,f488])).

fof(f455,plain,
    ( spl6_45
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).

fof(f469,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | ~ spl6_5
    | ~ spl6_45 ),
    inference(resolution,[],[f456,f93])).

fof(f456,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0)) )
    | ~ spl6_45 ),
    inference(avatar_component_clause,[],[f455])).

fof(f464,plain,
    ( ~ spl6_12
    | ~ spl6_16
    | spl6_46 ),
    inference(avatar_contradiction_clause,[],[f463])).

fof(f463,plain,
    ( $false
    | ~ spl6_12
    | ~ spl6_16
    | spl6_46 ),
    inference(subsumption_resolution,[],[f462,f180])).

fof(f180,plain,
    ( v5_relat_1(sK3,sK0)
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f178])).

fof(f178,plain,
    ( spl6_16
  <=> v5_relat_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f462,plain,
    ( ~ v5_relat_1(sK3,sK0)
    | ~ spl6_12
    | spl6_46 ),
    inference(resolution,[],[f460,f161])).

fof(f161,plain,
    ( ! [X2] :
        ( r1_tarski(k2_relat_1(sK3),X2)
        | ~ v5_relat_1(sK3,X2) )
    | ~ spl6_12 ),
    inference(resolution,[],[f154,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f154,plain,
    ( v1_relat_1(sK3)
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f152])).

fof(f152,plain,
    ( spl6_12
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f460,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK0)
    | spl6_46 ),
    inference(avatar_component_clause,[],[f458])).

fof(f458,plain,
    ( spl6_46
  <=> r1_tarski(k2_relat_1(sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).

fof(f461,plain,
    ( spl6_45
    | ~ spl6_46
    | ~ spl6_1
    | ~ spl6_2
    | spl6_4
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_17
    | ~ spl6_20
    | ~ spl6_22
    | spl6_29 ),
    inference(avatar_split_clause,[],[f357,f334,f242,f198,f183,f127,f122,f117,f86,f76,f71,f458,f455])).

fof(f183,plain,
    ( spl6_17
  <=> k1_relset_1(sK0,sK2,sK4) = k1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f198,plain,
    ( spl6_20
  <=> k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f242,plain,
    ( spl6_22
  <=> sK0 = k1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f357,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(sK3),sK0)
        | ~ m1_subset_1(X0,sK1)
        | k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0)) )
    | ~ spl6_1
    | ~ spl6_2
    | spl6_4
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_17
    | ~ spl6_20
    | ~ spl6_22
    | spl6_29 ),
    inference(subsumption_resolution,[],[f356,f335])).

fof(f335,plain,
    ( k1_xboole_0 != sK1
    | spl6_29 ),
    inference(avatar_component_clause,[],[f334])).

fof(f356,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(sK3),sK0)
        | ~ m1_subset_1(X0,sK1)
        | k1_xboole_0 = sK1
        | k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0)) )
    | ~ spl6_1
    | ~ spl6_2
    | spl6_4
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_17
    | ~ spl6_20
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f355,f129])).

fof(f355,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(sK3),sK0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        | ~ m1_subset_1(X0,sK1)
        | k1_xboole_0 = sK1
        | k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0)) )
    | ~ spl6_1
    | ~ spl6_2
    | spl6_4
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_17
    | ~ spl6_20
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f354,f119])).

fof(f354,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(sK3),sK0)
        | ~ v1_funct_2(sK3,sK1,sK0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        | ~ m1_subset_1(X0,sK1)
        | k1_xboole_0 = sK1
        | k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0)) )
    | ~ spl6_1
    | ~ spl6_2
    | spl6_4
    | ~ spl6_8
    | ~ spl6_17
    | ~ spl6_20
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f353,f78])).

fof(f353,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(sK3),sK0)
        | ~ v1_funct_1(sK3)
        | ~ v1_funct_2(sK3,sK1,sK0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        | ~ m1_subset_1(X0,sK1)
        | k1_xboole_0 = sK1
        | k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0)) )
    | ~ spl6_1
    | spl6_4
    | ~ spl6_8
    | ~ spl6_17
    | ~ spl6_20
    | ~ spl6_22 ),
    inference(superposition,[],[f342,f200])).

fof(f200,plain,
    ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3)
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f198])).

fof(f342,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(k2_relset_1(X0,sK0,X1),sK0)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,X0,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
        | ~ m1_subset_1(X2,X0)
        | k1_xboole_0 = X0
        | k1_funct_1(k8_funct_2(X0,sK0,sK2,X1,sK4),X2) = k1_funct_1(sK4,k1_funct_1(X1,X2)) )
    | ~ spl6_1
    | spl6_4
    | ~ spl6_8
    | ~ spl6_17
    | ~ spl6_22 ),
    inference(forward_demodulation,[],[f205,f244])).

fof(f244,plain,
    ( sK0 = k1_relat_1(sK4)
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f242])).

fof(f205,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(k2_relset_1(X0,sK0,X1),k1_relat_1(sK4))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,X0,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
        | ~ m1_subset_1(X2,X0)
        | k1_xboole_0 = X0
        | k1_funct_1(k8_funct_2(X0,sK0,sK2,X1,sK4),X2) = k1_funct_1(sK4,k1_funct_1(X1,X2)) )
    | ~ spl6_1
    | spl6_4
    | ~ spl6_8
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f204,f88])).

fof(f204,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(k2_relset_1(X0,sK0,X1),k1_relat_1(sK4))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,X0,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
        | ~ m1_subset_1(X2,X0)
        | v1_xboole_0(sK0)
        | k1_xboole_0 = X0
        | k1_funct_1(k8_funct_2(X0,sK0,sK2,X1,sK4),X2) = k1_funct_1(sK4,k1_funct_1(X1,X2)) )
    | ~ spl6_1
    | ~ spl6_8
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f203,f124])).

fof(f203,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(k2_relset_1(X0,sK0,X1),k1_relat_1(sK4))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,X0,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
        | ~ m1_subset_1(X2,X0)
        | v1_xboole_0(sK0)
        | k1_xboole_0 = X0
        | k1_funct_1(k8_funct_2(X0,sK0,sK2,X1,sK4),X2) = k1_funct_1(sK4,k1_funct_1(X1,X2)) )
    | ~ spl6_1
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f202,f73])).

fof(f202,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(k2_relset_1(X0,sK0,X1),k1_relat_1(sK4))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,X0,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
        | ~ v1_funct_1(sK4)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
        | ~ m1_subset_1(X2,X0)
        | v1_xboole_0(sK0)
        | k1_xboole_0 = X0
        | k1_funct_1(k8_funct_2(X0,sK0,sK2,X1,sK4),X2) = k1_funct_1(sK4,k1_funct_1(X1,X2)) )
    | ~ spl6_17 ),
    inference(superposition,[],[f57,f185])).

fof(f185,plain,
    ( k1_relset_1(sK0,sK2,sK4) = k1_relat_1(sK4)
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f183])).

fof(f57,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ m1_subset_1(X5,X1)
      | v1_xboole_0(X2)
      | k1_xboole_0 = X1
      | k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ! [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
                  | k1_xboole_0 = X1
                  | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  | ~ m1_subset_1(X5,X1) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              | ~ v1_funct_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X3,X1,X2)
          | ~ v1_funct_1(X3) )
      | v1_xboole_0(X2) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ! [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
                  | k1_xboole_0 = X1
                  | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  | ~ m1_subset_1(X5,X1) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              | ~ v1_funct_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X3,X1,X2)
          | ~ v1_funct_1(X3) )
      | v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X3,X1,X2)
            & v1_funct_1(X3) )
         => ! [X4] :
              ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                & v1_funct_1(X4) )
             => ! [X5] :
                  ( m1_subset_1(X5,X1)
                 => ( r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                   => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
                      | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t185_funct_2)).

fof(f440,plain,
    ( spl6_43
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f314,f127,f122,f117,f76,f71,f437])).

fof(f314,plain,
    ( m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f313,f73])).

fof(f313,plain,
    ( ~ v1_funct_1(sK4)
    | m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(resolution,[],[f259,f124])).

fof(f259,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
        | ~ v1_funct_1(X0)
        | m1_subset_1(k8_funct_2(sK1,sK0,X1,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) )
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f258,f119])).

fof(f258,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(sK3,sK1,sK0)
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
        | m1_subset_1(k8_funct_2(sK1,sK0,X1,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) )
    | ~ spl6_2
    | ~ spl6_9 ),
    inference(resolution,[],[f113,f129])).

fof(f113,plain,
    ( ! [X21,X19,X22,X20] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))
        | ~ v1_funct_2(sK3,X19,X20)
        | ~ v1_funct_1(X21)
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X20,X22)))
        | m1_subset_1(k8_funct_2(X19,X20,X22,sK3,X21),k1_zfmisc_1(k2_zfmisc_1(X19,X22))) )
    | ~ spl6_2 ),
    inference(resolution,[],[f78,f68])).

fof(f68,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f364,plain,
    ( spl6_33
    | ~ spl6_28
    | ~ spl6_31 ),
    inference(avatar_split_clause,[],[f352,f344,f329,f361])).

fof(f329,plain,
    ( spl6_28
  <=> m1_subset_1(k7_partfun1(sK0,sK3,sK5),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f352,plain,
    ( m1_subset_1(k1_funct_1(sK3,sK5),sK0)
    | ~ spl6_28
    | ~ spl6_31 ),
    inference(superposition,[],[f331,f346])).

fof(f331,plain,
    ( m1_subset_1(k7_partfun1(sK0,sK3,sK5),sK0)
    | ~ spl6_28 ),
    inference(avatar_component_clause,[],[f329])).

fof(f347,plain,
    ( spl6_31
    | ~ spl6_2
    | spl6_3
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_27 ),
    inference(avatar_split_clause,[],[f321,f309,f127,f117,f91,f81,f76,f344])).

fof(f321,plain,
    ( k7_partfun1(sK0,sK3,sK5) = k1_funct_1(sK3,sK5)
    | ~ spl6_2
    | spl6_3
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_27 ),
    inference(subsumption_resolution,[],[f320,f83])).

fof(f320,plain,
    ( k7_partfun1(sK0,sK3,sK5) = k1_funct_1(sK3,sK5)
    | v1_xboole_0(sK1)
    | ~ spl6_2
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_27 ),
    inference(subsumption_resolution,[],[f319,f93])).

fof(f319,plain,
    ( k7_partfun1(sK0,sK3,sK5) = k1_funct_1(sK3,sK5)
    | ~ m1_subset_1(sK5,sK1)
    | v1_xboole_0(sK1)
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_27 ),
    inference(subsumption_resolution,[],[f318,f129])).

fof(f318,plain,
    ( k7_partfun1(sK0,sK3,sK5) = k1_funct_1(sK3,sK5)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK5,sK1)
    | v1_xboole_0(sK1)
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_27 ),
    inference(subsumption_resolution,[],[f315,f119])).

fof(f315,plain,
    ( k7_partfun1(sK0,sK3,sK5) = k1_funct_1(sK3,sK5)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK5,sK1)
    | v1_xboole_0(sK1)
    | ~ spl6_2
    | ~ spl6_27 ),
    inference(superposition,[],[f311,f110])).

fof(f110,plain,
    ( ! [X10,X8,X9] :
        ( k3_funct_2(X8,X9,sK3,X10) = k1_funct_1(sK3,X10)
        | ~ v1_funct_2(sK3,X8,X9)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
        | ~ m1_subset_1(X10,X8)
        | v1_xboole_0(X8) )
    | ~ spl6_2 ),
    inference(resolution,[],[f78,f65])).

fof(f332,plain,
    ( spl6_28
    | ~ spl6_2
    | spl6_3
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_27 ),
    inference(avatar_split_clause,[],[f322,f309,f127,f117,f91,f81,f76,f329])).

fof(f322,plain,
    ( m1_subset_1(k7_partfun1(sK0,sK3,sK5),sK0)
    | ~ spl6_2
    | spl6_3
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_27 ),
    inference(subsumption_resolution,[],[f316,f93])).

fof(f316,plain,
    ( m1_subset_1(k7_partfun1(sK0,sK3,sK5),sK0)
    | ~ m1_subset_1(sK5,sK1)
    | ~ spl6_2
    | spl6_3
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_27 ),
    inference(superposition,[],[f225,f311])).

fof(f312,plain,
    ( spl6_27
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f291,f127,f117,f91,f86,f81,f76,f309])).

fof(f291,plain,
    ( k3_funct_2(sK1,sK0,sK3,sK5) = k7_partfun1(sK0,sK3,sK5)
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(resolution,[],[f254,f93])).

fof(f254,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | k3_funct_2(sK1,sK0,sK3,X0) = k7_partfun1(sK0,sK3,X0) )
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f253,f88])).

fof(f253,plain,
    ( ! [X0] :
        ( v1_xboole_0(sK0)
        | ~ m1_subset_1(X0,sK1)
        | k3_funct_2(sK1,sK0,sK3,X0) = k7_partfun1(sK0,sK3,X0) )
    | ~ spl6_2
    | spl6_3
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f252,f119])).

fof(f252,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK3,sK1,sK0)
        | v1_xboole_0(sK0)
        | ~ m1_subset_1(X0,sK1)
        | k3_funct_2(sK1,sK0,sK3,X0) = k7_partfun1(sK0,sK3,X0) )
    | ~ spl6_2
    | spl6_3
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f251,f83])).

fof(f251,plain,
    ( ! [X0] :
        ( v1_xboole_0(sK1)
        | ~ v1_funct_2(sK3,sK1,sK0)
        | v1_xboole_0(sK0)
        | ~ m1_subset_1(X0,sK1)
        | k3_funct_2(sK1,sK0,sK3,X0) = k7_partfun1(sK0,sK3,X0) )
    | ~ spl6_2
    | ~ spl6_9 ),
    inference(resolution,[],[f107,f129])).

fof(f107,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | v1_xboole_0(X1)
        | ~ v1_funct_2(sK3,X1,X0)
        | v1_xboole_0(X0)
        | ~ m1_subset_1(X2,X1)
        | k3_funct_2(X1,X0,sK3,X2) = k7_partfun1(X0,sK3,X2) )
    | ~ spl6_2 ),
    inference(resolution,[],[f78,f51])).

fof(f296,plain,
    ( spl6_26
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f290,f127,f122,f117,f76,f71,f293])).

fof(f290,plain,
    ( v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f289,f73])).

fof(f289,plain,
    ( ~ v1_funct_1(sK4)
    | v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4))
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(resolution,[],[f235,f124])).

fof(f235,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
        | ~ v1_funct_1(X0)
        | v1_funct_1(k8_funct_2(sK1,sK0,X1,sK3,X0)) )
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f234,f119])).

fof(f234,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(sK3,sK1,sK0)
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
        | v1_funct_1(k8_funct_2(sK1,sK0,X1,sK3,X0)) )
    | ~ spl6_2
    | ~ spl6_9 ),
    inference(resolution,[],[f111,f129])).

fof(f111,plain,
    ( ! [X14,X12,X13,X11] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))
        | ~ v1_funct_2(sK3,X11,X12)
        | ~ v1_funct_1(X13)
        | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X12,X14)))
        | v1_funct_1(k8_funct_2(X11,X12,X14,sK3,X13)) )
    | ~ spl6_2 ),
    inference(resolution,[],[f78,f66])).

fof(f66,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f277,plain,
    ( ~ spl6_1
    | ~ spl6_6
    | ~ spl6_8
    | spl6_25 ),
    inference(avatar_contradiction_clause,[],[f276])).

fof(f276,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_6
    | ~ spl6_8
    | spl6_25 ),
    inference(subsumption_resolution,[],[f275,f124])).

fof(f275,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl6_1
    | ~ spl6_6
    | spl6_25 ),
    inference(subsumption_resolution,[],[f274,f98])).

fof(f98,plain,
    ( v1_partfun1(sK4,sK0)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl6_6
  <=> v1_partfun1(sK4,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f274,plain,
    ( ~ v1_partfun1(sK4,sK0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl6_1
    | spl6_25 ),
    inference(resolution,[],[f271,f101])).

fof(f101,plain,
    ( ! [X4,X3] :
        ( v1_funct_2(sK4,X3,X4)
        | ~ v1_partfun1(sK4,X3)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
    | ~ spl6_1 ),
    inference(resolution,[],[f73,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_partfun1(X2,X0)
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).

fof(f271,plain,
    ( ~ v1_funct_2(sK4,sK0,sK2)
    | spl6_25 ),
    inference(avatar_component_clause,[],[f269])).

fof(f245,plain,
    ( spl6_22
    | ~ spl6_6
    | ~ spl6_11
    | ~ spl6_13 ),
    inference(avatar_split_clause,[],[f237,f163,f147,f96,f242])).

fof(f147,plain,
    ( spl6_11
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f163,plain,
    ( spl6_13
  <=> v4_relat_1(sK4,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f237,plain,
    ( sK0 = k1_relat_1(sK4)
    | ~ spl6_6
    | ~ spl6_11
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f236,f98])).

fof(f236,plain,
    ( sK0 = k1_relat_1(sK4)
    | ~ v1_partfun1(sK4,sK0)
    | ~ spl6_11
    | ~ spl6_13 ),
    inference(resolution,[],[f156,f165])).

fof(f165,plain,
    ( v4_relat_1(sK4,sK0)
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f163])).

fof(f156,plain,
    ( ! [X0] :
        ( ~ v4_relat_1(sK4,X0)
        | k1_relat_1(sK4) = X0
        | ~ v1_partfun1(sK4,X0) )
    | ~ spl6_11 ),
    inference(resolution,[],[f149,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0)
      | k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

fof(f149,plain,
    ( v1_relat_1(sK4)
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f147])).

fof(f231,plain,
    ( ~ spl6_21
    | spl6_4
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f226,f122,f96,f86,f228])).

fof(f226,plain,
    ( ~ v1_xboole_0(sK2)
    | spl6_4
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(resolution,[],[f218,f124])).

fof(f218,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
        | ~ v1_xboole_0(X0) )
    | spl6_4
    | ~ spl6_6 ),
    inference(resolution,[],[f115,f98])).

fof(f115,plain,
    ( ! [X0,X1] :
        ( ~ v1_partfun1(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
        | ~ v1_xboole_0(X0) )
    | spl6_4 ),
    inference(resolution,[],[f88,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X0)
      | ~ v1_xboole_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ~ v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_partfun1)).

fof(f201,plain,
    ( spl6_20
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f139,f127,f198])).

fof(f139,plain,
    ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3)
    | ~ spl6_9 ),
    inference(resolution,[],[f129,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f186,plain,
    ( spl6_17
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f133,f122,f183])).

fof(f133,plain,
    ( k1_relset_1(sK0,sK2,sK4) = k1_relat_1(sK4)
    | ~ spl6_8 ),
    inference(resolution,[],[f124,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f181,plain,
    ( spl6_16
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f137,f127,f178])).

fof(f137,plain,
    ( v5_relat_1(sK3,sK0)
    | ~ spl6_9 ),
    inference(resolution,[],[f129,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f166,plain,
    ( spl6_13
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f131,f122,f163])).

fof(f131,plain,
    ( v4_relat_1(sK4,sK0)
    | ~ spl6_8 ),
    inference(resolution,[],[f124,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f155,plain,
    ( spl6_12
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f140,f127,f152])).

fof(f140,plain,
    ( v1_relat_1(sK3)
    | ~ spl6_9 ),
    inference(resolution,[],[f129,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f150,plain,
    ( spl6_11
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f135,f122,f147])).

fof(f135,plain,
    ( v1_relat_1(sK4)
    | ~ spl6_8 ),
    inference(resolution,[],[f124,f58])).

fof(f145,plain,(
    ~ spl6_10 ),
    inference(avatar_split_clause,[],[f42,f142])).

fof(f142,plain,
    ( spl6_10
  <=> k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f42,plain,(
    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))
                      & v1_partfun1(X4,X0)
                      & m1_subset_1(X5,X1) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))
                      & v1_partfun1(X4,X0)
                      & m1_subset_1(X5,X1) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2,X3] :
                ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
                  & v1_funct_2(X3,X1,X0)
                  & v1_funct_1(X3) )
               => ! [X4] :
                    ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                      & v1_funct_1(X4) )
                   => ! [X5] :
                        ( m1_subset_1(X5,X1)
                       => ( v1_partfun1(X4,X0)
                         => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2,X3] :
              ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
                & v1_funct_2(X3,X1,X0)
                & v1_funct_1(X3) )
             => ! [X4] :
                  ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                    & v1_funct_1(X4) )
                 => ! [X5] :
                      ( m1_subset_1(X5,X1)
                     => ( v1_partfun1(X4,X0)
                       => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t193_funct_2)).

fof(f130,plain,(
    spl6_9 ),
    inference(avatar_split_clause,[],[f47,f127])).

fof(f47,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f125,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f44,f122])).

fof(f44,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f18])).

fof(f120,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f46,f117])).

fof(f46,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f99,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f41,f96])).

fof(f41,plain,(
    v1_partfun1(sK4,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f94,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f40,f91])).

fof(f40,plain,(
    m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f89,plain,(
    ~ spl6_4 ),
    inference(avatar_split_clause,[],[f49,f86])).

fof(f49,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f84,plain,(
    ~ spl6_3 ),
    inference(avatar_split_clause,[],[f48,f81])).

fof(f48,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f79,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f45,f76])).

fof(f45,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f74,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f43,f71])).

fof(f43,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:40:46 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.46  % (11427)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.48  % (11419)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (11433)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.48  % (11423)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.48  % (11432)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.48  % (11421)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.49  % (11436)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.49  % (11425)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.49  % (11419)Refutation not found, incomplete strategy% (11419)------------------------------
% 0.21/0.49  % (11419)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (11419)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (11419)Memory used [KB]: 10618
% 0.21/0.49  % (11419)Time elapsed: 0.087 s
% 0.21/0.49  % (11419)------------------------------
% 0.21/0.49  % (11419)------------------------------
% 0.21/0.49  % (11422)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.49  % (11430)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (11429)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.49  % (11428)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.50  % (11418)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (11421)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % (11426)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.50  % (11437)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.50  % (11431)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.51  % (11420)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.51  % (11431)Refutation not found, incomplete strategy% (11431)------------------------------
% 0.21/0.51  % (11431)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (11438)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.51  % (11435)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f646,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f74,f79,f84,f89,f94,f99,f120,f125,f130,f145,f150,f155,f166,f181,f186,f201,f231,f245,f277,f296,f312,f332,f347,f364,f440,f461,f464,f491,f530,f569,f595,f633,f644,f645])).
% 0.21/0.51  fof(f645,plain,(
% 0.21/0.51    k3_funct_2(sK1,sK0,sK3,sK5) != k7_partfun1(sK0,sK3,sK5) | k7_partfun1(sK0,sK3,sK5) != k1_funct_1(sK3,sK5) | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5))),
% 0.21/0.51    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.51  fof(f644,plain,(
% 0.21/0.51    spl6_64 | spl6_3 | ~spl6_5 | ~spl6_26 | ~spl6_43 | ~spl6_49 | ~spl6_63),
% 0.21/0.51    inference(avatar_split_clause,[],[f638,f623,f488,f437,f293,f91,f81,f641])).
% 0.21/0.51  fof(f641,plain,(
% 0.21/0.51    spl6_64 <=> k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_64])])).
% 0.21/0.51  fof(f81,plain,(
% 0.21/0.51    spl6_3 <=> v1_xboole_0(sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.21/0.51  fof(f91,plain,(
% 0.21/0.51    spl6_5 <=> m1_subset_1(sK5,sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.21/0.51  fof(f293,plain,(
% 0.21/0.51    spl6_26 <=> v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).
% 0.21/0.51  fof(f437,plain,(
% 0.21/0.51    spl6_43 <=> m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).
% 0.21/0.51  fof(f488,plain,(
% 0.21/0.51    spl6_49 <=> k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_49])])).
% 0.21/0.51  fof(f623,plain,(
% 0.21/0.51    spl6_63 <=> v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_63])])).
% 0.21/0.51  fof(f638,plain,(
% 0.21/0.51    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | (spl6_3 | ~spl6_5 | ~spl6_26 | ~spl6_43 | ~spl6_49 | ~spl6_63)),
% 0.21/0.51    inference(forward_demodulation,[],[f637,f490])).
% 0.21/0.51  fof(f490,plain,(
% 0.21/0.51    k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | ~spl6_49),
% 0.21/0.51    inference(avatar_component_clause,[],[f488])).
% 0.21/0.51  fof(f637,plain,(
% 0.21/0.51    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) | (spl6_3 | ~spl6_5 | ~spl6_26 | ~spl6_43 | ~spl6_63)),
% 0.21/0.51    inference(resolution,[],[f636,f93])).
% 0.21/0.51  fof(f93,plain,(
% 0.21/0.51    m1_subset_1(sK5,sK1) | ~spl6_5),
% 0.21/0.51    inference(avatar_component_clause,[],[f91])).
% 0.21/0.51  fof(f636,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(X0,sK1) | k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0)) ) | (spl6_3 | ~spl6_26 | ~spl6_43 | ~spl6_63)),
% 0.21/0.51    inference(subsumption_resolution,[],[f601,f624])).
% 0.21/0.51  fof(f624,plain,(
% 0.21/0.51    v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2) | ~spl6_63),
% 0.21/0.51    inference(avatar_component_clause,[],[f623])).
% 0.21/0.51  % (11438)Refutation not found, incomplete strategy% (11438)------------------------------
% 0.21/0.51  % (11438)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (11438)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (11438)Memory used [KB]: 10618
% 0.21/0.51  % (11438)Time elapsed: 0.090 s
% 0.21/0.51  % (11438)------------------------------
% 0.21/0.51  % (11438)------------------------------
% 0.21/0.51  % (11434)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.52  % (11424)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.52  % (11431)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (11431)Memory used [KB]: 1791
% 0.21/0.52  % (11431)Time elapsed: 0.091 s
% 0.21/0.52  % (11431)------------------------------
% 0.21/0.52  % (11431)------------------------------
% 0.21/0.52  fof(f601,plain,(
% 0.21/0.52    ( ! [X0] : (~v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2) | ~m1_subset_1(X0,sK1) | k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0)) ) | (spl6_3 | ~spl6_26 | ~spl6_43)),
% 0.21/0.52    inference(subsumption_resolution,[],[f600,f83])).
% 0.21/0.52  fof(f83,plain,(
% 0.21/0.52    ~v1_xboole_0(sK1) | spl6_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f81])).
% 0.21/0.52  fof(f600,plain,(
% 0.21/0.52    ( ! [X0] : (~v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2) | v1_xboole_0(sK1) | ~m1_subset_1(X0,sK1) | k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0)) ) | (~spl6_26 | ~spl6_43)),
% 0.21/0.52    inference(resolution,[],[f301,f439])).
% 0.21/0.52  fof(f439,plain,(
% 0.21/0.52    m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl6_43),
% 0.21/0.52    inference(avatar_component_clause,[],[f437])).
% 0.21/0.52  fof(f301,plain,(
% 0.21/0.52    ( ! [X10,X8,X9] : (~m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(X8,X9))) | ~v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X8,X9) | v1_xboole_0(X8) | ~m1_subset_1(X10,X8) | k3_funct_2(X8,X9,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X10) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X10)) ) | ~spl6_26),
% 0.21/0.52    inference(resolution,[],[f295,f65])).
% 0.21/0.52  fof(f65,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | v1_xboole_0(X0) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,X0) | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f37])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 0.21/0.52    inference(flattening,[],[f36])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).
% 0.21/0.52  fof(f295,plain,(
% 0.21/0.52    v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4)) | ~spl6_26),
% 0.21/0.52    inference(avatar_component_clause,[],[f293])).
% 0.21/0.52  fof(f633,plain,(
% 0.21/0.52    ~spl6_1 | ~spl6_2 | ~spl6_7 | ~spl6_8 | ~spl6_9 | spl6_63),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f632])).
% 0.21/0.52  fof(f632,plain,(
% 0.21/0.52    $false | (~spl6_1 | ~spl6_2 | ~spl6_7 | ~spl6_8 | ~spl6_9 | spl6_63)),
% 0.21/0.52    inference(subsumption_resolution,[],[f631,f119])).
% 0.21/0.52  fof(f119,plain,(
% 0.21/0.52    v1_funct_2(sK3,sK1,sK0) | ~spl6_7),
% 0.21/0.52    inference(avatar_component_clause,[],[f117])).
% 0.21/0.52  fof(f117,plain,(
% 0.21/0.52    spl6_7 <=> v1_funct_2(sK3,sK1,sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.21/0.52  fof(f631,plain,(
% 0.21/0.52    ~v1_funct_2(sK3,sK1,sK0) | (~spl6_1 | ~spl6_2 | ~spl6_8 | ~spl6_9 | spl6_63)),
% 0.21/0.52    inference(subsumption_resolution,[],[f630,f124])).
% 0.21/0.52  fof(f124,plain,(
% 0.21/0.52    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~spl6_8),
% 0.21/0.52    inference(avatar_component_clause,[],[f122])).
% 0.21/0.52  fof(f122,plain,(
% 0.21/0.52    spl6_8 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.21/0.52  fof(f630,plain,(
% 0.21/0.52    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK1,sK0) | (~spl6_1 | ~spl6_2 | ~spl6_9 | spl6_63)),
% 0.21/0.52    inference(subsumption_resolution,[],[f629,f73])).
% 0.21/0.52  fof(f73,plain,(
% 0.21/0.52    v1_funct_1(sK4) | ~spl6_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f71])).
% 0.21/0.52  fof(f71,plain,(
% 0.21/0.52    spl6_1 <=> v1_funct_1(sK4)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.52  fof(f629,plain,(
% 0.21/0.52    ~v1_funct_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK1,sK0) | (~spl6_2 | ~spl6_9 | spl6_63)),
% 0.21/0.52    inference(subsumption_resolution,[],[f627,f129])).
% 0.21/0.52  fof(f129,plain,(
% 0.21/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl6_9),
% 0.21/0.52    inference(avatar_component_clause,[],[f127])).
% 0.21/0.52  fof(f127,plain,(
% 0.21/0.52    spl6_9 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.21/0.52  fof(f627,plain,(
% 0.21/0.52    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK1,sK0) | (~spl6_2 | spl6_63)),
% 0.21/0.52    inference(resolution,[],[f625,f112])).
% 0.21/0.52  fof(f112,plain,(
% 0.21/0.52    ( ! [X17,X15,X18,X16] : (v1_funct_2(k8_funct_2(X15,X16,X18,sK3,X17),X15,X18) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X15,X16))) | ~v1_funct_1(X17) | ~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X16,X18))) | ~v1_funct_2(sK3,X15,X16)) ) | ~spl6_2),
% 0.21/0.52    inference(resolution,[],[f78,f67])).
% 0.21/0.52  fof(f67,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f39])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2) & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.21/0.52    inference(flattening,[],[f38])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2) & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.21/0.52    inference(ennf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2) & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_funct_2)).
% 0.21/0.52  fof(f78,plain,(
% 0.21/0.52    v1_funct_1(sK3) | ~spl6_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f76])).
% 0.21/0.52  fof(f76,plain,(
% 0.21/0.52    spl6_2 <=> v1_funct_1(sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.52  fof(f625,plain,(
% 0.21/0.52    ~v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2) | spl6_63),
% 0.21/0.52    inference(avatar_component_clause,[],[f623])).
% 0.21/0.52  fof(f595,plain,(
% 0.21/0.52    spl6_59 | ~spl6_1 | spl6_4 | ~spl6_8 | ~spl6_25 | ~spl6_33 | ~spl6_57),
% 0.21/0.52    inference(avatar_split_clause,[],[f576,f566,f361,f269,f122,f86,f71,f592])).
% 0.21/0.52  fof(f592,plain,(
% 0.21/0.52    spl6_59 <=> k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_59])])).
% 0.21/0.52  fof(f86,plain,(
% 0.21/0.52    spl6_4 <=> v1_xboole_0(sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.21/0.52  fof(f269,plain,(
% 0.21/0.52    spl6_25 <=> v1_funct_2(sK4,sK0,sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).
% 0.21/0.52  fof(f361,plain,(
% 0.21/0.52    spl6_33 <=> m1_subset_1(k1_funct_1(sK3,sK5),sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).
% 0.21/0.52  fof(f566,plain,(
% 0.21/0.52    spl6_57 <=> k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,sK5)) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_57])])).
% 0.21/0.52  fof(f576,plain,(
% 0.21/0.52    k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | (~spl6_1 | spl6_4 | ~spl6_8 | ~spl6_25 | ~spl6_33 | ~spl6_57)),
% 0.21/0.52    inference(subsumption_resolution,[],[f575,f88])).
% 0.21/0.52  fof(f88,plain,(
% 0.21/0.52    ~v1_xboole_0(sK0) | spl6_4),
% 0.21/0.52    inference(avatar_component_clause,[],[f86])).
% 0.21/0.52  fof(f575,plain,(
% 0.21/0.52    k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | v1_xboole_0(sK0) | (~spl6_1 | ~spl6_8 | ~spl6_25 | ~spl6_33 | ~spl6_57)),
% 0.21/0.52    inference(subsumption_resolution,[],[f574,f363])).
% 0.21/0.52  fof(f363,plain,(
% 0.21/0.52    m1_subset_1(k1_funct_1(sK3,sK5),sK0) | ~spl6_33),
% 0.21/0.52    inference(avatar_component_clause,[],[f361])).
% 0.21/0.52  fof(f574,plain,(
% 0.21/0.52    k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | ~m1_subset_1(k1_funct_1(sK3,sK5),sK0) | v1_xboole_0(sK0) | (~spl6_1 | ~spl6_8 | ~spl6_25 | ~spl6_57)),
% 0.21/0.52    inference(subsumption_resolution,[],[f573,f124])).
% 0.21/0.52  fof(f573,plain,(
% 0.21/0.52    k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~m1_subset_1(k1_funct_1(sK3,sK5),sK0) | v1_xboole_0(sK0) | (~spl6_1 | ~spl6_25 | ~spl6_57)),
% 0.21/0.52    inference(subsumption_resolution,[],[f570,f270])).
% 0.21/0.52  fof(f270,plain,(
% 0.21/0.52    v1_funct_2(sK4,sK0,sK2) | ~spl6_25),
% 0.21/0.52    inference(avatar_component_clause,[],[f269])).
% 0.21/0.52  fof(f570,plain,(
% 0.21/0.52    k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | ~v1_funct_2(sK4,sK0,sK2) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~m1_subset_1(k1_funct_1(sK3,sK5),sK0) | v1_xboole_0(sK0) | (~spl6_1 | ~spl6_57)),
% 0.21/0.52    inference(superposition,[],[f568,f103])).
% 0.21/0.52  fof(f103,plain,(
% 0.21/0.52    ( ! [X10,X8,X9] : (k3_funct_2(X8,X9,sK4,X10) = k1_funct_1(sK4,X10) | ~v1_funct_2(sK4,X8,X9) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X8,X9))) | ~m1_subset_1(X10,X8) | v1_xboole_0(X8)) ) | ~spl6_1),
% 0.21/0.52    inference(resolution,[],[f73,f65])).
% 0.21/0.52  fof(f568,plain,(
% 0.21/0.52    k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,sK5)) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) | ~spl6_57),
% 0.21/0.52    inference(avatar_component_clause,[],[f566])).
% 0.21/0.52  fof(f569,plain,(
% 0.21/0.52    spl6_57 | ~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | ~spl6_5 | ~spl6_7 | ~spl6_8 | ~spl6_9 | spl6_21 | ~spl6_25 | ~spl6_27 | ~spl6_31),
% 0.21/0.52    inference(avatar_split_clause,[],[f448,f344,f309,f269,f228,f127,f122,f117,f91,f86,f81,f76,f71,f566])).
% 0.21/0.52  fof(f228,plain,(
% 0.21/0.52    spl6_21 <=> v1_xboole_0(sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 0.21/0.52  fof(f309,plain,(
% 0.21/0.52    spl6_27 <=> k3_funct_2(sK1,sK0,sK3,sK5) = k7_partfun1(sK0,sK3,sK5)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).
% 0.21/0.52  fof(f344,plain,(
% 0.21/0.52    spl6_31 <=> k7_partfun1(sK0,sK3,sK5) = k1_funct_1(sK3,sK5)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).
% 0.21/0.52  fof(f448,plain,(
% 0.21/0.52    k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,sK5)) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | ~spl6_5 | ~spl6_7 | ~spl6_8 | ~spl6_9 | spl6_21 | ~spl6_25 | ~spl6_27 | ~spl6_31)),
% 0.21/0.52    inference(forward_demodulation,[],[f447,f346])).
% 0.21/0.52  fof(f346,plain,(
% 0.21/0.52    k7_partfun1(sK0,sK3,sK5) = k1_funct_1(sK3,sK5) | ~spl6_31),
% 0.21/0.52    inference(avatar_component_clause,[],[f344])).
% 0.21/0.52  fof(f447,plain,(
% 0.21/0.52    k3_funct_2(sK0,sK2,sK4,k7_partfun1(sK0,sK3,sK5)) = k7_partfun1(sK2,sK4,k7_partfun1(sK0,sK3,sK5)) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | ~spl6_5 | ~spl6_7 | ~spl6_8 | ~spl6_9 | spl6_21 | ~spl6_25 | ~spl6_27)),
% 0.21/0.52    inference(forward_demodulation,[],[f446,f311])).
% 0.21/0.52  fof(f311,plain,(
% 0.21/0.52    k3_funct_2(sK1,sK0,sK3,sK5) = k7_partfun1(sK0,sK3,sK5) | ~spl6_27),
% 0.21/0.52    inference(avatar_component_clause,[],[f309])).
% 0.21/0.52  fof(f446,plain,(
% 0.21/0.52    k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) = k3_funct_2(sK0,sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | ~spl6_5 | ~spl6_7 | ~spl6_8 | ~spl6_9 | spl6_21 | ~spl6_25)),
% 0.21/0.52    inference(resolution,[],[f306,f93])).
% 0.21/0.52  fof(f306,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(X0,sK1) | k3_funct_2(sK0,sK2,sK4,k3_funct_2(sK1,sK0,sK3,X0)) = k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,X0))) ) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | ~spl6_7 | ~spl6_8 | ~spl6_9 | spl6_21 | ~spl6_25)),
% 0.21/0.52    inference(resolution,[],[f305,f225])).
% 0.21/0.52  fof(f225,plain,(
% 0.21/0.52    ( ! [X0] : (m1_subset_1(k3_funct_2(sK1,sK0,sK3,X0),sK0) | ~m1_subset_1(X0,sK1)) ) | (~spl6_2 | spl6_3 | ~spl6_7 | ~spl6_9)),
% 0.21/0.52    inference(subsumption_resolution,[],[f224,f83])).
% 0.21/0.52  fof(f224,plain,(
% 0.21/0.52    ( ! [X0] : (v1_xboole_0(sK1) | ~m1_subset_1(X0,sK1) | m1_subset_1(k3_funct_2(sK1,sK0,sK3,X0),sK0)) ) | (~spl6_2 | ~spl6_7 | ~spl6_9)),
% 0.21/0.52    inference(subsumption_resolution,[],[f223,f119])).
% 0.21/0.52  fof(f223,plain,(
% 0.21/0.52    ( ! [X0] : (~v1_funct_2(sK3,sK1,sK0) | v1_xboole_0(sK1) | ~m1_subset_1(X0,sK1) | m1_subset_1(k3_funct_2(sK1,sK0,sK3,X0),sK0)) ) | (~spl6_2 | ~spl6_9)),
% 0.21/0.52    inference(resolution,[],[f109,f129])).
% 0.21/0.52  fof(f109,plain,(
% 0.21/0.52    ( ! [X6,X7,X5] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | ~v1_funct_2(sK3,X5,X6) | v1_xboole_0(X5) | ~m1_subset_1(X7,X5) | m1_subset_1(k3_funct_2(X5,X6,sK3,X7),X6)) ) | ~spl6_2),
% 0.21/0.52    inference(resolution,[],[f78,f64])).
% 0.21/0.52  fof(f64,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | v1_xboole_0(X0) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,X0) | m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f35])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 0.21/0.52    inference(flattening,[],[f34])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_funct_2)).
% 0.21/0.52  fof(f305,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(X0,sK0) | k3_funct_2(sK0,sK2,sK4,X0) = k7_partfun1(sK2,sK4,X0)) ) | (~spl6_1 | spl6_4 | ~spl6_8 | spl6_21 | ~spl6_25)),
% 0.21/0.52    inference(subsumption_resolution,[],[f240,f270])).
% 0.21/0.52  fof(f240,plain,(
% 0.21/0.52    ( ! [X0] : (~v1_funct_2(sK4,sK0,sK2) | ~m1_subset_1(X0,sK0) | k3_funct_2(sK0,sK2,sK4,X0) = k7_partfun1(sK2,sK4,X0)) ) | (~spl6_1 | spl6_4 | ~spl6_8 | spl6_21)),
% 0.21/0.52    inference(subsumption_resolution,[],[f239,f230])).
% 0.21/0.52  fof(f230,plain,(
% 0.21/0.52    ~v1_xboole_0(sK2) | spl6_21),
% 0.21/0.52    inference(avatar_component_clause,[],[f228])).
% 0.21/0.52  fof(f239,plain,(
% 0.21/0.52    ( ! [X0] : (~v1_funct_2(sK4,sK0,sK2) | v1_xboole_0(sK2) | ~m1_subset_1(X0,sK0) | k3_funct_2(sK0,sK2,sK4,X0) = k7_partfun1(sK2,sK4,X0)) ) | (~spl6_1 | spl6_4 | ~spl6_8)),
% 0.21/0.52    inference(subsumption_resolution,[],[f238,f88])).
% 0.21/0.52  fof(f238,plain,(
% 0.21/0.52    ( ! [X0] : (v1_xboole_0(sK0) | ~v1_funct_2(sK4,sK0,sK2) | v1_xboole_0(sK2) | ~m1_subset_1(X0,sK0) | k3_funct_2(sK0,sK2,sK4,X0) = k7_partfun1(sK2,sK4,X0)) ) | (~spl6_1 | ~spl6_8)),
% 0.21/0.52    inference(resolution,[],[f100,f124])).
% 0.21/0.52  fof(f100,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_xboole_0(X1) | ~v1_funct_2(sK4,X1,X0) | v1_xboole_0(X0) | ~m1_subset_1(X2,X1) | k3_funct_2(X1,X0,sK4,X2) = k7_partfun1(X0,sK4,X2)) ) | ~spl6_1),
% 0.21/0.52    inference(resolution,[],[f73,f51])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | v1_xboole_0(X1) | v1_xboole_0(X0) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,X0) | k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3) | ~m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.21/0.52    inference(flattening,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3) | ~m1_subset_1(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,axiom,(
% 0.21/0.52    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,X0) => k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3)))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t176_funct_2)).
% 0.21/0.52  fof(f530,plain,(
% 0.21/0.52    spl6_3 | ~spl6_29),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f529])).
% 0.21/0.52  fof(f529,plain,(
% 0.21/0.52    $false | (spl6_3 | ~spl6_29)),
% 0.21/0.52    inference(subsumption_resolution,[],[f505,f50])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    v1_xboole_0(k1_xboole_0)),
% 0.21/0.52    inference(cnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    v1_xboole_0(k1_xboole_0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.52  fof(f505,plain,(
% 0.21/0.52    ~v1_xboole_0(k1_xboole_0) | (spl6_3 | ~spl6_29)),
% 0.21/0.52    inference(superposition,[],[f83,f336])).
% 0.21/0.52  fof(f336,plain,(
% 0.21/0.52    k1_xboole_0 = sK1 | ~spl6_29),
% 0.21/0.52    inference(avatar_component_clause,[],[f334])).
% 0.21/0.52  fof(f334,plain,(
% 0.21/0.52    spl6_29 <=> k1_xboole_0 = sK1),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).
% 0.21/0.52  fof(f491,plain,(
% 0.21/0.52    spl6_49 | ~spl6_5 | ~spl6_45),
% 0.21/0.52    inference(avatar_split_clause,[],[f469,f455,f91,f488])).
% 0.21/0.52  fof(f455,plain,(
% 0.21/0.52    spl6_45 <=> ! [X0] : (~m1_subset_1(X0,sK1) | k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).
% 0.21/0.52  fof(f469,plain,(
% 0.21/0.52    k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | (~spl6_5 | ~spl6_45)),
% 0.21/0.52    inference(resolution,[],[f456,f93])).
% 0.21/0.52  fof(f456,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(X0,sK1) | k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))) ) | ~spl6_45),
% 0.21/0.52    inference(avatar_component_clause,[],[f455])).
% 0.21/0.52  fof(f464,plain,(
% 0.21/0.52    ~spl6_12 | ~spl6_16 | spl6_46),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f463])).
% 0.21/0.52  fof(f463,plain,(
% 0.21/0.52    $false | (~spl6_12 | ~spl6_16 | spl6_46)),
% 0.21/0.52    inference(subsumption_resolution,[],[f462,f180])).
% 0.21/0.52  fof(f180,plain,(
% 0.21/0.52    v5_relat_1(sK3,sK0) | ~spl6_16),
% 0.21/0.52    inference(avatar_component_clause,[],[f178])).
% 0.21/0.52  fof(f178,plain,(
% 0.21/0.52    spl6_16 <=> v5_relat_1(sK3,sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.21/0.52  fof(f462,plain,(
% 0.21/0.52    ~v5_relat_1(sK3,sK0) | (~spl6_12 | spl6_46)),
% 0.21/0.52    inference(resolution,[],[f460,f161])).
% 0.21/0.52  fof(f161,plain,(
% 0.21/0.52    ( ! [X2] : (r1_tarski(k2_relat_1(sK3),X2) | ~v5_relat_1(sK3,X2)) ) | ~spl6_12),
% 0.21/0.52    inference(resolution,[],[f154,f53])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.21/0.52  fof(f154,plain,(
% 0.21/0.52    v1_relat_1(sK3) | ~spl6_12),
% 0.21/0.52    inference(avatar_component_clause,[],[f152])).
% 0.21/0.52  fof(f152,plain,(
% 0.21/0.52    spl6_12 <=> v1_relat_1(sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.21/0.52  fof(f460,plain,(
% 0.21/0.52    ~r1_tarski(k2_relat_1(sK3),sK0) | spl6_46),
% 0.21/0.52    inference(avatar_component_clause,[],[f458])).
% 0.21/0.52  fof(f458,plain,(
% 0.21/0.52    spl6_46 <=> r1_tarski(k2_relat_1(sK3),sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).
% 0.21/0.52  fof(f461,plain,(
% 0.21/0.52    spl6_45 | ~spl6_46 | ~spl6_1 | ~spl6_2 | spl6_4 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_17 | ~spl6_20 | ~spl6_22 | spl6_29),
% 0.21/0.52    inference(avatar_split_clause,[],[f357,f334,f242,f198,f183,f127,f122,f117,f86,f76,f71,f458,f455])).
% 0.21/0.52  fof(f183,plain,(
% 0.21/0.52    spl6_17 <=> k1_relset_1(sK0,sK2,sK4) = k1_relat_1(sK4)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 0.21/0.52  fof(f198,plain,(
% 0.21/0.52    spl6_20 <=> k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 0.21/0.52  fof(f242,plain,(
% 0.21/0.52    spl6_22 <=> sK0 = k1_relat_1(sK4)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 0.21/0.52  fof(f357,plain,(
% 0.21/0.52    ( ! [X0] : (~r1_tarski(k2_relat_1(sK3),sK0) | ~m1_subset_1(X0,sK1) | k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))) ) | (~spl6_1 | ~spl6_2 | spl6_4 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_17 | ~spl6_20 | ~spl6_22 | spl6_29)),
% 0.21/0.52    inference(subsumption_resolution,[],[f356,f335])).
% 0.21/0.52  fof(f335,plain,(
% 0.21/0.52    k1_xboole_0 != sK1 | spl6_29),
% 0.21/0.52    inference(avatar_component_clause,[],[f334])).
% 0.21/0.52  fof(f356,plain,(
% 0.21/0.52    ( ! [X0] : (~r1_tarski(k2_relat_1(sK3),sK0) | ~m1_subset_1(X0,sK1) | k1_xboole_0 = sK1 | k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))) ) | (~spl6_1 | ~spl6_2 | spl6_4 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_17 | ~spl6_20 | ~spl6_22)),
% 0.21/0.52    inference(subsumption_resolution,[],[f355,f129])).
% 0.21/0.52  fof(f355,plain,(
% 0.21/0.52    ( ! [X0] : (~r1_tarski(k2_relat_1(sK3),sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~m1_subset_1(X0,sK1) | k1_xboole_0 = sK1 | k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))) ) | (~spl6_1 | ~spl6_2 | spl6_4 | ~spl6_7 | ~spl6_8 | ~spl6_17 | ~spl6_20 | ~spl6_22)),
% 0.21/0.52    inference(subsumption_resolution,[],[f354,f119])).
% 0.21/0.52  fof(f354,plain,(
% 0.21/0.52    ( ! [X0] : (~r1_tarski(k2_relat_1(sK3),sK0) | ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~m1_subset_1(X0,sK1) | k1_xboole_0 = sK1 | k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))) ) | (~spl6_1 | ~spl6_2 | spl6_4 | ~spl6_8 | ~spl6_17 | ~spl6_20 | ~spl6_22)),
% 0.21/0.52    inference(subsumption_resolution,[],[f353,f78])).
% 0.21/0.52  fof(f353,plain,(
% 0.21/0.52    ( ! [X0] : (~r1_tarski(k2_relat_1(sK3),sK0) | ~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~m1_subset_1(X0,sK1) | k1_xboole_0 = sK1 | k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))) ) | (~spl6_1 | spl6_4 | ~spl6_8 | ~spl6_17 | ~spl6_20 | ~spl6_22)),
% 0.21/0.52    inference(superposition,[],[f342,f200])).
% 0.21/0.52  fof(f200,plain,(
% 0.21/0.52    k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) | ~spl6_20),
% 0.21/0.52    inference(avatar_component_clause,[],[f198])).
% 0.21/0.52  fof(f342,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r1_tarski(k2_relset_1(X0,sK0,X1),sK0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) | ~m1_subset_1(X2,X0) | k1_xboole_0 = X0 | k1_funct_1(k8_funct_2(X0,sK0,sK2,X1,sK4),X2) = k1_funct_1(sK4,k1_funct_1(X1,X2))) ) | (~spl6_1 | spl6_4 | ~spl6_8 | ~spl6_17 | ~spl6_22)),
% 0.21/0.52    inference(forward_demodulation,[],[f205,f244])).
% 0.21/0.52  fof(f244,plain,(
% 0.21/0.52    sK0 = k1_relat_1(sK4) | ~spl6_22),
% 0.21/0.52    inference(avatar_component_clause,[],[f242])).
% 0.21/0.52  fof(f205,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r1_tarski(k2_relset_1(X0,sK0,X1),k1_relat_1(sK4)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) | ~m1_subset_1(X2,X0) | k1_xboole_0 = X0 | k1_funct_1(k8_funct_2(X0,sK0,sK2,X1,sK4),X2) = k1_funct_1(sK4,k1_funct_1(X1,X2))) ) | (~spl6_1 | spl6_4 | ~spl6_8 | ~spl6_17)),
% 0.21/0.52    inference(subsumption_resolution,[],[f204,f88])).
% 0.21/0.52  fof(f204,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r1_tarski(k2_relset_1(X0,sK0,X1),k1_relat_1(sK4)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) | ~m1_subset_1(X2,X0) | v1_xboole_0(sK0) | k1_xboole_0 = X0 | k1_funct_1(k8_funct_2(X0,sK0,sK2,X1,sK4),X2) = k1_funct_1(sK4,k1_funct_1(X1,X2))) ) | (~spl6_1 | ~spl6_8 | ~spl6_17)),
% 0.21/0.52    inference(subsumption_resolution,[],[f203,f124])).
% 0.21/0.52  fof(f203,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r1_tarski(k2_relset_1(X0,sK0,X1),k1_relat_1(sK4)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~m1_subset_1(X2,X0) | v1_xboole_0(sK0) | k1_xboole_0 = X0 | k1_funct_1(k8_funct_2(X0,sK0,sK2,X1,sK4),X2) = k1_funct_1(sK4,k1_funct_1(X1,X2))) ) | (~spl6_1 | ~spl6_17)),
% 0.21/0.52    inference(subsumption_resolution,[],[f202,f73])).
% 0.21/0.52  fof(f202,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r1_tarski(k2_relset_1(X0,sK0,X1),k1_relat_1(sK4)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~m1_subset_1(X2,X0) | v1_xboole_0(sK0) | k1_xboole_0 = X0 | k1_funct_1(k8_funct_2(X0,sK0,sK2,X1,sK4),X2) = k1_funct_1(sK4,k1_funct_1(X1,X2))) ) | ~spl6_17),
% 0.21/0.52    inference(superposition,[],[f57,f185])).
% 0.21/0.52  fof(f185,plain,(
% 0.21/0.52    k1_relset_1(sK0,sK2,sK4) = k1_relat_1(sK4) | ~spl6_17),
% 0.21/0.52    inference(avatar_component_clause,[],[f183])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~m1_subset_1(X5,X1) | v1_xboole_0(X2) | k1_xboole_0 = X1 | k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3)) | v1_xboole_0(X2))),
% 0.21/0.52    inference(flattening,[],[f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3))) | v1_xboole_0(X2))),
% 0.21/0.52    inference(ennf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t185_funct_2)).
% 0.21/0.52  fof(f440,plain,(
% 0.21/0.52    spl6_43 | ~spl6_1 | ~spl6_2 | ~spl6_7 | ~spl6_8 | ~spl6_9),
% 0.21/0.52    inference(avatar_split_clause,[],[f314,f127,f122,f117,f76,f71,f437])).
% 0.21/0.52  fof(f314,plain,(
% 0.21/0.52    m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | (~spl6_1 | ~spl6_2 | ~spl6_7 | ~spl6_8 | ~spl6_9)),
% 0.21/0.52    inference(subsumption_resolution,[],[f313,f73])).
% 0.21/0.52  fof(f313,plain,(
% 0.21/0.52    ~v1_funct_1(sK4) | m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | (~spl6_2 | ~spl6_7 | ~spl6_8 | ~spl6_9)),
% 0.21/0.52    inference(resolution,[],[f259,f124])).
% 0.21/0.52  fof(f259,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) | ~v1_funct_1(X0) | m1_subset_1(k8_funct_2(sK1,sK0,X1,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))) ) | (~spl6_2 | ~spl6_7 | ~spl6_9)),
% 0.21/0.52    inference(subsumption_resolution,[],[f258,f119])).
% 0.21/0.52  fof(f258,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) | m1_subset_1(k8_funct_2(sK1,sK0,X1,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))) ) | (~spl6_2 | ~spl6_9)),
% 0.21/0.52    inference(resolution,[],[f113,f129])).
% 0.21/0.52  fof(f113,plain,(
% 0.21/0.52    ( ! [X21,X19,X22,X20] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X19,X20))) | ~v1_funct_2(sK3,X19,X20) | ~v1_funct_1(X21) | ~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X20,X22))) | m1_subset_1(k8_funct_2(X19,X20,X22,sK3,X21),k1_zfmisc_1(k2_zfmisc_1(X19,X22)))) ) | ~spl6_2),
% 0.21/0.52    inference(resolution,[],[f78,f68])).
% 0.21/0.52  fof(f68,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f39])).
% 0.21/0.52  fof(f364,plain,(
% 0.21/0.52    spl6_33 | ~spl6_28 | ~spl6_31),
% 0.21/0.52    inference(avatar_split_clause,[],[f352,f344,f329,f361])).
% 0.21/0.52  fof(f329,plain,(
% 0.21/0.52    spl6_28 <=> m1_subset_1(k7_partfun1(sK0,sK3,sK5),sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).
% 0.21/0.52  fof(f352,plain,(
% 0.21/0.52    m1_subset_1(k1_funct_1(sK3,sK5),sK0) | (~spl6_28 | ~spl6_31)),
% 0.21/0.52    inference(superposition,[],[f331,f346])).
% 0.21/0.52  fof(f331,plain,(
% 0.21/0.52    m1_subset_1(k7_partfun1(sK0,sK3,sK5),sK0) | ~spl6_28),
% 0.21/0.52    inference(avatar_component_clause,[],[f329])).
% 0.21/0.52  fof(f347,plain,(
% 0.21/0.52    spl6_31 | ~spl6_2 | spl6_3 | ~spl6_5 | ~spl6_7 | ~spl6_9 | ~spl6_27),
% 0.21/0.52    inference(avatar_split_clause,[],[f321,f309,f127,f117,f91,f81,f76,f344])).
% 0.21/0.52  fof(f321,plain,(
% 0.21/0.52    k7_partfun1(sK0,sK3,sK5) = k1_funct_1(sK3,sK5) | (~spl6_2 | spl6_3 | ~spl6_5 | ~spl6_7 | ~spl6_9 | ~spl6_27)),
% 0.21/0.52    inference(subsumption_resolution,[],[f320,f83])).
% 0.21/0.52  fof(f320,plain,(
% 0.21/0.52    k7_partfun1(sK0,sK3,sK5) = k1_funct_1(sK3,sK5) | v1_xboole_0(sK1) | (~spl6_2 | ~spl6_5 | ~spl6_7 | ~spl6_9 | ~spl6_27)),
% 0.21/0.52    inference(subsumption_resolution,[],[f319,f93])).
% 0.21/0.52  fof(f319,plain,(
% 0.21/0.52    k7_partfun1(sK0,sK3,sK5) = k1_funct_1(sK3,sK5) | ~m1_subset_1(sK5,sK1) | v1_xboole_0(sK1) | (~spl6_2 | ~spl6_7 | ~spl6_9 | ~spl6_27)),
% 0.21/0.52    inference(subsumption_resolution,[],[f318,f129])).
% 0.21/0.52  fof(f318,plain,(
% 0.21/0.52    k7_partfun1(sK0,sK3,sK5) = k1_funct_1(sK3,sK5) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~m1_subset_1(sK5,sK1) | v1_xboole_0(sK1) | (~spl6_2 | ~spl6_7 | ~spl6_27)),
% 0.21/0.52    inference(subsumption_resolution,[],[f315,f119])).
% 0.21/0.52  fof(f315,plain,(
% 0.21/0.52    k7_partfun1(sK0,sK3,sK5) = k1_funct_1(sK3,sK5) | ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~m1_subset_1(sK5,sK1) | v1_xboole_0(sK1) | (~spl6_2 | ~spl6_27)),
% 0.21/0.52    inference(superposition,[],[f311,f110])).
% 0.21/0.52  fof(f110,plain,(
% 0.21/0.52    ( ! [X10,X8,X9] : (k3_funct_2(X8,X9,sK3,X10) = k1_funct_1(sK3,X10) | ~v1_funct_2(sK3,X8,X9) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X8,X9))) | ~m1_subset_1(X10,X8) | v1_xboole_0(X8)) ) | ~spl6_2),
% 0.21/0.52    inference(resolution,[],[f78,f65])).
% 0.21/0.52  fof(f332,plain,(
% 0.21/0.52    spl6_28 | ~spl6_2 | spl6_3 | ~spl6_5 | ~spl6_7 | ~spl6_9 | ~spl6_27),
% 0.21/0.52    inference(avatar_split_clause,[],[f322,f309,f127,f117,f91,f81,f76,f329])).
% 0.21/0.52  fof(f322,plain,(
% 0.21/0.52    m1_subset_1(k7_partfun1(sK0,sK3,sK5),sK0) | (~spl6_2 | spl6_3 | ~spl6_5 | ~spl6_7 | ~spl6_9 | ~spl6_27)),
% 0.21/0.52    inference(subsumption_resolution,[],[f316,f93])).
% 0.21/0.52  fof(f316,plain,(
% 0.21/0.52    m1_subset_1(k7_partfun1(sK0,sK3,sK5),sK0) | ~m1_subset_1(sK5,sK1) | (~spl6_2 | spl6_3 | ~spl6_7 | ~spl6_9 | ~spl6_27)),
% 0.21/0.52    inference(superposition,[],[f225,f311])).
% 0.21/0.52  fof(f312,plain,(
% 0.21/0.52    spl6_27 | ~spl6_2 | spl6_3 | spl6_4 | ~spl6_5 | ~spl6_7 | ~spl6_9),
% 0.21/0.52    inference(avatar_split_clause,[],[f291,f127,f117,f91,f86,f81,f76,f309])).
% 0.21/0.52  fof(f291,plain,(
% 0.21/0.52    k3_funct_2(sK1,sK0,sK3,sK5) = k7_partfun1(sK0,sK3,sK5) | (~spl6_2 | spl6_3 | spl6_4 | ~spl6_5 | ~spl6_7 | ~spl6_9)),
% 0.21/0.52    inference(resolution,[],[f254,f93])).
% 0.21/0.52  fof(f254,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(X0,sK1) | k3_funct_2(sK1,sK0,sK3,X0) = k7_partfun1(sK0,sK3,X0)) ) | (~spl6_2 | spl6_3 | spl6_4 | ~spl6_7 | ~spl6_9)),
% 0.21/0.52    inference(subsumption_resolution,[],[f253,f88])).
% 0.21/0.52  fof(f253,plain,(
% 0.21/0.52    ( ! [X0] : (v1_xboole_0(sK0) | ~m1_subset_1(X0,sK1) | k3_funct_2(sK1,sK0,sK3,X0) = k7_partfun1(sK0,sK3,X0)) ) | (~spl6_2 | spl6_3 | ~spl6_7 | ~spl6_9)),
% 0.21/0.52    inference(subsumption_resolution,[],[f252,f119])).
% 0.21/0.52  fof(f252,plain,(
% 0.21/0.52    ( ! [X0] : (~v1_funct_2(sK3,sK1,sK0) | v1_xboole_0(sK0) | ~m1_subset_1(X0,sK1) | k3_funct_2(sK1,sK0,sK3,X0) = k7_partfun1(sK0,sK3,X0)) ) | (~spl6_2 | spl6_3 | ~spl6_9)),
% 0.21/0.52    inference(subsumption_resolution,[],[f251,f83])).
% 0.21/0.52  fof(f251,plain,(
% 0.21/0.52    ( ! [X0] : (v1_xboole_0(sK1) | ~v1_funct_2(sK3,sK1,sK0) | v1_xboole_0(sK0) | ~m1_subset_1(X0,sK1) | k3_funct_2(sK1,sK0,sK3,X0) = k7_partfun1(sK0,sK3,X0)) ) | (~spl6_2 | ~spl6_9)),
% 0.21/0.52    inference(resolution,[],[f107,f129])).
% 0.21/0.52  fof(f107,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_xboole_0(X1) | ~v1_funct_2(sK3,X1,X0) | v1_xboole_0(X0) | ~m1_subset_1(X2,X1) | k3_funct_2(X1,X0,sK3,X2) = k7_partfun1(X0,sK3,X2)) ) | ~spl6_2),
% 0.21/0.52    inference(resolution,[],[f78,f51])).
% 0.21/0.53  fof(f296,plain,(
% 0.21/0.53    spl6_26 | ~spl6_1 | ~spl6_2 | ~spl6_7 | ~spl6_8 | ~spl6_9),
% 0.21/0.53    inference(avatar_split_clause,[],[f290,f127,f122,f117,f76,f71,f293])).
% 0.21/0.53  fof(f290,plain,(
% 0.21/0.53    v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4)) | (~spl6_1 | ~spl6_2 | ~spl6_7 | ~spl6_8 | ~spl6_9)),
% 0.21/0.53    inference(subsumption_resolution,[],[f289,f73])).
% 0.21/0.53  fof(f289,plain,(
% 0.21/0.53    ~v1_funct_1(sK4) | v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4)) | (~spl6_2 | ~spl6_7 | ~spl6_8 | ~spl6_9)),
% 0.21/0.53    inference(resolution,[],[f235,f124])).
% 0.21/0.53  fof(f235,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) | ~v1_funct_1(X0) | v1_funct_1(k8_funct_2(sK1,sK0,X1,sK3,X0))) ) | (~spl6_2 | ~spl6_7 | ~spl6_9)),
% 0.21/0.53    inference(subsumption_resolution,[],[f234,f119])).
% 0.21/0.53  fof(f234,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) | v1_funct_1(k8_funct_2(sK1,sK0,X1,sK3,X0))) ) | (~spl6_2 | ~spl6_9)),
% 0.21/0.53    inference(resolution,[],[f111,f129])).
% 0.21/0.53  fof(f111,plain,(
% 0.21/0.53    ( ! [X14,X12,X13,X11] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X11,X12))) | ~v1_funct_2(sK3,X11,X12) | ~v1_funct_1(X13) | ~m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X12,X14))) | v1_funct_1(k8_funct_2(X11,X12,X14,sK3,X13))) ) | ~spl6_2),
% 0.21/0.53    inference(resolution,[],[f78,f66])).
% 0.21/0.53  fof(f66,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f39])).
% 0.21/0.53  fof(f277,plain,(
% 0.21/0.53    ~spl6_1 | ~spl6_6 | ~spl6_8 | spl6_25),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f276])).
% 0.21/0.53  fof(f276,plain,(
% 0.21/0.53    $false | (~spl6_1 | ~spl6_6 | ~spl6_8 | spl6_25)),
% 0.21/0.53    inference(subsumption_resolution,[],[f275,f124])).
% 0.21/0.53  fof(f275,plain,(
% 0.21/0.53    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | (~spl6_1 | ~spl6_6 | spl6_25)),
% 0.21/0.53    inference(subsumption_resolution,[],[f274,f98])).
% 0.21/0.53  fof(f98,plain,(
% 0.21/0.53    v1_partfun1(sK4,sK0) | ~spl6_6),
% 0.21/0.53    inference(avatar_component_clause,[],[f96])).
% 0.21/0.53  fof(f96,plain,(
% 0.21/0.53    spl6_6 <=> v1_partfun1(sK4,sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.21/0.53  fof(f274,plain,(
% 0.21/0.53    ~v1_partfun1(sK4,sK0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | (~spl6_1 | spl6_25)),
% 0.21/0.53    inference(resolution,[],[f271,f101])).
% 0.21/0.53  fof(f101,plain,(
% 0.21/0.53    ( ! [X4,X3] : (v1_funct_2(sK4,X3,X4) | ~v1_partfun1(sK4,X3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) ) | ~spl6_1),
% 0.21/0.53    inference(resolution,[],[f73,f63])).
% 0.21/0.53  fof(f63,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_partfun1(X2,X0) | v1_funct_2(X2,X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f33])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(flattening,[],[f32])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(ennf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_partfun1(X2,X0) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).
% 0.21/0.53  fof(f271,plain,(
% 0.21/0.53    ~v1_funct_2(sK4,sK0,sK2) | spl6_25),
% 0.21/0.53    inference(avatar_component_clause,[],[f269])).
% 0.21/0.53  fof(f245,plain,(
% 0.21/0.53    spl6_22 | ~spl6_6 | ~spl6_11 | ~spl6_13),
% 0.21/0.53    inference(avatar_split_clause,[],[f237,f163,f147,f96,f242])).
% 0.21/0.53  fof(f147,plain,(
% 0.21/0.53    spl6_11 <=> v1_relat_1(sK4)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.21/0.53  fof(f163,plain,(
% 0.21/0.53    spl6_13 <=> v4_relat_1(sK4,sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.21/0.53  fof(f237,plain,(
% 0.21/0.53    sK0 = k1_relat_1(sK4) | (~spl6_6 | ~spl6_11 | ~spl6_13)),
% 0.21/0.53    inference(subsumption_resolution,[],[f236,f98])).
% 0.21/0.53  fof(f236,plain,(
% 0.21/0.53    sK0 = k1_relat_1(sK4) | ~v1_partfun1(sK4,sK0) | (~spl6_11 | ~spl6_13)),
% 0.21/0.53    inference(resolution,[],[f156,f165])).
% 0.21/0.53  fof(f165,plain,(
% 0.21/0.53    v4_relat_1(sK4,sK0) | ~spl6_13),
% 0.21/0.53    inference(avatar_component_clause,[],[f163])).
% 0.21/0.53  fof(f156,plain,(
% 0.21/0.53    ( ! [X0] : (~v4_relat_1(sK4,X0) | k1_relat_1(sK4) = X0 | ~v1_partfun1(sK4,X0)) ) | ~spl6_11),
% 0.21/0.53    inference(resolution,[],[f149,f56])).
% 0.21/0.53  fof(f56,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.53    inference(flattening,[],[f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.53    inference(ennf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).
% 0.21/0.53  fof(f149,plain,(
% 0.21/0.53    v1_relat_1(sK4) | ~spl6_11),
% 0.21/0.53    inference(avatar_component_clause,[],[f147])).
% 0.21/0.53  fof(f231,plain,(
% 0.21/0.53    ~spl6_21 | spl6_4 | ~spl6_6 | ~spl6_8),
% 0.21/0.53    inference(avatar_split_clause,[],[f226,f122,f96,f86,f228])).
% 0.21/0.53  fof(f226,plain,(
% 0.21/0.53    ~v1_xboole_0(sK2) | (spl6_4 | ~spl6_6 | ~spl6_8)),
% 0.21/0.53    inference(resolution,[],[f218,f124])).
% 0.21/0.53  fof(f218,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | ~v1_xboole_0(X0)) ) | (spl6_4 | ~spl6_6)),
% 0.21/0.53    inference(resolution,[],[f115,f98])).
% 0.21/0.53  fof(f115,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v1_partfun1(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | ~v1_xboole_0(X0)) ) | spl6_4),
% 0.21/0.53    inference(resolution,[],[f88,f54])).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (v1_xboole_0(X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_partfun1(X2,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ! [X0,X1] : (! [X2] : (~v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X1) | v1_xboole_0(X0))),
% 0.21/0.53    inference(flattening,[],[f22])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ! [X0,X1] : (! [X2] : (~v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | (~v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0,X1] : ((v1_xboole_0(X1) & ~v1_xboole_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ~v1_partfun1(X2,X0)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_partfun1)).
% 0.21/0.53  fof(f201,plain,(
% 0.21/0.53    spl6_20 | ~spl6_9),
% 0.21/0.53    inference(avatar_split_clause,[],[f139,f127,f198])).
% 0.21/0.53  fof(f139,plain,(
% 0.21/0.53    k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) | ~spl6_9),
% 0.21/0.53    inference(resolution,[],[f129,f59])).
% 0.21/0.53  fof(f59,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f29])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(ennf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.53  fof(f186,plain,(
% 0.21/0.53    spl6_17 | ~spl6_8),
% 0.21/0.53    inference(avatar_split_clause,[],[f133,f122,f183])).
% 0.21/0.53  fof(f133,plain,(
% 0.21/0.53    k1_relset_1(sK0,sK2,sK4) = k1_relat_1(sK4) | ~spl6_8),
% 0.21/0.53    inference(resolution,[],[f124,f60])).
% 0.21/0.53  fof(f60,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(ennf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.53  fof(f181,plain,(
% 0.21/0.53    spl6_16 | ~spl6_9),
% 0.21/0.53    inference(avatar_split_clause,[],[f137,f127,f178])).
% 0.21/0.53  fof(f137,plain,(
% 0.21/0.53    v5_relat_1(sK3,sK0) | ~spl6_9),
% 0.21/0.53    inference(resolution,[],[f129,f62])).
% 0.21/0.53  fof(f62,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(ennf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.53  fof(f166,plain,(
% 0.21/0.53    spl6_13 | ~spl6_8),
% 0.21/0.53    inference(avatar_split_clause,[],[f131,f122,f163])).
% 0.21/0.53  fof(f131,plain,(
% 0.21/0.53    v4_relat_1(sK4,sK0) | ~spl6_8),
% 0.21/0.53    inference(resolution,[],[f124,f61])).
% 0.21/0.53  fof(f61,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f31])).
% 0.21/0.53  fof(f155,plain,(
% 0.21/0.53    spl6_12 | ~spl6_9),
% 0.21/0.53    inference(avatar_split_clause,[],[f140,f127,f152])).
% 0.21/0.53  fof(f140,plain,(
% 0.21/0.53    v1_relat_1(sK3) | ~spl6_9),
% 0.21/0.53    inference(resolution,[],[f129,f58])).
% 0.21/0.53  fof(f58,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(ennf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.53  fof(f150,plain,(
% 0.21/0.53    spl6_11 | ~spl6_8),
% 0.21/0.53    inference(avatar_split_clause,[],[f135,f122,f147])).
% 0.21/0.53  fof(f135,plain,(
% 0.21/0.53    v1_relat_1(sK4) | ~spl6_8),
% 0.21/0.53    inference(resolution,[],[f124,f58])).
% 0.21/0.53  fof(f145,plain,(
% 0.21/0.53    ~spl6_10),
% 0.21/0.53    inference(avatar_split_clause,[],[f42,f142])).
% 0.21/0.53  fof(f142,plain,(
% 0.21/0.53    spl6_10 <=> k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5))),
% 0.21/0.53    inference(cnf_transformation,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.21/0.53    inference(flattening,[],[f17])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : ((k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0)) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f16])).
% 0.21/0.53  fof(f16,negated_conjecture,(
% 0.21/0.53    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (v1_partfun1(X4,X0) => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))))))))),
% 0.21/0.53    inference(negated_conjecture,[],[f15])).
% 0.21/0.53  fof(f15,conjecture,(
% 0.21/0.53    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (v1_partfun1(X4,X0) => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))))))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t193_funct_2)).
% 0.21/0.53  fof(f130,plain,(
% 0.21/0.53    spl6_9),
% 0.21/0.53    inference(avatar_split_clause,[],[f47,f127])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.53    inference(cnf_transformation,[],[f18])).
% 0.21/0.53  fof(f125,plain,(
% 0.21/0.53    spl6_8),
% 0.21/0.53    inference(avatar_split_clause,[],[f44,f122])).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.21/0.53    inference(cnf_transformation,[],[f18])).
% 0.21/0.53  fof(f120,plain,(
% 0.21/0.53    spl6_7),
% 0.21/0.53    inference(avatar_split_clause,[],[f46,f117])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    v1_funct_2(sK3,sK1,sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f18])).
% 0.21/0.53  fof(f99,plain,(
% 0.21/0.53    spl6_6),
% 0.21/0.53    inference(avatar_split_clause,[],[f41,f96])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    v1_partfun1(sK4,sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f18])).
% 0.21/0.53  fof(f94,plain,(
% 0.21/0.53    spl6_5),
% 0.21/0.53    inference(avatar_split_clause,[],[f40,f91])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    m1_subset_1(sK5,sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f18])).
% 0.21/0.53  fof(f89,plain,(
% 0.21/0.53    ~spl6_4),
% 0.21/0.53    inference(avatar_split_clause,[],[f49,f86])).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    ~v1_xboole_0(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f18])).
% 0.21/0.53  fof(f84,plain,(
% 0.21/0.53    ~spl6_3),
% 0.21/0.53    inference(avatar_split_clause,[],[f48,f81])).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    ~v1_xboole_0(sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f18])).
% 0.21/0.53  fof(f79,plain,(
% 0.21/0.53    spl6_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f45,f76])).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    v1_funct_1(sK3)),
% 0.21/0.53    inference(cnf_transformation,[],[f18])).
% 0.21/0.53  fof(f74,plain,(
% 0.21/0.53    spl6_1),
% 0.21/0.53    inference(avatar_split_clause,[],[f43,f71])).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    v1_funct_1(sK4)),
% 0.21/0.53    inference(cnf_transformation,[],[f18])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (11421)------------------------------
% 0.21/0.53  % (11421)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (11421)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (11421)Memory used [KB]: 11001
% 0.21/0.53  % (11421)Time elapsed: 0.080 s
% 0.21/0.53  % (11421)------------------------------
% 0.21/0.53  % (11421)------------------------------
% 0.21/0.53  % (11417)Success in time 0.168 s
%------------------------------------------------------------------------------
